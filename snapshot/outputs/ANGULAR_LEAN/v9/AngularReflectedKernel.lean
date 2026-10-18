import AngularGammaMultiplier
import OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel

/-! Fixed-angular-order reflected kernel with the actual shifted gamma
multiplier. The extra order is n, so the physical derivative order is n+1.
This ports the spectral/Fourier identities, genuine contour integrability,
all Euler derivatives, and source-seminorm controls to that multiplier.
The original paper scale is retained. These are kernel estimates, not the
physical smoothed-reflection identity or the zero-free theorem.
Adapted from the pinned OAI InitialBound and ReflectedKernel proofs. -/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics Set

namespace OAI.CubicEisenstein.AngularReflectionKernel
open CubicReflectionKernel

def spectralProfile (angularOrder : ℕ) (logSource : SchwartzMap ℝ ℂ) (u : ℝ) : ℂ := (axisMultiplier angularOrder) u * (𝓕 logSource) u

theorem spectralProfile_norm (angularOrder : ℕ) (logSource : SchwartzMap ℝ ℂ) (u : ℝ) :
    ‖(spectralProfile angularOrder) logSource u‖ = ‖(𝓕 logSource) u‖ := by
  rw [spectralProfile, norm_mul, (axisMultiplier_norm angularOrder), one_mul]

theorem spectralProfile_continuous (angularOrder : ℕ) (logSource : SchwartzMap ℝ ℂ) : Continuous ((spectralProfile angularOrder) logSource) :=
  (axisMultiplier_continuous angularOrder).mul (𝓕 logSource).continuous

theorem spectralProfile_moment_integrable (angularOrder : ℕ) (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    Integrable (fun u : ℝ => ‖u‖ ^ j * ‖(spectralProfile angularOrder) logSource u‖) := by
  simpa only [(spectralProfile_norm angularOrder)] using (𝓕 logSource).integrable_pow_mul volume j

theorem spectralProfile_pow_integrable (angularOrder : ℕ) (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    Integrable (fun u : ℝ => u ^ j • (spectralProfile angularOrder) logSource u) := by
  apply ((spectralProfile_moment_integrable angularOrder) logSource j).mono'
    ((show Continuous (fun u : ℝ => u ^ j • (spectralProfile angularOrder) logSource u) by
      exact (continuous_id.pow j).smul ((spectralProfile_continuous angularOrder) logSource)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun u => by simp only [norm_smul, norm_pow, le_rfl])

def reflectedLogProfile (angularOrder : ℕ) (logSource : SchwartzMap ℝ ℂ) : ℝ → ℂ := 𝓕 ((spectralProfile angularOrder) logSource)

theorem reflectedLogProfile_smooth (angularOrder : ℕ) (logSource : SchwartzMap ℝ ℂ) :
    ContDiff ℝ ∞ ((reflectedLogProfile angularOrder) logSource) :=
  Real.contDiff_fourier (fun j _ => (spectralProfile_moment_integrable angularOrder) logSource j)

theorem reflectedLogProfile_deriv (angularOrder : ℕ) (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    iteratedDeriv j ((reflectedLogProfile angularOrder) logSource) =
      𝓕 (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * (spectralProfile angularOrder) logSource u) := by
  simpa only [reflectedLogProfile, smul_eq_mul] using
    (Real.iteratedDeriv_fourier (N := (⊤ : ℕ∞))
      (fun n _ => (spectralProfile_pow_integrable angularOrder) logSource n) (by simp : (j : ℕ∞) ≤ ⊤))


theorem reflectedLogProfile_deriv_bound (angularOrder : ℕ) (logSource : SchwartzMap ℝ ℂ) (j : ℕ) (y : ℝ) :
    ‖iteratedDeriv j ((reflectedLogProfile angularOrder) logSource) y‖ ≤
      (2 * Real.pi) ^ j * ∫ u : ℝ, ‖u‖ ^ j * ‖(𝓕 logSource) u‖ := by
  rw [(reflectedLogProfile_deriv angularOrder)]
  have hb := VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ)
    (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * (spectralProfile angularOrder) logSource u) y
  change ‖𝓕 (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * (spectralProfile angularOrder) logSource u) y‖ ≤ _ at hb
  refine hb.trans_eq ?_
  have hnorm (u : ℝ) :
      ‖(-2 * Real.pi * Complex.I * u) ^ j * (spectralProfile angularOrder) logSource u‖ =
        (2 * Real.pi) ^ j * (‖u‖ ^ j * ‖(𝓕 logSource) u‖) := by
    simp only [norm_mul, norm_pow, (spectralProfile_norm angularOrder), Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  simp_rw [hnorm]
  exact integral_const_mul _ _



theorem reflectedLogProfile_source_bound (angularOrder : ℕ) (j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (logSource : SchwartzMap ℝ ℂ) (y : ℝ),
        ‖iteratedDeriv j ((reflectedLogProfile angularOrder) logSource) y‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by
  let m := j + (volume : Measure ℝ).integrablePower
  let S : Finset (ℕ × ℕ) := {(0, 0), (m, 0)}
  obtain ⟨s, C, hC, hbound⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control (E := ℝ)
    (FourierTransform.fourierCLM ℝ (SchwartzMap ℝ ℂ)) S
  refine ⟨s, (2 * Real.pi) ^ j * (momentScale + 1) * (2 * C), by
    have := momentScale_nonneg
    positivity, ?_⟩
  intro logSource y
  have h0' : schwartzSeminormFamily ℝ ℝ ℂ (0, 0) ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
    Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S])
  have hm' : schwartzSeminormFamily ℝ ℝ ℂ (m, 0) ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
    Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S])
  have h0 := Seminorm.le_def.mp h0' (𝓕 logSource)
  have hm := Seminorm.le_def.mp hm' (𝓕 logSource)
  change SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) ≤ _ at h0
  change SchwartzMap.seminorm ℝ m 0 (𝓕 logSource) ≤ _ at hm
  have hs := hbound logSource
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (𝓕 logSource) ≤ _ at hs
  have hsum : SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) + SchwartzMap.seminorm ℝ m 0 (𝓕 logSource) ≤
      2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by linarith
  have hmoment := FourierBridge.fourier_coefficient_moment logSource j
  change (∫ u : ℝ, ‖u‖ ^ j * ‖(𝓕 logSource) u‖) ≤ momentScale *
    (SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) + SchwartzMap.seminorm ℝ m 0 (𝓕 logSource)) at hmoment
  calc
    _ ≤ (2 * Real.pi) ^ j * ∫ u : ℝ, ‖u‖ ^ j * ‖(𝓕 logSource) u‖ :=
      (reflectedLogProfile_deriv_bound angularOrder) logSource j y
    _ ≤ (2 * Real.pi) ^ j * (momentScale *
        (2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource)) := by
      exact mul_le_mul_of_nonneg_left
        (hmoment.trans (mul_le_mul_of_nonneg_left hsum momentScale_nonneg)) (by positivity)
    _ ≤ _ := by
      have hpos : 0 ≤ 2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by positivity
      calc
        _ ≤ (2 * Real.pi) ^ j * ((momentScale + 1) *
            (2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right zero_le_one) hpos) (by positivity)
        _ = _ := by ring


def paperKernel (angularOrder : ℕ) (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  mellinInv 0 (fun t => mellin V (-t) * (gammaMultiplier angularOrder) t) (paperScale * x)



theorem paperKernel_eq_logFourier (angularOrder : ℕ) (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (x : ℝ) (hx : 0 < x) :
    (paperKernel angularOrder) V x = (reflectedLogProfile angularOrder) logSource (Real.log (paperScale * x)) := by
  unfold paperKernel
  rw [mellinInv_eq_fourierInv 0 _ (mul_pos paperScale_pos hx)]
  simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_smul]
  rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  have hfun : (fun y : ℝ => mellin V (-(0 + 2 * Real.pi * y * Complex.I)) *
      (gammaMultiplier angularOrder) (0 + 2 * Real.pi * y * Complex.I)) = (spectralProfile angularOrder) logSource := by
    funext y
    have hy : (0 + 2 * Real.pi * y * Complex.I : ℂ) =
        ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hy, mellin_axis_eq_fourier V logSource hL]
    exact mul_comm _ _
  rw [hfun]
  rfl


theorem kernel_vertical_eq_spectralProfile (angularOrder : ℕ) (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (y : ℝ) :
    mellin V (-(y * Complex.I)) * (gammaMultiplier angularOrder) (y * Complex.I) =
      (spectralProfile angularOrder) logSource (y / (2 * Real.pi)) := by
  have hy : 2 * Real.pi * (y / (2 * Real.pi)) = y := by field_simp
  rw [spectralProfile, axisMultiplier, ← mellin_axis_eq_fourier V logSource hL, hy]
  exact mul_comm _ _

theorem kernel_vertical_integrable (angularOrder : ℕ) (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) :
    Complex.VerticalIntegrable (fun t => mellin V (-t) * (gammaMultiplier angularOrder) t) 0 := by
  have hi : Integrable ((spectralProfile angularOrder) logSource) := by
    simpa using (spectralProfile_pow_integrable angularOrder) logSource 0
  have hscaled := hi.comp_div (R := 2 * Real.pi) (by positivity)
  simpa only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add,
    (kernel_vertical_eq_spectralProfile angularOrder) V logSource hL] using hscaled

theorem paperKernel_integrable (angularOrder : ℕ) (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (x : ℝ) (hx : 0 < x) :
    Integrable (fun y : ℝ => ((paperScale * x : ℝ) : ℂ) ^ (-(y * Complex.I)) *
      (mellin V (-(y * Complex.I)) * (gammaMultiplier angularOrder) (y * Complex.I))) := by
  have hcx := mul_pos paperScale_pos hx
  have hi := (kernel_vertical_integrable angularOrder) V logSource hL
  simp only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add] at hi
  apply hi.bdd_mul (c := 1)
  · exact ((show Continuous (fun y : ℝ => -(y * Complex.I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hcx)))).aestronglyMeasurable
  · filter_upwards [] with y
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hcx]
    simp

theorem paperKernel_contDiffOn (angularOrder : ℕ) (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) :
    ContDiffOn ℝ ∞ ((paperKernel angularOrder) V) (Set.Ioi 0) := by
  have hg : ContDiffOn ℝ ∞
      (fun x => (reflectedLogProfile angularOrder) logSource (Real.log (paperScale * x))) (Set.Ioi 0) := by
    intro x hx
    apply ((reflectedLogProfile_smooth angularOrder) logSource).contDiffAt.comp_contDiffWithinAt x
    exact ((contDiffAt_const.mul contDiffAt_id).log
      (ne_of_gt (mul_pos paperScale_pos hx))).contDiffWithinAt
  apply hg.congr
  intro x hx
  exact (paperKernel_eq_logFourier angularOrder) V logSource hL x hx

theorem paperKernel_euler_eq (angularOrder : ℕ) (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) (x : ℝ) (hx : 0 < x) :
    LocalLogFourier.eulerDeriv ((paperKernel angularOrder) V) j x =
      iteratedDeriv j ((reflectedLogProfile angularOrder) logSource) (Real.log (paperScale * x)) := by
  have hfun : (fun t : ℝ => (paperKernel angularOrder) V (x * Real.exp t)) =
      (fun t : ℝ => (reflectedLogProfile angularOrder) logSource (Real.log (paperScale * x) + t)) := by
    funext t
    rw [(paperKernel_eq_logFourier angularOrder) V logSource hL _ (mul_pos hx (Real.exp_pos t))]
    rw [← mul_assoc, Real.log_mul (ne_of_gt (mul_pos paperScale_pos hx))
      (ne_of_gt (Real.exp_pos t)), Real.log_exp]
  rw [LocalLogFourier.eulerDeriv, hfun, iteratedDeriv_comp_const_add]
  simp

theorem paperKernel_source_euler_bound (angularOrder : ℕ) (j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
        (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
        (x : ℝ), 0 < x →
        ‖LocalLogFourier.eulerDeriv ((paperKernel angularOrder) V) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (logSchwartz V a b ha hsupp hV) := by
  obtain ⟨s, C, hC, hb⟩ := (reflectedLogProfile_source_bound angularOrder) j
  refine ⟨s, C, hC, ?_⟩
  intro V a b ha hsupp hV x hx
  rw [(paperKernel_euler_eq angularOrder) V (logSchwartz V a b ha hsupp hV) (by intro u; rfl) j x hx]
  exact hb _ _

theorem paperKernel_compact_source_integrable (angularOrder : ℕ)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (x : ℝ) (hx : 0 < x) :
    Integrable (fun y : ℝ => ((paperScale * x : ℝ) : ℂ) ^ (-(y * Complex.I)) *
      (mellin V (-(y * Complex.I)) * (gammaMultiplier angularOrder) (y * Complex.I))) :=
  (paperKernel_integrable angularOrder) V (logSchwartz V a b ha hsupp hV) (by intro u; rfl) x hx

theorem paperKernel_compact_source_smooth (angularOrder : ℕ)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    ContDiffOn ℝ ∞ ((paperKernel angularOrder) V) (Set.Ioi 0) :=
  (paperKernel_contDiffOn angularOrder) V (logSchwartz V a b ha hsupp hV) (by intro u; rfl)

theorem reflectedLogProfile_deriv_vanish (angularOrder : ℕ) (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    Tendsto (iteratedDeriv j ((reflectedLogProfile angularOrder) logSource)) (cocompact ℝ) (𝓝 0) := by
  rw [(reflectedLogProfile_deriv angularOrder)]
  exact Real.zero_at_infty_fourier _

theorem paperKernel_euler_vanish_infty (angularOrder : ℕ) (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) :
    Tendsto (LocalLogFourier.eulerDeriv ((paperKernel angularOrder) V) j) atTop (𝓝 0) := by
  have hd := ((reflectedLogProfile_deriv_vanish angularOrder) logSource j).mono_left atTop_le_cocompact
  have hlog : Tendsto (fun x : ℝ => Real.log (paperScale * x)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Tendsto.const_mul_atTop paperScale_pos tendsto_id)
  apply (hd.comp hlog).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact ((paperKernel_euler_eq angularOrder) V logSource hL j x hx).symm

theorem paperKernel_euler_vanish_zero (angularOrder : ℕ) (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) :
    Tendsto (LocalLogFourier.eulerDeriv ((paperKernel angularOrder) V) j) (𝓝[>] 0) (𝓝 0) := by
  have hd := ((reflectedLogProfile_deriv_vanish angularOrder) logSource j).mono_left atBot_le_cocompact
  have hmul : Tendsto (fun x : ℝ => paperScale * x) (𝓝[>] 0) (𝓝[>] 0) := by
    have hm : Tendsto (fun x : ℝ => paperScale * x)
        (comap (fun x : ℝ => paperScale * x) (𝓝[>] 0)) (𝓝[>] 0) := tendsto_comap
    rwa [comap_mulLeft_nhdsGT_zero paperScale_pos] at hm
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hmul
  apply (hd.comp hlog).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ((paperKernel_euler_eq angularOrder) V logSource hL j x hx).symm

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

/-- The shifted Mellin integrand is holomorphic on the full right half-plane
where the two numerator gamma factors have positive real part. -/
theorem kernelMellinIntegrand_differentiableAt (angularOrder : ℕ)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) (hs : -((angularOrder : ℝ) / 2 + 5 / 6) < s.re) :
    DifferentiableAt ℂ (fun t => mellin V (-t) * gammaMultiplier angularOrder t) s := by
  exact ((CubicReflectionKernel.compact_source_mellin_differentiable V a b ha hsupp hV (-s)).comp s
    differentiableAt_id.neg).mul (gammaMultiplier_differentiableAt angularOrder s hs)

/-- The new actual kernel recovers the pinned original kernel at n=0. -/
theorem paperKernel_zero (V : ℝ → ℂ) (x : ℝ) :
    paperKernel 0 V x = CubicReflectionKernel.paperKernel V x := by
  simp only [paperKernel, gammaMultiplier_zero, CubicReflectionKernel.paperKernel]

end OAI.CubicEisenstein.AngularReflectionKernel
