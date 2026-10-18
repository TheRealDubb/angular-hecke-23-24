import AngularKernelContour
import AngularShiftedBesselReflection

/-! Shifted-kernel summation and the reflected smoothing integral. Every
coefficient weight and order-dependent scalar remains explicit. Absolute
vertical integrability is proved before the integrated reflection identity.
No completedT contour shift or moment estimate is asserted here. -/

noncomputable section
open MeasureTheory Filter
open scoped Classical BigOperators Topology ContDiff ENNReal

namespace OAI.CubicEisenstein.AngularSmoothedReflection
open CompletedGauss AngularShiftedBesselReflection
open CubicReflectionKernel (paperScale paperScale_pos)
open AngularReflectionKernel

theorem paperKernel_three_halves (n : ℕ) (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (x:ℝ) (hx:0<x) :
    (paperKernel n) V x=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      ((paperScale*x:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
        (mellinEulerData n) V 0 ((3/2:ℂ)+t*Complex.I) := by
  have he:=mellinInv_euler_shift n V v0 v1 hv0 hVs hV 2 0 (3/2) (by norm_num)
    (paperScale*x) (mul_pos paperScale_pos hx)
  change (paperKernel n) V x=_
  have hl:mellinInv 0 ((mellinEulerData n) V 0) (paperScale*x)=(paperKernel n) V x:=by
    have hf : (mellinEulerData n) V 0=(fun s:ℂ=>mellin V (-s)*(gammaMultiplier n) s) := by
      funext s
      simp only [mellinEulerData,pow_zero,one_mul,mellinData]
    rw [hf]
    rfl
  rw [hl] at he
  simpa only [mellinInv,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using he

theorem paperKernel_three_halves_bound (n : ℕ) (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V) :
    ∃C:ℝ,0<C ∧ ∀x:ℝ,0<x→‖(paperKernel n) V x‖≤C*(paperScale*x)^(-(3/2:ℝ)) := by
  obtain ⟨C,hC,hb⟩:=mellinInv_euler_line_bound n V v0 v1 hv0 hVs hV 2 0
  refine ⟨C,hC,?_⟩
  intro x hx
  have he:=mellinInv_euler_shift n V v0 v1 hv0 hVs hV 2 0 (3/2) (by norm_num)
    (paperScale*x) (mul_pos paperScale_pos hx)
  have hl:mellinInv 0 ((mellinEulerData n) V 0) (paperScale*x)=(paperKernel n) V x:=by
    have hf : (mellinEulerData n) V 0=(fun s:ℂ=>mellin V (-s)*(gammaMultiplier n) s) := by
      funext s
      simp only [mellinEulerData,pow_zero,one_mul,mellinData]
    rw [hf]
    rfl
  rw [hl] at he
  rw [he]
  exact hb (3/2) (by norm_num) (paperScale*x) (mul_pos paperScale_pos hx)

theorem paperKernel_weighted_summable (n : ℕ) {α:Type*}
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) : Summable (fun i=>a i*(paperKernel n) V (c*r i)) := by
  obtain ⟨C,hC,hb⟩:=paperKernel_three_halves_bound n V v0 v1 hv0 hVs hV
  apply Summable.of_norm
  apply (has.mul_left (C*(paperScale*c)^(-(3/2:ℝ)))).of_nonneg_of_le (fun i=>norm_nonneg _)
  intro i
  rw [norm_mul]
  calc
    _≤‖a i‖*(C*(paperScale*(c*r i))^(-(3/2:ℝ))):=
      mul_le_mul_of_nonneg_left (hb _ (mul_pos hc (hr i))) (norm_nonneg _)
    _=(C*(paperScale*c)^(-(3/2:ℝ)))*(‖a i‖*(r i)^(-(3/2:ℝ))):=by
      rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
        Real.mul_rpow (mul_pos paperScale_pos hc).le (hr i).le]
      ring

theorem paperKernel_weighted_mellin (n : ℕ) {α:Type*} [Countable α]
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) :
    (∑'i,a i*(paperKernel n) V (c*r i))=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      (∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
        (((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
          (mellinEulerData n) V 0 ((3/2:ℂ)+t*Complex.I)) := by
  let M:ℝ→ℂ:=fun t=>((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
    (mellinEulerData n) V 0 ((3/2:ℂ)+t*Complex.I)
  have hM:Integrable M:=by
    simpa only [M,inverseMellinIntegrand,Complex.ofReal_div,Complex.ofReal_ofNat] using
      inverseMellinIntegrand_vertical_integrable n V v0 v1 hv0 hVs hV 2 0 (3/2)
        (by norm_num) (paperScale*c) (mul_pos paperScale_pos hc)
  have hi (i:α) : a i*(paperKernel n) V (c*r i)=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I))*M t := by
    rw [paperKernel_three_halves n V v0 v1 hv0 hVs hV _ (mul_pos hc (hr i))]
    rw [←mul_assoc,mul_comm (a i),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_pos paperScale_pos hc).le (hr i).le]
    dsimp only [M]
    ring
  simp_rw [hi]
  rw [tsum_mul_left]
  congr 1
  simpa only [M,Complex.ofReal_div,Complex.ofReal_ofNat] using
    weighted_vertical_sum_integral r hr a (3/2) has M hM
theorem paperKernel_weighted_norm_summable (n : ℕ) {α:Type*}
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) : Summable (fun i=>‖a i*(paperKernel n) V (c*r i)‖) := by
  obtain ⟨C,hC,hb⟩:=paperKernel_three_halves_bound n V v0 v1 hv0 hVs hV
  apply (has.mul_left (C*(paperScale*c)^(-(3/2:ℝ)))).of_nonneg_of_le (fun i=>norm_nonneg _)
  intro i
  rw [norm_mul]
  calc
    _≤‖a i‖*(C*(paperScale*(c*r i))^(-(3/2:ℝ))):=
      mul_le_mul_of_nonneg_left (hb _ (mul_pos hc (hr i))) (norm_nonneg _)
    _=(C*(paperScale*c)^(-(3/2:ℝ)))*(‖a i‖*(r i)^(-(3/2:ℝ))):=by
      rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
        Real.mul_rpow (mul_pos paperScale_pos hc).le (hr i).le]
      ring

theorem normalized_weight_summable {ι : Type*} (n : ℕ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (b : ι → ℂ)
    (hb : Summable (fun i => ‖b i‖ * r i ^ (-(3 / 2 : ℝ) - (n : ℝ) / 2))) :
    Summable (fun i => ‖b i * (r i : ℂ) ^ (-(n : ℂ) / 2)‖ * r i ^ (-(3 / 2 : ℝ))) := by
  apply hb.congr
  intro i
  symm
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hr i)]
  simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re]
  rw [mul_assoc, ← Real.rpow_add (hr i)]
  congr 2
  ring

/-- Absolute integrals of the weighted vertical summands are summable. -/
theorem weighted_vertical_integrable {ι : Type*} [Countable ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (a : ι → ℂ) (σ : ℝ)
    (ha : Summable (fun i => ‖a i‖ * r i ^ (-σ)))
    (M : ℝ → ℂ) (hM : Integrable M) :
    Integrable (fun t : ℝ =>
      (∑' i, a i * (r i : ℂ) ^ (-((σ : ℂ) + t * Complex.I))) * M t) := by
  let F : ι → ℝ → ℂ := fun i t => a i * (r i : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) * M t
  have hi (i : ι) : Integrable (F i) :=
    weighted_vertical_power_integrable M hM (r i) σ (hr i) (a i)
  have hs : Summable (fun i => ∫ t : ℝ, ‖F i t‖) := by
    simp only [F, weighted_vertical_power_integral_norm M _ σ (hr _) _]
    exact ha.mul_right _
  have hsum : Integrable (fun t => ∑' i, F i t) := by
    refine ⟨AEStronglyMeasurable.tsum (fun i => (hi i).1), ?_⟩
    unfold HasFiniteIntegral
    calc
      (∫⁻ t, ‖∑' i, F i t‖ₑ) ≤ ∫⁻ t, ∑' i, ‖F i t‖ₑ :=
        lintegral_mono (fun t => enorm_tsum_le_tsum_enorm)
      _ = ∑' i, ∫⁻ t, ‖F i t‖ₑ := lintegral_tsum (fun i => (hi i).1.enorm)
      _ = ∑' i, ENNReal.ofReal (∫ t : ℝ, ‖F i t‖) := by
        apply tsum_congr
        intro i
        exact (ofReal_integral_norm_eq_lintegral_enorm (hi i)).symm
      _ < (⊤ : ℝ≥0∞) := hs.tsum_ofReal_lt_top
  convert hsum using 1
  funext t
  exact (tsum_mul_right).symm

/-- Genuine integrability of the reflected smoothing line, in the original
positive-t orientation used for contour shifts. -/
theorem reflected_smoothing_integrable {ι : Type*} [Countable ι]
    (n : ℕ) (F : ℝ → ℂ) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (b : ι → ℂ)
    (q d Q : ℝ) (hq : 0 < q) (hd : 0 < d) (hQ : 0 < Q) (A : ℂ)
    (hreflect : ∀ v : ℝ, 0 < v → F v = A *
      ((v : ℂ) ^ (-2 * ((n : ℂ) + 1)) * radialBesselProfile r b d ((Q * v)⁻¹)))
    (hb : Summable (fun i => ‖b i‖ * r i ^ (-(3 / 2 : ℝ) - (n : ℝ) / 2)))
    (V : ℝ → ℂ) (v0 v1 : ℝ) (hv0 : 0 < v0)
    (hVs : Function.support V ⊆ Set.Icc v0 v1) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    Integrable (fun t : ℝ => smoothingIntegrand n F q V X ((-1 : ℂ) + t * Complex.I)) := by
  let a : ι → ℂ := fun i => b i * (r i : ℂ) ^ (-(n : ℂ) / 2)
  have ha := normalized_weight_summable n r hr b hb
  let c : ℝ := 27 * q ^ 2 * d ^ 2 * X / Q ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  let M : ℝ → ℂ := fun t => ((paperScale * c : ℝ) : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I)) *
    mellinEulerData n V 0 ((3 / 2 : ℂ) + t * Complex.I)
  have hM : Integrable M := by
    simpa only [M, inverseMellinIntegrand, Complex.ofReal_div, Complex.ofReal_ofNat] using
      inverseMellinIntegrand_vertical_integrable n V v0 v1 hv0 hVs hV 2 0 (3 / 2)
        (by norm_num) (paperScale * c) (mul_pos paperScale_pos hc)
  have hH := weighted_vertical_integrable r hr a (3 / 2) ha M hM
  let K : ℂ := A * (Q : ℂ) ^ (n + 1) * ((q / d : ℝ) : ℂ) ^ (n + 2)
  have hpoint (t : ℝ) : smoothingIntegrand n F q V X ((-1 : ℂ) + (-t) * Complex.I) =
      K * ((∑' i, a i * (r i : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I))) * M t) := by
    simpa only [K, a, M, c, mellinEulerData, pow_zero, one_mul, mellinData] using
      reflected_smoothing_line n F r hr b q d Q hq hd hQ A hreflect hb V X hX t
  have hneg : Integrable (fun t : ℝ =>
      smoothingIntegrand n F q V X ((-1 : ℂ) + (-t) * Complex.I)) := by
    simp_rw [hpoint]
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hH.const_mul K
  simpa only [Complex.ofReal_neg, neg_neg] using hneg.comp_neg

/-- Integrated reflected smoothing with the literal raw radial coefficient.
The old weight b is replaced by b*r^(-n/2), and no such factor is dropped. -/
theorem reflected_smoothing_integral {ι : Type*} [Countable ι]
    (n : ℕ) (F : ℝ → ℂ) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (b : ι → ℂ)
    (q d Q : ℝ) (hq : 0 < q) (hd : 0 < d) (hQ : 0 < Q) (A : ℂ)
    (hreflect : ∀ v : ℝ, 0 < v → F v = A *
      ((v : ℂ) ^ (-2 * ((n : ℂ) + 1)) * radialBesselProfile r b d ((Q * v)⁻¹)))
    (hb : Summable (fun i => ‖b i‖ * r i ^ (-(3 / 2 : ℝ) - (n : ℝ) / 2)))
    (V : ℝ → ℂ) (v0 v1 : ℝ) (hv0 : 0 < v0)
    (hVs : Function.support V ⊆ Set.Icc v0 v1) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      smoothingIntegrand n F q V X ((-1 : ℂ) + t * Complex.I) =
        (A * (Q : ℂ) ^ (n + 1) * ((q / d : ℝ) : ℂ) ^ (n + 2)) *
          ∑' i, (b i * (r i : ℂ) ^ (-(n : ℂ) / 2)) *
            paperKernel n V (27 * q ^ 2 * d ^ 2 * X * r i / Q ^ 2) := by
  let a : ι → ℂ := fun i => b i * (r i : ℂ) ^ (-(n : ℂ) / 2)
  have ha := normalized_weight_summable n r hr b hb
  let c : ℝ := 27 * q ^ 2 * d ^ 2 * X / Q ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  let M : ℝ → ℂ := fun t => (∑' i, a i * (r i : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I))) *
    (((paperScale * c : ℝ) : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I)) *
      mellinEulerData n V 0 ((3 / 2 : ℂ) + t * Complex.I))
  let K : ℂ := A * (Q : ℂ) ^ (n + 1) * ((q / d : ℝ) : ℂ) ^ (n + 2)
  have hk := paperKernel_weighted_mellin n r hr a ha V v0 v1 hv0 hVs hV c hc
  have hpoint (t : ℝ) : smoothingIntegrand n F q V X ((-1 : ℂ) + (-t) * Complex.I) = K * M t := by
    simpa only [K, a, M, c, mellinEulerData, pow_zero, one_mul, mellinData] using
      reflected_smoothing_line n F r hr b q d Q hq hd hQ A hreflect hb V X hX t
  calc
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        smoothingIntegrand n F q V X ((-1 : ℂ) + (-t) * Complex.I) := by
      congr 1
      simpa only [Complex.ofReal_neg] using
        (integral_neg_eq_self (fun t : ℝ =>
          smoothingIntegrand n F q V X ((-1 : ℂ) + t * Complex.I)) volume).symm
    _ = K * ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, M t) := by
      simp_rw [hpoint]
      rw [integral_const_mul]
      ring
    _ = K * (∑' i, a i * paperKernel n V (c * r i)) := by rw [hk]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro i
      congr 2
      dsimp [c]
      ring

end OAI.CubicEisenstein.AngularSmoothedReflection
