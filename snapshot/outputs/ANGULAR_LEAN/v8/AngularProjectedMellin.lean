import AngularFiniteProjector

/-! The actual finite Fourier projector has the completed angular
Dirichlet-series Mellin formula on Re(s)>3/2. The radial derivative powers
cancel in both the summability estimate and the complex Dirichlet powers.
No summability assumption is imposed on the physical character. This is
not a moment estimate or a zero-free theorem. -/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace OAI.CubicEisenstein.AngularProjectedMellin

open CompletedGauss SevenEighths.Angular AngularFiniteProjector

local notation "Eis" => ActualEisensteinCubic.O
local instance : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal Eis) := ConcretePrimeRowBridge.idealGenerator_injective.countable

theorem sqrt_pow_cpow (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (Real.sqrt r : ℂ) ^ n = (r : ℂ) ^ ((n : ℂ) / 2) := by
  have h := positive_sqrt_cpow_twice r hr (((n : ℂ) - 1) / 2)
  rw [show (2 : ℂ) * (((n : ℂ) - 1) / 2) + 1 = (n : ℂ) by ring,
    show (((n : ℂ) - 1) / 2) + 1 / 2 = (n : ℂ) / 2 by ring] at h
  simpa only [Complex.cpow_natCast] using h

theorem sqrt_power_complex_cancel (r : ℝ) (hr : 0 < r) (n : ℕ) (s : ℂ) :
    (Real.sqrt r : ℂ) ^ n * (r : ℂ) ^ (1 / 2 - (s + (n : ℂ) / 2)) =
      (r : ℂ) ^ (1 / 2 - s) := by
  rw [sqrt_pow_cpow r hr n,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hr.ne')]
  congr 1
  ring

theorem sqrt_power_real_cancel (r : ℝ) (hr : 0 < r) (n : ℕ) (s : ℂ) :
    Real.sqrt r ^ n * r ^ (1 / 2 - (s + (n : ℂ) / 2).re) =
      r ^ (1 / 2 - s.re) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hr.le,
    ← Real.rpow_add hr]
  congr 1
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
  ring

def angularRadialCoefficient (χ : AngularCharacter) (n : ℕ)
    (p : CompletedMellinIndex) : ℂ :=
  completedMellinCoefficient χ.elementHom.toMonoidHom p *
    (Real.sqrt (completedMellinLength p) : ℂ) ^ n

/-- The weighted radial array is actually summable in the full original
absolute-convergence half-plane, with no additional summability premise. -/
theorem angularRadialCoefficient_summable (χ : AngularCharacter) (n : ℕ)
    (s : ℂ) (hs : 3 / 2 < s.re) :
    Summable (fun p : CompletedMellinIndex => ‖angularRadialCoefficient χ n p‖ *
      completedMellinLength p ^ (1 / 2 - (s + (n : ℂ) / 2).re)) := by
  have hnorm : ∀ a : Eis, ‖χ.elementHom.toMonoidHom a‖ ≤ 1 :=
    χ.norm_elementCoeff_le_one
  have hsum := completedMellinCoefficient_summable χ.elementHom.toMonoidHom hnorm
    (s.re - 1 / 2) (by linarith)
  apply hsum.congr
  intro p
  simp only [angularRadialCoefficient, norm_mul, norm_pow,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_assoc, sqrt_power_real_cancel _ (completedMellinLength_pos p) n s]
  congr 1
  congr 1
  ring

theorem angularRadialCoefficient_series (χ : AngularCharacter) (n : ℕ) (s : ℂ) :
    (∑' p : CompletedMellinIndex, angularRadialCoefficient χ n p *
      (completedMellinLength p : ℂ) ^ (1 / 2 - (s + (n : ℂ) / 2))) =
        completedDirichletSeries χ.elementHom.toMonoidHom s := by
  unfold completedDirichletSeries
  apply tsum_congr
  intro p
  rw [angularRadialCoefficient, mul_assoc,
    sqrt_power_complex_cancel _ (completedMellinLength_pos p) n s]

/-- The actual finite projector, rather than an assumed abstract profile,
is the radial Bessel profile with the extra physical derivative powers. -/
theorem finiteProjector_radial (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * χ.modulus)
    (v : ℝ) (hv : 0 < v) :
    finiteProjector χ n c hc v =
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
        radialBesselProfile completedMellinLength (angularRadialCoefficient χ n)
          thetaBesselScale v := by
  rw [finiteProjector_completed_indices χ n hk c hc hcQ v hv]
  congr 1
  unfold radialBesselProfile
  apply tsum_congr
  intro p
  unfold angularRadialCoefficient
  ring

/-- Actual projected physical profile to actual angular completed
Dirichlet series, with every theta scalar and the shifted gamma factor. -/
theorem finiteProjector_mellin (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * χ.modulus)
    (s : ℂ) (hs : 3 / 2 < s.re) :
    mellin (finiteProjector χ n c hc) (2 * s + (n : ℂ)) =
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
        besselMellinFactor thetaBesselScale (s + (n : ℂ) / 2) *
          completedDirichletSeries χ.elementHom.toMonoidHom s := by
  let A : ℂ := thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n
  let f : ℝ → ℂ := radialBesselProfile completedMellinLength
    (angularRadialCoefficient χ n) thetaBesselScale
  have hp : mellin (finiteProjector χ n c hc) (2 * s + (n : ℂ)) =
      mellin (fun v => A * f v) (2 * s + (n : ℂ)) := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [finiteProjector_radial χ n hk c hc hcQ v hv]
  have hmul := mellin_const_smul f (2 * s + (n : ℂ)) A
  simp only [smul_eq_mul] at hmul
  rw [hp, hmul]
  have ht : -(1 / 3 : ℝ) < (s + (n : ℂ) / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hm := radialBesselProfile_mellin completedMellinLength completedMellinLength_pos
    (angularRadialCoefficient χ n) thetaBesselScale thetaBesselScale_pos
    (s + (n : ℂ) / 2) ht (angularRadialCoefficient_summable χ n s hs)
  rw [show (2 : ℂ) * (s + (n : ℂ) / 2) = 2 * s + (n : ℂ) by ring,
    angularRadialCoefficient_series χ n s] at hm
  have hm' : mellin f (2 * s + (n : ℂ)) =
    besselMellinFactor thetaBesselScale (s + (n : ℂ) / 2) *
      completedDirichletSeries χ.elementHom.toMonoidHom s := by
    simpa only [f, besselMellinFactor,
      show (2 : ℂ) * (s + (n : ℂ) / 2) = 2 * s + (n : ℂ) by ring] using hm
  rw [hm']
  exact (mul_assoc _ _ _).symm

/-- Summable integrals of norms establish actual integrability of a
countable sum. The totalized sum need not be summable at exceptional points. -/
theorem integrableOn_tsum_of_summable_norm_integrals {ι : Type*} [Countable ι]
    (F : ι → ℝ → ℂ) (hi : ∀ i, IntegrableOn (F i) (Ioi 0))
    (hs : Summable (fun i => ∫ v : ℝ in Ioi 0, ‖F i v‖)) :
    IntegrableOn (fun v => ∑' i, F i v) (Ioi 0) := by
  refine ⟨AEStronglyMeasurable.tsum (fun i => (hi i).1), ?_⟩
  unfold HasFiniteIntegral
  calc
    (∫⁻ v, ‖∑' i, F i v‖ₑ ∂(volume.restrict (Ioi 0)))
        ≤ ∫⁻ v, ∑' i, ‖F i v‖ₑ ∂(volume.restrict (Ioi 0)) :=
      lintegral_mono (fun v => enorm_tsum_le_tsum_enorm)
    _ = ∑' i, ∫⁻ v, ‖F i v‖ₑ ∂(volume.restrict (Ioi 0)) :=
      lintegral_tsum (fun i => (hi i).1.enorm)
    _ = ∑' i, ENNReal.ofReal (∫ v : ℝ in Ioi 0, ‖F i v‖) := by
      apply tsum_congr
      intro i
      exact (ofReal_integral_norm_eq_lintegral_enorm (hi i)).symm
    _ < ∞ := hs.tsum_ofReal_lt_top

/-- Actual Mellin convergence for the radial Bessel series under the same
explicit weighted-coefficient hypothesis used by the original Mellin formula. -/
theorem radialBesselProfile_mellinConvergent {ι : Type*} [Countable ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (a : ι → ℂ) (q : ℝ) (hq : 0 < q)
    (s : ℂ) (hs : -(1 / 3) < s.re)
    (ha : Summable (fun i => ‖a i‖ * r i ^ (1 / 2 - s.re))) :
    MellinConvergent (radialBesselProfile r a q) (2 * s) := by
  let freq : ι → ℂ := fun i => ((q * Real.sqrt (r i) : ℝ) : ℂ)
  have hf (i : ι) : freq i ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos hq (Real.sqrt_pos.mpr (hr i))).ne'
  have has : Summable (fun i => ‖a i * (r i : ℂ)‖ *
      ‖freq i‖ ^ (-(2 * s.re + 1))) := by
    simp only [freq, radial_bessel_coefficient_norm _ q s.re (hr _) hq]
    exact ha.mul_left _
  let F : ι → ℝ → ℂ := fun i v => (a i * (r i : ℂ)) *
    ((v : ℂ) ^ (2 * s) * schlafliBesselK (1 / 3) (4 * Real.pi * ‖freq i‖ * v))
  have hi (i : ι) : IntegrableOn (F i) (Ioi 0) :=
    (source_cubic_bessel_mellin_integrable s (freq i) hs (hf i)).const_mul (a i * (r i : ℂ))
  have hsum : Summable (fun i => ∫ v : ℝ in Ioi 0, ‖F i v‖) := by
    simp only [F, weighted_cubic_bessel_integral_norm s _ _ (hf _)]
    exact has.mul_right _
  have hint := integrableOn_tsum_of_summable_norm_integrals F hi hsum
  unfold MellinConvergent
  apply (integrableOn_congr_fun (s := Ioi 0) (fun v hv => ?_) measurableSet_Ioi).mpr hint
  dsimp only [radialBesselProfile]
  simp only [smul_eq_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  dsimp only [F]
  have hp : (v : ℂ) ^ (2 * s - 1) * (v : ℂ) = (v : ℂ) ^ (2 * s) := by
    calc
      _ = (v : ℂ) ^ (2 * s - 1) * (v : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = (v : ℂ) ^ ((2 * s - 1) + 1) :=
        (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')).symm
      _ = _ := by rw [sub_add_cancel]
  have hn : ‖freq i‖ = q * Real.sqrt (r i) :=
    Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr (hr i))).le
  rw [hn, show 4 * Real.pi * q * Real.sqrt (r i) * v =
    4 * Real.pi * (q * Real.sqrt (r i)) * v by ring]
  change (v : ℂ) ^ (2 * s - 1) * _ = _
  linear_combination (a i * (r i : ℂ)) *
    schlafliBesselK (1 / 3) (4 * Real.pi * (q * Real.sqrt (r i)) * v) * hp

/-- The actual finite projector's Mellin integral exists throughout the
stated half-plane. There is no caller-supplied summability hypothesis. -/
theorem finiteProjector_mellinConvergent (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * χ.modulus)
    (s : ℂ) (hs : 3 / 2 < s.re) :
    MellinConvergent (finiteProjector χ n c hc) (2 * s + (n : ℂ)) := by
  have ht : -(1 / 3 : ℝ) < (s + (n : ℂ) / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hi := radialBesselProfile_mellinConvergent completedMellinLength
    completedMellinLength_pos (angularRadialCoefficient χ n) thetaBesselScale
    thetaBesselScale_pos (s + (n : ℂ) / 2) ht
    (angularRadialCoefficient_summable χ n s hs)
  have hscaled := hi.const_smul
    (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n)
  rw [show (2 : ℂ) * (s + (n : ℂ) / 2) = 2 * s + (n : ℂ) by ring] at hscaled
  unfold MellinConvergent at hscaled ⊢
  apply (integrableOn_congr_fun (s := Ioi 0) (fun v hv => ?_) measurableSet_Ioi).mpr hscaled
  simp only [smul_eq_mul]
  rw [finiteProjector_radial χ n hk c hc hcQ v hv]

end OAI.CubicEisenstein.AngularProjectedMellin
