import AngularProjectedReflection

/-! Actual higher-order dual radial coefficients at the three physical
cusps. The radial factor is removed exactly before using the original
weighted estimate. No coefficient-summability premise is left to a caller. -/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators MatrixGroups

namespace OAI.CubicEisenstein.AngularDualRadialCoefficients

open SevenEighths.Angular AngularProjectedReflection AngularProjectedMellin
open AngularHigherProfiles AngularBesselDerivatives AngularBesselClosure AngularProfileDirichlet
open EisensteinEmbedding ConcreteTraceCRT AngularFiniteCuspSecondReflection

local notation "Eis" => ActualEisensteinCubic.O
local instance : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

def extraScale (j : Fin 3) : ℂ :=
  -2 * Real.pi * Complex.I * thetaFrequencyScale / (sourceCuspScale j : ℂ)

/-- The literal additional n derivatives of the order-one physical array. -/
def dualRadialCoefficient (j : Fin 3) (n : ℕ) (z : ℂ) (h : Eis) : ℂ :=
  sourceCuspRadialCoefficient j z h *
    (-2 * Real.pi * Complex.I * cuspFrequency h / (sourceCuspScale j : ℂ)) ^ n

theorem dualRadialCoefficient_zero (j : Fin 3) (n : ℕ) (z : ℂ) :
    dualRadialCoefficient j n z 0 = 0 := by
  simp only [dualRadialCoefficient, sourceCuspRadialCoefficient_zero, zero_mul]

theorem dualRadialCoefficient_order_zero (j : Fin 3) (z : ℂ) :
    dualRadialCoefficient j 0 z = sourceCuspRadialCoefficient j z := by
  funext h
  simp only [dualRadialCoefficient, pow_zero, mul_one]

theorem frequency_radial_phase (h : Eis) (hh : h ≠ 0) :
    cuspFrequency h = thetaFrequencyScale * alpha h *
      (Real.sqrt (sourceCuspRadialLength h) : ℂ) := by
  rw [cuspFrequency_eq_thetaFrequencyScale, sourceCuspRadialLength, ite_eq_right hh,
    Real.sqrt_sq (norm_nonneg _)]
  have hn : (‖eisEmbedding h‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hh))
  simp only [alpha, FiniteGaussPhase.angularFactor]
  field_simp

theorem dualRadialCoefficient_split (j : Fin 3) (n : ℕ) (z : ℂ) (h : Eis) :
    dualRadialCoefficient j n z h =
      sourceCuspRadialCoefficient j z h * extraScale j ^ n * alpha h ^ n *
        (Real.sqrt (sourceCuspRadialLength h) : ℂ) ^ n := by
  by_cases hh : h = 0
  · subst h
    simp only [dualRadialCoefficient_zero, sourceCuspRadialCoefficient_zero, zero_mul]
  · have he : -2 * Real.pi * Complex.I * cuspFrequency h / (sourceCuspScale j : ℂ) =
        extraScale j * alpha h * (Real.sqrt (sourceCuspRadialLength h) : ℂ) := by
      rw [frequency_radial_phase h hh]
      unfold extraScale
      ring
    rw [dualRadialCoefficient, he, mul_pow, mul_pow]
    ring

/-- Radial normalization preserves the actual phase and all theta scales. -/
theorem dualRadialCoefficient_normalized (j : Fin 3) (n : ℕ) (z : ℂ) (h : Eis) :
    dualRadialCoefficient j n z h * (sourceCuspRadialLength h : ℂ) ^ (-(n : ℂ) / 2) =
      sourceCuspRadialCoefficient j z h * extraScale j ^ n * alpha h ^ n := by
  have hr := sourceCuspRadialLength_pos h
  have hp : (Real.sqrt (sourceCuspRadialLength h) : ℂ) ^ n *
      (sourceCuspRadialLength h : ℂ) ^ (-(n : ℂ) / 2) = 1 := by
    rw [sqrt_pow_cpow _ hr n, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hr.ne'),
      show (n : ℂ) / 2 + -(n : ℂ) / 2 = 0 by ring, Complex.cpow_zero]
  rw [dualRadialCoefficient_split, mul_assoc, hp, mul_one]

theorem dualRadialCoefficient_normalized_norm (j : Fin 3) (n : ℕ) (z : ℂ) (h : Eis) :
    ‖dualRadialCoefficient j n z h * (sourceCuspRadialLength h : ℂ) ^ (-(n : ℂ) / 2)‖ =
      ‖extraScale j‖ ^ n * ‖sourceCuspRadialCoefficient j z h‖ := by
  rw [dualRadialCoefficient_normalized]
  by_cases hh : h = 0
  · subst h
    simp only [sourceCuspRadialCoefficient_zero, zero_mul, norm_zero, mul_zero]
  · rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_alpha hh, one_pow, mul_one]
    ring

theorem sqrt_weight_cancel (r : ℝ) (hr : 0 < r) (n : ℕ) :
    Real.sqrt r ^ n * r ^ (-(3 / 2 : ℝ) - (n : ℝ) / 2) = r ^ (-(3 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
  congr 1
  ring

/-- The extra physical derivative powers cancel in the weighted norm. -/
theorem dualRadialCoefficient_weighted_norm (j : Fin 3) (n : ℕ) (z : ℂ) (h : Eis) :
    ‖dualRadialCoefficient j n z h‖ *
        sourceCuspRadialLength h ^ (-(3 / 2 : ℝ) - (n : ℝ) / 2) =
      ‖extraScale j‖ ^ n * (‖sourceCuspRadialCoefficient j z h‖ *
        sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
  by_cases hh : h = 0
  · subst h
    simp only [dualRadialCoefficient_zero, sourceCuspRadialCoefficient_zero,
      norm_zero, zero_mul, mul_zero]
  · rw [dualRadialCoefficient_split]
    simp only [norm_mul, norm_pow, norm_alpha hh, one_pow, mul_one,
      Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_assoc, sqrt_weight_cancel _ (sourceCuspRadialLength_pos h) n]
    ring

/-- Genuine physical summability on the required reflected line. -/
theorem dualRadialCoefficient_weighted_summable (j : Fin 3) (n : ℕ) (z : ℂ) :
    Summable (fun h : Eis => ‖dualRadialCoefficient j n z h‖ *
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ) - (n : ℝ) / 2)) := by
  exact ((sourceCuspRadialCoefficient_weighted_summable j z).mul_left (‖extraScale j‖ ^ n)).congr
    (fun h => (dualRadialCoefficient_weighted_norm j n z h).symm)

theorem dualRadialCoefficient_normalized_summable (j : Fin 3) (n : ℕ) (z : ℂ) :
    Summable (fun h : Eis =>
      ‖dualRadialCoefficient j n z h * (sourceCuspRadialLength h : ℂ) ^ (-(n : ℂ) / 2)‖ *
        sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
  apply ((sourceCuspRadialCoefficient_weighted_summable j z).mul_left (‖extraScale j‖ ^ n)).congr
  intro h
  rw [dualRadialCoefficient_normalized_norm]
  ring

/-- The actual conjugate Z-derivative Fourier expansion, including the
unmodified constant in the source before differentiation. -/
theorem conjugate_zProfile_full_fourier (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (n : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    zProfile (fun w => star (coeff.fullFunction constant w)) (n + 1) z v =
      ∑' h : NonzeroFrequency,
        (-derivativeScalar * cuspFrequency h.val) ^ (n + 1) * star (coeff.value h.val) *
          (v : ℂ) * schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v) *
            ShortDraftTrace.breveE (-cuspFrequency h.val * z) := by
  rw [zProfile_star]
  change star (barProfile (coeff.fullFunction constant) (n + 1) z v) = _
  rw [barProfile_full_fourier coeff constant n z v hv, tsum_star]
  apply tsum_congr
  intro h
  have hx : 0 < 4 * Real.pi * ‖cuspFrequency h.val‖ * v := by
    have hf := norm_pos_iff.mpr (cuspFrequency_ne_zero h.val h.property)
    positivity
  have hD : star derivativeScalar = -derivativeScalar := by
    simp only [derivativeScalar, star_mul, Complex.star_def, map_ofNat,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [schlafliBesselK_cubic_real _ hx]
  simp only [barCoefficient, star_mul, star_pow, hD, breveE_star,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_conj, neg_mul]
  ring

/-- Exact physical dual Z-profile to radial Bessel series. In particular,
the coefficient is the higher-order array, not the order-one array. -/
theorem datumDualProfile_eq_radial (n : ℕ) (d : SourceCuspDatum) (v : ℝ) (hv : 0 < v) :
    datumDualProfile (n + 1) d v =
      radialBesselProfile sourceCuspRadialLength (dualRadialCoefficient d.index n d.dualPoint)
        (sourceCuspRadialScale d.index) v := by
  rw [datumDualProfile_scaled (n + 1) d v hv,
    conjugate_zProfile_full_fourier _ _ n _ _ (div_pos hv (sourceCuspScale_pos d.index)),
    ← tsum_mul_left]
  unfold radialBesselProfile
  rw [← tsum_subtype_eq_of_support_subset
    (f := fun h : Eis => (dualRadialCoefficient d.index n d.dualPoint h *
      (sourceCuspRadialLength h : ℂ)) * (v : ℂ) * schlafliBesselK (1 / 3)
        (4 * Real.pi * sourceCuspRadialScale d.index * Real.sqrt (sourceCuspRadialLength h) * v))
    (s := {h : Eis | h ≠ 0}) (by
      intro h hh hz
      subst h
      exact hh (by simp only [dualRadialCoefficient_zero, zero_mul]))]
  apply tsum_congr
  intro h
  have hs0 : (sourceCuspScale d.index : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos d.index).ne'
  have hr0 : (sourceCuspRadialLength h.val : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sourceCuspRadialLength_pos h.val).ne'
  rw [sourceCuspRadialLength_frequency h.val h.property]
  have hb : 4 * Real.pi * (thetaBesselScale * Real.sqrt (sourceCuspRadialLength h.val)) *
      (v / sourceCuspScale d.index) =
      4 * Real.pi * sourceCuspRadialScale d.index * Real.sqrt (sourceCuspRadialLength h.val) * v := by
    unfold sourceCuspRadialScale
    ring
  rw [hb]
  have hD : -derivativeScalar = -2 * Real.pi * Complex.I := by unfold derivativeScalar; ring
  rw [hD]
  simp only [dualRadialCoefficient, sourceCuspRadialCoefficient, sourceCuspRadialBaseCoefficient,
    Complex.ofReal_div, pow_succ, mul_pow, div_pow, inv_pow]
  field_simp [hs0, hr0]

end OAI.CubicEisenstein.AngularDualRadialCoefficients
