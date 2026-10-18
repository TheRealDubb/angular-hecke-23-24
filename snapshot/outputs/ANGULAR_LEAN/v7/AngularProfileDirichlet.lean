import AngularHigherProfiles
import OAI.NumberTheory.DirichletL.Eisenstein.FullFrequencyExpansion

/-! The actual positive-order physical source profiles have their exact
shifted-gamma Dirichlet coefficient formula on Re(s)=2. The fourth-weight
summability hypothesis in the analytic helper is discharged for the physical
source and conjugate source. No canonical moment estimate is asserted. -/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators

namespace OAI.CubicEisenstein.AngularProfileDirichlet

open AngularHigherProfiles AngularBesselClosure AngularBesselDerivatives
open EisensteinEmbedding ConcreteTraceCRT

abbrev Eis := ActualEisensteinCubic.O
abbrev NonzeroFrequency := {h : Eis // h ≠ 0}

local instance : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

def barCoefficient (coeff : SubexponentialBesselCoefficients) (j : ℕ)
    (z : ℂ) (h : NonzeroFrequency) : ℂ :=
  (derivativeScalar * star (cuspFrequency h.val)) ^ j * coeff.value h.val *
    ShortDraftTrace.breveE (cuspFrequency h.val * z)

def conjugateBarCoefficient (coeff : SubexponentialBesselCoefficients) (j : ℕ)
    (z : ℂ) (h : NonzeroFrequency) : ℂ :=
  (-derivativeScalar * star (cuspFrequency h.val)) ^ j * star (coeff.value h.val) *
    ShortDraftTrace.breveE (-cuspFrequency h.val * z)

def mellinCoefficient (j : ℕ) (s : ℂ) (h : NonzeroFrequency) : ℂ :=
  ((2 : ℂ) ^ (2 * s + (j : ℂ) - 2) *
    Complex.Gamma (s + (j : ℂ) / 2 - 1 / 6) *
    Complex.Gamma (s + (j : ℂ) / 2 + 1 / 6)) /
      ((4 * Real.pi * ‖cuspFrequency h.val‖ : ℝ) : ℂ) ^ (2 * s + (j : ℂ))

theorem series_eq_nonzero (coeff : SubexponentialBesselCoefficients)
    (v : ℝ) (hv : 0 < v) (z : ℂ) :
    coeff.series (v, z) = ∑' h : NonzeroFrequency,
      coeff.value h.val * (v : ℂ) *
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v) *
          ShortDraftTrace.breveE (cuspFrequency h.val * z) := by
  unfold SubexponentialBesselCoefficients.series
  rw [← tsum_subtype_eq_of_support_subset (s := {h : Eis | h ≠ 0}) (by
    intro h hh hz
    subst h
    exact hh (by simp [SubexponentialBesselCoefficients.term]))]
  exact tsum_congr (fun h => coeff.term_bessel h.val h.property v hv z)

theorem barProfile_full_fourier (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (n : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    barProfile (coeff.fullFunction constant) (n + 1) z v =
      ∑' h : NonzeroFrequency, barCoefficient coeff (n + 1) z h * (v : ℂ) *
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v) := by
  rw [barProfile_full_eq coeff constant n z v hv, series_eq_nonzero _ v hv z,
    ← tsum_mul_left]
  apply tsum_congr
  intro h
  simp only [conjugateFrequencyPow_value, barCoefficient, mul_pow]
  ring

theorem conjugate_barProfile_full_fourier (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (n : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    barProfile (fun w => star (coeff.fullFunction constant w)) (n + 1) z v =
      ∑' h : NonzeroFrequency, conjugateBarCoefficient coeff (n + 1) z h * (v : ℂ) *
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v) := by
  rw [barProfile_star]
  change star (zProfile (coeff.fullFunction constant) (n + 1) z v) = _
  rw [zProfile_full_eq coeff constant n z v hv,
    series_eq_nonzero _ v hv z, star_mul, tsum_star, ← tsum_mul_right]
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
  simp only [frequencyPow_value, conjugateBarCoefficient,
    star_mul, star_pow, hD, breveE_star, Complex.star_def,
    Complex.conj_ofReal, neg_mul, mul_pow]
  ring

theorem barCoefficient_norm (coeff : SubexponentialBesselCoefficients)
    (j : ℕ) (z : ℂ) (h : NonzeroFrequency) :
    ‖barCoefficient coeff j z h‖ =
      ‖derivativeScalar‖ ^ j * ‖cuspFrequency h.val‖ ^ j * ‖coeff.value h.val‖ := by
  simp only [barCoefficient, norm_mul, norm_pow, norm_star, breveE_norm, mul_one, mul_pow]

theorem conjugateBarCoefficient_norm (coeff : SubexponentialBesselCoefficients)
    (j : ℕ) (z : ℂ) (h : NonzeroFrequency) :
    ‖conjugateBarCoefficient coeff j z h‖ =
      ‖derivativeScalar‖ ^ j * ‖cuspFrequency h.val‖ ^ j * ‖coeff.value h.val‖ := by
  simp only [conjugateBarCoefficient, norm_mul, norm_pow, norm_star, norm_neg,
    breveE_norm, mul_one, mul_pow]

theorem frequency_power_cancel (r : ℝ) (hr : 0 < r) (j : ℕ)
    (s : ℂ) (hs : s.re = 2) :
    r ^ j * r ^ (-(2 * (s + ((j : ℂ) - 1) / 2).re + 1)) = r ^ (-4 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hr]
  congr 1
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.sub_re,
    Complex.natCast_re, Complex.one_re, hs]
  ring

theorem coefficient_mellin_summable (coeff : SubexponentialBesselCoefficients)
    (hfourth : Summable (fun h : Eis => if h = 0 then (0 : ℝ) else
      ‖coeff.value h‖ * ‖cuspFrequency h‖ ^ (-4 : ℝ)))
    (j : ℕ) (a : NonzeroFrequency → ℂ)
    (ha : ∀ h, ‖a h‖ =
      ‖derivativeScalar‖ ^ j * ‖cuspFrequency h.val‖ ^ j * ‖coeff.value h.val‖)
    (s : ℂ) (hs : s.re = 2) :
    Summable (fun h : NonzeroFrequency => ‖a h‖ *
      ‖cuspFrequency h.val‖ ^ (-(2 * (s + ((j : ℂ) - 1) / 2).re + 1))) := by
  have hf : Summable (fun h : NonzeroFrequency =>
      ‖coeff.value h.val‖ * ‖cuspFrequency h.val‖ ^ (-4 : ℝ)) := by
    apply (hfourth.subtype (fun h => h ≠ 0)).congr
    intro h
    simp only [Function.comp_apply, ite_eq_right h.property]
  apply (hf.mul_left (‖derivativeScalar‖ ^ j)).congr
  intro h
  rw [ha h]
  have hc := frequency_power_cancel ‖cuspFrequency h.val‖
    (norm_pos_iff.mpr (cuspFrequency_ne_zero h.val h.property)) j s hs
  rw [← hc]
  ring

theorem profile_mellin_line_two (f : ℝ → ℂ) (j : ℕ)
    (a : NonzeroFrequency → ℂ) (s : ℂ) (hs : s.re = 2)
    (ha : Summable (fun h : NonzeroFrequency => ‖a h‖ *
      ‖cuspFrequency h.val‖ ^ (-(2 * (s + ((j : ℂ) - 1) / 2).re + 1))))
    (hf : ∀ v : ℝ, 0 < v → f v = ∑' h : NonzeroFrequency,
      a h * (v : ℂ) *
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v)) :
    mellin f (2 * s + (j : ℂ) - 1) =
      ∑' h : NonzeroFrequency, a h * mellinCoefficient j s h := by
  let t : ℂ := s + ((j : ℂ) - 1) / 2
  have ht : -(1 / 3 : ℝ) < t.re := by
    dsimp [t]
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.sub_re,
      Complex.natCast_re, Complex.one_re, hs]
    have hj := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hm := cubic_bessel_series_mellin (fun h : NonzeroFrequency => cuspFrequency h.val)
    a (fun h => cuspFrequency_ne_zero h.val h.property) t ht ha
  calc
    _ = ∫ v : ℝ in Ioi 0, ∑' h : NonzeroFrequency,
        a h * ((v : ℂ) ^ (2 * t) *
          schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v)) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      simp only [smul_eq_mul, hf v hv, ← tsum_mul_left]
      apply tsum_congr
      intro h
      have hp : (v : ℂ) ^ (2 * s + (j : ℂ) - 1 - 1) * (v : ℂ) =
          (v : ℂ) ^ (2 * t) := by
        calc
          _ = (v : ℂ) ^ (2 * s + (j : ℂ) - 1 - 1) * (v : ℂ) ^ (1 : ℂ) :=
            by rw [Complex.cpow_one]
          _ = (v : ℂ) ^ ((2 * s + (j : ℂ) - 1 - 1) + 1) :=
            (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')).symm
          _ = _ := by congr 1; dsimp [t]; ring
      calc
        _ = a h * (((v : ℂ) ^ (2 * s + (j : ℂ) - 1 - 1) * (v : ℂ)) *
            schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v)) := by ring
        _ = _ := by rw [hp]
    _ = _ := by
      rw [hm]
      apply tsum_congr
      intro h
      unfold mellinCoefficient
      have h1 : 2 * t - 1 = 2 * s + (j : ℂ) - 2 := by dsimp [t]; ring
      have h2 : t + 1 / 3 = s + (j : ℂ) / 2 - 1 / 6 := by dsimp [t]; ring
      have h3 : t + 2 / 3 = s + (j : ℂ) / 2 + 1 / 6 := by dsimp [t]; ring
      have h4 : 2 * t + 1 = 2 * s + (j : ℂ) := by dsimp [t]; ring
      rw [h1, h2, h3, h4]

theorem barProfile_full_mellin_line_two (coeff : SubexponentialBesselCoefficients)
    (hfourth : Summable (fun h : Eis => if h = 0 then (0 : ℝ) else
      ‖coeff.value h‖ * ‖cuspFrequency h‖ ^ (-4 : ℝ)))
    (constant : ℂ) (n : ℕ) (z s : ℂ) (hs : s.re = 2) :
    mellin (barProfile (coeff.fullFunction constant) (n + 1) z)
      (2 * s + ((n + 1 : ℕ) : ℂ) - 1) =
      ∑' h : NonzeroFrequency, barCoefficient coeff (n + 1) z h *
        mellinCoefficient (n + 1) s h := by
  exact profile_mellin_line_two _ (n + 1) _ s hs
    (coefficient_mellin_summable coeff hfourth (n + 1) _
      (barCoefficient_norm coeff (n + 1) z) s hs)
    (barProfile_full_fourier coeff constant n z)

theorem conjugate_barProfile_full_mellin_line_two (coeff : SubexponentialBesselCoefficients)
    (hfourth : Summable (fun h : Eis => if h = 0 then (0 : ℝ) else
      ‖coeff.value h‖ * ‖cuspFrequency h‖ ^ (-4 : ℝ)))
    (constant : ℂ) (n : ℕ) (z s : ℂ) (hs : s.re = 2) :
    mellin (barProfile (fun w => star (coeff.fullFunction constant w)) (n + 1) z)
      (2 * s + ((n + 1 : ℕ) : ℂ) - 1) =
      ∑' h : NonzeroFrequency, conjugateBarCoefficient coeff (n + 1) z h *
        mellinCoefficient (n + 1) s h := by
  exact profile_mellin_line_two _ (n + 1) _ s hs
    (coefficient_mellin_summable coeff hfourth (n + 1) _
      (conjugateBarCoefficient_norm coeff (n + 1) z) s hs)
    (conjugate_barProfile_full_fourier coeff constant n z)

/-- Actual residual source; the summability input is proved from its physical
Fourier coefficients, not imposed on the caller. -/
theorem source_barProfile_mellin_line_two (n : ℕ) (z s : ℂ) (hs : s.re = 2) :
    mellin (barProfile cubicSourceResidualFunction (n + 1) z)
      (2 * s + ((n + 1 : ℕ) : ℂ) - 1) =
      ∑' h : NonzeroFrequency, barCoefficient sourceBesselCoefficients (n + 1) z h *
        mellinCoefficient (n + 1) s h := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact barProfile_full_mellin_line_two sourceBesselCoefficients
    three_cusp_coefficients_weighted_summable.1 _ n z s hs

/-- Actual conjugate source, retaining the sign and conjugate frequency of
every derivative and the negative horizontal phase. -/
theorem source_conjugate_barProfile_mellin_line_two (n : ℕ) (z s : ℂ) (hs : s.re = 2) :
    mellin (barProfile cubicSourceConjugateFunction (n + 1) z)
      (2 * s + ((n + 1 : ℕ) : ℂ) - 1) =
      ∑' h : NonzeroFrequency, conjugateBarCoefficient sourceBesselCoefficients (n + 1) z h *
        mellinCoefficient (n + 1) s h := by
  unfold cubicSourceConjugateFunction
  rw [cubicSourceResidualFunction_eq_bessel]
  exact conjugate_barProfile_full_mellin_line_two sourceBesselCoefficients
    three_cusp_coefficients_weighted_summable.1 _ n z s hs

end OAI.CubicEisenstein.AngularProfileDirichlet
