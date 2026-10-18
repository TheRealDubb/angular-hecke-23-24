import AngularThetaBasic
import AngularMellinShift
import AngularElementSeries

/-! Mellin identification of the actual centered angular theta with the actual
ideal series in Re(s)>1. No continued L-function or zero-free theorem is asserted. -/

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace OAI.SevenEighths.Angular.ThetaMellin

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open OAI.SevenEighths.Angular.Polynomial MellinShift

theorem coefficient_cpow_shift (χ : AngularCharacter) (A : ℝ) (hA : 0 < A)
    (s : ℂ) (a : O) :
    centeredWeightedCoeff χ a /
        ((A * ‖eisEmbedding a‖ ^ 2 : ℝ) : ℂ) ^ (s + (χ.k.natAbs : ℂ) / 2) =
      (A : ℂ) ^ (-(s + (χ.k.natAbs : ℂ) / 2)) * χ.elementDirichletTerm s a := by
  by_cases ha : a = 0
  · simp [ha, centeredWeightedCoeff]
  have hr : 0 < ‖eisEmbedding a‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero ha)
  rw [centeredWeightedCoeff_eq, χ.elementDirichletTerm_eq_embedding s a]
  calc
    _ = χ.elementCoeff a * ((‖eisEmbedding a‖ : ℂ) ^ χ.k.natAbs /
        ((A * ‖eisEmbedding a‖ ^ 2 : ℝ) : ℂ) ^ (s + (χ.k.natAbs : ℂ) / 2)) := by ring
    _ = _ := by rw [scaled_cpow_shift A _ hA hr]; ring

theorem coefficient_norm_shift (χ : AngularCharacter) (A : ℝ) (hA : 0 < A)
    (s : ℂ) (a : O) :
    ‖centeredWeightedCoeff χ a‖ /
        (A * ‖eisEmbedding a‖ ^ 2) ^ (s + (χ.k.natAbs : ℂ) / 2).re =
      A ^ (-(s + (χ.k.natAbs : ℂ) / 2).re) * ‖χ.elementDirichletTerm s a‖ := by
  by_cases ha : a = 0
  · simp [ha, centeredWeightedCoeff]
  have hr : 0 < ‖eisEmbedding a‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero ha)
  have hre : (s + (χ.k.natAbs : ℂ) / 2).re = s.re + (χ.k.natAbs : ℝ) / 2 := by simp
  rw [centeredWeightedCoeff_eq, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    χ.norm_elementDirichletTerm_eq_embedding s a, hre]
  calc
    _ = ‖χ.elementCoeff a‖ * (‖eisEmbedding a‖ ^ χ.k.natAbs /
        (A * ‖eisEmbedding a‖ ^ 2) ^ (s.re + (χ.k.natAbs : ℝ) / 2)) := by ring
    _ = _ := by rw [scaled_rpow_shift A _ hA hr]; ring

theorem shifted_norm_summable (χ : AngularCharacter) (A : ℝ) (hA : 0 < A)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun a : O => ‖centeredWeightedCoeff χ a‖ /
      (A * ‖eisEmbedding a‖ ^ 2) ^ (s + (χ.k.natAbs : ℂ) / 2).re) := by
  simp_rw [coefficient_norm_shift χ A hA s]
  exact (χ.summable_norm_elementDirichletTerm s hs).mul_left _

theorem gaussian_eq_real_exp (A t : ℝ) (z : ℂ) :
    GaussianTheta.gaussian (A * t) z =
      (Real.exp (-Real.pi * (A * ‖z‖ ^ 2) * t) : ℂ) := by
  rw [GaussianTheta.gaussian, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem centeredTheta_mellin (χ : AngularCharacter) (A : ℝ) (hA : 0 < A)
    (s : ℂ) (hs : 1 < s.re) :
    mellin (centeredTheta χ A) (s + (χ.k.natAbs : ℂ) / 2) =
      6 * Complex.Gamma (s + (χ.k.natAbs : ℂ) / 2) *
        ((Real.pi * A : ℝ) : ℂ) ^ (-(s + (χ.k.natAbs : ℂ) / 2)) * χ.series s := by
  let : Countable O := latticeCoordEquiv.countable_iff.mpr inferInstance
  let S : ℂ := s + (χ.k.natAbs : ℂ) / 2
  have hS : 0 < S.re := by
    dsimp [S]
    simp only [Complex.div_ofNat_re, Complex.natCast_re]
    positivity
  have hp (a : O) : centeredWeightedCoeff χ a = 0 ∨ 0 < A * ‖eisEmbedding a‖ ^ 2 := by
    by_cases ha : a = 0
    · left; simp [centeredWeightedCoeff, ha]
    · right; exact mul_pos hA (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero ha)))
  have ht (t : ℝ) (ht : t ∈ Set.Ioi 0) :
      HasSum (fun a : O => centeredWeightedCoeff χ a *
        (Real.exp (-Real.pi * (A * ‖eisEmbedding a‖ ^ 2) * t) : ℂ))
        (centeredTheta χ A t) := by
    simpa only [gaussian_eq_real_exp] using centeredTheta_hasSum χ A t hA ht
  have hM := hasSum_mellin_pi_mul hp hS ht (shifted_norm_summable χ A hA s hs)
  have hterms (a : O) :
      (Real.pi : ℂ) ^ (-S) * Complex.Gamma S * centeredWeightedCoeff χ a /
        ((A * ‖eisEmbedding a‖ ^ 2 : ℝ) : ℂ) ^ S =
      ((Real.pi : ℂ) ^ (-S) * Complex.Gamma S * (A : ℂ) ^ (-S)) *
        χ.elementDirichletTerm s a := by
    rw [mul_div_assoc, coefficient_cpow_shift χ A hA s]
    ring
  have hM' : HasSum (fun a : O =>
      ((Real.pi : ℂ) ^ (-S) * Complex.Gamma S * (A : ℂ) ^ (-S)) *
        χ.elementDirichletTerm s a) (mellin (centeredTheta χ A) S) := by
    simpa only [hterms] using hM
  have he := hM'.unique ((χ.hasSum_elementDirichletTerm s hs).mul_left
    ((Real.pi : ℂ) ^ (-S) * Complex.Gamma S * (A : ℂ) ^ (-S)))
  change mellin (centeredTheta χ A) S = _
  rw [he, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le hA.le]
  dsimp [S]
  ring

end OAI.SevenEighths.Angular.ThetaMellin
