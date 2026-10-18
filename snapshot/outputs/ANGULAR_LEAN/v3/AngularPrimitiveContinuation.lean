import AngularThetaFEPair
import AngularMellinConvergence
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Actual primitive angular L-functions: analytic continuation constructed
from theta, agreement with the physical ideal series, and the shifted completed
functional equation. This file asserts no zero-free strip beyond Re(s)>1. -/

noncomputable section
open scoped Classical Topology

namespace OAI.SevenEighths.Angular.ThetaContinuation

open ActualEisensteinCubic ConcreteTraceCRT
open OAI.SevenEighths.Angular.Polynomial ThetaMellin ThetaTransform

variable (c : O) [NeZero c] (χ : AngularCharacter)
  (hmod : χ.modulus = Ideal.span {c})
  (hχ : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue))

include hχ

theorem pair_hasMellin_centered (s : ℂ) (hs : 1 < s.re) :
    HasMellin (centeredTheta χ (GaussianTheta.parameter c 1))
      (s + (χ.k.natAbs : ℂ) / 2)
      ((pair c χ hmod hχ).Λ (s + (χ.k.natAbs : ℂ) / 2)) := by
  change HasMellin (fun t => (pair c χ hmod hχ).f t - (pair c χ hmod hχ).f₀) _ _
  by_cases hk : χ.k = 0
  · apply (pair c χ hmod hχ).hasMellin
    simpa only [pair, hk, Int.natAbs_zero, Nat.zero_add, Nat.cast_one,
      Nat.cast_zero, zero_div, add_zero] using hs
  · have hstrong := pair_strong c χ hmod hχ hk
    simpa only [hstrong.hf₀, sub_zero] using
      hstrong.hasMellin (s + (χ.k.natAbs : ℂ) / 2)

theorem completed_eq_series (s : ℂ) (hs : 1 < s.re) :
    completed c χ hmod hχ s =
      Complex.Gamma (s + (χ.k.natAbs : ℂ) / 2) *
        ((Real.pi * GaussianTheta.parameter c 1 : ℝ) : ℂ) ^
          (-(s + (χ.k.natAbs : ℂ) / 2)) * χ.series s := by
  have h := (pair_hasMellin_centered c χ hmod hχ s hs).2.symm.trans
    (centeredTheta_hasMellin χ _ (GaussianTheta.parameter_pos c 1 zero_lt_one) s hs).2
  unfold completed
  rw [h]
  ring

theorem pairDual_hasMellin_centered (s : ℂ) (hs : 1 < s.re) :
    HasMellin (centeredTheta χ.conjugate (GaussianTheta.parameter c 1))
      (s + (χ.k.natAbs : ℂ) / 2)
      ((pair c χ hmod hχ).symm.Λ (s + (χ.k.natAbs : ℂ) / 2)) := by
  change HasMellin
    (fun t => (pair c χ hmod hχ).symm.f t - (pair c χ hmod hχ).symm.f₀) _ _
  by_cases hk : χ.k = 0
  · apply (pair c χ hmod hχ).symm.hasMellin
    simpa only [WeakFEPair.symm, pair, hk, Int.natAbs_zero, Nat.zero_add,
      Nat.cast_one, Nat.cast_zero, zero_div, add_zero] using hs
  · have hstrong := (pair_strong c χ hmod hχ hk).symm
    simpa only [hstrong.hf₀, sub_zero] using
      hstrong.hasMellin (s + (χ.k.natAbs : ℂ) / 2)

theorem completedDual_eq_series (s : ℂ) (hs : 1 < s.re) :
    completedDual c χ hmod hχ s =
      Complex.Gamma (s + (χ.k.natAbs : ℂ) / 2) *
        ((Real.pi * GaussianTheta.parameter c 1 : ℝ) : ℂ) ^
          (-(s + (χ.k.natAbs : ℂ) / 2)) * χ.conjugate.series s := by
  have hm := centeredTheta_hasMellin χ.conjugate _
    (GaussianTheta.parameter_pos c 1 zero_lt_one) s hs
  simp only [AngularCharacter.conjugate_k, Int.natAbs_neg] at hm
  have h := (pairDual_hasMellin_centered c χ hmod hχ s hs).2.symm.trans hm.2
  unfold completedDual
  rw [h]
  ring

/-- The entire factor removing the Gamma and conductor factors. -/
def decompleteFactor (s : ℂ) : ℂ :=
  ((Real.pi * GaussianTheta.parameter c 1 : ℝ) : ℂ) ^ (s + (χ.k.natAbs : ℂ) / 2) *
    (Complex.Gamma (s + (χ.k.natAbs : ℂ) / 2))⁻¹

omit hχ in
theorem decompleteFactor_differentiable : Differentiable ℂ (decompleteFactor c χ) := by
  have hbase : ((Real.pi * GaussianTheta.parameter c 1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (mul_pos Real.pi_pos (GaussianTheta.parameter_pos c 1 zero_lt_one)).ne'
  exact ((differentiable_id.add_const _).const_cpow (Or.inl hbase)).mul
    (Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _))

/-- Continued primitive angular L-function defined by the proved theta pair. -/
def LFunction (s : ℂ) : ℂ := decompleteFactor c χ s * completed c χ hmod hχ s

theorem LFunction_differentiable (hk : χ.k ≠ 0) :
    Differentiable ℂ (LFunction c χ hmod hχ) :=
  (decompleteFactor_differentiable c χ).mul (completed_differentiable c χ hmod hχ hk)

omit hχ in
theorem shifted_re_pos (s : ℂ) (hs : 0 < s.re) : 0 < (s + (χ.k.natAbs : ℂ) / 2).re := by
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
  positivity

omit hχ in
theorem decompleteFactor_cancel (s : ℂ) (hs : 0 < s.re) (z : ℂ) :
    decompleteFactor c χ s *
      (Complex.Gamma (s + (χ.k.natAbs : ℂ) / 2) *
        ((Real.pi * GaussianTheta.parameter c 1 : ℝ) : ℂ) ^
          (-(s + (χ.k.natAbs : ℂ) / 2)) * z) = z := by
  have hg := Complex.Gamma_ne_zero_of_re_pos (shifted_re_pos χ s hs)
  have hb : ((Real.pi * GaussianTheta.parameter c 1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (mul_pos Real.pi_pos (GaussianTheta.parameter_pos c 1 zero_lt_one)).ne'
  have hp : ((Real.pi * GaussianTheta.parameter c 1 : ℝ) : ℂ) ^
      (s + (χ.k.natAbs : ℂ) / 2) ≠ 0 := by
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hb)
  unfold decompleteFactor
  rw [Complex.cpow_neg]
  calc
    _ = (((Real.pi * GaussianTheta.parameter c 1 : ℝ) : ℂ) ^
        (s + (χ.k.natAbs : ℂ) / 2) *
        (((Real.pi * GaussianTheta.parameter c 1 : ℝ) : ℂ) ^
          (s + (χ.k.natAbs : ℂ) / 2))⁻¹) *
        ((Complex.Gamma (s + (χ.k.natAbs : ℂ) / 2))⁻¹ *
          Complex.Gamma (s + (χ.k.natAbs : ℂ) / 2)) * z := by ring
    _ = z := by rw [mul_inv_cancel₀ hp, inv_mul_cancel₀ hg, one_mul, one_mul]

theorem LFunction_eq_series (s : ℂ) (hs : 1 < s.re) :
    LFunction c χ hmod hχ s = χ.series s := by
  rw [LFunction, completed_eq_series c χ hmod hχ s hs]
  exact decompleteFactor_cancel c χ s (lt_trans zero_lt_one hs) _

theorem LFunction_ne_zero (s : ℂ) (hs : 1 < s.re) :
    LFunction c χ hmod hχ s ≠ 0 := by
  rw [LFunction_eq_series c χ hmod hχ s hs]
  exact χ.series_ne_zero s hs

theorem LFunction_differentiableAt (s : ℂ) (hs : 0 < s.re) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (LFunction c χ hmod hχ) s := by
  by_cases hk : χ.k = 0
  · have h0 : s ≠ 0 := by intro he; simp [he] at hs
    apply (decompleteFactor_differentiable c χ s).mul
    apply completed_differentiableAt c χ hmod hχ s
    · left
      simpa only [hk, Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero] using h0
    · left
      simpa only [hk, Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero, zero_add] using h1
  · exact LFunction_differentiable c χ hmod hχ hk s

end OAI.SevenEighths.Angular.ThetaContinuation
