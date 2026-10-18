import AngularThetaDecay
import AngularThetaTransform
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-! The actual primitive angular theta functions form a weak FE pair. Every
analytic field is proved from the physical Schwartz theta series. Nonzero
angular types give strong FE pairs; type zero retains its origin constants. -/

noncomputable section
open scoped Classical Topology
open Set Filter MeasureTheory

namespace OAI.SevenEighths.Angular.ThetaContinuation

open ActualEisensteinCubic ConcreteTraceCRT
open OAI.SevenEighths.Angular.Polynomial ThetaMellin ThetaTransform

theorem theta_continuousOn (χ : AngularCharacter) (A : ℝ) (hA : 0 < A) :
    ContinuousOn (theta χ A) (Ioi 0) := by
  have h : ContinuousOn (fun t => centeredTheta χ A t + weightedCoeff χ 0) (Ioi 0) :=
    (centeredTheta_continuousOn χ A hA).add continuousOn_const
  simpa only [centeredTheta, sub_add_cancel] using h

theorem theta_locallyIntegrableOn (χ : AngularCharacter) (A : ℝ) (hA : 0 < A) :
    LocallyIntegrableOn (theta χ A) (Ioi 0) :=
  (theta_continuousOn χ A hA).locallyIntegrableOn measurableSet_Ioi

variable (c : O) [NeZero c] (χ : AngularCharacter)
  (hmod : χ.modulus = Ideal.span {c})
  (hχ : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue))

include hχ

theorem theta_reflection_for_pair (x : ℝ) (hx : 0 < x) :
    theta χ (GaussianTheta.parameter c 1) (1 / x) =
      (epsilon c χ.k (hmod ▸ χ.residue) *
        (x : ℂ) ^ (χ.k.natAbs + 1)) * theta χ.conjugate (GaussianTheta.parameter c 1) x := by
  have h := theta_functional_equation c χ hmod hχ (1 / x) (one_div_pos.mpr hx)
  simpa only [one_div, Complex.ofReal_inv, inv_pow, div_inv_eq_mul, inv_inv, one_mul] using h

/-- The genuine theta FE pair, including all analytic obligations. -/
def pair : WeakFEPair ℂ where
  f := theta χ (GaussianTheta.parameter c 1)
  g := theta χ.conjugate (GaussianTheta.parameter c 1)
  k := ((χ.k.natAbs + 1 : ℕ) : ℝ)
  ε := epsilon c χ.k (hmod ▸ χ.residue)
  f₀ := weightedCoeff χ 0
  g₀ := weightedCoeff χ.conjugate 0
  hf_int := theta_locallyIntegrableOn χ _ (GaussianTheta.parameter_pos c 1 zero_lt_one)
  hg_int := theta_locallyIntegrableOn χ.conjugate _ (GaussianTheta.parameter_pos c 1 zero_lt_one)
  hk := by positivity
  hε := norm_ne_zero_iff.mp (by rw [norm_epsilon c χ.k _ hχ]; exact one_ne_zero)
  h_feq x hx := by
    simpa only [Real.rpow_natCast, Complex.ofReal_pow, smul_eq_mul] using
      theta_reflection_for_pair c χ hmod hχ x hx
  hf_top := centeredTheta_rapidDecay χ _ (GaussianTheta.parameter_pos c 1 zero_lt_one)
  hg_top := centeredTheta_rapidDecay χ.conjugate _ (GaussianTheta.parameter_pos c 1 zero_lt_one)

theorem pair_strong (hk : χ.k ≠ 0) : IsStrongFEPair (pair c χ hmod hχ) := by
  constructor <;> simp [pair, weightedCoeff_origin, hk]

/-- Completed continuation in the arithmetic variable, including the exact
half-degree shift and the six-element unit group normalization. -/
def completed (s : ℂ) : ℂ :=
  (pair c χ hmod hχ).Λ (s + (χ.k.natAbs : ℂ) / 2) / 6

/-- The companion continuation uses the actual conjugate theta function. -/
def completedDual (s : ℂ) : ℂ :=
  (pair c χ hmod hχ).symm.Λ (s + (χ.k.natAbs : ℂ) / 2) / 6

theorem completed_differentiable (hk : χ.k ≠ 0) :
    Differentiable ℂ (completed c χ hmod hχ) := by
  have h := (pair_strong c χ hmod hχ hk).differentiable_Λ
  exact (h.comp (differentiable_id.add_const _)).div_const 6

theorem completedDual_differentiable (hk : χ.k ≠ 0) :
    Differentiable ℂ (completedDual c χ hmod hχ) := by
  have h := (pair_strong c χ hmod hχ hk).symm.differentiable_Λ
  exact (h.comp (differentiable_id.add_const _)).div_const 6

theorem completed_differentiableAt (s : ℂ)
    (h0 : s + (χ.k.natAbs : ℂ) / 2 ≠ 0 ∨ weightedCoeff χ 0 = 0)
    (h1 : s + (χ.k.natAbs : ℂ) / 2 ≠ (χ.k.natAbs : ℂ) + 1 ∨
      weightedCoeff χ.conjugate 0 = 0) :
    DifferentiableAt ℂ (completed c χ hmod hχ) s := by
  have h := (pair c χ hmod hχ).differentiableAt_Λ h0 (by
    simpa only [pair, Nat.cast_add, Nat.cast_one, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one] using h1)
  exact (h.comp s (differentiableAt_id.add_const _)).div_const 6

theorem completed_functional_equation (s : ℂ) :
    completed c χ hmod hχ (1 - s) =
      epsilon c χ.k (hmod ▸ χ.residue) * completedDual c χ hmod hχ s := by
  have h := (pair c χ hmod hχ).functional_equation (s + (χ.k.natAbs : ℂ) / 2)
  have hs : (((pair c χ hmod hχ).k : ℝ) : ℂ) - (s + (χ.k.natAbs : ℂ) / 2) =
      1 - s + (χ.k.natAbs : ℂ) / 2 := by
    simp only [pair, Nat.cast_add, Nat.cast_one, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one]
    ring
  rw [hs] at h
  unfold completed completedDual
  rw [h]
  simp only [smul_eq_mul, pair]
  ring

end OAI.SevenEighths.Angular.ThetaContinuation
