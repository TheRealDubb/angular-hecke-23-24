import AngularPolynomial
import AngularGaussianWeighted

/-! The actual polynomially weighted angular theta series, its centered
origin term, and summability at every positive height.
No analytic continuation or zero-free conclusion is defined here. -/

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace OAI.SevenEighths.Angular.ThetaMellin

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open OAI.SevenEighths.Angular.Polynomial

def test (k : ℤ) (a : ℝ) (ha : 0 < a) : SchwartzMap ℂ ℂ :=
  if 0 ≤ k then GaussianFourier.holo a ha k.natAbs
  else GaussianFourier.anti a ha k.natAbs

theorem test_apply (k : ℤ) (a : ℝ) (ha : 0 < a) (z : ℂ) :
    test k a ha z = harmonic k z * GaussianTheta.gaussian a z := by
  unfold test Polynomial.harmonic
  split <;> simp only [GaussianFourier.holo_apply, GaussianFourier.anti_apply,
    GaussianSchwartz.gaussian_apply, GaussianTheta.gaussian]

def thetaTerm (χ : AngularCharacter) (A t : ℝ) (a : O) : ℂ :=
  weightedCoeff χ a * GaussianTheta.gaussian (A * t) (eisEmbedding a)

def theta (χ : AngularCharacter) (A t : ℝ) : ℂ := ∑' a : O, thetaTerm χ A t a

def centeredTheta (χ : AngularCharacter) (A t : ℝ) : ℂ :=
  theta χ A t - weightedCoeff χ 0

theorem theta_summable (χ : AngularCharacter) (A t : ℝ) (hA : 0 < A) (ht : 0 < t) :
    Summable (thetaTerm χ A t) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  have h := actual_eisenstein_periodic_summable (test χ.k (A * t) (mul_pos hA ht))
    (Ideal.Quotient.mk χ.modulus) χ.residue
  convert h using 1
  funext a
  rw [test_apply]
  simp only [thetaTerm, weightedCoeff]
  ring

theorem centeredTheta_hasSum (χ : AngularCharacter) (A t : ℝ) (hA : 0 < A) (ht : 0 < t) :
    HasSum (fun a : O => centeredWeightedCoeff χ a *
      GaussianTheta.gaussian (A * t) (eisEmbedding a)) (centeredTheta χ A t) := by
  have h := hasSum_ite_sub_hasSum (theta_summable χ A t hA ht).hasSum 0
  convert h using 1
  · funext a
    by_cases ha : a = 0 <;> simp [centeredWeightedCoeff, thetaTerm, ha]
  · simp [centeredTheta, theta, thetaTerm, GaussianTheta.gaussian]

theorem centeredTheta_eq_theta_of_nonzero_type (χ : AngularCharacter) (hk : χ.k ≠ 0)
    (A t : ℝ) : centeredTheta χ A t = theta χ A t := by
  simp [centeredTheta, weightedCoeff_origin, hk]

end OAI.SevenEighths.Angular.ThetaMellin
