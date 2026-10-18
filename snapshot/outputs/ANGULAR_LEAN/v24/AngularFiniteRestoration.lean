import AngularEulerProducts
import AngularFamilyContinuation

/-! Exact finite-prime restoration and the physical continued L-function
identity in the absolute-convergence half-plane. No continuation of this
identity below that half-plane is asserted here. -/
noncomputable section
open scoped Classical BigOperators ContDiff
namespace OAI.CubicEisenstein.AngularFiniteRestoration
open ActualEisensteinCubic
open MeasureTheory
open SevenEighths SevenEighths.Angular
open SmoothMobiusCorrection (PrimeIdeal)
open AngularEulerProducts AngularEulerCorrection

def finiteEulerFactor (χ : AngularCharacter) (S : Finset PrimeIdeal) (s : ℂ) : ℂ :=
  ∏ P ∈ S, (1 - χ.idealTerm s P.val)

theorem finiteEulerFactor_differentiable (χ : AngularCharacter) (S : Finset PrimeIdeal) :
    Differentiable ℂ (finiteEulerFactor χ S) := by
  unfold finiteEulerFactor
  apply Differentiable.fun_finsetProd
  intro P hP
  apply (differentiable_const (1 : ℂ)).sub
  have he : (fun s : ℂ => χ.idealTerm s P.val) = primeCharacterTerm χ P := by
    funext s
    simp only [AngularCharacter.idealTerm, primeCharacterTerm,
      SmoothMobiusCorrection.primeNormPower, Complex.cpow_neg, div_eq_mul_inv]
  rw [he]
  exact primeCharacterTerm_differentiable χ P

theorem image_primes (S : Finset PrimeIdeal) :
    ∀ P ∈ S.image Subtype.val, Prime P := by
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
  exact Q.property

theorem ordinarySeries_eq_deletedInverse (χ : AngularCharacter) (S : Finset PrimeIdeal)
    (s : ℂ) :
    (∑' I : Ideal O, ordinarySeriesTerm χ (S.image Subtype.val) s I) =
      IdealEuler.inverseSeries (IdealEuler.deletePrimes S χ.idealHom) s := by
  unfold IdealEuler.inverseSeries
  apply tsum_congr
  intro I
  have hmask : (∀ P ∈ S, ¬P.val ∣ I) ↔
      (∀ P ∈ S.image Subtype.val, ¬P ∣ I) := by simp
  change SmoothMobiusCorrection.outsideMask (S.image Subtype.val) I *
      AngularIdealRow.mobiusWeight χ I * fullIdealWeight s I =
    (UniqueFactorizationMonoid.moebius I : ℂ) *
      (IdealEuler.deletePrimes S χ.idealHom I * fullIdealWeight s I)
  rw [IdealEuler.deletePrimes_apply]
  simp only [hmask]
  unfold SmoothMobiusCorrection.outsideMask AngularIdealRow.mobiusWeight
  split_ifs <;> ring

theorem inverseSeries_restoration (χ : AngularCharacter) (S : Finset PrimeIdeal)
    (s : ℂ) (hs : 1 < s.re) :
    IdealEuler.inverseSeries χ.idealHom s = finiteEulerFactor χ S s *
      IdealEuler.inverseSeries (IdealEuler.deletePrimes S χ.idealHom) s := by
  apply mul_right_cancel₀ (χ.series_ne_zero s hs)
  calc
    _ = 1 := χ.inverseSeries_mul_series s hs
    _ = IdealEuler.inverseSeries (IdealEuler.deletePrimes S χ.idealHom) s *
        IdealEuler.series (IdealEuler.deletePrimes S χ.idealHom) s :=
      (IdealEuler.inverseSeries_mul_series _
        (IdealEuler.deletePrimes_norm_le_one S χ.idealHom χ.norm_idealHom_le_one) s hs).symm
    _ = _ := by
      rw [χ.deleted_series S s hs]
      unfold finiteEulerFactor
      ring

theorem full_inverse_eq_correction (χ : AngularCharacter) (S : Finset PrimeIdeal)
    (s : ℂ) (hs : 1 < s.re) :
    IdealEuler.inverseSeries χ.idealHom s =
      (finiteEulerFactor χ S s * eulerCorrection χ (S.image Subtype.val) s) *
        LSeries (AngularWeightedMellin.weightedCoeff χ (S.image Subtype.val)) s := by
  rw [inverseSeries_restoration χ S s hs, ← ordinarySeries_eq_deletedInverse,
    actual_dirichlet_correction χ (S.image Subtype.val) (image_primes S) s hs,
    dampedSeries_eq_LSeries χ (S.image Subtype.val) s hs]
  ring

theorem full_correction_mul_LFunction (χ : AngularCharacter) (S : Finset PrimeIdeal)
    (s : ℂ) (hs : 1 < s.re) :
    ((finiteEulerFactor χ S s * eulerCorrection χ (S.image Subtype.val) s) *
      LSeries (AngularWeightedMellin.weightedCoeff χ (S.image Subtype.val)) s) *
        FamilyContinuation.LFunction χ s = 1 := by
  rw [← full_inverse_eq_correction χ S s hs, FamilyContinuation.LFunction_eq_series χ s hs]
  exact χ.inverseSeries_mul_series s hs

theorem compactMellin_correction_identity (χ : AngularCharacter) (S : Finset PrimeIdeal)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hWsupport : ∀ x, x ≤ 1 ∨ 2 ≤ x → W x = 0)
    (s : ℂ) (hs : 2 < s.re) :
    ((finiteEulerFactor χ S s * eulerCorrection χ (S.image Subtype.val) s) *
      mellin (fun Z : ℝ => AngularWeightedMellin.weightedCompactSum
        χ (S.image Subtype.val) W Z⁻¹) (-s)) * FamilyContinuation.LFunction χ s =
          mellin W s := by
  rw [AngularWeightedMellin.weightedCompactMellin_eq_series χ (S.image Subtype.val)
    W hW hWsupport s hs]
  calc
    _ = mellin W s * (((finiteEulerFactor χ S s *
          eulerCorrection χ (S.image Subtype.val) s) *
          LSeries (AngularWeightedMellin.weightedCoeff χ (S.image Subtype.val)) s) *
            FamilyContinuation.LFunction χ s) := by ring
    _ = _ := by rw [full_correction_mul_LFunction χ S s (by linarith), mul_one]

end OAI.CubicEisenstein.AngularFiniteRestoration
