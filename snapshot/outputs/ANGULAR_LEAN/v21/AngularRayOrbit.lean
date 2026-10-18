import AngularRowClosure
import AngularPhysicalRowEnergy
import OAI.NumberTheory.DirichletL.Moments.FixedRay

/-! Exact realization of the sieve's raw finite ray orbit by unit-compatible
angular characters on the actual masked completed rows. -/
noncomputable section
open scoped Classical

namespace OAI.CubicEisenstein.AngularRayOrbit
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open CanonicalRowCompletion CanonicalRowCompletion.ActualFiber
open SevenEighths.Angular SevenEighths.AngularRowClosure
open SevenEighths.CenteredMomentFixedRay AngularCompletedCoefficient
local notation "Eis" => ActualEisensteinCubic.O

def orbitConductor (χ : AngularCharacter) : ℕ := 3 * χ.modulus.absNorm

theorem orbitConductor_ne_zero (χ : AngularCharacter) : orbitConductor χ ≠ 0 :=
  mul_ne_zero (by decide) (AngularPhysicalRowEnergy.finiteConductor_ne_zero χ)

theorem orbitConductor_le (χ : AngularCharacter) :
    CanonicalCoefficientClass.fixedBaseConductor (orbitConductor χ) ≤
      χ.modulus ⊓ Ideal.span {(12 : Eis)} := by
  have he : CanonicalCoefficientClass.fixedBaseConductor (orbitConductor χ) =
      Ideal.span {(χ.modulus.absNorm : Eis)} * Ideal.span {(12 : Eis)} := by
    simp only [CanonicalCoefficientClass.fixedBaseConductor, orbitConductor,
      Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, Nat.cast_ofNat]
    congr 2
    ring
  rw [he]
  exact le_inf (Ideal.mul_le_left.trans (Ideal.span_singleton_absNorm_le χ.modulus))
    Ideal.mul_le_right

theorem base_finiteResidue_periodic (χ : AngularCharacter) :
    CanonicalCoefficientClass.FactorsModulo
      (CanonicalCoefficientClass.fixedBaseConductor (orbitConductor χ))
      (finiteResidueHom χ) := by
  intro x y hxy
  exact finiteResidueHom_factorsModulo χ x y ((orbitConductor_le χ).trans inf_le_left hxy)

def rayChild (χ : AngularCharacter) (η : RayFourExpansion.RayCharacter) : AngularCharacter :=
  finiteTwist χ (primaryRayCharacter η)

theorem rayChild_type (χ : AngularCharacter) (η : RayFourExpansion.RayCharacter) :
    (rayChild χ η).k = χ.k := rfl

theorem rayChild_finiteResidue_periodic (χ : AngularCharacter)
    (η : RayFourExpansion.RayCharacter) :
    CanonicalCoefficientClass.FactorsModulo
      (CanonicalCoefficientClass.fixedBaseConductor (orbitConductor χ))
      (finiteResidueHom (rayChild χ η)) := by
  intro x y hxy
  apply finiteResidueHom_factorsModulo (rayChild χ η) x y
  exact (orbitConductor_le χ) hxy

theorem rayChild_supported_primary (χ : AngularCharacter) (η : RayFourExpansion.RayCharacter)
    (a : Eis) (ha : Supported (Ideal.span {a})) (hp : lambda^2 ∣ a - 1) :
    (rayChild χ η).elementCoeff a =
      (SecondPassArithmetic.rayMonoid η * χ.elementHom.toMonoidHom) a := by
  rw [rayChild, elementCoeff_finiteTwist, primaryRayCharacter_primary η a ha hp]
  change χ.elementCoeff a * RayFourExpansion.rayCharacter η a =
    RayFourExpansion.rayCharacter η a * χ.elementCoeff a
  exact mul_comm _ _

theorem masked_row_zero_of_unsupported (q : ℕ) (Ψ : Eis →* ℂ) (m f z a : Eis)
    (ha : ¬ Supported (Ideal.span {a})) :
    rowTwist Ψ (maskElement q m) f z a = 0 := by
  have hzero : ∀ P ∈ fixedBadPrimes, P ∣ Ideal.span {a} →
      idealRowHom ((maskElement q m)^6*f^4*z) (Ideal.span {a}) = 0 := by
    intro P hP hd
    have he := reflectionExcludedPrimes_bad q hP
    have hm : maskElement q m ∈ P :=
      P.mul_mem_left m (excludedGenerator_mem _ he)
    have hm6 : (maskElement q m)^6 ∈ P := by
      rw [show (maskElement q m)^6 = (maskElement q m)^5 * maskElement q m by ring]
      exact P.mul_mem_left _ hm
    exact idealRowHom_zero_of_dvd _ (reflectionExcludedPrimes_prime q P he) hd
      (P.mul_mem_right z (P.mul_mem_right (f^4) hm6))
  have hbad : lambda ∣ a ∨ (2 : Eis) ∣ a := by
    simpa only [supported_span_iff, not_and_or, not_not] using ha
  have hz : idealRowHom ((maskElement q m)^6*f^4*z) (Ideal.span {a}) = 0 := by
    rcases hbad with h | h
    · apply hzero (Ideal.span {lambda}) (by simp [fixedBadPrimes])
      exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr h)
    · apply hzero (Ideal.span {(2 : Eis)}) (by simp [fixedBadPrimes])
      exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr h)
  change Ψ a * idealRowHom ((maskElement q m)^6*f^4*z) (Ideal.span {a}) = 0
  rw [hz, mul_zero]

theorem masked_row_congr_supported_primary (q : ℕ) (Ψ Φ : Eis →* ℂ)
    (h : ∀ a, Supported (Ideal.span {a}) → lambda^2 ∣ a - 1 → Ψ a = Φ a)
    (m f z a : Eis) (hp : lambda^2 ∣ a - 1) :
    rowTwist Ψ (maskElement q m) f z a = rowTwist Φ (maskElement q m) f z a := by
  by_cases ha : Supported (Ideal.span {a})
  · change Ψ a * _ = Φ a * _
    rw [h a ha hp]
  · rw [masked_row_zero_of_unsupported q Ψ m f z a ha,
      masked_row_zero_of_unsupported q Φ m f z a ha]

theorem completed_row_rayChild (χ : AngularCharacter) (η : RayFourExpansion.RayCharacter)
    (q : ℕ) (m f z : Eis) (W : ℝ → ℂ) (X : ℝ) :
    completedT (rowTwist (rayChild χ η).elementHom.toMonoidHom (maskElement q m) f z) W X =
      completedT (rowTwist (SecondPassArithmetic.rayMonoid η * χ.elementHom.toMonoidHom)
        (maskElement q m) f z) W X := by
  apply completedT_congr_primary
  intro a hp
  exact masked_row_congr_supported_primary q _ _
    (rayChild_supported_primary χ η) m f z a hp

theorem exists_orbit_character (χ : AngularCharacter) (Ψ : Eis →* ℂ)
    (hΨ : CanonicalCoefficientClass.IsBaseRayTwist χ.elementHom.toMonoidHom Ψ) :
    ∃ ψ : AngularCharacter, ψ.k = χ.k ∧
      CanonicalCoefficientClass.FactorsModulo
        (CanonicalCoefficientClass.fixedBaseConductor (orbitConductor χ)) (finiteResidueHom ψ) ∧
      ∀ (m f z : Eis) (W : ℝ → ℂ) (X : ℝ),
        completedT (rowTwist Ψ (maskElement (orbitConductor χ) m) f z) W X =
          completedT (rowTwist ψ.elementHom.toMonoidHom
            (maskElement (orbitConductor χ) m) f z) W X := by
  rcases hΨ with rfl | ⟨η, rfl⟩
  · exact ⟨χ, rfl, base_finiteResidue_periodic χ, fun _ _ _ _ _ => rfl⟩
  · refine ⟨rayChild χ η, rfl, rayChild_finiteResidue_periodic χ η, ?_⟩
    intro m f z W X
    exact (completed_row_rayChild χ η (orbitConductor χ) m f z W X).symm

end OAI.CubicEisenstein.AngularRayOrbit
