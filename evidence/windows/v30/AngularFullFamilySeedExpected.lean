/- STATEMENT-ONLY FIXTURE; NOT A SOLUTION. Module boundary retained. -/
import AngularTypeZeroEntireExpected
import AngularNormTwistContinuation

noncomputable section
open scoped Classical Topology
open Complex
namespace OAI.SevenEighths.Angular.FullFamilySeed

theorem physical_seed (χ : AngularCharacter) (s : ℂ)
    (hs : (23:ℝ)/24 < s.re) (hpole : χ.k = 0 → χ.residue = 1 → s ≠ 1) :
    FamilyContinuation.LFunction χ s ≠ 0 := by sorry

theorem physical_seed_norm_twist (χ : AngularCharacter) (τ : ℝ) (s : ℂ)
    (hs : (23:ℝ)/24 < s.re)
    (hpole : χ.k = 0 → χ.residue = 1 → s ≠ 1+(τ:ℂ)*I) :
    NormTwist.LFunction χ τ s ≠ 0 := by sorry

theorem nonprincipal_entire (χ : AngularCharacter)
    (hnonprincipal : χ.k ≠ 0 ∨ χ.residue ≠ 1) :
    Differentiable ℂ (FamilyContinuation.LFunction χ) := by sorry

theorem norm_twist_nonprincipal_entire (χ : AngularCharacter) (τ : ℝ)
    (hnonprincipal : χ.k ≠ 0 ∨ χ.residue ≠ 1) :
    Differentiable ℂ (NormTwist.LFunction χ τ) := by sorry

theorem norm_twist_differentiableAt (χ : AngularCharacter) (τ : ℝ) (s : ℂ)
    (hs : 0 < s.re)
    (hpole : χ.k = 0 → χ.residue = 1 → s ≠ 1+(τ:ℂ)*I) :
    DifferentiableAt ℂ (NormTwist.LFunction χ τ) s := by sorry

theorem halfPlane_transport_iff (χ : AngularCharacter) (τ β : ℝ) :
    (∀ s : ℂ, β < s.re → (χ.k = 0 → χ.residue = 1 → s ≠ 1) →
      FamilyContinuation.LFunction χ s ≠ 0) ↔
    (∀ s : ℂ, β < s.re → (χ.k = 0 → χ.residue = 1 → s ≠ 1+(τ:ℂ)*I) →
      NormTwist.LFunction χ τ s ≠ 0) := by sorry

end OAI.SevenEighths.Angular.FullFamilySeed
