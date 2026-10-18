/- STATEMENT-ONLY FIXTURE; NOT A SOLUTION. Module boundary retained. -/
import AngularFiniteIdentification
import OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
import OAI.NumberTheory.DirichletL.Hecke.BoundaryIntegration

/-! Actual type-zero nonprincipal continuation, including its value at one.
The primitive theta origin terms vanish by nonprincipality, so entireness is
proved before analytic uniqueness is used for the finite-family identification. -/
noncomputable section
open scoped Classical Topology
open Set Filter Complex
namespace OAI.SevenEighths.Angular.TypeZeroEntire
open ActualEisensteinCubic FiniteIdentification PrimitiveReduction ThetaContinuation
open Polynomial

theorem finite_idealCoeff (χ : AngularCharacter) (hk : χ.k = 0) :
    HeckeFamily.idealCoeff (toFinite χ hk) = χ.idealHom := by sorry

theorem primitive_residue_nonprincipal (χ : AngularCharacter) (hk : χ.k = 0)
    (hχ : χ.residue ≠ 1) : (primitive χ).residue ≠ 1 := by sorry

theorem weightedCoeff_zero (χ : AngularCharacter) (hk : χ.k = 0)
    (hχ : χ.residue ≠ 1) : weightedCoeff χ 0 = 0 := by sorry

theorem pair_strong_nonprincipal (c : O) [NeZero c] (χ : AngularCharacter)
    (hmod : χ.modulus = Ideal.span {c})
    (hp : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue))
    (hk : χ.k = 0) (hχ : χ.residue ≠ 1) : IsStrongFEPair (pair c χ hmod hp) := by sorry

theorem primitive_LFunction_entire (c : O) [NeZero c] (χ : AngularCharacter)
    (hmod : χ.modulus = Ideal.span {c})
    (hp : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue))
    (hk : χ.k = 0) (hχ : χ.residue ≠ 1) :
    Differentiable ℂ (ThetaContinuation.LFunction c χ hmod hp) := by sorry

theorem LFunction_entire (χ : AngularCharacter) (hk : χ.k = 0)
    (hχ : χ.residue ≠ 1) : Differentiable ℂ (FamilyContinuation.LFunction χ) := by sorry

theorem LFunction_eq_finite (χ : AngularCharacter) (hk : χ.k = 0)
    (hχ : χ.residue ≠ 1) (s : ℂ) :
    FamilyContinuation.LFunction χ s = HeckeFamily.LFunction (toFinite χ hk) s := by sorry

theorem LFunction_one_ne_zero (χ : AngularCharacter) (hk : χ.k = 0)
    (hχ : χ.residue ≠ 1) : FamilyContinuation.LFunction χ 1 ≠ 0 := by sorry

end OAI.SevenEighths.Angular.TypeZeroEntire
