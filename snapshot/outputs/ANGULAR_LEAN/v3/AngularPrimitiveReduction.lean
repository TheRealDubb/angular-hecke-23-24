import AngularSeries
import OAI.NumberTheory.DirichletL.TraceConductor
import OAI.NumberTheory.DirichletL.EulerFactors

/-! Actual primitive conductor reduction for the angular family. The finite
source mask preserves the angular type and global-unit compatibility. Series
identities are confined to their proven domain Re(s)>1; no continued angular
L-function is assumed or defined in this module. -/

noncomputable section
open scoped Classical BigOperators

namespace OAI.SevenEighths.Angular.PrimitiveReduction

open ActualEisensteinCubic ConcreteTraceCRT

def presentation (χ : AngularCharacter) :
    TraceConductor.PrimitivePresentation χ.modulus χ.residue :=
  TraceConductor.primitivePresentation χ.modulus χ.modulus_ne_bot χ.residue

/-- The same angular type and the primitive finite residue supplied by OAI-003. -/
def primitive (χ : AngularCharacter) : AngularCharacter where
  k := χ.k
  modulus := (presentation χ).conductor
  modulus_ne_bot := (presentation χ).conductor_ne_bot
  residue := (presentation χ).character
  unit_compatible u := by
    have h := (presentation χ).source_mask (u : O)
    simp only [u.isUnit.map (Ideal.Quotient.mk χ.modulus), ite_true] at h
    change alpha (u : O) ^ χ.k * (presentation χ).character
      (Ideal.Quotient.mk (Ideal.span {(presentation χ).generator}) (u : O)) = 1
    rw [← h]
    exact χ.unit_compatible u

def generator (χ : AngularCharacter) : O := (presentation χ).generator

theorem generator_ne_zero (χ : AngularCharacter) : generator χ ≠ 0 :=
  (presentation χ).generator_ne_zero

@[simp] theorem primitive_k (χ : AngularCharacter) : (primitive χ).k = χ.k := rfl

theorem primitive_modulus (χ : AngularCharacter) :
    (primitive χ).modulus = Ideal.span {generator χ} := rfl

theorem primitive_isPrimitive (χ : AngularCharacter) :
    FiniteFourier.IsPrimitiveOnIdeals (primitive χ).residue :=
  (presentation χ).primitive

theorem modulus_le (χ : AngularCharacter) : χ.modulus ≤ (primitive χ).modulus :=
  (presentation χ).modulus_le

theorem norm_le (χ : AngularCharacter) :
    Ideal.absNorm (primitive χ).modulus ≤ χ.modulus.absNorm :=
  (presentation χ).norm_le

theorem residue_source_mask (χ : AngularCharacter) (a : O) :
    χ.residue (Ideal.Quotient.mk χ.modulus a) =
      if IsUnit (Ideal.Quotient.mk χ.modulus a) then
        (primitive χ).residue (Ideal.Quotient.mk (primitive χ).modulus a) else 0 :=
  (presentation χ).source_mask a

theorem elementCoeff_source_mask (χ : AngularCharacter) (a : O) :
    χ.elementCoeff a = if IsUnit (Ideal.Quotient.mk χ.modulus a) then
      (primitive χ).elementCoeff a else 0 := by
  by_cases ha : a = 0
  · simp [ha]
  rw [χ.elementCoeff_eq ha, (primitive χ).elementCoeff_eq ha,
    primitive_k, residue_source_mask χ a]
  split_ifs <;> simp only [mul_zero]

theorem idealHom_source_mask (χ : AngularCharacter) (I : Ideal O) :
    χ.idealHom I = if IsCoprime I χ.modulus then (primitive χ).idealHom I else 0 := by
  rw [← Ideal.span_singleton_generator I, AngularCharacter.idealHom_span,
    AngularCharacter.idealHom_span, elementCoeff_source_mask]
  simp only [IdealCharacter.isUnit_mk_iff_isCoprime]

/-- The exact finite Euler product, with the primitive angular ideal coefficients. -/
def factors (χ : AngularCharacter) : ℂ → ℂ :=
  EulerFactors.deletedProduct (SmoothMobiusCorrection.primeSet χ.modulus)
    (fun P => Ideal.absNorm P.val) (fun P => (primitive χ).idealHom P.val)

theorem factors_eq (χ : AngularCharacter) (s : ℂ) :
    factors χ s = ∏ P ∈ SmoothMobiusCorrection.primeSet χ.modulus,
      (1 - IdealEuler.weighted (primitive χ).idealHom s P.val) := by
  apply Finset.prod_congr rfl
  intro P _
  simp only [EulerFactors.factor, IdealEuler.weighted, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, IdealEuler.normWeight, CubicEisenstein.fullIdealWeight,
    P.property.ne_zero, ite_false, Complex.ofReal_natCast]

theorem factors_differentiable (χ : AngularCharacter) : Differentiable ℂ (factors χ) := by
  apply EulerFactors.differentiable_deletedProduct
  intro P _
  have h := SmoothMobiusCorrection.prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

theorem factors_ne_zero (χ : AngularCharacter) {s : ℂ} (hs : 0 < s.re) :
    factors χ s ≠ 0 := by
  apply EulerFactors.deletedProduct_ne_zero _ _ _ _ _ hs
  · intro P _
    have h := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)
  · intro P _
    exact (primitive χ).norm_idealHom_le_one P.val

theorem series_eq_primitive_mul_factors (χ : AngularCharacter) (s : ℂ) (hs : 1 < s.re) :
    χ.series s = (primitive χ).series s * factors χ s := by
  rw [factors_eq]
  exact IdealEuler.series_of_coprime_mask χ.modulus χ.modulus_ne_bot _ _
    (primitive χ).norm_idealHom_le_one (idealHom_source_mask χ) s hs

end OAI.SevenEighths.Angular.PrimitiveReduction
