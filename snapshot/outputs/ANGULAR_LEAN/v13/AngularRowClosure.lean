import AngularCompletedCoefficient
import OAI.NumberTheory.DirichletL.Hecke.RowClosure

/-! Actual angular row-character closure with unchanged angular type and a
quantitative finite-conductor bound. Only finite residue factors are periodic. -/

noncomputable section
open scoped Classical

namespace OAI.SevenEighths.AngularRowClosure

open Angular
open CubicEisenstein.AngularCompletedCoefficient

abbrev Eis := ActualEisensteinCubic.O

def finiteTwist (χ : AngularCharacter) (η : HeckeFamily.Character) : AngularCharacter where
  k := χ.k
  modulus := χ.modulus ⊓ η.modulus
  modulus_ne_bot := Ideal.inf_ne_bot_of_ne_bot χ.modulus_ne_bot η.modulus_ne_bot
  residue := ResidueCharacter.product χ.modulus η.modulus χ.residue η.residue
  unit_compatible u := by
    rw [ResidueCharacter.product_mk, η.unit_trivial, mul_one]
    exact χ.unit_compatible u

theorem elementCoeff_finiteTwist (χ : AngularCharacter) (η : HeckeFamily.Character) (a : Eis) :
    (finiteTwist χ η).elementCoeff a = χ.elementCoeff a * HeckeFamily.elementCoeff η a := by
  by_cases ha : a = 0
  · subst a
    rw [AngularCharacter.elementCoeff_zero, AngularCharacter.elementCoeff_zero, zero_mul]
  · rw [AngularCharacter.elementCoeff_eq _ ha, AngularCharacter.elementCoeff_eq χ ha]
    change alpha a^χ.k * ResidueCharacter.product χ.modulus η.modulus χ.residue η.residue
      (Ideal.Quotient.mk (χ.modulus ⊓ η.modulus) a) =
      (alpha a^χ.k * χ.residue (Ideal.Quotient.mk χ.modulus a)) *
        η.residue (Ideal.Quotient.mk η.modulus a)
    rw [ResidueCharacter.product_mk]
    ring

theorem finiteResidueHom_finiteTwist (χ : AngularCharacter) (η : HeckeFamily.Character) (a : Eis) :
    finiteResidueHom (finiteTwist χ η) a =
      finiteResidueHom χ a * HeckeFamily.elementCoeff η a :=
  ResidueCharacter.product_mk χ.modulus η.modulus χ.residue η.residue a

theorem finiteTwist_conductor_bound (χ : AngularCharacter) (η : HeckeFamily.Character) :
    (finiteTwist χ η).modulus.absNorm ≤ χ.modulus.absNorm * η.modulus.absNorm := by
  let : Finite (Eis ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Finite (Eis ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  exact FiniteConductor.absNorm_inf_le_mul χ.modulus η.modulus

def finiteTrivial : HeckeFamily.Character :=
  HeckeFamily.Character.ofResidue ⊤ top_ne_bot 1 (by
    intro u
    have he : Ideal.Quotient.mk (⊤ : Ideal Eis) (u : Eis) = 1 := Subsingleton.elim _ _
    rw [he, map_one])

theorem finiteTrivial_elementCoeff (a : Eis) : HeckeFamily.elementCoeff finiteTrivial a = 1 := by
  have he : Ideal.Quotient.mk (⊤ : Ideal Eis) a = 1 := Subsingleton.elim _ _
  change (1 : MulChar (Eis ⧸ (⊤ : Ideal Eis)) ℂ) (Ideal.Quotient.mk ⊤ a) = 1
  rw [he, map_one]

def rowConductorBound (χ : AngularCharacter) (m f z : Eis) : ℕ :=
  χ.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : Eis)}).absNorm *
    ((Ideal.span {f}).absNorm^4 * (Ideal.span {z}).absNorm)

/-- Both the physical element coefficients and the finite residue factors
are identified with the actual row twist. The finite factor equality supplies
the arithmetic projector; the full angular character is not called periodic. -/
theorem exists_angular_row_character (χ : AngularCharacter) (m f z : Eis)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2 : Eis) ∣ m) :
    ∃ ψ : AngularCharacter,
      ψ.k = χ.k ∧ ψ.modulus.absNorm ≤ rowConductorBound χ m f z ∧
      (∀ a : Eis, ψ.elementCoeff a =
        CanonicalRowCompletion.rowTwist χ.elementHom.toMonoidHom m f z a) ∧
      (∀ a : Eis, finiteResidueHom ψ a =
        CanonicalRowCompletion.rowTwist (finiteResidueHom χ) m f z a) := by
  obtain ⟨η, hηbound, hη⟩ := HeckeRowClosure.exists_row_character_with_conductor
    finiteTrivial m f z hm hf hz hmLam hm2
  refine ⟨finiteTwist χ η, rfl, ?_, ?_, ?_⟩
  · apply (finiteTwist_conductor_bound χ η).trans
    have he : finiteTrivial.modulus = ⊤ := rfl
    rw [HeckeRowClosure.rowConductorBound, he, Ideal.absNorm_top, one_mul] at hηbound
    simpa only [rowConductorBound, mul_assoc] using
      Nat.mul_le_mul_left χ.modulus.absNorm hηbound
  · intro a
    rw [elementCoeff_finiteTwist, hη]
    change χ.elementCoeff a *
      (HeckeFamily.elementCoeff finiteTrivial a *
        CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {a})) =
      χ.elementCoeff a * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {a})
    rw [finiteTrivial_elementCoeff, one_mul]
  · intro a
    rw [finiteResidueHom_finiteTwist, hη]
    change finiteResidueHom χ a *
      (HeckeFamily.elementCoeff finiteTrivial a *
        CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {a})) =
      finiteResidueHom χ a * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {a})
    rw [finiteTrivial_elementCoeff, one_mul]

end OAI.SevenEighths.AngularRowClosure
