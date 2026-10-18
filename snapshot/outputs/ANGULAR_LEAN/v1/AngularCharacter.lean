import OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
import OAI.NumberTheory.DirichletL.Hecke.Family
import OAI.NumberTheory.DirichletL.IdealCharacter

/-!
# Actual angular Hecke coefficients over the Eisenstein integers

This module extends the finite-character coefficient foundation of OAI-003.
The angular character is defined by its finite residue character and integer
infinity type, with the actual global-unit compatibility equation. Its ideal
coefficients are descended from the physical element coefficients; they are not
arbitrary analytic data. No analytic continuation or zero-free theorem is
postulated or proved in this module.
-/

namespace OAI.SevenEighths.Angular

noncomputable section
open scoped Classical
open Submodule.IsPrincipal

abbrev O := ActualEisensteinCubic.O
abbrev alpha := FiniteGaussPhase.angularFactor

@[simp] theorem alpha_one : alpha (1 : O) = 1 := by
  simp [alpha, FiniteGaussPhase.angularFactor]

theorem alpha_mul (a b : O) : alpha (a * b) = alpha a * alpha b :=
  CompletedGauss.angularFactor_mul a b

theorem norm_alpha {a : O} (ha : a ≠ 0) : ‖alpha a‖ = 1 :=
  FiniteGaussPhase.norm_angularFactor a ha

theorem alpha_ne_zero {a : O} (ha : a ≠ 0) : alpha a ≠ 0 := by
  intro h
  have hnorm := norm_alpha ha
  rw [h, norm_zero] at hnorm
  exact zero_ne_one hnorm

theorem alpha_neg_zpow {a : O} (ha : a ≠ 0) (k : ℤ) :
    alpha a ^ (-k) = star (alpha a ^ k) := by
  rw [zpow_neg]
  exact Complex.inv_eq_conj (by rw [norm_zpow, norm_alpha ha, one_zpow])

/-- A finite residue character paired with its actual angular type.
The compatibility equation is what makes the physical coefficient independent
of the choice of generator of a principal ideal. -/
structure AngularCharacter where
  k : ℤ
  modulus : Ideal O
  modulus_ne_bot : modulus ≠ ⊥
  residue : MulChar (O ⧸ modulus) ℂ
  unit_compatible : ∀ u : Oˣ,
    alpha (u : O) ^ k * residue (Ideal.Quotient.mk modulus (u : O)) = 1

namespace AngularCharacter

/-- Physical element coefficient, with zero explicitly excluded even for
type zero and the trivial quotient ring. -/
def elementCoeff (χ : AngularCharacter) (a : O) : ℂ :=
  if a = 0 then 0 else alpha a ^ χ.k * χ.residue (Ideal.Quotient.mk χ.modulus a)

@[simp] theorem elementCoeff_zero (χ : AngularCharacter) : χ.elementCoeff 0 = 0 := by
  simp [elementCoeff]

theorem elementCoeff_eq (χ : AngularCharacter) {a : O} (ha : a ≠ 0) :
    χ.elementCoeff a = alpha a ^ χ.k * χ.residue (Ideal.Quotient.mk χ.modulus a) := by
  simp only [elementCoeff, ha, ite_false]

@[simp] theorem elementCoeff_one (χ : AngularCharacter) : χ.elementCoeff 1 = 1 := by
  simp [elementCoeff]

theorem elementCoeff_mul (χ : AngularCharacter) (a b : O) :
    χ.elementCoeff (a * b) = χ.elementCoeff a * χ.elementCoeff b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [elementCoeff_eq χ (mul_ne_zero ha hb), elementCoeff_eq χ ha,
    elementCoeff_eq χ hb, alpha_mul, mul_zpow, map_mul, map_mul]
  ring

def elementHom (χ : AngularCharacter) : O →*₀ ℂ where
  toFun := χ.elementCoeff
  map_zero' := χ.elementCoeff_zero
  map_one' := χ.elementCoeff_one
  map_mul' := χ.elementCoeff_mul

@[simp] theorem elementCoeff_unit (χ : AngularCharacter) (u : Oˣ) :
    χ.elementCoeff (u : O) = 1 := by
  rw [elementCoeff_eq χ (Units.ne_zero u)]
  exact χ.unit_compatible u

theorem elementCoeff_unit_mul (χ : AngularCharacter) (u : Oˣ) (a : O) :
    χ.elementCoeff ((u : O) * a) = χ.elementCoeff a := by
  rw [elementCoeff_mul, elementCoeff_unit, one_mul]

theorem elementCoeff_eq_of_associated (χ : AngularCharacter) {a b : O}
    (hab : Associated a b) : χ.elementCoeff a = χ.elementCoeff b := by
  obtain ⟨u, rfl⟩ := hab
  rw [elementCoeff_mul, elementCoeff_unit, mul_one]

theorem norm_elementCoeff (χ : AngularCharacter) {a : O} (ha : a ≠ 0) :
    ‖χ.elementCoeff a‖ = ‖χ.residue (Ideal.Quotient.mk χ.modulus a)‖ := by
  rw [elementCoeff_eq χ ha, norm_mul, norm_zpow, norm_alpha ha, one_zpow, one_mul]

theorem norm_elementCoeff_le_one (χ : AngularCharacter) (a : O) :
    ‖χ.elementCoeff a‖ ≤ 1 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  by_cases ha : a = 0
  · simp [ha]
  rw [norm_elementCoeff χ ha]
  exact IdealCharacter.norm_residue_le_one χ.modulus χ.residue _

theorem elementCoeff_zero_iff (χ : AngularCharacter) (a : O) :
    χ.elementCoeff a = 0 ↔ a = 0 ∨ ¬ IsUnit (Ideal.Quotient.mk χ.modulus a) := by
  by_cases ha : a = 0
  · simp [ha]
  rw [elementCoeff_eq χ ha, mul_eq_zero]
  simp only [zpow_ne_zero χ.k (alpha_ne_zero ha), false_or, ha, MulChar.apply_eq_zero_iff]

/-- Generator-independent ideal coefficient. This definition includes all
nonzero ideals, including those meeting the finite conductor, where it vanishes. -/
def idealValue (χ : AngularCharacter) (I : Ideal O) : ℂ :=
  if I = ⊥ then 0 else χ.elementCoeff (generator I)

@[simp] theorem idealValue_bot (χ : AngularCharacter) : χ.idealValue ⊥ = 0 := by
  simp [idealValue]

theorem idealValue_span (χ : AngularCharacter) (a : O) :
    χ.idealValue (Ideal.span ({a} : Set O)) = χ.elementCoeff a := by
  by_cases ha : a = 0
  · simp [ha]
  have hI : Ideal.span ({a} : Set O) ≠ ⊥ := by
    exact fun h => ha (Ideal.span_singleton_eq_bot.mp h)
  simp only [idealValue, hI, ite_false]
  exact elementCoeff_eq_of_associated χ (associated_generator_span_self a)

/-- The actual multiplicative ideal coefficient, descended from the angular
element expression using the unit compatibility proof. -/
def idealHom (χ : AngularCharacter) : Ideal O →*₀ ℂ where
  toFun := χ.idealValue
  map_zero' := χ.idealValue_bot
  map_one' := by
    simpa only [Ideal.span_singleton_one, Ideal.one_eq_top, elementCoeff_one] using
      χ.idealValue_span 1
  map_mul' I J := by
    rw [← Ideal.span_singleton_generator I, ← Ideal.span_singleton_generator J,
      Ideal.span_singleton_mul_span_singleton, idealValue_span, idealValue_span,
      idealValue_span, elementCoeff_mul]

@[simp] theorem idealHom_bot (χ : AngularCharacter) : χ.idealHom ⊥ = 0 :=
  χ.idealValue_bot

theorem idealHom_span (χ : AngularCharacter) (a : O) :
    χ.idealHom (Ideal.span ({a} : Set O)) = χ.elementCoeff a :=
  χ.idealValue_span a

theorem idealHom_of_generator (χ : AngularCharacter) {I : Ideal O} {a : O}
    (ha : Ideal.span ({a} : Set O) = I) : χ.idealHom I = χ.elementCoeff a := by
  rw [← ha, idealHom_span]

theorem norm_idealHom_le_one (χ : AngularCharacter) (I : Ideal O) :
    ‖χ.idealHom I‖ ≤ 1 := by
  rw [← Ideal.span_singleton_generator I, idealHom_span]
  exact χ.norm_elementCoeff_le_one _

theorem idealHom_zero_iff (χ : AngularCharacter) (I : Ideal O) :
    χ.idealHom I = 0 ↔ I = ⊥ ∨ ¬ IsCoprime I χ.modulus := by
  rw [← Ideal.span_singleton_generator I, idealHom_span, elementCoeff_zero_iff,
    IdealCharacter.isUnit_mk_iff_isCoprime, Ideal.span_singleton_generator,
    ← eq_bot_iff_generator_eq_zero]

/-- Every original OAI-003 unit-trivial finite character is a type-zero
angular character. -/
def ofFinite (χ : HeckeFamily.Character) : AngularCharacter where
  k := 0
  modulus := χ.modulus
  modulus_ne_bot := χ.modulus_ne_bot
  residue := χ.residue
  unit_compatible u := by simpa using χ.unit_trivial u

@[simp] theorem ofFinite_k (χ : HeckeFamily.Character) : (ofFinite χ).k = 0 := rfl

theorem ofFinite_elementCoeff (χ : HeckeFamily.Character) {a : O} (ha : a ≠ 0) :
    (ofFinite χ).elementCoeff a = HeckeFamily.elementCoeff χ a := by
  simp [elementCoeff_eq _ ha, ofFinite, HeckeFamily.elementCoeff]

theorem ofFinite_idealHom (χ : HeckeFamily.Character) :
    (ofFinite χ).idealHom = IdealCharacter.ofResidue χ.modulus χ.residue
      χ.unit_trivial := by
  ext I
  by_cases hI : I = ⊥
  · simp [hI]
  have hg : generator I ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
  rw [← Ideal.span_singleton_generator I, idealHom_span,
    IdealCharacter.ofResidue_span _ _ _ hg, ofFinite_elementCoeff χ hg]
  rfl

/-- Complex conjugation reverses the angular type and conjugates the actual
finite residue character on the same finite modulus. -/
def conjugate (χ : AngularCharacter) : AngularCharacter where
  k := -χ.k
  modulus := χ.modulus
  modulus_ne_bot := χ.modulus_ne_bot
  residue := star χ.residue
  unit_compatible u := by
    rw [MulChar.star_apply, alpha_neg_zpow (Units.ne_zero u), ← star_mul',
      χ.unit_compatible u, star_one]

@[simp] theorem conjugate_k (χ : AngularCharacter) : χ.conjugate.k = -χ.k := rfl

theorem conjugate_elementCoeff (χ : AngularCharacter) (a : O) :
    χ.conjugate.elementCoeff a = star (χ.elementCoeff a) := by
  by_cases ha : a = 0
  · simp [ha]
  rw [elementCoeff_eq _ ha, elementCoeff_eq _ ha]
  change alpha a ^ (-χ.k) * (star χ.residue) (Ideal.Quotient.mk χ.modulus a) = _
  rw [MulChar.star_apply, alpha_neg_zpow ha, star_mul']

theorem conjugate_idealHom (χ : AngularCharacter) (I : Ideal O) :
    χ.conjugate.idealHom I = star (χ.idealHom I) := by
  rw [← Ideal.span_singleton_generator I, idealHom_span, idealHom_span,
    conjugate_elementCoeff]

theorem conjugate_conjugate_idealHom (χ : AngularCharacter) (I : Ideal O) :
    χ.conjugate.conjugate.idealHom I = χ.idealHom I := by
  rw [conjugate_idealHom, conjugate_idealHom, star_star]

/-- Multiplication of physical angular characters. The finite modulus is the
intersection so that all original conductor zeros are preserved. -/
def product (χ ψ : AngularCharacter) : AngularCharacter where
  k := χ.k + ψ.k
  modulus := χ.modulus ⊓ ψ.modulus
  modulus_ne_bot := Ideal.inf_ne_bot_of_ne_bot χ.modulus_ne_bot ψ.modulus_ne_bot
  residue := ResidueCharacter.product χ.modulus ψ.modulus χ.residue ψ.residue
  unit_compatible u := by
    rw [ResidueCharacter.product_mk,
      zpow_add₀ (alpha_ne_zero (Units.ne_zero u))]
    calc
      _ = (alpha (u : O) ^ χ.k * χ.residue (Ideal.Quotient.mk χ.modulus (u : O))) *
          (alpha (u : O) ^ ψ.k * ψ.residue (Ideal.Quotient.mk ψ.modulus (u : O))) := by ring
      _ = 1 := by rw [χ.unit_compatible, ψ.unit_compatible, one_mul]

@[simp] theorem product_k (χ ψ : AngularCharacter) : (χ.product ψ).k = χ.k + ψ.k := rfl

theorem product_elementCoeff (χ ψ : AngularCharacter) (a : O) :
    (χ.product ψ).elementCoeff a = χ.elementCoeff a * ψ.elementCoeff a := by
  by_cases ha : a = 0
  · simp [ha]
  rw [elementCoeff_eq _ ha, elementCoeff_eq _ ha, elementCoeff_eq _ ha]
  change alpha a ^ (χ.k + ψ.k) *
    ResidueCharacter.product χ.modulus ψ.modulus χ.residue ψ.residue
      (Ideal.Quotient.mk (χ.modulus ⊓ ψ.modulus) a) = _
  rw [ResidueCharacter.product_mk, zpow_add₀ (alpha_ne_zero ha)]
  ring

theorem product_idealHom (χ ψ : AngularCharacter) (I : Ideal O) :
    (χ.product ψ).idealHom I = χ.idealHom I * ψ.idealHom I := by
  rw [← Ideal.span_singleton_generator I, idealHom_span, idealHom_span,
    idealHom_span, product_elementCoeff]

theorem finite_twist_preserves_type (χ : AngularCharacter) (ψ : HeckeFamily.Character) :
    (χ.product (ofFinite ψ)).k = χ.k := by simp

/-- Enlarge the conductor with the original OAI-003 residue inflation. The
new local zeros remain in the coefficient; no cancellation removes them. -/
def inflate (χ : AngularCharacter) (M : Ideal O) (hM : M ≠ ⊥)
    (h : M ≤ χ.modulus) : AngularCharacter where
  k := χ.k
  modulus := M
  modulus_ne_bot := hM
  residue := ResidueCharacter.inflate h χ.residue
  unit_compatible u := by
    rw [ResidueCharacter.inflate_mk]
    simp only [u.isUnit.map (Ideal.Quotient.mk M), ite_true, χ.unit_compatible]

@[simp] theorem inflate_k (χ : AngularCharacter) (M : Ideal O) (hM : M ≠ ⊥)
    (h : M ≤ χ.modulus) : (χ.inflate M hM h).k = χ.k := rfl

theorem inflate_elementCoeff (χ : AngularCharacter) (M : Ideal O) (hM : M ≠ ⊥)
    (h : M ≤ χ.modulus) (a : O) :
    (χ.inflate M hM h).elementCoeff a =
      if IsUnit (Ideal.Quotient.mk M a) then χ.elementCoeff a else 0 := by
  by_cases ha : a = 0
  · simp [ha]
  rw [elementCoeff_eq _ ha, elementCoeff_eq _ ha]
  change alpha a ^ χ.k * ResidueCharacter.inflate h χ.residue
    (Ideal.Quotient.mk M a) = _
  rw [ResidueCharacter.inflate_mk]
  split_ifs <;> simp only [mul_zero]

theorem inflate_idealHom (χ : AngularCharacter) (M : Ideal O) (hM : M ≠ ⊥)
    (h : M ≤ χ.modulus) (I : Ideal O) :
    (χ.inflate M hM h).idealHom I = if IsCoprime I M then χ.idealHom I else 0 := by
  rw [← Ideal.span_singleton_generator I, idealHom_span, idealHom_span,
    inflate_elementCoeff]
  simp only [IdealCharacter.isUnit_mk_iff_isCoprime]

end AngularCharacter
end
end OAI.SevenEighths.Angular
