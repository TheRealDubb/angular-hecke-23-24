import AngularCharacter
import AngularOrientation

/-!
# Paired orientations of actual angular Hecke coefficients

An oriented character carries the physical finite residue character and angular
type from `AngularCharacter`, not a formal type symbol alone. Its canonical
child is the original character for a negative row and its actual conjugate
for a positive row. The resulting coefficient identities and negative harmonic
are proved below.

The `paired` field states the explicit index restriction for this construction.
This module does not prove that the detector, affine, inverse, plain, or error
calls in the source argument satisfy that restriction. Those source-call
membership proofs, the harmonic transform and all moment estimates remain
separate analytic obligations. No zero-free theorem is claimed here.
-/

namespace OAI.SevenEighths.Angular

noncomputable section
open scoped Classical
open OAI.SevenEighths.Angular.Orientation

/-- A physical character together with one allowed orientation. -/
structure OrientedCharacter (n : ℕ) where
  character : AngularCharacter
  row : RowSign
  paired : Paired n character.k row

namespace OrientedCharacter

variable {n : ℕ}

def negativeTarget (χ : AngularCharacter) (hk : χ.k = -(n : ℤ)) :
    OrientedCharacter n where
  character := χ
  row := .negative
  paired := Or.inr (Or.inl ⟨hk, rfl⟩)

def positiveParent (χ : AngularCharacter) (hk : χ.k = (n : ℤ)) :
    OrientedCharacter n where
  character := χ
  row := .positive
  paired := Or.inr (Or.inr ⟨hk, rfl⟩)

def finite (χ : HeckeFamily.Character) (e : RowSign) : OrientedCharacter n where
  character := AngularCharacter.ofFinite χ
  row := e
  paired := Or.inl rfl

/-- The actual coefficient character used after orientation normalization. -/
def canonicalChild (P : OrientedCharacter n) : AngularCharacter :=
  match P.row with
  | .negative => P.character
  | .positive => P.character.conjugate

theorem canonicalChild_type (P : OrientedCharacter n) :
    P.canonicalChild.k = canonicalType P.character.k P.row := by
  cases he : P.row <;> simp [canonicalChild, he, canonicalType, exponent]

theorem canonicalChild_type_options (P : OrientedCharacter n) :
    P.canonicalChild.k = 0 ∨ P.canonicalChild.k = -(n : ℤ) := by
  rw [canonicalChild_type]
  exact paired_canonical n P.character.k P.row P.paired

theorem canonicalChild_type_of_nonzero (P : OrientedCharacter n)
    (hk : P.character.k ≠ 0) : P.canonicalChild.k = -(n : ℤ) := by
  rcases P.paired with hzero | ⟨hneg, he⟩ | ⟨hpos, he⟩
  · exact (hk hzero).elim
  · simp [canonicalChild, he, hneg]
  · simp [canonicalChild, he, hpos]

/-- This index is computed from the actual canonical child's type. Its role
as the harmonic of a completed analytic transform is a future theorem. -/
def completedHarmonic (P : OrientedCharacter n) : ℤ := P.canonicalChild.k - 1

theorem completedHarmonic_eq (P : OrientedCharacter n) :
    P.completedHarmonic = harmonic P.character.k P.row := by
  rw [completedHarmonic, canonicalChild_type]
  rfl

theorem completedHarmonic_negative (P : OrientedCharacter n) :
    P.completedHarmonic < 0 := by
  rw [completedHarmonic_eq]
  exact paired_harmonic_negative n P.character.k P.row P.paired

theorem completedHarmonic_nonzero (P : OrientedCharacter n) :
    P.completedHarmonic ≠ 0 := ne_of_lt P.completedHarmonic_negative

theorem completedHarmonic_of_nonzero (P : OrientedCharacter n)
    (hk : P.character.k ≠ 0) : P.completedHarmonic = -(n : ℤ) - 1 := by
  rw [completedHarmonic, canonicalChild_type_of_nonzero P hk]

theorem exceptional_completedHarmonic (P : OrientedCharacter 1)
    (hk : P.character.k ≠ 0) : P.completedHarmonic = -2 := by
  rw [completedHarmonic_of_nonzero P hk]
  norm_num

/-- Every physical angular character admits one of these orientations.
This only chooses its coefficient orientation; it does not identify any
particular analytic source call with the chosen object. -/
def orient (χ : AngularCharacter) : OrientedCharacter χ.k.natAbs := by
  by_cases hk : χ.k ≤ 0
  · exact negativeTarget χ (by simp [abs_of_nonpos hk])
  · have hpos : 0 ≤ χ.k := le_of_lt (lt_of_not_ge hk)
    exact positiveParent χ (by simp [abs_of_nonneg hpos])

theorem orient_character (χ : AngularCharacter) : (orient χ).character = χ := by
  unfold orient
  split <;> rfl

theorem orient_canonical_type (χ : AngularCharacter) :
    (orient χ).canonicalChild.k = -(χ.k.natAbs : ℤ) := by
  by_cases hk : χ.k = 0
  · rw [canonicalChild_type, orient_character]
    simp [canonicalType, hk]
  · apply canonicalChild_type_of_nonzero
    simpa only [orient_character] using hk

theorem orient_completedHarmonic (χ : AngularCharacter) :
    (orient χ).completedHarmonic = -(χ.k.natAbs : ℤ) - 1 := by
  rw [completedHarmonic, orient_canonical_type]

theorem canonicalChild_elementCoeff (P : OrientedCharacter n) (a : O) :
    P.canonicalChild.elementCoeff a =
      match P.row with
      | .negative => P.character.elementCoeff a
      | .positive => star (P.character.elementCoeff a) := by
  cases he : P.row <;>
    simp [canonicalChild, he, AngularCharacter.conjugate_elementCoeff]

theorem canonicalChild_idealHom (P : OrientedCharacter n) (I : Ideal O) :
    P.canonicalChild.idealHom I =
      match P.row with
      | .negative => P.character.idealHom I
      | .positive => star (P.character.idealHom I) := by
  cases he : P.row <;>
    simp [canonicalChild, he, AngularCharacter.conjugate_idealHom]

/-- Whole-character conjugation also flips the row. Flipping the row alone
is deliberately not included as an allowed construction. -/
def conjugateFlip (P : OrientedCharacter n) : OrientedCharacter n where
  character := P.character.conjugate
  row := Orientation.flip P.row
  paired := paired_conjugation n P.character.k P.row P.paired

theorem conjugateFlip_type (P : OrientedCharacter n) :
    P.conjugateFlip.character.k = -P.character.k := rfl

theorem conjugateFlip_row (P : OrientedCharacter n) :
    P.conjugateFlip.row = Orientation.flip P.row := rfl

theorem conjugateFlip_canonical_type (P : OrientedCharacter n) :
    P.conjugateFlip.canonicalChild.k = P.canonicalChild.k := by
  rw [canonicalChild_type, canonicalChild_type, conjugateFlip_type,
    conjugateFlip_row, canonical_conjugation]

theorem conjugateFlip_completedHarmonic (P : OrientedCharacter n) :
    P.conjugateFlip.completedHarmonic = P.completedHarmonic := by
  rw [completedHarmonic, completedHarmonic, conjugateFlip_canonical_type]

theorem conjugateFlip_canonical_elementCoeff (P : OrientedCharacter n) (a : O) :
    P.conjugateFlip.canonicalChild.elementCoeff a = P.canonicalChild.elementCoeff a := by
  cases he : P.row <;>
    simp [canonicalChild, conjugateFlip, he, Orientation.flip,
      AngularCharacter.conjugate_elementCoeff]

theorem conjugateFlip_canonical_idealHom (P : OrientedCharacter n) (I : Ideal O) :
    P.conjugateFlip.canonicalChild.idealHom I = P.canonicalChild.idealHom I := by
  cases he : P.row <;>
    simp [canonicalChild, conjugateFlip, he, Orientation.flip,
      AngularCharacter.conjugate_idealHom]

def finiteTwist (P : OrientedCharacter n) (ψ : HeckeFamily.Character) :
    OrientedCharacter n where
  character := P.character.product (AngularCharacter.ofFinite ψ)
  row := P.row
  paired := by simpa only [AngularCharacter.finite_twist_preserves_type] using P.paired

theorem finiteTwist_type (P : OrientedCharacter n) (ψ : HeckeFamily.Character) :
    (P.finiteTwist ψ).character.k = P.character.k :=
  AngularCharacter.finite_twist_preserves_type P.character ψ

theorem finiteTwist_row (P : OrientedCharacter n) (ψ : HeckeFamily.Character) :
    (P.finiteTwist ψ).row = P.row := rfl

theorem finiteTwist_completedHarmonic (P : OrientedCharacter n)
    (ψ : HeckeFamily.Character) :
    (P.finiteTwist ψ).completedHarmonic = P.completedHarmonic := by
  rw [completedHarmonic_eq, completedHarmonic_eq, finiteTwist_type, finiteTwist_row]

theorem finiteTwist_idealHom (P : OrientedCharacter n) (ψ : HeckeFamily.Character)
    (I : Ideal O) :
    (P.finiteTwist ψ).character.idealHom I = P.character.idealHom I *
      (AngularCharacter.ofFinite ψ).idealHom I :=
  AngularCharacter.product_idealHom P.character (AngularCharacter.ofFinite ψ) I

theorem finiteTwist_canonical_idealHom (P : OrientedCharacter n)
    (ψ : HeckeFamily.Character) (I : Ideal O) :
    (P.finiteTwist ψ).canonicalChild.idealHom I = P.canonicalChild.idealHom I *
      match P.row with
      | .negative => (AngularCharacter.ofFinite ψ).idealHom I
      | .positive => star ((AngularCharacter.ofFinite ψ).idealHom I) := by
  cases he : P.row <;>
    simp [canonicalChild, finiteTwist, he, AngularCharacter.product_idealHom,
      AngularCharacter.conjugate_idealHom, star_mul']

def inflate (P : OrientedCharacter n) (M : Ideal O) (hM : M ≠ ⊥)
    (h : M ≤ P.character.modulus) : OrientedCharacter n where
  character := P.character.inflate M hM h
  row := P.row
  paired := P.paired

theorem inflate_type (P : OrientedCharacter n) (M : Ideal O) (hM : M ≠ ⊥)
    (h : M ≤ P.character.modulus) : (P.inflate M hM h).character.k = P.character.k := rfl

theorem inflate_row (P : OrientedCharacter n) (M : Ideal O) (hM : M ≠ ⊥)
    (h : M ≤ P.character.modulus) : (P.inflate M hM h).row = P.row := rfl

theorem inflate_completedHarmonic (P : OrientedCharacter n) (M : Ideal O) (hM : M ≠ ⊥)
    (h : M ≤ P.character.modulus) :
    (P.inflate M hM h).completedHarmonic = P.completedHarmonic := by
  rw [completedHarmonic_eq, completedHarmonic_eq, inflate_type, inflate_row]

theorem inflate_idealHom (P : OrientedCharacter n) (M : Ideal O) (hM : M ≠ ⊥)
    (h : M ≤ P.character.modulus) (I : Ideal O) :
    (P.inflate M hM h).character.idealHom I =
      if IsCoprime I M then P.character.idealHom I else 0 :=
  AngularCharacter.inflate_idealHom P.character M hM h I

theorem inflate_canonical_idealHom (P : OrientedCharacter n) (M : Ideal O) (hM : M ≠ ⊥)
    (h : M ≤ P.character.modulus) (I : Ideal O) :
    (P.inflate M hM h).canonicalChild.idealHom I =
      if IsCoprime I M then P.canonicalChild.idealHom I else 0 := by
  by_cases hc : IsCoprime I M <;> cases he : P.row <;>
    simp [canonicalChild, inflate, he, hc, AngularCharacter.inflate_idealHom,
      AngularCharacter.conjugate_idealHom]

end OrientedCharacter
end
end OAI.SevenEighths.Angular
