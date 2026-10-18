import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Exact signed-type bookkeeping for the paired moment route

These index identities do not prove that a moment estimate exists, that an
actual source call has this type, or that a continued L-function is zero-free.
They identify the nonzero completed harmonics that those future bridges need.
-/
namespace OAI.SevenEighths.Angular.Orientation

inductive RowSign where
  | negative
  | positive
  deriving DecidableEq

def exponent : RowSign → ℤ
  | .negative => -1
  | .positive => 1

def flip : RowSign → RowSign
  | .negative => .positive
  | .positive => .negative

def canonicalType (k : ℤ) (e : RowSign) : ℤ := -exponent e * k
def harmonic (k : ℤ) (e : RowSign) : ℤ := canonicalType k e - 1

/-- This is a paired family, not the Cartesian product of both signs. -/
def Paired (n : ℕ) (k : ℤ) (e : RowSign) : Prop :=
  k = 0 ∨ (k = -(n : ℤ) ∧ e = .negative) ∨ (k = (n : ℤ) ∧ e = .positive)

theorem canonical_conjugation (k : ℤ) (e : RowSign) :
    canonicalType (-k) (flip e) = canonicalType k e := by
  cases e <;> simp [canonicalType, exponent, flip]

theorem paired_conjugation (n : ℕ) (k : ℤ) (e : RowSign) :
    Paired n k e → Paired n (-k) (flip e) := by
  rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact Or.inl (neg_zero)
  · exact Or.inr (Or.inr ⟨neg_neg _, rfl⟩)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

theorem paired_canonical (n : ℕ) (k : ℤ) (e : RowSign) (h : Paired n k e) :
    canonicalType k e = 0 ∨ canonicalType k e = -(n : ℤ) := by
  rcases h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; simp [canonicalType]
  · right; simp [canonicalType, exponent]
  · right; simp [canonicalType, exponent]

theorem paired_harmonic_negative (n : ℕ) (k : ℤ) (e : RowSign)
    (h : Paired n k e) : harmonic k e < 0 := by
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  rcases paired_canonical n k e h with hcan | hcan <;>
    simp only [harmonic, hcan] <;> omega

theorem paired_harmonic_nonzero (n : ℕ) (k : ℤ) (e : RowSign)
    (h : Paired n k e) : harmonic k e ≠ 0 :=
  ne_of_lt (paired_harmonic_negative n k e h)

theorem negative_target_harmonic (n : ℕ) :
    harmonic (-(n : ℤ)) .negative = -(n : ℤ) - 1 := by
  simp [harmonic, canonicalType, exponent]

theorem positive_parent_harmonic (n : ℕ) :
    harmonic (n : ℤ) .positive = -(n : ℤ) - 1 := by
  simp [harmonic, canonicalType, exponent]

theorem exceptional_safe_pairs :
    harmonic (-1) .negative = -2 ∧ harmonic 1 .positive = -2 := by
  norm_num [harmonic, canonicalType, exponent]

/-- Negative control: the two omitted orientations really do reach harmonic 0. -/
theorem exceptional_wrong_pairs :
    harmonic (-1) .positive = 0 ∧ harmonic 1 .negative = 0 := by
  norm_num [harmonic, canonicalType, exponent]

end OAI.SevenEighths.Angular.Orientation
