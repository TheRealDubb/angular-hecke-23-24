import AngularCharacter
import OAI.NumberTheory.DirichletL.GaussianTheta

/-!
The actual harmonic monomial for every integer angular type, and its connection
to the physical angular character. The origin is kept explicit: type zero can
have a nonzero theta constant, whereas nonzero type has none. These are algebraic
identifications for the future weighted theta/Mellin proof, not continuation.
-/

noncomputable section
open scoped Classical ComplexConjugate

namespace OAI.SevenEighths.Angular.Polynomial

open ActualEisensteinCubic EisensteinEmbedding ConcreteTraceCRT EisensteinSchwartzPoisson

def harmonic (k : ℤ) (z : ℂ) : ℂ :=
  if 0 ≤ k then z ^ k.natAbs else (star z) ^ k.natAbs

@[simp] theorem harmonic_nat (m : ℕ) (z : ℂ) :
    harmonic (m : ℤ) z = z ^ m := by simp [harmonic]

@[simp] theorem harmonic_negSucc (m : ℕ) (z : ℂ) :
    harmonic (Int.negSucc m) z = (star z) ^ (m + 1) := by simp [harmonic]

@[simp] theorem harmonic_zero_type (z : ℂ) : harmonic 0 z = 1 := by simp [harmonic]

theorem harmonic_mul (k : ℤ) (z w : ℂ) :
    harmonic k (z * w) = harmonic k z * harmonic k w := by
  unfold harmonic
  split <;> simp [mul_pow]

theorem harmonic_div (k : ℤ) (z w : ℂ) :
    harmonic k (z / w) = harmonic k z / harmonic k w := by
  unfold harmonic
  split <;> simp [div_pow]

theorem norm_harmonic (k : ℤ) (z : ℂ) : ‖harmonic k z‖ = ‖z‖ ^ k.natAbs := by
  unfold harmonic
  split <;> simp

theorem harmonic_origin (k : ℤ) : harmonic k 0 = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · have h : k.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hk
    simp [harmonic, hk, h]

theorem harmonic_neg (k : ℤ) (z : ℂ) : harmonic (-k) z = star (harmonic k z) := by
  by_cases hk : k = 0
  · simp [hk]
  by_cases hp : 0 ≤ k
  · have hn : ¬ 0 ≤ -k := by omega
    simp only [harmonic, ite_eq_left hp, ite_eq_right hn, Int.natAbs_neg, star_pow]
  · have hn : 0 ≤ -k := by omega
    simp only [harmonic, ite_eq_right hp, ite_eq_left hn, Int.natAbs_neg, star_pow, star_star]

/-- The smooth harmonic weight agrees with the radius times the actual phase. -/
theorem harmonic_phase (k : ℤ) (z : ℂ) (hz : z ≠ 0) :
    harmonic k z = (‖z‖ : ℂ) ^ k.natAbs * (z / (‖z‖ : ℂ)) ^ k := by
  have hr : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hp : ‖z / (‖z‖ : ℂ)‖ = 1 := by simp [hz]
  have hmul : (‖z‖ : ℂ) * (z / (‖z‖ : ℂ)) = z := by field_simp
  cases k with
  | ofNat m =>
      change harmonic (m : ℤ) z = (‖z‖ : ℂ) ^ m * (z / (‖z‖ : ℂ)) ^ (m : ℤ)
      rw [harmonic_nat, zpow_natCast, ← mul_pow, hmul]
  | negSucc m =>
      rw [harmonic_negSucc]
      change (star z) ^ (m + 1) = (‖z‖ : ℂ) ^ (m + 1) *
        (z / (‖z‖ : ℂ)) ^ (-((m + 1 : ℕ) : ℤ))
      rw [zpow_neg, zpow_natCast, ← inv_pow, Complex.inv_eq_conj hp, ← mul_pow]
      congr 1
      simpa only [Complex.star_def, map_mul, Complex.conj_ofReal] using congrArg star hmul.symm

theorem harmonic_embedding (k : ℤ) (a : O) (ha : a ≠ 0) :
    harmonic k (eisEmbedding a) =
      (‖eisEmbedding a‖ : ℂ) ^ k.natAbs * alpha a ^ k :=
  harmonic_phase k (eisEmbedding a) (eisEmbedding_ne_zero ha)

theorem harmonic_unit (k : ℤ) (u : Oˣ) :
    harmonic k (eisEmbedding (u : O)) = alpha (u : O) ^ k := by
  rw [harmonic_embedding k _ (Units.ne_zero u), GaussianTheta.embedding_unit_norm]
  simp

def weightedCoeff (χ : AngularCharacter) (a : O) : ℂ :=
  χ.residue (Ideal.Quotient.mk χ.modulus a) * harmonic χ.k (eisEmbedding a)

def centeredWeightedCoeff (χ : AngularCharacter) (a : O) : ℂ :=
  if a = 0 then 0 else weightedCoeff χ a

theorem weightedCoeff_origin (χ : AngularCharacter) :
    weightedCoeff χ 0 = if χ.k = 0 then χ.residue (Ideal.Quotient.mk χ.modulus 0) else 0 := by
  simp only [weightedCoeff, map_zero, harmonic_origin]
  split <;> simp

theorem weightedCoeff_eq (χ : AngularCharacter) (a : O) (ha : a ≠ 0) :
    weightedCoeff χ a =
      (‖eisEmbedding a‖ : ℂ) ^ χ.k.natAbs * χ.elementCoeff a := by
  rw [weightedCoeff, harmonic_embedding χ.k a ha, χ.elementCoeff_eq ha]
  ring

theorem centeredWeightedCoeff_eq (χ : AngularCharacter) (a : O) :
    centeredWeightedCoeff χ a =
      (‖eisEmbedding a‖ : ℂ) ^ χ.k.natAbs * χ.elementCoeff a := by
  by_cases ha : a = 0
  · simp [centeredWeightedCoeff, ha]
  · simp only [centeredWeightedCoeff, ha, ite_false]
    exact weightedCoeff_eq χ a ha

theorem weightedCoeff_unit_mul (χ : AngularCharacter) (u : Oˣ) (a : O) :
    weightedCoeff χ ((u : O) * a) = weightedCoeff χ a := by
  simp only [weightedCoeff, map_mul, harmonic_mul, harmonic_unit]
  calc
    _ = (alpha (u : O) ^ χ.k * χ.residue (Ideal.Quotient.mk χ.modulus (u : O))) *
        (χ.residue (Ideal.Quotient.mk χ.modulus a) * harmonic χ.k (eisEmbedding a)) := by ring
    _ = _ := by rw [χ.unit_compatible, one_mul]

theorem norm_weightedCoeff_le (χ : AngularCharacter) (a : O) :
    ‖weightedCoeff χ a‖ ≤ ‖eisEmbedding a‖ ^ χ.k.natAbs := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  rw [weightedCoeff, norm_mul, norm_harmonic]
  exact mul_le_of_le_one_left (by positivity)
    (IdealCharacter.norm_residue_le_one χ.modulus χ.residue _)

end OAI.SevenEighths.Angular.Polynomial
