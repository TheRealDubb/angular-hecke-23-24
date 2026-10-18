import AngularCharacter
import OAI.NumberTheory.DirichletL.Hecke.Euler

/-!
# The actual angular ideal Dirichlet series in its convergence half-plane

All results about `series` below carry `1 < s.re`. This totalized tsum is not
called an analytic continuation, and no conclusion below 1 is drawn from it.
The coefficient is the actual generator-independent angular ideal character.
-/

namespace OAI.SevenEighths.Angular.AngularCharacter

noncomputable section
open scoped BigOperators Classical ComplexConjugate
open Complex
open SmoothMobiusCorrection (PrimeIdeal)

def idealTerm (χ : AngularCharacter) (s : ℂ) (I : Ideal O) : ℂ :=
  χ.idealHom I / (Ideal.absNorm I : ℂ) ^ s

theorem idealTerm_eq_weighted (χ : AngularCharacter) (s : ℂ) (I : Ideal O) :
    χ.idealTerm s I = IdealEuler.weighted χ.idealHom s I := by
  change χ.idealHom I / (Ideal.absNorm I : ℂ)^s =
    χ.idealHom I * CubicEisenstein.fullIdealWeight s I
  by_cases hI : I = 0
  · rw [hI, map_zero]
    simp
  · simp only [CubicEisenstein.fullIdealWeight, hI, ite_false,
      Complex.cpow_neg, div_eq_mul_inv]

/-- The defining Dirichlet series, used here only for Re(s)>1. -/
def series (χ : AngularCharacter) (s : ℂ) : ℂ :=
  IdealEuler.series χ.idealHom s

theorem series_eq_tsum (χ : AngularCharacter) (s : ℂ) :
    χ.series s = ∑' I : Ideal O, χ.idealTerm s I := by
  unfold series IdealEuler.series
  exact tsum_congr (fun I => (idealTerm_eq_weighted χ s I).symm)

theorem summable_norm (χ : AngularCharacter) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I : Ideal O => ‖χ.idealTerm s I‖) := by
  simp_rw [idealTerm_eq_weighted]
  exact IdealEuler.weighted_summable_norm χ.idealHom χ.norm_idealHom_le_one s hs

theorem hasSum_series (χ : AngularCharacter) (s : ℂ) (hs : 1 < s.re) :
    HasSum (χ.idealTerm s) (χ.series s) := by
  rw [series_eq_tsum]
  exact (summable_norm χ s hs).of_norm.hasSum

theorem series_ne_zero (χ : AngularCharacter) (s : ℂ) (hs : 1 < s.re) :
    χ.series s ≠ 0 :=
  IdealEuler.series_ne_zero χ.idealHom χ.norm_idealHom_le_one s hs

theorem series_hasProd (χ : AngularCharacter) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeal => (1 - χ.idealTerm s P.val)⁻¹) (χ.series s) := by
  simp_rw [idealTerm_eq_weighted]
  exact IdealEuler.euler_hasProd χ.idealHom χ.norm_idealHom_le_one s hs

theorem inverseSeries_mul_series (χ : AngularCharacter) (s : ℂ) (hs : 1 < s.re) :
    IdealEuler.inverseSeries χ.idealHom s * χ.series s = 1 :=
  IdealEuler.inverseSeries_mul_series χ.idealHom χ.norm_idealHom_le_one s hs

theorem idealTerm_conjugate (χ : AngularCharacter) (s : ℂ) (I : Ideal O) :
    χ.conjugate.idealTerm s I = conj (χ.idealTerm (conj s) I) := by
  by_cases hI : I = 0
  · subst I
    simp only [idealTerm, map_zero, zero_div]
  have hN : (0 : ℝ) < I.absNorm := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hpow := Complex.cpow_conj ((I.absNorm : ℝ) : ℂ) (conj s)
    (by rw [Complex.arg_ofReal_of_nonneg hN.le]; exact Real.pi_ne_zero.symm)
  simp only [conj_ofReal, conj_conj] at hpow
  unfold idealTerm
  rw [conjugate_idealHom, map_div₀]
  congr 1

/-- Conjugation for the actual series in the half-plane of absolute convergence.
The continuation step is intentionally not asserted. -/
theorem series_conjugate (χ : AngularCharacter) (s : ℂ) (_hs : 1 < s.re) :
    χ.conjugate.series s = conj (χ.series (conj s)) := by
  rw [series_eq_tsum, series_eq_tsum, conj_tsum]
  exact tsum_congr (idealTerm_conjugate χ s)

theorem ofFinite_series (χ : HeckeFamily.Character) (s : ℂ) (hs : 1 < s.re) :
    (ofFinite χ).series s = HeckeFamily.LFunction χ s := by
  rw [HeckeFamily.LFunction_eq_series χ hs]
  unfold series
  rw [ofFinite_idealHom]
  rfl

/-- Conductor enlargement keeps the exact finite Euler factors. -/
theorem inflate_series (χ : AngularCharacter) (M : Ideal O) (hM : M ≠ ⊥)
    (h : M ≤ χ.modulus) (s : ℂ) (hs : 1 < s.re) :
    (χ.inflate M hM h).series s = χ.series s *
      ∏ P ∈ SmoothMobiusCorrection.primeSet M, (1 - χ.idealTerm s P.val) := by
  simp_rw [idealTerm_eq_weighted]
  exact IdealEuler.series_of_coprime_mask M hM _ _ χ.norm_idealHom_le_one
    (χ.inflate_idealHom M hM h) s hs

/-- Deleting arbitrary finitely many prime ideals does not erase existing zeros. -/
theorem deleted_series (χ : AngularCharacter) (S : Finset PrimeIdeal)
    (s : ℂ) (hs : 1 < s.re) :
    IdealEuler.series (IdealEuler.deletePrimes S χ.idealHom) s = χ.series s *
      ∏ P ∈ S, (1 - χ.idealTerm s P.val) := by
  simp_rw [idealTerm_eq_weighted]
  exact IdealEuler.series_deletePrimes S χ.idealHom χ.norm_idealHom_le_one s hs

end
end OAI.SevenEighths.Angular.AngularCharacter
