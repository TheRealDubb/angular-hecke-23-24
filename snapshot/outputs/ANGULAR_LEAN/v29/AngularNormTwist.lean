import AngularSeries

/-! The physical unitary norm twist is an actual multiplicative ideal
coefficient, with convergence and its exact vertical-translation identity. -/
noncomputable section
open scoped Classical BigOperators
open Complex
namespace OAI.SevenEighths.Angular.NormTwist
open ActualEisensteinCubic

def normTwist (τ : ℝ) : Ideal O →*₀ ℂ where
  toFun J := if J = 0 then 0 else (J.absNorm:ℂ)^((τ:ℂ)*I)
  map_zero' := by simp
  map_one' := by simp
  map_mul' J K := by
    by_cases hJ : J = 0
    · simp [hJ]
    by_cases hK : K = 0
    · simp [hK]
    simp only [if_neg hJ,if_neg hK,if_neg (mul_ne_zero hJ hK),map_mul,Nat.cast_mul]
    exact Complex.mul_cpow_ofReal_nonneg (show (0:ℝ)≤J.absNorm by positivity)
      (show (0:ℝ)≤K.absNorm by positivity) ((τ:ℂ)*I)

theorem normTwist_apply (τ : ℝ) (J : Ideal O) :
    normTwist τ J = if J = 0 then 0 else (J.absNorm:ℂ)^((τ:ℂ)*I) := rfl

theorem norm_normTwist (τ : ℝ) (J : Ideal O) :
    ‖normTwist τ J‖ = if J = 0 then 0 else 1 := by
  rw [normTwist_apply]
  by_cases hJ : J = 0
  · simp [hJ]
  have hN : (0:ℝ) < J.absNorm := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  simp only [if_neg hJ]
  rw [show (J.absNorm:ℂ)=((J.absNorm:ℝ):ℂ) by simp,
    Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp

theorem norm_normTwist_le_one (τ : ℝ) (J : Ideal O) : ‖normTwist τ J‖ ≤ 1 := by
  rw [norm_normTwist]
  split_ifs <;> norm_num

def twistedIdealHom (χ : AngularCharacter) (τ : ℝ) : Ideal O →*₀ ℂ where
  toFun J := χ.idealHom J * normTwist τ J
  map_zero' := by simp
  map_one' := by
    change χ.idealHom 1 * normTwist τ 1 = 1
    rw [map_one,map_one,one_mul]
  map_mul' J K := by simp only [map_mul]; ring

theorem twistedIdealHom_apply (χ : AngularCharacter) (τ : ℝ) (J : Ideal O) :
    twistedIdealHom χ τ J = χ.idealHom J * normTwist τ J := rfl

theorem twistedIdealHom_norm_le_one (χ : AngularCharacter) (τ : ℝ) (J : Ideal O) :
    ‖twistedIdealHom χ τ J‖ ≤ 1 := by
  rw [twistedIdealHom_apply,norm_mul]
  exact (mul_le_mul (χ.norm_idealHom_le_one J) (norm_normTwist_le_one τ J)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem weighted_shift (χ : AngularCharacter) (τ : ℝ) (s : ℂ) (J : Ideal O) :
    IdealEuler.weighted (twistedIdealHom χ τ) s J =
      IdealEuler.weighted χ.idealHom (s-(τ:ℂ)*I) J := by
  change (χ.idealHom J * normTwist τ J) * CubicEisenstein.fullIdealWeight s J =
    χ.idealHom J * CubicEisenstein.fullIdealWeight (s-(τ:ℂ)*I) J
  by_cases hJ : J = 0
  · simp [hJ,CubicEisenstein.fullIdealWeight]
  have hN : (J.absNorm:ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hJ
  rw [normTwist_apply,if_neg hJ]
  simp only [CubicEisenstein.fullIdealWeight,if_neg hJ]
  rw [mul_assoc,←Complex.cpow_add _ _ hN]
  congr 2
  ring

theorem series_shift (χ : AngularCharacter) (τ : ℝ) (s : ℂ) :
    IdealEuler.series (twistedIdealHom χ τ) s = χ.series (s-(τ:ℂ)*I) := by
  unfold IdealEuler.series AngularCharacter.series
  exact tsum_congr (weighted_shift χ τ s)

theorem twisted_series_summable_norm (χ : AngularCharacter) (τ : ℝ)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun J : Ideal O => ‖IdealEuler.weighted (twistedIdealHom χ τ) s J‖) :=
  IdealEuler.weighted_summable_norm _ (twistedIdealHom_norm_le_one χ τ) s hs

end OAI.SevenEighths.Angular.NormTwist
