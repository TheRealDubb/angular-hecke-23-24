import AngularCharacter
import OAI.NumberTheory.DirichletL.Eisenstein.RamifiedTransform

/-! Exact arithmetic identification of higher differentiated primary-pair
coefficients. Only the finite residue part is evaluated on the finite
quotient. The angular factor is supplied by the extra physical derivatives.
All scales from the pinned order-one identity are retained explicitly. -/

noncomputable section
open scoped Classical

namespace OAI.CubicEisenstein.AngularCompletedCoefficient

open CompletedGauss EisensteinEmbedding ConcreteTraceCRT
open SevenEighths.Angular

/-- The finite factor of an actual angular character. This definition does
not descend the full angular character to a finite quotient. -/
def finiteResidueHom (χ : AngularCharacter) : ActualEisensteinCubic.O →* ℂ where
  toFun a := χ.residue (Ideal.Quotient.mk χ.modulus a)
  map_one' := by simp
  map_mul' a b := by simp

theorem finiteResidueHom_apply (χ : AngularCharacter) (a : ActualEisensteinCubic.O) :
    finiteResidueHom χ a = χ.residue (Ideal.Quotient.mk χ.modulus a) := rfl

/-- Only the finite residue factor is periodic modulo the finite modulus. -/
theorem finiteResidueHom_factorsModulo (χ : AngularCharacter) :
    CanonicalCoefficientClass.FactorsModulo χ.modulus (finiteResidueHom χ) := by
  intro x y hxy
  change χ.residue (Ideal.Quotient.mk χ.modulus x) =
    χ.residue (Ideal.Quotient.mk χ.modulus y)
  exact congrArg χ.residue (Ideal.Quotient.eq.mpr hxy)

theorem finiteResidueHom_norm_le_one (χ : AngularCharacter) (a : ActualEisensteinCubic.O) :
    ‖finiteResidueHom χ a‖ ≤ 1 := by
  let : Finite (ActualEisensteinCubic.O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact SevenEighths.IdealCharacter.norm_residue_le_one χ.modulus χ.residue _

/-- The exact physical generator norm, recovered from the pinned frequency
formula without dropping its theta frequency scale. -/
theorem thetaPair_embedding_norm (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val ≠ 0) (hJ : primaryGenerator J.val ≠ 0) :
    ‖eisEmbedding (primaryGenerator I.val * (primaryGenerator J.val) ^ 3)‖ =
      Real.sqrt (completedMellinLength (I,J)) := by
  have he := thetaPair_frequency_norm I J hI hJ
  rw [cuspFrequency_eq_thetaFrequencyScale, norm_mul] at he
  exact mul_left_cancel₀ thetaBesselScale_pos.ne' he

/-- A conjugate generator power is its negative angular phase times its
positive radial power. Nonvanishing is needed for the normalized phase. -/
theorem star_embedding_pow (a : ActualEisensteinCubic.O) (ha : a ≠ 0) (n : ℕ) :
    star (eisEmbedding a) ^ n =
      alpha a ^ (-(n : ℤ)) * (‖eisEmbedding a‖ : ℂ) ^ n := by
  have hn : (‖eisEmbedding a‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))
  have hs : star (eisEmbedding a) = star (alpha a) * (‖eisEmbedding a‖ : ℂ) := by
    simp only [alpha, FiniteGaussPhase.angularFactor, Complex.star_def,
      map_div₀, Complex.conj_ofReal]
    exact (div_mul_cancel₀ _ hn).symm
  rw [alpha_neg_zpow ha, zpow_natCast, star_pow, hs, mul_pow]

theorem thetaPair_star_embedding_pow (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val ≠ 0) (hJ : primaryGenerator J.val ≠ 0) (n : ℕ) :
    star (eisEmbedding (primaryGenerator I.val * (primaryGenerator J.val) ^ 3)) ^ n =
      alpha (primaryGenerator I.val * (primaryGenerator J.val) ^ 3) ^ (-(n : ℤ)) *
        (Real.sqrt (completedMellinLength (I,J)) : ℂ) ^ n := by
  rw [star_embedding_pow _ (mul_ne_zero hI (pow_ne_zero 3 hJ)),
    thetaPair_embedding_norm I J hI hJ]

/-- The extra n physical derivative factors retain the frequency scalar
and split into their angular phase and radial power. -/
theorem thetaPair_extra_derivative_factor (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val ≠ 0) (hJ : primaryGenerator J.val ≠ 0) (n : ℕ) :
    (-2 * Real.pi * Complex.I *
      star (cuspFrequency (primaryGenerator I.val * (primaryGenerator J.val) ^ 3))) ^ n =
      (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n *
        alpha (primaryGenerator I.val * (primaryGenerator J.val) ^ 3) ^ (-(n : ℤ)) *
          (Real.sqrt (completedMellinLength (I,J)) : ℂ) ^ n := by
  have hf : -2 * Real.pi * Complex.I *
      star (cuspFrequency (primaryGenerator I.val * (primaryGenerator J.val) ^ 3)) =
      (-2 * Real.pi * Complex.I * star thetaFrequencyScale) *
        star (eisEmbedding (primaryGenerator I.val * (primaryGenerator J.val) ^ 3)) := by
    rw [cuspFrequency_eq_thetaFrequencyScale, star_mul]
    ring
  rw [hf, mul_pow, thetaPair_star_embedding_pow I J hI hJ n]
  ring

/-- Exact coefficient at derivative order n+1, obtained by multiplying the
pinned order-one theorem by the n additional actual frequency factors. -/
theorem thetaPair_higher_derivative_coefficient (Ψ : ActualEisensteinCubic.O →* ℂ)
    (I J : NonzeroIdeal) (hI : primaryGenerator I.val ≠ 0)
    (hJ : primaryGenerator J.val ≠ 0) (hsq : Squarefree I.val) (n : ℕ) :
    (-2 * Real.pi * Complex.I *
      star (cuspFrequency (primaryGenerator I.val * (primaryGenerator J.val) ^ 3))) ^ (n+1) *
      fixedThetaTwist Ψ (primaryGenerator I.val * (primaryGenerator J.val) ^ 3) *
        star (sourceResidualFourierCoefficient
          (primaryGenerator I.val * (primaryGenerator J.val) ^ 3)) =
      thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n *
        (alpha (primaryGenerator I.val * (primaryGenerator J.val) ^ 3) ^ (-(n : ℤ)) *
          completedMellinCoefficient Ψ (I,J)) *
        ((completedMellinLength (I,J) : ℂ) *
          (Real.sqrt (completedMellinLength (I,J)) : ℂ) ^ n) := by
  let A : ℂ := -2 * Real.pi * Complex.I *
    star (cuspFrequency (primaryGenerator I.val * (primaryGenerator J.val) ^ 3))
  have hbase := thetaPair_derivative_coefficient Ψ I J hI hJ hsq
  have he := congrArg (fun z : ℂ => A ^ n * z) hbase
  have hp := thetaPair_extra_derivative_factor I J hI hJ n
  change A ^ n = _ at hp
  rw [hp] at he
  calc
    _ = A ^ n * (A * fixedThetaTwist Ψ
        (primaryGenerator I.val * (primaryGenerator J.val) ^ 3) *
      star (sourceResidualFourierCoefficient
        (primaryGenerator I.val * (primaryGenerator J.val) ^ 3))) := by
          change A ^ (n+1) * _ * _ = _
          rw [pow_succ]
          ring
    _ = _ := by
      rw [hp]
      convert! he using 1; ring

/-- The negative angular phase is exactly the physical element character
at the requested type, with only the finite factor using the quotient. -/
theorem elementHom_negative_type (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (a : ActualEisensteinCubic.O) (ha : a ≠ 0) :
    χ.elementHom.toMonoidHom a = alpha a ^ (-(n : ℤ)) * finiteResidueHom χ a := by
  change χ.elementCoeff a = _
  rw [χ.elementCoeff_eq ha, hk]
  rfl

/-- Multiplying the finite completed coefficient by the phase gives the
completed coefficient of the actual angular element homomorphism. -/
theorem completedCoefficient_angular_phase (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val ≠ 0) (hJ : primaryGenerator J.val ≠ 0)
    (hsq : Squarefree I.val) :
    alpha (primaryGenerator I.val * (primaryGenerator J.val) ^ 3) ^ (-(n : ℤ)) *
      completedMellinCoefficient (finiteResidueHom χ) (I,J) =
        completedMellinCoefficient χ.elementHom.toMonoidHom (I,J) := by
  have hl : (completedMellinLength (I,J) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (completedMellinLength_pos (I,J)).ne'
  apply mul_right_cancel₀ hl
  rw [mul_assoc, completedCoefficient_mul_length _ I J hI hJ hsq,
    completedCoefficient_mul_length _ I J hI hJ hsq]
  have he := elementHom_negative_type χ n hk
    (primaryGenerator I.val * (primaryGenerator J.val) ^ 3)
    (mul_ne_zero hI (pow_ne_zero 3 hJ))
  simp only [map_mul, map_pow] at he
  calc
    _ = star (eisEmbedding (primaryGenerator I.val * (primaryGenerator J.val) ^ 3)) *
        (‖eisEmbedding (primaryGenerator J.val)‖ : ℂ) * gaussTwo I.val hI *
        (alpha (primaryGenerator I.val * (primaryGenerator J.val) ^ 3) ^ (-(n : ℤ)) *
          (finiteResidueHom χ (primaryGenerator I.val) *
            finiteResidueHom χ (primaryGenerator J.val) ^ 3)) := by ring
    _ = _ := by rw [← he]; ring

/-- Higher differentiated physical coefficients realize the actual negative
angular type. All theta and length factors are shown rather than absorbed. -/
theorem thetaPair_angular_derivative_coefficient (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val ≠ 0) (hJ : primaryGenerator J.val ≠ 0)
    (hsq : Squarefree I.val) :
    (-2 * Real.pi * Complex.I *
      star (cuspFrequency (primaryGenerator I.val * (primaryGenerator J.val) ^ 3))) ^ (n+1) *
      fixedThetaTwist (finiteResidueHom χ)
        (primaryGenerator I.val * (primaryGenerator J.val) ^ 3) *
        star (sourceResidualFourierCoefficient
          (primaryGenerator I.val * (primaryGenerator J.val) ^ 3)) =
      thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n *
        completedMellinCoefficient χ.elementHom.toMonoidHom (I,J) *
        ((completedMellinLength (I,J) : ℂ) *
          (Real.sqrt (completedMellinLength (I,J)) : ℂ) ^ n) := by
  rw [thetaPair_higher_derivative_coefficient _ I J hI hJ hsq n,
    completedCoefficient_angular_phase χ n hk I J hI hJ hsq]

/-- The same physical element value is the generator-independent ideal
character value, using the actual primary-generator span theorem. -/
theorem idealHom_primaryGenerator (χ : AngularCharacter) (I : NonzeroIdeal)
    (hI : primaryGenerator I.val ≠ 0) :
    χ.idealHom I.val = χ.elementCoeff (primaryGenerator I.val) :=
  χ.idealHom_of_generator (primaryGenerator_spec I.val hI).1

theorem idealHom_primaryGenerator_negative_type (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (I : NonzeroIdeal) (hI : primaryGenerator I.val ≠ 0) :
    χ.idealHom I.val = alpha (primaryGenerator I.val) ^ (-(n : ℤ)) *
      finiteResidueHom χ (primaryGenerator I.val) := by
  rw [idealHom_primaryGenerator χ I hI, χ.elementCoeff_eq hI, hk]
  rfl

end OAI.CubicEisenstein.AngularCompletedCoefficient
