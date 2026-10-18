import AngularThetaBasic
import AngularGaussianPaper

/-! Primitive harmonic theta reflection, derived from the actual Schwartz Fourier
identity and the pinned finite-character Poisson formula. No continuation or
zero-free conclusion is assumed or defined here. -/

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace OAI.SevenEighths.Angular.ThetaTransform

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open OAI.SevenEighths.Angular.Polynomial ThetaMellin

def phaseSign (k : ℤ) : ℂ := if 0 ≤ k then 1 else (-1 : ℂ) ^ k.natAbs

theorem norm_phaseSign (k : ℤ) : ‖phaseSign k‖ = 1 := by
  unfold phaseSign
  split <;> simp

theorem paperFourier_test (k : ℤ) (a : ℝ) (ha : 0 < a) (u : ℂ) :
    paperFourier (test k a ha) u = phaseSign k *
      (2 / ((Real.sqrt 3 : ℂ) * a)) ^ (k.natAbs + 1) *
      harmonic (-k) u * GaussianTheta.gaussian (4 / (3 * a)) u := by
  rw [harmonic_neg]
  by_cases hk : 0 ≤ k
  · simp only [test, hk, ite_true, phaseSign, Polynomial.harmonic, star_pow, one_mul]
    simpa only [GaussianSchwartz.gaussian_apply, GaussianTheta.gaussian] using
      GaussianFourier.paperFourier_holo a ha k.natAbs u
  · simp only [test, hk, ite_false, phaseSign, Polynomial.harmonic, star_pow, star_star]
    simpa only [GaussianSchwartz.gaussian_apply, GaussianTheta.gaussian] using
      GaussianFourier.paperFourier_anti a ha k.natAbs u

theorem gaussian_div (a : ℝ) (z w : ℂ) :
    GaussianTheta.gaussian a (z / w) =
      GaussianTheta.gaussian (a / ‖w‖ ^ 2) z := by
  unfold GaussianTheta.gaussian
  rw [norm_div]
  push_cast
  congr 1
  ring

variable (c : O) [NeZero c]

def rawTheta (k : ℤ) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) : ℂ :=
  ∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) * harmonic k (eisEmbedding z) *
    GaussianTheta.gaussian (GaussianTheta.parameter c t) (eisEmbedding z)

def epsilon (k : ℤ) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ :=
  phaseSign k * alpha c ^ k * TraceCharacter.normalizedGauss c χ

theorem norm_epsilon (k : ℤ) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) : ‖epsilon c k χ‖ = 1 := by
  simp [epsilon, norm_phaseSign, norm_zpow,
    norm_alpha (NeZero.ne c), TraceCharacter.normalizedGauss_norm c χ hχ]

theorem parameter_fourier_scalar (t : ℝ) (ht : 0 < t) :
    2 / ((Real.sqrt 3 : ℂ) * GaussianTheta.parameter c t) =
      (‖eisEmbedding c‖ : ℂ) / t := by
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hq : (‖eisEmbedding c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  unfold GaussianTheta.parameter
  push_cast
  field_simp

theorem test_transform_scaled (k : ℤ) (t : ℝ) (ht : 0 < t) (z : O) :
    paperFourier (test k (GaussianTheta.parameter c t) (GaussianTheta.parameter_pos c t ht))
      (eisEmbedding z / eisEmbedding c) =
    (phaseSign k * ((‖eisEmbedding c‖ : ℂ) / t) ^ (k.natAbs + 1) /
      harmonic (-k) (eisEmbedding c)) * harmonic (-k) (eisEmbedding z) *
        GaussianTheta.gaussian (GaussianTheta.parameter c (1 / t)) (eisEmbedding z) := by
  rw [paperFourier_test, parameter_fourier_scalar c t ht, harmonic_div, gaussian_div]
  have hp : (4 / (3 * GaussianTheta.parameter c t)) / ‖eisEmbedding c‖ ^ 2 =
      GaussianTheta.parameter c (1 / t) := by
    rw [div_div, mul_assoc, GaussianTheta.parameter_dual c t ht]
  rw [hp]
  ring

theorem reflection_scalar (k : ℤ) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 0 < t) :
    (TraceCharacter.gaussScalar c χ / (Ideal.absNorm (Ideal.span {c}) : ℂ)) *
      (phaseSign k * ((‖eisEmbedding c‖ : ℂ) / t) ^ (k.natAbs + 1) /
        harmonic (-k) (eisEmbedding c)) =
      epsilon c k χ / (t : ℂ) ^ (k.natAbs + 1) := by
  have hq : (‖eisEmbedding c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hα : alpha c ≠ 0 := alpha_ne_zero (NeZero.ne c)
  have hN : (Ideal.absNorm (Ideal.span {c}) : ℂ) = (‖eisEmbedding c‖ : ℂ) ^ 2 := by
    exact_mod_cast (eisEmbedding_norm_sq_eq_absNorm_span c).symm
  rw [hN, harmonic_embedding (-k) c (NeZero.ne c), Int.natAbs_neg, zpow_neg]
  unfold epsilon TraceCharacter.normalizedGauss
  simp only [div_pow, pow_succ]
  field_simp

theorem rawTheta_functional_equation (k : ℤ) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) (ht : 0 < t) :
    rawTheta c k χ t = (epsilon c k χ / (t : ℂ) ^ (k.natAbs + 1)) *
      rawTheta c (-k) χ⁻¹ (1 / t) := by
  have hp := TraceCharacter.primitive_paper_poisson c
    (test k (GaussianTheta.parameter c t) (GaussianTheta.parameter_pos c t ht)) χ hχ
  simp_rw [test_apply, test_transform_scaled c k t ht] at hp
  have hl : (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      (harmonic k (eisEmbedding z) *
        GaussianTheta.gaussian (GaussianTheta.parameter c t) (eisEmbedding z))) =
      rawTheta c k χ t := by
    unfold rawTheta
    apply tsum_congr
    intro z
    ring
  rw [hl] at hp
  rw [hp, ← reflection_scalar c k χ t ht, mul_assoc]
  congr 1
  unfold rawTheta
  rw [← tsum_mul_left]
  apply tsum_congr
  intro z
  ring

omit [NeZero c] in
theorem parameter_one_mul (t : ℝ) :
    GaussianTheta.parameter c 1 * t = GaussianTheta.parameter c t := by
  unfold GaussianTheta.parameter
  ring

omit [NeZero c] in
/-- The raw primitive theta is the actual angular-character theta; the only
transport identifies its finite modulus with the chosen principal generator. -/
theorem rawTheta_eq_theta (χ : AngularCharacter) (hmod : χ.modulus = Ideal.span {c})
    (t : ℝ) :
    rawTheta c χ.k (hmod ▸ χ.residue) t =
      theta χ (GaussianTheta.parameter c 1) t := by
  rcases χ with ⟨k, M, hM, ρ, hu⟩
  dsimp only at hmod
  subst M
  simp only [rawTheta, theta, thetaTerm, weightedCoeff, parameter_one_mul]

/-- The primitive functional equation for the actual angular family and its
actual conjugate, including non-unit-trivial residue characters. -/
theorem theta_functional_equation (χ : AngularCharacter)
    (hmod : χ.modulus = Ideal.span {c})
    (hχ : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue))
    (t : ℝ) (ht : 0 < t) :
    theta χ (GaussianTheta.parameter c 1) t =
      (epsilon c χ.k (hmod ▸ χ.residue) / (t : ℂ) ^ (χ.k.natAbs + 1)) *
      theta χ.conjugate (GaussianTheta.parameter c 1) (1 / t) := by
  rcases χ with ⟨k, M, hM, ρ, hu⟩
  dsimp only at hmod
  subst M
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
  have hp := rawTheta_functional_equation c k ρ hχ t ht
  simp only [rawTheta, theta, thetaTerm, weightedCoeff, parameter_one_mul,
    AngularCharacter.conjugate, MulChar.star_eq_inv] at hp ⊢
  convert! hp using 1

/-- Centering keeps both possible origin terms explicit, including type zero. -/
theorem centeredTheta_functional_equation (χ : AngularCharacter)
    (hmod : χ.modulus = Ideal.span {c})
    (hχ : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue))
    (t : ℝ) (ht : 0 < t) :
    centeredTheta χ (GaussianTheta.parameter c 1) t =
      (epsilon c χ.k (hmod ▸ χ.residue) / (t : ℂ) ^ (χ.k.natAbs + 1)) *
        centeredTheta χ.conjugate (GaussianTheta.parameter c 1) (1 / t) +
      (epsilon c χ.k (hmod ▸ χ.residue) / (t : ℂ) ^ (χ.k.natAbs + 1)) *
        weightedCoeff χ.conjugate 0 - weightedCoeff χ 0 := by
  unfold centeredTheta
  rw [theta_functional_equation c χ hmod hχ t ht]
  ring

theorem centeredTheta_functional_equation_nonzero (χ : AngularCharacter)
    (hmod : χ.modulus = Ideal.span {c})
    (hχ : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue)) (hk : χ.k ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    centeredTheta χ (GaussianTheta.parameter c 1) t =
      (epsilon c χ.k (hmod ▸ χ.residue) / (t : ℂ) ^ (χ.k.natAbs + 1)) *
        centeredTheta χ.conjugate (GaussianTheta.parameter c 1) (1 / t) := by
  rw [centeredTheta_eq_theta_of_nonzero_type χ hk,
    centeredTheta_eq_theta_of_nonzero_type χ.conjugate (by simpa using hk)]
  exact theta_functional_equation c χ hmod hχ t ht

end OAI.SevenEighths.Angular.ThetaTransform
