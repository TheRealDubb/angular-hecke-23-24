import AngularThetaMellin

/-!
# Genuine Mellin convergence of the actual centered angular theta

Convergence is proved from integrable exponential summands and summable
integrals of their norms. It is not inferred from an equality between totalized
integrals. The exponential estimates below reuse the proofs in Mathlib's
`NumberTheory/LSeries/MellinEqDirichlet.lean` (David Loeffler, Apache 2.0).
The separate convergence conclusion is then combined with the already proved
Mellin value for the physical angular ideal series.
-/

noncomputable section
open scoped BigOperators Classical Topology ENNReal
open Real Set MeasureTheory Filter Complex ENNReal

namespace OAI.SevenEighths.Angular.ThetaMellin

/-- An integrable limit of a countable series with summable integrals of norms.
Both the strong measurability and finite norm integral are proved explicitly. -/
theorem integrable_of_hasSum_of_summable_integral_norm
    {ι X : Type*} [Countable ι] [MeasurableSpace X] {μ : Measure X}
    {G : ι → X → ℂ} {g : X → ℂ}
    (hG : ∀ i, Integrable (G i) μ)
    (hNorm : Summable (fun i => ∫ x, ‖G i x‖ ∂μ))
    (hSum : ∀ᵐ x ∂μ, HasSum (fun i => G i x) (g x)) : Integrable g μ := by
  have hm : AEStronglyMeasurable g μ := by
    apply aestronglyMeasurable_of_tendsto_ae (SummationFilter.unconditional ι).filter
      (fun K => K.aestronglyMeasurable_fun_sum (fun i _ => (hG i).1))
    simpa only [HasSum] using hSum
  have he (i : ι) : ∫⁻ x, ‖G i x‖ₑ ∂μ = ‖∫ x, ‖G i x‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hG i).norm, coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (G i x)))]
    simp only [coe_nnnorm]
  have hfinite : (∑' i, ∫⁻ x, ‖G i x‖ₑ ∂μ) ≠ ∞ := by
    rw [funext he]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hNorm.abs
  refine ⟨hm, ?_⟩
  change (∫⁻ x, ‖g x‖ₑ ∂μ) < ∞
  calc
    (∫⁻ x, ‖g x‖ₑ ∂μ) ≤ ∫⁻ x, ∑' i, ‖G i x‖ₑ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hSum] with x hx
      rw [← hx.tsum_eq]
      exact enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ x, ‖G i x‖ₑ ∂μ := lintegral_tsum (fun i => (hG i).1.enorm)
    _ < ∞ := hfinite.lt_top

/-- Absolute Mellin convergence for a countable exponential series. -/
theorem mellinConvergent_exp_series {ι : Type*} [Countable ι]
    {a : ι → ℂ} {p : ι → ℝ} {F : ℝ → ℂ} {s : ℂ}
    (hp : ∀ i, a i = 0 ∨ 0 < p i) (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i => a i * rexp (-p i * t)) (F t))
    (hNorm : Summable (fun i => ‖a i‖ / (p i) ^ s.re)) :
    MellinConvergent F s := by
  change Integrable (fun t : ℝ => (t : ℂ) ^ (s - 1) * F t) (volume.restrict (Ioi 0))
  apply integrable_of_hasSum_of_summable_integral_norm
    (G := fun i (t : ℝ) => (t : ℂ) ^ (s - 1) * (a i * rexp (-p i * t)))
  · intro i
    rcases hp i with hai | hpi
    · simp [hai]
    simp_rw [← mul_assoc, mul_comm _ (a i), mul_assoc]
    have hGamma := Complex.GammaIntegral_convergent hs
    rw [← mul_zero (p i), ← integrableOn_Ioi_comp_mul_left_iff _ _ hpi] at hGamma
    refine (IntegrableOn.congr_fun (hGamma.const_mul (1 / p i ^ (s - 1)))
      (fun t (ht : 0 < t) => ?_) measurableSet_Ioi).const_mul _
    simp_rw [mul_comm (↑(rexp _) : ℂ), ← mul_assoc, neg_mul, Complex.ofReal_mul]
    rw [mul_cpow_ofReal_nonneg hpi.le ht.le, ← mul_assoc, one_div,
      inv_mul_cancel₀, one_mul]
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (ofReal_ne_zero.mpr hpi.ne')
  · apply Summable.of_norm
    convert! hNorm.mul_left (Real.Gamma s.re) using 2 with i
    simp_rw [← mul_assoc, mul_comm _ (a i), mul_assoc, norm_mul (a i), integral_const_mul]
    rw [← mul_div_assoc, mul_comm (Real.Gamma _), mul_div_assoc, norm_mul ‖a i‖, norm_norm]
    rcases hp i with hai | hpi
    · simp [hai]
    congr 1
    have hGamma := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hpi
    simp_rw [← neg_mul (p i), one_div, inv_rpow hpi.le, ← div_eq_inv_mul] at hGamma
    rw [norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), ← hGamma]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, Real.abs_exp,
      norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hF t ht).mul_left ((t : ℂ) ^ (s - 1))

theorem mellinConvergent_exp_pi_series {ι : Type*} [Countable ι]
    {a : ι → ℂ} {q : ι → ℝ} {F : ℝ → ℂ} {s : ℂ}
    (hq : ∀ i, a i = 0 ∨ 0 < q i) (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i => a i * rexp (-π * q i * t)) (F t))
    (hNorm : Summable (fun i => ‖a i‖ / (q i) ^ s.re)) :
    MellinConvergent F s := by
  have hp i : a i = 0 ∨ 0 < π * q i := by
    rcases hq i with h | h <;> simp [h, pi_pos]
  apply mellinConvergent_exp_series hp hs (by simpa using hF)
  have he (i : ι) : ‖a i‖ / (π * q i) ^ s.re = π ^ (-s.re) * ‖a i‖ / q i ^ s.re := by
    rcases hq i with h | h
    · simp [h]
    · rw [mul_rpow pi_pos.le h.le, ← div_div, rpow_neg pi_pos.le, ← div_eq_inv_mul]
  simpa only [he, mul_div_assoc] using hNorm.mul_left _

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open OAI.SevenEighths.Angular.Polynomial

/-- Explicit convergence of the shifted Mellin integral of the physical
centered theta. The Dirichlet half-plane is Re(s)>1. -/
theorem centeredTheta_mellinConvergent (χ : AngularCharacter) (A : ℝ) (hA : 0 < A)
    (s : ℂ) (hs : 1 < s.re) :
    MellinConvergent (centeredTheta χ A) (s + (χ.k.natAbs : ℂ) / 2) := by
  let : Countable O := latticeCoordEquiv.countable_iff.mpr inferInstance
  have hS : 0 < (s + (χ.k.natAbs : ℂ) / 2).re := by
    have hs0 : 0 < s.re := lt_trans zero_lt_one hs
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    positivity
  have hp (a : O) : centeredWeightedCoeff χ a = 0 ∨ 0 < A * ‖eisEmbedding a‖ ^ 2 := by
    by_cases ha : a = 0
    · left; simp [centeredWeightedCoeff, ha]
    · right; exact mul_pos hA (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero ha)))
  have ht (t : ℝ) (ht : t ∈ Ioi 0) :
      HasSum (fun a : O => centeredWeightedCoeff χ a *
        (Real.exp (-Real.pi * (A * ‖eisEmbedding a‖ ^ 2) * t) : ℂ))
        (centeredTheta χ A t) := by
    simpa only [gaussian_eq_real_exp] using centeredTheta_hasSum χ A t hA ht
  exact mellinConvergent_exp_pi_series hp hS ht (shifted_norm_summable χ A hA s hs)

theorem centeredTheta_hasMellin (χ : AngularCharacter) (A : ℝ) (hA : 0 < A)
    (s : ℂ) (hs : 1 < s.re) :
    HasMellin (centeredTheta χ A) (s + (χ.k.natAbs : ℂ) / 2)
      (6 * Complex.Gamma (s + (χ.k.natAbs : ℂ) / 2) *
        ((Real.pi * A : ℝ) : ℂ) ^ (-(s + (χ.k.natAbs : ℂ) / 2)) * χ.series s) :=
  ⟨centeredTheta_mellinConvergent χ A hA s hs, centeredTheta_mellin χ A hA s hs⟩

end OAI.SevenEighths.Angular.ThetaMellin
