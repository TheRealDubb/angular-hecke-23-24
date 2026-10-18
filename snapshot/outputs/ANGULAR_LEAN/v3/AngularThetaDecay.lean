import AngularThetaMellin

/-! Actual positive-height continuity and rapid decay of the centered angular
theta series. The majorant is its summable norm series at a fixed positive
height, so all bounds retain the actual physical coefficients. -/

noncomputable section
open scoped BigOperators Classical Topology
open Filter Asymptotics MeasureTheory

namespace OAI.SevenEighths.Angular.ThetaMellin

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open OAI.SevenEighths.Angular.Polynomial

def centeredTerm (χ : AngularCharacter) (A t : ℝ) (a : O) : ℂ :=
  centeredWeightedCoeff χ a * GaussianTheta.gaussian (A * t) (eisEmbedding a)

theorem centeredTerm_hasSum (χ : AngularCharacter) (A t : ℝ) (hA : 0 < A) (ht : 0 < t) :
    HasSum (centeredTerm χ A t) (centeredTheta χ A t) := centeredTheta_hasSum χ A t hA ht

theorem norm_centeredTerm (χ : AngularCharacter) (A t : ℝ) (a : O) :
    ‖centeredTerm χ A t a‖ = ‖centeredWeightedCoeff χ a‖ *
      Real.exp (-Real.pi * (A * ‖eisEmbedding a‖ ^ 2) * t) := by
  rw [centeredTerm, norm_mul, gaussian_eq_real_exp, Complex.norm_real,
    Real.norm_eq_abs, Real.abs_exp]

theorem centeredTerm_norm_antitone (χ : AngularCharacter) (A : ℝ) (hA : 0 < A)
    (a : O) {b t : ℝ} (hbt : b ≤ t) :
    ‖centeredTerm χ A t a‖ ≤ ‖centeredTerm χ A b a‖ := by
  rw [norm_centeredTerm, norm_centeredTerm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hp : 0 ≤ Real.pi * (A * ‖eisEmbedding a‖ ^ 2) := by positivity
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hbt)]

theorem centeredTheta_continuousOn_Ici (χ : AngularCharacter) (A b : ℝ)
    (hA : 0 < A) (hb : 0 < b) : ContinuousOn (centeredTheta χ A) (Set.Ici b) := by
  have hcont (a : O) : Continuous (fun t : ℝ => centeredTerm χ A t a) := by
    simp only [centeredTerm, gaussian_eq_real_exp]
    fun_prop
  have hsum := (centeredTerm_hasSum χ A b hA hb).summable.norm
  have hc := continuousOn_tsum (s := Set.Ici b) (fun a => (hcont a).continuousOn)
    hsum (fun a t ht => centeredTerm_norm_antitone χ A hA a ht)
  apply hc.congr
  intro t ht
  exact (centeredTerm_hasSum χ A t hA (lt_of_lt_of_le hb ht)).tsum_eq.symm

theorem centeredTheta_continuousOn (χ : AngularCharacter) (A : ℝ) (hA : 0 < A) :
    ContinuousOn (centeredTheta χ A) (Set.Ioi 0) := by
  intro t ht
  have ht0 : 0 < t := ht
  have hb : 0 < t / 2 := by positivity
  have hbt : t / 2 < t := by linarith
  have hc := centeredTheta_continuousOn_Ici χ A (t / 2) hA hb
  exact ((hc t hbt.le).continuousAt (Ici_mem_nhds hbt)).continuousWithinAt

theorem centeredTheta_locallyIntegrableOn (χ : AngularCharacter) (A : ℝ) (hA : 0 < A) :
    LocallyIntegrableOn (centeredTheta χ A) (Set.Ioi 0) :=
  (centeredTheta_continuousOn χ A hA).locallyIntegrableOn measurableSet_Ioi

theorem embedding_norm_sq_ge_one (a : O) (ha : a ≠ 0) :
    1 ≤ ‖eisEmbedding a‖ ^ 2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  have hI : Ideal.span ({a} : Set O) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr ha
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem centeredTerm_exp_bound (χ : AngularCharacter) (A : ℝ) (hA : 0 < A)
    (t : ℝ) (ht : 1 ≤ t) (a : O) :
    ‖centeredTerm χ A t a‖ ≤ Real.exp (-(Real.pi * A / 2) * t) *
      ‖centeredTerm χ A (1 / 2) a‖ := by
  by_cases ha : a = 0
  · simp [centeredTerm, centeredWeightedCoeff, ha]
  have hq := embedding_norm_sq_ge_one a ha
  have hqt : t / 2 + ‖eisEmbedding a‖ ^ 2 / 2 ≤ ‖eisEmbedding a‖ ^ 2 * t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hq)]
  have he : -Real.pi * (A * ‖eisEmbedding a‖ ^ 2) * t ≤
      -(Real.pi * A / 2) * t + -Real.pi * (A * ‖eisEmbedding a‖ ^ 2) * (1 / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hqt (mul_pos Real.pi_pos hA).le]
  rw [norm_centeredTerm, norm_centeredTerm]
  calc
    _ ≤ ‖centeredWeightedCoeff χ a‖ * Real.exp
        (-(Real.pi * A / 2) * t + -Real.pi * (A * ‖eisEmbedding a‖ ^ 2) * (1 / 2)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (norm_nonneg _)
    _ = _ := by rw [Real.exp_add]; ring

def decayConstant (χ : AngularCharacter) (A : ℝ) : ℝ :=
  ∑' a : O, ‖centeredTerm χ A (1 / 2) a‖

theorem centeredTheta_exp_bound (χ : AngularCharacter) (A : ℝ) (hA : 0 < A)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖centeredTheta χ A t‖ ≤ decayConstant χ A * Real.exp (-(Real.pi * A / 2) * t) := by
  have hhalf := (centeredTerm_hasSum χ A (1 / 2) hA (by norm_num)).summable.norm
  have hsum := (centeredTerm_hasSum χ A t hA (by linarith)).summable.norm
  rw [← (centeredTerm_hasSum χ A t hA (by linarith)).tsum_eq]
  calc
    _ ≤ ∑' a : O, ‖centeredTerm χ A t a‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' a : O, Real.exp (-(Real.pi * A / 2) * t) * ‖centeredTerm χ A (1 / 2) a‖ :=
      hsum.tsum_le_tsum (centeredTerm_exp_bound χ A hA t ht) (hhalf.mul_left _)
    _ = _ := by rw [tsum_mul_left]; exact mul_comm _ _

theorem centeredTheta_isBigO_exp (χ : AngularCharacter) (A : ℝ) (hA : 0 < A) :
    centeredTheta χ A =O[atTop] (fun t : ℝ => Real.exp (-(Real.pi * A / 2) * t)) := by
  apply IsBigO.of_bound (decayConstant χ A)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  simpa only [Real.norm_eq_abs, Real.abs_exp] using centeredTheta_exp_bound χ A hA t ht

theorem centeredTheta_rapidDecay (χ : AngularCharacter) (A : ℝ) (hA : 0 < A) (r : ℝ) :
    centeredTheta χ A =O[atTop] (fun t : ℝ => t ^ r) :=
  (centeredTheta_isBigO_exp χ A hA).trans
    (isLittleO_exp_neg_mul_rpow_atTop (by positivity : 0 < Real.pi * A / 2) r).isBigO

end OAI.SevenEighths.Angular.ThetaMellin
