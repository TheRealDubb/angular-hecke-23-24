import AngularBesselHigherKernel
import AngularBesselClosure

/-! The actual shifted-derivative Bessel series. Fixed-order bounds on positive
height slabs justify summation. This module does not assert an endpoint theorem. -/

noncomputable section
open Filter Set
open scoped Classical Topology ContDiff

namespace OAI.CubicEisenstein.AngularBesselKernelSeries

open AngularBesselClosure AngularBesselHigherKernel

def kernel (n : ℕ) : ℝ → ℂ := iteratedDeriv n (schlafliBesselK (1 / 3 : ℂ))

def radial (coeff : SubexponentialBesselCoefficients) : SubexponentialBesselCoefficients :=
  weightFrequency coeff (fun h => (‖cuspFrequency h‖ : ℂ))
    (fun h => by rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)])

def term (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (h : Eis) (p : ℝ × ℂ) : ℂ :=
  if h = 0 then 0 else coeff.value h * kernel n (4 * Real.pi * ‖cuspFrequency h‖ * p.1) *
    ShortDraftTrace.breveE (cuspFrequency h * p.2)

def series (coeff : SubexponentialBesselCoefficients) (n : ℕ) (p : ℝ × ℂ) : ℂ :=
  ∑' h : Eis, term coeff n h p

theorem kernel_hasDerivAt (n : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (kernel n) (kernel (n + 1) x) x :=
  schlafliBesselK_cubic_iteratedDeriv_hasDerivAt n x hx

theorem weighted_kernel_bound (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (a : ℝ) (ha : 0 < a) : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Eis, h ≠ 0 → ∀ v : ℝ, a ≤ v →
      ‖coeff.value h‖ * ‖kernel n (4 * Real.pi * ‖cuspFrequency h‖ * v)‖ ≤
        C * Real.exp (-(Real.pi * a / 2) * ‖cuspFrequency h‖) := by
  have hd : 0 < ‖(3 : ℂ) * ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let δ : ℝ := 4 * Real.pi * a * ‖(3 : ℂ) * ConcreteTraceCRT.eisLam‖⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hK := kernelBound_nonneg n 0 0 δ hδ
  obtain ⟨C, hC, hcoeff⟩ := coeff.growth (Real.pi * a / 2) (by positivity)
  refine ⟨C * kernelBound n 0 0 δ, mul_nonneg hC hK, ?_⟩
  intro h hh v hv
  have hr : 0 < ‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : δ ≤ 4 * Real.pi * ‖cuspFrequency h‖ * v := by
    have hm := mul_le_mul (cuspFrequency_norm_lower h hh) hv ha.le (norm_nonneg _)
    dsimp [δ]
    nlinarith [mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 4 * Real.pi)]
  have hb := schlafliBesselK_cubic_iteratedDeriv_bound n δ _ hδ hx
  calc
    _ ≤ (C * Real.exp ((Real.pi * a / 2) * ‖cuspFrequency h‖)) *
        (kernelBound n 0 0 δ * Real.exp (-(4 * Real.pi * ‖cuspFrequency h‖ * v) / 4)) :=
      mul_le_mul (hcoeff h hh) hb (norm_nonneg _) (by positivity)
    _ = (C * kernelBound n 0 0 δ) * Real.exp
        ((Real.pi * a / 2) * ‖cuspFrequency h‖ - (4 * Real.pi * ‖cuspFrequency h‖ * v) / 4) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hK)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hv (mul_pos Real.pi_pos hr).le]

theorem term_norm_bound (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (a : ℝ) (ha : 0 < a) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Eis) (p : ℝ × ℂ), a ≤ p.1 →
      ‖term coeff n h p‖ ≤ C * Real.exp (-(Real.pi * a / 2) * ‖cuspFrequency h‖) := by
  obtain ⟨C, hC, hb⟩ := weighted_kernel_bound coeff n a ha
  refine ⟨C, hC, ?_⟩
  intro h p hp
  by_cases hh : h = 0
  · simp only [term, hh, ite_true, norm_zero]
    positivity
  · simp only [term, hh, ite_false, norm_mul, breveE_norm, mul_one]
    exact hb h hh p.1 hp

theorem term_summable (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (p : ℝ × ℂ) (hp : 0 < p.1) : Summable (fun h : Eis => term coeff n h p) := by
  obtain ⟨C, _, hb⟩ := term_norm_bound coeff n p.1 hp
  exact Summable.of_norm_bounded
    ((summable_exp_neg_cuspFrequency_norm (Real.pi * p.1 / 2) (by positivity)).mul_left C)
    (fun h => hb h p le_rfl)

theorem term_continuousAt (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (h : Eis) (p : ℝ × ℂ) (hp : 0 < p.1) : ContinuousAt (term coeff n h) p := by
  change ContinuousAt (fun q : ℝ × ℂ => if h = 0 then 0 else
    coeff.value h * kernel n (4 * Real.pi * ‖cuspFrequency h‖ * q.1) *
      ShortDraftTrace.breveE (cuspFrequency h * q.2)) p
  by_cases hh : h = 0
  · simp only [hh, ite_true]
    exact continuousAt_const
  have hx : 0 < 4 * Real.pi * ‖cuspFrequency h‖ * p.1 :=
    mul_pos (mul_pos (by positivity) (norm_pos_iff.mpr (cuspFrequency_ne_zero h hh))) hp
  have hK := (kernel_hasDerivAt n _ hx).continuousAt.comp
    (f := fun q : ℝ × ℂ => 4 * Real.pi * ‖cuspFrequency h‖ * q.1)
    (continuousAt_const.mul continuousAt_fst)
  have hE : ContinuousAt (fun q : ℝ × ℂ => ShortDraftTrace.breveE (cuspFrequency h * q.2)) p :=
    (brevePhase_hasFDerivAt (cuspFrequency h) p.2).continuousAt.comp
      (f := fun q : ℝ × ℂ => q.2) continuousAt_snd
  simp only [hh, ite_false]
  exact (continuousAt_const.mul hK).mul hE

theorem series_continuousAt (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (p : ℝ × ℂ) (hp : 0 < p.1) : ContinuousAt (series coeff n) p := by
  obtain ⟨C, _, hb⟩ := term_norm_bound coeff n (p.1 / 2) (by positivity)
  have hc : ContinuousOn (series coeff n) {q : ℝ × ℂ | p.1 / 2 ≤ q.1} := by
    apply continuousOn_tsum
      (u := fun h : Eis => C * Real.exp (-(Real.pi * (p.1 / 2) / 2) * ‖cuspFrequency h‖))
    · intro h q hq
      exact (term_continuousAt coeff n h q (by change p.1 / 2 ≤ q.1 at hq; linarith)).continuousWithinAt
    · exact (summable_exp_neg_cuspFrequency_norm _ (by positivity)).mul_left C
    · exact hb
  exact (hc p (by change p.1 / 2 ≤ p.1; linarith)).continuousAt
    (continuousAt_fst.tendsto.eventually (Ici_mem_nhds (by linarith : p.1 / 2 < p.1)))

theorem term_frequency (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (h : Eis) (p : ℝ × ℂ) :
    term (frequency coeff) n h p = cuspFrequency h * term coeff n h p := by
  simp only [term, frequency_value]
  split_ifs <;> ring

theorem term_conjugateFrequency (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (h : Eis) (p : ℝ × ℂ) :
    term (conjugateFrequency coeff) n h p = star (cuspFrequency h) * term coeff n h p := by
  simp only [term, conjugateFrequency_value]
  split_ifs <;> ring

theorem term_radial (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (h : Eis) (p : ℝ × ℂ) :
    term (radial coeff) n h p = (‖cuspFrequency h‖ : ℂ) * term coeff n h p := by
  simp only [term, radial, weightFrequency]
  split_ifs <;> ring

theorem actual_series_eq (coeff : SubexponentialBesselCoefficients)
    (p : ℝ × ℂ) (hp : 0 < p.1) : coeff.series p = (p.1 : ℂ) * series coeff 0 p := by
  rw [SubexponentialBesselCoefficients.series, series, ← tsum_mul_left]
  apply tsum_congr
  intro h
  by_cases hh : h = 0
  · simp [term, SubexponentialBesselCoefficients.term, hh]
  · rw [coeff.term_bessel h hh p.1 hp p.2]
    simp only [term, hh, ite_false, kernel, iteratedDeriv_zero]
    ring

end OAI.CubicEisenstein.AngularBesselKernelSeries
