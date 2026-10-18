import OAI.NumberTheory.DirichletL.Eisenstein.ReflectedCuspMellin

/-!
# Frequency-weighted actual Bessel coefficient arrays

The OAI-003 subexponential coefficient class is stable under multiplication by
the actual cusp frequency, its conjugate, and any fixed natural power of either.
Consequently its actual Bessel-series summability applies at every fixed order.
This module does not assert a higher cusp-composition rule or a zero-free bound.
-/

namespace OAI.CubicEisenstein.AngularBesselClosure

noncomputable section
open scoped Classical

abbrev Eis := ActualEisensteinCubic.O

/-- Weighting by any array with exactly the cusp-frequency norm preserves the
actual coefficient growth condition, with a constant depending on epsilon. -/
def weightFrequency (coeff : SubexponentialBesselCoefficients) (w : Eis → ℂ)
    (hw : ∀ h, ‖w h‖ = ‖cuspFrequency h‖) : SubexponentialBesselCoefficients where
  value h := w h * coeff.value h
  growth ε hε := by
    obtain ⟨C, hC, hcoeff⟩ := coeff.growth (ε / 2) (by positivity)
    refine ⟨C * (2 / ε), by positivity, ?_⟩
    intro h hh
    have hfreq : ‖cuspFrequency h‖ ≤
        (2 / ε) * Real.exp ((ε / 2) * ‖cuspFrequency h‖) := by
      have hexp := Real.add_one_le_exp ((ε / 2) * ‖cuspFrequency h‖)
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hε).mpr
      nlinarith
    calc
      ‖w h * coeff.value h‖ = ‖cuspFrequency h‖ * ‖coeff.value h‖ := by
        rw [norm_mul, hw]
      _ ≤ ((2 / ε) * Real.exp ((ε / 2) * ‖cuspFrequency h‖)) *
          (C * Real.exp ((ε / 2) * ‖cuspFrequency h‖)) :=
        mul_le_mul hfreq (hcoeff h hh) (norm_nonneg _) (by positivity)
      _ = (C * (2 / ε)) * Real.exp (ε * ‖cuspFrequency h‖) := by
        rw [show ε * ‖cuspFrequency h‖ =
          (ε / 2) * ‖cuspFrequency h‖ + (ε / 2) * ‖cuspFrequency h‖ by ring,
          Real.exp_add]
        ring

def frequency (coeff : SubexponentialBesselCoefficients) :
    SubexponentialBesselCoefficients :=
  weightFrequency coeff cuspFrequency (fun _ => rfl)

def conjugateFrequency (coeff : SubexponentialBesselCoefficients) :
    SubexponentialBesselCoefficients :=
  weightFrequency coeff (fun h => star (cuspFrequency h)) (fun _ => norm_star _)

@[simp] theorem frequency_value (coeff : SubexponentialBesselCoefficients) (h : Eis) :
    (frequency coeff).value h = cuspFrequency h * coeff.value h := rfl

@[simp] theorem conjugateFrequency_value (coeff : SubexponentialBesselCoefficients)
    (h : Eis) :
    (conjugateFrequency coeff).value h = star (cuspFrequency h) * coeff.value h := rfl

def frequencyPow (coeff : SubexponentialBesselCoefficients) :
    ℕ → SubexponentialBesselCoefficients
  | 0 => coeff
  | j + 1 => frequency (frequencyPow coeff j)

def conjugateFrequencyPow (coeff : SubexponentialBesselCoefficients) :
    ℕ → SubexponentialBesselCoefficients
  | 0 => coeff
  | j + 1 => conjugateFrequency (conjugateFrequencyPow coeff j)

@[simp] theorem frequencyPow_value (coeff : SubexponentialBesselCoefficients)
    (j : ℕ) (h : Eis) :
    (frequencyPow coeff j).value h = cuspFrequency h ^ j * coeff.value h := by
  induction j with
  | zero => simp [frequencyPow]
  | succ j ih =>
      simp only [frequencyPow, frequency_value, ih, pow_succ]
      ring

@[simp] theorem conjugateFrequencyPow_value (coeff : SubexponentialBesselCoefficients)
    (j : ℕ) (h : Eis) :
    (conjugateFrequencyPow coeff j).value h =
      star (cuspFrequency h) ^ j * coeff.value h := by
  induction j with
  | zero => simp [conjugateFrequencyPow]
  | succ j ih =>
      simp only [conjugateFrequencyPow, conjugateFrequency_value, ih, pow_succ]
      ring

theorem frequencyPow_term (coeff : SubexponentialBesselCoefficients)
    (j : ℕ) (h : Eis) (p : ℝ × ℂ) :
    (frequencyPow coeff j).term h p = cuspFrequency h ^ j * coeff.term h p := by
  simp only [SubexponentialBesselCoefficients.term, frequencyPow_value]
  split_ifs <;> ring

theorem conjugateFrequencyPow_term (coeff : SubexponentialBesselCoefficients)
    (j : ℕ) (h : Eis) (p : ℝ × ℂ) :
    (conjugateFrequencyPow coeff j).term h p =
      star (cuspFrequency h) ^ j * coeff.term h p := by
  simp only [SubexponentialBesselCoefficients.term, conjugateFrequencyPow_value]
  split_ifs <;> ring

/-- The actual polynomially weighted Bessel series is summable at each
positive height. The derivative order is fixed before its constants. -/
theorem summable_frequencyPow_terms (coeff : SubexponentialBesselCoefficients)
    (j : ℕ) (p : ℝ × ℂ) (hp : 0 < p.1) :
    Summable (fun h : Eis => cuspFrequency h ^ j * coeff.term h p) := by
  simpa only [frequencyPow_term] using (frequencyPow coeff j).summable p hp

theorem summable_conjugateFrequencyPow_terms (coeff : SubexponentialBesselCoefficients)
    (j : ℕ) (p : ℝ × ℂ) (hp : 0 < p.1) :
    Summable (fun h : Eis => star (cuspFrequency h) ^ j * coeff.term h p) := by
  simpa only [conjugateFrequencyPow_term] using
    (conjugateFrequencyPow coeff j).summable p hp

end
end OAI.CubicEisenstein.AngularBesselClosure
