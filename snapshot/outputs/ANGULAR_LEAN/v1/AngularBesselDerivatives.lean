import AngularBesselClosure

/-!
# Actual higher horizontal derivatives of the Bessel series

At each positive height, every fixed pure horizontal Wirtinger derivative of
the actual OAI-003 Bessel series is the corresponding frequency-power weighted
series. The inherited horizontal HasDerivAt theorem also applies at every
iteration, so these are actual derivatives, not conclusions obtained from a
default value of `deriv` at a nondifferentiable function.

No higher cusp-composition rule, translated joint regularity theorem, angular
functional equation or zero-free bound is asserted in this module.
-/

namespace OAI.CubicEisenstein.AngularBesselDerivatives

noncomputable section
open scoped BigOperators Classical
open AngularBesselClosure

def derivativeScalar : ℂ := 2 * Real.pi * Complex.I

theorem horizontalWirtingerBar_const_mul (a : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    horizontalWirtingerBar (fun w => a * f w) z = a * horizontalWirtingerBar f z := by
  unfold horizontalWirtingerBar
  simp only [deriv_const_mul_field]
  ring

theorem horizontalWirtingerZ_const_mul (a : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    horizontalWirtingerZ (fun w => a * f w) z = a * horizontalWirtingerZ f z := by
  unfold horizontalWirtingerZ
  simp only [deriv_const_mul_field]
  ring

theorem frequency_term (coeff : SubexponentialBesselCoefficients)
    (h : Eis) (p : ℝ × ℂ) :
    (frequency coeff).term h p = cuspFrequency h * coeff.term h p := by
  simpa only [frequencyPow, pow_one] using frequencyPow_term coeff 1 h p

theorem conjugateFrequency_term (coeff : SubexponentialBesselCoefficients)
    (h : Eis) (p : ℝ × ℂ) :
    (conjugateFrequency coeff).term h p = star (cuspFrequency h) * coeff.term h p := by
  simpa only [conjugateFrequencyPow, pow_one] using
    conjugateFrequencyPow_term coeff 1 h p

theorem series_wirtingerBar (coeff : SubexponentialBesselCoefficients)
    (v : ℝ) (hv : 0 < v) (z : ℂ) :
    horizontalWirtingerBar (fun w => coeff.series (v, w)) z =
      derivativeScalar * (conjugateFrequency coeff).series (v, z) := by
  have hsource := coeff.fullFunction_wirtingerBar 0 v hv z
  simp only [SubexponentialBesselCoefficients.fullFunction, zero_mul, zero_add,
    SubexponentialBesselCoefficients.function, hyperbolicHeight_upperPoint,
    hyperbolicHorizontal_upperPoint] at hsource
  rw [hsource, SubexponentialBesselCoefficients.series, ← tsum_mul_left]
  apply tsum_congr
  intro h
  rw [conjugateFrequency_term]
  unfold derivativeScalar
  ring

theorem series_wirtingerZ (coeff : SubexponentialBesselCoefficients)
    (v : ℝ) (hv : 0 < v) (z : ℂ) :
    horizontalWirtingerZ (fun w => coeff.series (v, w)) z =
      derivativeScalar * (frequency coeff).series (v, z) := by
  have hsource := coeff.fullFunction_wirtingerZ 0 v hv z
  simp only [SubexponentialBesselCoefficients.fullFunction, zero_mul, zero_add,
    SubexponentialBesselCoefficients.function, hyperbolicHeight_upperPoint,
    hyperbolicHorizontal_upperPoint] at hsource
  rw [hsource, SubexponentialBesselCoefficients.series, ← tsum_mul_left]
  apply tsum_congr
  intro h
  rw [frequency_term]
  unfold derivativeScalar
  ring

def iteratedBar : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0, f => f
  | j + 1, f => horizontalWirtingerBar (iteratedBar j f)

def iteratedZ : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0, f => f
  | j + 1, f => horizontalWirtingerZ (iteratedZ j f)

theorem iteratedBar_series (coeff : SubexponentialBesselCoefficients)
    (j : ℕ) (v : ℝ) (hv : 0 < v) :
    iteratedBar j (fun z => coeff.series (v, z)) =
      fun z => derivativeScalar ^ j * (conjugateFrequencyPow coeff j).series (v, z) := by
  induction j with
  | zero => simp [iteratedBar, conjugateFrequencyPow]
  | succ j ih =>
      funext z
      simp only [iteratedBar, ih, horizontalWirtingerBar_const_mul,
        series_wirtingerBar _ v hv, conjugateFrequencyPow, pow_succ]
      ring

theorem iteratedZ_series (coeff : SubexponentialBesselCoefficients)
    (j : ℕ) (v : ℝ) (hv : 0 < v) :
    iteratedZ j (fun z => coeff.series (v, z)) =
      fun z => derivativeScalar ^ j * (frequencyPow coeff j).series (v, z) := by
  induction j with
  | zero => simp [iteratedZ, frequencyPow]
  | succ j ih =>
      funext z
      simp only [iteratedZ, ih, horizontalWirtingerZ_const_mul,
        series_wirtingerZ _ v hv, frequencyPow, pow_succ]
      ring

theorem iteratedBar_series_eq_tsum (coeff : SubexponentialBesselCoefficients)
    (j : ℕ) (v : ℝ) (hv : 0 < v) (z : ℂ) :
    iteratedBar j (fun w => coeff.series (v, w)) z =
      ∑' h : Eis, (derivativeScalar * star (cuspFrequency h)) ^ j * coeff.term h (v, z) := by
  rw [iteratedBar_series coeff j v hv]
  change derivativeScalar ^ j *
    (∑' h : Eis, (conjugateFrequencyPow coeff j).term h (v, z)) = _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  rw [conjugateFrequencyPow_term, mul_pow]
  ring

theorem iteratedZ_series_eq_tsum (coeff : SubexponentialBesselCoefficients)
    (j : ℕ) (v : ℝ) (hv : 0 < v) (z : ℂ) :
    iteratedZ j (fun w => coeff.series (v, w)) z =
      ∑' h : Eis, (derivativeScalar * cuspFrequency h) ^ j * coeff.term h (v, z) := by
  rw [iteratedZ_series coeff j v hv]
  change derivativeScalar ^ j *
    (∑' h : Eis, (frequencyPow coeff j).term h (v, z)) = _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  rw [frequencyPow_term, mul_pow]
  ring

/-- Every intermediate pure derivative has the inherited actual horizontal
derivative at every real line parameter. -/
theorem iteratedBar_series_horizontal_hasDerivAt
    (coeff : SubexponentialBesselCoefficients) (j : ℕ)
    (v : ℝ) (hv : 0 < v) (z direction : ℂ) (t : ℝ) :
    HasDerivAt
      (fun x : ℝ => iteratedBar j (fun w => coeff.series (v, w))
        (z + (x : ℂ) * direction))
      (derivativeScalar ^ j * ∑' h : Eis,
        (conjugateFrequencyPow coeff j).directionalTerm h v
          (z + (t : ℂ) * direction) direction) t := by
  rw [iteratedBar_series coeff j v hv]
  exact ((conjugateFrequencyPow coeff j).series_horizontal_hasDerivAt
    v hv z direction t).const_mul (derivativeScalar ^ j)

theorem iteratedZ_series_horizontal_hasDerivAt
    (coeff : SubexponentialBesselCoefficients) (j : ℕ)
    (v : ℝ) (hv : 0 < v) (z direction : ℂ) (t : ℝ) :
    HasDerivAt
      (fun x : ℝ => iteratedZ j (fun w => coeff.series (v, w))
        (z + (x : ℂ) * direction))
      (derivativeScalar ^ j * ∑' h : Eis,
        (frequencyPow coeff j).directionalTerm h v
          (z + (t : ℂ) * direction) direction) t := by
  rw [iteratedZ_series coeff j v hv]
  exact ((frequencyPow coeff j).series_horizontal_hasDerivAt
    v hv z direction t).const_mul (derivativeScalar ^ j)

end
end OAI.CubicEisenstein.AngularBesselDerivatives
