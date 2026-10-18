import AngularBesselHorizontalRegularity
import OAI.NumberTheory.DirichletL.Eisenstein.CubeResidueStrata

/-! Actual higher horizontal cusp profiles. At every positive derivative
order, the retained cusp constant differentiates to zero, the profile is the
frequency-power weighted Bessel series, and positive-height continuity and
exponential decay follow for every fixed order. No uniformity in the order
or higher cusp reflection is asserted here. -/

noncomputable section
open Filter Asymptotics Set
open scoped Classical Topology

namespace OAI.CubicEisenstein.AngularHigherProfiles

open AngularBesselClosure AngularBesselDerivatives AngularBesselHorizontalRegularity

def barProfile (f : HyperbolicSpace → ℂ) (j : ℕ) (z : ℂ) (v : ℝ) : ℂ :=
  iteratedBar j (fun w => f (cuspCoordinateLift (v, w))) z

def zProfile (f : HyperbolicSpace → ℂ) (j : ℕ) (z : ℂ) (v : ℝ) : ℂ :=
  iteratedZ j (fun w => f (cuspCoordinateLift (v, w))) z

theorem barProfile_positive (f : HyperbolicSpace → ℂ) (j : ℕ) (z : ℂ)
    (v : ℝ) (hv : 0 < v) :
    barProfile f j z v = iteratedBar j (fun w => f (upperPoint w v hv)) z := by
  simp only [barProfile, cuspCoordinateLift_positive v _ hv]

theorem zProfile_positive (f : HyperbolicSpace → ℂ) (j : ℕ) (z : ℂ)
    (v : ℝ) (hv : 0 < v) :
    zProfile f j z v = iteratedZ j (fun w => f (upperPoint w v hv)) z := by
  simp only [zProfile, cuspCoordinateLift_positive v _ hv]

theorem iteratedBar_splitFull (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (j : ℕ) (v : ℝ) (hv : 0 < v) :
    iteratedBar (j + 1) (fun z => splitFull coeff constant (z, v)) =
      fun z => derivativeScalar ^ (j + 1) *
        (conjugateFrequencyPow coeff (j + 1)).series (v, z) := by
  induction j with
  | zero =>
      funext z
      simpa only [Nat.zero_add, iteratedBar, pow_one, conjugateFrequencyPow] using
        splitFull_wirtingerBar coeff constant z v hv
  | succ j ih =>
      funext z
      change horizontalWirtingerBar (iteratedBar (j + 1)
        (fun z => splitFull coeff constant (z, v))) z = _
      rw [ih, horizontalWirtingerBar_const_mul, series_wirtingerBar _ v hv]
      simp only [
        conjugateFrequencyPow, pow_succ]
      ring

theorem iteratedZ_splitFull (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (j : ℕ) (v : ℝ) (hv : 0 < v) :
    iteratedZ (j + 1) (fun z => splitFull coeff constant (z, v)) =
      fun z => derivativeScalar ^ (j + 1) *
        (frequencyPow coeff (j + 1)).series (v, z) := by
  induction j with
  | zero =>
      funext z
      simpa only [Nat.zero_add, iteratedZ, pow_one, frequencyPow] using
        splitFull_wirtingerZ coeff constant z v hv
  | succ j ih =>
      funext z
      change horizontalWirtingerZ (iteratedZ (j + 1)
        (fun z => splitFull coeff constant (z, v))) z = _
      rw [ih, horizontalWirtingerZ_const_mul, series_wirtingerZ _ v hv]
      simp only [frequencyPow, pow_succ]
      ring

theorem barProfile_full_eq (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (j : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    barProfile (coeff.fullFunction constant) (j + 1) z v =
      derivativeScalar ^ (j + 1) * (conjugateFrequencyPow coeff (j + 1)).series (v, z) :=
  congrFun (iteratedBar_splitFull coeff constant j v hv) z

theorem zProfile_full_eq (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (j : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    zProfile (coeff.fullFunction constant) (j + 1) z v =
      derivativeScalar ^ (j + 1) * (frequencyPow coeff (j + 1)).series (v, z) :=
  congrFun (iteratedZ_splitFull coeff constant j v hv) z

theorem barProfile_full_continuousOn (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (j : ℕ) (z : ℂ) :
    ContinuousOn (barProfile (coeff.fullFunction constant) (j + 1) z) (Ioi 0) := by
  have hh : ContinuousOn (fun v : ℝ => derivativeScalar ^ (j + 1) *
      (conjugateFrequencyPow coeff (j + 1)).series (v, z)) (Ioi 0) := by
    intro v hv
    have hs := ((conjugateFrequencyPow coeff (j + 1)).series_contDiffAt_one (v, z) hv).continuousAt
    exact (continuousAt_const.mul (hs.comp (f := fun t : ℝ => (t, z))
      (continuousAt_id.prodMk continuousAt_const))).continuousWithinAt
  exact hh.congr (fun v hv => barProfile_full_eq coeff constant j z v hv)

theorem zProfile_full_continuousOn (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (j : ℕ) (z : ℂ) :
    ContinuousOn (zProfile (coeff.fullFunction constant) (j + 1) z) (Ioi 0) := by
  have hh : ContinuousOn (fun v : ℝ => derivativeScalar ^ (j + 1) *
      (frequencyPow coeff (j + 1)).series (v, z)) (Ioi 0) := by
    intro v hv
    have hs := ((frequencyPow coeff (j + 1)).series_contDiffAt_one (v, z) hv).continuousAt
    exact (continuousAt_const.mul (hs.comp (f := fun t : ℝ => (t, z))
      (continuousAt_id.prodMk continuousAt_const))).continuousWithinAt
  exact hh.congr (fun v hv => zProfile_full_eq coeff constant j z v hv)

theorem barProfile_full_isBigO (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (j : ℕ) (z : ℂ) :
    barProfile (coeff.fullFunction constant) (j + 1) z =O[atTop]
      (fun v : ℝ => Real.exp (-residualCuspDecayRate * v)) := by
  obtain ⟨C, _, hb⟩ := (conjugateFrequencyPow coeff (j + 1)).series_cusp_decay 1 (by norm_num)
  apply IsBigO.of_bound (‖derivativeScalar ^ (j + 1)‖ * C)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
  rw [barProfile_full_eq coeff constant j z v (lt_of_lt_of_le (by norm_num) hv),
    norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (mul_le_mul_of_nonneg_left (hb v z hv) (norm_nonneg _)).trans_eq (by ring)

theorem zProfile_full_isBigO (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (j : ℕ) (z : ℂ) :
    zProfile (coeff.fullFunction constant) (j + 1) z =O[atTop]
      (fun v : ℝ => Real.exp (-residualCuspDecayRate * v)) := by
  obtain ⟨C, _, hb⟩ := (frequencyPow coeff (j + 1)).series_cusp_decay 1 (by norm_num)
  apply IsBigO.of_bound (‖derivativeScalar ^ (j + 1)‖ * C)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
  rw [zProfile_full_eq coeff constant j z v (lt_of_lt_of_le (by norm_num) hv),
    norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (mul_le_mul_of_nonneg_left (hb v z hv) (norm_nonneg _)).trans_eq (by ring)

theorem iteratedBar_star (f : ℂ → ℂ) (j : ℕ) :
    iteratedBar j (fun z => star (f z)) = fun z => star (iteratedZ j f z) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      funext z
      simp only [iteratedBar, iteratedZ, ih, horizontalWirtingerBar_star]

theorem iteratedZ_star (f : ℂ → ℂ) (j : ℕ) :
    iteratedZ j (fun z => star (f z)) = fun z => star (iteratedBar j f z) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      funext z
      simp only [iteratedZ, iteratedBar, ih, horizontalWirtingerZ_star]

theorem barProfile_star (f : HyperbolicSpace → ℂ) (j : ℕ) (z : ℂ) :
    barProfile (fun w => star (f w)) j z = fun v => star (zProfile f j z v) := by
  funext v
  exact congrFun (iteratedBar_star _ j) z

theorem zProfile_star (f : HyperbolicSpace → ℂ) (j : ℕ) (z : ℂ) :
    zProfile (fun w => star (f w)) j z = fun v => star (barProfile f j z v) := by
  funext v
  exact congrFun (iteratedZ_star _ j) z

end OAI.CubicEisenstein.AngularHigherProfiles
