import AngularBesselDerivatives
import OAI.NumberTheory.DirichletL.Eisenstein.ConjugateCuspProfiles

/-!
# Joint C1 regularity of the physical horizontal Bessel partials

The full function retains its arbitrary cusp constant. Its horizontal partials
are the actual frequency-weighted Bessel series, whose joint C1 regularity is
already supplied by OAI for every subexponential coefficient array. Vertical
partial continuity follows from C1 regularity of the full function. No C2 or
all-order vertical regularity is assumed or asserted.
-/

noncomputable section
open scoped Classical Topology
open Set Filter

namespace OAI.CubicEisenstein.AngularBesselHorizontalRegularity

open AngularBesselClosure AngularBesselDerivatives

def splitFull (coeff : SubexponentialBesselCoefficients) (constant : ℂ)
    (p : ℂ × ℝ) : ℂ :=
  coeff.fullFunction constant (cuspCoordinateLift (p.2, p.1))

def zCoefficient (coeff : SubexponentialBesselCoefficients) (constant : ℂ)
    (p : ℂ × ℝ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ (splitFull coeff constant) p (1, 0) -
    Complex.I * fderiv ℝ (splitFull coeff constant) p (Complex.I, 0))

def barCoefficient (coeff : SubexponentialBesselCoefficients) (constant : ℂ)
    (p : ℂ × ℝ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ (splitFull coeff constant) p (1, 0) +
    Complex.I * fderiv ℝ (splitFull coeff constant) p (Complex.I, 0))

def vCoefficient (coeff : SubexponentialBesselCoefficients) (constant : ℂ)
    (p : ℂ × ℝ) : ℂ :=
  fderiv ℝ (splitFull coeff constant) p (0, 1)

theorem splitFull_contDiffAt_one (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (p : ℂ × ℝ) (hp : 0 < p.2) :
    ContDiffAt ℝ 1 (splitFull coeff constant) p := by
  have hswap : ContDiffAt ℝ 1 (fun q : ℂ × ℝ => (q.2, q.1)) p := by fun_prop
  have h := (coeff.fullFunction_cusp_contDiffAt_one constant (p.2, p.1) hp).comp p hswap
  exact h

theorem splitFull_eq (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    splitFull coeff constant (z, v) =
      constant * (v : ℂ) ^ (2 / 3 : ℂ) + coeff.series (v, z) :=
  coeff.fullFunction_cusp_eq constant (v, z) hv

theorem splitFull_wirtingerZ (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    horizontalWirtingerZ (fun w => splitFull coeff constant (w, v)) z =
      derivativeScalar * (frequency coeff).series (v, z) := by
  have he : (fun w => splitFull coeff constant (w, v)) =
      fun w => constant * (v : ℂ) ^ (2 / 3 : ℂ) + coeff.series (v, w) := by
    funext w; exact splitFull_eq coeff constant w v hv
  rw [he]
  simpa only [horizontalWirtingerZ, deriv_const_add] using series_wirtingerZ coeff v hv z

theorem splitFull_wirtingerBar (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    horizontalWirtingerBar (fun w => splitFull coeff constant (w, v)) z =
      derivativeScalar * (conjugateFrequency coeff).series (v, z) := by
  have he : (fun w => splitFull coeff constant (w, v)) =
      fun w => constant * (v : ℂ) ^ (2 / 3 : ℂ) + coeff.series (v, w) := by
    funext w; exact splitFull_eq coeff constant w v hv
  rw [he]
  simpa only [horizontalWirtingerBar, deriv_const_add] using series_wirtingerBar coeff v hv z

theorem zCoefficient_eq (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (p : ℂ × ℝ) (hp : 0 < p.2) :
    zCoefficient coeff constant p = derivativeScalar * (frequency coeff).series (p.2, p.1) := by
  have hd := ((splitFull_contDiffAt_one coeff constant p hp).differentiableAt (by norm_num)).hasFDerivAt
  have he := horizontalWirtingerZ_eq_fderiv (splitFull coeff constant)
    (fderiv ℝ (splitFull coeff constant) p) p.1 p.2 hd
  unfold zCoefficient
  rw [← he]
  exact splitFull_wirtingerZ coeff constant p.1 p.2 hp

theorem barCoefficient_eq (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (p : ℂ × ℝ) (hp : 0 < p.2) :
    barCoefficient coeff constant p =
      derivativeScalar * (conjugateFrequency coeff).series (p.2, p.1) := by
  have hd := ((splitFull_contDiffAt_one coeff constant p hp).differentiableAt (by norm_num)).hasFDerivAt
  have he := horizontalWirtingerBar_eq_fderiv (splitFull coeff constant)
    (fderiv ℝ (splitFull coeff constant) p) p.1 p.2 hd
  unfold barCoefficient
  rw [← he]
  exact splitFull_wirtingerBar coeff constant p.1 p.2 hp

theorem zCoefficient_contDiffAt_one (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (p : ℂ × ℝ) (hp : 0 < p.2) :
    ContDiffAt ℝ 1 (zCoefficient coeff constant) p := by
  have hswap : ContDiffAt ℝ 1 (fun q : ℂ × ℝ => (q.2, q.1)) p := by fun_prop
  have hw := ((frequency coeff).series_contDiffAt_one (p.2, p.1) hp).comp p hswap
  have h : ContDiffAt ℝ 1 (fun q : ℂ × ℝ =>
      derivativeScalar * (frequency coeff).series (q.2, q.1)) p := contDiffAt_const.mul hw
  apply h.congr_of_eventuallyEq
  filter_upwards [continuousAt_snd.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact zCoefficient_eq coeff constant q hq

theorem barCoefficient_contDiffAt_one (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (p : ℂ × ℝ) (hp : 0 < p.2) :
    ContDiffAt ℝ 1 (barCoefficient coeff constant) p := by
  have hswap : ContDiffAt ℝ 1 (fun q : ℂ × ℝ => (q.2, q.1)) p := by fun_prop
  have hw := ((conjugateFrequency coeff).series_contDiffAt_one (p.2, p.1) hp).comp p hswap
  have h : ContDiffAt ℝ 1 (fun q : ℂ × ℝ =>
      derivativeScalar * (conjugateFrequency coeff).series (q.2, q.1)) p := contDiffAt_const.mul hw
  apply h.congr_of_eventuallyEq
  filter_upwards [continuousAt_snd.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact barCoefficient_eq coeff constant q hq

theorem splitFull_fderiv_continuousAt (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (p : ℂ × ℝ) (hp : 0 < p.2) :
    ContinuousAt (fderiv ℝ (splitFull coeff constant)) p :=
  (splitFull_contDiffAt_one coeff constant p hp).continuousAt_fderiv (by norm_num)

theorem vCoefficient_continuousAt (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (p : ℂ × ℝ) (hp : 0 < p.2) :
    ContinuousAt (vCoefficient coeff constant) p :=
  (splitFull_fderiv_continuousAt coeff constant p hp).clm_apply continuousAt_const

theorem inverse_cusp_center_regular (coeff : SubexponentialBesselCoefficients)
    (constant c d : ℂ) (hc : c ≠ 0) (v : ℝ) (hv : 0 < v) :
    let p : ℂ × ℝ := (-d / c, 1 / (‖c‖ ^ 2 * v))
    ContDiffAt ℝ 1 (splitFull coeff constant) p ∧
    ContDiffAt ℝ 1 (zCoefficient coeff constant) p ∧
    ContDiffAt ℝ 1 (barCoefficient coeff constant) p ∧
    ContinuousAt (vCoefficient coeff constant) p := by
  have hp : 0 < 1 / (‖c‖ ^ 2 * v) :=
    one_div_pos.mpr (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hc)) hv)
  exact ⟨splitFull_contDiffAt_one coeff constant _ hp,
    zCoefficient_contDiffAt_one coeff constant _ hp,
    barCoefficient_contDiffAt_one coeff constant _ hp,
    vCoefficient_continuousAt coeff constant _ hp⟩

end OAI.CubicEisenstein.AngularBesselHorizontalRegularity
