import AngularBesselKernelDifferentiation

/-! All fixed-order real spatial regularity of the actual Bessel series and
the full function, with its arbitrary cusp constant retained. The proof uses
local summation on positive heights, not a global uniform-series assertion. -/

noncomputable section
open Set
open scoped Classical Topology ContDiff

namespace OAI.CubicEisenstein.AngularBesselSpatialSmoothness

open AngularBesselClosure AngularBesselKernelSeries AngularBesselKernelDifferentiation

def positiveHeight : Set (ℝ × ℂ) := {p | 0 < p.1}

theorem positiveHeight_open : IsOpen positiveHeight :=
  isOpen_lt continuous_const continuous_fst

theorem field_contDiffOn (m n : ℕ) (coeff : SubexponentialBesselCoefficients)
    (hv : ContDiffOn ℝ m (series (radial coeff) (n + 1)) positiveHeight)
    (hz : ContDiffOn ℝ m (series (frequency coeff) n) positiveHeight)
    (hb : ContDiffOn ℝ m (series (conjugateFrequency coeff) n) positiveHeight) :
    ContDiffOn ℝ m (seriesFDeriv coeff n) positiveHeight := by
  have h1 := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℂ) ℂ
    (ContinuousLinearMap.fst ℝ ℝ ℂ)).contDiff.comp_contDiffOn
      ((contDiffOn_const (c := (4 * Real.pi : ℂ))).mul hv)
  have h2 := ((contDiffOn_const (c := (2 * Real.pi * Complex.I : ℂ))).mul hz).smul
    (contDiffOn_const (c := ContinuousLinearMap.snd ℝ ℝ ℂ))
  have h3 := ((contDiffOn_const (c := (2 * Real.pi * Complex.I : ℂ))).mul hb).smul
    (contDiffOn_const (c := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
      (ContinuousLinearMap.snd ℝ ℝ ℂ)))
  exact (h1.add h2).add h3

theorem kernelSeries_contDiffOn (m : ℕ) (coeff : SubexponentialBesselCoefficients) (n : ℕ) :
    ContDiffOn ℝ m (series coeff n) positiveHeight := by
  induction m generalizing coeff n with
  | zero =>
      apply contDiffOn_zero.mpr
      intro p hp
      exact (series_continuousAt coeff n p hp).continuousWithinAt
  | succ m ih =>
      rw [show ((m + 1 : ℕ) : ℕ∞ω) = (m : ℕ∞ω) + 1 by simp,
        contDiffOn_succ_iff_fderiv_of_isOpen positiveHeight_open]
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        exact (series_hasFDerivAt coeff n p hp).differentiableAt.differentiableWithinAt
      · simp
      · exact (field_contDiffOn m n coeff (ih _ _) (ih _ _) (ih _ _)).congr
          (fun p hp => (series_hasFDerivAt coeff n p hp).fderiv)

theorem kernelSeries_contDiffOn_infty (coeff : SubexponentialBesselCoefficients) (n : ℕ) :
    ContDiffOn ℝ ∞ (series coeff n) positiveHeight :=
  contDiffOn_infty.mpr (fun m => kernelSeries_contDiffOn m coeff n)

theorem actual_series_contDiffOn (m : ℕ) (coeff : SubexponentialBesselCoefficients) :
    ContDiffOn ℝ m coeff.series positiveHeight := by
  have hv : ContDiffOn ℝ m (fun p : ℝ × ℂ => (p.1 : ℂ)) positiveHeight :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_fst
  exact (hv.mul (kernelSeries_contDiffOn m coeff 0)).congr
    (fun p hp => actual_series_eq coeff p hp)

theorem actual_series_contDiffAt (m : ℕ) (coeff : SubexponentialBesselCoefficients)
    (p : ℝ × ℂ) (hp : 0 < p.1) : ContDiffAt ℝ m coeff.series p :=
  (actual_series_contDiffOn m coeff p hp).contDiffAt (positiveHeight_open.mem_nhds hp)

theorem fullFunction_cusp_contDiffAt (m : ℕ) (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (p : ℝ × ℂ) (hp : 0 < p.1) :
    ContDiffAt ℝ m (fun q : ℝ × ℂ => coeff.fullFunction constant (cuspCoordinateLift q)) p := by
  have hreal : ContDiffAt ℝ m (fun q : ℝ × ℂ => q.1 ^ (2 / 3 : ℝ)) p :=
    contDiff_fst.contDiffAt.rpow_const_of_ne hp.ne'
  have hcast := Complex.ofRealCLM.contDiff.contDiffAt.comp p hreal
  have hpow : ContDiffAt ℝ m (fun q : ℝ × ℂ => (q.1 : ℂ) ^ (2 / 3 : ℂ)) p := by
    apply hcast.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
    have he := Complex.ofReal_cpow (le_of_lt hq) (2 / 3 : ℝ)
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at he
    exact he.symm
  have hfull : ContDiffAt ℝ m
      (fun q : ℝ × ℂ => constant * (q.1 : ℂ) ^ (2 / 3 : ℂ) + coeff.series q) p :=
    (contDiffAt_const.mul hpow).add (actual_series_contDiffAt m coeff p hp)
  apply hfull.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.fullFunction_cusp_eq constant q hq

theorem fullFunction_cusp_contDiffOn_infty (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) : ContDiffOn ℝ ∞
      (fun q : ℝ × ℂ => coeff.fullFunction constant (cuspCoordinateLift q)) positiveHeight := by
  apply contDiffOn_infty.mpr
  intro m p hp
  exact (fullFunction_cusp_contDiffAt m coeff constant p hp).contDiffWithinAt

end OAI.CubicEisenstein.AngularBesselSpatialSmoothness
