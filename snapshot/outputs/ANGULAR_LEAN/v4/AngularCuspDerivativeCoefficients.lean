import AngularCuspJets

/-! Exact coefficient functions in the inverse-cusp Wirtinger chain rule.
These are smooth actual coordinate derivatives, with their values and next
pure derivatives at the center proved explicitly. -/

noncomputable section
open scoped Classical Topology

namespace OAI.CubicEisenstein.AngularCuspDerivativeCoefficients

open AngularCuspJets AngularBesselDerivatives

def hCoeff (c d : ℂ) (v : ℝ) (z : ℂ) : ℂ :=
  horizontalWirtingerBar (fun w => (inverseCuspCoordinates c d v w).1) z

def barCoeff (c d : ℂ) (v : ℝ) (z : ℂ) : ℂ :=
  horizontalWirtingerBar (fun w => star (inverseCuspCoordinates c d v w).1) z

def vCoeff (c d : ℂ) (v : ℝ) (z : ℂ) : ℂ :=
  horizontalWirtingerBar (fun w => ((inverseCuspCoordinates c d v w).2 : ℂ)) z

theorem hCoeff_eq (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    hCoeff c d v = fun z => (-(c ^ 2)⁻¹ * (v : ℂ) ^ 2) * kernel v 0 1 z :=
  horizontal_coordinate_wirtingerBar c d v hv

theorem barCoeff_eq (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    barCoeff c d v = fun z => (star c ^ 2)⁻¹ * kernel v 2 1 z := by
  funext z
  simp only [barCoeff, conjugate_coordinate, horizontalWirtingerBar_const_sub,
    horizontalWirtingerBar_const_mul, kernel_wirtingerBar v hv]
  norm_num

theorem vCoeff_eq (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    vCoeff c d v = fun z => -((v / ‖c‖ ^ 2 : ℝ) : ℂ) * kernel v 1 1 z := by
  funext z
  simp only [vCoeff, height_coordinate, horizontalWirtingerBar_const_mul,
    kernel_wirtingerBar v hv]
  norm_num

theorem hCoeff_differentiable (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    Differentiable ℝ (hCoeff c d v) := by
  rw [hCoeff_eq c d v hv]
  exact (differentiable_const _).mul ((kernel_contDiff v hv 0 1).differentiable (by simp))

theorem barCoeff_differentiable (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    Differentiable ℝ (barCoeff c d v) := by
  rw [barCoeff_eq c d v hv]
  exact (differentiable_const _).mul ((kernel_contDiff v hv 2 1).differentiable (by simp))

theorem vCoeff_differentiable (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    Differentiable ℝ (vCoeff c d v) := by
  rw [vCoeff_eq c d v hv]
  exact (differentiable_const _).mul ((kernel_contDiff v hv 1 1).differentiable (by simp))

theorem hCoeff_zero (c d : ℂ) (hc : c ≠ 0) (v : ℝ) (hv : 0 < v) :
    hCoeff c d v 0 = -1 / (c ^ 2 * (v : ℂ) ^ 2) :=
  horizontal_coordinate_first_jet c d hc v hv

theorem barCoeff_zero (c d : ℂ) (v : ℝ) (hv : 0 < v) : barCoeff c d v 0 = 0 :=
  conjugate_coordinate_pure_jet_zero c d v hv 0

theorem vCoeff_zero (c d : ℂ) (v : ℝ) (hv : 0 < v) : vCoeff c d v 0 = 0 :=
  height_coordinate_pure_jet_zero c d v hv 1 (by norm_num)

theorem bar_hCoeff_zero (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    horizontalWirtingerBar (hCoeff c d v) 0 = 0 :=
  horizontal_coordinate_second_jet_zero c d v hv

theorem bar_barCoeff_zero (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    horizontalWirtingerBar (barCoeff c d v) 0 = 0 :=
  conjugate_coordinate_pure_jet_zero c d v hv 1

theorem bar_vCoeff_zero (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    horizontalWirtingerBar (vCoeff c d v) 0 = 0 :=
  height_coordinate_second_jet_zero c d v hv

theorem inverseCuspCoordinates_zero (c d : ℂ) (v : ℝ) :
    inverseCuspCoordinates c d v 0 = (-d / c, 1 / (‖c‖ ^ 2 * v)) := by
  unfold inverseCuspCoordinates
  simp only [star_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, zero_div, sub_zero]
  apply Prod.ext
  · rfl
  · by_cases hv : v = 0
    · simp [hv]
    · field_simp

end OAI.CubicEisenstein.AngularCuspDerivativeCoefficients
