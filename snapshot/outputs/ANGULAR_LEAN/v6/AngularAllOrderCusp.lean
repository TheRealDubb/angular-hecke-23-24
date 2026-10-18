import AngularWirtingerJets
import AngularCuspDerivativeCoefficients

/-! All-order pure inverse-cusp composition from actual real smoothness.
The outer function is assumed smooth on the positive-height domain. This is
an explicit regularity hypothesis, not a claimed physical Bessel instance.
The proof uses the full real three-term chain rule and the actual coordinate
jets, including all terms containing vertical or conjugate-horizontal partials.
-/

noncomputable section
open scoped Classical Topology ContDiff

namespace OAI.CubicEisenstein.AngularAllOrderCusp

open AngularBesselDerivatives AngularCuspJets AngularCuspChainRule
open AngularCuspDerivativeCoefficients AngularWirtingerJets

def positiveHeight : Set (ℂ × ℝ) := {p | 0 < p.2}

theorem positiveHeight_isOpen : IsOpen positiveHeight :=
  isOpen_lt continuous_const continuous_snd

theorem partialZ_contDiffOn {F : ℂ × ℝ → ℂ}
    (hF : ContDiffOn ℝ ∞ F positiveHeight) :
    ContDiffOn ℝ ∞ (partialZ F) positiveHeight := by
  have hd := hF.fderiv_of_isOpen positiveHeight_isOpen (m := ∞) (by simp)
  have h1 : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p (1, 0)) positiveHeight :=
    hd.clm_apply contDiffOn_const
  have hI : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p (Complex.I, 0)) positiveHeight :=
    hd.clm_apply contDiffOn_const
  exact contDiffOn_const.mul (h1.sub (contDiffOn_const.mul hI))

theorem partialBar_contDiffOn {F : ℂ × ℝ → ℂ}
    (hF : ContDiffOn ℝ ∞ F positiveHeight) :
    ContDiffOn ℝ ∞ (partialBar F) positiveHeight := by
  have hd := hF.fderiv_of_isOpen positiveHeight_isOpen (m := ∞) (by simp)
  have h1 : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p (1, 0)) positiveHeight :=
    hd.clm_apply contDiffOn_const
  have hI : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p (Complex.I, 0)) positiveHeight :=
    hd.clm_apply contDiffOn_const
  exact contDiffOn_const.mul (h1.add (contDiffOn_const.mul hI))

theorem partialV_contDiffOn {F : ℂ × ℝ → ℂ}
    (hF : ContDiffOn ℝ ∞ F positiveHeight) :
    ContDiffOn ℝ ∞ (partialV F) positiveHeight := by
  exact (hF.fderiv_of_isOpen positiveHeight_isOpen (m := ∞) (by simp)).clm_apply
    contDiffOn_const

theorem differentiableAt_of_positive {F : ℂ × ℝ → ℂ}
    (hF : ContDiffOn ℝ ∞ F positiveHeight) (p : ℂ × ℝ) (hp : 0 < p.2) :
    DifferentiableAt ℝ F p :=
  (hF.contDiffAt (positiveHeight_isOpen.mem_nhds hp)).differentiableAt (by simp)

theorem inverse_comp_contDiff (c d : ℂ) (hc : c ≠ 0) (v : ℝ) (hv : 0 < v)
    {F : ℂ × ℝ → ℂ} (hF : ContDiffOn ℝ ∞ F positiveHeight) :
    ContDiff ℝ ∞ (fun z => F (inverseCuspCoordinates c d v z)) := by
  exact hF.comp_contDiff ((inverseCuspCoordinates_contDiff c d v hv).of_le le_top)
    (fun z => inverseCuspCoordinates_height_pos c d v z hc hv)

theorem hCoeff_contDiff (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    ContDiff ℝ ∞ (hCoeff c d v) := by
  rw [hCoeff_eq c d v hv]
  exact contDiff_const.mul ((kernel_contDiff v hv 0 1).of_le le_top)

theorem barCoeff_contDiff (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    ContDiff ℝ ∞ (barCoeff c d v) := by
  rw [barCoeff_eq c d v hv]
  exact contDiff_const.mul ((kernel_contDiff v hv 2 1).of_le le_top)

theorem vCoeff_contDiff (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    ContDiff ℝ ∞ (vCoeff c d v) := by
  rw [vCoeff_eq c d v hv]
  exact contDiff_const.mul ((kernel_contDiff v hv 1 1).of_le le_top)

theorem hCoeff_positive_pure_jets (c d : ℂ) (v : ℝ) (hv : 0 < v) (i : ℕ) :
    iteratedBar (i + 1) (hCoeff c d v) 0 = 0 := by
  change iteratedBar (i + 1)
    (horizontalWirtingerBar (fun z => (inverseCuspCoordinates c d v z).1)) 0 = 0
  rw [← iteratedBar_succ_inner]
  exact horizontal_coordinate_pure_jet_zero c d v hv (i + 1) (by omega)

theorem barCoeff_positive_pure_jets (c d : ℂ) (v : ℝ) (hv : 0 < v) (i : ℕ) :
    iteratedBar (i + 1) (barCoeff c d v) 0 = 0 := by
  change iteratedBar (i + 1)
    (horizontalWirtingerBar (fun z => star (inverseCuspCoordinates c d v z).1)) 0 = 0
  rw [← iteratedBar_succ_inner]
  exact conjugate_coordinate_pure_jet_zero c d v hv (i + 1)

theorem vCoeff_positive_pure_jets (c d : ℂ) (v : ℝ) (hv : 0 < v) (i : ℕ) :
    iteratedBar (i + 1) (vCoeff c d v) 0 = 0 := by
  change iteratedBar (i + 1)
    (horizontalWirtingerBar (fun z => ((inverseCuspCoordinates c d v z).2 : ℂ))) 0 = 0
  rw [← iteratedBar_succ_inner]
  exact height_coordinate_pure_jet_zero c d v hv (i + 1 + 1) (by omega)

theorem iteratedZ_succ_inner (j : ℕ) (f : ℂ → ℂ) :
    iteratedZ (j + 1) f = iteratedZ j (horizontalWirtingerZ f) := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg horizontalWirtingerZ ih

theorem partialZ_slice {F : ℂ × ℝ → ℂ}
    (hF : ContDiffOn ℝ ∞ F positiveHeight) (y : ℝ) (hy : 0 < y) :
    (fun z => partialZ F (z, y)) = horizontalWirtingerZ (fun z => F (z, y)) := by
  funext z
  exact (horizontalWirtingerZ_eq_fderiv F _ z y
    (differentiableAt_of_positive hF (z, y) hy).hasFDerivAt).symm

/-- All pure bar jets of the actual inverse-cusp pullback, for an outer
function genuinely smooth in the real spatial variables on positive heights.
No estimate or smoothness of a physical Bessel function is assumed silently. -/
theorem inverse_cusp_all_pure (j : ℕ) (c d : ℂ) (hc : c ≠ 0) (v : ℝ) (hv : 0 < v)
    (F : ℂ × ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F positiveHeight) :
    iteratedBar j (fun z => F (inverseCuspCoordinates c d v z)) 0 =
      (-1 / (c ^ 2 * (v : ℂ) ^ 2)) ^ j *
        iteratedZ j (fun z => F (z, 1 / (‖c‖ ^ 2 * v))) (-d / c) := by
  induction j generalizing F with
  | zero => simp only [iteratedBar, iteratedZ, pow_zero, one_mul, inverseCuspCoordinates_zero]
  | succ j ih =>
    let g := inverseCuspCoordinates c d v
    let AZ := fun z => partialZ F (g z)
    let AB := fun z => partialBar F (g z)
    let AV := fun z => partialV F (g z)
    have hAZ : ContDiff ℝ ∞ AZ := inverse_comp_contDiff c d hc v hv (partialZ_contDiffOn hF)
    have hAB : ContDiff ℝ ∞ AB := inverse_comp_contDiff c d hc v hv (partialBar_contDiffOn hF)
    have hAV : ContDiff ℝ ∞ AV := inverse_comp_contDiff c d hc v hv (partialV_contDiffOn hF)
    have hA := hCoeff_contDiff c d v hv
    have hB := barCoeff_contDiff c d v hv
    have hV := vCoeff_contDiff c d v hv
    have he : horizontalWirtingerBar (fun z => F (g z)) = fun z =>
        AZ z * hCoeff c d v z + AB z * barCoeff c d v z + AV z * vCoeff c d v z := by
      funext z
      exact inverse_cusp_wirtingerBar_chain c d v hc hv F
        (differentiableAt_of_positive hF) z
    change iteratedBar (j + 1) (fun z => F (g z)) 0 = _
    rw [iteratedBar_succ_inner, he,
      iteratedBar_add j ((hAZ.mul hA).add (hAB.mul hB)) (hAV.mul hV),
      iteratedBar_add j (hAZ.mul hA) (hAB.mul hB)]
    simp only
    rw [iteratedBar_mul_flat j hAZ hA (hCoeff_positive_pure_jets c d v hv),
      iteratedBar_mul_zero_flat j hAB hB (barCoeff_zero c d v hv)
        (barCoeff_positive_pure_jets c d v hv),
      iteratedBar_mul_zero_flat j hAV hV (vCoeff_zero c d v hv)
        (vCoeff_positive_pure_jets c d v hv)]
    simp only [add_zero]
    rw [hCoeff_zero c d hc v hv]
    change iteratedBar j (fun z => partialZ F (inverseCuspCoordinates c d v z)) 0 * _ = _
    rw [ih (partialZ F) (partialZ_contDiffOn hF),
      partialZ_slice hF _ (by positivity), ← iteratedZ_succ_inner]
    simp only [pow_succ]
    ring

/-- A form of the same theorem whose hypothesis explicitly lists all finite
orders. This avoids confusing smooth order ∞ with analytic order ω. -/
theorem inverse_cusp_all_pure_of_finite_orders (j : ℕ) (c d : ℂ) (hc : c ≠ 0)
    (v : ℝ) (hv : 0 < v) (F : ℂ × ℝ → ℂ)
    (hF : ∀ n : ℕ, ContDiffOn ℝ n F positiveHeight) :
    iteratedBar j (fun z => F (inverseCuspCoordinates c d v z)) 0 =
      (-1 / (c ^ 2 * (v : ℂ) ^ 2)) ^ j *
        iteratedZ j (fun z => F (z, 1 / (‖c‖ ^ 2 * v))) (-d / c) :=
  inverse_cusp_all_pure j c d hc v hv F (contDiffOn_infty.mpr hF)

/-- Pointwise all-finite-order regularity on the positive-height domain is
enough; no regularity on nonpositive heights is requested. -/
theorem inverse_cusp_all_pure_of_pointwise_finite_orders (j : ℕ) (c d : ℂ) (hc : c ≠ 0)
    (v : ℝ) (hv : 0 < v) (F : ℂ × ℝ → ℂ)
    (hF : ∀ (n : ℕ) (p : ℂ × ℝ), 0 < p.2 → ContDiffAt ℝ n F p) :
    iteratedBar j (fun z => F (inverseCuspCoordinates c d v z)) 0 =
      (-1 / (c ^ 2 * (v : ℂ) ^ 2)) ^ j *
        iteratedZ j (fun z => F (z, 1 / (‖c‖ ^ 2 * v))) (-d / c) := by
  apply inverse_cusp_all_pure_of_finite_orders j c d hc v hv F
  intro n p hp
  exact (hF n p hp).contDiffWithinAt

end OAI.CubicEisenstein.AngularAllOrderCusp
