import AngularBesselHigherDensity
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Differentiating the actual Schläfli integral to every fixed order

The integral identities use the proved density recurrence and integrable
majorants. They establish all finite-order smoothness of the actual cubic
Schläfli Bessel kernel on positive arguments. This module does not establish
mixed spatial derivative estimates or smoothness of its infinite cusp series.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Classical Topology ContDiff

namespace OAI.CubicEisenstein.AngularBesselHigherIntegral

open AngularBesselHigherDensity

def integral (n a b : ℕ) (x : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), density n a b x t

@[simp] theorem integral_zero (x : ℝ) :
    integral 0 0 0 x = ∫ t in Ioi (0 : ℝ), cubicBesselDensity x t := by
  simp [integral]

theorem integral_hasDerivAt (n a b : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (integral n a b) (integral (n + 1) a b x) x := by
  let δ := x / 2
  have hδ : 0 < δ := half_pos hx
  have hU : Ioi δ ∈ 𝓝 x := isOpen_Ioi.mem_nhds (by change δ < x; dsimp [δ]; linarith)
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ∀ y ∈ Ioi δ,
      ‖density (n + 1) a b y t‖ ≤ boundConstant (n + 1) a b δ * majorant t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htp : 0 < t := ht
    intro y hy
    have hyp : 0 < y := hδ.trans hy
    have he : Real.exp (-y / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc
      _ ≤ boundConstant (n + 1) a b δ * Real.exp (-y / 4) * majorant t :=
        density_bound (n + 1) a b δ y t hδ hy.le ht
      _ ≤ boundConstant (n + 1) a b δ * 1 * majorant t := by
        have hC := boundConstant_nonneg (n + 1) a b δ
        have hM : 0 ≤ majorant t := by unfold majorant; positivity
        gcongr
      _ = _ := by ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := density n a b) (F' := density (n + 1) a b)
    (bound := fun t => boundConstant (n + 1) a b δ * majorant t) hU
    (Eventually.of_forall (fun y => (density_measurable n a b y).aestronglyMeasurable))
    (density_integrable n a b x hx)
    (density_measurable (n + 1) a b x).aestronglyMeasurable
    hbound (majorant_integrable.const_mul (boundConstant (n + 1) a b δ))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro y hy
      exact density_hasDerivAt n a b y t ht)).2

theorem integral_continuousOn (n a b : ℕ) : ContinuousOn (integral n a b) (Ioi 0) := by
  intro x hx
  exact (integral_hasDerivAt n a b x hx).continuousAt.continuousWithinAt

theorem integral_contDiffOn (m n a b : ℕ) : ContDiffOn ℝ m (integral n a b) (Ioi 0) := by
  induction m generalizing n with
  | zero => exact contDiffOn_zero.mpr (integral_continuousOn n a b)
  | succ m ih =>
      rw [show ((m + 1 : ℕ) : ℕ∞ω) = (m : ℕ∞ω) + 1 by simp,
        contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        exact (integral_hasDerivAt n a b x hx).differentiableAt.differentiableWithinAt
      · simp
      · exact (ih (n + 1)).congr (fun x hx => (integral_hasDerivAt n a b x hx).deriv)

theorem integral_contDiffOn_infty (n a b : ℕ) :
    ContDiffOn ℝ ∞ (integral n a b) (Ioi 0) :=
  contDiffOn_infty.mpr (fun m => integral_contDiffOn m n a b)

theorem iteratedDeriv_integral (m n a b : ℕ) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv m (integral n a b) x = integral (n + m) a b x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv m (integral n a b) =ᶠ[𝓝 x] integral (n + m) a b := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        exact ih y hy
      rw [he.deriv_eq, (integral_hasDerivAt (n + m) a b x hx).deriv]
      congr 1

theorem integral_norm_bound (n a b : ℕ) (δ x : ℝ) (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖integral n a b x‖ ≤ boundConstant n a b δ * Real.exp (-x / 4) *
      ((2 : ℝ) ^ (1 / 3 : ℝ) * Real.Gamma (1 / 3)) := by
  have hb := integral_mono_ae (density_integrable n a b x (hδ.trans_le hx)).norm
    (majorant_integrable.const_mul (boundConstant n a b δ * Real.exp (-x / 4)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact density_bound n a b δ x t hδ hx ht)
  rw [integral_const_mul, show (∫ t in Ioi (0 : ℝ), majorant t) =
      (2 : ℝ) ^ (1 / 3 : ℝ) * Real.Gamma (1 / 3) from cubicBesselDerivativeMajorant_integral] at hb
  exact (norm_integral_le_integral_norm _).trans hb

theorem actual_integral_iteratedDeriv (n : ℕ) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv n (fun y => ∫ t in Ioi (0 : ℝ), cubicBesselDensity y t) x =
      ∫ t in Ioi (0 : ℝ), density n 0 0 x t := by
  have he : integral 0 0 0 = fun y => ∫ t in Ioi (0 : ℝ), cubicBesselDensity y t :=
    funext integral_zero
  rw [← he]
  convert! iteratedDeriv_integral n 0 0 0 x hx using 1
  simp only [Nat.zero_add, integral]

theorem schlafliBesselK_cubic_contDiffOn (n : ℕ) :
    ContDiffOn ℝ n (schlafliBesselK (1 / 3 : ℂ)) (Ioi 0) := by
  have hI : ContDiffOn ℝ n (integral 0 0 0) (Ioi 0) := integral_contDiffOn n 0 0 0
  have hp : ContDiffOn ℝ n (fun x : ℝ => (x / 2) ^ (-(1 : ℝ) / 3)) (Ioi 0) :=
    (contDiffOn_id.div_const 2).rpow_const_of_ne (by intro x hx; have hxp : 0 < x := hx; positivity)
  have hR : ContDiffOn ℝ n (fun x : ℝ =>
      (1 / 2 : ℝ) * (x / 2) ^ (-(1 : ℝ) / 3) * integral 0 0 0 x) (Ioi 0) :=
    (contDiffOn_const.mul hp).mul hI
  have hC := Complex.ofRealCLM.contDiff.comp_contDiffOn hR
  apply hC.congr
  intro x hx
  simpa only [Function.comp_apply, Complex.ofRealCLM_apply, integral_zero] using
    schlafliBesselK_cubic_real x hx

theorem schlafliBesselK_cubic_contDiffOn_infty :
    ContDiffOn ℝ ∞ (schlafliBesselK (1 / 3 : ℂ)) (Ioi 0) :=
  contDiffOn_infty.mpr schlafliBesselK_cubic_contDiffOn

end OAI.CubicEisenstein.AngularBesselHigherIntegral
