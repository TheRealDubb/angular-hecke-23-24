import AngularCuspChainRule
import AngularCuspLineCalculus
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Pure Wirtinger jet algebra derived from actual real differentiation.
The regularity used here is smoothness at all finite orders (∞), not analytic
order (ω). No complex multilinearity of a real derivative is assumed. -/

noncomputable section
open scoped Classical Topology ContDiff

namespace OAI.CubicEisenstein.AngularWirtingerJets

open AngularBesselDerivatives AngularCuspJets AngularCuspChainRule
open AngularCuspLineCalculus

theorem bar_eq_fderiv (f : ℂ → ℂ) (hf : Differentiable ℝ f) :
    horizontalWirtingerBar f = fun z =>
      (1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) := by
  funext z
  exact horizontalWirtingerBar_eq_linear f z _ (hf z).hasFDerivAt

theorem bar_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (horizontalWirtingerBar f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z 1) := hd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun z => fderiv ℝ f z Complex.I) :=
    hd.clm_apply contDiff_const
  rw [bar_eq_fderiv f (hf.differentiable (by simp))]
  exact contDiff_const.mul (h1.add (contDiff_const.mul hI))

theorem iteratedBar_contDiff (j : ℕ) {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (iteratedBar j f) := by
  induction j with
  | zero => exact hf
  | succ j ih => exact bar_contDiff ih

theorem bar_add {f g : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    horizontalWirtingerBar (fun z => f z + g z) =
      fun z => horizontalWirtingerBar f z + horizontalWirtingerBar g z := by
  funext z
  exact wirtingerBar_add
    (line_of_differentiable (hf.differentiable (by simp) z))
    (line_of_differentiable (hg.differentiable (by simp) z))

theorem bar_mul {f g : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    horizontalWirtingerBar (fun z => f z * g z) = fun z =>
      horizontalWirtingerBar f z * g z + f z * horizontalWirtingerBar g z := by
  funext z
  exact wirtingerBar_mul
    (line_of_differentiable (hf.differentiable (by simp) z))
    (line_of_differentiable (hg.differentiable (by simp) z))

theorem iteratedBar_add (j : ℕ) {f g : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    iteratedBar j (fun z => f z + g z) =
      fun z => iteratedBar j f z + iteratedBar j g z := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [iteratedBar, ih]
    exact bar_add (iteratedBar_contDiff j hf) (iteratedBar_contDiff j hg)

/-- A smooth multiplier with no positive pure bar jets at the center acts
on every pure jet by multiplication by its value. The proof differentiates
the actual real product rule; it does not invoke a formal complex direction. -/
theorem iteratedBar_mul_flat (j : ℕ) {f g : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hflat : ∀ i : ℕ, iteratedBar (i + 1) g 0 = 0) :
    iteratedBar j (fun z => f z * g z) 0 = iteratedBar j f 0 * g 0 := by
  induction j generalizing f g with
  | zero => rfl
  | succ j ih =>
    have hflat' : ∀ i : ℕ, iteratedBar (i + 1) (horizontalWirtingerBar g) 0 = 0 := by
      intro i
      rw [← iteratedBar_succ_inner]
      exact hflat (i + 1)
    rw [iteratedBar_succ_inner, bar_mul hf hg,
      iteratedBar_add j ((bar_contDiff hf).mul hg) (hf.mul (bar_contDiff hg))]
    simp only
    rw [ih (bar_contDiff hf) hg hflat, ih hf (bar_contDiff hg) hflat']
    have hg0 : horizontalWirtingerBar g 0 = 0 := hflat 0
    rw [hg0, mul_zero, add_zero, ← iteratedBar_succ_inner]

theorem iteratedBar_mul_zero_flat (j : ℕ) {f g : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hzero : g 0 = 0) (hflat : ∀ i : ℕ, iteratedBar (i + 1) g 0 = 0) :
    iteratedBar j (fun z => f z * g z) 0 = 0 := by
  rw [iteratedBar_mul_flat j hf hg hflat, hzero, mul_zero]

end OAI.CubicEisenstein.AngularWirtingerJets
