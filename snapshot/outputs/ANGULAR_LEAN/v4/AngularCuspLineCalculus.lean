import AngularCuspProductAtZero

/-! Actual real-line differentiability witnesses for the sums and products
used in second-order cusp composition. -/

noncomputable section
open scoped Classical Topology

namespace OAI.CubicEisenstein.AngularCuspLineCalculus

open AngularCuspProductAtZero

def LineDifferentiable (f : ℂ → ℂ) (z : ℂ) : Prop :=
  ∀ direction : ℂ, DifferentiableAt ℝ (fun t : ℝ => f (z + (t : ℂ) * direction)) 0

theorem line_of_differentiable {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    LineDifferentiable f z := by
  intro direction
  have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * direction) direction 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const direction).const_add z)
  have hfe : HasFDerivAt f (fderiv ℝ f z) (z + (0 : ℂ) * direction) := by simpa using hf.hasFDerivAt
  convert! (hfe.comp_hasDerivAt 0 hl).differentiableAt using 1

theorem line_continuous_mul_zero {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContinuousAt f z) (hg : DifferentiableAt ℝ g z) (hzero : g z = 0) :
    LineDifferentiable (fun w => f w * g w) z := by
  intro direction
  have hl : ContinuousAt (fun t : ℝ => z + (t : ℂ) * direction) 0 := by fun_prop
  have hfe : ContinuousAt f (z + (0 : ℂ) * direction) := by simpa using hf
  have hfc : ContinuousAt (fun t : ℝ => f (z + (t : ℂ) * direction)) 0 := by
    convert! hfe.comp (f := fun t : ℝ => z + (t : ℂ) * direction) hl using 1
  have hd := hasDerivAt_continuous_mul_zero hfc
    (line_of_differentiable hg direction).hasDerivAt
    (by simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hzero)
  exact hd.differentiableAt

theorem line_add {f g : ℂ → ℂ} {z : ℂ}
    (hf : LineDifferentiable f z) (hg : LineDifferentiable g z) :
    LineDifferentiable (fun w => f w + g w) z := fun d => (hf d).add (hg d)

theorem line_mul {f g : ℂ → ℂ} {z : ℂ}
    (hf : LineDifferentiable f z) (hg : LineDifferentiable g z) :
    LineDifferentiable (fun w => f w * g w) z := fun d => (hf d).mul (hg d)

theorem wirtingerBar_add {f g : ℂ → ℂ} {z : ℂ}
    (hf : LineDifferentiable f z) (hg : LineDifferentiable g z) :
    horizontalWirtingerBar (fun w => f w + g w) z =
      horizontalWirtingerBar f z + horizontalWirtingerBar g z := by
  have hf1 : DifferentiableAt ℝ (fun t : ℝ => f (z + (t : ℂ))) 0 := by simpa using hf 1
  have hg1 : DifferentiableAt ℝ (fun t : ℝ => g (z + (t : ℂ))) 0 := by simpa using hg 1
  simp only [horizontalWirtingerBar]
  rw [deriv_fun_add hf1 hg1, deriv_fun_add (hf Complex.I) (hg Complex.I)]
  ring

theorem wirtingerBar_mul {f g : ℂ → ℂ} {z : ℂ}
    (hf : LineDifferentiable f z) (hg : LineDifferentiable g z) :
    horizontalWirtingerBar (fun w => f w * g w) z =
      horizontalWirtingerBar f z * g z + f z * horizontalWirtingerBar g z := by
  have hf1 : DifferentiableAt ℝ (fun t : ℝ => f (z + (t : ℂ))) 0 := by simpa using hf 1
  have hg1 : DifferentiableAt ℝ (fun t : ℝ => g (z + (t : ℂ))) 0 := by simpa using hg 1
  simp only [horizontalWirtingerBar]
  rw [deriv_fun_mul hf1 hg1, deriv_fun_mul (hf Complex.I) (hg Complex.I)]
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  ring

end OAI.CubicEisenstein.AngularCuspLineCalculus
