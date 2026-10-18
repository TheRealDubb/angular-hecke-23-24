import AngularCuspJets

/-! The real first-derivative chain rule in Wirtinger coordinates, including
the vertical term, at every point of the actual inverse-cusp map. No second
derivative of the Bessel function or assumed chain identity is introduced. -/

noncomputable section
open scoped Classical Topology

namespace OAI.CubicEisenstein.AngularCuspChainRule

open AngularCuspJets

def partialZ (F : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ F p (1, 0) - Complex.I * fderiv ℝ F p (Complex.I, 0))

def partialBar (F : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ F p (1, 0) + Complex.I * fderiv ℝ F p (Complex.I, 0))

def partialV (F : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ := fderiv ℝ F p (0, 1)

theorem horizontalWirtingerBar_eq_linear (f : ℂ → ℂ) (z : ℂ) (A : ℂ →L[ℝ] ℂ)
    (hf : HasFDerivAt f A z) :
    horizontalWirtingerBar f z = (1 / 2 : ℂ) * (A 1 + Complex.I * A Complex.I) := by
  have hline (direction : ℂ) :
      HasDerivAt (fun t : ℝ => f (z + (t : ℂ) * direction)) (A direction) 0 := by
    have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * direction) direction 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const direction).const_add z)
    have hfe : HasFDerivAt f A (z + (0 : ℂ) * direction) := by simpa using hf
    have hh := hfe.comp_hasDerivAt 0 hl
    convert! hh using 1
  have h1 := (hline 1).deriv
  have hI := (hline Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerBar, h1, hI]

theorem real_linear_split (A : (ℂ × ℝ) →L[ℝ] ℂ) (w : ℂ) (y : ℝ) :
    A (w, y) =
      ((1 / 2 : ℂ) * (A (1, 0) - Complex.I * A (Complex.I, 0))) * w +
      ((1 / 2 : ℂ) * (A (1, 0) + Complex.I * A (Complex.I, 0))) * star w +
      A (0, 1) * (y : ℂ) := by
  have hp : (w, y) = (w, (0 : ℝ)) + y • ((0, 1) : ℂ × ℝ) := by
    ext <;> simp
  rw [hp, map_add, map_smul, real_linear_horizontal_decompose]
  simp only [Complex.real_smul]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The full three-term rule for any real differentiable coordinate map. -/
theorem wirtingerBar_comp (F : ℂ × ℝ → ℂ) (g : ℂ → ℂ × ℝ) (z : ℂ)
    (hF : DifferentiableAt ℝ F (g z)) (hg : DifferentiableAt ℝ g z) :
    horizontalWirtingerBar (fun w => F (g w)) z =
      partialZ F (g z) * horizontalWirtingerBar (fun w => (g w).1) z +
      partialBar F (g z) * horizontalWirtingerBar (fun w => star (g w).1) z +
      partialV F (g z) * horizontalWirtingerBar (fun w => ((g w).2 : ℂ)) z := by
  have hcomp := hF.hasFDerivAt.comp z hg.hasFDerivAt
  have hh := hg.hasFDerivAt.fst
  have hstar := Complex.conjCLE.hasFDerivAt.comp z hh
  have hv := Complex.ofRealCLM.hasFDerivAt.comp z hg.hasFDerivAt.snd
  have hcomp' : HasFDerivAt (fun w => F (g w))
      ((fderiv ℝ F (g z)).comp (fderiv ℝ g z)) z := by convert! hcomp using 1
  have hstar' : HasFDerivAt (fun w => star (g w).1)
      (Complex.conjCLE.toContinuousLinearMap.comp
        ((ContinuousLinearMap.fst ℝ ℂ ℝ).comp (fderiv ℝ g z))) z := by
    convert! hstar using 1
  have hv' : HasFDerivAt (fun w => ((g w).2 : ℂ))
      (Complex.ofRealCLM.comp
        ((ContinuousLinearMap.snd ℝ ℂ ℝ).comp (fderiv ℝ g z))) z := by
    convert! hv using 1
  rw [horizontalWirtingerBar_eq_linear _ _ _ hcomp',
    horizontalWirtingerBar_eq_linear _ _ _ hh,
    horizontalWirtingerBar_eq_linear _ _ _ hstar',
    horizontalWirtingerBar_eq_linear _ _ _ hv']
  change (1 / 2 : ℂ) *
      ((fderiv ℝ F (g z)) ((fderiv ℝ g z) 1) +
        Complex.I * (fderiv ℝ F (g z)) ((fderiv ℝ g z) Complex.I)) =
    partialZ F (g z) * ((1 / 2 : ℂ) *
      (((fderiv ℝ g z) 1).1 + Complex.I * ((fderiv ℝ g z) Complex.I).1)) +
    partialBar F (g z) * ((1 / 2 : ℂ) *
      (star ((fderiv ℝ g z) 1).1 + Complex.I * star ((fderiv ℝ g z) Complex.I).1)) +
    partialV F (g z) * ((1 / 2 : ℂ) *
      ((((fderiv ℝ g z) 1).2 : ℂ) + Complex.I * (((fderiv ℝ g z) Complex.I).2 : ℂ)))
  rw [real_linear_split (fderiv ℝ F (g z)) ((fderiv ℝ g z) 1).1
      ((fderiv ℝ g z) 1).2,
    real_linear_split (fderiv ℝ F (g z)) ((fderiv ℝ g z) Complex.I).1
      ((fderiv ℝ g z) Complex.I).2]
  unfold partialZ partialBar partialV
  ring

theorem antiKernel_contDiff (v : ℝ) (hv : 0 < v) : ContDiff ℝ ⊤ (antiKernel v) := by
  have h := Complex.conjCLE.contDiff.mul
    ((denominator_contDiff v).inv (denominator_ne_zero v hv))
  convert! h using 1

/-- The concrete inverse-cusp coordinates are smooth at every horizontal point. -/
theorem inverseCuspCoordinates_contDiff (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    ContDiff ℝ ⊤ (inverseCuspCoordinates c d v) := by
  have hh : ContDiff ℝ ⊤ (fun z => (inverseCuspCoordinates c d v z).1) := by
    simp only [horizontal_coordinate]
    exact contDiff_const.sub (contDiff_const.mul (antiKernel_contDiff v hv))
  have hyc : ContDiff ℝ ⊤ (fun z => ((inverseCuspCoordinates c d v z).2 : ℂ)) := by
    simp only [height_coordinate]
    exact contDiff_const.mul (kernel_contDiff v hv 0 0)
  have hy : ContDiff ℝ ⊤ (fun z => (inverseCuspCoordinates c d v z).2) := by
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using
      Complex.reCLM.contDiff.comp hyc
  exact hh.prodMk hy

/-- The chain identity holds for every z, so it may subsequently be
differentiated at the center after proving the required term regularity. -/
theorem inverse_cusp_wirtingerBar_chain (c d : ℂ) (v : ℝ) (hc : c ≠ 0) (hv : 0 < v)
    (F : ℂ × ℝ → ℂ) (hF : ∀ p : ℂ × ℝ, 0 < p.2 → DifferentiableAt ℝ F p) (z : ℂ) :
    horizontalWirtingerBar (fun w => F (inverseCuspCoordinates c d v w)) z =
      partialZ F (inverseCuspCoordinates c d v z) *
        horizontalWirtingerBar (fun w => (inverseCuspCoordinates c d v w).1) z +
      partialBar F (inverseCuspCoordinates c d v z) *
        horizontalWirtingerBar (fun w => star (inverseCuspCoordinates c d v w).1) z +
      partialV F (inverseCuspCoordinates c d v z) *
        horizontalWirtingerBar (fun w => ((inverseCuspCoordinates c d v w).2 : ℂ)) z := by
  apply wirtingerBar_comp
  · exact hF _ (inverseCuspCoordinates_height_pos c d v z hc hv)
  · exact (inverseCuspCoordinates_contDiff c d v hv).differentiable (by simp) z

end OAI.CubicEisenstein.AngularCuspChainRule
