import AngularBesselDerivatives
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Product differentiation at a vanishing coordinate factor. Only continuity
of the other factor is required. This is used for the vertical derivative
coefficient in second-order inverse-cusp composition; it does not assert that
the physical Bessel function has joint derivatives of all orders. -/

noncomputable section
open scoped Classical Topology
open Filter

namespace OAI.CubicEisenstein.AngularCuspProductAtZero

theorem hasDerivAt_continuous_mul_zero {f g : ℝ → ℂ} {x : ℝ} {g' : ℂ}
    (hf : ContinuousAt f x) (hg : HasDerivAt g g' x) (hzero : g x = 0) :
    HasDerivAt (fun t => f t * g t) (f x * g') x := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  convert (hf.tendsto.mono_left nhdsWithin_le_nhds).mul hg.tendsto_slope using 1
  funext y
  simp only [slope_def_module, hzero, mul_zero, sub_zero, Complex.real_smul]
  ring

theorem wirtingerBar_continuous_mul_zero {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContinuousAt f z) (hg : DifferentiableAt ℝ g z) (hzero : g z = 0) :
    horizontalWirtingerBar (fun w => f w * g w) z =
      f z * horizontalWirtingerBar g z := by
  have hline (direction : ℂ) :
      HasDerivAt (fun t : ℝ => z + (t : ℂ) * direction) direction 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const direction).const_add z)
  have hgl (direction : ℂ) :
      HasDerivAt (fun t : ℝ => g (z + (t : ℂ) * direction))
        (fderiv ℝ g z direction) 0 := by
    have hge : HasFDerivAt g (fderiv ℝ g z) (z + (0 : ℂ) * direction) := by simpa using hg.hasFDerivAt
    have hd := hge.comp_hasDerivAt 0 (hline direction)
    convert! hd using 1
  have hfl (direction : ℂ) :
      ContinuousAt (fun t : ℝ => f (z + (t : ℂ) * direction)) 0 := by
    have hfe : ContinuousAt f (z + (0 : ℂ) * direction) := by simpa using hf
    convert! (hfe.comp (f := fun t : ℝ => z + (t : ℂ) * direction)
      (hline direction).continuousAt) using 1
  have hp (direction : ℂ) := hasDerivAt_continuous_mul_zero (hfl direction)
    (hgl direction) (by simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hzero)
  have hp1 := (hp 1).deriv
  have hpI := (hp Complex.I).deriv
  have hg1 := (hgl 1).deriv
  have hgI := (hgl Complex.I).deriv
  simp only [mul_one, Complex.ofReal_zero, zero_mul, add_zero] at hp1 hg1 hpI
  rw [horizontalWirtingerBar, horizontalWirtingerBar, hp1, hpI, hg1, hgI]
  ring

end OAI.CubicEisenstein.AngularCuspProductAtZero
