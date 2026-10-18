import AngularCuspChainRule
import AngularCuspLineCalculus
import AngularCuspDerivativeCoefficients
import AngularBesselHorizontalRegularity

/-! The actual second pure inverse-cusp composition formula, including its
physical Bessel instantiation. Joint C1 of the horizontal partial suffices;
the vertical partial is used only continuously at a vanishing coordinate
factor. No joint C2 assumption is supplied. -/

noncomputable section
open scoped Classical Topology

namespace OAI.CubicEisenstein.AngularCuspSecondOrder

open AngularBesselDerivatives AngularCuspChainRule AngularCuspLineCalculus
open AngularCuspDerivativeCoefficients AngularCuspProductAtZero
open AngularBesselHorizontalRegularity

theorem inverse_cusp_second_pure (c d : ℂ) (hc : c ≠ 0) (v : ℝ) (hv : 0 < v)
    (F : ℂ × ℝ → ℂ)
    (hF : ∀ p : ℂ × ℝ, 0 < p.2 → DifferentiableAt ℝ F p)
    (hZ : DifferentiableAt ℝ (partialZ F) (-d / c, 1 / (‖c‖ ^ 2 * v)))
    (hB : ContinuousAt (partialBar F) (-d / c, 1 / (‖c‖ ^ 2 * v)))
    (hV : ContinuousAt (partialV F) (-d / c, 1 / (‖c‖ ^ 2 * v))) :
    iteratedBar 2 (fun z => F (inverseCuspCoordinates c d v z)) 0 =
      (-1 / (c ^ 2 * (v : ℂ) ^ 2)) ^ 2 *
        iteratedZ 2 (fun z => F (z, 1 / (‖c‖ ^ 2 * v))) (-d / c) := by
  let g := inverseCuspCoordinates c d v
  let AZ := fun z => partialZ F (g z)
  let AB := fun z => partialBar F (g z)
  let AV := fun z => partialV F (g z)
  have hgd : Differentiable ℝ g :=
    (inverseCuspCoordinates_contDiff c d v hv).differentiable (by simp)
  have hZ' : DifferentiableAt ℝ (partialZ F) (g 0) := by
    simpa only [g, inverseCuspCoordinates_zero] using hZ
  have hB' : ContinuousAt (partialBar F) (g 0) := by
    simpa only [g, inverseCuspCoordinates_zero] using hB
  have hV' : ContinuousAt (partialV F) (g 0) := by
    simpa only [g, inverseCuspCoordinates_zero] using hV
  have hAZ : DifferentiableAt ℝ AZ 0 := by convert! hZ'.comp 0 (hgd 0) using 1
  have hAB : ContinuousAt AB 0 := by convert! hB'.comp (f := g) (hgd 0).continuousAt using 1
  have hAV : ContinuousAt AV 0 := by convert! hV'.comp (f := g) (hgd 0).continuousAt using 1
  have hA := hCoeff_differentiable c d v hv 0
  have hC := barCoeff_differentiable c d v hv 0
  have hY := vCoeff_differentiable c d v hv 0
  have hLA := line_mul (line_of_differentiable hAZ) (line_of_differentiable hA)
  have hLB := line_continuous_mul_zero hAB hC (barCoeff_zero c d v hv)
  have hLV := line_continuous_mul_zero hAV hY (vCoeff_zero c d v hv)
  have he : horizontalWirtingerBar (fun z => F (g z)) = fun z =>
      AZ z * hCoeff c d v z + AB z * barCoeff c d v z + AV z * vCoeff c d v z := by
    funext z
    exact inverse_cusp_wirtingerBar_chain c d v hc hv F hF z
  have hmain : horizontalWirtingerBar AZ 0 =
      (-1 / (c ^ 2 * (v : ℂ) ^ 2)) *
        horizontalWirtingerZ (fun z => partialZ F (z, 1 / (‖c‖ ^ 2 * v))) (-d / c) :=
    inverse_cusp_wirtinger_rule c d v hc hv (partialZ F) _ hZ.hasFDerivAt
  have hp : 0 < 1 / (‖c‖ ^ 2 * v) := by positivity
  have hrow : (fun z => partialZ F (z, 1 / (‖c‖ ^ 2 * v))) =
      horizontalWirtingerZ (fun z => F (z, 1 / (‖c‖ ^ 2 * v))) := by
    funext z
    exact (horizontalWirtingerZ_eq_fderiv F _ z _ (hF _ hp).hasFDerivAt).symm
  change horizontalWirtingerBar (horizontalWirtingerBar (fun z => F (g z))) 0 = _
  rw [he, wirtingerBar_add (line_add hLA hLB) hLV, wirtingerBar_add hLA hLB,
    wirtingerBar_mul (line_of_differentiable hAZ) (line_of_differentiable hA),
    wirtingerBar_continuous_mul_zero hAB hC (barCoeff_zero c d v hv),
    wirtingerBar_continuous_mul_zero hAV hY (vCoeff_zero c d v hv),
    bar_hCoeff_zero c d v hv, bar_barCoeff_zero c d v hv,
    bar_vCoeff_zero c d v hv, hCoeff_zero c d hc v hv, hmain, hrow]
  simp only [iteratedZ, mul_zero, add_zero]
  ring

/-- The full physical Bessel function satisfies the order-two rule, with its
arbitrary cusp constant retained and every regularity input discharged. -/
theorem fullFunction_inverse_cusp_second_pure (coeff : SubexponentialBesselCoefficients)
    (constant c d : ℂ) (hc : c ≠ 0) (v : ℝ) (hv : 0 < v) :
    iteratedBar 2
      (fun z => splitFull coeff constant (inverseCuspCoordinates c d v z)) 0 =
      (-1 / (c ^ 2 * (v : ℂ) ^ 2)) ^ 2 *
        iteratedZ 2 (fun z => splitFull coeff constant (z, 1 / (‖c‖ ^ 2 * v))) (-d / c) := by
  have hp : 0 < 1 / (‖c‖ ^ 2 * v) := by positivity
  apply inverse_cusp_second_pure c d hc v hv (splitFull coeff constant)
  · intro p hp
    exact (splitFull_contDiffAt_one coeff constant p hp).differentiableAt (by norm_num)
  · exact (zCoefficient_contDiffAt_one coeff constant _ hp).differentiableAt (by norm_num)
  · exact (barCoefficient_contDiffAt_one coeff constant _ hp).continuousAt
  · exact vCoefficient_continuousAt coeff constant _ hp

end OAI.CubicEisenstein.AngularCuspSecondOrder
