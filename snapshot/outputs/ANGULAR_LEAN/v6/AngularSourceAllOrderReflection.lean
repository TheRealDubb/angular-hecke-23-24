import AngularPhysicalAllOrderCusp
import AngularCuspSecondReflection

/-! All-order reflection for the actual principal residual and conjugate
cubic sources. The general transport theorem explicitly requires genuine
real smoothness on positive heights; its physical instances discharge this
with the full Bessel function, including the ordinary cusp constant. -/

noncomputable section
open scoped Classical Topology MatrixGroups ContDiff

namespace OAI.CubicEisenstein.AngularSourceAllOrderReflection

open AngularBesselDerivatives AngularCuspJets AngularCuspChainRule
open AngularAllOrderCusp AngularPhysicalAllOrderCusp AngularCuspSecondReflection
open AngularBesselHorizontalRegularity EisensteinEmbedding

/-- Every finite order, including zero, of actual cusp transport. Arbitrary
translated sources must supply their positive-height real smoothness. -/
theorem cuspDerivative_of_transform (order : ℕ) (f : HyperbolicSpace → ℂ)
    (g H : SL(2,ℂ)) (κ : ℂ)
    (htransform : ∀ w, f (g • w) = κ * f (H • w)) (hc : g 1 0 ≠ 0)
    (v : ℝ) (hv : 0 < v)
    (hF : ∀ (m : ℕ) (p : ℂ × ℝ), 0 < p.2 → ContDiffAt ℝ m
      (fun q : ℂ × ℝ => f (H • cuspCoordinateLift (q.2, q.1))) p) :
    iteratedBar order (fun z => f (upperPoint z v hv)) (g 0 0 / g 1 0) =
      κ * (-1 / ((g 1 0) ^ 2 * (v : ℂ) ^ 2)) ^ order *
        iteratedZ order (fun z => f (H • upperPoint z (1 / (‖g 1 0‖ ^ 2 * v))
          (by positivity))) (-g 1 1 / g 1 0) := by
  let FH : ℂ × ℝ → ℂ := fun q => f (H • cuspCoordinateLift (q.2, q.1))
  have he := inverse_cusp_all_pure_of_pointwise_finite_orders order
    (g 1 0) (g 1 1) hc v hv FH hF
  have hline : (fun z => κ * FH (inverseCuspCoordinates (g 1 0) (g 1 1) v z)) =
      (fun z => f (upperPoint (z + g 0 0 / g 1 0) v hv)) := by
    funext z
    have ht := htransform (g⁻¹ • upperPoint (z + g 0 0 / g 1 0) v hv)
    rw [smul_inv_smul, inverse_cusp_action g hc v hv z] at ht
    change κ * f (H • cuspCoordinateLift
      ((inverseCuspCoordinates (g 1 0) (g 1 1) v z).2,
       (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1)) = _
    rw [cuspCoordinateLift_positive _ _ (inverseCuspCoordinates_height_pos _ _ _ _ hc hv)]
    exact ht.symm
  have hFH : (fun z => FH (z, 1 / (‖g 1 0‖ ^ 2 * v))) =
      (fun z => f (H • upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity))) := by
    funext z
    exact congrArg (fun w => f (H • w)) (cuspCoordinateLift_positive _ _ (by positivity))
  have hshift := congrFun (iteratedBar_translate order (fun z => f (upperPoint z v hv))
    (g 0 0 / g 1 0)) 0
  simp only [zero_add] at hshift
  have hs := congrArg (fun a : ℂ => κ * a) he
  rw [hFH] at hs
  have hscaled := congrFun (iteratedBar_const_mul order κ
    (fun z => FH (inverseCuspCoordinates (g 1 0) (g 1 1) v z))) 0
  have htotal := hscaled.trans hs
  rw [hline] at htotal
  rw [← hshift]
  convert! htotal using 1 <;> ring

/-- The actual full Bessel source is smooth at every finite order. The
displayed automorphy identity is the only source-specific input here. -/
theorem fullFunction_all_reflection (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (order : ℕ) (g : SL(2,ℂ)) (κ : ℂ)
    (htransform : ∀ w, coeff.fullFunction constant (g • w) = κ * coeff.fullFunction constant w)
    (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    iteratedBar order (fun z => coeff.fullFunction constant (upperPoint z v hv))
      (g 0 0 / g 1 0) =
      κ * (-1 / ((g 1 0) ^ 2 * (v : ℂ) ^ 2)) ^ order *
        iteratedZ order (fun z => coeff.fullFunction constant
          (upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity))) (-g 1 1 / g 1 0) := by
  have h := cuspDerivative_of_transform order (coeff.fullFunction constant) g 1 κ
    (by simpa only [one_smul] using htransform) hc v hv
    (fun m p hp => by
      simp only [one_smul]
      convert! splitFull_contDiffAt m coeff constant p hp using 1)
  simpa only [one_smul] using h

/-- Conjugation preserves real smoothness. Its automorphy multiplier is
conjugated by the actual source theorem, not by changing the cusp coefficient. -/
theorem conjugate_fullFunction_all_reflection (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (order : ℕ) (g : SL(2,ℂ)) (κ : ℂ)
    (htransform : ∀ w, star (coeff.fullFunction constant (g • w)) =
      κ * star (coeff.fullFunction constant w))
    (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    iteratedBar order (fun z => star (coeff.fullFunction constant (upperPoint z v hv)))
      (g 0 0 / g 1 0) =
      κ * (-1 / ((g 1 0) ^ 2 * (v : ℂ) ^ 2)) ^ order *
        iteratedZ order (fun z => star (coeff.fullFunction constant
          (upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity)))) (-g 1 1 / g 1 0) := by
  have h := cuspDerivative_of_transform order (fun w => star (coeff.fullFunction constant w)) g 1 κ
    (by simpa only [one_smul] using htransform) hc v hv
    (fun m p hp => by
      simp only [one_smul]
      convert! Complex.conjCLE.contDiff.contDiffAt.comp p
        (splitFull_contDiffAt m coeff constant p hp) using 1)
  simpa only [one_smul] using h

/-- Actual residual-source reflection at every principal level-three cusp
and every finite derivative order. No regularity hypothesis remains. -/
theorem cubicSourceResidualFunction_principal_all_reflection (order : ℕ)
    (G : CubicKubota.levelThree) (hc : complexMatrix G 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    iteratedBar order (fun z => cubicSourceResidualFunction (upperPoint z v hv))
      (complexMatrix G 0 0 / complexMatrix G 1 0) =
      CubicKubota.complexCharacter G *
        (-1 / ((complexMatrix G 1 0) ^ 2 * (v : ℂ) ^ 2)) ^ order *
        iteratedZ order (fun z => cubicSourceResidualFunction
          (upperPoint z (1 / (‖complexMatrix G 1 0‖ ^ 2 * v)) (by positivity)))
          (-complexMatrix G 1 1 / complexMatrix G 1 0) := by
  have ht (w : HyperbolicSpace) := cubicSourceResidualFunction_levelThree G w
  simp only [cubicSourceResidualFunction_eq_bessel, sourceBesselFunction] at ht ⊢
  exact fullFunction_all_reflection sourceBesselCoefficients _ order _ _ ht hc v hv

/-- Actual conjugate-source reflection. The character is conjugated; the
inverse-cusp derivative factor is the same as for the residual source. -/
theorem cubicSourceConjugateFunction_principal_all_reflection (order : ℕ)
    (G : CubicKubota.levelThree) (hc : complexMatrix G 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    iteratedBar order (fun z => cubicSourceConjugateFunction (upperPoint z v hv))
      (complexMatrix G 0 0 / complexMatrix G 1 0) =
      star (CubicKubota.complexCharacter G) *
        (-1 / ((complexMatrix G 1 0) ^ 2 * (v : ℂ) ^ 2)) ^ order *
        iteratedZ order (fun z => cubicSourceConjugateFunction
          (upperPoint z (1 / (‖complexMatrix G 1 0‖ ^ 2 * v)) (by positivity)))
          (-complexMatrix G 1 1 / complexMatrix G 1 0) := by
  have ht (w : HyperbolicSpace) := cubicSourceConjugateFunction_levelThree G w
  simp only [cubicSourceConjugateFunction, cubicSourceResidualFunction_eq_bessel,
    sourceBesselFunction] at ht ⊢
  exact conjugate_fullFunction_all_reflection sourceBesselCoefficients _ order _ _ ht hc v hv

end OAI.CubicEisenstein.AngularSourceAllOrderReflection
