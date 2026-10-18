import AngularCuspSecondOrder

/-! Actual order-two reflection at principal cubic cusps. The conditional
transport lemma lists its horizontal-partial regularity inputs explicitly;
the physical Bessel and cubic-source instances discharge them. No arbitrary
translated C1 function is treated as having C1 horizontal partials. -/

noncomputable section
open scoped Classical Topology MatrixGroups

namespace OAI.CubicEisenstein.AngularCuspSecondReflection

open AngularBesselDerivatives AngularCuspJets AngularCuspChainRule
open AngularCuspSecondOrder AngularBesselHorizontalRegularity EisensteinEmbedding

theorem wirtingerBar_translate_at (f : ℂ → ℂ) (a z : ℂ) :
    horizontalWirtingerBar (fun w => f (w + a)) z = horizontalWirtingerBar f (z + a) := by
  have h1 : (fun t : ℝ => f (z + (t : ℂ) + a)) =
      (fun t : ℝ => f (z + a + (t : ℂ))) := by
    funext t; congr 1; ring
  have hI : (fun t : ℝ => f (z + (t : ℂ) * Complex.I + a)) =
      (fun t : ℝ => f (z + a + (t : ℂ) * Complex.I)) := by
    funext t; congr 1; ring
  unfold horizontalWirtingerBar
  rw [h1, hI]

theorem iteratedBar_translate (j : ℕ) (f : ℂ → ℂ) (a : ℂ) :
    iteratedBar j (fun z => f (z + a)) = fun z => iteratedBar j f (z + a) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      funext z
      simp only [iteratedBar, ih, wirtingerBar_translate_at]

theorem partialZ_star (F : ℂ × ℝ → ℂ) (p : ℂ × ℝ) :
    partialZ (fun q => star (F q)) p = star (partialBar F p) := by
  rw [partialZ, fderiv_star]
  simp [partialBar, sub_eq_add_neg]

theorem partialBar_star (F : ℂ × ℝ → ℂ) (p : ℂ × ℝ) :
    partialBar (fun q => star (F q)) p = star (partialZ F p) := by
  rw [partialBar, fderiv_star]
  simp [partialZ]

theorem partialV_star (F : ℂ × ℝ → ℂ) (p : ℂ × ℝ) :
    partialV (fun q => star (F q)) p = star (partialV F p) := by
  rw [partialV, fderiv_star]
  rfl

/-- Conditional transport statement. Unlike the first-order rule, this
requires a differentiable horizontal Z partial at the dual center. -/
theorem cuspSecondDerivative_of_transform (f : HyperbolicSpace → ℂ) (g H : SL(2,ℂ))
    (κ : ℂ) (htransform : ∀ w, f (g • w) = κ * f (H • w)) (hc : g 1 0 ≠ 0)
    (v : ℝ) (hv : 0 < v)
    (hF : ∀ p : ℂ × ℝ, 0 < p.2 → DifferentiableAt ℝ
      (fun q : ℂ × ℝ => f (H • cuspCoordinateLift (q.2, q.1))) p)
    (hZ : DifferentiableAt ℝ (partialZ
      (fun q : ℂ × ℝ => f (H • cuspCoordinateLift (q.2, q.1))))
      (-g 1 1 / g 1 0, 1 / (‖g 1 0‖ ^ 2 * v)))
    (hB : ContinuousAt (partialBar
      (fun q : ℂ × ℝ => f (H • cuspCoordinateLift (q.2, q.1))))
      (-g 1 1 / g 1 0, 1 / (‖g 1 0‖ ^ 2 * v)))
    (hV : ContinuousAt (partialV
      (fun q : ℂ × ℝ => f (H • cuspCoordinateLift (q.2, q.1))))
      (-g 1 1 / g 1 0, 1 / (‖g 1 0‖ ^ 2 * v))) :
    iteratedBar 2 (fun z => f (upperPoint z v hv)) (g 0 0 / g 1 0) =
      κ * (-1 / ((g 1 0) ^ 2 * (v : ℂ) ^ 2)) ^ 2 *
        iteratedZ 2 (fun z => f (H • upperPoint z (1 / (‖g 1 0‖ ^ 2 * v))
          (by positivity))) (-g 1 1 / g 1 0) := by
  let FH : ℂ × ℝ → ℂ := fun q => f (H • cuspCoordinateLift (q.2, q.1))
  have he := inverse_cusp_second_pure (g 1 0) (g 1 1) hc v hv FH hF hZ hB hV
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
  have hshift := congrFun (iteratedBar_translate 2 (fun z => f (upperPoint z v hv))
    (g 0 0 / g 1 0)) 0
  simp only [zero_add] at hshift
  have hs := congrArg (fun a : ℂ => κ * a) he
  rw [hFH] at hs
  have hscaled := congrFun (iteratedBar_const_mul 2 κ
    (fun z => FH (inverseCuspCoordinates (g 1 0) (g 1 1) v z))) 0
  have htotal := hscaled.trans hs
  rw [hline] at htotal
  rw [← hshift]
  convert! htotal using 1 <;> ring

/-- Full Bessel source, including the constant term. Its needed regularity is
proved, while the displayed automorphy identity remains an explicit input. -/
theorem fullFunction_second_reflection (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (g : SL(2,ℂ)) (κ : ℂ)
    (htransform : ∀ w, coeff.fullFunction constant (g • w) = κ * coeff.fullFunction constant w)
    (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    iteratedBar 2 (fun z => coeff.fullFunction constant (upperPoint z v hv)) (g 0 0 / g 1 0) =
      κ * (-1 / ((g 1 0) ^ 2 * (v : ℂ) ^ 2)) ^ 2 *
        iteratedZ 2 (fun z => coeff.fullFunction constant
          (upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity))) (-g 1 1 / g 1 0) := by
  have hp : 0 < 1 / (‖g 1 0‖ ^ 2 * v) := by positivity
  have h := cuspSecondDerivative_of_transform (coeff.fullFunction constant) g 1 κ
    (by simpa only [one_smul] using htransform) hc v hv
    (fun p hp => by
      simp only [one_smul]
      convert! (splitFull_contDiffAt_one coeff constant p hp).differentiableAt (by norm_num) using 1)
    (by
      simp only [one_smul]
      convert! (zCoefficient_contDiffAt_one coeff constant
        (-g 1 1 / g 1 0, 1 / (‖g 1 0‖ ^ 2 * v)) hp).differentiableAt (by norm_num) using 1)
    (by
      simp only [one_smul]
      convert! (barCoefficient_contDiffAt_one coeff constant
        (-g 1 1 / g 1 0, 1 / (‖g 1 0‖ ^ 2 * v)) hp).continuousAt using 1)
    (by
      simp only [one_smul]
      convert! vCoefficient_continuousAt coeff constant
        (-g 1 1 / g 1 0, 1 / (‖g 1 0‖ ^ 2 * v)) hp using 1)
  simpa only [one_smul] using h

/-- Conjugate Bessel source. Horizontal regularity follows from the opposite
horizontal partial of the original function; no vertical C2 input is used. -/
theorem conjugate_fullFunction_second_reflection (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (g : SL(2,ℂ)) (κ : ℂ)
    (htransform : ∀ w, star (coeff.fullFunction constant (g • w)) =
      κ * star (coeff.fullFunction constant w))
    (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    iteratedBar 2 (fun z => star (coeff.fullFunction constant (upperPoint z v hv)))
      (g 0 0 / g 1 0) =
      κ * (-1 / ((g 1 0) ^ 2 * (v : ℂ) ^ 2)) ^ 2 *
        iteratedZ 2 (fun z => star (coeff.fullFunction constant
          (upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity)))) (-g 1 1 / g 1 0) := by
  have hp : 0 < 1 / (‖g 1 0‖ ^ 2 * v) := by positivity
  have hZ : (partialZ (fun q => star (splitFull coeff constant q))) =
      fun q => star (barCoefficient coeff constant q) := by
    funext q; exact partialZ_star _ q
  have hB : (partialBar (fun q => star (splitFull coeff constant q))) =
      fun q => star (zCoefficient coeff constant q) := by
    funext q; exact partialBar_star _ q
  have hV : (partialV (fun q => star (splitFull coeff constant q))) =
      fun q => star (vCoefficient coeff constant q) := by
    funext q; exact partialV_star _ q
  have h := cuspSecondDerivative_of_transform (fun w => star (coeff.fullFunction constant w)) g 1 κ
    (by simpa only [one_smul] using htransform) hc v hv
    (fun p hp => by
      simp only [one_smul]
      convert! ((splitFull_contDiffAt_one coeff constant p hp).differentiableAt (by norm_num)).star using 1)
    (by
      simp only [one_smul]
      change DifferentiableAt ℝ (partialZ (fun q => star (splitFull coeff constant q))) _
      rw [hZ]
      convert! ((barCoefficient_contDiffAt_one coeff constant
        (-g 1 1 / g 1 0, 1 / (‖g 1 0‖ ^ 2 * v)) hp).differentiableAt (by norm_num)).star using 1)
    (by
      simp only [one_smul]
      change ContinuousAt (partialBar (fun q => star (splitFull coeff constant q))) _
      rw [hB]
      convert! (zCoefficient_contDiffAt_one coeff constant
        (-g 1 1 / g 1 0, 1 / (‖g 1 0‖ ^ 2 * v)) hp).continuousAt.star using 1)
    (by
      simp only [one_smul]
      change ContinuousAt (partialV (fun q => star (splitFull coeff constant q))) _
      rw [hV]
      convert! (vCoefficient_continuousAt coeff constant
        (-g 1 1 / g 1 0, 1 / (‖g 1 0‖ ^ 2 * v)) hp).star using 1)
  simpa only [one_smul] using h

/-- The actual cubic residual source at every principal level-three cusp. -/
theorem cubicSourceResidualFunction_principal_second_reflection (G : CubicKubota.levelThree)
    (hc : complexMatrix G 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    iteratedBar 2 (fun z => cubicSourceResidualFunction (upperPoint z v hv))
      (complexMatrix G 0 0 / complexMatrix G 1 0) =
      CubicKubota.complexCharacter G *
        (-1 / ((complexMatrix G 1 0) ^ 2 * (v : ℂ) ^ 2)) ^ 2 *
        iteratedZ 2 (fun z => cubicSourceResidualFunction
          (upperPoint z (1 / (‖complexMatrix G 1 0‖ ^ 2 * v)) (by positivity)))
          (-complexMatrix G 1 1 / complexMatrix G 1 0) := by
  have ht (w : HyperbolicSpace) := cubicSourceResidualFunction_levelThree G w
  simp only [cubicSourceResidualFunction_eq_bessel, sourceBesselFunction] at ht ⊢
  exact fullFunction_second_reflection sourceBesselCoefficients _ _ _ ht hc v hv

/-- The actual conjugate cubic source; its multiplier is conjugated, while
the inverse-cusp derivative coefficient itself is not conjugated. -/
theorem cubicSourceConjugateFunction_principal_second_reflection (G : CubicKubota.levelThree)
    (hc : complexMatrix G 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    iteratedBar 2 (fun z => cubicSourceConjugateFunction (upperPoint z v hv))
      (complexMatrix G 0 0 / complexMatrix G 1 0) =
      star (CubicKubota.complexCharacter G) *
        (-1 / ((complexMatrix G 1 0) ^ 2 * (v : ℂ) ^ 2)) ^ 2 *
        iteratedZ 2 (fun z => cubicSourceConjugateFunction
          (upperPoint z (1 / (‖complexMatrix G 1 0‖ ^ 2 * v)) (by positivity)))
          (-complexMatrix G 1 1 / complexMatrix G 1 0) := by
  have ht (w : HyperbolicSpace) := cubicSourceConjugateFunction_levelThree G w
  simp only [cubicSourceConjugateFunction, cubicSourceResidualFunction_eq_bessel,
    sourceBesselFunction] at ht ⊢
  exact conjugate_fullFunction_second_reflection sourceBesselCoefficients _ _ _ ht hc v hv

end OAI.CubicEisenstein.AngularCuspSecondReflection
