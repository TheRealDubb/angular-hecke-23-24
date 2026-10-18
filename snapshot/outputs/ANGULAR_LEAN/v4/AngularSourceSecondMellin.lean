import AngularCuspSecondReflection
import AngularHigherProfiles
import AngularHigherMellin

/-! Order-two Mellin reflection and entire Mellin transforms of the actual
residual and conjugate cubic sources at principal level-three cusps. Physical
automorphy, Bessel regularity, decay and convergence are discharged. This is
not a zero-free L-function theorem or a claim that a zero-harmonic residue
vanishes. -/

noncomputable section
open Filter Asymptotics MeasureTheory Set
open scoped Classical Topology MatrixGroups

namespace OAI.CubicEisenstein.AngularSourceSecondMellin

open AngularBesselDerivatives AngularHigherProfiles AngularHigherMellin
open AngularCuspSecondReflection EisensteinEmbedding

theorem second_prefactor (κ c : ℂ) (v : ℝ) :
    κ * (-1 / (c ^ 2 * (v : ℂ) ^ 2)) ^ 2 =
      (κ / c ^ 4) * (v : ℂ) ^ (-4 : ℂ) := by
  rw [show (-4 : ℂ) = -(4 : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_ofNat]
  ring

theorem source_second_reflection (G : CubicKubota.levelThree)
    (hc : complexMatrix G 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    barProfile cubicSourceResidualFunction 2 (complexMatrix G 0 0 / complexMatrix G 1 0) v =
      reflected 4 (CubicKubota.complexCharacter G / (complexMatrix G 1 0) ^ 4)
        (‖complexMatrix G 1 0‖ ^ 2)
        (zProfile cubicSourceResidualFunction 2 (-complexMatrix G 1 1 / complexMatrix G 1 0)) v := by
  have hp : 0 < (‖complexMatrix G 1 0‖ ^ 2 * v)⁻¹ := by positivity
  rw [barProfile_positive _ _ _ _ hv, reflected, zProfile_positive _ _ _ _ hp]
  rw [cubicSourceResidualFunction_principal_second_reflection G hc v hv, second_prefactor]
  simp only [one_div, mul_assoc]

theorem conjugate_second_reflection (G : CubicKubota.levelThree)
    (hc : complexMatrix G 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    barProfile cubicSourceConjugateFunction 2 (complexMatrix G 0 0 / complexMatrix G 1 0) v =
      reflected 4 (star (CubicKubota.complexCharacter G) / (complexMatrix G 1 0) ^ 4)
        (‖complexMatrix G 1 0‖ ^ 2)
        (zProfile cubicSourceConjugateFunction 2 (-complexMatrix G 1 1 / complexMatrix G 1 0)) v := by
  have hp : 0 < (‖complexMatrix G 1 0‖ ^ 2 * v)⁻¹ := by positivity
  rw [barProfile_positive _ _ _ _ hv, reflected, zProfile_positive _ _ _ _ hp]
  rw [cubicSourceConjugateFunction_principal_second_reflection G hc v hv, second_prefactor]
  simp only [one_div, mul_assoc]

theorem source_profiles_regular (j : ℕ) (z : ℂ) :
    ContinuousOn (barProfile cubicSourceResidualFunction (j + 1) z) (Ioi 0) ∧
    ContinuousOn (zProfile cubicSourceResidualFunction (j + 1) z) (Ioi 0) ∧
    (barProfile cubicSourceResidualFunction (j + 1) z =O[atTop]
      (fun v : ℝ => Real.exp (-residualCuspDecayRate * v))) ∧
    (zProfile cubicSourceResidualFunction (j + 1) z =O[atTop]
      (fun v : ℝ => Real.exp (-residualCuspDecayRate * v))) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact ⟨barProfile_full_continuousOn sourceBesselCoefficients _ j z,
    zProfile_full_continuousOn sourceBesselCoefficients _ j z,
    barProfile_full_isBigO sourceBesselCoefficients _ j z,
    zProfile_full_isBigO sourceBesselCoefficients _ j z⟩

theorem conjugate_profiles_regular (j : ℕ) (z : ℂ) :
    ContinuousOn (barProfile cubicSourceConjugateFunction (j + 1) z) (Ioi 0) ∧
    ContinuousOn (zProfile cubicSourceConjugateFunction (j + 1) z) (Ioi 0) ∧
    (barProfile cubicSourceConjugateFunction (j + 1) z =O[atTop]
      (fun v : ℝ => Real.exp (-residualCuspDecayRate * v))) ∧
    (zProfile cubicSourceConjugateFunction (j + 1) z =O[atTop]
      (fun v : ℝ => Real.exp (-residualCuspDecayRate * v))) := by
  have h := source_profiles_regular j z
  have hb : barProfile cubicSourceConjugateFunction (j + 1) z =
      fun v => star (zProfile cubicSourceResidualFunction (j + 1) z v) :=
    barProfile_star cubicSourceResidualFunction (j + 1) z
  have hz : zProfile cubicSourceConjugateFunction (j + 1) z =
      fun v => star (barProfile cubicSourceResidualFunction (j + 1) z v) :=
    zProfile_star cubicSourceResidualFunction (j + 1) z
  rw [hb, hz]
  refine ⟨h.2.1.star, h.1.star, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := isBigO_iff.mp h.2.2.2
    apply IsBigO.of_bound C
    filter_upwards [hC] with v hv
    simpa only [norm_star] using hv
  · obtain ⟨C, hC⟩ := isBigO_iff.mp h.2.2.1
    apply IsBigO.of_bound C
    filter_upwards [hC] with v hv
    simpa only [norm_star] using hv

theorem source_second_mellin_entire (G : CubicKubota.levelThree)
    (hc : complexMatrix G 1 0 ≠ 0) :
    (∀ s : ℂ, MellinConvergent
      (barProfile cubicSourceResidualFunction 2 (complexMatrix G 0 0 / complexMatrix G 1 0)) s) ∧
    Differentiable ℂ
      (mellin (barProfile cubicSourceResidualFunction 2 (complexMatrix G 0 0 / complexMatrix G 1 0))) := by
  have hf := source_profiles_regular 1 (complexMatrix G 0 0 / complexMatrix G 1 0)
  have hg := source_profiles_regular 1 (-complexMatrix G 1 1 / complexMatrix G 1 0)
  exact mellin_entire 4 _ _ residualCuspDecayRate residualCuspDecayRate
    (by positivity) residualCuspDecayRate_pos residualCuspDecayRate_pos
    _ _ hf.1 hg.2.1 hf.2.2.1 hg.2.2.2 (source_second_reflection G hc)

theorem conjugate_second_mellin_entire (G : CubicKubota.levelThree)
    (hc : complexMatrix G 1 0 ≠ 0) :
    (∀ s : ℂ, MellinConvergent
      (barProfile cubicSourceConjugateFunction 2 (complexMatrix G 0 0 / complexMatrix G 1 0)) s) ∧
    Differentiable ℂ
      (mellin (barProfile cubicSourceConjugateFunction 2 (complexMatrix G 0 0 / complexMatrix G 1 0))) := by
  have hf := conjugate_profiles_regular 1 (complexMatrix G 0 0 / complexMatrix G 1 0)
  have hg := conjugate_profiles_regular 1 (-complexMatrix G 1 1 / complexMatrix G 1 0)
  exact mellin_entire 4 _ _ residualCuspDecayRate residualCuspDecayRate
    (by positivity) residualCuspDecayRate_pos residualCuspDecayRate_pos
    _ _ hf.1 hg.2.1 hf.2.2.1 hg.2.2.2 (conjugate_second_reflection G hc)

theorem source_second_mellin_reflection (G : CubicKubota.levelThree)
    (hc : complexMatrix G 1 0 ≠ 0) (s : ℂ) :
    mellin (barProfile cubicSourceResidualFunction 2
      (complexMatrix G 0 0 / complexMatrix G 1 0)) (2 * s + 1) =
      (CubicKubota.complexCharacter G / (complexMatrix G 1 0) ^ 4) *
        (‖complexMatrix G 1 0‖ ^ 2 : ℝ) ^ (3 - 2 * s : ℂ) *
          mellin (zProfile cubicSourceResidualFunction 2
            (-complexMatrix G 1 1 / complexMatrix G 1 0)) (3 - 2 * s) := by
  simpa only [Nat.cast_ofNat, show (2 * s + (2 : ℂ) - 1) = 2 * s + 1 by ring,
    show ((2 : ℂ) + 1 - 2 * s) = 3 - 2 * s by ring] using
      OAI.SevenEighths.Angular.AnalyticFoundation.cusp_mellin_reflection_order_of_identity
        2 _ _ _ s _ (by positivity) (by
          intro v hv
          simpa only [reflected, Nat.cast_ofNat,
            show (-2 * (2 : ℂ)) = -(4 : ℂ) by norm_num] using source_second_reflection G hc v hv)

theorem conjugate_second_mellin_reflection (G : CubicKubota.levelThree)
    (hc : complexMatrix G 1 0 ≠ 0) (s : ℂ) :
    mellin (barProfile cubicSourceConjugateFunction 2
      (complexMatrix G 0 0 / complexMatrix G 1 0)) (2 * s + 1) =
      (star (CubicKubota.complexCharacter G) / (complexMatrix G 1 0) ^ 4) *
        (‖complexMatrix G 1 0‖ ^ 2 : ℝ) ^ (3 - 2 * s : ℂ) *
          mellin (zProfile cubicSourceConjugateFunction 2
            (-complexMatrix G 1 1 / complexMatrix G 1 0)) (3 - 2 * s) := by
  simpa only [Nat.cast_ofNat, show (2 * s + (2 : ℂ) - 1) = 2 * s + 1 by ring,
    show ((2 : ℂ) + 1 - 2 * s) = 3 - 2 * s by ring] using
      OAI.SevenEighths.Angular.AnalyticFoundation.cusp_mellin_reflection_order_of_identity
        2 _ _ _ s _ (by positivity) (by
          intro v hv
          simpa only [reflected, Nat.cast_ofNat,
            show (-2 * (2 : ℂ)) = -(4 : ℂ) by norm_num] using conjugate_second_reflection G hc v hv)

end OAI.CubicEisenstein.AngularSourceSecondMellin
