import AngularProfileScaling
import AngularSourceSecondMellin

/-! Actual finite-cusp profiles: explicit scaled Bessel identities give
positive-height continuity and exponential decay. The proved order-two
reflection then gives genuine all-s Mellin convergence and an entire Mellin
transform for the actual source at the represented cusp, not only a formal
identity between totalized integrals. -/

noncomputable section
open Filter Asymptotics MeasureTheory Set
open scoped Classical Topology MatrixGroups

namespace OAI.CubicEisenstein.AngularFiniteCuspSecondMellin

open AngularHigherProfiles AngularHigherMellin AngularProfileScaling
open AngularFiniteCuspSecondReflection AngularSourceSecondMellin EisensteinEmbedding

theorem finite_source_profiles_regular (j : Fin 3) (n : ℕ) (z : ℂ) :
    ContinuousOn (barProfile (fun w => cubicSourceResidualFunction (representative j • w))
      (n + 1) z) (Ioi 0) ∧
    ContinuousOn (zProfile (fun w => cubicSourceResidualFunction (representative j • w))
      (n + 1) z) (Ioi 0) ∧
    (barProfile (fun w => cubicSourceResidualFunction (representative j • w)) (n + 1) z
      =O[atTop] (fun v : ℝ => Real.exp (-(residualCuspDecayRate / sourceCuspScale j) * v))) ∧
    (zProfile (fun w => cubicSourceResidualFunction (representative j • w)) (n + 1) z
      =O[atTop] (fun v : ℝ => Real.exp (-(residualCuspDecayRate / sourceCuspScale j) * v))) := by
  have hs := sourceCuspScale_pos j
  have hmap : MapsTo (fun v : ℝ => v / sourceCuspScale j) (Ioi 0) (Ioi 0) :=
    fun v hv => div_pos hv hs
  have hcont : ContinuousOn (fun v : ℝ => v / sourceCuspScale j) (Ioi 0) :=
    (continuous_id.div_const (sourceCuspScale j)).continuousOn
  have htop : Tendsto (fun v : ℝ => v / sourceCuspScale j) atTop atTop :=
    tendsto_id.atTop_div_const hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := (barProfile_full_continuousOn (sourceCuspCoefficients j)
      (sourceCuspBesselConstant j) n (z / (sourceCuspScale j : ℂ))).comp hcont hmap
    apply (continuousOn_const.mul hh).congr
    intro v hv
    exact finite_barProfile_eq j (n + 1) z v hv
  · have hh := (zProfile_full_continuousOn (sourceCuspCoefficients j)
      (sourceCuspBesselConstant j) n (z / (sourceCuspScale j : ℂ))).comp hcont hmap
    apply (continuousOn_const.mul hh).congr
    intro v hv
    exact finite_zProfile_eq j (n + 1) z v hv
  · have hh := ((barProfile_full_isBigO (sourceCuspCoefficients j)
      (sourceCuspBesselConstant j) n (z / (sourceCuspScale j : ℂ))).comp_tendsto htop).const_mul_left
      (((sourceCuspScale j : ℂ)⁻¹) ^ (n + 1))
    apply hh.congr'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
      exact (finite_barProfile_eq j (n + 1) z v hv).symm
    · filter_upwards [] with v
      change Real.exp (-residualCuspDecayRate * (v / sourceCuspScale j)) = _
      congr 1
      ring
  · have hh := ((zProfile_full_isBigO (sourceCuspCoefficients j)
      (sourceCuspBesselConstant j) n (z / (sourceCuspScale j : ℂ))).comp_tendsto htop).const_mul_left
      (((sourceCuspScale j : ℂ)⁻¹) ^ (n + 1))
    apply hh.congr'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
      exact (finite_zProfile_eq j (n + 1) z v hv).symm
    · filter_upwards [] with v
      change Real.exp (-residualCuspDecayRate * (v / sourceCuspScale j)) = _
      congr 1
      ring

theorem finite_conjugate_profiles_regular (j : Fin 3) (n : ℕ) (z : ℂ) :
    ContinuousOn (barProfile (fun w => cubicSourceConjugateFunction (representative j • w))
      (n + 1) z) (Ioi 0) ∧
    ContinuousOn (zProfile (fun w => cubicSourceConjugateFunction (representative j • w))
      (n + 1) z) (Ioi 0) ∧
    (barProfile (fun w => cubicSourceConjugateFunction (representative j • w)) (n + 1) z
      =O[atTop] (fun v : ℝ => Real.exp (-(residualCuspDecayRate / sourceCuspScale j) * v))) ∧
    (zProfile (fun w => cubicSourceConjugateFunction (representative j • w)) (n + 1) z
      =O[atTop] (fun v : ℝ => Real.exp (-(residualCuspDecayRate / sourceCuspScale j) * v))) := by
  have h := finite_source_profiles_regular j n z
  have hb : barProfile (fun w => cubicSourceConjugateFunction (representative j • w)) (n + 1) z =
      fun v => star (zProfile (fun w => cubicSourceResidualFunction (representative j • w)) (n + 1) z v) :=
    barProfile_star (fun w => cubicSourceResidualFunction (representative j • w)) (n + 1) z
  have hz : zProfile (fun w => cubicSourceConjugateFunction (representative j • w)) (n + 1) z =
      fun v => star (barProfile (fun w => cubicSourceResidualFunction (representative j • w)) (n + 1) z v) :=
    zProfile_star (fun w => cubicSourceResidualFunction (representative j • w)) (n + 1) z
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

theorem source_second_reflection (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j)
    (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    barProfile cubicSourceResidualFunction 2 (g 0 0 / g 1 0) v =
      reflected 4 (CubicKubota.complexCharacter G / (g 1 0) ^ 4) (‖g 1 0‖ ^ 2)
        (zProfile (fun w => cubicSourceResidualFunction (representative j • w)) 2
          (-g 1 1 / g 1 0)) v := by
  have hp : 0 < (‖g 1 0‖ ^ 2 * v)⁻¹ := by positivity
  rw [barProfile_positive _ _ _ _ hv, reflected, zProfile_positive _ _ _ _ hp]
  rw [cubicSourceResidualFunction_finite_second_reflection G j g hfactor hc v hv,
    second_prefactor]
  simp only [one_div, mul_assoc]

theorem conjugate_second_reflection (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j)
    (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    barProfile cubicSourceConjugateFunction 2 (g 0 0 / g 1 0) v =
      reflected 4 (star (CubicKubota.complexCharacter G) / (g 1 0) ^ 4) (‖g 1 0‖ ^ 2)
        (zProfile (fun w => cubicSourceConjugateFunction (representative j • w)) 2
          (-g 1 1 / g 1 0)) v := by
  have hp : 0 < (‖g 1 0‖ ^ 2 * v)⁻¹ := by positivity
  rw [barProfile_positive _ _ _ _ hv, reflected, zProfile_positive _ _ _ _ hp]
  rw [cubicSourceConjugateFunction_finite_second_reflection G j g hfactor hc v hv,
    second_prefactor]
  simp only [one_div, mul_assoc]

theorem source_second_mellin_entire (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j) (hc : g 1 0 ≠ 0) :
    (∀ s : ℂ, MellinConvergent (barProfile cubicSourceResidualFunction 2 (g 0 0 / g 1 0)) s) ∧
    Differentiable ℂ (mellin (barProfile cubicSourceResidualFunction 2 (g 0 0 / g 1 0))) := by
  have hf := source_profiles_regular 1 (g 0 0 / g 1 0)
  have hg := finite_source_profiles_regular j 1 (-g 1 1 / g 1 0)
  exact mellin_entire 4 _ _ residualCuspDecayRate (residualCuspDecayRate / sourceCuspScale j)
    (by positivity) residualCuspDecayRate_pos (div_pos residualCuspDecayRate_pos (sourceCuspScale_pos j))
    _ _ hf.1 hg.2.1 hf.2.2.1 hg.2.2.2 (source_second_reflection G j g hfactor hc)

theorem conjugate_second_mellin_entire (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j) (hc : g 1 0 ≠ 0) :
    (∀ s : ℂ, MellinConvergent (barProfile cubicSourceConjugateFunction 2 (g 0 0 / g 1 0)) s) ∧
    Differentiable ℂ (mellin (barProfile cubicSourceConjugateFunction 2 (g 0 0 / g 1 0))) := by
  have hf := conjugate_profiles_regular 1 (g 0 0 / g 1 0)
  have hg := finite_conjugate_profiles_regular j 1 (-g 1 1 / g 1 0)
  exact mellin_entire 4 _ _ residualCuspDecayRate (residualCuspDecayRate / sourceCuspScale j)
    (by positivity) residualCuspDecayRate_pos (div_pos residualCuspDecayRate_pos (sourceCuspScale_pos j))
    _ _ hf.1 hg.2.1 hf.2.2.1 hg.2.2.2 (conjugate_second_reflection G j g hfactor hc)

theorem source_second_mellin_reflection (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j) (hc : g 1 0 ≠ 0) (s : ℂ) :
    mellin (barProfile cubicSourceResidualFunction 2 (g 0 0 / g 1 0)) (2 * s + 1) =
      (CubicKubota.complexCharacter G / (g 1 0) ^ 4) *
        (‖g 1 0‖ ^ 2 : ℝ) ^ (3 - 2 * s : ℂ) *
          mellin (zProfile (fun w => cubicSourceResidualFunction (representative j • w)) 2
            (-g 1 1 / g 1 0)) (3 - 2 * s) := by
  simpa only [Nat.cast_ofNat, show (2 * s + (2 : ℂ) - 1) = 2 * s + 1 by ring,
    show ((2 : ℂ) + 1 - 2 * s) = 3 - 2 * s by ring] using
      OAI.SevenEighths.Angular.AnalyticFoundation.cusp_mellin_reflection_order_of_identity
        2 _ _ _ s _ (by positivity) (by
          intro v hv
          simpa only [reflected, Nat.cast_ofNat,
            show (-2 * (2 : ℂ)) = -(4 : ℂ) by norm_num] using
              source_second_reflection G j g hfactor hc v hv)

theorem conjugate_second_mellin_reflection (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j) (hc : g 1 0 ≠ 0) (s : ℂ) :
    mellin (barProfile cubicSourceConjugateFunction 2 (g 0 0 / g 1 0)) (2 * s + 1) =
      (star (CubicKubota.complexCharacter G) / (g 1 0) ^ 4) *
        (‖g 1 0‖ ^ 2 : ℝ) ^ (3 - 2 * s : ℂ) *
          mellin (zProfile (fun w => cubicSourceConjugateFunction (representative j • w)) 2
            (-g 1 1 / g 1 0)) (3 - 2 * s) := by
  simpa only [Nat.cast_ofNat, show (2 * s + (2 : ℂ) - 1) = 2 * s + 1 by ring,
    show ((2 : ℂ) + 1 - 2 * s) = 3 - 2 * s by ring] using
      OAI.SevenEighths.Angular.AnalyticFoundation.cusp_mellin_reflection_order_of_identity
        2 _ _ _ s _ (by positivity) (by
          intro v hv
          simpa only [reflected, Nat.cast_ofNat,
            show (-2 * (2 : ℂ)) = -(4 : ℂ) by norm_num] using
              conjugate_second_reflection G j g hfactor hc v hv)

end OAI.CubicEisenstein.AngularFiniteCuspSecondMellin
