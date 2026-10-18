import AngularFiniteAllOrderReflection
import AngularMellinOrderAlgebra

/-! Actual finite-cusp Mellin reflection at every positive fixed order.
Both source and translated dual integrals converge for every complex Mellin
parameter and define entire functions. This is not a zero-free theorem. -/

noncomputable section
open Filter Asymptotics MeasureTheory Set
open scoped Classical Topology MatrixGroups

namespace OAI.CubicEisenstein.AngularFiniteAllOrderMellin

open AngularHigherProfiles AngularHigherMellin AngularMellinOrderAlgebra
open AngularFiniteCuspSecondReflection AngularSourceSecondMellin
open AngularFiniteCuspSecondMellin AngularFiniteCuspDualMellin
open AngularFiniteAllOrderReflection EisensteinEmbedding

theorem source_reflection (order : ℕ) (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j) (hc : g 1 0 ≠ 0)
    (v : ℝ) (hv : 0 < v) :
    barProfile cubicSourceResidualFunction order (g 0 0 / g 1 0) v =
      reflected ((2 * order : ℕ) : ℂ)
        (CubicKubota.complexCharacter G * (-1 : ℂ) ^ order / (g 1 0) ^ (2 * order))
        (‖g 1 0‖ ^ 2)
        (zProfile (fun w => cubicSourceResidualFunction (representative j • w)) order
          (-g 1 1 / g 1 0)) v := by
  have hp : 0 < (‖g 1 0‖ ^ 2 * v)⁻¹ := by positivity
  rw [barProfile_positive _ _ _ _ hv, reflected, zProfile_positive _ _ _ _ hp]
  rw [cubicSourceResidualFunction_finite_all_reflection order G j g hfactor hc v hv,
    order_prefactor]
  simp only [one_div, mul_assoc, Nat.cast_mul, Nat.cast_ofNat, neg_mul]

theorem conjugate_reflection (order : ℕ) (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j) (hc : g 1 0 ≠ 0)
    (v : ℝ) (hv : 0 < v) :
    barProfile cubicSourceConjugateFunction order (g 0 0 / g 1 0) v =
      reflected ((2 * order : ℕ) : ℂ)
        (star (CubicKubota.complexCharacter G) * (-1 : ℂ) ^ order / (g 1 0) ^ (2 * order))
        (‖g 1 0‖ ^ 2)
        (zProfile (fun w => cubicSourceConjugateFunction (representative j • w)) order
          (-g 1 1 / g 1 0)) v := by
  have hp : 0 < (‖g 1 0‖ ^ 2 * v)⁻¹ := by positivity
  rw [barProfile_positive _ _ _ _ hv, reflected, zProfile_positive _ _ _ _ hp]
  rw [cubicSourceConjugateFunction_finite_all_reflection order G j g hfactor hc v hv,
    order_prefactor]
  simp only [one_div, mul_assoc, Nat.cast_mul, Nat.cast_ofNat, neg_mul]

theorem source_mellin_entire (n : ℕ) (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j) (hc : g 1 0 ≠ 0) :
    (∀ s : ℂ, MellinConvergent
      (barProfile cubicSourceResidualFunction (n + 1) (g 0 0 / g 1 0)) s) ∧
    Differentiable ℂ (mellin
      (barProfile cubicSourceResidualFunction (n + 1) (g 0 0 / g 1 0))) := by
  have hf := source_profiles_regular n (g 0 0 / g 1 0)
  have hg := finite_source_profiles_regular j n (-g 1 1 / g 1 0)
  exact mellin_entire _ _ _ residualCuspDecayRate
    (residualCuspDecayRate / sourceCuspScale j)
    (by positivity) residualCuspDecayRate_pos
    (div_pos residualCuspDecayRate_pos (sourceCuspScale_pos j))
    _ _ hf.1 hg.2.1 hf.2.2.1 hg.2.2.2 (source_reflection (n + 1) G j g hfactor hc)

theorem conjugate_mellin_entire (n : ℕ) (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j) (hc : g 1 0 ≠ 0) :
    (∀ s : ℂ, MellinConvergent
      (barProfile cubicSourceConjugateFunction (n + 1) (g 0 0 / g 1 0)) s) ∧
    Differentiable ℂ (mellin
      (barProfile cubicSourceConjugateFunction (n + 1) (g 0 0 / g 1 0))) := by
  have hf := conjugate_profiles_regular n (g 0 0 / g 1 0)
  have hg := finite_conjugate_profiles_regular j n (-g 1 1 / g 1 0)
  exact mellin_entire _ _ _ residualCuspDecayRate
    (residualCuspDecayRate / sourceCuspScale j)
    (by positivity) residualCuspDecayRate_pos
    (div_pos residualCuspDecayRate_pos (sourceCuspScale_pos j))
    _ _ hf.1 hg.2.1 hf.2.2.1 hg.2.2.2 (conjugate_reflection (n + 1) G j g hfactor hc)

theorem source_dual_mellin_entire (n : ℕ) (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j) (hc : g 1 0 ≠ 0) :
    (∀ s : ℂ, MellinConvergent
      (zProfile (fun w => cubicSourceResidualFunction (representative j • w)) (n + 1)
        (-g 1 1 / g 1 0)) s) ∧
    Differentiable ℂ (mellin
      (zProfile (fun w => cubicSourceResidualFunction (representative j • w)) (n + 1)
        (-g 1 1 / g 1 0))) := by
  have hf := source_profiles_regular n (g 0 0 / g 1 0)
  have hg := finite_source_profiles_regular j n (-g 1 1 / g 1 0)
  have hA := order_prefactor_ne_zero _ _ (character_ne_zero G) hc (n + 1)
  exact mellin_entire _ _ _ (residualCuspDecayRate / sourceCuspScale j) residualCuspDecayRate
    (by positivity) (div_pos residualCuspDecayRate_pos (sourceCuspScale_pos j)) residualCuspDecayRate_pos
    _ _ hg.2.1 hf.1 hg.2.2.2 hf.2.2.1
    (reflected_nat_reverse (2 * (n + 1)) _ hA _ (by positivity) _ _
      (source_reflection (n + 1) G j g hfactor hc))

theorem conjugate_dual_mellin_entire (n : ℕ) (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j) (hc : g 1 0 ≠ 0) :
    (∀ s : ℂ, MellinConvergent
      (zProfile (fun w => cubicSourceConjugateFunction (representative j • w)) (n + 1)
        (-g 1 1 / g 1 0)) s) ∧
    Differentiable ℂ (mellin
      (zProfile (fun w => cubicSourceConjugateFunction (representative j • w)) (n + 1)
        (-g 1 1 / g 1 0))) := by
  have hf := conjugate_profiles_regular n (g 0 0 / g 1 0)
  have hg := finite_conjugate_profiles_regular j n (-g 1 1 / g 1 0)
  have hA := order_prefactor_ne_zero _ _ (star_ne_zero.mpr (character_ne_zero G)) hc (n + 1)
  exact mellin_entire _ _ _ (residualCuspDecayRate / sourceCuspScale j) residualCuspDecayRate
    (by positivity) (div_pos residualCuspDecayRate_pos (sourceCuspScale_pos j)) residualCuspDecayRate_pos
    _ _ hg.2.1 hf.1 hg.2.2.2 hf.2.2.1
    (reflected_nat_reverse (2 * (n + 1)) _ hA _ (by positivity) _ _
      (conjugate_reflection (n + 1) G j g hfactor hc))

theorem source_mellin_reflection (n : ℕ) (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j) (hc : g 1 0 ≠ 0)
    (s : ℂ) :
    mellin (barProfile cubicSourceResidualFunction (n + 1) (g 0 0 / g 1 0))
        (2 * s + ((n + 1 : ℕ) : ℂ) - 1) =
      (CubicKubota.complexCharacter G * (-1 : ℂ) ^ (n + 1) / (g 1 0) ^ (2 * (n + 1))) *
        (‖g 1 0‖ ^ 2 : ℝ) ^ (((n + 1 : ℕ) : ℂ) + 1 - 2 * s) *
          mellin (zProfile (fun w => cubicSourceResidualFunction (representative j • w))
            (n + 1) (-g 1 1 / g 1 0)) (((n + 1 : ℕ) : ℂ) + 1 - 2 * s) := by
  apply OAI.SevenEighths.Angular.AnalyticFoundation.cusp_mellin_reflection_order_of_identity
    (n + 1) _ _ _ s _ (by positivity)
  intro v hv
  simpa only [reflected, Nat.cast_mul, Nat.cast_ofNat, neg_mul] using
    source_reflection (n + 1) G j g hfactor hc v hv

theorem conjugate_mellin_reflection (n : ℕ) (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j) (hc : g 1 0 ≠ 0)
    (s : ℂ) :
    mellin (barProfile cubicSourceConjugateFunction (n + 1) (g 0 0 / g 1 0))
        (2 * s + ((n + 1 : ℕ) : ℂ) - 1) =
      (star (CubicKubota.complexCharacter G) * (-1 : ℂ) ^ (n + 1) / (g 1 0) ^ (2 * (n + 1))) *
        (‖g 1 0‖ ^ 2 : ℝ) ^ (((n + 1 : ℕ) : ℂ) + 1 - 2 * s) *
          mellin (zProfile (fun w => cubicSourceConjugateFunction (representative j • w))
            (n + 1) (-g 1 1 / g 1 0)) (((n + 1 : ℕ) : ℂ) + 1 - 2 * s) := by
  apply OAI.SevenEighths.Angular.AnalyticFoundation.cusp_mellin_reflection_order_of_identity
    (n + 1) _ _ _ s _ (by positivity)
  intro v hv
  simpa only [reflected, Nat.cast_mul, Nat.cast_ofNat, neg_mul] using
    conjugate_reflection (n + 1) G j g hfactor hc v hv

end OAI.CubicEisenstein.AngularFiniteAllOrderMellin
