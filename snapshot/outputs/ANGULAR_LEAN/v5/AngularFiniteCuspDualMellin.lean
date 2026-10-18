import AngularFiniteCuspSecondMellin

/-! Explicit convergence on the dual finite-cusp side. Inverting the nonzero
physical reflection multiplier gives the reverse positive-height identity,
so the Mellin integral of the actual translated Z-profile also converges for
every complex parameter and defines an entire function. -/

noncomputable section
open Filter Asymptotics MeasureTheory Set
open scoped Classical Topology MatrixGroups

namespace OAI.CubicEisenstein.AngularFiniteCuspDualMellin

open AngularHigherProfiles AngularHigherMellin AngularFiniteCuspSecondReflection
open AngularSourceSecondMellin AngularFiniteCuspSecondMellin EisensteinEmbedding

theorem cpow_neg_four (z : ℂ) : z ^ (-4 : ℂ) = (z ^ 4)⁻¹ := by
  rw [show (-4 : ℂ) = -(4 : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_ofNat]

theorem reflected_four_reverse (A : ℂ) (hA : A ≠ 0) (Q : ℝ) (hQ : 0 < Q)
    (f g : ℝ → ℂ) (hfg : ∀ v : ℝ, 0 < v → f v = reflected 4 A Q g v)
    (v : ℝ) (hv : 0 < v) :
    g v = reflected 4 (A⁻¹ / (Q : ℂ) ^ 4) Q f v := by
  have hQc : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have hvc : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hinv : (Q * (Q * v)⁻¹)⁻¹ = v := by field_simp
  have he := hfg (Q * v)⁻¹ (inv_pos.mpr (mul_pos hQ hv))
  rw [reflected, hinv] at he
  rw [reflected, he]
  simp only [cpow_neg_four, Complex.ofReal_inv, Complex.ofReal_mul]
  field_simp

theorem character_ne_zero (G : CubicKubota.levelThree) : CubicKubota.complexCharacter G ≠ 0 := by
  intro h
  have hn := CubicKubota.norm_complexCharacter G
  rw [h, norm_zero] at hn
  norm_num at hn

/-- Actual translated residual Z-profile at the reflected center. -/
theorem source_dual_second_mellin_entire (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j) (hc : g 1 0 ≠ 0) :
    (∀ s : ℂ, MellinConvergent
      (zProfile (fun w => cubicSourceResidualFunction (representative j • w)) 2
        (-g 1 1 / g 1 0)) s) ∧
    Differentiable ℂ (mellin
      (zProfile (fun w => cubicSourceResidualFunction (representative j • w)) 2
        (-g 1 1 / g 1 0))) := by
  have hf := source_profiles_regular 1 (g 0 0 / g 1 0)
  have hg := finite_source_profiles_regular j 1 (-g 1 1 / g 1 0)
  have hA : CubicKubota.complexCharacter G / (g 1 0) ^ 4 ≠ 0 :=
    div_ne_zero (character_ne_zero G) (pow_ne_zero 4 hc)
  exact mellin_entire 4 _ _ (residualCuspDecayRate / sourceCuspScale j) residualCuspDecayRate
    (by positivity) (div_pos residualCuspDecayRate_pos (sourceCuspScale_pos j)) residualCuspDecayRate_pos
    _ _ hg.2.1 hf.1 hg.2.2.2 hf.2.2.1
    (reflected_four_reverse _ hA _ (by positivity) _ _
      (AngularFiniteCuspSecondMellin.source_second_reflection G j g hfactor hc))

/-- Actual translated conjugate Z-profile at the reflected center. -/
theorem conjugate_dual_second_mellin_entire (G : CubicKubota.levelThree) (j : Fin 3)
    (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j) (hc : g 1 0 ≠ 0) :
    (∀ s : ℂ, MellinConvergent
      (zProfile (fun w => cubicSourceConjugateFunction (representative j • w)) 2
        (-g 1 1 / g 1 0)) s) ∧
    Differentiable ℂ (mellin
      (zProfile (fun w => cubicSourceConjugateFunction (representative j • w)) 2
        (-g 1 1 / g 1 0))) := by
  have hf := conjugate_profiles_regular 1 (g 0 0 / g 1 0)
  have hg := finite_conjugate_profiles_regular j 1 (-g 1 1 / g 1 0)
  have hA : star (CubicKubota.complexCharacter G) / (g 1 0) ^ 4 ≠ 0 :=
    div_ne_zero (star_ne_zero.mpr (character_ne_zero G)) (pow_ne_zero 4 hc)
  exact mellin_entire 4 _ _ (residualCuspDecayRate / sourceCuspScale j) residualCuspDecayRate
    (by positivity) (div_pos residualCuspDecayRate_pos (sourceCuspScale_pos j)) residualCuspDecayRate_pos
    _ _ hg.2.1 hf.1 hg.2.2.2 hf.2.2.1
    (reflected_four_reverse _ hA _ (by positivity) _ _
      (AngularFiniteCuspSecondMellin.conjugate_second_reflection G j g hfactor hc))

end OAI.CubicEisenstein.AngularFiniteCuspDualMellin
