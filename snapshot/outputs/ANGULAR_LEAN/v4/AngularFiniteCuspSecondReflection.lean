import AngularScaledBesselRegularity
import OAI.NumberTheory.DirichletL.Eisenstein.SourceCuspKernels

/-! Second reflection at the three actual finite cubic cusp representatives.
Their translated source is identified with the pinned scaled Bessel expansion
on the open positive-height domain; regularity is transferred locally. -/

noncomputable section
open scoped Classical Topology MatrixGroups
open Filter Set

namespace OAI.CubicEisenstein.AngularFiniteCuspSecondReflection

open AngularCuspChainRule AngularBesselHorizontalRegularity AngularBesselDerivatives
open AngularCuspSecondReflection AngularScaledBesselRegularity
open EisensteinEmbedding EisensteinCuspModThree

def representative (j : Fin 3) : SL(2,ℂ) := integralComplexMatrix (cuspRepresentative j)

def finiteSplit (j : Fin 3) (p : ℂ × ℝ) : ℂ :=
  cubicSourceResidualFunction (representative j • cuspCoordinateLift (p.2, p.1))

theorem finiteSplit_eq_scaledSplit (j : Fin 3) (p : ℂ × ℝ) (hp : 0 < p.2) :
    finiteSplit j p = scaledSplit (sourceCuspCoefficients j) (sourceCuspBesselConstant j)
      (sourceCuspScale j) p := by
  rw [finiteSplit, representative, cuspCoordinateLift_positive _ _ hp,
    sourceCusp_bessel_expansion]
  rw [scaledSplit, scale_apply, splitFull,
    cuspCoordinateLift_positive _ _ (div_pos hp (sourceCuspScale_pos j))]

theorem finiteSplit_eventuallyEq_scaledSplit (j : Fin 3) (p : ℂ × ℝ) (hp : 0 < p.2) :
    finiteSplit j =ᶠ[𝓝 p] scaledSplit (sourceCuspCoefficients j) (sourceCuspBesselConstant j)
      (sourceCuspScale j) := by
  filter_upwards [continuousAt_snd.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact finiteSplit_eq_scaledSplit j q hq

/-- Every second-composition regularity input is proved for the actual
translated source at each of the three finite cusp representatives. -/
theorem finiteSplit_regular (j : Fin 3) (p : ℂ × ℝ) (hp : 0 < p.2) :
    DifferentiableAt ℝ (finiteSplit j) p ∧
    ContDiffAt ℝ 1 (partialZ (finiteSplit j)) p ∧
    ContDiffAt ℝ 1 (partialBar (finiteSplit j)) p ∧
    ContinuousAt (partialV (finiteSplit j)) p := by
  have hr := scaledSplit_regular (sourceCuspCoefficients j) (sourceCuspBesselConstant j)
    (sourceCuspScale j) (sourceCuspScale_pos j) p hp
  have he := finiteSplit_eventuallyEq_scaledSplit j p hp
  have hd := he.fderiv (𝕜 := ℝ)
  refine ⟨hr.1.congr_of_eventuallyEq he, ?_, ?_, ?_⟩
  · apply hr.2.1.congr_of_eventuallyEq
    filter_upwards [hd] with q hq
    simp only [partialZ, hq]
  · apply hr.2.2.1.congr_of_eventuallyEq
    filter_upwards [hd] with q hq
    simp only [partialBar, hq]
  · apply hr.2.2.2.congr_of_eventuallyEq
    filter_upwards [hd] with q hq
    simp only [partialV, hq]

theorem conjugate_finiteSplit_regular (j : Fin 3) (p : ℂ × ℝ) (hp : 0 < p.2) :
    DifferentiableAt ℝ (fun q => star (finiteSplit j q)) p ∧
    ContDiffAt ℝ 1 (partialZ (fun q => star (finiteSplit j q))) p ∧
    ContDiffAt ℝ 1 (partialBar (fun q => star (finiteSplit j q))) p ∧
    ContinuousAt (partialV (fun q => star (finiteSplit j q))) p := by
  have hr := finiteSplit_regular j p hp
  have hZ : partialZ (fun q => star (finiteSplit j q)) =
      fun q => star (partialBar (finiteSplit j) q) := by
    funext q; exact partialZ_star _ q
  have hB : partialBar (fun q => star (finiteSplit j q)) =
      fun q => star (partialZ (finiteSplit j) q) := by
    funext q; exact partialBar_star _ q
  have hV : partialV (fun q => star (finiteSplit j q)) =
      fun q => star (partialV (finiteSplit j) q) := by
    funext q; exact partialV_star _ q
  refine ⟨hr.1.star, ?_, ?_, ?_⟩
  · rw [hZ]
    convert! Complex.conjCLE.contDiff.contDiffAt.comp p hr.2.2.1 using 1
  · rw [hB]
    convert! Complex.conjCLE.contDiff.contDiffAt.comp p hr.2.1 using 1
  · rw [hV]; exact hr.2.2.2.star

/-- Actual source reflection for a level-three factor followed by any of the
three pinned finite cusp representatives. No analytic regularity input remains. -/
theorem cubicSourceResidualFunction_finite_second_reflection (G : CubicKubota.levelThree)
    (j : Fin 3) (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j)
    (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    iteratedBar 2 (fun z => cubicSourceResidualFunction (upperPoint z v hv)) (g 0 0 / g 1 0) =
      CubicKubota.complexCharacter G * (-1 / ((g 1 0) ^ 2 * (v : ℂ) ^ 2)) ^ 2 *
        iteratedZ 2 (fun z => cubicSourceResidualFunction
          (representative j • upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity)))
          (-g 1 1 / g 1 0) := by
  have hp : 0 < 1 / (‖g 1 0‖ ^ 2 * v) := by positivity
  have hr := finiteSplit_regular j (-g 1 1 / g 1 0, 1 / (‖g 1 0‖ ^ 2 * v)) hp
  refine cuspSecondDerivative_of_transform cubicSourceResidualFunction g (representative j)
    (CubicKubota.complexCharacter G) ?_ hc v hv ?_ ?_ ?_ ?_
  · intro w
    rw [hfactor, mul_smul, cubicSourceResidualFunction_levelThree]
  · intro p hp
    convert! (finiteSplit_regular j p hp).1 using 1
  · convert! hr.2.1.differentiableAt (by norm_num) using 1
  · convert! hr.2.2.1.continuousAt using 1
  · convert! hr.2.2.2 using 1

/-- The conjugate source has the conjugate character multiplier and the same
holomorphic inverse-cusp derivative coefficient. -/
theorem cubicSourceConjugateFunction_finite_second_reflection (G : CubicKubota.levelThree)
    (j : Fin 3) (g : SL(2,ℂ)) (hfactor : g = complexMatrix G * representative j)
    (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    iteratedBar 2 (fun z => cubicSourceConjugateFunction (upperPoint z v hv)) (g 0 0 / g 1 0) =
      star (CubicKubota.complexCharacter G) * (-1 / ((g 1 0) ^ 2 * (v : ℂ) ^ 2)) ^ 2 *
        iteratedZ 2 (fun z => cubicSourceConjugateFunction
          (representative j • upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity)))
          (-g 1 1 / g 1 0) := by
  have hp : 0 < 1 / (‖g 1 0‖ ^ 2 * v) := by positivity
  have hr := conjugate_finiteSplit_regular j
    (-g 1 1 / g 1 0, 1 / (‖g 1 0‖ ^ 2 * v)) hp
  refine cuspSecondDerivative_of_transform cubicSourceConjugateFunction g (representative j)
    (star (CubicKubota.complexCharacter G)) ?_ hc v hv ?_ ?_ ?_ ?_
  · intro w
    rw [hfactor, mul_smul, cubicSourceConjugateFunction_levelThree]
  · intro p hp
    convert! (conjugate_finiteSplit_regular j p hp).1 using 1
  · convert! hr.2.1.differentiableAt (by norm_num) using 1
  · convert! hr.2.2.1.continuousAt using 1
  · convert! hr.2.2.2 using 1

end OAI.CubicEisenstein.AngularFiniteCuspSecondReflection
