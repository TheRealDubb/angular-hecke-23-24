import AngularSourceAllOrderReflection
import AngularFiniteCuspSecondReflection

/-! All-order reflection at the three actual finite cubic cusp
representatives. Smoothness is proved from their pinned scaled full Bessel
expansions, whose scales remain 1, 3, 3 and whose constants remain present. -/

noncomputable section
open scoped Classical Topology MatrixGroups ContDiff

namespace OAI.CubicEisenstein.AngularFiniteAllOrderReflection

open AngularBesselDerivatives AngularCuspChainRule AngularBesselHorizontalRegularity
open AngularPhysicalAllOrderCusp AngularSourceAllOrderReflection
open AngularScaledBesselRegularity AngularFiniteCuspSecondReflection
open EisensteinEmbedding EisensteinCuspModThree

theorem scaledSplit_contDiffAt (m : ℕ) (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (s : ℝ) (hs : 0 < s) (p : ℂ × ℝ) (hp : 0 < p.2) :
    ContDiffAt ℝ m (scaledSplit coeff constant s) p := by
  exact (splitFull_contDiffAt m coeff constant (scale s p)
    (scale_height_pos s hs p hp)).comp p (scale s).contDiff.contDiffAt

/-- Genuine real smoothness of every actual finite translated source on
positive heights, obtained locally from its exact physical expansion. -/
theorem finiteSplit_contDiffAt (m : ℕ) (j : Fin 3) (p : ℂ × ℝ) (hp : 0 < p.2) :
    ContDiffAt ℝ m (finiteSplit j) p := by
  exact (scaledSplit_contDiffAt m (sourceCuspCoefficients j) (sourceCuspBesselConstant j)
    (sourceCuspScale j) (sourceCuspScale_pos j) p hp).congr_of_eventuallyEq
      (finiteSplit_eventuallyEq_scaledSplit j p hp)

theorem conjugate_finiteSplit_contDiffAt (m : ℕ) (j : Fin 3)
    (p : ℂ × ℝ) (hp : 0 < p.2) :
    ContDiffAt ℝ m (fun q => star (finiteSplit j q)) p := by
  convert! Complex.conjCLE.contDiff.contDiffAt.comp p (finiteSplit_contDiffAt m j p hp) using 1

/-- Actual residual reflection at any of the three pinned finite cusps.
Every derivative order is included, and no analytic regularity input remains. -/
theorem cubicSourceResidualFunction_finite_all_reflection (order : ℕ)
    (G : CubicKubota.levelThree) (j : Fin 3) (g : SL(2,ℂ))
    (hfactor : g = complexMatrix G * representative j)
    (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    iteratedBar order (fun z => cubicSourceResidualFunction (upperPoint z v hv))
      (g 0 0 / g 1 0) =
      CubicKubota.complexCharacter G * (-1 / ((g 1 0) ^ 2 * (v : ℂ) ^ 2)) ^ order *
        iteratedZ order (fun z => cubicSourceResidualFunction
          (representative j • upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity)))
          (-g 1 1 / g 1 0) := by
  refine AngularSourceAllOrderReflection.cuspDerivative_of_transform order
    cubicSourceResidualFunction g (representative j)
    (CubicKubota.complexCharacter G) ?_ hc v hv ?_
  · intro w
    rw [hfactor, mul_smul, cubicSourceResidualFunction_levelThree]
  · intro m p hp
    convert! finiteSplit_contDiffAt m j p hp using 1

/-- Actual conjugate reflection with conjugated character and unchanged
inverse-cusp derivative factor, using the same physical cusp scales. -/
theorem cubicSourceConjugateFunction_finite_all_reflection (order : ℕ)
    (G : CubicKubota.levelThree) (j : Fin 3) (g : SL(2,ℂ))
    (hfactor : g = complexMatrix G * representative j)
    (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) :
    iteratedBar order (fun z => cubicSourceConjugateFunction (upperPoint z v hv))
      (g 0 0 / g 1 0) =
      star (CubicKubota.complexCharacter G) * (-1 / ((g 1 0) ^ 2 * (v : ℂ) ^ 2)) ^ order *
        iteratedZ order (fun z => cubicSourceConjugateFunction
          (representative j • upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity)))
          (-g 1 1 / g 1 0) := by
  refine AngularSourceAllOrderReflection.cuspDerivative_of_transform order
    cubicSourceConjugateFunction g (representative j)
    (star (CubicKubota.complexCharacter G)) ?_ hc v hv ?_
  · intro w
    rw [hfactor, mul_smul, cubicSourceConjugateFunction_levelThree]
  · intro m p hp
    convert! conjugate_finiteSplit_contDiffAt m j p hp using 1

end OAI.CubicEisenstein.AngularFiniteAllOrderReflection
