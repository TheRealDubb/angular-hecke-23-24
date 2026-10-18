import AngularDualRadialCoefficients
import AngularSmoothedReflection
import AngularSmoothingContour

/-! Actual completed angular sum to the finite reflected physical cusp
kernel series. All reflection, Mellin regularity and coefficient summability
inputs are discharged. The initial derivative scalar is retained. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology ContDiff MatrixGroups

namespace OAI.CubicEisenstein.AngularPhysicalSmoothedReflection

open CompletedGauss SevenEighths.Angular ConcreteTraceCRT
open AngularFiniteProjector AngularCompletedCoefficient AngularProjectedReflection
open AngularHigherProfiles AngularHigherMellin AngularDualRadialCoefficients
open AngularShiftedBesselReflection AngularSmoothedReflection AngularSmoothingContour

local notation "Eis" => ActualEisensteinCubic.O
local instance : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

/-- Exact cancellation of the modulus-height power in the physical scalar. -/
theorem datumMultiplier_height_norm (order : ℕ) (d : SourceCuspDatum) :
    ‖datumMultiplier order d * (d.heightScale : ℂ) ^ order‖ = 1 := by
  have hc : ‖d.matrix 1 0‖ ≠ 0 := norm_ne_zero_iff.mpr d.lower_ne_zero
  rw [norm_mul, datumMultiplier, norm_div, norm_mul, norm_star,
    CubicKubota.norm_levelTwoComplexCharacter, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, norm_pow, norm_pow, Complex.norm_of_nonneg d.heightScale_pos.le]
  simp only [SourceCuspDatum.heightScale, pow_mul]
  field_simp

theorem sourceCusp_scale_ratio (j : Fin 3) :
    thetaBesselScale / sourceCuspRadialScale j = sourceCuspScale j := by
  unfold sourceCuspRadialScale
  field_simp [thetaBesselScale_pos.ne', (sourceCuspScale_pos j).ne']

theorem datum_geometric_prefactor_norm (n : ℕ) (d : SourceCuspDatum) :
    ‖datumMultiplier (n + 1) d * (d.heightScale : ℂ) ^ (n + 1) *
      ((thetaBesselScale / sourceCuspRadialScale d.index : ℝ) : ℂ) ^ (n + 2)‖ =
      sourceCuspScale d.index ^ (n + 2) := by
  rw [norm_mul, datumMultiplier_height_norm, one_mul, norm_pow,
    sourceCusp_scale_ratio, Complex.norm_of_nonneg (sourceCuspScale_pos d.index).le]

/-- After the actual derivative scalar is removed, the scalar norm is
exactly the old cusp-scale factor; no height-scale or order power remains.
This assertion concerns the scalar only, not order-uniform kernel bounds. -/
theorem datum_normalized_scalar_norm (n : ℕ) (d : SourceCuspDatum) :
    ‖((datumMultiplier (n + 1) d * (d.heightScale : ℂ) ^ (n + 1) *
        ((thetaBesselScale / sourceCuspRadialScale d.index : ℝ) : ℂ) ^ (n + 2)) *
        extraScale d.index ^ n) /
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n)‖ =
      sourceCuspScale d.index ^ 2 / ‖thetaDerivativeScalar‖ := by
  have hfreq : thetaFrequencyScale ≠ 0 := norm_pos_iff.mp thetaBesselScale_pos
  have hB : ‖(-2 * Real.pi * Complex.I * thetaFrequencyScale : ℂ)‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) hfreq
  have hT : ‖thetaDerivativeScalar‖ ≠ 0 := norm_ne_zero_iff.mpr thetaDerivativeScalar_ne_zero
  have hS := (sourceCuspScale_pos d.index).ne'
  have he : ‖(-2 * Real.pi * Complex.I * star thetaFrequencyScale : ℂ)‖ =
      ‖(-2 * Real.pi * Complex.I * thetaFrequencyScale : ℂ)‖ := by
    simp only [norm_mul, norm_star]
  have hE : ‖extraScale d.index‖ =
      ‖(-2 * Real.pi * Complex.I * thetaFrequencyScale : ℂ)‖ / sourceCuspScale d.index := by
    rw [extraScale, norm_div, Complex.norm_of_nonneg (sourceCuspScale_pos d.index).le]
  have hden : ‖thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n‖ =
      ‖thetaDerivativeScalar‖ * ‖(-2 * Real.pi * Complex.I * thetaFrequencyScale : ℂ)‖ ^ n := by
    rw [norm_mul, norm_pow, he]
  rw [norm_div, norm_mul, datum_geometric_prefactor_norm, norm_pow,
    hE, hden, div_pow, pow_add]
  field_simp [hB, hT, hS] <;> ring

/-- The actual physical coefficient after exact radial normalization. -/
def dualKernelTerm (n : ℕ) (d : SourceCuspDatum) (V : ℝ → ℂ) (X : ℝ) (h : Eis) : ℂ :=
  (sourceCuspRadialCoefficient d.index d.dualPoint h * extraScale d.index ^ n * alpha h ^ n) *
    AngularReflectionKernel.paperKernel n V
      (27 * thetaBesselScale ^ 2 * sourceCuspRadialScale d.index ^ 2 * X *
        sourceCuspRadialLength h / d.heightScale ^ 2)

def datumSmoothedDual (n : ℕ) (d : SourceCuspDatum) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  (datumMultiplier (n + 1) d * (d.heightScale : ℂ) ^ (n + 1) *
    ((thetaBesselScale / sourceCuspRadialScale d.index : ℝ) : ℂ) ^ (n + 2)) *
      ∑' h : Eis, dualKernelTerm n d V X h

theorem datum_reflection_radial (n : ℕ) (d : SourceCuspDatum) (v : ℝ) (hv : 0 < v) :
    barProfile cubicSourceConjugateFunction (n + 1) d.point v =
      datumMultiplier (n + 1) d * ((v : ℂ) ^ (-2 * ((n : ℂ) + 1)) *
        radialBesselProfile sourceCuspRadialLength
          (dualRadialCoefficient d.index n d.dualPoint) (sourceCuspRadialScale d.index)
          ((d.heightScale * v)⁻¹)) := by
  rw [datum_reflection (n + 1) d v hv, reflected, datumDualProfile_eq_radial n d _
    (inv_pos.mpr (mul_pos d.heightScale_pos hv))]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, neg_mul]

/-- The physical reflected series is absolutely summable. -/
theorem dualKernelTerm_norm_summable (n : ℕ) (d : SourceCuspDatum)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    Summable (fun h : Eis => ‖dualKernelTerm n d V X h‖) := by
  let coeff : Eis → ℂ := fun h =>
    sourceCuspRadialCoefficient d.index d.dualPoint h * extraScale d.index ^ n * alpha h ^ n
  have hcoeff : Summable (fun h : Eis => ‖coeff h‖ * sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
    simpa only [coeff, dualRadialCoefficient_normalized] using
      dualRadialCoefficient_normalized_summable d.index n d.dualPoint
  let scale : ℝ := 27 * thetaBesselScale ^ 2 * sourceCuspRadialScale d.index ^ 2 * X / d.heightScale ^ 2
  have hscale : 0 < scale := by
    have hq := thetaBesselScale_pos
    have hd := sourceCuspRadialScale_pos d.index
    have hQ := d.heightScale_pos
    dsimp only [scale]
    positivity
  apply (paperKernel_weighted_norm_summable n sourceCuspRadialLength sourceCuspRadialLength_pos
    coeff hcoeff V a b ha hVs hV scale hscale).congr
  intro h
  have he : scale * sourceCuspRadialLength h =
      27 * thetaBesselScale ^ 2 * sourceCuspRadialScale d.index ^ 2 * X *
        sourceCuspRadialLength h / d.heightScale ^ 2 := by dsimp [scale]; ring
  simp only [he, coeff, dualKernelTerm]

theorem datum_smoothing_integrable (n : ℕ) (d : SourceCuspDatum)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    Integrable (fun t : ℝ => smoothingIntegrand n
      (barProfile cubicSourceConjugateFunction (n + 1) d.point) thetaBesselScale V X
        ((-1 : ℂ) + t * Complex.I)) := by
  exact reflected_smoothing_integrable n
    (barProfile cubicSourceConjugateFunction (n + 1) d.point)
    sourceCuspRadialLength sourceCuspRadialLength_pos
    (dualRadialCoefficient d.index n d.dualPoint) thetaBesselScale
    (sourceCuspRadialScale d.index) d.heightScale thetaBesselScale_pos
    (sourceCuspRadialScale_pos d.index) d.heightScale_pos (datumMultiplier (n + 1) d)
    (datum_reflection_radial n d) (dualRadialCoefficient_weighted_summable d.index n d.dualPoint)
    V a b ha hVs hV X hX

/-- Actual cusp integral to its physical kernel series; no reflection,
regularity or summability premise is supplied by the caller. -/
theorem datum_smoothing_integral (n : ℕ) (d : SourceCuspDatum)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, smoothingIntegrand n
      (barProfile cubicSourceConjugateFunction (n + 1) d.point) thetaBesselScale V X
        ((-1 : ℂ) + t * Complex.I) = datumSmoothedDual n d V X := by
  have hi := reflected_smoothing_integral n
    (barProfile cubicSourceConjugateFunction (n + 1) d.point)
    sourceCuspRadialLength sourceCuspRadialLength_pos
    (dualRadialCoefficient d.index n d.dualPoint) thetaBesselScale
    (sourceCuspRadialScale d.index) d.heightScale thetaBesselScale_pos
    (sourceCuspRadialScale_pos d.index) d.heightScale_pos (datumMultiplier (n + 1) d)
    (datum_reflection_radial n d) (dualRadialCoefficient_weighted_summable d.index n d.dualPoint)
    V a b ha hVs hV X hX
  simpa only [dualRadialCoefficient_normalized, datumSmoothedDual, dualKernelTerm] using hi

theorem finiteProjector_smoothingIntegrand_sum (χ : AngularCharacter) (n : ℕ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (V : ℝ → ℂ) (X : ℝ) (s : ℂ) :
    smoothingIntegrand n (finiteProjector χ n c hc) thetaBesselScale V X s =
      ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient (finiteResidueHom χ) c) h *
          smoothingIntegrand n (barProfile cubicSourceConjugateFunction (n + 1)
            (finiteTwistCusp c hc h).point) thetaBesselScale V X s := by
  unfold smoothingIntegrand continuedDirichlet
  rw [finiteProjector_mellin_sum]
  simp only [Finset.mul_sum, finiteTwistCusp_point]
  apply Finset.sum_congr rfl
  intro h hh
  ring

/-- The actual finite projector is integrable on the left line. -/
theorem finiteProjector_left_integrable (χ : AngularCharacter) (n : ℕ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    Integrable (fun t : ℝ => smoothingIntegrand n (finiteProjector χ n c hc)
      thetaBesselScale V X ((-1 : ℂ) + t * Complex.I)) := by
  simp_rw [finiteProjector_smoothingIntegrand_sum]
  apply integrable_finsetSum
  intro h hh
  exact (datum_smoothing_integrable n (finiteTwistCusp c hc h) V a b ha hVs hV X hX).const_mul _

theorem finiteProjector_smoothing_integral (χ : AngularCharacter) (n : ℕ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      smoothingIntegrand n (finiteProjector χ n c hc) thetaBesselScale V X
        ((-1 : ℂ) + t * Complex.I) =
      ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient (finiteResidueHom χ) c) h *
          datumSmoothedDual n (finiteTwistCusp c hc h) V X := by
  simp_rw [finiteProjector_smoothingIntegrand_sum]
  rw [integral_finsetSum Finset.univ (fun h hh =>
    (datum_smoothing_integrable n (finiteTwistCusp c hc h) V a b ha hVs hV X hX).const_mul _),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [integral_const_mul]
  calc
    _ = finiteAdditiveFourierCoeff (quotientTrace c hc)
        (fixedThetaQuotient (finiteResidueHom χ) c) h *
        ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, smoothingIntegrand n
          (barProfile cubicSourceConjugateFunction (n + 1) (finiteTwistCusp c hc h).point)
          thetaBesselScale V X ((-1 : ℂ) + t * Complex.I)) := by ring
    _ = _ := by rw [datum_smoothing_integral n _ V a b ha hVs hV X hX]

/-- Full physical smoothed reflection of the actual completed angular sum.
The initial scalar, every finite Fourier weight, the matrix-dependent height
and cusp scale, and the normalized angular-phase coefficient are retained. -/
theorem completedT_reflection (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * χ.modulus)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
      completedT χ.elementHom.toMonoidHom W X =
        ∑ h : Eis ⧸ Ideal.span {c},
          finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient (finiteResidueHom χ) c) h *
            datumSmoothedDual n (finiteTwistCusp c hc h) (Vstar W) X := by
  have hVs := Vstar_support W a b hWs
  have hV := Vstar_contDiff W a b ha hWs hW
  have hleft : Integrable (fun t : ℝ => smoothingIntegrand n (finiteProjector χ n c hc)
      thetaBesselScale (Vstar W) X (((-1 : ℝ) : ℂ) + t * Complex.I)) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_one] using
      finiteProjector_left_integrable χ n c hc (Vstar W) a b ha hVs hV X hX
  rw [finiteProjector_mellin_shift χ n hk c hc hcQ W a b ha hWs hW X hX
    (-1) (by norm_num) hleft]
  simpa only [Complex.ofReal_neg, Complex.ofReal_one] using
    finiteProjector_smoothing_integral χ n c hc (Vstar W) a b ha hVs hV X hX

end OAI.CubicEisenstein.AngularPhysicalSmoothedReflection
