import AngularCuspPhase

/-! The actual completed angular sum with arbitrary physical cusp data, and
its exact absolutely convergent full-frequency reindexing. -/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators Topology ContDiff MatrixGroups

namespace OAI.CubicEisenstein.AngularPhysicalReindex

open SevenEighths.Angular CompletedGauss ConcreteTraceCRT
open AngularFiniteProjector AngularCompletedCoefficient AngularProjectedReflection
open AngularHigherProfiles AngularDualRadialCoefficients AngularPhysicalSmoothedReflection
open AngularCuspPhase

local notation "Eis" => ActualEisensteinCubic.O
local instance : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

def physicalKernelTerm (n : ℕ) (d : SourceCuspDatum) (V : ℝ → ℂ) (X : ℝ) (h : Eis) : ℂ :=
  sourceCuspRadialCoefficient d.index d.dualPoint h * alpha h^n *
    AngularReflectionKernel.paperKernel n V
      (X * sourceCuspRadialLength h / (27 * (sourceCuspScale d.index)^2 * d.heightScale^2))

theorem dualKernelTerm_eq (n : ℕ) (d : SourceCuspDatum) (V : ℝ → ℂ) (X : ℝ) (h : Eis) :
    dualKernelTerm n d V X h = extraScale d.index^n * physicalKernelTerm n d V X h := by
  unfold dualKernelTerm physicalKernelTerm
  rw [sourceCuspKernel_argument]
  ring

theorem physicalKernelTerm_norm_summable (n : ℕ) (d : SourceCuspDatum)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    Summable (fun h : Eis => ‖physicalKernelTerm n d V X h‖) := by
  have hs := dualKernelTerm_norm_summable n d V a b ha hVs hV X hX
  simp_rw [dualKernelTerm_eq, norm_mul] at hs
  have hE : extraScale d.index ≠ 0 := by
    unfold extraScale
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
        (norm_pos_iff.mp thetaBesselScale_pos))
      (Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos d.index).ne')
  exact (summable_mul_left_iff (norm_ne_zero_iff.mpr (pow_ne_zero n hE))).mp hs

theorem physicalKernelTerm_tsum_full_index (n : ℕ) (d : SourceCuspDatum)
    (V : ℝ → ℂ) (X : ℝ) :
    (∑' h : Eis, physicalKernelTerm n d V X h) =
      ∑' p : ThetaFullIndex, physicalKernelTerm n d V X (thetaFullFrequency p) := by
  have he := sourceCuspRadialCoefficient_tsum_full_index d.index d.dualPoint
    (fun h => alpha h^n * AngularReflectionKernel.paperKernel n V
      (X * sourceCuspRadialLength h / (27 * (sourceCuspScale d.index)^2 * d.heightScale^2)))
  simpa only [physicalKernelTerm, mul_assoc, mul_comm, mul_left_comm] using he

theorem physicalKernelTerm_full_index_norm_summable (n : ℕ) (d : SourceCuspDatum)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    Summable (fun p : ThetaFullIndex => ‖physicalKernelTerm n d V X (thetaFullFrequency p)‖) :=
  (physicalKernelTerm_norm_summable n d V a b ha hVs hV X hX).comp_injective
    thetaFullFrequency_injective

theorem datumSmoothedDual_normalized (n : ℕ) (d : SourceCuspDatum)
    (V : ℝ → ℂ) (X : ℝ) :
    datumSmoothedDual n d V X /
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n) =
    (d.multiplier * (d.heightScale : ℂ) * (sourceCuspScale d.index : ℂ)^2 /
      thetaDerivativeScalar) * datumAngularPhase d^n *
        ∑' p : ThetaFullIndex, physicalKernelTerm n d V X (thetaFullFrequency p) := by
  unfold datumSmoothedDual
  simp_rw [dualKernelTerm_eq]
  rw [tsum_mul_left]
  calc
    _ = ((datumMultiplier (n + 1) d * (d.heightScale : ℂ)^(n + 1) *
        ((thetaBesselScale / sourceCuspRadialScale d.index : ℝ) : ℂ)^(n + 2)) *
          extraScale d.index^n) /
        (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n) *
          ∑' h : Eis, physicalKernelTerm n d V X h := by ring
    _ = _ := by rw [datum_normalized_scalar_split, physicalKernelTerm_tsum_full_index]

theorem datumSmoothedDual_eq_of_point (n : ℕ) (d e : SourceCuspDatum)
    (he : d.point = e.point) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    datumSmoothedDual n d V X = datumSmoothedDual n e V X := by
  rw [←datum_smoothing_integral n d V a b ha hVs hV X hX,
    ←datum_smoothing_integral n e V a b ha hVs hV X hX, he]

/-- Any actual cusp representatives at the Fourier translation points may
be used, including the controlled-stratum representatives in OAI-003. -/
theorem completedT_reflection_data (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * χ.modulus)
    (d : (Eis ⧸ Ideal.span {c}) → SourceCuspDatum)
    (hd : ∀ h, (d h).point = thetaFourierTranslation c h)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n) *
      completedT χ.elementHom.toMonoidHom W X =
        ∑ h : Eis ⧸ Ideal.span {c},
          finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient (finiteResidueHom χ) c) h *
            datumSmoothedDual n (d h) (Vstar W) X := by
  rw [completedT_reflection χ n hk c hc hcQ W a b ha hWs hW X hX]
  apply Finset.sum_congr rfl
  intro h hh
  rw [datumSmoothedDual_eq_of_point n (finiteTwistCusp c hc h) (d h)
    (by rw [finiteTwistCusp_point, hd]) (Vstar W) a b ha
      (Vstar_support W a b hWs) (Vstar_contDiff W a b ha hWs hW) X hX]

/-- Actual completed angular sum, with the initial scalar removed and exact
full-frequency reindexing. No periodicity premise is imposed on the full
angular character. The finite residue factor alone occurs in the weights. -/
theorem completedT_full_index (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * χ.modulus)
    (d : (Eis ⧸ Ideal.span {c}) → SourceCuspDatum)
    (hd : ∀ h, (d h).point = thetaFourierTranslation c h)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    completedT χ.elementHom.toMonoidHom W X =
      ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient (finiteResidueHom χ) c) h *
        (((d h).multiplier * ((d h).heightScale : ℂ) * (sourceCuspScale (d h).index : ℂ)^2 /
          thetaDerivativeScalar) * datumAngularPhase (d h)^n *
            ∑' p : ThetaFullIndex, physicalKernelTerm n (d h) (Vstar W) X (thetaFullFrequency p)) := by
  have hT : thetaDerivativeScalar *
      (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n ≠ 0 :=
    mul_ne_zero thetaDerivativeScalar_ne_zero (pow_ne_zero n
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
        (star_ne_zero.mpr (norm_pos_iff.mp thetaBesselScale_pos))))
  have he := completedT_reflection_data χ n hk c hc hcQ d hd W a b ha hWs hW X hX
  have he' := congrArg (fun z : ℂ => z /
    (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n)) he
  rw [mul_div_cancel_left₀ _ hT, Finset.sum_div] at he'
  rw [he']
  apply Finset.sum_congr rfl
  intro h hh
  rw [mul_div_assoc, datumSmoothedDual_normalized]

end OAI.CubicEisenstein.AngularPhysicalReindex
