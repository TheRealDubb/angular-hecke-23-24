import AngularCuspSecondReflection

/-! Real-linear scaling of the physical Bessel source and its first partials.
All regularity assertions are at positive height and use exact derivative
formulas; no regularity of an arbitrary translated source is assumed. -/

noncomputable section
open scoped Classical Topology
open Filter Set

namespace OAI.CubicEisenstein.AngularScaledBesselRegularity

open AngularCuspChainRule AngularBesselHorizontalRegularity

def scale (s : ℝ) : (ℂ × ℝ) →L[ℝ] (ℂ × ℝ) :=
  s⁻¹ • ContinuousLinearMap.id ℝ (ℂ × ℝ)

theorem scale_apply (s : ℝ) (p : ℂ × ℝ) :
    scale s p = (p.1 / (s : ℂ), p.2 / s) := by
  ext <;> simp [scale, Complex.real_smul, div_eq_mul_inv, mul_comm]

theorem scale_height_pos (s : ℝ) (hs : 0 < s) (p : ℂ × ℝ) (hp : 0 < p.2) :
    0 < (scale s p).2 := by rw [scale_apply]; exact div_pos hp hs

def scaledSplit (coeff : SubexponentialBesselCoefficients) (constant : ℂ) (s : ℝ)
    (p : ℂ × ℝ) : ℂ := splitFull coeff constant (scale s p)

theorem scaledSplit_contDiffAt_one (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (s : ℝ) (hs : 0 < s) (p : ℂ × ℝ) (hp : 0 < p.2) :
    ContDiffAt ℝ 1 (scaledSplit coeff constant s) p := by
  exact (splitFull_contDiffAt_one coeff constant _ (scale_height_pos s hs p hp)).comp p
    (scale s).contDiff.contDiffAt

theorem fderiv_scaledSplit (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (s : ℝ) (hs : 0 < s) (p : ℂ × ℝ) (hp : 0 < p.2) :
    fderiv ℝ (scaledSplit coeff constant s) p =
      (fderiv ℝ (splitFull coeff constant) (scale s p)).comp (scale s) := by
  have hh := ((splitFull_contDiffAt_one coeff constant _ (scale_height_pos s hs p hp)).differentiableAt
    (by norm_num)).hasFDerivAt.comp p (scale s).hasFDerivAt
  have he : HasFDerivAt (scaledSplit coeff constant s)
      ((fderiv ℝ (splitFull coeff constant) (scale s p)).comp (scale s)) p := by
    convert! hh using 1
  exact he.fderiv

theorem partialZ_scaledSplit (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (s : ℝ) (hs : 0 < s) (p : ℂ × ℝ) (hp : 0 < p.2) :
    partialZ (scaledSplit coeff constant s) p =
      (s⁻¹ : ℝ) * zCoefficient coeff constant (scale s p) := by
  simp only [partialZ, fderiv_scaledSplit coeff constant s hs p hp,
    ContinuousLinearMap.comp_apply]
  simp only [scale, _root_.smul_apply, ContinuousLinearMap.id_apply,
    map_smul, Complex.real_smul]
  unfold zCoefficient
  ring

theorem partialBar_scaledSplit (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (s : ℝ) (hs : 0 < s) (p : ℂ × ℝ) (hp : 0 < p.2) :
    partialBar (scaledSplit coeff constant s) p =
      (s⁻¹ : ℝ) * barCoefficient coeff constant (scale s p) := by
  simp only [partialBar, fderiv_scaledSplit coeff constant s hs p hp,
    ContinuousLinearMap.comp_apply]
  simp only [scale, _root_.smul_apply, ContinuousLinearMap.id_apply,
    map_smul, Complex.real_smul]
  unfold barCoefficient
  ring

theorem partialV_scaledSplit (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (s : ℝ) (hs : 0 < s) (p : ℂ × ℝ) (hp : 0 < p.2) :
    partialV (scaledSplit coeff constant s) p =
      (s⁻¹ : ℝ) * vCoefficient coeff constant (scale s p) := by
  simp only [partialV, fderiv_scaledSplit coeff constant s hs p hp,
    ContinuousLinearMap.comp_apply]
  simp only [scale, _root_.smul_apply, ContinuousLinearMap.id_apply,
    map_smul, Complex.real_smul, vCoefficient]

/-- The exact positive-height regularity needed for second cusp reflection. -/
theorem scaledSplit_regular (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (s : ℝ) (hs : 0 < s) (p : ℂ × ℝ) (hp : 0 < p.2) :
    DifferentiableAt ℝ (scaledSplit coeff constant s) p ∧
    ContDiffAt ℝ 1 (partialZ (scaledSplit coeff constant s)) p ∧
    ContDiffAt ℝ 1 (partialBar (scaledSplit coeff constant s)) p ∧
    ContinuousAt (partialV (scaledSplit coeff constant s)) p := by
  have hq := scale_height_pos s hs p hp
  have hz := (zCoefficient_contDiffAt_one coeff constant _ hq).comp p
    (scale s).contDiff.contDiffAt
  have hb := (barCoefficient_contDiffAt_one coeff constant _ hq).comp p
    (scale s).contDiff.contDiffAt
  have hv := (vCoefficient_continuousAt coeff constant _ hq).comp
    (f := scale s) (scale s).continuous.continuousAt
  refine ⟨(scaledSplit_contDiffAt_one coeff constant s hs p hp).differentiableAt (by norm_num),
    ?_, ?_, ?_⟩
  · apply (contDiffAt_const.mul hz).congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
    exact partialZ_scaledSplit coeff constant s hs q hq
  · apply (contDiffAt_const.mul hb).congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
    exact partialBar_scaledSplit coeff constant s hs q hq
  · apply (continuousAt_const.mul hv).congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
    exact partialV_scaledSplit coeff constant s hs q hq

end OAI.CubicEisenstein.AngularScaledBesselRegularity
