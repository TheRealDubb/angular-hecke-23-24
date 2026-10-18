import AngularPhysicalReindex

/-! Finite Fourier sums of the physical shifted reflected kernels in a fixed
cusp stratum. The local Gauss multiplier sum is unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators Topology ContDiff MatrixGroups

namespace OAI.CubicEisenstein.AngularFixedStratum

open SevenEighths.Angular CompletedGauss CompletedDyadic CubicKubota
open EisensteinEmbedding ConcreteTraceCRT
open AngularProjectedReflection AngularDualRadialCoefficients
open AngularPhysicalSmoothedReflection AngularCuspPhase AngularPhysicalReindex

local notation "Eis" => ActualEisensteinCubic.O

theorem sum_normalized_common_cusp {ι : Type*} [Fintype ι] (n : ℕ)
    (d : ι → SourceCuspDatum) (w : ι → ℂ) (j : Fin 3) (Q : ℝ) (φ : ℂ)
    (hj : ∀ i, (d i).index = j) (hQ : ∀ i, (d i).heightScale = Q)
    (hφ : ∀ i, datumAngularPhase (d i) = φ)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    (∑ i, w i * (datumSmoothedDual n (d i) (Vstar W) X /
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n))) =
    (thetaDerivativeScalar⁻¹ * φ^n) * (fixedRadialCoefficientScalar *
      ∑' p : ThetaFullIndex,
        ((fixedConjugateCuspArray j p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
          sourceFrequencyAngle (thetaFullFrequency p)) /
          ((ramifiedScale 1 completedRamifiedStep p.2.1 *
            Real.sqrt (Ideal.absNorm p.2.2.1.val : ℝ) * (Ideal.absNorm p.2.2.2.val : ℝ) : ℝ) : ℂ)) *
        (alpha (thetaFullFrequency p)^n * AngularReflectionKernel.paperKernel n (Vstar W)
          (X * sourceCuspRadialLength (thetaFullFrequency p) / (27 * (sourceCuspScale j)^2 * Q^2))) *
        (∑ i, w i * ((d i).multiplier * (Q : ℂ)) *
          ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p) *
            ((d i).dualPoint / (sourceCuspScale j : ℂ))))) := by
  let F : ι → ThetaFullIndex → ℂ := fun i p => w i *
    ((d i).multiplier * ((d i).heightScale : ℂ) * (sourceCuspScale (d i).index : ℂ)^2) *
      physicalKernelTerm n (d i) (Vstar W) X (thetaFullFrequency p)
  have hs (i : ι) : Summable (F i) :=
    (physicalKernelTerm_full_index_norm_summable n (d i) (Vstar W) a b ha
      (Vstar_support W a b hsupp) (Vstar_contDiff W a b ha hsupp hW) X hX).of_norm.mul_left _
  have he (i : ι) :
      w i * (datumSmoothedDual n (d i) (Vstar W) X /
        (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n)) =
      (thetaDerivativeScalar⁻¹ * φ^n) * ∑' p, F i p := by
    rw [datumSmoothedDual_normalized, hφ i]
    simp only [F, tsum_mul_left]
    ring
  simp_rw [he]
  rw [←Finset.mul_sum]
  apply congrArg (fun z : ℂ => (thetaDerivativeScalar⁻¹ * φ^n) * z)
  rw [←Summable.tsum_finsetSum (fun i _ => hs i), ←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hn := (d i).smoothedFullCoefficient_normalization p
  dsimp only [F, physicalKernelTerm]
  calc
    _ = w i * (((d i).multiplier * ((d i).heightScale : ℂ) * (sourceCuspScale (d i).index : ℂ)^2) *
      sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p)) *
      (alpha (thetaFullFrequency p)^n * AngularReflectionKernel.paperKernel n (Vstar W)
        (X * sourceCuspRadialLength (thetaFullFrequency p) /
          (27 * (sourceCuspScale (d i).index)^2 * (d i).heightScale^2))) := by ring
    _ = _ := by rw [hn, hj i, hQ i]; ring

theorem sum_normalized_integral_phase (n : ℕ) {H : SL(2,Eis)} (s : FixedCuspShape H) {ι:Type*} [Fintype ι]
    (g:ι→levelTwo) (c:Eis) (hc:c≠0) (hC:∀v,((g v:SL(2,Eis))*H) 1 0=c)
    (w:ι→ℂ) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑v,w v*(datumSmoothedDual n (s.datum (g v) (by rw [hC v];exact hc)) (Vstar W) X /
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n)))=
      (thetaDerivativeScalar⁻¹ * stratumAngularPhase s c^n) *
      (fixedRadialCoefficientScalar*s.stratumShapeFactor c*
      ∑'p:ThetaFullIndex,
        (s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val /
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        (alpha (thetaFullFrequency p)^n * AngularReflectionKernel.paperKernel n (Vstar W)
          ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3))*
        (∑v,w v*star (levelTwoComplexCharacter (g v))*
          ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
            (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
              eisEmbedding c))) := by
  let d:ι→SourceCuspDatum:=fun v=>s.datum (g v) (by rw [hC v];exact hc)
  have hindex:∀v,(d v).index=s.index:=fun _=>rfl
  have hheight:∀v,(d v).heightScale=(Ideal.absNorm (Ideal.span {c}):ℝ):=by
    intro v
    dsimp only [d]
    rw [s.datum_heightScale,hC v,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  have hphase : ∀ v, datumAngularPhase (d v) = stratumAngularPhase s c := by
    intro v
    exact datumAngularPhase_eq_stratum s (g v) c hc (hC v)
  have he := sum_normalized_common_cusp n d w s.index (Ideal.absNorm (Ideal.span {c}):ℝ)
    (stratumAngularPhase s c) hindex hheight hphase W a b ha hsupp hW X hX
  rw [he]
  apply congrArg (fun z : ℂ => (thetaDerivativeScalar⁻¹ * stratumAngularPhase s c^n) * z)
  conv_rhs => rw [mul_assoc]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*z)
  rw [←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [sourceCusp_full_index_kernel_argument p s.index (Ideal.absNorm (Ideal.span {c}):ℝ) X]
  let A:ℂ:=fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
    sourceFrequencyAngle (thetaFullFrequency p)
  let B:ℂ:=s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val
  let lengthScale:ι→ℂ:=fun v=>w v*((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
    ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*((d v).dualPoint/(sourceCuspScale s.index:ℂ)))
  let R:ι→ℂ:=fun v=>w v*star (levelTwoComplexCharacter (g v))*
    ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
      (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/eisEmbedding c)
  have hs:A*(∑v,lengthScale v)=s.stratumShapeFactor c*B*(∑v,R v):=by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [lengthScale,R]
    calc
      _=w v*(((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
          (A*ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
            ((d v).dualPoint/(sourceCuspScale s.index:ℂ))))):=by ring
      _=w v*((s.stratumShapeFactor c*star (levelTwoComplexCharacter (g v)))*
          (B*ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
            (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/eisEmbedding c))):=by
        rw [s.datum_common_row_factor (g v) c hc (hC v),s.datum_integral_phase (g v) c hc (hC v) p]
      _=_:=by ring
  let D:ℂ:=((ramifiedScale 1 completedRamifiedStep p.2.1*
    Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ)
  let K:ℂ:=(alpha (thetaFullFrequency p)^n * AngularReflectionKernel.paperKernel n (Vstar W)
    ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
      (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3))
  change A/D*K*(∑v,lengthScale v)=s.stratumShapeFactor c*(B/D*K*(∑v,R v))
  calc
    _=(A*(∑v,lengthScale v))/D*K:=by ring
    _=(s.stratumShapeFactor c*B*(∑v,R v))/D*K:=by rw [hs]
    _=_:=by ring

end OAI.CubicEisenstein.AngularFixedStratum
