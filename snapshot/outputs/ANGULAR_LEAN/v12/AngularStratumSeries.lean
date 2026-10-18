import AngularStratumModel

/-! Exact physical reflected series with a separated bounded angular column
array and a modulus-one angular row phase. The fixed residue selector is retained. -/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators Topology ContDiff MatrixGroups

namespace OAI.CubicEisenstein.AngularStratumSeries

open SevenEighths.Angular ActualEisensteinCubic ConcreteTraceCRT
open CompletedGauss CompletedDyadic CubicKubota CubicJacobiGlobal
open LocalReflectionBrackets ShortDraftCusp
open AngularCuspPhase AngularControlledStratum AngularStratumModel

local notation "Eis" => ActualEisensteinCubic.O
variable {c : Eis} {h : Eis ⧸ Ideal.span {c}} (G : FixedFourierGeometry c h)
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N : Eis}

theorem angularReflectedValue_eq_weighted_model_series (n : ℕ) (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) :
    angularReflectedValue n D G.shape hp G.denominator_ne_zero hg j W X=
    (thetaDerivativeScalar⁻¹ * stratumAngularPhase G.shape (G.c0*∏i,p i)^n) *
    (fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
      ∑'t:ThetaFullIndex,
        (D.modelRowPhase G.shape hp hg j t.1 t.2.1*
          ∑e:ι→Fin 3,
            G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U))
              t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
            reflectedBranch (fun i=>Ideal.span {p i}) hg j e
              (primaryGenerator t.2.2.1.val) (primaryGenerator t.2.2.2.val)) /
          ((ramifiedScale 1 completedRamifiedStep t.2.1*
            Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ)*
        (alpha (thetaFullFrequency t)^n * AngularReflectionKernel.paperKernel n (Vstar W)
          ((X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
            (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
            (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3))) := by
  unfold angularReflectedValue
  apply congrArg (fun z : ℂ => (thetaDerivativeScalar⁻¹ * stratumAngularPhase G.shape (G.c0*∏i,p i)^n) * z)
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  apply tsum_congr
  intro t
  rw [fixed_stratum_kernel_scale]
  have he:=G.stratum_model_coefficient D hp hg j t.1 t.2.1 t.2.2.1.val t.2.2.2.val
  have hx:sourceCuspPhaseNumerator G.shape.index (G.shape.upper 0 0) (thetaFullFrequency t)=
      G.dualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val := by
    rw [thetaFullFrequency_eq_fixedCuspArrayIndex]
    rfl
  rw [hx]
  let denominator:ℂ:=((ramifiedScale 1 completedRamifiedStep t.2.1*
    Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ)
  let kernel:ℂ:=(alpha (thetaFullFrequency t)^n * AngularReflectionKernel.paperKernel n (Vstar W)
    ((X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
      (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3))
  change _/denominator*kernel*_=_/denominator*kernel
  calc
    _=(G.shape.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
      (star D.fixedFactor*A4BadPhase G.c0 G.denominator_ne_zero (D.matrix (fun _=>1) 1 1) D.U
        (G.dualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val))*
      D.bracketProduct hp hg j (G.dualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val))/denominator*kernel := by ring
    _=_:=by rw [he]


theorem angularReflectedValue_eq_model_series (n : ℕ)
    (D : ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (j : ι → ℕ) (W : ℝ → ℂ) (X : ℝ) :
    angularReflectedValue n D G.shape hp G.denominator_ne_zero hg j W X =
    (thetaDerivativeScalar⁻¹ * fixedRadialCoefficientScalar *
      G.shape.stratumShapeFactor (G.c0 * ∏ i, p i)) *
      ∑' t : ThetaFullIndex,
        (angularModelRowPhase G n D hp hg j t.1 t.2.1 *
          ∑ e : ι → Fin 3,
            angularArray G n (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1) * D.U))
              t.1 t.2.1 t.2.2.1.val t.2.2.2.val *
            reflectedBranch (fun i => Ideal.span {p i}) hg j e
              (primaryGenerator t.2.2.1.val) (primaryGenerator t.2.2.2.val)) /
          ((ramifiedScale 1 completedRamifiedStep t.2.1 *
            Real.sqrt (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ) : ℝ) : ℂ) *
        AngularReflectionKernel.paperKernel n (Vstar W)
          ((X / (G.levelScale * (Ideal.absNorm (Ideal.span {∏ i, p i}) : ℝ)^2)) *
            (ramifiedScale 1 completedRamifiedStep t.2.1)^3 *
            (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ)^3) := by
  rw [angularReflectedValue_eq_weighted_model_series]
  let B : ThetaFullIndex → ℂ := fun t =>
    (D.modelRowPhase G.shape hp hg j t.1 t.2.1 *
      ∑ e : ι → Fin 3,
        G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1) * D.U))
          t.1 t.2.1 t.2.2.1.val t.2.2.2.val *
        reflectedBranch (fun i => Ideal.span {p i}) hg j e
          (primaryGenerator t.2.2.1.val) (primaryGenerator t.2.2.2.val)) /
      ((ramifiedScale 1 completedRamifiedStep t.2.1 *
        Real.sqrt (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ) : ℝ) : ℂ) *
    (alpha (thetaFullFrequency t)^n * AngularReflectionKernel.paperKernel n (Vstar W)
      ((X / (G.levelScale * (Ideal.absNorm (Ideal.span {∏ i, p i}) : ℝ)^2)) *
        (ramifiedScale 1 completedRamifiedStep t.2.1)^3 *
        (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ)^3))
  change (thetaDerivativeScalar⁻¹ * stratumAngularPhase G.shape (G.c0 * ∏ i, p i)^n) *
    (fixedRadialCoefficientScalar * G.shape.stratumShapeFactor (G.c0 * ∏ i, p i) * ∑' t, B t) = _
  calc
    _ = (thetaDerivativeScalar⁻¹ * fixedRadialCoefficientScalar *
        G.shape.stratumShapeFactor (G.c0 * ∏ i, p i)) *
        ∑' t, stratumAngularPhase G.shape (G.c0 * ∏ i, p i)^n * B t := by
          rw [tsum_mul_left]
          ring
    _ = _ := by
      apply congrArg (fun z : ℂ => (thetaDerivativeScalar⁻¹ * fixedRadialCoefficientScalar *
        G.shape.stratumShapeFactor (G.c0 * ∏ i, p i)) * z)
      apply tsum_congr
      intro t
      simp only [B, angularModelRowPhase, angularArray,
        ←thetaFullFrequency_eq_fixedCuspArrayIndex t, ←mul_assoc, ←Finset.mul_sum]
      ring

end OAI.CubicEisenstein.AngularStratumSeries
