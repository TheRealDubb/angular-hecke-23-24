import AngularFixedStratum
import OAI.NumberTheory.DirichletL.Eisenstein.FixedFrequencyExpansion

/-! The actual constructed conductor strata, with angular reflection and
the original local bracket product. No replacement Gauss identity is assumed. -/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators Topology ContDiff MatrixGroups Matrix

namespace OAI.CubicEisenstein.AngularControlledStratum

open SevenEighths.Angular ActualEisensteinCubic ConcreteTraceCRT
open CompletedGauss CompletedDyadic CubicKubota CubicJacobiGlobal
open ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets
open AngularPhysicalSmoothedReflection AngularCuspPhase AngularFixedStratum
open ControlledStratumArithmetic

local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

def angularSmoothedValue (n : ℕ) (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,fourierWeight hp hg j v*
    (datumSmoothedDual n (D.datum hN hr hbase s hp hc0 v) (Vstar W) X /
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n))

def angularReflectedValue (n : ℕ) (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  (thetaDerivativeScalar⁻¹ * stratumAngularPhase s (c0*∏i,p i)^n) *
  (fixedRadialCoefficientScalar*s.stratumShapeFactor (c0*∏i,p i)*
    ∑'t:ThetaFullIndex,
      (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
        ((ramifiedScale 1 completedRamifiedStep t.2.1*
          Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      (alpha (thetaFullFrequency t)^n * AngularReflectionKernel.paperKernel n (Vstar W)
        ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c0*∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3))*
      ((star D.fixedFactor*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U
        (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))*
          D.bracketProduct hp hg j
            (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))))

theorem angular_smoothed_eq_reflected (n : ℕ) (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    angularSmoothedValue n D hN hr hbase s hp hc0 hg j W X=angularReflectedValue n D s hp hc0 hg j W X := by
  let (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  have hc:c0*(∏i,p i)≠0:=mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  have hC:∀v,((D.sourceGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode) 1 0=c0*∏i,p i := by
    intro v
    rw [D.sourceGamma_mul,D.denominator]
  have he:=sum_normalized_integral_phase n s (D.sourceGamma hN hr hbase) _ hc hC
    (fourierWeight hp hg j) W lo hi hlo hsupp hW X hX
  change angularSmoothedValue n D hN hr hbase s hp hc0 hg j W X=_ at he
  rw [he]
  unfold angularReflectedValue
  apply congrArg (fun z : ℂ => (thetaDerivativeScalar⁻¹ * stratumAngularPhase s (c0*∏i,p i)^n) * z)
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*s.stratumShapeFactor (c0*∏i,p i)*z)
  apply tsum_congr
  intro t
  apply congrArg (fun z:ℂ=>
    (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
      ((ramifiedScale 1 completedRamifiedStep t.2.1*
        Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      (alpha (thetaFullFrequency t)^n * AngularReflectionKernel.paperKernel n (Vstar W)
        ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c0*∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3))*z)
  simpa only [multiplierSum,D.sourceGamma_character,D.sourceGamma_mul,map_mul] using
    D.multiplierSum_eq hN hr hbase hp hc0 hcop hg hchar j hj
      (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))


end OAI.CubicEisenstein.AngularControlledStratum
