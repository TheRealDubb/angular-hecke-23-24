import AngularPhysicalFiberData
import AngularBranchPhase
import AngularStratumBranches

/-! Exact membership of each actual angular representative-row branch in the
shifted model. The finite residue selector and fixed column dilations remain
literal; no complete physical fiber energy consequence is assumed. -/
noncomputable section
open scoped Classical BigOperators ContDiff
namespace OAI.CubicEisenstein.AngularPhysicalFiberBranch
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open CanonicalRowCompletion CanonicalRowCompletion.ActualFiber
local notation "Eis" => ActualEisensteinCubic.O
variable (angularOrder : ℕ) (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

theorem reflectedFiber_branch_exact
    (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u:Eisˣ) (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X)
    (hK:0<completedResidualScale K R (maskIdeal q m F))
    (hk:completedResidualScale K R (maskIdeal q m F)/2≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ)) :
    let D:=data q m hm rows R F hF hrows v J
    let A:=activeSet q hq m hm rows R F hR hF hrows v e J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    let S:=D.activeStratum (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
      (reflectionConductor_ideal q) h G A
    let E:=activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J
    letI : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
      fun P=>freePrimaryPrime_maximal _ _ D.movingSupported P.val
    let hp:=fun P:A=>freePrimaryPrime_ne_zero _ _ D.movingSupported P.val
    let hg:=fun P:A=>freePrimaryPrime_good _ _ D.movingSupported P.val
    let j:=fun P:A=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6
    let ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq):=⟨h,rho,u⟩
    let d:=(AngularPhysicalFiberData.reflectedFiber angularOrder q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,e)
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    let dN:=columnDivisor q m R F e 1
    let dB:=columnDivisor q m R F e 2
    let hdN:=columnDivisor_ne_zero q m R F e 1
    let hdB:=columnDivisor_ne_zero q m R F e 2
    4*AngularBranchData.value angularOrder d W X 1 completedRamifiedStep k=
      if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
        (reflectionConductor_ideal q) h G A then
        fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
          (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
        G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
        ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
          @AngularStratumBranches.stratumBranchTerm _ _ G A (Finset.Subtype.fintype A) _ _ angularOrder S _ hp hg j u
            (residualLabelVia E (FreeReflection.reflectionActiveLabel R (maskIdeal q m F) (freeConductor q) e))
            W X (nonzeroDualDilation dN dB hdN hdB x)
      else 0 := by
  let D:=data q m hm rows R F hF hrows v J
  let A:=activeSet q hq m hm rows R F hR hF hrows v e J
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  let S:=D.activeStratum (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ideal q) h G A
  let E:=activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J
  let : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ D.movingSupported P.val
  let hp:=fun P:A=>freePrimaryPrime_ne_zero _ _ D.movingSupported P.val
  let hg:=fun P:A=>freePrimaryPrime_good _ _ D.movingSupported P.val
  let j:=fun P:A=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6
  let ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq):=⟨h,rho,u⟩
  let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
  let scalar:(FreeReflection.FixedBranchIndex (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      R (maskIdeal q m F) (freeConductor q)×ℕ) → RowIndex q m rows R F → ℂ:=fun a J=>AngularPhysicalFiberData.rowScalar angularOrder q hq m hm rows R F hR hF hrows v Ψ a.1 a.2 J
  have hscalar:∀a J,‖scalar a J‖≤1:=fun a J=>AngularPhysicalFiberData.rowScalar_norm angularOrder q hq m hm rows R F hR hF hrows v Ψ hΨ a.1 a.2 J
  let σ:ℕ→idealRange (completedResidualScale K R (maskIdeal q m F))→ℂ:=
    fun n=>extendFiberRowScalar rows R (maskIdeal q m F) K scalar ((ray,e),n)
  have hσ:∀n k,‖σ n k‖≤1:=fun n=>extendFiberRowScalar_norm_le_one rows R (maskIdeal q m F)
    K scalar hscalar ((ray,e),n)
  let d:=FreeReflection.sixPhaseFixedCuspBranch R F (maskIdeal q m F) (freeConductor q) hR
    (maskIdeal_ne_zero q m hm F hF.ne_zero) K (fixedCuspLevelBound (reflectionConductor q))
    G.levelScale G.levelScale_pos (G.levelScale_le (reflectionConductor_ne_zero q hq))
    e G.shape.index u (AngularBranchRealization.angularStaticPhase G angularOrder rho u) (AngularBranchRealization.angularStaticPhase_norm_le_one G angularOrder rho u) σ hσ
  have hb:=AngularPhysicalFiberData.fixedRayFiber_branch angularOrder (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    R F (maskIdeal q m F) (freeConductor q) hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K
    (fun _=>1) (by intro;simp)
    (fun x n=>extendFiberRowScalar rows R (maskIdeal q m F) K scalar (x,n))
    (fun x n=>extendFiberRowScalar_norm_le_one rows R (maskIdeal q m F) K scalar hscalar (x,n)) ray e
  change (AngularPhysicalFiberData.reflectedFiber angularOrder q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
    (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,e)=d at hb
  dsimp only
  rw [hb]
  let dN:=columnDivisor q m R F e 1
  let dB:=columnDivisor q m R F e 2
  let η:=fun n I J=>AngularStratumModel.angularArray G angularOrder rho u n (dN*I) (dB*J)
  let τ:=fun n (l:idealRange (completedResidualScale K R (maskIdeal q m F)))=>
    @AngularStratumModel.angularModelRowPhase _ _ G A (Finset.Subtype.fintype A) _ _ angularOrder S _ hp hg j u n*residualArgumentPhase l.val 1 dN dB
  let weight:=fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
    G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)
  have hraw:AngularBranchData.value angularOrder d W X 1 completedRamifiedStep k=AngularBranchData.rawValue angularOrder d η σ W X 1 completedRamifiedStep k:=by
    exact AngularBranchRealization.sixPhaseFixedCuspBranch_value_eq_geometric_rawValue angularOrder G R F (maskIdeal q m F) (freeConductor q)
      hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K (fixedCuspLevelBound (reflectionConductor q))
      (G.levelScale_le (reflectionConductor_ne_zero q hq)) e rho u σ hσ
      W lo hi hlo hsupp hW X 1 completedRamifiedStep hX (by norm_num) completedRamifiedStep_gt_one hK k hk
  rw [hraw]
  have hσrow (n:ℕ):σ n k=AngularPhysicalFiberData.rowScalar angularOrder q hq m hm rows R F hR hF hrows v Ψ (ray,e) n J:=
    extendFiberRowScalar_at_original rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) scalar ((ray,e),n) J
  by_cases hphase:rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q)
    (reflectionConductor q) (reflectionConductor_ideal q) h G A
  · rw [ite_eq_left hphase]
    have hσmatch (n:ℕ):σ n k=weight*τ n k := by
      rw [hσrow]
      change (if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q)
        (reflectionConductor q) (reflectionConductor_ideal q) h G A then
        AngularRowAmplitudes.sourceRowScalar D (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
          (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) h G A angularOrder Ψ u n*
            residualArgumentPhase k.val 1 dN dB else 0)=_
      rw [ite_eq_left hphase]
      dsimp only [AngularRowAmplitudes.sourceRowScalar,weight,τ]
      change (weight*@AngularStratumModel.angularModelRowPhase _ _ G A (Finset.Subtype.fintype A) _ _ angularOrder S _ hp hg j u n)*residualArgumentPhase k.val 1 dN dB=
        weight*(@AngularStratumModel.angularModelRowPhase _ _ G A (Finset.Subtype.fintype A) _ _ angularOrder S _ hp hg j u n*residualArgumentPhase k.val 1 dN dB)
      exact mul_assoc _ _ _
    rw [AngularBranchPhase.rawValue_congr_phase_at angularOrder d η σ (fun n l=>weight*τ n l) W X 1 completedRamifiedStep k hσmatch,
      AngularBranchPhase.rawValue_mul_phase_at angularOrder d η τ W X 1 completedRamifiedStep k (fun _=>weight)]
    have hterm:=@AngularBranchRealization.stratumBranchTerm_tsum_eq_rawValue_at_row _ _ G A
      (Finset.Subtype.fintype A) _ _ angularOrder S _ hp hg j _ _ _ _ _ d hK k E
      (fun P=>activeModelPrimeEquiv_span q hq m hm rows R F hR hF hrows v e J (Sum.inl P))
      (fun P=>activeModelPrimeEquiv_span q hq m hm rows R F hR hF hrows v e J (Sum.inr P))
      (fun P=>activeModelPrimeEquiv_exponent q hq m hm rows R F hR hF hrows v e J (Sum.inl P))
      (fun P=>activeModelPrimeEquiv_exponent q hq m hm rows R F hR hF hrows v e J (Sum.inr P)) rfl u W X
    have harr:η=fun n I J=>AngularStratumModel.angularArray G angularOrder
        (Ideal.Quotient.mk _ (-(@ControlledStratumArithmetic.matrix A (Finset.Subtype.fintype A) _ _ _ _ _ S (fun _=>1) 1 1)*(@ControlledStratumArithmetic.U A (Finset.Subtype.fintype A) _ _ _ _ _ S))) u n (dN*I) (dB*J):=by
      dsimp only [η]
      rw [hphase]
      rfl
    rw [harr]
    calc
      _=weight*(4*AngularBranchData.rawValue angularOrder d
          (fun n I J=>AngularStratumModel.angularArray G angularOrder (Ideal.Quotient.mk _ (-(@ControlledStratumArithmetic.matrix A (Finset.Subtype.fintype A) _ _ _ _ _ S (fun _=>1) 1 1)*(@ControlledStratumArithmetic.U A (Finset.Subtype.fintype A) _ _ _ _ _ S))) u n (dN*I) (dB*J))
          τ W X 1 completedRamifiedStep k):=by ring
      _=_:=congrArg (fun z:ℂ=>weight*z) hterm.symm
  · rw [ite_eq_right hphase]
    have hσzero (n:ℕ):σ n k=0 := by
      rw [hσrow]
      change (if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q)
        (reflectionConductor q) (reflectionConductor_ideal q) h G A then _ else 0)=0
      rw [ite_eq_right hphase]
    rw [AngularBranchPhase.rawValue_congr_phase_at angularOrder d η σ (fun _ _=>0) W X 1 completedRamifiedStep k hσzero,
      AngularBranchPhase.rawValue_zero_phase angularOrder d η W X 1 completedRamifiedStep k,mul_zero]

end OAI.CubicEisenstein.AngularPhysicalFiberBranch
