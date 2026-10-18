import AngularCompressedSource
import AngularPhysicalFiberBranch
/-! Exact active-label decoding of the actual shifted angular branches.
All selectors, inactive weights and column divisor equalities are retained. -/
noncomputable section
open scoped Classical BigOperators ContDiff
namespace OAI.CubicEisenstein.AngularFiberDecoding
open ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve
open CanonicalRowCompletion CanonicalRowCompletion.ActualFiber
local notation "Eis" => ActualEisensteinCubic.O
variable (angularOrder : ℕ) (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

theorem reflectedFiber_decoded_branch_exact
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
    let B:=reflectionSixSupport e
    let l:=fun b:B=>reflectionSixLabel (e b.val)
    let D:=data q m hm rows R F hF hrows v J
    let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    let ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq):=⟨h,rho,u⟩
    let d:=(AngularPhysicalFiberData.reflectedFiber angularOrder q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,
        e)
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    4*AngularBranchData.value angularOrder d W X 1 completedRamifiedStep k=
      if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
        (reflectionConductor_ideal q) h G A then
        fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
          (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
        G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
        AngularCompressedSource.sourceCompressedTerm angularOrder q hq m hm rows R F hR hF hrows v h B J u l W X
      else 0 := by
  let D:=data q m hm rows R F hF hrows v J
  let A:=activeSet q hq m hm rows R F hR hF hrows v e J
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  let S:=D.activeStratum (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ideal q) h G A
  let Em:=activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J
  let Es:=selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J) (reflectionSixSupport e)
  let labels:=fun b:reflectionSixSupport e=>reflectionSixLabel (e b.val)
  let : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (CanonicalCoefficientClass.fixedBaseConductor q*
      Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ D.movingSupported P.val
  let hp:=fun P:A=>freePrimaryPrime_ne_zero _ _ D.movingSupported P.val
  let hg:=fun P:A=>freePrimaryPrime_good _ _ D.movingSupported P.val
  let j:=fun P:A=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6
  have ht:=AngularPhysicalFiberBranch.reflectedFiber_branch_exact angularOrder q hq m hm rows R F hR hF hrows v K Ψ hΨ hbound J h rho u
    e W lo hi hlo hsupp hW X hX hK hk
  refine ht.trans (congrArg (fun z:ℂ=>if rho=D.sourceRowResidue
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q) (reflectionConductor_ideal q)
    h G A then fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
      G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*z
    else 0) ?_)
  unfold AngularCompressedSource.sourceCompressedTerm
  apply tsum_congr
  intro x
  have hlabel:residualLabelVia Em (FreeReflection.reflectionActiveLabel R (maskIdeal q m F) (freeConductor q) e)=
      residualLabelVia Es labels:=activeModelPrimeEquiv_labels q hq m hm rows R F hR hF hrows v e J
  have hdiv (side:Fin 3):columnDivisor q m R F e side=
      sourceDivisor q m R F (reflectionSixSupport e) labels side:=
    FreeReflection.supportActivePoolEquiv_divisor R F (maskIdeal q m F) (freeConductor q) e side
  have harg:nonzeroDualDilation (columnDivisor q m R F e 1) (columnDivisor q m R F e 2)
      (columnDivisor_ne_zero q m R F e 1) (columnDivisor_ne_zero q m R F e 2) x=
    nonzeroDualDilation (sourceDivisor q m R F (reflectionSixSupport e) labels 1)
      (sourceDivisor q m R F (reflectionSixSupport e) labels 2)
      (sourceDivisor_ne_zero q m R F (reflectionSixSupport e) labels 1)
      (sourceDivisor_ne_zero q m R F (reflectionSixSupport e) labels 2) x := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> apply Subtype.ext <;> dsimp only [nonzeroDualDilation] <;> rw [hdiv]
  exact congrArg₂ (fun label arg =>
    @AngularStratumBranches.stratumBranchTerm _ _ G A (Finset.Subtype.fintype A)
      _ _ angularOrder S _ hp hg j u label W X arg) hlabel harg

theorem reflectedFiber_encoded_branch_exact
    (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u:Eisˣ) (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) (l:B→Fin 3)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X)
    (hK:0<completedResidualScale K R (maskIdeal q m F))
    (hk:completedResidualScale K R (maskIdeal q m F)/2≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ)) :
    let D:=data q m hm rows R F hF hrows v J
    let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    let ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq):=⟨h,rho,u⟩
    let d:=(AngularPhysicalFiberData.reflectedFiber angularOrder q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,
        encodeReflectionSix ⟨B,l⟩)
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    4*AngularBranchData.value angularOrder d W X 1 completedRamifiedStep k=
      if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
        (reflectionConductor_ideal q) h G A then
        fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
          (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
        G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
        AngularCompressedSource.sourceCompressedTerm angularOrder q hq m hm rows R F hR hF hrows v h B J u l W X
      else 0 := by
  let result:(ΣB:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),B→Fin 3) → ℂ := fun x =>
    let D:=data q m hm rows R F hF hrows v J
    let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v x.1 J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
      (reflectionConductor_ideal q) h G A then
      fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
        (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
      G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
      AngularCompressedSource.sourceCompressedTerm angularOrder q hq m hm rows R F hR hF hrows v h x.1 J u x.2 W X
    else 0
  have ht:=reflectedFiber_decoded_branch_exact angularOrder q hq m hm rows R F hR hF hrows v K Ψ hΨ hbound J h rho u
    (encodeReflectionSix ⟨B,l⟩) W lo hi hlo hsupp hW X hX hK hk
  change _=result (decodeReflectionSix (encodeReflectionSix ⟨B,l⟩)) at ht
  rw [decode_encodeReflectionSix] at ht
  change _=result ⟨B,l⟩
  exact ht

end OAI.CubicEisenstein.AngularFiberDecoding
