import AngularFiberDecoding
import AngularFiberCollection
import AngularCompletedModels
/-! The actual full angular completed sum equals the constructed shifted
fiber at its representative residual ideal, with the exact normalized scale.
Only the finite residue factor is used in the periodic arithmetic coefficients. -/
noncomputable section
open scoped Classical BigOperators ContDiff
namespace OAI.CubicEisenstein.AngularPhysicalFiberIdentity
open SevenEighths.Angular AngularCompletedCoefficient
open ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve
open CanonicalRowCompletion CanonicalRowCompletion.ActualFiber
local notation "Eis" => ActualEisensteinCubic.O
variable (angularOrder : ℕ) (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

local instance collectionUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _

theorem reflectedFiber_four_mul_value
    (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X)
    (hK:0<completedResidualScale K R (maskIdeal q m F))
    (hk:completedResidualScale K R (maskIdeal q m F)/2≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ)) :
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    4*AngularFiberEnergy.fiberValue angularOrder (AngularPhysicalFiberData.reflectedFiber angularOrder q hq m hm rows R F hR hF hrows v K Ψ hΨ)
      W X 1 completedRamifiedStep k=
        AngularCompressedSource.compressedSourceTotal angularOrder q hq m hm rows R F hR hF hrows v Ψ J W X := by
  let : ∀h:Eis⧸Ideal.span {reflectionConductor q},
      Fintype (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue :=
    fun h=>Fintype.ofFinite _
  let d:=AngularPhysicalFiberData.reflectedFiber angularOrder q hq m hm rows R F hR hF hrows v K Ψ hΨ
  let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
  let f:=fun (h:Eis⧸Ideal.span {reflectionConductor q})
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u:Eisˣ) (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) (l:B→Fin 3)=>
      AngularBranchData.value angularOrder (d.branch (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq)
        ⟨h,rho,u⟩,encodeReflectionSix ⟨B,l⟩)) W X 1 completedRamifiedStep k
  let g:=fun (h:Eis⧸Ideal.span {reflectionConductor q}) (u:Eisˣ)
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) (l:B→Fin 3)=>
      AngularCompressedSource.sourceCompressedTerm angularOrder q hq m hm rows R F hR hF hrows v h B J u l W X
  let chosen:=fun (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))=>
      (data q m hm rows R F hF hrows v J).sourceRowResidue
        (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q) (reflectionConductor_ideal q)
        h (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
        (sourcePrimeSet q hq m hm rows R F hR hF hrows v B J)
  let α:=fun h=>sourceFixedCoefficient q hq m hm rows R F hF hrows v Ψ h J
  let shape:=fun h B=>sourceShapeFactor q hq m hm rows R F hR hF hrows v h B J
  let w:=FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q)
  have hbranch:∀h rho u B l,4*f h rho u B l=
      if rho=chosen h B then α h*shape h B*g h u B l else 0 := by
    intro h rho u B l
    exact AngularFiberDecoding.reflectedFiber_encoded_branch_exact angularOrder q hq m hm rows R F hR hF hrows v K Ψ hΨ hbound
      J h rho u B l W lo hi hlo hsupp hW X hX hK hk
  have hvalue:AngularFiberEnergy.fiberValue angularOrder d W X 1 completedRamifiedStep k=
      ∑h,∑rho,∑u,∑B,w B*∑l,f h rho u B l := by
    rw [AngularFiberCollection.reflectedFiber_value angularOrder q hq m hm rows R F hR hF hrows v K Ψ hΨ W X k]
    exact sum_fixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq) _
  change 4*AngularFiberEnergy.fiberValue angularOrder d W X 1 completedRamifiedStep k=_
  rw [hvalue]
  exact finite_selected_branch_collection f g chosen α shape w hbranch

theorem completedT_eq_reflectedFiber_idealValue
    (χ : AngularCharacter) (hk : χ.k = -(angularOrder : ℤ))
    (hχ : CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q)
      (finiteResidueHom χ))
    (K:ℝ) (hshell:∀I∈rows,K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist χ.elementHom.toMonoidHom (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
      (4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar)*
        AngularCompletedModels.idealValue angularOrder (AngularPhysicalFiberData.reflectedFiber angularOrder q hq m hm rows R F hR hF hrows v K (finiteResidueHom χ) (finiteResidueHom_norm_le_one χ)) W X 1 completedRamifiedStep
          (rowResidualPart J.val (maskIdeal q m F)) := by
  let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI=>⟨hrows I hI,(hshell I hI).2⟩) J
  have hs:=residual_shell q m rows R F K (fun I hI=>⟨hrows I hI,hshell I hI⟩) J
  have he:=reflectedFiber_four_mul_value angularOrder q hq m hm rows R F hR hF hrows v K (finiteResidueHom χ) (finiteResidueHom_norm_le_one χ)
    (fun I hI=>(hshell I hI).2) J W lo hi hlo hsupp hW X hX hs.1 hs.2
  rw [AngularCompressedSource.completedT_eq_compressedSourceTotal angularOrder q hq m hm rows R F hR hF hrows v χ hk hχ
    J W lo hi hlo hsupp hW X hX,←he]
  have hid:rowResidualPart J.val (maskIdeal q m F)=k.val:=rfl
  rw [hid,AngularCompletedModels.idealValue_at]
  ring

end OAI.CubicEisenstein.AngularPhysicalFiberIdentity
