import AngularFiberEnergy
import AngularRowAmplitudes
import AngularBranchRealization
import OAI.NumberTheory.DirichletL.RowCompletion.ReflectedFibers

/-! Actual angular fiber records, with the original finite rays, inactive
weights, representative rows and arithmetic support. Their column arrays are
the literal fixed angular arrays. Evaluation uses the shifted kernel. -/
noncomputable section
open scoped Classical BigOperators ContDiff
namespace OAI.CubicEisenstein.AngularPhysicalFiberData
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open CompletedGauss.FreeReflection AngularBranchRealization
local notation "Eis" => ActualEisensteinCubic.O
def fixedRayFiber (angularOrder : ℕ) (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) :
    ReflectedFiberData (fixedReflectionRayCount c hc) (fixedCuspLevelBound c) K I F Q := by
  let R:SixReflectionIndex (fixedReflectionRayCount c hc) I Q Q0→FixedReflectionRay c hc:=
    fun x=>(fixedReflectionRayEquiv c hc).symm x.1
  let G:=fun x=>fixedFourierGeometry c hc (R x).1
  exact sixPhaseFixedCuspFiber (fixedReflectionRayCount c hc) I F Q Q0 hI hQ K
    (fixedCuspLevelBound c) (fun x=>(G x).levelScale)
    (fun x=>(G x).levelScale_pos) (fun x=>(G x).levelScale_le hc)
    (fun x=>(G x).shape.index) (fun x=>(R x).2.2)
    (fun x=>angularStaticPhase (G x) angularOrder (R x).2.1 (R x).2.2)
    (fun x=>angularStaticPhase_norm_le_one (G x) angularOrder (R x).2.1 (R x).2.2)
    (fun x=>rayWeight (R x,x.2)) (fun x=>hray (R x,x.2))
    (fun x=>rowPhase (R x,x.2)) (fun x=>hrow (R x,x.2))

lemma fixedRayFiber_pool (angularOrder : ℕ) (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) :
    (fixedRayFiber angularOrder c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow).pool=pool I Q Q0 := rfl

def fixedRayFiberFromRows (angularOrder : ℕ) (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1) :
    ReflectedFiberData (fixedReflectionRayCount c hc) (fixedCuspLevelBound c) K I F Q :=
  fixedRayFiber angularOrder c hc I F Q Q0 hI hQ K (fun _=>1) (by intro x;simp)
    (fun x m=>extendFiberRowScalar rows I Q K scalar (x,m))
    (fun x m=>extendFiberRowScalar_norm_le_one rows I Q K scalar hscalar (x,m))

lemma fixedRayFiberFromRows_rowPhase (angularOrder : ℕ) (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (J:representativeRowFiber rows I Q) (r:FixedReflectionRay c hc)
    (e:pool I Q Q0→Fin 6) (i:ℕ×ℕ×ℕ) :
    ((fixedRayFiberFromRows angularOrder c hc rows I F Q Q0 hI hQ K scalar hscalar).branch
      (fixedReflectionRayEquiv c hc r,e)).rowPhase i
        (fiberResidualIndex rows I Q K hbad hrows J)=scalar ((r,e),i.1) J := by
  change extendFiberRowScalar rows I Q K scalar
    ((((fixedReflectionRayEquiv c hc).symm (fixedReflectionRayEquiv c hc r)),e),i.1)
    (fiberResidualIndex rows I Q K hbad hrows J)=_
  rw [Equiv.symm_apply_apply]
  exact extendFiberRowScalar_at_original rows I Q K hbad hrows scalar ((r,e),i.1) J

lemma fixedRayFiberFromRows_weight (angularOrder : ℕ) (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1)
    (r:FixedReflectionRay c hc) (e:pool I Q Q0→Fin 6) :
    (fixedRayFiberFromRows angularOrder c hc rows I F Q Q0 hI hQ K scalar hscalar).weight
      (fixedReflectionRayEquiv c hc r,e)=reflectionSixInactiveWeight I F Q Q0 e := by
  change 1*reflectionSixInactiveWeight I F Q Q0 e=_
  exact one_mul _

lemma fixedRayFiber_branch (angularOrder : ℕ) (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (r:FixedReflectionRay c hc) (e:pool I Q Q0→Fin 6) :
    let G:=fixedFourierGeometry c hc r.1
    (fixedRayFiber angularOrder c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow).branch
      (fixedReflectionRayEquiv c hc r,e)=
      sixPhaseFixedCuspBranch I F Q Q0 hI hQ K (fixedCuspLevelBound c) G.levelScale
        G.levelScale_pos (G.levelScale_le hc) e G.shape.index r.2.2
        (angularStaticPhase G angularOrder r.2.1 r.2.2) (angularStaticPhase_norm_le_one G angularOrder r.2.1 r.2.2)
        (rowPhase (r,e)) (hrow (r,e)) := by
  let f : FixedReflectionRay c hc → ReflectedBranchData (fixedCuspLevelBound c) K I F Q := fun t =>
    let G:=fixedFourierGeometry c hc t.1
    sixPhaseFixedCuspBranch I F Q Q0 hI hQ K (fixedCuspLevelBound c) G.levelScale
      G.levelScale_pos (G.levelScale_le hc) e G.shape.index t.2.2
      (angularStaticPhase G angularOrder t.2.1 t.2.2) (angularStaticPhase_norm_le_one G angularOrder t.2.1 t.2.2)
      (rowPhase (t,e)) (hrow (t,e))
  change f ((fixedReflectionRayEquiv c hc).symm ((fixedReflectionRayEquiv c hc) r))=f r
  exact congrArg f ((fixedReflectionRayEquiv c hc).symm_apply_apply r)

section
open CanonicalRowCompletion CanonicalRowCompletion.ActualFiber
variable (angularOrder : ℕ) (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]
noncomputable def rowScalar (Ψ:Eis→*ℂ)
    (x:FreeReflection.FixedBranchIndex (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      R (maskIdeal q m F) (freeConductor q)) (n:ℕ) (J:RowIndex q m rows R F) : ℂ :=
  AngularRowAmplitudes.selectedSourceRowScalar (data q m hm rows R F hF hrows v J)
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) x.1.1
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) x.1.1)
    (activeSet q hq m hm rows R F hR hF hrows v x.2 J) angularOrder Ψ x.1.2.2 n x.1.2.1
    (rowResidualPart J.val (maskIdeal q m F))
    (columnDivisor q m R F x.2 1) (columnDivisor q m R F x.2 2)

lemma rowScalar_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (x:FreeReflection.FixedBranchIndex (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      R (maskIdeal q m F) (freeConductor q)) (n:ℕ) (J:RowIndex q m rows R F) :
    ‖rowScalar angularOrder q hq m hm rows R F hR hF hrows v Ψ x n J‖≤1 := by
  exact AngularRowAmplitudes.selectedSourceRowScalar_norm (data q m hm rows R F hF hrows v J)
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) x.1.1
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) x.1.1)
    (activeSet q hq m hm rows R F hR hF hrows v x.2 J) angularOrder Ψ hΨ x.1.2.2 n x.1.2.1
    (rowResidualPart J.val (maskIdeal q m F))
    (columnDivisor q m R F x.2 1) (columnDivisor q m R F x.2 2)

noncomputable def reflectedFiber (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) :
    ReflectedFiberData (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
      (fixedCuspLevelBound (reflectionConductor q)) K R F (maskIdeal q m F) :=
  fixedRayFiberFromRows angularOrder (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    rows R F (maskIdeal q m F) (freeConductor q) hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K
    (fun a J=>rowScalar angularOrder q hq m hm rows R F hR hF hrows v Ψ a.1 a.2 J)
    (fun a J=>rowScalar_norm angularOrder q hq m hm rows R F hR hF hrows v Ψ hΨ a.1 a.2 J)

lemma reflectedFiber_rowPhase (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq))
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6) (i:ℕ×ℕ×ℕ) :
    ((reflectedFiber angularOrder q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,e)).rowPhase i
        (fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
          (fun I hI=>⟨hrows I hI,hbound I hI⟩) J)=
      rowScalar angularOrder q hq m hm rows R F hR hF hrows v Ψ (ray,e) i.1 J := by
  exact fixedRayFiberFromRows_rowPhase angularOrder _ _ _ _ _ _ _ _ _ _ _ _
    (mask_bad q m F) (fun I hI=>⟨hrows I hI,hbound I hI⟩) J ray e i

end
end OAI.CubicEisenstein.AngularPhysicalFiberData
