import AngularPhysicalFiberData
import OAI.NumberTheory.DirichletL.RowCompletion.BranchDecoding
/-! Exact finite collection of shifted angular fiber values over the original
finite rays, inactive prime sets and three-valued active branch labels. -/
noncomputable section
open scoped BigOperators Classical ContDiff
namespace OAI.CubicEisenstein.AngularFiberCollection
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CompletedGauss.FreeReflection
local notation "Eis" => ActualEisensteinCubic.O
theorem fixedRayFiber_value (angularOrder : ℕ) (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=AngularPhysicalFiberData.fixedRayFiber angularOrder c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow
    AngularFiberEnergy.fiberValue angularOrder d W X ρ q k=
      ∑r:FixedReflectionRay c hc,∑A:Finset (pool I Q Q0),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q Q0 A*rayWeight (r,encodeReflectionSix ⟨A,e⟩)*
          AngularBranchData.value angularOrder (d.branch (fixedReflectionRayEquiv c hc r,encodeReflectionSix ⟨A,e⟩)) W X ρ q k := by
  dsimp only
  rw [AngularFiberEnergy.fiberValue,Fintype.sum_prod_type]
  calc
    _=∑r:FixedReflectionRay c hc,∑e:pool I Q Q0→Fin 6,
        reflectionSixInactiveWeight I F Q Q0 e*
          (rayWeight (r,e)*AngularBranchData.value angularOrder ((AngularPhysicalFiberData.fixedRayFiber angularOrder c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow).branch
            (fixedReflectionRayEquiv c hc r,e)) W X ρ q k) := by
      apply Fintype.sum_equiv (fixedReflectionRayEquiv c hc).symm
      intro t
      apply Finset.sum_congr rfl
      intro e he
      simp only [Equiv.apply_symm_apply]
      change (rayWeight ((fixedReflectionRayEquiv c hc).symm t,e)*
        reflectionSixInactiveWeight I F Q Q0 e)*_= _
      ring
    _=_:=by
      apply Finset.sum_congr rfl
      intro r hr
      rw [FreeReflection.sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro e he
      exact (mul_assoc _ _ _).symm

theorem fixedRayFiberFromRows_value (angularOrder : ℕ)
    (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=AngularPhysicalFiberData.fixedRayFiberFromRows angularOrder c hc rows I F Q Q0 hI hQ K scalar hscalar
    AngularFiberEnergy.fiberValue angularOrder d W X ρ q k=
      ∑r:FixedReflectionRay c hc,∑B:Finset (pool I Q Q0),
        reflectionInactiveStratumWeight I F Q Q0 B*
          ∑l:B→Fin 3,AngularBranchData.value angularOrder (d.branch (fixedReflectionRayEquiv c hc r,encodeReflectionSix ⟨B,l⟩)) W X ρ q k := by
  dsimp only
  unfold AngularPhysicalFiberData.fixedRayFiberFromRows
  rw [fixedRayFiber_value]
  simp only [mul_one, Finset.mul_sum]

section
open CanonicalRowCompletion CanonicalRowCompletion.ActualFiber
variable (angularOrder : ℕ) (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]
theorem reflectedFiber_value (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (W:ℝ→ℂ) (X:ℝ) (k:idealRange (completedResidualScale K R (maskIdeal q m F))) :
    let d:=AngularPhysicalFiberData.reflectedFiber angularOrder q hq m hm rows R F hR hF hrows v K Ψ hΨ
    AngularFiberEnergy.fiberValue angularOrder d W X 1 completedRamifiedStep k=
      ∑r:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq),
        ∑B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),
          FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
            ∑l:B→Fin 3,AngularBranchData.value angularOrder (d.branch (fixedReflectionRayEquiv (reflectionConductor q)
              (reflectionConductor_ne_zero q hq) r,encodeReflectionSix ⟨B,l⟩)) W X 1 completedRamifiedStep k := by
  exact fixedRayFiberFromRows_value angularOrder (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    rows R F (maskIdeal q m F) (freeConductor q) hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K
    (fun a J=>AngularPhysicalFiberData.rowScalar angularOrder q hq m hm rows R F hR hF hrows v Ψ a.1 a.2 J)
    (fun a J=>AngularPhysicalFiberData.rowScalar_norm angularOrder q hq m hm rows R F hR hF hrows v Ψ hΨ a.1 a.2 J)
    W X 1 completedRamifiedStep k

end
end OAI.CubicEisenstein.AngularFiberCollection
