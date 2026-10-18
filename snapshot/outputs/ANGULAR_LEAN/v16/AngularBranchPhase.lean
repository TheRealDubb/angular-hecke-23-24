import AngularBranchData
/-! Exact pointwise phase operations for the shifted raw series, preserving
the arithmetic column array and all branch scales. -/
noncomputable section
open scoped BigOperators Classical
namespace OAI.CubicEisenstein.AngularBranchPhase
open CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
variable {levelBound K:ℝ} {I F Q:Ideal Eis}
variable (angularOrder : ℕ) (d:ReflectedBranchData levelBound K I F Q)
variable (η:ℕ→Ideal Eis→Ideal Eis→ℂ)
variable (σ τ:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
variable (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q))

lemma rawValue_congr_phase_at (h:∀m,σ m k=τ m k) :
    AngularBranchData.rawValue angularOrder d η σ W X ρ q k=AngularBranchData.rawValue angularOrder d η τ W X ρ q k := by
  unfold AngularBranchData.rawValue
  apply tsum_congr
  intro x
  simp only [AngularRawKernel.rawDualKernelTerm,canonicalRawBranchCoefficient,h]

lemma rawValue_zero_phase : AngularBranchData.rawValue angularOrder d η (fun _ _=>0) W X ρ q k=0 := by
  unfold AngularBranchData.rawValue
  simp only [AngularRawKernel.rawDualKernelTerm,canonicalRawBranchCoefficient,zero_mul,tsum_zero]

lemma rawValue_mul_phase_at (a:idealRange (completedResidualScale K I Q)→ℂ) :
    AngularBranchData.rawValue angularOrder d η (fun m l=>a l*σ m l) W X ρ q k=a k*AngularBranchData.rawValue angularOrder d η σ W X ρ q k := by
  unfold AngularBranchData.rawValue
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  unfold AngularRawKernel.rawDualKernelTerm canonicalRawBranchCoefficient
  ring

lemma rawValue_select_phase_at (P:idealRange (completedResidualScale K I Q)→Prop)
    [DecidablePred P] :
    AngularBranchData.rawValue angularOrder d η (fun m l=>if P l then σ m l else 0) W X ρ q k=
      if P k then AngularBranchData.rawValue angularOrder d η σ W X ρ q k else 0 := by
  by_cases hp:P k
  · rw [ite_eq_left hp]
    exact rawValue_congr_phase_at angularOrder d η _ σ W X ρ q k (fun m=>ite_eq_left hp)
  · rw [ite_eq_right hp]
    calc
      _=AngularBranchData.rawValue angularOrder d η (fun _ _=>0) W X ρ q k:=
        rawValue_congr_phase_at angularOrder d η _ _ W X ρ q k (fun m=>ite_eq_right hp)
      _=0:=rawValue_zero_phase angularOrder d η W X ρ q k

end OAI.CubicEisenstein.AngularBranchPhase
