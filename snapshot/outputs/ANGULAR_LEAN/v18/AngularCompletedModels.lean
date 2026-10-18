import AngularFiberEnergy
import OAI.NumberTheory.DirichletL.RowCompletion.ReflectedFibers
/-! Exact shifted-kernel model membership and its quantitative completed-row
energy consequence. Physical model membership must be proved separately. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical ContDiff
namespace OAI.CubicEisenstein.AngularCompletedModels
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

def idealValue (angularOrder : ℕ) {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (J : Ideal O) : ℂ :=
  if h : J∈idealRange (completedResidualScale K I Q) then AngularFiberEnergy.fiberValue angularOrder d W X ρ q ⟨J,h⟩ else 0

theorem idealValue_at (angularOrder : ℕ) {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (J : idealRange (completedResidualScale K I Q)) :
    idealValue angularOrder d W X ρ q J.val=AngularFiberEnergy.fiberValue angularOrder d W X ρ q J := by
  simp only [idealValue,dite_eq_left J.property]

def HasExactCompletedModels (angularOrder : ℕ) (rays : ℕ) (rows : Finset (Ideal O))
    (K X ρ q levelBound : ℝ) (F Q : Ideal O) (W : ℝ→ℂ) (Ψ : Ideal O→O→*ℂ) (lengthScale : ℂ) : Prop :=
  ∀A∈rows.image rowPowerfulPart,∀T∈rows.image (fun I => rowMaskPart I Q),
    (completedRowFiber rows Q A T).Nonempty →
    ∃I∈completedRowFiber rows Q A T,∃d : ReflectedFiberData rays levelBound K I F Q,
      ∀J∈completedRowFiber rows Q A T,
        completedT (Ψ J) W X=lengthScale*idealValue angularOrder d W X ρ q (rowResidualPart J Q)

theorem completed_energy_of_exact_models (angularOrder : ℕ)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀(rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal O)) (F Q : Ideal O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal O→O→*ℂ) (lengthScale : ℂ),HasExactCompletedModels angularOrder rays rows K X ρ q levelBound F Q W Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) W X‖^2)≤
        C*(rays:ℝ)^2*‖lengthScale‖^2*(Ideal.absNorm Q:ℝ)^ε*
          (K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  obtain ⟨Cm,hCm,hm⟩ := AngularFiberEnergy.fiber_energy_bound angularOrder W a b ha hsupp hW deltaLoss ε ρ q levelBound hδ hε hρ hq hlevel
  obtain ⟨Co,hCo,ho⟩ := completed_outer_row_small_power ε hε
  refine ⟨Co*Cm,by positivity,?_⟩
  intro rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hexact
  let B : ℝ := Cm*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*
    (K+K^2*(Ideal.absNorm Q:ℝ)/X)
  have hB : 0≤B := by dsimp [B]; positivity
  have hblocks : ∀A∈rows.image rowPowerfulPart,∀T∈rows.image (fun I => rowMaskPart I Q),
      (∑I∈completedRowFiber rows Q A T,‖completedT (Ψ I) W X‖^2)≤B/(Ideal.absNorm A:ℝ) := by
    intro A hA T hT
    by_cases hempty : (completedRowFiber rows Q A T).Nonempty
    · obtain ⟨I,hIf,d,hd⟩ := hexact A hA T hT hempty
      obtain ⟨hIr,hIA,hIT⟩ := Finset.mem_filter.mp hIf
      have hI := (hrows I hIr).1
      have hIK := (hrows I hIr).2
      have hk := one_le_completedResidualScale K I Q hI hIK
      have hdenergy := hm rays K X hK hX I F Q hI hQ hIK hk d
      have hembed := completedRowFiber_energy_le rows Q A T hbad K hrows
        (idealValue angularOrder d W X ρ q)
      have hscale : K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))=completedResidualScale K I Q := by
        simp only [completedResidualScale,hIA,hIT]
      rw [hscale] at hembed
      simp_rw [idealValue_at] at hembed
      have hsource : (∑J∈completedRowFiber rows Q A T,‖completedT (Ψ J) W X‖^2)=
          ‖lengthScale‖^2*∑J∈completedRowFiber rows Q A T,‖idealValue angularOrder d W X ρ q (rowResidualPart J Q)‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hd J hJ,norm_mul,mul_pow]
      rw [hsource]
      apply (mul_le_mul_of_nonneg_left (hembed.trans hdenergy) (sq_nonneg _)).trans
      apply le_of_eq
      dsimp [B]
      rw [hIA]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.sum_empty]
      exact div_nonneg hB (Nat.cast_nonneg _)
  have hh := ho rows Q hQ (fun I => ‖completedT (Ψ I) W X‖^2) B hB hblocks
  apply hh.trans_eq
  dsimp [B]
  ring

theorem hasExactCompletedModels_of_representative_identity (angularOrder : ℕ)
    (rays:ℕ) (rows:Finset (Ideal Eis)) (K X ρ q levelBound:ℝ)
    (F Q:Ideal Eis) (W:ℝ→ℂ) (Ψ:Ideal Eis→Eis→*ℂ) (scale:ℂ)
    (model:∀I:Ideal Eis,I∈rows→ReflectedFiberData rays levelBound K I F Q)
    (hmodel:∀(I:Ideal Eis) (hI:I∈rows),∀J∈representativeRowFiber rows I Q,
      completedT (Ψ J) W X=scale*idealValue angularOrder (model I hI) W X ρ q (rowResidualPart J Q)) :
    HasExactCompletedModels angularOrder rays rows K X ρ q levelBound F Q W Ψ scale := by
  intro A hA T hT hnonempty
  obtain ⟨I,hI⟩:=hnonempty
  obtain ⟨hIrows,hIA,hIT⟩:=Finset.mem_filter.mp hI
  refine ⟨I,hI,model I hIrows,?_⟩
  intro J hJ
  apply hmodel I hIrows J
  simpa only [representativeRowFiber,hIA,hIT] using hJ

end OAI.CubicEisenstein.AngularCompletedModels
