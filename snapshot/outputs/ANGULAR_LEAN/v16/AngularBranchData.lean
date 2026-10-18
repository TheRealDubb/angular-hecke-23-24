import AngularRawKernel
import OAI.NumberTheory.DirichletL.RowCompletion.FixedCuspBranches

/-! The original branch record contains only arithmetic and bounded arrays.
Its original value uses the unshifted kernel. These evaluations use the
actual shifted kernel and are connected by proved absolute dyadic reindexing. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical ContDiff
namespace OAI.CubicEisenstein.AngularBranchData
open CompletedGauss ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def value (angularOrder : ℕ) {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedBranchData levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ := by
  letI : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact ∑'i : ℕ×ℕ×ℕ,AngularDyadicEnergy.reflectedBranchBlock angularOrder (fun p : d.primes => p.val) d.good
    (fun p => completedLocalExponent I F p.val) d.label W
    (completedResidualScale K I Q) (completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes => p.val) d.label)
    ρ q d.nColumns d.bColumns d.amplitude d.rowPhase i k
def rawValue (angularOrder : ℕ) {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ := by
  letI : ∀p : d.primes,p.val.IsMaximal:=d.maximal
  exact ∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
    AngularRawKernel.rawDualKernelTerm angularOrder (Vstar W)
      ((completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes=>p.val) d.label)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k.val:ℝ))^2) ρ q
      (canonicalRawBranchCoefficient (fun p : d.primes=>p.val) d.good
        (fun p=>completedLocalExponent I F p.val) d.label ρ q η (fun m=>σ m k) k.val) x

theorem withCanonicalCuspArray_value (angularOrder : ℕ) {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hσ : ∀m k,‖σ m k‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X ρ q : ℝ) (hX : 0<X) (hρ : 0<ρ) (hq : 1<q)
    (hK : 0<completedResidualScale K I Q)
    (k : idealRange (completedResidualScale K I Q))
    (hk : completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    value angularOrder (d.withCanonicalCuspArray η hη σ hσ) W X ρ q k =
      rawValue angularOrder d η σ W X ρ q k := by
  let : ∀p : d.primes,p.val.IsMaximal:=d.maximal
  have hn (J : Ideal Eis) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) :=
    nonzeroDualIdeal_norm_pos ⟨J,hJ⟩
  have hprod:=hn (∏p : d.primes,p.val)
    (Finset.prod_ne_zero_iff.mpr (fun p _=>NeZero.ne p.val))
  have hd:=hn _ (reflectionExtractedDivisor_ne_zero (fun p : d.primes=>p.val)
    (fun p=>NeZero.ne p.val) (fun p=>completedLocalExponent I F p.val) d.label 1)
  have he:=hn _ (reflectionExtractedDivisor_ne_zero (fun p : d.primes=>p.val)
    (fun p=>NeZero.ne p.val) (fun p=>completedLocalExponent I F p.val) d.label 2)
  have hy : 0<completedBranchScale K (X/d.levelScale) I F Q
      (fun p : d.primes=>p.val) d.label := by
    unfold completedBranchScale
    have hl:=d.levelScale_pos
    positivity
  exact AngularRawKernel.canonical_reflected_series angularOrder (fun p : d.primes=>p.val) d.good
    (fun p=>completedLocalExponent I F p.val) d.label W a b ha hsupp hW
    (completedResidualScale K I Q)
    (completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes=>p.val) d.label)
    ρ q hK hy hρ hq η σ hη hσ k hk
theorem restrictRows_value (angularOrder : ℕ) {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (sector : idealRange (completedResidualScale K I Q)→Prop)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) :
    value angularOrder (d.restrictRows sector) W X ρ q k =
      if sector k then value angularOrder d W X ρ q k else 0 := by
  by_cases hk:sector k
  · simp only [value,ReflectedBranchData.restrictRows,AngularDyadicEnergy.reflectedBranchBlock,ite_eq_left hk]
    rfl
  · simp only [value,ReflectedBranchData.restrictRows,AngularDyadicEnergy.reflectedBranchBlock,ite_eq_right hk,zero_mul,tsum_zero]

theorem sum_restrictRows_selected (angularOrder : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ι→ReflectedBranchData levelBound K I F Q)
    (sector : idealRange (completedResidualScale K I Q)→ι)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) :
    (∑s : ι,value angularOrder ((d s).restrictRows (fun k=>sector k=s)) W X ρ q k)=
      value angularOrder (d (sector k)) W X ρ q k := by
  calc
    _ = value angularOrder ((d (sector k)).restrictRows (fun k'=>sector k'=sector k)) W X ρ q k := by
      apply Finset.sum_eq_single (sector k)
      · intro s _ hs
        rw [restrictRows_value,ite_eq_right (Ne.symm hs)]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    _ = _ := by rw [restrictRows_value,ite_eq_left rfl]

end OAI.CubicEisenstein.AngularBranchData
