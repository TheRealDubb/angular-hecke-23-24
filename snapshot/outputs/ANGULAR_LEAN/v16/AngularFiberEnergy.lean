import AngularBranchData

/-! Shifted-kernel energy at the actual completed branch scales. The original
arithmetic cost and branch counts are reused unchanged. Constants may depend
on the fixed angular order; physical fiber membership is a separate identity. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical ContDiff
namespace OAI.CubicEisenstein.AngularFiberEnergy
open CompletedGauss ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

theorem completed_reflected_fiber_fixed_scale (angularOrder : ℕ)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q B : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hB : 1≤B) :
    ∃C : ℝ,0<C ∧ ∀K X c : ℝ,1≤K → 1≤X → 0<c → c≤B →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i),
      Pairwise (fun i j => IsCoprime (P i) (P j)) →
      (∀i,P i∣I*Q) → (∀i,¬P i∣rowResidualPart I Q) →
    ∀e : ι→Fin 3,∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀J∈S i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀J∈T i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ,(∀i k,‖σ i k‖≤1) →
      (∑k : idealRange (completedResidualScale K I Q),‖∑'i : ℕ×ℕ×ℕ,
        AngularDyadicEnergy.reflectedBranchBlock angularOrder P hg (fun i => completedLocalExponent I F (P i)) e W
          (completedResidualScale K I Q) (completedBranchScale K (X/c) I F Q P e) ρ q S T η σ i k‖^2)
        ≤C*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨C,hC,h⟩ := AngularDyadicEnergy.completed_reflected_branch_series angularOrder W a b ha hsupp hW deltaLoss ρ q hδ hρ hq
  refine ⟨C*B^(2*deltaLoss+1),by positivity,?_⟩
  intro K X c hK hX hc hcB I F Q hI hQ hIK hk ι _ P _ hg hcop hpool hres e S T hS hT η hη σ hσ
  have hn (J : Ideal O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj (v : Fin 3) := hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i))
    (fun i => completedLocalExponent I F (P i)) e v)
  have hp := hn (∏i,P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i)))
  have hk0 : 0<completedResidualScale K I Q := by linarith
  have hy : 0<completedBranchScale K X I F Q P e := by
    unfold completedBranchScale
    have hX0 : 0<X := by linarith
    have hd := hj 1
    have he := hj 2
    positivity
  rw [completedBranchScale_div]
  have hb := (h (completedResidualScale K I Q) (c*completedBranchScale K X I F Q P e)
    hk (mul_pos hc hy) P hg (fun i => completedLocalExponent I F (P i)) e S T hS hT η hη σ hσ).2
  have hs := completed_scaled_shape (2*deltaLoss) (completedResidualScale K I Q)
    (completedBranchScale K X I F Q P e) _ c B (by positivity) hk0 hy
    (mul_pos (hj 0) (hj 2)) hc hcB hB
  have hcst := completed_actual_fiber_cost deltaLoss K X hδ.le hK hX I F Q hI hQ hIK P hcop hpool hres e
  have hh := hs.trans (mul_le_mul_of_nonneg_left hcst (by positivity : 0≤B^(2*deltaLoss+1)))
  apply hb.trans
  have hfinal := mul_le_mul_of_nonneg_left hh hC.le
  convert hfinal using 1 <;> (try dsimp [completedResidualScale,completedBranchScale]) <;> ring

theorem branch_energy_bound (angularOrder : ℕ)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀K X : ℝ,1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q → ∀d : ReflectedBranchData levelBound K I F Q,
      (∑k,‖AngularBranchData.value angularOrder d W X ρ q k‖^2)≤
        C*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨C,hC,h⟩ := completed_reflected_fiber_fixed_scale angularOrder W a b ha hsupp hW deltaLoss ρ q levelBound hδ hρ hq hlevel
  refine ⟨C,hC,?_⟩
  intro K X hK hX I F Q hI hQ hIK hk d
  let : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact h K X d.levelScale hK hX d.levelScale_pos d.levelScale_le I F Q hI hQ hIK hk _ d.good d.coprime d.divides d.nonresidual
    d.label d.nColumns d.bColumns d.nBounds d.bBounds d.amplitude d.amplitude_bound
    d.rowPhase d.rowPhase_bound


def fiberValue (angularOrder : ℕ) {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ :=
  ∑b,d.weight b*AngularBranchData.value angularOrder (d.branch b) W X ρ q k

theorem fiber_energy_bound (angularOrder : ℕ)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀(rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q → ∀d : ReflectedFiberData rays levelBound K I F Q,
      (∑k,‖fiberValue angularOrder d W X ρ q k‖^2)≤
        C*(rays:ℝ)^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨Cb,hCb,hb⟩ := branch_energy_bound angularOrder W a b ha hsupp hW deltaLoss ρ q levelBound hδ hρ hq hlevel
  obtain ⟨Cp,hCp,hp⟩ := completed_branch_count_small_power ε hε
  refine ⟨Cb*Cp,by positivity,?_⟩
  intro rays K X hK hX I F Q hI hQ hIK hk d
  let : ∀p : d.pool,p.val.IsMaximal := d.maximal
  have hcount := hp (I*Q) (mul_ne_zero hI hQ) (fun p : d.pool => p.val)
    Subtype.val_injective d.divides
  have hnorm : (Ideal.absNorm (I*Q):ℝ)≤K*(Ideal.absNorm Q:ℝ) := by
    simp only [map_mul,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hIK (Nat.cast_nonneg _)
  have hcount' : (6:ℝ)^(2*d.pool.card)≤Cp*(K*(Ideal.absNorm Q:ℝ))^ε := by
    have hc : (6:ℝ)^(2*d.pool.card)≤Cp*(Ideal.absNorm (I*Q):ℝ)^ε := by
      simpa only [Fintype.card_coe] using hcount
    exact hc.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hε.le) hCp.le)
  have he := ReflectedFiberData.finite_energy_bound
    (fun b => AngularBranchData.value angularOrder (d.branch b) W X ρ q) d.weight d.weight_bound _
    (fun b => hb K X hK hX I F Q hI hQ hIK hk (d.branch b))
  change (∑k,‖fiberValue angularOrder d W X ρ q k‖^2)≤_ at he
  apply he.trans
  have hc : (Fintype.card (Fin rays×(d.pool→Fin 6)):ℝ)^2=(rays:ℝ)^2*(6:ℝ)^(2*d.pool.card) := by
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_mul,Nat.cast_pow]
    rw [mul_pow,←pow_mul,Nat.mul_comm d.pool.card 2]
    norm_num
  rw [hc]
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hKQ : 0<K*(Ideal.absNorm Q:ℝ) := mul_pos (by linarith) hnQ
  calc
    _ ≤ ((rays:ℝ)^2*(Cp*(K*(Ideal.absNorm Q:ℝ))^ε))*
      (Cb*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
        (Ideal.absNorm (rowPowerfulPart I):ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcount' (sq_nonneg _)
    _ = _ := by rw [Real.rpow_add hKQ]; ring

end OAI.CubicEisenstein.AngularFiberEnergy
