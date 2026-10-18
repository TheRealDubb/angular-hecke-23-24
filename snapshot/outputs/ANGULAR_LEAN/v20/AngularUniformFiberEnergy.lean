import AngularUniformKernelEnergy
import AngularPhysicalMeanSquare

/-! Uniform polynomial height propagation through the shifted branch,
fiber, row partition and full dyadic summation. Exact model membership is
an explicit premise here and is supplied for physical characters separately. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical SchwartzMap ContDiff
namespace OAI.CubicEisenstein.AngularHeight
open CompletedHeight CompletedGauss ActualEisensteinCubic CompletedDyadic
open CanonicalQuadraticSieve

theorem uniform_polynomial_reflected_branch_series (angularOrder : ℕ) {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel angularOrder Wfamily)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀θ K Y : ℝ,1≤K → 0<Y →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal ActualEisensteinCubic.O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i) (j : ι→ℕ) (e : ι→Fin 3),
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal ActualEisensteinCubic.O),
      (∀i,∀I∈S i,I≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖AngularDyadicEnergy.reflectedBranchBlock angularOrder P hg j e (Wfamily w θ) K Y ρ q S T η σ i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,AngularDyadicEnergy.reflectedBranchBlock angularOrder P hg j e (Wfamily w θ) K Y ρ q S T η σ i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*Y)^(2*deltaLoss)*(K+Y)/
          ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
            (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)) := by
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_smooth_series_rowPhase angularOrder
    completedShellWindow completedShellWindow completedShellWindow (Real.log 2) (Real.log 2) (Real.log 2)
    hl hl hl completedShellWindow_support completedShellWindow_support completedShellWindow_support
    completedShellWindow_norm completedShellWindow_norm completedShellWindow_norm
    Wfamily hWfamily deltaLoss ρ q hδ hρ hq
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨C,hC,h⟩ := hheight w
  refine ⟨C,hC,?_⟩
  intro θ K Y hK hY ι _ P _ hg j e S T hS hT η hη σ hσ
  have hn (v : Fin 3) : 0<(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz =>
      reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e v
        (Ideal.absNorm_eq_zero_iff.mp hz))
  exact h θ K Y _ hK hY (mul_pos (hn 0) (hn 2)) S T
    (fun i I hI => ⟨(hS i I hI).1,(hS i I hI).2.2⟩)
    (fun i I hI => ⟨(hT i I hI).1,(hT i I hI).2.2⟩)
    (fun v => reflectedDyadicCoefficient P hg j e (η v) (ramifiedScale ρ q v.1))
    (fun i n hn v hv => reflectedDyadicCoefficient_norm P hg j e (η i)
      (ramifiedScale ρ q i.1) _ _ (ramifiedScale_pos ρ q hρ (by linarith) _) (by positivity) (by positivity)
      n v (hS i n hn).1 (hT i v hv).1 (hη i n hn v hv) (hS i n hn).2.1 (hT i v hv).2.1)
    σ hσ

theorem uniform_polynomial_reflected_fiber_fixed_scale (angularOrder : ℕ) {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel angularOrder Wfamily)
    (deltaLoss ρ q B : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hB : 1≤B) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀θ K X c : ℝ,1≤K → 1≤X → 0<c → c≤B →
    ∀I F Q : Ideal ActualEisensteinCubic.O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal ActualEisensteinCubic.O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i),
      Pairwise (fun i j => IsCoprime (P i) (P j)) →
      (∀i,P i∣I*Q) → (∀i,¬P i∣rowResidualPart I Q) →
    ∀e : ι→Fin 3,∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal ActualEisensteinCubic.O),
      (∀i,∀J∈S i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀J∈T i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ,(∀i k,‖σ i k‖≤1) →
      (∑k : idealRange (completedResidualScale K I Q),‖∑'i : ℕ×ℕ×ℕ,
        AngularDyadicEnergy.reflectedBranchBlock angularOrder P hg (fun i => completedLocalExponent I F (P i)) e (Wfamily w θ)
          (completedResidualScale K I Q) (completedBranchScale K (X/c) I F Q P e) ρ q S T η σ i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_reflected_branch_series angularOrder Wfamily hWfamily deltaLoss ρ q hδ hρ hq
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨Cbase,hCbase,hbase⟩ := hheight w
  refine ⟨Cbase*B^(2*deltaLoss+1),by positivity,?_⟩
  intro θ K X c hK hX hc hcB I F Q hI hQ hIK hk ι _ P _ hg hcop hpool hres e S T hS hT η hη σ hσ
  let C := Cbase*(1+‖θ‖)^heightDegree
  have hC : 0<C := by dsimp [C]; positivity
  have h := hbase θ
  have hn (J : Ideal ActualEisensteinCubic.O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
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
  convert hfinal using 1 <;> (try dsimp [completedResidualScale,completedBranchScale,C]) <;> ring

theorem uniform_polynomial_branch_energy (angularOrder : ℕ) {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel angularOrder Wfamily)
    (deltaLoss ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀θ K X : ℝ,1≤K → 1≤X →
    ∀I F Q : Ideal ActualEisensteinCubic.O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q → ∀d : ReflectedBranchData levelBound K I F Q,
      (∑k,‖AngularBranchData.value angularOrder d (Wfamily w θ) X ρ q k‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_reflected_fiber_fixed_scale angularOrder Wfamily hWfamily deltaLoss ρ q levelBound hδ hρ hq hlevel
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨C,hC,h⟩ := hheight w
  refine ⟨C,hC,?_⟩
  intro θ K X hK hX I F Q hI hQ hIK hk d
  let : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact h θ K X d.levelScale hK hX d.levelScale_pos d.levelScale_le I F Q hI hQ hIK hk _ d.good d.coprime d.divides d.nonresidual
    d.label d.nColumns d.bColumns d.nBounds d.bBounds d.amplitude d.amplitude_bound
    d.rowPhase d.rowPhase_bound

theorem uniform_polynomial_fiber_energy (angularOrder : ℕ) {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel angularOrder Wfamily)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀I F Q : Ideal ActualEisensteinCubic.O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q → ∀d : ReflectedFiberData rays levelBound K I F Q,
      (∑k,‖AngularFiberEnergy.fiberValue angularOrder d (Wfamily w θ) X ρ q k‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_branch_energy angularOrder Wfamily hWfamily deltaLoss ρ q levelBound hδ hρ hq hlevel
  obtain ⟨Cp,hCp,hp⟩ := completed_branch_count_small_power ε hε
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨Cbase,hCbase,hbase⟩ := hheight w
  refine ⟨Cbase*Cp,by positivity,?_⟩
  intro θ rays K X hK hX I F Q hI hQ hIK hk d
  let Cb := Cbase*(1+‖θ‖)^heightDegree
  have hCb : 0<Cb := by dsimp [Cb]; positivity
  have hb := hbase θ
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
    (fun b => AngularBranchData.value angularOrder (d.branch b) (Wfamily w θ) X ρ q) d.weight d.weight_bound _
    (fun b => hb K X hK hX I F Q hI hQ hIK hk (d.branch b))
  change (∑k,‖AngularFiberEnergy.fiberValue angularOrder d (Wfamily w θ) X ρ q k‖^2)≤_ at he
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
    _ = _ := by rw [Real.rpow_add hKQ]; dsimp [Cb]; ring

theorem uniform_polynomial_energy_of_exact_models (angularOrder : ℕ) {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel angularOrder Wfamily)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal ActualEisensteinCubic.O)) (F Q : Ideal ActualEisensteinCubic.O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ) (lengthScale : ℂ),AngularCompletedModels.HasExactCompletedModels angularOrder rays rows K X ρ q levelBound F Q (Wfamily w θ) Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) (Wfamily w θ) X‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(Ideal.absNorm Q:ℝ)^ε*
          (K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_fiber_energy angularOrder Wfamily hWfamily deltaLoss ε ρ q levelBound hδ hε hρ hq hlevel
  obtain ⟨Co,hCo,ho⟩ := completed_outer_row_small_power ε hε
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨Cbase,hCbase,hbase⟩ := hheight w
  refine ⟨Co*Cbase,by positivity,?_⟩
  intro θ rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hexact
  let Cm := Cbase*(1+‖θ‖)^heightDegree
  have hCm : 0<Cm := by dsimp [Cm]; positivity
  have hm := hbase θ
  let B : ℝ := Cm*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*
    (K+K^2*(Ideal.absNorm Q:ℝ)/X)
  have hB : 0≤B := by dsimp [B,Cm]; positivity
  have hblocks : ∀A∈rows.image rowPowerfulPart,∀T∈rows.image (fun I => rowMaskPart I Q),
      (∑I∈completedRowFiber rows Q A T,‖completedT (Ψ I) (Wfamily w θ) X‖^2)≤B/(Ideal.absNorm A:ℝ) := by
    intro A hA T hT
    by_cases hempty : (completedRowFiber rows Q A T).Nonempty
    · obtain ⟨I,hIf,d,hd⟩ := hexact A hA T hT hempty
      obtain ⟨hIr,hIA,hIT⟩ := Finset.mem_filter.mp hIf
      have hI := (hrows I hIr).1
      have hIK := (hrows I hIr).2
      have hk := one_le_completedResidualScale K I Q hI hIK
      have hdenergy := hm rays K X hK hX I F Q hI hQ hIK hk d
      have hembed := completedRowFiber_energy_le rows Q A T hbad K hrows
        (AngularCompletedModels.idealValue angularOrder d (Wfamily w θ) X ρ q)
      have hscale : K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))=completedResidualScale K I Q := by
        simp only [completedResidualScale,hIA,hIT]
      rw [hscale] at hembed
      simp_rw [AngularCompletedModels.idealValue_at] at hembed
      have hsource : (∑J∈completedRowFiber rows Q A T,‖completedT (Ψ J) (Wfamily w θ) X‖^2)=
          ‖lengthScale‖^2*∑J∈completedRowFiber rows Q A T,‖AngularCompletedModels.idealValue angularOrder d (Wfamily w θ) X ρ q (rowResidualPart J Q)‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hd J hJ,norm_mul,mul_pow]
      rw [hsource]
      apply (mul_le_mul_of_nonneg_left (hembed.trans hdenergy) (sq_nonneg _)).trans
      apply le_of_eq
      dsimp [B,Cm]
      rw [hIA]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.sum_empty]
      exact div_nonneg hB (Nat.cast_nonneg _)
  have hh := ho rows Q hQ (fun I => ‖completedT (Ψ I) (Wfamily w θ) X‖^2) B hB hblocks
  apply hh.trans_eq
  dsimp [B,Cm]
  ring

theorem uniform_polynomial_mean_square_of_exact_reflection (angularOrder : ℕ) {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel angularOrder Wfamily)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal ActualEisensteinCubic.O)) (F Q : Ideal ActualEisensteinCubic.O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ) (lengthScale : ℂ),AngularDyadicModels.HasExactCompletedDyadicModels angularOrder rays rows K X ρ q levelBound F Q (Wfamily w θ) Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) (Wfamily w θ) X‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
          (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  let deltaLoss : ℝ := ε/12
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_energy_of_exact_models angularOrder Wfamily hWfamily deltaLoss deltaLoss ρ q levelBound hδ hδ hρ hq hlevel
  let s : ℝ := 10*deltaLoss+deltaLoss
  have hs : 0≤s := by dsimp [s]; positivity
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨Cbase,hCbase,hbase⟩ := hheight w
  refine ⟨Cbase*(16*(2:ℝ)^s),by positivity,?_⟩
  intro θ rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hmodels
  let C := Cbase*(1+‖θ‖)^heightDegree
  have hC : 0<C := by dsimp [C]; positivity
  have h := hbase θ
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  let A : ℝ := C*(rays:ℝ)^2*‖lengthScale‖^2*(Ideal.absNorm Q:ℝ)^deltaLoss
  have hA : 0≤A := by dsimp [A]; positivity
  rw [←completedRowDyad_sum rows K (by linarith : 0≤K) (fun I hI => (hrows I hI).2)
    (fun I => ‖completedT (Ψ I) (Wfamily w θ) X‖^2)]
  have hper (j : ℕ) (hj : j∈Finset.range (completedRowDyadicLength K+1)) :
      (∑I∈completedRowDyad rows j,‖completedT (Ψ I) (Wfamily w θ) X‖^2)≤
        A*(((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
          ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X)) := by
    have hb := h rays ((2:ℝ)^j) X (one_le_pow₀ (by norm_num)) hX
      (completedRowDyad rows j) F Q hQ hbad
      (fun I hI => ⟨(completedRowDyad_bounds rows j (fun I hI => (hrows I hI).1) I hI).1,
        (completedRowDyad_bounds rows j (fun I hI => (hrows I hI).1) I hI).2.2⟩)
      Ψ lengthScale (hmodels j hj)
    convert hb using 1
    dsimp [A,s,C]
    ring
  calc
    _ ≤ ∑j∈Finset.range (completedRowDyadicLength K+1),
      A*(((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
        ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X)) := Finset.sum_le_sum hper
    _ = A*∑j∈Finset.range (completedRowDyadicLength K+1),
      ((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
        ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*((16*(2:ℝ)^s)*(K*(Ideal.absNorm Q:ℝ))^s*(K+K^2*(Ideal.absNorm Q:ℝ)/X)) :=
      mul_le_mul_of_nonneg_left (completedRowDyadic_shape s K X (Ideal.absNorm Q:ℝ) hs hK
        (by linarith) hnQ) hA
    _ ≤ (C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
        (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
      have hnq : (Ideal.absNorm Q:ℝ)^deltaLoss≤(K*(Ideal.absNorm Q:ℝ))^deltaLoss := by
        apply Real.rpow_le_rpow hnQ.le _ hδ.le
        exact le_mul_of_one_le_left hnQ.le hK
      have hpower : (Ideal.absNorm Q:ℝ)^deltaLoss*(K*(Ideal.absNorm Q:ℝ))^s≤
          (K*(Ideal.absNorm Q:ℝ))^ε := by
        apply (mul_le_mul_of_nonneg_right hnq (by positivity)).trans_eq
        rw [←Real.rpow_add (mul_pos (by linarith) hnQ)]
        congr 1
        dsimp [s,deltaLoss]
        ring
      calc
        _ = ((C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K+K^2*(Ideal.absNorm Q:ℝ)/X))*
          ((Ideal.absNorm Q:ℝ)^deltaLoss*(K*(Ideal.absNorm Q:ℝ))^s) := by dsimp [A]; ring
        _ ≤ ((C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K+K^2*(Ideal.absNorm Q:ℝ)/X))*
          (K*(Ideal.absNorm Q:ℝ))^ε := mul_le_mul_of_nonneg_left hpower (by positivity)
        _ = _ := by ring

    _ = _ := by dsimp [C]; ring

end OAI.CubicEisenstein.AngularHeight
