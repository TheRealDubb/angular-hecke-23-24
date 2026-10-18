import AngularUniformKernel
import AngularDyadicEnergy

/-! Polynomial height control for the actual shifted angular reflection
kernel. The degree is chosen before the live height; the uniform source
certificate also chooses it before the supported smooth source. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
namespace OAI.CubicEisenstein.AngularHeight
open CompletedHeight CompletedGauss ActualEisensteinCubic CompletedDyadic
open CanonicalQuadraticSieve

theorem uniform_polynomial_smooth_quadratic (angularOrder : ℕ) {κ : Type*}
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (P : κ→ℝ→ℝ→ℂ) (hP : HasUniformPolynomialKernel angularOrder P)
    (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀θ K U B lengthScale R : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale → 0<R →
    ∀S T : Finset (Ideal ActualEisensteinCubic.O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,(∀n∈S,∀v∈T,‖β n v‖≤lengthScale) →
    ∀yr : idealRange K→ℝ,∀yn yb : Ideal ActualEisensteinCubic.O→ℝ,
    (∑k : idealRange K,‖∑n∈S,∑v∈T,
      quadraticRow k.val (primaryGenerator (n*v))*β n v*
      (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*AngularReflectionKernel.paperKernel angularOrder (Vstar (P w θ))
        (R*Real.exp (-2*yr k+yn n+3*yb v)))‖^2)≤
      (C*(1+‖θ‖)^heightDegree)*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2/(1+R)^(2*A) := by
  obtain ⟨Cq,hCq,hq⟩ := integrated_product_quadratic ε hε
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_kernel_three_window angularOrder P hP V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ A
  refine ⟨2*heightDegree,?_⟩
  intro w
  obtain ⟨Ck₀,hCk₀,hkernel⟩ := hheight w
  refine ⟨Cq*(Ck₀^2+1),by positivity,?_⟩
  intro θ K U B lengthScale R hK hU hB hL hR S T hS hT β hβ yr yn yb
  let Ck := Ck₀*(1+‖θ‖)^heightDegree
  have hCk : 0≤Ck := by dsimp [Ck]; positivity
  have hCoeff : Cq*(Ck^2+1)≤(Cq*(Ck₀^2+1))*(1+‖θ‖)^(2*heightDegree) := by
    have hh : 1≤(1+‖θ‖)^(2*heightDegree) := one_le_pow₀ (by linarith [norm_nonneg θ])
    have he : Ck^2=Ck₀^2*(1+‖θ‖)^(2*heightDegree) := by
      dsimp [Ck]
      rw [mul_pow,←pow_mul]
      congr 2
      omega
    rw [he]
    nlinarith [sq_nonneg Ck₀]
  obtain ⟨g,hsep,hg⟩ := hkernel θ R hR
  change (1+R)^A*(∫t : ℝ,‖g t‖)≤Ck at hg
  let rowPhase : idealRange K→ℝ→ℂ := fun k t => V₀ (yr k)*FourierBridge.logPhase t (-2*yr k)
  let βt : ℝ→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ := fun t n v =>
    β n v*(V₁ (yn n)*FourierBridge.logPhase t (yn n))*(V₂ (yb v)*FourierBridge.logPhase t (3*yb v))
  have hphase (t x : ℝ) : ‖FourierBridge.logPhase t x‖=1 := FourierBridge.logPhase_norm t x
  have hrowPhase (k : idealRange K) (t : ℝ) : ‖rowPhase k t‖≤1 := by
    simp only [rowPhase,norm_mul,hphase,mul_one]
    exact hV₀n _
  have hβt (t : ℝ) (n : Ideal ActualEisensteinCubic.O) (hn : n∈S) (v : Ideal ActualEisensteinCubic.O) (hv : v∈T) : ‖βt t n v‖≤lengthScale := by
    simp only [βt,norm_mul,hphase,mul_one]
    exact (mul_le_of_le_one_right (by positivity)
      (hV₂n _)).trans ((mul_le_of_le_one_right (norm_nonneg _) (hV₁n _)).trans (hβ n hn v hv))
  have hrowPhasec (k : idealRange K) : Continuous (rowPhase k) :=
    continuous_const.mul (FourierBridge.logPhase_continuous_left _)
  have hβtc (n v : Ideal ActualEisensteinCubic.O) : Continuous (fun t => βt t n v) :=
    (continuous_const.mul (continuous_const.mul (FourierBridge.logPhase_continuous_left _))).mul
      (continuous_const.mul (FourierBridge.logPhase_continuous_left _))
  have hi := hq K U B lengthScale hK hU hB hL S T hS hT βt hβtc hβt rowPhase hrowPhasec hrowPhase g
  have he (k : idealRange K) :
      (∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*β n v*
        (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*AngularReflectionKernel.paperKernel angularOrder (Vstar (P w θ))
          (R*Real.exp (-2*yr k+yn n+3*yb v)))) =
      ∫t : ℝ,g t*(rowPhase k t*∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*βt t n v) := by
    have hint (n v : Ideal ActualEisensteinCubic.O) : Integrable (fun t : ℝ =>
        g t*(rowPhase k t*(quadraticRow k.val (primaryGenerator (n*v))*βt t n v))) := by
      apply g.integrable.mul_bdd (c := ‖quadraticRow k.val (primaryGenerator (n*v))*β n v‖)
      · exact ((hrowPhasec k).mul (continuous_const.mul (hβtc n v))).aestronglyMeasurable
      · filter_upwards [] with t
        simp only [rowPhase,βt,norm_mul,hphase,mul_one]
        have hv01 : ‖V₀ (yr k)‖*‖V₁ (yn n)‖≤1 := by
          simpa only [one_mul] using mul_le_mul (hV₀n (yr k)) (hV₁n (yn n)) (norm_nonneg _) zero_le_one
        have hv012 : (‖V₀ (yr k)‖*‖V₁ (yn n)‖)*‖V₂ (yb v)‖≤1 := by
          simpa only [one_mul] using mul_le_mul hv01 (hV₂n (yb v)) (norm_nonneg _) zero_le_one
        calc
          _ = (‖quadraticRow k.val (primaryGenerator (n*v))‖*‖β n v‖)*
            ((‖V₀ (yr k)‖*‖V₁ (yn n)‖)*‖V₂ (yb v)‖) := by ring
          _ ≤ (‖quadraticRow k.val (primaryGenerator (n*v))‖*‖β n v‖)*1 :=
            mul_le_mul_of_nonneg_left hv012 (by positivity)
          _ = _ := by ring
    simp only [Finset.mul_sum]
    rw [integral_finsetSum _ (fun n hn => integrable_finsetSum _ (fun v hv => hint n v))]
    apply Finset.sum_congr rfl
    intro n hn
    rw [integral_finsetSum _ (fun v hv => hint n v)]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hsep (yr k) (yn n) (yb v),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [rowPhase,βt]
    ring
  simp_rw [he]
  apply hi.trans
  have hpow : 0<(1+R)^A := by positivity
  have hmass : (∫t : ℝ,‖g t‖)≤Ck/(1+R)^A := (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hg)
  have hmass2 := pow_le_pow_left₀ (integral_nonneg (fun t => norm_nonneg _)) hmass 2
  have hbase : 0≤Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2 := by positivity
  calc
    _ ≤ (Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)*(Ck/(1+R)^A)^2 :=
      mul_le_mul_of_nonneg_left hmass2 hbase
    _ ≤ (Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)*((Ck^2+1)/(1+R)^(2*A)) := by
      apply mul_le_mul_of_nonneg_left _ hbase
      rw [div_pow,←pow_mul]
      have hp : A*2=2*A := Nat.mul_comm _ _
      rw [hp]
      exact div_le_div_of_nonneg_right (by nlinarith : Ck^2≤Ck^2+1) (by positivity)
    _ = (Cq*(Ck^2+1))*((K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)/(1+R)^(2*A) := by ring
    _ ≤ _ := by
      have hb := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCoeff (by positivity : 0≤(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2))
        (by positivity : 0≤(1+R)^(2*A))
      convert hb using 1 ; ring

theorem uniform_polynomial_smooth_series_rowPhase (angularOrder : ℕ) {κ : Type*}
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (P : κ→ℝ→ℝ→ℂ) (hP : HasUniformPolynomialKernel angularOrder P)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀θ K Y H : ℝ,1≤K → 0<Y → 0<H →
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal ActualEisensteinCubic.O),
      (∀i,∀I∈S i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀β : (ℕ×ℕ×ℕ)→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖β i n v‖≤
        1/(Real.sqrt ((2:ℝ)^i.2.2)*(2:ℝ)^i.2.1*ramifiedScale ρ q i.1*Real.sqrt H)) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖σ i k*AngularDyadicEnergy.completedSmoothDyadicBlock angularOrder V₀ V₁ V₂ (P w θ) K Y ρ q S T β i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,
        σ i k*AngularDyadicEnergy.completedSmoothDyadicBlock angularOrder V₀ V₁ V₂ (P w θ) K Y ρ q S T β i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*Y)^(2*deltaLoss)*(K+Y)/H := by
  obtain ⟨A,hA⟩ := exists_nat_gt (deltaLoss+1/2)
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_smooth_quadratic angularOrder V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ hV₀n hV₁n hV₂n P hP A (2*deltaLoss) (by positivity)
  obtain ⟨Cs,hCs,hsum⟩ := normMajorant_sum_bound deltaLoss A ρ q hδ hA hρ hq
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨Cbase,hCbase,hquadbase⟩ := hheight w
  refine ⟨2*Cbase*Cs^2,by positivity,?_⟩
  intro θ K Y H hK hY hH S T hS hT β hβ σ hσ
  let Cq := Cbase*(1+‖θ‖)^heightDegree
  have hCq : 0<Cq := by dsimp [Cq]; positivity
  have hquad := hquadbase θ
  have hKp : 0<K := by linarith
  have hqp : 0<q := by linarith
  let g : (ℕ×ℕ×ℕ)→ℝ := fun i => Real.sqrt Cq *
    normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
  have hg0 (i : ℕ×ℕ×ℕ) : 0≤g i := by
    dsimp [g]
    exact mul_nonneg (Real.sqrt_nonneg _) (normMajorant_nonneg _ _ _ _ _ _ _ _
      hKp (by positivity) (ramifiedScale_pos ρ q hρ hqp _) hH (by positivity) (by positivity))
  have henergy (i : ℕ×ℕ×ℕ) :
      (∑k : idealRange K,‖σ i k*AngularDyadicEnergy.completedSmoothDyadicBlock angularOrder V₀ V₁ V₂ (P w θ) K Y ρ q S T β i k‖^2)
        ≤(g i)^2 := by
    let U : ℝ := (2:ℝ)^i.2.2
    let B : ℝ := (2:ℝ)^i.2.1
    let r : ℝ := ramifiedScale ρ q i.1
    let R : ℝ := Y⁻¹*r^3*B^3*U
    have hU : 1≤U := one_le_pow₀ (by norm_num)
    have hB : 1≤B := one_le_pow₀ (by norm_num)
    have hUp : 0<U := by positivity
    have hBp : 0<B := by positivity
    have hr : 0<r := ramifiedScale_pos ρ q hρ hqp _
    have hR : 0<R := by dsimp [R]; positivity
    have h := hquad K U B (1/(Real.sqrt U*B*r*Real.sqrt H)) R
      hK hU hB (by positivity) hR (S i) (T i) (hS i) (hT i) (β i) (hβ i)
      (fun k => Real.log ((Ideal.absNorm k.val:ℝ)/K))
      (fun n => Real.log ((Ideal.absNorm n:ℝ)/U))
      (fun v => Real.log ((Ideal.absNorm v:ℝ)/B))
    change (∑k,‖AngularDyadicEnergy.completedSmoothDyadicBlock angularOrder V₀ V₁ V₂ (P w θ) K Y ρ q S T β i k‖^2)≤_ at h
    have hphase : (∑k : idealRange K,‖σ i k*AngularDyadicEnergy.completedSmoothDyadicBlock angularOrder V₀ V₁ V₂ (P w θ) K Y ρ q S T β i k‖^2)≤
        ∑k : idealRange K,‖AngularDyadicEnergy.completedSmoothDyadicBlock angularOrder V₀ V₁ V₂ (P w θ) K Y ρ q S T β i k‖^2 := by
      apply Finset.sum_le_sum
      intro k _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hσ i k)
    apply (hphase.trans h).trans
    have he : Cq*(K*(U*B))^(2*deltaLoss)*(K+U*B)*(U*B)*
        (1/(Real.sqrt U*B*r*Real.sqrt H))^2/(1+R)^(2*A)=
        Cq*((K*(U*B))^(2*deltaLoss)*(K+U*B)/(B*r^2*H)/(1+R)^(2*(A:ℝ))) := by
      rw [show 2*(A:ℝ)=((2*A:ℕ):ℝ) by norm_num,Real.rpow_natCast]
      simp only [one_div,inv_pow,mul_pow,Real.sq_sqrt hUp.le,Real.sq_sqrt hH.le]
      field_simp

    rw [he]
    have hm := smooth_energy_le_normMajorant_sq deltaLoss A K Y⁻¹ r H U B
      hKp (by positivity) hr hH hUp hBp
    calc
      _ ≤ Cq*(normMajorant deltaLoss A K Y⁻¹ r H U B)^2 := mul_le_mul_of_nonneg_left hm hCq.le
      _ = (g i)^2 := by dsimp [g,U,B,r]; rw [mul_pow,Real.sq_sqrt hCq.le]
  obtain ⟨hs,hb⟩ := hsum K Y H hKp hY hH
  have hm := finite_tsum_energy_bound
    (fun i k => σ i k*AngularDyadicEnergy.completedSmoothDyadicBlock angularOrder V₀ V₁ V₂ (P w θ) K Y ρ q S T β i k) g hg0
    (hs.mul_left (Real.sqrt Cq)) henergy
  refine ⟨hm.1,hm.2.trans ?_⟩
  have hb' : (∑'i,g i)≤Real.sqrt Cq*(Cs*(K*Y)^deltaLoss*(Real.sqrt K+Real.sqrt Y)/Real.sqrt H) := by
    rw [show g=(fun i => Real.sqrt Cq*normMajorant deltaLoss A K Y⁻¹
      (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)) from rfl,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ (tsum_nonneg hg0) hb' 2
  apply hsq.trans
  have hroot : (Real.sqrt K+Real.sqrt Y)^2≤2*(K+Y) := by
    nlinarith [Real.sq_sqrt hKp.le,Real.sq_sqrt hY.le,
      sq_nonneg (Real.sqrt K-Real.sqrt Y)]
  simp only [mul_pow,div_pow,Real.sq_sqrt hCq.le,Real.sq_sqrt hH.le]
  have hp : ((K*Y)^deltaLoss)^2=(K*Y)^(2*deltaLoss) := by
    rw [←Real.rpow_mul_natCast (mul_pos hKp hY).le]
    congr 1
    ring
  rw [hp]
  calc
    _ ≤ Cq*(Cs^2*(K*Y)^(2*deltaLoss)*(2*(K+Y))/H) := by
      apply mul_le_mul_of_nonneg_left _ hCq.le
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity)) hH.le
    _ = _ := by dsimp [Cq]; ring

end OAI.CubicEisenstein.AngularHeight
