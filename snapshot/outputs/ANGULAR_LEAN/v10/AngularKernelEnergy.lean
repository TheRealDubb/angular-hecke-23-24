import AngularKernelContour
import OAI.NumberTheory.DirichletL.Eisenstein.DirichletForm

/-! Quantitative quadratic energy for the actual shifted reflection kernel.
The arithmetic quadratic estimate is reused with its literal common-column
and row-phase hypotheses. Physical branch-model membership remains separate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

namespace OAI.CubicEisenstein.AngularKernelEnergy

open CompletedGauss ActualEisensteinCubic CanonicalQuadraticSieve

theorem completed_kernel_log_separation (angularOrder : ℕ)
    {ι : Type*} [Fintype ι] (V : ι→ℝ→ℂ) (slope M : ι→ℝ)
    (hM : ∀i,0≤M i) (hV : ∀i y,V i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (A J : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀y : ι→ℝ,(∏i,V i (y i))*AngularReflectionKernel.paperKernel angularOrder (Vstar W)
          (R*Real.exp (∑i,slope i*y i))=
        ∫t : ℝ,(∏i,V i (y i)*FourierBridge.logPhase t (slope i*y i))*B t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖B t‖) volume ∧
      (1+R)^A*(∫t : ℝ,(1+‖t‖)^J*‖B t‖)≤C ∧
      (∀t : ℝ,(1+R)^A*(1+‖t‖)^J*‖B t‖≤C) := by
  let S := vstarSchwartz W a b ha hsupp hW
  obtain ⟨s,D,hD,hbound⟩ := AngularReflectionKernel.paperKernel_euler_source_uniform_weighted_bound angularOrder
    a b ha A (J+(volume : Measure ℝ).integrablePower)
  have hF := AngularReflectionKernel.paperKernel_compact_source_smooth angularOrder (Vstar W) a b ha
    (Vstar_support W a b hsupp) (Vstar_contDiff W a b ha hsupp hW)
  apply LocalLogFourier.coupled_positive_log_separation_envelope V (AngularReflectionKernel.paperKernel angularOrder (Vstar W))
    slope M hM hV hF A J (D*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) S) (by positivity)
  intro i hi x hx
  have he : (S : ℝ→ℂ)=Vstar W := rfl
  have hb := hbound S (Vstar_support W a b hsupp) i hi x hx
  rw [he] at hb
  exact hb

theorem completed_kernel_three_window (angularOrder : ℕ)
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀r u v : ℝ,V₀ r*V₁ u*V₂ v*AngularReflectionKernel.paperKernel angularOrder (Vstar W)
        (R*Real.exp (-2*r+u+3*v))=
        ∫t : ℝ,(V₀ r*FourierBridge.logPhase t (-2*r))*
          (V₁ u*FourierBridge.logPhase t u)*(V₂ v*FourierBridge.logPhase t (3*v))*B t) ∧
      (1+R)^A*(∫t : ℝ,‖B t‖)≤C := by
  let V : Fin 3→ℝ→ℂ := ![V₀,V₁,V₂]
  let slope : Fin 3→ℝ := ![-2,1,3]
  let M : Fin 3→ℝ := ![M₀,M₁,M₂]
  have hm : ∀i,0≤M i := by intro i; fin_cases i <;> assumption
  have hv : ∀i y,V i y≠0 → |y|≤M i := by intro i; fin_cases i <;> assumption
  obtain ⟨C,hC,h⟩ := completed_kernel_log_separation angularOrder V slope M hm hv W a b ha hsupp hW A 0
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨B,hB,hi,hbound,hpoint⟩ := h R hR
  refine ⟨B,?_,by simpa only [pow_zero,one_mul] using hbound⟩
  intro r u v
  simpa [V,slope,Fin.prod_univ_succ,Fin.sum_univ_succ,mul_assoc,add_assoc] using hB ![r,u,v]

theorem completed_smooth_quadratic (angularOrder : ℕ)
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B lengthScale R : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale → 0<R →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal O→Ideal O→ℂ,(∀n∈S,∀v∈T,‖β n v‖≤lengthScale) →
    ∀yr : idealRange K→ℝ,∀yn yb : Ideal O→ℝ,
    (∑k : idealRange K,‖∑n∈S,∑v∈T,
      quadraticRow k.val (primaryGenerator (n*v))*β n v*
      (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*AngularReflectionKernel.paperKernel angularOrder (Vstar W)
        (R*Real.exp (-2*yr k+yn n+3*yb v)))‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2/(1+R)^(2*A) := by
  obtain ⟨Cq,hCq,hq⟩ := integrated_product_quadratic ε hε
  obtain ⟨Ck,hCk,hkernel⟩ := completed_kernel_three_window angularOrder V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ W a b ha hsupp hW A
  refine ⟨Cq*(Ck^2+1),by positivity,?_⟩
  intro K U B lengthScale R hK hU hB hL hR S T hS hT β hβ yr yn yb
  obtain ⟨g,hsep,hg⟩ := hkernel R hR
  let rowPhase : idealRange K→ℝ→ℂ := fun k t => V₀ (yr k)*FourierBridge.logPhase t (-2*yr k)
  let βt : ℝ→Ideal O→Ideal O→ℂ := fun t n v =>
    β n v*(V₁ (yn n)*FourierBridge.logPhase t (yn n))*(V₂ (yb v)*FourierBridge.logPhase t (3*yb v))
  have hphase (t x : ℝ) : ‖FourierBridge.logPhase t x‖=1 := FourierBridge.logPhase_norm t x
  have hrowPhase (k : idealRange K) (t : ℝ) : ‖rowPhase k t‖≤1 := by
    simp only [rowPhase,norm_mul,hphase,mul_one]
    exact hV₀n _
  have hβt (t : ℝ) (n : Ideal O) (hn : n∈S) (v : Ideal O) (hv : v∈T) : ‖βt t n v‖≤lengthScale := by
    simp only [βt,norm_mul,hphase,mul_one]
    exact (mul_le_of_le_one_right (by positivity)
      (hV₂n _)).trans ((mul_le_of_le_one_right (norm_nonneg _) (hV₁n _)).trans (hβ n hn v hv))
  have hrowPhasec (k : idealRange K) : Continuous (rowPhase k) :=
    continuous_const.mul (FourierBridge.logPhase_continuous_left _)
  have hβtc (n v : Ideal O) : Continuous (fun t => βt t n v) :=
    (continuous_const.mul (continuous_const.mul (FourierBridge.logPhase_continuous_left _))).mul
      (continuous_const.mul (FourierBridge.logPhase_continuous_left _))
  have hi := hq K U B lengthScale hK hU hB hL S T hS hT βt hβtc hβt rowPhase hrowPhasec hrowPhase g
  have he (k : idealRange K) :
      (∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*β n v*
        (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*AngularReflectionKernel.paperKernel angularOrder (Vstar W)
          (R*Real.exp (-2*yr k+yn n+3*yb v)))) =
      ∫t : ℝ,g t*(rowPhase k t*∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*βt t n v) := by
    have hint (n v : Ideal O) : Integrable (fun t : ℝ =>
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
    _ = _ := by ring

end OAI.CubicEisenstein.AngularKernelEnergy
