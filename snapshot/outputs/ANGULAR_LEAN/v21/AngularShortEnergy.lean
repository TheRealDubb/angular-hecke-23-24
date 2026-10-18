import AngularShortAverage
import AngularSieveModels

/-! The angular short-sum estimates expressed in the original sieve's
physical element rows, unit sum, and canonical state geometry. -/
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.CubicEisenstein.AngularShortEnergy
open ActualEisensteinCubic CanonicalRowCompletion CompletedUnitRows
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)
local instance : Fintype ActualEisensteinCubic.Oˣ :=
  @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

theorem short_completed_elements_uniform_twist (angularOrder : ℕ)
    (a b : ℝ) (ha : 0<a)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀T : Finset ActualEisensteinCubic.O,(∀z∈T,z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤K) →
    ∀(Ψ : ActualEisensteinCubic.O→*ℂ),(∀x,‖Ψ x‖≤1) → ∀(mask : ActualEisensteinCubic.O) (lengthScale : ℂ),
      (∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        AngularDyadicModels.HasExactCompletedDyadicModels angularOrder rays (T.image (fun z=>Ideal.span {z})) K
          (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val (G*f.val)
          (CompletedHeight.normTwistedSource W θ) (unitRowFamily Ψ mask u f) lengthScale) →
      (∑f : idealRange F,∑z∈T,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) z) W X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨n,hn⟩ := AngularHeight.short_completed_average_uniform_twist angularOrder
    a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨n,?_⟩
  intro W hsupp hW
  obtain ⟨C,hC,hbound⟩ := hn W hsupp hW
  refine ⟨6*C,by positivity,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin T hT Ψ hΨ mask lengthScale hmodels
  let rows := T.image (fun z=>Ideal.span {z})
  let R : ℝ := (C*(1+‖θ‖)^n)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε
  have hrows := image_span_nonzero_norm T K hT
  have hu (u : ActualEisensteinCubic.Oˣ) :
      (∑f : idealRange F,∑I∈rows,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) (u.val*idealGenerator I)) W X (Z^(1/1000:ℝ))‖^2)/F≤R := by
    simp_rw [rowTwist_normHeight]
    exact hbound θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows
      (unitRowFamily Ψ mask u) (unitRowFamily_norm Ψ hΨ mask u) lengthScale (hmodels u)
  have hsum :
      (∑f : idealRange F,∑z∈T,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) z) W X (Z^(1/1000:ℝ))‖^2)≤
      ∑u : ActualEisensteinCubic.Oˣ,∑f : idealRange F,∑I∈rows,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) (u.val*idealGenerator I)) W X (Z^(1/1000:ℝ))‖^2 := by
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro f _
    exact sum_nonzero_element_le_units T (fun z hz=>(hT z hz).1) _ (fun z=>sq_nonneg _)
  calc
    _ ≤ (∑u : ActualEisensteinCubic.Oˣ,∑f : idealRange F,∑I∈rows,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) (u.val*idealGenerator I)) W X (Z^(1/1000:ℝ))‖^2)/F :=
      div_le_div_of_nonneg_right hsum (by linarith)
    _ = ∑u : ActualEisensteinCubic.Oˣ,(∑f : idealRange F,∑I∈rows,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) (u.val*idealGenerator I)) W X (Z^(1/1000:ℝ))‖^2)/F :=
      Finset.sum_div _ _ _
    _ ≤ ∑u : ActualEisensteinCubic.Oˣ,R := Finset.sum_le_sum (fun u _=>hu u)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,unit_card,nsmul_eq_mul]; dsimp [R]; ring


theorem canonicalShortEnergy_uniform_twist (angularOrder : ℕ)
    (a b : ℝ) (ha : 0<a) (ε ρ q levelBound : ℝ)
    (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃d : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0≤C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^((1:ℝ)/1000) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      (2*K)*(Ideal.absNorm G:ℝ)≤X*F*Z^(-((1:ℝ)/40)) →
    ∀(labels : Finset (Ideal ActualEisensteinCubic.O)),labels⊆idealRange F →
    ∀(Ψ : ActualEisensteinCubic.O→*ℂ),(∀x,‖Ψ x‖≤1) → ∀(mask : ActualEisensteinCubic.O) (lengthScale : ℂ),
      (∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^((1:ℝ)/1000)),
        AngularDyadicModels.HasExactCompletedDyadicModels angularOrder rays (((firstFrequencyDisk (2*K)).erase 0).image (fun z=>Ideal.span {z})) (2*K)
          (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val (G*f.val)
          (CompletedHeight.normTwistedSource W θ) (CompletedUnitRows.unitRowFamily Ψ mask u f) lengthScale) →
      rowFamilyEnergy labels (fun I z=>shortCompletedSum (rowTwist (normHeightTwist Ψ θ)
        mask (idealGenerator I) z) W X (Z^((1:ℝ)/1000))) K≤
      (C*(1+‖θ‖)^d)*(rays:ℝ)^2*‖lengthScale‖^2*((2*K)*(Ideal.absNorm G:ℝ)*F)^ε*(K*F)*Z^ε := by
  obtain ⟨d,hbound⟩:=short_completed_elements_uniform_twist angularOrder a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨d,?_⟩
  intro W hs hW
  obtain ⟨C,hC,h⟩:=hbound W hs hW
  refine ⟨2*SchwartzMap.seminorm ℝ 0 0 rowMajorant*C,by positivity,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin labels hlabels Ψ hΨ mask lengthScale hmodels
  have hK0 : 0<K:=zero_lt_one.trans_le hK
  have hF0 : 0<F:=zero_lt_one.trans_le hF
  have hT : ∀z∈(firstFrequencyDisk (2*K)).erase 0,
      z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤2*K := by
    intro z hz
    refine ⟨(Finset.mem_erase.mp hz).1,?_⟩
    rw [←eisEmbedding_norm_sq_eq_absNorm_span]
    exact (mem_firstFrequencyDisk (2*K) z).mp (Finset.mem_erase.mp hz).2
  have hshort:=h θ rays Z (2*K) X F hZ (by linarith) hF hFZ G hG hbad hmargin
    ((firstFrequencyDisk (2*K)).erase 0) hT Ψ hΨ mask lengthScale hmodels
  have hsum := (div_le_iff₀ hF0).mp hshort
  have hrect:=rowFamilyEnergy_le_rectangle labels F K hK0 hlabels
    (fun I z=>shortCompletedSum (rowTwist (normHeightTwist Ψ θ) mask (idealGenerator I) z) W X (Z^((1:ℝ)/1000)))
  exact hrect.trans ((mul_le_mul_of_nonneg_left hsum (apply_nonneg _ _)).trans_eq (by ring))


theorem canonicalShortEnergy_normalized_uniform_twist (angularOrder : ℕ)
    (a b : ℝ) (ha : 0<a) (ε ρ q levelBound : ℝ)
    (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃d : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0≤C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^((1:ℝ)/1000) → 0<X → X*F≤Z^3 →
    ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      (2*K)*(Ideal.absNorm G:ℝ)≤X*F*Z^(-((1:ℝ)/40)) →
    ∀(labels : Finset (Ideal ActualEisensteinCubic.O)),labels⊆idealRange F →
    ∀(Ψ : ActualEisensteinCubic.O→*ℂ),(∀x,‖Ψ x‖≤1) → ∀(mask : ActualEisensteinCubic.O) (lengthScale : ℂ),
      (∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^((1:ℝ)/1000)),
        AngularDyadicModels.HasExactCompletedDyadicModels angularOrder rays (((firstFrequencyDisk (2*K)).erase 0).image (fun z=>Ideal.span {z})) (2*K)
          (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val (G*f.val)
          (CompletedHeight.normTwistedSource W θ) (CompletedUnitRows.unitRowFamily Ψ mask u f) lengthScale) →
      2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum (rowTwist (normHeightTwist Ψ θ)
        mask (idealGenerator I) z) W X (Z^((1:ℝ)/1000))) K≤
      (C*(1+‖θ‖)^d)*(rays:ℝ)^2*‖lengthScale‖^2*(X*F)^2*Z^(7*ε-(1:ℝ)/40) := by
  obtain ⟨d,hbound⟩:=canonicalShortEnergy_uniform_twist angularOrder a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨d,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩:=hbound W hs hW
  refine ⟨C,hC,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ hX hmass G hG hbad hmargin labels hlabels Ψ hΨ mask lengthScale hmodels
  have he:=hb θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin labels hlabels Ψ hΨ mask lengthScale hmodels
  have hFZ' : F≤Z^3 := by
    apply hFZ.trans
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
  have hGN : 1≤(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz=>hG (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscalar:=shortEnergy_scalar_normalization C ((1+‖θ‖)^d) ((rays:ℝ)^2*‖lengthScale‖^2)
    Z K X F (Ideal.absNorm G:ℝ) ε hC (by positivity) (by positivity) hZ
    (zero_le_one.trans hK) hX (zero_le_one.trans hF) hGN hε.le hFZ' hmass hmargin
  apply (mul_le_mul_of_nonneg_left he (by positivity : 0≤2*X)).trans
  convert hscalar using 1 <;> ring


theorem canonicalShortState_uniform_twist (angularOrder : ℕ)
    (a b : ℝ) (ha : 0<a) (ε ρ q levelBound : ℝ)
    (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃d : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0≤C ∧ ∀(θ : ℝ) (rays : ℕ) (S : Finset (Ideal ActualEisensteinCubic.O)),
    (∀P∈S,Prime P) → fixedBadPrimes⊆S →
    ∀(base : ActualEisensteinCubic.O→*ℂ) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ),
    CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
    (∀x,‖base x‖≤1) → 1≤Z → Real.exp 9000≤Z → 0≤η → 3000*η≤(1:ℝ)/80 →
    2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) → ∀lengthScale : ℂ,
    (F<Z^((1:ℝ)/1000) → ∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^((1:ℝ)/1000)),
      AngularDyadicModels.HasExactCompletedDyadicModels angularOrder rays (((firstFrequencyDisk (2*K)).erase 0).image (fun z=>Ideal.span {z})) (2*K)
        (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val ((Ideal.span {m*excludedGenerator S})*f.val)
        (CompletedHeight.normTwistedSource W θ)
        (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator S) u f) lengthScale) →
    2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum
      (rowTwist (normHeightTwist Ψ θ) (m*excludedGenerator S) (idealGenerator I) z)
      W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K≤
    (C*(1+‖θ‖)^d)*(rays:ℝ)^2*‖lengthScale‖^2*(X*F)^2*Z^(7*ε-(1:ℝ)/40) := by
  obtain ⟨d,hbound⟩:=canonicalShortEnergy_normalized_uniform_twist angularOrder a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨d,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩:=hbound W hs hW
  refine ⟨C,hC,?_⟩
  intro θ rays S hSp hbad base Z η Ψ m labels X F K hstate hbase hZ hZbig hη hbudget hfixed lengthScale hmodels
  by_cases hF : F<Z^((1:ℝ)/1000)
  · rw [ite_eq_left hF]
    obtain ⟨hG,hpG,hlabels,hmass,hmargin⟩:=canonicalShortState_geometry S hSp hbad base Z η Ψ m labels X F K
      hstate hZ hZbig hη hbudget hfixed
    exact hb θ rays Z K X F hZ hstate.row_ge_one hstate.label_ge_one hF.le hstate.column_pos hmass
      (Ideal.span {m*excludedGenerator S}) hG hpG hmargin labels hlabels Ψ
      (fun x=>hstate.coefficient.norm_le hbase x) (m*excludedGenerator S) lengthScale (hmodels hF)
  · rw [ite_eq_right hF,rowFamilyEnergy_eq_sum labels _ K (zero_lt_one.trans_le hstate.row_ge_one)]
    have hz (I : Ideal ActualEisensteinCubic.O) (z : ActualEisensteinCubic.O) : shortCompletedSum
        (rowTwist (normHeightTwist Ψ θ) (m*excludedGenerator S) (idealGenerator I) z) W X 0=0:=
      shortCompletedSum_nonpos _ _ _ _ le_rfl
    simp only [hz,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,Finset.sum_const_zero]
    positivity


end OAI.CubicEisenstein.AngularShortEnergy
