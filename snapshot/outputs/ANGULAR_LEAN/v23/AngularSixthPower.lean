import AngularPoissonMoment
import OAI.NumberTheory.DirichletL.Mellin.SixthPowerAverage

/-! Sixth-power averaging retains the actual angular ideal coefficient.
The arithmetic masks and Poisson estimates are reused from pinned OAI-003. -/
noncomputable section
namespace OAI.CubicEisenstein.AngularSixthPower
open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter Asymptotics MeasureTheory
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O idealRowSum
open EisensteinSchwartzPoisson hiding O
open IdealMobiusDivisorSum hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion InitialMeanSquare
open SevenEighths.Angular
open AngularIdealRow (mobiusWeight)
open SixthPowerAverage hiding idealRowSum_sixth_average sixth_average_remainder_bound
  idealRowSum_sixth_eq_coprime_sum average_remainder_small_power totient_sum_normalized_bound

theorem idealMoebius_norm_le_one (I : Ideal O) :
    ‖((UniqueFactorizationMonoid.moebius I : ℤ) : ℂ)‖ ≤ 1 := by
  classical
  by_cases h : Squarefree I
  · rw [h.moebius_eq]
    simp
  · rw [UniqueFactorizationMonoid.moebius_of_not_squarefree h]
    simp

theorem mobiusWeight_norm_le_one 
    (χ : AngularCharacter) (I : Ideal O) :
    ‖mobiusWeight χ I‖ ≤ 1 := by
  rw [mobiusWeight, norm_mul]
  have hμ := idealMoebius_norm_le_one I
  have hχ := χ.norm_idealHom_le_one I
  exact (mul_le_mul hμ hχ (norm_nonneg _) (by positivity)).trans (by norm_num)

theorem idealRowSum_sixth_average 
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (χ : AngularCharacter) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    (∑'b : ActualEisensteinCubic.O, V (‖eisEmbedding b‖^2/Y)*AngularIdealRow.idealRowSum F hF hg χ W (b^6))=
      (Y:ℂ)*paperRadialFourier V 0*
        (∑I∈F,mobiusWeight χ I*W (Ideal.absNorm I)*totientDensity I)+
      ∑I∈F,mobiusWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y := by
  have he (b : ActualEisensteinCubic.O) : V (‖eisEmbedding b‖^2/Y)*AngularIdealRow.idealRowSum F hF hg χ W (b^6)=
      ∑I∈F,(mobiusWeight χ I*W (Ideal.absNorm I))*
        (idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y)) := by
    rw [AngularIdealRow.idealRowSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I hI
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun I _ =>
    (idealSexticRow_sixth_radial_summable F hF hg I V Y hY).mul_left _)]
  simp_rw [tsum_mul_left]
  rw [show (∑I∈F,mobiusWeight χ I*W (Ideal.absNorm I)*
      ∑'b : ActualEisensteinCubic.O,idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y))=
      ∑I∈F,mobiusWeight χ I*W (Ideal.absNorm I)*
        ((Y:ℂ)*paperRadialFourier V 0*totientDensity I+
          maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y) by
    apply Finset.sum_congr rfl
    intro I hI
    rw [idealSexticRow_sixth_average F hF hg hI V Y hY]]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem sixth_average_remainder_bound 
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (χ : AngularCharacter) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    ‖∑I∈F,mobiusWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y‖≤
      ∑I∈F,‖W (Ideal.absNorm I)‖*(2:ℝ)^(primeSupport I).card*pvControl V := by
  let : ∀i : primePool F,(i.val).IsMaximal := primePool_maximal F hF
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  have hr := maskedPrincipalRemainder_uniform (fun i : primePool F=>i.val)
    (idealSupport F I) V Y hY
  rw [idealSupport_card F hI] at hr
  rw [norm_mul,norm_mul]
  calc
    _≤(1*‖W (Ideal.absNorm I)‖)*((2:ℝ)^(primeSupport I).card*pvControl V) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (mobiusWeight_norm_le_one χ I) (norm_nonneg _))
        hr (norm_nonneg _) (by positivity)
    _=_ := by ring

theorem idealRowSum_sixth_eq_coprime_sum 
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (χ : AngularCharacter) (W : ℕ→ℂ) (b : ActualEisensteinCubic.O) :
    AngularIdealRow.idealRowSum F hF hg χ W (b^6)=
      ∑I∈F with IsCoprime I (Ideal.span {b}),mobiusWeight χ I*W (Ideal.absNorm I) := by
  rw [AngularIdealRow.idealRowSum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hsq : Squarefree I
  · rw [squarefree_sixth_row_coprime F hF hg hI hsq b]
    split_ifs <;> simp
  · rw [AngularIdealRow.mobiusWeight_zero_of_not_squarefree χ I hsq]
    simp
theorem average_remainder_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ 
      (F : Finset (Ideal ActualEisensteinCubic.O)) (_hF : ∀I∈F,I≠⊥)
      (χ : AngularCharacter) (W : ℕ→ℂ)
      (V : 𝓢(ℝ,ℂ)) (Y lengthScale G : ℝ),0<Y → 1≤lengthScale → 0≤G →
      (∀n,‖W n‖≤G) → (∀I∈F,W (Ideal.absNorm I)≠0→(Ideal.absNorm I:ℝ)≤lengthScale) →
      ‖∑I∈F,mobiusWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y‖≤
      C*G*pvControl V*lengthScale^(1+ε) := by
  obtain ⟨C,hC,hp⟩:=SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨128*C,by positivity,?_⟩
  intro F hF χ W V Y lengthScale G hY hL hG hW hnorm
  apply (sixth_average_remainder_bound F hF χ W V Y hY).trans
  let T:=F.filter (fun I=>W (Ideal.absNorm I)≠0)
  have he : (∑I∈F,‖W (Ideal.absNorm I)‖*(2:ℝ)^(primeSupport I).card*pvControl V)=
      ∑I∈T,‖W (Ideal.absNorm I)‖*(2:ℝ)^(primeSupport I).card*pvControl V := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro I hI hn
    have hz : W (Ideal.absNorm I)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
    simp only [hz,norm_zero,zero_mul]
  have hc : (T.card:ℝ)≤128*lengthScale :=
    DescentFiberCost.finite_ideal_count_real T lengthScale hL
      (fun I hI=>hF I (Finset.mem_filter.mp hI).1)
      (fun I hI=>hnorm I (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hI).2)
  rw [he]
  calc
    _≤∑I∈T,G*(C*lengthScale^ε)*pvControl V := by
      apply Finset.sum_le_sum
      intro I hI
      have hh:=Finset.mem_filter.mp hI
      have hb:=(hp I (hF I hh.1)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm I hh.1 hh.2) hε.le) hC.le)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hW _) hb (by positivity) hG) (pvControl_nonneg V)
    _=(T.card:ℝ)*(G*(C*lengthScale^ε)*pvControl V) := by simp
    _≤128*lengthScale*(G*(C*lengthScale^ε)*pvControl V) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (by positivity) (pvControl_nonneg V))
    _=(128*C)*G*pvControl V*lengthScale^(1+ε) := by
      rw [Real.rpow_add (by linarith : (0:ℝ)<lengthScale),Real.rpow_one]
      ring

theorem totient_sum_normalized_bound 
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (χ : AngularCharacter) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    Y*‖paperRadialFourier V 0‖*
      ‖∑I∈F,mobiusWeight χ I*W (Ideal.absNorm I)*totientDensity I‖≤
      ‖∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*AngularIdealRow.idealRowSum F hF hg χ W (b^6)‖+
      ‖∑I∈F,mobiusWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y‖ := by
  have he:=idealRowSum_sixth_average F hF hg χ W V Y hY
  have hh:=norm_sub_le (∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*AngularIdealRow.idealRowSum F hF hg χ W (b^6))
    (∑I∈F,mobiusWeight χ I*W (Ideal.absNorm I)*
      maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y)
  rw [he,add_sub_cancel_right,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY] at hh
  rwa [←he] at hh

end OAI.CubicEisenstein.AngularSixthPower
