import AngularTotientSeed

/-! Exact angular ideal/norm-fiber compact-sum identities and a seed Mellin
continuation. The series is the Mobius-totient series, not the ordinary L-function. -/
noncomputable section
namespace OAI.CubicEisenstein.AngularWeightedMellin
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
open SixthPowerAverage (totientDensity totientDensity_norm_le_one)
open AngularSixthPower (mobiusWeight_norm_le_one)
open AngularTotientSeed (outside_totient_moebius_bound)
open CompactMellinBridge

def weightedMoebius  (χ : AngularCharacter) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  mobiusWeight χ I*totientDensity I

def outsideWeight  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : Ideal ActualEisensteinCubic.O→ℂ :=
  FiniteSFactor.outsideWeight S (weightedMoebius χ)

def weightedCoeff  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : ℕ→ℂ :=
  FiniteSFactor.outsideCoeff S (weightedMoebius χ)

theorem weightedMoebius_norm_le_one  (χ : AngularCharacter)
    (I : Ideal ActualEisensteinCubic.O) : ‖weightedMoebius χ I‖≤1 := by
  rw [weightedMoebius,norm_mul]
  exact (mul_le_mul (mobiusWeight_norm_le_one χ I)
    (totientDensity_norm_le_one I) (norm_nonneg _) zero_le_one).trans_eq (mul_one _)

@[simp] theorem weightedMoebius_zero  (χ : AngularCharacter) :
    weightedMoebius χ (0:Ideal ActualEisensteinCubic.O)=0 := by
  change ((UniqueFactorizationMonoid.moebius (0:Ideal ActualEisensteinCubic.O):ℂ)*
    χ.idealHom (0:Ideal ActualEisensteinCubic.O))*totientDensity 0=0
  rw [UniqueFactorizationMonoid.moebius_zero,Int.cast_zero,zero_mul,zero_mul]

theorem outsideWeight_norm_le_one  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (I : Ideal ActualEisensteinCubic.O) :
    ‖outsideWeight χ S I‖≤1 := by
  unfold outsideWeight FiniteSFactor.outsideWeight
  split_ifs
  · exact weightedMoebius_norm_le_one χ I
  · simp

@[simp] theorem outsideWeight_zero  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) :
    outsideWeight χ S (0:Ideal ActualEisensteinCubic.O)=0 := by
  unfold outsideWeight FiniteSFactor.outsideWeight
  split_ifs
  · exact weightedMoebius_zero χ
  · rfl

@[simp] theorem weightedCoeff_zero  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : weightedCoeff χ S 0=0 := by
  unfold weightedCoeff FiniteSFactor.outsideCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hz:=Ideal.absNorm_eq_zero_iff.mp (FiniteSFactor.mem_fiber.mp hI)
  change outsideWeight χ S I=0
  rw [hz]
  exact outsideWeight_zero χ S

theorem weightedCoeff_norm_bound  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (n : ℕ) : ‖weightedCoeff χ S n‖≤128*n := by
  by_cases hn : n=0
  · subst n
    simp
  have hn1 : (1:ℝ)≤n:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hc:=DescentFiberCost.finite_ideal_count_real (FiniteSFactor.fiber n) n hn1 (by
      intro I hI hz
      have hh:=FiniteSFactor.mem_fiber.mp hI
      rw [hz] at hh
      simp only [Ideal.absNorm_bot] at hh
      exact hn hh.symm) (by
      intro I hI
      exact_mod_cast (FiniteSFactor.mem_fiber.mp hI).le)
  calc
    _≤∑I∈FiniteSFactor.fiber n,‖outsideWeight χ S I‖:=norm_sum_le _ _
    _≤∑I∈FiniteSFactor.fiber n,(1:ℝ):=Finset.sum_le_sum (fun I hI=>outsideWeight_norm_le_one χ S I)
    _=(FiniteSFactor.fiber n).card:=by simp
    _≤128*n:=hc

theorem weightedCoeff_LSeriesSummable  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (s : ℂ) (hs : 2<s.re) :
    LSeriesSummable (weightedCoeff χ S) s := by
  apply LSeriesSummable_of_isBigO_rpow hs
  apply Asymptotics.IsBigO.of_bound 128
  filter_upwards [] with n
  simpa only [show (2:ℝ)-1=1 by norm_num,Real.rpow_one,Real.norm_natCast]
    using weightedCoeff_norm_bound χ S n

theorem weightedCoeff_hasSum  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (b Z : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) (D : ℕ) (hD : b*Z≤D) :
    HasSum (fun n : ℕ=>weightedCoeff χ S n*W ((n:ℝ)/Z))
      (∑I∈outsideIdealsUpTo S D,mobiusWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I) := by
  have ht (n : ℕ) (hn : n∉Finset.Icc 1 D) : weightedCoeff χ S n*W ((n:ℝ)/Z)=0 := by
    by_cases hn0 : n=0
    · subst n
      simp
    · have hnD : D<n := by simp only [Finset.mem_Icc] at hn;omega
      have hz : W ((n:ℝ)/Z)=0 := by
        by_contra hw
        have hh:=(div_le_iff₀ hZ).mp (hW _ hw)
        have hl : (D:ℝ)<n:=by exact_mod_cast hnD
        linarith
      rw [hz,mul_zero]
  have hh : HasSum (fun n : ℕ=>weightedCoeff χ S n*W ((n:ℝ)/Z))
      (∑n∈Finset.Icc 1 D,weightedCoeff χ S n*W ((n:ℝ)/Z)) :=
    hasSum_sum_of_ne_finset_zero ht
  have he:=outsideIdealSum_eq_outsideCoeff_sum S D (weightedMoebius χ)
    (fun n=>W ((n:ℝ)/Z))
  change _=(∑n∈Finset.Icc 1 D,weightedCoeff χ S n*W ((n:ℝ)/Z)) at he
  rw [←he] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only [weightedMoebius]
  ring

theorem ideal_weighted_hasSum  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (b Z : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) (D : ℕ) (hD : b*Z≤D) :
    HasSum (fun I : Ideal ActualEisensteinCubic.O=>outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z))
      (∑I∈outsideIdealsUpTo S D,mobiusWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I) := by
  have ht (I : Ideal ActualEisensteinCubic.O) (hI : I∉outsideIdealsUpTo S D) :
      outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z)=0 := by
    by_cases hI0 : I=0
    · rw [hI0,outsideWeight_zero,zero_mul]
    by_cases hg : ∀P∈S,¬P∣I
    · have hz : W ((Ideal.absNorm I:ℝ)/Z)=0 := by
        by_contra hn
        apply hI
        refine mem_outsideIdealsUpTo.mpr ⟨?_,?_,hg⟩
        · exact Nat.one_le_iff_ne_zero.mpr (fun hh=>hI0 (Ideal.absNorm_eq_zero_iff.mp hh))
        · exact_mod_cast ((div_le_iff₀ hZ).mp (hW _ hn)).trans hD
      rw [hz,mul_zero]
    · simp [outsideWeight,FiniteSFactor.outsideWeight,hg]
  have hh : HasSum (fun I : Ideal ActualEisensteinCubic.O=>outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z))
      (∑I∈outsideIdealsUpTo S D,outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z)) :=
    hasSum_sum_of_ne_finset_zero ht
  convert hh using 1
  apply Finset.sum_congr rfl
  intro I hI
  simp only [outsideWeight,FiniteSFactor.outsideWeight,ite_eq_left (mem_outsideIdealsUpTo.mp hI).2.2,weightedMoebius]
  ring


open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter Asymptotics MeasureTheory
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion
open InitialMeanSquare CompactMellinBridge

def weightedCompactSum  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (t : ℝ) : ℂ :=
  ∑'n : ℕ,weightedCoeff χ S n*W ((n:ℝ)*t)

theorem weightedCompactSum_hasSum  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ)
    (hW : ∀x,2≤x→W x=0) (t : ℝ) (ht : 0<t) :
    HasSum (fun n : ℕ=>weightedCoeff χ S n*W ((n:ℝ)*t)) (weightedCompactSum χ S W t) := by
  obtain ⟨N,hN⟩:=exists_nat_gt (2/t)
  have hz (n : ℕ) (hn : n∉Finset.range N) : weightedCoeff χ S n*W ((n:ℝ)*t)=0 := by
    have hNn : N≤n:=by simpa only [Finset.mem_range,not_lt] using hn
    have htwo : 2≤(n:ℝ)*t := by
      have hh:=(div_lt_iff₀ ht).mp hN
      exact hh.le.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hNn) ht.le)
    rw [hW _ htwo,mul_zero]
  exact (summable_of_ne_finset_zero hz).hasSum

theorem weightedCompactSum_inv_eq  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (Z b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) (D : ℕ) (hD : b*Z≤D) :
    weightedCompactSum χ S W Z⁻¹=
      ∑I∈outsideIdealsUpTo S D,mobiusWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I := by
  simpa only [weightedCompactSum,div_eq_mul_inv] using
    (weightedCoeff_hasSum χ S W b Z hZ hW D hD).tsum_eq

theorem weightedCompactSum_eq_ideal_tsum  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (Z b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) :
    weightedCompactSum χ S W Z⁻¹=
      ∑'I : Ideal ActualEisensteinCubic.O,outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z) := by
  have hD : b*Z≤(⌈b*Z⌉₊:ℝ):=Nat.le_ceil _
  rw [weightedCompactSum_inv_eq χ S W Z b hZ hW _ hD,
    (ideal_weighted_hasSum χ S W b Z hZ hW _ hD).tsum_eq]

theorem weightedCompactSum_isBigO_of_density 
    (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (hcan : AngularInitialDensity.HasInitialCanonicalDensityAtRadius
      (conjugateMonoid χ.elementHom.toMonoidHom) S hbad)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε : ℝ) (hε : 0<ε) :
    (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹)=O[atTop]
      (fun Z : ℝ=>Z^((23:ℝ)/24+ε)) := by
  obtain ⟨C,hC,hbound⟩:=outside_totient_moebius_bound χ S hbad hSp hcan
    W a b ha hs hW ε hε
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with Z hZ
  have hZp : 0<Z:=by linarith
  have hD : b*Z≤(⌈b*Z⌉₊:ℝ):=Nat.le_ceil _
  rw [weightedCompactSum_inv_eq χ S W Z b hZp (fun x hx=>(hs hx).2) _ hD,
    Real.norm_of_nonneg (Real.rpow_nonneg hZp.le _)]
  exact hbound _ Z hZ hD

theorem weightedCompactMellin_analytic_of_density 
    (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (hcan : AngularInitialDensity.HasInitialCanonicalDensityAtRadius
      (conjugateMonoid χ.elementHom.toMonoidHom) S hbad)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0)
    (ε : ℝ) (hε : 0<ε) :
    AnalyticOnNhd ℂ
      (fun s : ℂ=>mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))
      {s : ℂ | (23:ℝ)/24+ε<s.re} := by
  have hf:=weightedCompactSum_hasSum χ S W (fun x hx=>hs x (Or.inr hx))
  have hlocal:=weighted_sum_inv_locallyIntegrableOn_pos (weightedCoeff χ S) W
    (weightedCompactSum χ S W) hW (fun x hx=>hs x (Or.inr hx)) hf
  have hzero:=weighted_sum_zero_near_small_D (weightedCoeff χ S) (weightedCoeff_zero χ S) W
    (weightedCompactSum χ S W) (fun x hx=>hs x (Or.inr hx)) hf
  have hsup : Function.support W⊆Set.Icc (1:ℝ) 2 := by
    intro x hx
    have h1 : 1<x:=by by_contra hh;exact hx (hs x (Or.inl (le_of_not_gt hh)))
    have h2 : x<2:=by by_contra hh;exact hx (hs x (Or.inr (le_of_not_gt hh)))
    exact ⟨h1.le,h2.le⟩
  exact ShortDraftMellin.inverse_mellin_analytic _ _ hlocal
    (weightedCompactSum_isBigO_of_density χ S hbad hSp hcan
      W 1 2 (by norm_num) hsup hW ε hε) hzero

theorem weightedCompactMellin_eq_series 
    (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0)
    (s : ℂ) (hRe : 2<s.re) :
    mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s)=
      mellin W s*LSeries (weightedCoeff χ S) s := by
  have hls:=weightedCoeff_LSeriesSummable χ S s hRe
  exact mellin_weighted_sum (weightedCoeff χ S) W (weightedCompactSum χ S W) s
    (weightedCoeff_zero χ S) (weightedCompactSum_hasSum χ S W (fun x hx=>hs x (Or.inr hx)))
    (weighted_term_integrable _ (weightedCoeff_zero χ S) W s (compact_weight_mellin_convergent W hW hs s))
    (weighted_terms_fubini _ (weightedCoeff_zero χ S) W s hls) hls

theorem weightedCompactMellin_analytic 
    (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (hcan : AngularInitialDensity.HasInitialCanonicalDensityAtRadius
      (conjugateMonoid χ.elementHom.toMonoidHom) S hbad)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0) :
    AnalyticOnNhd ℂ
      (fun s : ℂ=>mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))
      {s : ℂ | (23:ℝ)/24<s.re} := by
  intro s hsRe
  have he : 0<(s.re-(23:ℝ)/24)/2:=by change (23:ℝ)/24<s.re at hsRe;linarith
  apply weightedCompactMellin_analytic_of_density χ S hbad hSp hcan
    W hW hs _ he s
  change (23:ℝ)/24+(s.re-23/24)/2<s.re
  change (23:ℝ)/24<s.re at hsRe
  linarith

theorem ideal_totient_moebius_bound 
    (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (hcan : AngularInitialDensity.HasInitialCanonicalDensityAtRadius
      (conjugateMonoid χ.elementHom.toMonoidHom) S hbad)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
      ‖∑'I : Ideal ActualEisensteinCubic.O,outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z)‖≤
        C*Z^((23:ℝ)/24+ε) := by
  obtain ⟨C,hC,hbound⟩:=outside_totient_moebius_bound χ S hbad hSp hcan
    W a b ha hs hW ε hε
  refine ⟨C,hC,?_⟩
  intro Z hZ
  have hZp : 0<Z:=by linarith
  have hD : b*Z≤(⌈b*Z⌉₊:ℝ):=Nat.le_ceil _
  rw [(ideal_weighted_hasSum χ S W b Z hZp (fun x hx=>(hs hx).2) _ hD).tsum_eq]
  exact hbound _ Z hZ hD

theorem physical_weightedCompactMellin_analytic (χ : AngularCharacter) (angularOrder : ℕ)
    (hk : χ.k = (angularOrder : ℤ))
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀ x, x ≤ 1 ∨ 2 ≤ x → W x = 0) :
    let S := reflectionExcludedPrimes (AngularRayOrbit.orbitConductor χ.conjugate)
    AnalyticOnNhd ℂ
      (fun s : ℂ => mellin (fun Z : ℝ => weightedCompactSum χ S W Z⁻¹) (-s))
      {s : ℂ | (23 : ℝ)/24 < s.re} := by
  have hkconj : χ.conjugate.k = -(angularOrder : ℤ) := by
    change -χ.k = -(angularOrder : ℤ)
    rw [hk]
  have he : χ.conjugate.elementHom.toMonoidHom = conjugateMonoid χ.elementHom.toMonoidHom := by
    ext a
    exact χ.conjugate_elementCoeff a
  have hcan := AngularInitialDensity.physical_initial_density χ.conjugate angularOrder hkconj
  rw [he] at hcan
  exact weightedCompactMellin_analytic χ
    (reflectionExcludedPrimes (AngularRayOrbit.orbitConductor χ.conjugate))
    (reflectionExcludedPrimes_bad (AngularRayOrbit.orbitConductor χ.conjugate))
    (reflectionExcludedPrimes_prime (AngularRayOrbit.orbitConductor χ.conjugate))
    hcan W hW hs

end OAI.CubicEisenstein.AngularWeightedMellin
