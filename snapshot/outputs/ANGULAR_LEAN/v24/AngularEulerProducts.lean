import AngularEulerCorrection

/-! Exact actual angular ordinary/damped Mobius-series product identity,
including the outside-prime mask and norm-fiber LSeries conversion. -/
noncomputable section
namespace OAI.CubicEisenstein.AngularEulerProducts
open scoped BigOperators Classical Topology
open Filter Asymptotics MeasureTheory
open ActualEisensteinCubic
open SevenEighths.Angular
open SmoothMobiusCorrection (PrimeIdeal primeNormPower primeDensity norm_primeNormPower
  primeDensity_norm_le_one one_sub_ne_zero prime_norm_series_summable prime_norm_pos prime_norm_two_le)
open UniqueFactorizationMonoid
open ShortDraftHeckeBridge hiding O
open IdealMobiusDivisorSum hiding O
open SmoothMobiusCorrection (primeProduct primeSet primeProduct_primeSet nat_cpow_prod
  outsideMask prod_cut_primes primeValueHom_squarefree prod_primeSet
  mobiusPrimeCoeff mobiusPrimeCoeff_nonsquarefree mobiusPrimeCoeff_euler
  prime_reciprocal_series_summable idealDirichlet_eq_LSeries)
open AngularEulerCorrection

lemma primeNormTerm_prod  (χ : AngularCharacter) (t : Finset PrimeIdeal) (s : ℂ) :
    (∏P∈t,χ.idealHom P.val*(Ideal.absNorm P.val:ℂ)^(-s))=
      χ.idealHom (primeProduct t)*(Ideal.absNorm (primeProduct t):ℂ)^(-s) := by
  rw [Finset.prod_mul_distrib]
  simp only [primeProduct,map_prod,Nat.cast_prod]
  congr 1
  simpa only [Nat.cast_prod] using (nat_cpow_prod t (fun P=>Ideal.absNorm P.val) (-s)).symm

def ordinaryPrimeValue  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  if I∈S then 0 else χ.idealHom I*(Ideal.absNorm I:ℂ)^(-s)

def dampedPrimeValue  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  if I∈S then 0 else (1-(1:ℂ)/(Ideal.absNorm I:ℂ))*(χ.idealHom I*(Ideal.absNorm I:ℂ)^(-s))

def ordinarySeriesTerm  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  outsideMask S I * AngularIdealRow.mobiusWeight χ I * CubicEisenstein.fullIdealWeight s I

def dampedSeriesTerm  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  ordinarySeriesTerm χ S s I * SixthPowerAverage.totientDensity I

lemma ordinarySeriesTerm_eq  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (I : Ideal ActualEisensteinCubic.O) :
    ordinarySeriesTerm χ S s I = mobiusPrimeCoeff (ordinaryPrimeValue χ S s) I := by
  by_cases hI : Squarefree I
  · rw [mobiusPrimeCoeff,primeValueHom_squarefree _ I hI]
    simp only [ordinaryPrimeValue]
    rw [prod_cut_primes S hS (primeSet I) (fun P => χ.idealHom P*(Ideal.absNorm P:ℂ)^(-s)),
      primeNormTerm_prod,primeProduct_primeSet I hI]
    simp only [ordinarySeriesTerm,AngularIdealRow.mobiusWeight,CubicEisenstein.fullIdealWeight,ite_eq_right hI.ne_zero]
    ring
  · simp [ordinarySeriesTerm,AngularIdealRow.mobiusWeight,mobiusPrimeCoeff_nonsquarefree _ I hI,
      moebius_of_not_squarefree hI]

lemma dampedSeriesTerm_eq  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (I : Ideal ActualEisensteinCubic.O) :
    dampedSeriesTerm χ S s I = mobiusPrimeCoeff (dampedPrimeValue χ S s) I := by
  by_cases hI : Squarefree I
  · rw [mobiusPrimeCoeff,primeValueHom_squarefree _ I hI]
    simp only [dampedPrimeValue]
    rw [prod_cut_primes S hS (primeSet I) (fun P => (1-(1:ℂ)/(Ideal.absNorm P:ℂ))*(χ.idealHom P*(Ideal.absNorm P:ℂ)^(-s))),
      Finset.prod_mul_distrib,primeNormTerm_prod,
      prod_primeSet I (fun P => (1-(1:ℂ)/(Ideal.absNorm P:ℂ))),
      primeProduct_primeSet I hI]
    simp only [dampedSeriesTerm,ordinarySeriesTerm,AngularIdealRow.mobiusWeight,SixthPowerAverage.totientDensity,
      CubicEisenstein.fullIdealWeight,ite_eq_right hI.ne_zero]
    ring
  · simp [dampedSeriesTerm,ordinarySeriesTerm,AngularIdealRow.mobiusWeight,mobiusPrimeCoeff_nonsquarefree _ I hI,
      moebius_of_not_squarefree hI]


open ActualEisensteinCubic

lemma ordinaryPrimeValue_norm_le  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) :
    ‖ordinaryPrimeValue χ S s P.val‖≤(Ideal.absNorm P.val:ℝ)^(-s.re) := by
  by_cases hP : P.val∈S
  · simp only [ordinaryPrimeValue,ite_eq_left hP,norm_zero]
    positivity
  · simpa only [ordinaryPrimeValue,ite_eq_right hP,primeCharacterTerm,primeNormPower] using
      primeCharacterTerm_norm_le χ P s s.re le_rfl

lemma dampedPrimeValue_norm_le  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) :
    ‖dampedPrimeValue χ S s P.val‖≤(Ideal.absNorm P.val:ℝ)^(-s.re) := by
  by_cases hP : P.val∈S
  · simp only [dampedPrimeValue,ite_eq_left hP,norm_zero]
    positivity
  · change ‖if P.val∈S then 0 else primeDensity P*primeCharacterTerm χ P s‖≤_
    rw [ite_eq_right hP,norm_mul]
    exact (mul_le_mul_of_nonneg_right (primeDensity_norm_le_one P) (norm_nonneg _)).trans
      (by simpa using primeCharacterTerm_norm_le χ P s s.re le_rfl)

lemma ordinaryPrimeValue_summable  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : Summable (fun P : PrimeIdeal => ‖ordinaryPrimeValue χ S s P.val‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => ordinaryPrimeValue_norm_le χ S P s) (prime_reciprocal_series_summable s hs)

lemma dampedPrimeValue_summable  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : Summable (fun P : PrimeIdeal => ‖dampedPrimeValue χ S s P.val‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => dampedPrimeValue_norm_le χ S P s) (prime_reciprocal_series_summable s hs)

lemma ordinarySeries_euler  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,ordinarySeriesTerm χ S s I)=
      ∏'P : PrimeIdeal,(1-ordinaryPrimeValue χ S s P.val) := by
  simp_rw [ordinarySeriesTerm_eq χ S hS]
  exact mobiusPrimeCoeff_euler _ (ordinaryPrimeValue_summable χ S s hs)

lemma dampedSeries_euler  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,dampedSeriesTerm χ S s I)=
      ∏'P : PrimeIdeal,(1-dampedPrimeValue χ S s P.val) := by
  simp_rw [dampedSeriesTerm_eq χ S hS]
  exact mobiusPrimeCoeff_euler _ (dampedPrimeValue_summable χ S s hs)

lemma local_correction_identity  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) (hs : 0<s.re) :
    (1-dampedPrimeValue χ S s P.val)*(1+correctionTerm χ S P s)=
      1-ordinaryPrimeValue χ S s P.val := by
  rw [correctionTerm_factor χ S P s hs]
  by_cases hP : P.val∈S
  · simp [dampedPrimeValue,ordinaryPrimeValue,hP]
  · simp only [dampedPrimeValue,ordinaryPrimeValue,ite_eq_right hP]
    change (1-primeDensity P*primeCharacterTerm χ P s)*
      ((1-primeCharacterTerm χ P s)/(1-primeDensity P*primeCharacterTerm χ P s))=
      1-primeCharacterTerm χ P s
    exact mul_div_cancel₀ _ (correctionDenominator_ne_zero χ P s hs)

theorem actual_dirichlet_correction  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,ordinarySeriesTerm χ S s I)=
      eulerCorrection χ S s*(∑'I : Ideal ActualEisensteinCubic.O,dampedSeriesTerm χ S s I) := by
  rw [ordinarySeries_euler χ S hS s hs,dampedSeries_euler χ S hS s hs,mul_comm]
  have hd : Multipliable (fun P : PrimeIdeal => 1-dampedPrimeValue χ S s P.val) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (show Summable (fun P : PrimeIdeal => ‖-dampedPrimeValue χ S s P.val‖) by
        simpa only [norm_neg] using dampedPrimeValue_summable χ S s hs)
  have hc := multipliable_one_add_of_summable (correctionTerm_summable χ S s (by linarith))
  change _ = (∏' P : PrimeIdeal, (1-dampedPrimeValue χ S s P.val))*(∏' P : PrimeIdeal, (1+correctionTerm χ S P s))
  rw [←hd.tprod_mul hc]
  apply tprod_congr
  intro P
  exact (local_correction_identity χ S P s (by linarith)).symm
lemma ordinarySeriesTerm_outside  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ordinarySeriesTerm χ S s I=
      FiniteSFactor.outsideWeight S (AngularIdealRow.mobiusWeight χ) I*CubicEisenstein.fullIdealWeight s I := by
  unfold ordinarySeriesTerm outsideMask FiniteSFactor.outsideWeight
  split_ifs <;> simp

lemma dampedSeriesTerm_outside  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : dampedSeriesTerm χ S s I=
      AngularWeightedMellin.outsideWeight χ S I*CubicEisenstein.fullIdealWeight s I := by
  unfold dampedSeriesTerm ordinarySeriesTerm outsideMask AngularWeightedMellin.outsideWeight
    FiniteSFactor.outsideWeight AngularWeightedMellin.weightedMoebius
  split_ifs <;> ring

lemma ordinarySeries_eq_LSeries  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : (∑'I : Ideal ActualEisensteinCubic.O,ordinarySeriesTerm χ S s I)=
      LSeries (FiniteSFactor.outsideCoeff S (AngularIdealRow.mobiusWeight χ)) s := by
  simp_rw [ordinarySeriesTerm_outside]
  apply idealDirichlet_eq_LSeries
  intro I
  unfold FiniteSFactor.outsideWeight
  split_ifs
  · exact AngularSixthPower.mobiusWeight_norm_le_one χ I
  · simp
  exact hs

lemma dampedSeries_eq_LSeries  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : (∑'I : Ideal ActualEisensteinCubic.O,dampedSeriesTerm χ S s I)=
      LSeries (AngularWeightedMellin.weightedCoeff χ S) s := by
  simp_rw [dampedSeriesTerm_outside]
  exact idealDirichlet_eq_LSeries _ (AngularWeightedMellin.outsideWeight_norm_le_one χ S) s hs

theorem actual_LSeries_correction  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    LSeries (FiniteSFactor.outsideCoeff S (AngularIdealRow.mobiusWeight χ)) s=
      eulerCorrection χ S s*LSeries (AngularWeightedMellin.weightedCoeff χ S) s := by
  rw [←ordinarySeries_eq_LSeries χ S s hs,←dampedSeries_eq_LSeries χ S s hs]
  exact actual_dirichlet_correction χ S hS s hs


end OAI.CubicEisenstein.AngularEulerProducts
