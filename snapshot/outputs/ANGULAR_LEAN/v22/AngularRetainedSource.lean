import AngularInitialDensity

/-! Actual retained paired-source bounds on the original squarefree source
sectors. The base coefficients are explicit, with the proved initial-density
predicate and boundedness used separately. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.CubicEisenstein.AngularInitialDensity
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open InitialMeanSquare hiding outsideCanonicalDensity HasInitialCanonicalDensityAtRadius
open FirstPassCubeLabels (primeProductNorm firstLogDensity normalizedColumn columnLog)

theorem HasInitialCanonicalDensityAtRadius.retained_density (base : ActualEisensteinCubic.O →* ℂ) (hbase : ∀ x, ‖base x‖ ≤ 1)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S)
    (hcan : HasInitialCanonicalDensityAtRadius base S hbad)
    (a b σ θ ν η : ℝ) (hσ : 0 ≤ σ) (hν : 0 < ν) (hη : 0 < η)
    (hmargin : ν+θ ≤ σ-(1 : ℝ)/20) (A : ℝ) (hA : 0≤A) :
    ∃ J : ℕ,∀ V₁ V₂ : ℝ → ℂ,HasCompactSupport V₁ → HasCompactSupport V₂ →
      ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
      (∀s,V₁ s≠0→|s|≤A) → (∀s,V₂ s≠0→|s|≤A) →
      ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧ ∀ (D : ℕ) (Z : ℝ)
        (R : Finset (OutsidePrimeIndex S D)) (ray : SecondRayIndex) (j : SecondLogIndex)
        (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)),
        1 ≤ Z → Cpool*Z^E ≤ D →
        R ∈ boundedPrimeSupports (outsidePrime S D) Finset.univ (Z*Real.exp (initialErrorWindow a b)) →
        j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z (Z^(1+σ))) →
        initialRadial Z (Z^(1+σ)) (primeProductNorm (outsidePrime S D) R) j ≤ Z^θ →
        (∀ z ∈ T,Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
          z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2) →
        (∀z∈T,IsCoprime z.1 (∏P∈S,P)) →
        outsideCanonicalDensity base S hbad D ray R T V₁ V₂
          (initialLogColumn Z (primeProductNorm (outsidePrime S D) R) j) J ≤
        C*Z^η*(initialLogColumn Z (primeProductNorm (outsidePrime S D) R) j*initialLogLabel j)^2 := by
  obtain ⟨J,hJ⟩ := hcan η hη 20 A hA
  refine ⟨J,?_⟩
  intro V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂ hVrad₁ hVrad₂
  obtain ⟨Cc,Cpool,E,hCc,hCpool,hPE,hcanonical⟩ := hJ V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂ hVrad₁ hVrad₂
  obtain ⟨A,Vmax,hA,hVmax,hV₁,hV₂,hs₁,hs₂⟩ :=
    initial_two_windows_bounded V₁ V₂ hVc₁ hVc₂ hVs₁.continuous hVs₂.continuous
  obtain ⟨Z0,hZ0,hthreshold⟩ := initial_large_threshold a b (initialExcludedNorm S) ν
    (initialExcludedNorm_ge_one S) hν
  let Ce := initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3
  let K0 := initialPolynomialCap a b*Z0^17*Real.exp 2
  let C := Cc+Ce*(K0+1)+1
  have hI : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hCe : 0 ≤ Ce := mul_nonneg (initialElementaryConstant_nonneg A Vmax) (pow_nonneg hI _)
  have hcap := initialPolynomialCap_ge_one a b
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCcC : Cc ≤ C := by dsimp [C]; nlinarith
  have hCeC : Ce ≤ C := by dsimp [C]; nlinarith
  have hCeKC : Ce*K0 ≤ C := by dsimp [C]; nlinarith
  refine ⟨C,Cpool,E,hC,hCpool,hPE,?_⟩
  intro D Z R ray j T hZ hpool hR hj hrad hT hTc
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := base
  let X := initialLogColumn Z (primeProductNorm p R) j
  let lengthScale := initialLogLabel j
  let Kr := secondLogK j*Real.exp 2
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ Z^(1+σ) := Real.one_le_rpow hZ (by linarith)
  have hB := primeProductNorm_ge_one p hp R
  have hBpos := zero_lt_one.trans_le hB
  have hX : 0 < X := initialLogColumn_pos Z _ j hZp hBpos
  have hL : 1 ≤ lengthScale := initialLogLabel_ge_one j
  have hKr : 1 ≤ Kr := one_le_mul_of_one_le_of_one_le
    (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  have hZη : 1 ≤ Z^η := Real.one_le_rpow hZ hη.le
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := hbase
  have hΨ₁ : ∀ z,‖secondRayMinus Ψ ray z‖ ≤ 1 :=
    fun z => (secondRayMinus_norm_le Ψ ray z).trans (hΨ z)
  have hΨ₂ : ∀ z,‖secondRayPlus Ψ ray z‖ ≤ 1 :=
    fun z => (secondRayPlus_norm_le Ψ ray z).trans (hΨ z)
  have hTb : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ Kr := by
    intro z hz
    exact ⟨(hT z hz).1.1,(hT z hz).2.1,(hT z hz).2.2.2⟩
  have promote (d : ℝ) (hd : d ≤ C)
      (he : outsideCanonicalDensity base S hbad D ray R T V₁ V₂ X J ≤ d*(X*lengthScale)^2) :
      outsideCanonicalDensity base S hbad D ray R T V₁ V₂ X J ≤ C*Z^η*(X*lengthScale)^2 :=
    he.trans (mul_le_mul_of_nonneg_right (hd.trans (le_mul_of_one_le_right hC.le hZη)) (sq_nonneg _))
  by_cases hzlarge : Z0 ≤ Z
  · have hgeom := initial_large_bin_geometry p hp Finset.univ R a b Z σ θ ν (initialExcludedNorm S)
      j hZ (initialExcludedNorm_ge_one S) hR hj hσ hmargin (hthreshold Z hzlarge) hrad
    dsimp only at hgeom
    by_cases hxlarge : 1 ≤ X
    · exact (hcanonical D Z X lengthScale Kr R ray T hZ hpool hxlarge hL hKr
        hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2.1 hgeom.2.2.2.2.2 hT hTc).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcC (Real.rpow_nonneg hZp.le _)) (sq_nonneg _))
    · have hKL : Kr ≤ lengthScale := initial_subunit_row_le_label Z X lengthScale Kr
        (initialExcludedNorm S*primeProductNorm p R) ((1 : ℝ)/20) hZ (le_of_not_ge hxlarge)
        (zero_le_one.trans hL) (zero_le_one.trans hKr)
        (one_le_mul_of_one_le_of_one_le (initialExcludedNorm_ge_one S) hB)
        (by norm_num) (by simpa only [Kr,X,lengthScale,neg_div] using hgeom.2.2.2.2.2)
      apply promote Ce hCeC
      exact initial_subunit_density_bound p hp hcop hg (outsidePrime_odd S hbad D)
        (outsidePrime_injective S hbad D) Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        hΨ₁ hΨ₂ _ T V₁ V₂ X lengthScale Kr A Vmax J hX hL hKr hKL hA hVmax hV₁ hV₂ hs₁ hs₂ hTb
  · have hKmax := initialErrorRowBound_ge_one a b Z (Z^(1+σ)) hZ hH
    have hkr : Kr ≤ K0 := by
      have hbin := initial_bin_row_scale_le (Z*Real.exp (initialErrorWindow a b))
        (initialErrorRowBound a b Z (Z^(1+σ))) hKmax j hj
      have hcapZ := (initial_actual_bin_polynomial_caps a b Z (Z^(1+σ)) hZ hH).2
      have hpow : Z^17 ≤ Z0^17 := pow_le_pow_left₀ hZp.le (le_of_not_ge hzlarge) 17
      calc
        Kr ≤ (initialPolynomialCap a b*Z^17)*Real.exp 2 :=
          mul_le_mul_of_nonneg_right (hbin.trans hcapZ) (Real.exp_pos _).le
        _ ≤ K0 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hcap)) (Real.exp_pos _).le
    apply promote (Ce*Kr) ((mul_le_mul_of_nonneg_left hkr hCe).trans hCeKC)
    exact initial_density_elementary_squared_mass p hp hcop hg (outsidePrime_odd S hbad D)
      (outsidePrime_injective S hbad D) Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      hΨ₁ hΨ₂ _ T V₁ V₂ X lengthScale Kr A Vmax J hX hL hKr hA hVmax hV₁ hV₂ hs₁ hs₂ hTb


theorem HasInitialCanonicalDensityAtRadius.retained_source (base : ActualEisensteinCubic.O →* ℂ) (hbase : ∀ x, ‖base x‖ ≤ 1)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (hcan : HasInitialCanonicalDensityAtRadius base S hbad)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b σ θ ν η : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hσ : 0 ≤ σ) (hν : 0 < ν) (hη : 0 < η)
    (hmargin : ν+θ ≤ σ-(1 : ℝ)/20) :
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧
      ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → Cpool*Z^E ≤ D →
      let p := outsidePrime S D
      let hp := outsidePrime_ne_zero S hbad D
      let hcop := outsidePrime_coprime S hbad D
      let hg := outsidePrime_good S hbad D
      letI := outsidePrime_maximal S hbad D
      let Ψ := base
      let H := Z^(1+σ)
      let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
      let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray
            (initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z (initialErrorWindow a b) j))
            G G W H‖ else 0) ≤ C*H*Z^(35*η) := by
  obtain ⟨J,hJ⟩ := HasInitialCanonicalDensityAtRadius.retained_density base hbase S hbad hcan a b σ θ ν η hσ hν hη hmargin
    (initialErrorWindow a b+2+1) (by unfold initialErrorWindow; positivity)
  have hM : 0 ≤ initialErrorWindow a b := by unfold initialErrorWindow; positivity
  obtain ⟨windows,Ct,Cs,hCt,hCs,hwc,hws,hwb,ht⟩ :=
    initial_subbin_transfer_radius U hUc hUs g W (initialErrorWindow a b) hM hU hgs η hη 0 (2*J)
  obtain ⟨Ce,Cpool,E,hCe,hCpool,hPE,henergy⟩ := hJ (windows 5) (windows 6) (hwc 5) (hwc 6) (hws 5) (hws 6) (hwb 5) (hwb 6)
  obtain ⟨Cl,hCl,hlog⟩ := initial_row_log_budget η (initialPolynomialCap a b) hη (initialPolynomialCap_ge_one a b)
  let C0 := Ct*Real.exp 4*Ce*Cs*initialRayMass*Cl
  have hray := initialRayMass_nonneg
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨C0+1,Cpool,E,by linarith,hCpool,hPE,?_⟩
  intro D Z hZ hpool
  dsimp only
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := base
  let H := Z^(1+σ)
  let M := initialErrorWindow a b
  let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
  let Kmax := initialErrorRowBound a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let s := fun (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z M j)
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := hbase
  have hKmax : 1 ≤ Kmax := initialErrorRowBound_ge_one a b Z H hZ hH
  let B : SecondRayIndex → Finset (OutsidePrimeIndex S D) → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg (outsidePrime_injective S hbad D) (outsidePrime_odd S hbad D)
        (outsidePrime_primary S hbad D) Finset.univ R Ψ 1 ray K Z H M j (s R j)
        hZp hHp hΨ (Finset.filter_subset _ _))
  have hB (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) :=
    Classical.choose_spec
      (ht p hp hcop hg (outsidePrime_injective S hbad D) (outsidePrime_odd S hbad D)
        (outsidePrime_primary S hbad D) Finset.univ R Ψ 1 ray K Z H M j (s R j)
        hZp hHp hΨ (Finset.filter_subset _ _))
  let d := H*Real.exp 4*(Ce*Z^η)*Cs*(Kmax*Real.exp 2)^η
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hterm (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D))
      (hR : R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M))
      (j : SecondLogIndex) (hj : j ∈ secondLogBinBox (Z*Real.exp M) Kmax)
      (hlow : initialRadial Z H (primeProductNorm p R) j ≤ Z^θ) :
      initialSquarefreeBinCost p hp hcop hg Finset.univ R Ψ 1 ray K Z H M η j windows (B ray R j) ≤
        d/primeProductNorm p R*‖secondRayCoefficient ray‖ := by
    have hT := initial_squarefree_target_geometry p hp hg (outsidePrime_odd S hbad D)
      Finset.univ R K Z M j
    have hTe : ∀ z ∈ sourceIdealTarget ((s R j).image (sourceObservation p)),
        Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧ z.2 ≠ 0 ∧
        ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2 := by
      intro z hz
      exact ⟨(hT z hz).1,(hT z hz).2.1,(hT z hz).2.2.1,(hT z hz).2.2.2.trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num)) (normLogScale_pos _).le)⟩
    have hTc := initial_source_target_coprime p (∏P∈S,P)
      (CanonicalRowCompletion.outside_pool_coprime_excluded S D hbad hSp) (s R j)
    have he := henergy D Z R ray j _ hZ hpool hR hj hlow hTe hTc
    have he' :
        densityChildEnergy p hp hcop hg Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (1*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
          (sourceIdealTarget ((s R j).image (sourceObservation p)))
          (windows 5) (windows 6) (initialLogColumn Z (primeProductNorm p R) j)
          (initialLogColumn Z (primeProductNorm p R) j) (2*J) ≤
          (Ce*Z^η)*(initialLogColumn Z (primeProductNorm p R) j*initialLogLabel j)^2 := by
      simpa only [outsideCanonicalDensity,one_mul] using he
    exact initial_bin_cost_uniform p hp hcop hg Finset.univ R Ψ 1 ray K Z H M Kmax η Cs
      (Ce*Z^η) hZp hHp hKmax hη.le hCs (by positivity) j hj windows (B ray R j) (2*J) 0
      (hB ray R j).1 (hB ray R j).2.1 he'
  have hsum :
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
        ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
        if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray (s R j) G G W H‖ else 0) ≤
      Ct*(d*initialRayMass*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left
      (initial_harmonic_aggregation p (outsidePrime_injective S hbad D) Finset.univ
        (Z*Real.exp M) Kmax d hd
        (fun ray R j => if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          initialSquarefreeBinCost p hp hcop hg Finset.univ R Ψ 1 ray K Z H M η j windows (B ray R j)
          else 0) (by
          intro ray R hR j hj
          split_ifs with hlow
          · exact hterm ray R hR j hj hlow
          · have hRp := FirstPassCubeLabels.primeProductNorm_pos p hp R
            positivity)) hCt)
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ray hray
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with hlow
    · convert (hB ray R j).2.2 using 1 ;
        dsimp only [initialSquarefreeBinCost,s,G,B] ; ring
    · simp
  have hlogBound := hlog Z (Z*Real.exp M) Kmax hZ (by positivity) (zero_lt_one.trans_le hKmax)
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).1
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).2
  calc
    _ ≤ Ct*(d*initialRayMass*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := hsum
    _ = (Ct*Real.exp 4*Ce*Cs*initialRayMass)*H*Z^η*
        ((Kmax*Real.exp 2)^η*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := by dsimp [d]; ring
    _ ≤ (Ct*Real.exp 4*Ce*Cs*initialRayMass)*H*Z^η*(Cl*Z^(34*η)) :=
      mul_le_mul_of_nonneg_left hlogBound (by positivity)
    _ = C0*H*Z^(35*η) := by
      rw [show 35*η=η+34*η by ring,Real.rpow_add hZp]
      dsimp [C0]
      ring
    _ ≤ (C0+1)*H*Z^(35*η) := by
      gcongr
      linarith


end OAI.CubicEisenstein.AngularInitialDensity
