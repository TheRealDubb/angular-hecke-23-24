import AngularIdealRow
import AngularNonzeroSource

/-! Actual angular ideal-row mean square from the original physical Poisson
source, with its conjugated coefficient orientation retained exactly. -/
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.CubicEisenstein.AngularPoissonMoment
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration InitialMeanSquare
open CanonicalRowCompletion
open FirstPassCubeLabels (normalizedColumn columnLog)
open SevenEighths.Angular

theorem outside_mean_square_source (χ : AngularCharacter)
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (W : ℝ → ℂ) (a b Z Y : ℝ)
    (ha : 0 < a) (hZ : 0 < Z) (hY : 0 < Y)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hD : b*Z ≤ D) (T : Finset O)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0)
    (K : Finset (primePool (outsideSquarefreeIdeals S D)) →
      Finset (primePool (outsideSquarefreeIdeals S D)) → Finset O) :
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    let p := poolPrimary F
    let hp := poolPrimary_ne_zero F hF
    let hg := poolPrimary_good F hF
    letI : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
      intro i j hij
      apply Subtype.ext
      simpa only [p, poolPrimary_span F hF] using hij
    let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
    let Ψ := conjugateMonoid χ.elementHom.toMonoidHom
    (∑ z ∈ T, ‖AngularIdealRow.idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)/Z ≤
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y (fun C E => (K C E).erase 0)‖+
      (truncatedSecondZero p hg Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y K).re+
      ‖secondSourceTail p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y K‖-‖G ∅‖^2 := by
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let p := poolPrimary F
  let hp := poolPrimary_ne_zero F hF
  let hg := poolPrimary_good F hF
  let : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
    intro i j hij
    apply Subtype.ext
    simpa only [p, poolPrimary_span F hF] using hij
  let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
  have he := mobiusRow_finite_source p hg hp hinj (poolPrimary_odd F hF) Finset.univ
    χ.elementHom.toMonoidHom 1 G Y hY T hT hT0 K
  calc
    _ = ∑ z ∈ T, ‖mobiusRow p hg Finset.univ χ.elementHom.toMonoidHom 1 G z‖^2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z hz
      exact AngularIdealRow.outside_idealRowSum_initial_energy χ S D hbad hSp W a b Z ha hZ hs hW hD z
    _ ≤ _ := he


theorem outside_mean_square_source_with_errors
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃C : ℝ,0<C ∧ ∀(χ : AngularCharacter)
      (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
      (hSp : ∀P∈S,Prime P) (Z Y : ℝ),0<Z → 0<Y → b*Z≤D →
    ∀T : Finset O,(∀z∈T,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Y) → (∀z∈T,z≠0) →
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    let p := poolPrimary F
    let hp := poolPrimary_ne_zero F hF
    let hg := poolPrimary_good F hF
    letI : ∀i : primePool F,(Ideal.span {p i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
      intro i j hij
      apply Subtype.ext
      simpa only [p,poolPrimary_span F hF] using hij
    let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
    let Ψ := conjugateMonoid χ.elementHom.toMonoidHom
    (∑z∈T,‖AngularIdealRow.idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)/Z≤
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
        rowMajorant Y (fun _ _ => (initialErrorCutoff a b Z Y).erase 0)‖+
      C*Y-‖G ∅‖^2 := by
  obtain ⟨C,hC,h⟩ := initial_normalized_errors W a b ha hs hW
  refine ⟨C,hC,?_⟩
  intro χ S D hbad hSp Z Y hZ hY hD T hT hT0
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let p := poolPrimary F
  let hp := poolPrimary_ne_zero F hF
  let hg := poolPrimary_good F hF
  let : ∀i : primePool F,(Ideal.span {p i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
    intro i j hij
    apply Subtype.ext
    simpa only [p,poolPrimary_span F hF] using hij
  let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
  let Ψ := conjugateMonoid χ.elementHom.toMonoidHom
  let K : Finset (primePool F)→Finset (primePool F)→Finset O := fun _ _ => initialErrorCutoff a b Z Y
  have he := h p hp hg hinj (poolPrimary_odd F hF) Finset.univ Ψ
    (conjugateMonoid_norm_le_one χ.elementHom.toMonoidHom (fun a => χ.norm_elementCoeff_le_one a)) Z Y hZ hY
  have hm := outside_mean_square_source χ S D hbad hSp W a b Z Y ha hZ hY hs hW hD T hT hT0 K
  have hz := Complex.re_le_norm (truncatedSecondZero p hg Finset.univ Ψ 1 1 1
    (fun V => star (G V)) rowMajorant Y K)
  change ‖truncatedSecondZero p hg Finset.univ Ψ 1 1 1 (fun V => star (G V)) rowMajorant Y K‖+
    ‖secondSourceTail p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V)) rowMajorant Y K‖≤C*Y at he
  apply hm.trans
  linarith


theorem outside_mean_square_of_canonical_density_at_radius (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀ P ∈ S,Prime P)
    (hcan : AngularInitialDensity.HasInitialCanonicalDensityAtRadius (conjugateMonoid χ.elementHom.toMonoidHom) S hbad)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (σ ε : ℝ) (hσ : (1 : ℝ)/20 < σ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → b*Z ≤ D →
      ∀ T : Finset ActualEisensteinCubic.O,
      (∀ z ∈ T,(Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Z^(1+σ)) →
      (∀ z ∈ T,z ≠ 0) →
      (∑ z ∈ T,‖AngularIdealRow.idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
        (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2) ≤ C*Z*(Z^(1+σ))*Z^ε := by
  let g0 := initialLogProfile W a b ha hs hW
  let g := conjugateProfile g0
  let M := initialErrorWindow a b
  have hM : 0 ≤ M := by dsimp [M,initialErrorWindow]; positivity
  have hg0 : ∀ t,g0 t ≠ 0 → |t| ≤ M := initialLogProfile_support W a b ha hs hW
  have hg : ∀ t,g t ≠ 0 → |t| ≤ M := conjugateProfile_support_bound g0 M hg0
  obtain ⟨U,hUc,hUs,hUeq,hUsupp,hUzero⟩ := FourierBridge.exists_complex_smooth_cutoff M hM
  have hU : ∀ t,g t ≠ 0 → U t=1 := fun t ht => hUeq t (hg t ht)
  obtain ⟨Cs,Cpool,E,hCs,hCpool,hE,hsource⟩ := AngularInitialDensity.HasInitialCanonicalDensityAtRadius.nonzero_source_bound
    (conjugateMonoid χ.elementHom.toMonoidHom)
    (conjugateMonoid_norm_le_one _ (fun a => χ.norm_elementCoeff_le_one a)) S hbad hSp hcan
    U hUc hUs g rowMajorant a b σ ε hU hg hσ hε
  obtain ⟨Ce,hCe,herrors⟩ := outside_mean_square_source_with_errors W a b ha hs hW
  refine ⟨Cs+Ce,by positivity,?_⟩
  intro D Z hZ hD T hT hT0
  let Db : ℕ := max D ⌈Cpool*Z^E⌉₊
  have hDDb : D ≤ Db := le_max_left _ _
  have hpool : Cpool*Z^E ≤ (Db : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right D ⌈Cpool*Z^E⌉₊)
  have hDb : b*Z ≤ (Db : ℝ) := hD.trans (by exact_mod_cast hDDb)
  let p := outsidePrime S Db
  let hp := outsidePrime_ne_zero S hbad Db
  let hg := outsidePrime_good S hbad Db
  let hinj := outsidePrime_injective S hbad Db
  let := outsidePrime_maximal S hbad Db
  let Ψ := conjugateMonoid χ.elementHom.toMonoidHom
  let H := Z^(1+σ)
  let G := fun V => normalizedColumn p (fun T => g0 (columnLog p Z T)) V
  let MS := ∑ z ∈ T,‖AngularIdealRow.idealRowSum (outsideIdealsUpTo S Db) (outsideIdealsUpTo_ne_bot S Db)
    (outside_good S Db hbad) χ (fun n => W (n/Z)) z‖^2
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hεZ : 1 ≤ Z^ε := Real.one_le_rpow hZ hε.le
  have he := herrors χ S Db hbad hSp Z H hZp hHp hDb T hT hT0
  have hsrc := hsource Db Z hZ hpool
  have hstar : (fun V => star (G V)) =
      (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V) := by
    funext V
    exact star_normalizedColumn p g0 Z V
  have hsrc' :
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
        rowMajorant H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖ ≤ Cs*H*Z^ε := by
    rw [hstar]
    exact hsrc
  change MS/Z ≤
    ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
      rowMajorant H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖+Ce*H-‖G ∅‖^2 at he
  have herr : Ce*H ≤ Ce*H*Z^ε := le_mul_of_one_le_right (mul_nonneg hCe.le hHp.le) hεZ
  have hnorm : MS/Z ≤ (Cs+Ce)*H*Z^ε := by
    nlinarith [sq_nonneg ‖G ∅‖]
  have hfinal := (div_le_iff₀ hZp).mp hnorm
  have hMS : (∑ z ∈ T,‖AngularIdealRow.idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)=MS := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [AngularIdealRow.outside_row_cutoff_stable S hbad hDDb χ W b Z hZp (fun t ht => (hs ht).2) hD z]
  rw [hMS]
  convert hfinal using 1 ; dsimp only [H] ; ring

theorem physical_outside_mean_square (χ : AngularCharacter) (angularOrder : ℕ)
    (hk : χ.k = (angularOrder : ℤ))
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (σ ε : ℝ) (hσ : (1 : ℝ)/20 < σ) (hε : 0 < ε) :
    let q := AngularRayOrbit.orbitConductor χ.conjugate
    let S := reflectionExcludedPrimes q
    let hbad := reflectionExcludedPrimes_bad q
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ) (Z : ℝ), 1 ≤ Z → b*Z ≤ D →
      ∀ T : Finset O,
      (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Z^(1+σ)) →
      (∀ z ∈ T, z ≠ 0) →
      (∑ z ∈ T, ‖AngularIdealRow.idealRowSum (outsideIdealsUpTo S D)
        (outsideIdealsUpTo_ne_bot S D) (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)
        ≤ C*Z*(Z^(1+σ))*Z^ε := by
  have hkconj : χ.conjugate.k = -(angularOrder : ℤ) := by
    change -χ.k = -(angularOrder : ℤ)
    rw [hk]
  have he : χ.conjugate.elementHom.toMonoidHom = conjugateMonoid χ.elementHom.toMonoidHom := by
    ext a
    exact χ.conjugate_elementCoeff a
  have hcan := AngularInitialDensity.physical_initial_density χ.conjugate angularOrder hkconj
  rw [he] at hcan
  exact outside_mean_square_of_canonical_density_at_radius χ
    (reflectionExcludedPrimes (AngularRayOrbit.orbitConductor χ.conjugate))
    (reflectionExcludedPrimes_bad (AngularRayOrbit.orbitConductor χ.conjugate))
    (reflectionExcludedPrimes_prime (AngularRayOrbit.orbitConductor χ.conjugate))
    hcan W a b ha hs hW σ ε hσ hε

end OAI.CubicEisenstein.AngularPoissonMoment
