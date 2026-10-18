import AngularPhysicalSieveEnergy
import OAI.NumberTheory.DirichletL.MeanSquare.PoissonSource

/-! Actual angular Mobius-weighted ideal rows and their exact physical
prime-pool and radial-normalization identities. -/
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.CubicEisenstein.AngularIdealRow
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic InitialMeanSquare
open FirstPassCubeLabels (normalizedColumn columnLog primeProductNorm)
open FirstCauchyArithmetic (supportMobius)
open SevenEighths.Angular

def mobiusWeight (χ : AngularCharacter) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ) * χ.idealHom I

theorem mobiusWeight_zero_of_not_squarefree (χ : AngularCharacter) (I : Ideal O)
    (hI : ¬ Squarefree I) : mobiusWeight χ I = 0 := by
  rw [mobiusWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hI]
  simp

theorem elementHom_prod {ι : Type*} (p : ι → O) (S : Finset ι)
    (χ : AngularCharacter) :
    χ.elementHom.toMonoidHom (∏ i ∈ S, p i) = χ.idealHom (∏ i ∈ S, Ideal.span {p i}) := by
  rw [← FiniteGaussPhase.span_finset_prod, χ.idealHom_span]
  rfl

noncomputable def idealRowSum
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (χ : AngularCharacter) (W : ℕ → ℂ) (u : O) : ℂ :=
  ∑ I ∈ F,
    mobiusWeight χ I * W (Ideal.absNorm I) *
      idealSexticRow F hFpos hFgood I u

theorem idealRowSum_filter_squarefree (F : Finset (Ideal O))
    (hFp : ∀ I ∈ F, I ≠ ⊥)
    (hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      goodLambda ∉ P) (χ : AngularCharacter) (W : ℕ → ℂ) (z : O) :
    idealRowSum F hFp hFg χ W z =
    idealRowSum (F.filter Squarefree)
      (fun I hI => hFp I (Finset.mem_filter.mp hI).1)
      (fun I hI => hFg I (Finset.mem_filter.mp hI).1) χ W z := by
  unfold idealRowSum
  calc
    _ = ∑ I ∈ F.filter Squarefree,
        mobiusWeight χ I * W (Ideal.absNorm I) *
          idealSexticRow F hFp hFg I z := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro I hIF hIn
      have hs : ¬ Squarefree I := fun h => hIn (Finset.mem_filter.mpr ⟨hIF,h⟩)
      rw [mobiusWeight_zero_of_not_squarefree χ I hs, zero_mul, zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [idealSexticRow_ambient F (F.filter Squarefree) hFp
        (fun J hJ => hFp J (Finset.mem_filter.mp hJ).1) hFg
        (fun J hJ => hFg J (Finset.mem_filter.mp hJ).1) I
        (Finset.mem_filter.mp hI).1 hI z]

theorem idealRowSum_eq_mobiusRow (F : Finset (Ideal O)) (hF : ∀I∈F,Admissible I)
    (χ : AngularCharacter) (W : ℕ→ℂ) (z : O) :
    let hFpos := fun I hI => (hF I hI).1
    let hFgood := fun I hI P hP => ((hF I hI).2.2 P hP).1
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    idealRowSum F hFpos hFgood χ W z=
      mobiusRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ χ.elementHom.toMonoidHom 1
        (selectedIdealTest F W) z := by
  dsimp only
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hP : (fun i:primePool F => Ideal.span {poolPrimary F i})=(fun i:primePool F => i.val) :=
    funext (poolPrimary_span F hF)
  unfold idealRowSum
  rw [sum_selected_ideals F (fun I hI => (hF I hI).2.1)]
  unfold mobiusRow
  apply Finset.sum_congr rfl
  intro S hS
  have ht := elementHom_prod (poolPrimary F) S χ
  simp only [hP] at ht
  by_cases hs : (∏i∈S,i.val)∈F
  · rw [ite_eq_left hs]
    simp only [inputColumn,selectedIdealTest,ite_eq_left hs,mul_one,ht]
    have hm : rowCoprimeMask (fun i => Ideal.span {poolPrimary F i}) S 1=1 := by
      simp [rowCoprimeMask,Ideal.IsPrime.one_notMem]
    rw [hm,mul_one]
    simp only [supportMobius,hP,mobiusWeight,idealSexticRow,pool_support_product]
    ring
  · rw [ite_eq_right hs]
    simp only [inputColumn,selectedIdealTest,ite_eq_right hs,mul_zero,zero_mul]

theorem outside_idealRowSum_initial_energy (χ : AngularCharacter)
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (W : ℝ → ℂ) (a b Z : ℝ) (ha : 0 < a) (hZ : 0 < Z)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hD : b*Z ≤ D) (z : O) :
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    ‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2/Z =
    ‖mobiusRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ χ.elementHom.toMonoidHom 1
      (normalizedColumn (poolPrimary F)
        (fun T => initialLogProfile W a b ha hs hW (columnLog (poolPrimary F) Z T))) z‖^2 := by
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  rw [idealRowSum_filter_squarefree]
  change ‖idealRowSum F (fun I hI => (hF I hI).1)
    (fun I hI P hP => ((hF I hI).2.2 P hP).1) χ (fun n => W (n/Z)) z‖^2/Z = _
  rw [idealRowSum_eq_mobiusRow F hF]
  have ht : selectedIdealTest F (fun n => W (n/Z)) =
      fun T => W (primeProductNorm (poolPrimary F) T/Z) := by
    funext T
    exact selectedIdealTest_outside S D hbad hSp W b Z hZ (fun t ht => (hs ht).2) hD T
  rw [ht]
  exact (mobiusRow_initial_energy (poolPrimary F) (poolPrimary_good F hF)
    (poolPrimary_ne_zero F hF) Finset.univ χ.elementHom.toMonoidHom 1 z Z hZ W a b ha hs hW).symm

theorem outside_row_cutoff_stable (S : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ S)
    {D E : ℕ} (hDE : D ≤ E) (χ : AngularCharacter)
    (W : ℝ → ℂ) (b Z : ℝ) (hZ : 0 < Z)
    (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*Z ≤ D) (z : O) :
    idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z =
    idealRowSum (outsideIdealsUpTo S E) (outsideIdealsUpTo_ne_bot S E)
      (outside_good S E hbad) χ (fun n => W (n/Z)) z := by
  have hsub := outsideIdealsUpTo_mono S hDE
  unfold idealRowSum
  calc
    _ = ∑ I ∈ outsideIdealsUpTo S D,
        mobiusWeight χ I * W ((Ideal.absNorm I : ℝ)/Z) *
        idealSexticRow (outsideIdealsUpTo S E) (outsideIdealsUpTo_ne_bot S E)
          (outside_good S E hbad) I z := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [idealSexticRow_ambient (outsideIdealsUpTo S D) (outsideIdealsUpTo S E)
        (outsideIdealsUpTo_ne_bot S D) (outsideIdealsUpTo_ne_bot S E)
        (outside_good S D hbad) (outside_good S E hbad) I hI (hsub hI) z]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro I hIE hID
      have hw : W ((Ideal.absNorm I : ℝ)/Z) = 0 := by
        by_contra hn
        have hbound : (Ideal.absNorm I : ℝ) ≤ D :=
          ((div_le_iff₀ hZ).mp (hW _ hn)).trans hD
        have hnat : Ideal.absNorm I ≤ D := by exact_mod_cast hbound
        obtain ⟨hpos,_,hS⟩ := mem_outsideIdealsUpTo.mp hIE
        exact hID (mem_outsideIdealsUpTo.mpr ⟨hpos,hnat,hS⟩)
      rw [hw,mul_zero,zero_mul]


end OAI.CubicEisenstein.AngularIdealRow
