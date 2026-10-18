import AngularFiniteRestoration
import AngularSeedRegularization
import AngularFamilyConjugation
import OAI.NumberTheory.DirichletL.Mellin.CompactScale

/-! Physical angular seed nonvanishing for Re(s)>23/24, with s=1 excluded
only for type zero. Nonzero angular types include that point.
This is weaker than the requested 8748389/10000000 bound. -/
noncomputable section
open scoped Classical BigOperators ContDiff Topology ComplexConjugate
namespace OAI.CubicEisenstein.AngularSeedNonvanishing
open ActualEisensteinCubic
open SevenEighths SevenEighths.Angular
open MeasureTheory Filter Complex
open CanonicalQuadraticSieve SecondPassArithmetic CanonicalRowCompletion
open AngularFiniteRestoration AngularEulerCorrection AngularSeedRegularization
open SmoothMobiusCorrection (PrimeIdeal)
open InitialMeanSquare (conjugateMonoid)

set_option maxHeartbeats 600000 in
theorem nonvanishing_of_initial_density (χ : AngularCharacter)
    (S : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀ P ∈ S, Prime P)
    (hcan : AngularInitialDensity.HasInitialCanonicalDensityAtRadius
      (conjugateMonoid χ.elementHom.toMonoidHom) S hbad)
    (z : ℂ) (hz : (23 : ℝ)/24 < z.re) (hpole : χ.k = 0 → z ≠ 1) :
    FamilyContinuation.LFunction χ z ≠ 0 := by
  let Q : Finset PrimeIdeal := S.attach.image (fun P => ⟨P.val, hSp P.val P.property⟩)
  have hQ : Q.image Subtype.val = S := by
    ext P
    simp [Q]
    exact hSp P
  let W : ℝ → ℂ := ConcreteCompactWeight.weight z
  have hW : ContDiff ℝ ∞ W := ConcreteCompactWeight.weight_smooth z
  have hWs : ∀ x, x ≤ 1 ∨ 2 ≤ x → W x = 0 := ConcreteCompactWeight.weight_support z
  let M : ℂ → ℂ := fun s =>
    (finiteEulerFactor χ Q s * eulerCorrection χ S s) *
      mellin (fun Z : ℝ => AngularWeightedMellin.weightedCompactSum χ S W Z⁻¹) (-s)
  have hE : AnalyticOnNhd ℂ (finiteEulerFactor χ Q) {s : ℂ | (23 : ℝ)/24 < s.re} :=
    (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt _)).mpr
      (finiteEulerFactor_differentiable χ Q).differentiableOn
  have hH : AnalyticOnNhd ℂ (eulerCorrection χ S) {s : ℂ | (23 : ℝ)/24 < s.re} :=
    (eulerCorrection_analytic χ S).mono (by
      intro s hs
      change 0 < s.re
      change (23 : ℝ)/24 < s.re at hs
      linarith)
  have hMellin := AngularWeightedMellin.weightedCompactMellin_analytic χ S hbad hSp hcan W hW hWs
  have hM : AnalyticOnNhd ℂ M {s : ℂ | (23 : ℝ)/24 < s.re} := (hE.mul hH).mul hMellin
  have hR : AnalyticOnNhd ℂ (regularizedL χ) {s : ℂ | (23 : ℝ)/24 < s.re} :=
    (regularizedL_analytic χ).mono (by
      intro s hs
      change 0 < s.re
      change (23 : ℝ)/24 < s.re at hs
      linarith)
  have hWanalytic := CompactMellinBridge.compact_weight_mellin_analytic W hW hWs ((23 : ℝ)/24)
  have hid (s : ℂ) (hs : 2 < s.re) : M s * FamilyContinuation.LFunction χ s = mellin W s := by
    simpa only [hQ] using compactMellin_correction_identity χ Q W hW hWs s hs
  by_cases hk : χ.k = 0
  · apply CompactMellinBridge.zero_free_of_regularized_identity_gt_two
      ((23 : ℝ)/24) (by norm_num) (FamilyContinuation.LFunction χ) (regularizedL χ)
      M (mellin W) hR hM hWanalytic ?_ ?_ z hz (hpole hk)
      (ConcreteCompactWeight.weight_mellin_ne_zero z)
    · intro s hs hs1
      exact regularizedL_eq χ s (by intro he; norm_num [he] at hs) hs1
    · intro s hs
      have h0 : s ≠ 0 := by intro he; norm_num [he] at hs
      have h1 : s ≠ 1 := by intro he; norm_num [he] at hs
      rw [regularizedL_eq χ s h0 h1]
      calc
        _ = (s - 1) * (M s * FamilyContinuation.LFunction χ s) := by ring
        _ = _ := congrArg (fun x : ℂ => (s - 1) * x) (hid s hs)
  · have hL : AnalyticOnNhd ℂ (FamilyContinuation.LFunction χ)
        {s : ℂ | (23 : ℝ)/24 < s.re} :=
      (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt _)).mpr
        (FamilyContinuation.LFunction_differentiable χ hk).differentiableOn
    exact CompactMellinBridge.zero_free_of_analytic_identity_gt_two
      ((23 : ℝ)/24) (by norm_num) (FamilyContinuation.LFunction χ) M (mellin W)
      hL hM hWanalytic (fun s hs => by simpa only [mul_comm] using hid s hs)
      z hz (ConcreteCompactWeight.weight_mellin_ne_zero z)

theorem physical_seed_nonnegative (χ : AngularCharacter) (angularOrder : ℕ)
    (hk : χ.k = (angularOrder : ℤ)) (z : ℂ)
    (hz : (23 : ℝ)/24 < z.re) (hpole : χ.k = 0 → z ≠ 1) :
    FamilyContinuation.LFunction χ z ≠ 0 := by
  have hkconj : χ.conjugate.k = -(angularOrder : ℤ) := by
    change -χ.k = -(angularOrder : ℤ)
    rw [hk]
  have he : χ.conjugate.elementHom.toMonoidHom = conjugateMonoid χ.elementHom.toMonoidHom := by
    ext a
    exact χ.conjugate_elementCoeff a
  have hcan := AngularInitialDensity.physical_initial_density χ.conjugate angularOrder hkconj
  rw [he] at hcan
  exact nonvanishing_of_initial_density χ
    (reflectionExcludedPrimes (AngularRayOrbit.orbitConductor χ.conjugate))
    (reflectionExcludedPrimes_bad (AngularRayOrbit.orbitConductor χ.conjugate))
    (reflectionExcludedPrimes_prime (AngularRayOrbit.orbitConductor χ.conjugate)) hcan z hz hpole

theorem physical_seed_all_types (χ : AngularCharacter) (z : ℂ)
    (hz : (23 : ℝ)/24 < z.re) (hpole : χ.k = 0 → z ≠ 1) :
    FamilyContinuation.LFunction χ z ≠ 0 := by
  by_cases hk : 0 ≤ χ.k
  · exact physical_seed_nonnegative χ χ.k.toNat (Int.toNat_of_nonneg hk).symm z hz hpole
  · have hkc : 0 ≤ χ.conjugate.k := by change 0 ≤ -χ.k; omega
    have hkne : χ.k ≠ 0 := by omega
    have hkcne : χ.conjugate.k ≠ 0 := by change -χ.k ≠ 0; omega
    have hn := physical_seed_nonnegative χ.conjugate χ.conjugate.k.toNat
      (Int.toNat_of_nonneg hkc).symm (conj z) (by simpa using hz)
      (fun he => (hkcne he).elim)
    simpa only [conj_conj] using
      (FamilyConjugation.conjugate_nonzero_iff χ hkne (conj z)).mp hn

end OAI.CubicEisenstein.AngularSeedNonvanishing
