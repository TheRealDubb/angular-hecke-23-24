import AngularSieveDensity

/-! Canonical sieve energy for actual unit-compatible angular characters.
All reflection-model premises are discharged by the physical source chain. -/
noncomputable section
open scoped Classical BigOperators ContDiff
namespace OAI.CubicEisenstein.AngularPhysicalSieveEnergy
open ActualEisensteinCubic CanonicalRowCompletion
open CompletedGauss CanonicalQuadraticSieve SecondPassArithmetic CanonicalCubeSeparation
open SevenEighths.Angular AngularRayOrbit
open ConcreteTraceCRT (eisEmbedding)
local notation "Eis" => ActualEisensteinCubic.O

theorem physical_canonical_energy (χ : AngularCharacter) (angularOrder : ℕ)
    (hk : χ.k = -(angularOrder : ℤ)) (ε : ℝ) (hε : 0 < ε) (A : ℝ) (hA : 0 ≤ A) :
    let q := orbitConductor χ
    let S := reflectionExcludedPrimes q
    let hbad := reflectionExcludedPrimes_bad q
    ∃ d : ℕ, ∀ V : ℝ → ℂ, ContDiff ℝ ∞ V → (∀ s, V s ≠ 0 → |s| ≤ A) →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : ℕ) (Z : ℝ) (Ψ : Eis →* ℂ) (m : Eis)
        (labels : Finset (Ideal Eis)) (X F K t : ℝ),
        CanonicalStateCondition χ.elementHom.toMonoidHom (∏ P ∈ S, P)
          Z (canonicalDescentPadding ε) Ψ m labels X F K →
        1 < Z → Real.exp 9000 ≤ Z →
        2*‖eisEmbedding (excludedGenerator S)‖^2 ≤ Z^((1 : ℝ)/80) →
        Real.exp (radiusIter A 3000)*Z^3 ≤ D →
        outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K ≤
          C*Z^ε*(X*F)^2*(1+|t|)^d := by
  exact AngularSieveDensity.outsideLogEnergy_small_power angularOrder
    (reflectionExcludedPrimes (orbitConductor χ))
    (reflectionExcludedPrimes_prime (orbitConductor χ))
    (reflectionExcludedPrimes_bad (orbitConductor χ))
    χ.elementHom.toMonoidHom (fun a => χ.norm_elementCoeff_le_one a)
    1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor (orbitConductor χ)))
    (by norm_num) completedRamifiedStep_gt_one
    (reflectionLevelBound_ge_one (orbitConductor χ) (orbitConductor_ne_zero χ))
    (AngularSieveModels.actual_canonicalThetaModels χ angularOrder hk) ε hε A hA

end OAI.CubicEisenstein.AngularPhysicalSieveEnergy
