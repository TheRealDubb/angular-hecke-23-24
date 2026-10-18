import AngularPhysicalFiberIdentity

/-! Actual angular completed-row model membership and its physical quadratic
energy estimate. The full character occurs in the sum, and only its finite
residue factor occurs in the constructed fiber's periodic coefficients. -/
noncomputable section
open scoped Classical BigOperators ContDiff

namespace OAI.CubicEisenstein.AngularPhysicalRowEnergy
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open CanonicalRowCompletion CanonicalRowCompletion.ActualFiber
open SevenEighths.Angular AngularCompletedCoefficient
local notation "Eis" => ActualEisensteinCubic.O

def finiteConductor (χ : AngularCharacter) : ℕ := Ideal.absNorm χ.modulus

theorem finiteConductor_ne_zero (χ : AngularCharacter) : finiteConductor χ ≠ 0 := by
  intro hz
  exact χ.modulus_ne_bot (Ideal.absNorm_eq_zero_iff.mp hz)

theorem finiteResidue_factors_fixedConductor (χ : AngularCharacter) :
    CanonicalCoefficientClass.FactorsModulo
      (CanonicalCoefficientClass.fixedBaseConductor (finiteConductor χ)) (finiteResidueHom χ) := by
  intro x y hxy
  apply finiteResidueHom_factorsModulo χ x y
  exact (Ideal.span_singleton_absNorm_le χ.modulus) (Ideal.mul_le_left hxy)

theorem actual_exactModels (angularOrder q : ℕ) (hq : q ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {reflectionConductor q})]
    (χ : AngularCharacter) (hk : χ.k = -(angularOrder : ℤ))
    (hχ : CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q)
      (finiteResidueHom χ))
    (m : Eis) (hm : m ≠ 0) (F : Ideal Eis) (hF : Squarefree F) (u : Eisˣ)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (K X : ℝ) (hX : 0 < X) (rows : Finset (Ideal Eis))
    (hrows : ∀ I ∈ rows, I ≠ 0 ∧ K/2 ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ K) :
    AngularCompletedModels.HasExactCompletedModels angularOrder
      (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
      rows K X 1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q))
      F (maskIdeal q m F) W
      (fun J => rowTwist χ.elementHom.toMonoidHom (maskElement q m)
        (ConcretePrimeRowBridge.idealGenerator F) (u.val * ConcretePrimeRowBridge.idealGenerator J))
      (4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar) := by
  let models := fun (R : Ideal Eis) (hR : R ∈ rows) =>
    AngularPhysicalFiberData.reflectedFiber angularOrder q hq m hm rows R F
      (hrows R hR).1 hF (fun I hI => (hrows I hI).1) u K
      (finiteResidueHom χ) (finiteResidueHom_norm_le_one χ)
  apply AngularCompletedModels.hasExactCompletedModels_of_representative_identity
    angularOrder _ rows K X 1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q))
    F (maskIdeal q m F) W _ _ models
  intro R hR J hJ
  exact AngularPhysicalFiberIdentity.completedT_eq_reflectedFiber_idealValue angularOrder q hq m hm
    rows R F (hrows R hR).1 hF (fun I hI => (hrows I hI).1) u χ hk hχ K
    (fun I hI => (hrows I hI).2) ⟨J,hJ⟩ W a b ha hsupp hW X hX

/-- A physical mean-square estimate, with uniformity over bounded finite
residue factors at the indicated fixed conductor and fixed angular order.
No model-membership hypothesis is left in the conclusion or inputs. -/
theorem completed_angular_row_energy (angularOrder q : ℕ) (hq : q ≠ 0)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ε : ℝ) (hδ : 0 < deltaLoss) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (χ : AngularCharacter), χ.k = -(angularOrder : ℤ) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q)
        (finiteResidueHom χ) →
      ∀ (m : Eis), m ≠ 0 → ∀ (F : Ideal Eis), Squarefree F → ∀ (u : Eisˣ),
      ∀ (K X : ℝ), 1 ≤ K → 1 ≤ X → ∀ rows : Finset (Ideal Eis),
      (∀ I ∈ rows, I ≠ 0 ∧ K/2 ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ K) →
      (∑ I ∈ rows, ‖completedT
        (rowTwist χ.elementHom.toMonoidHom (maskElement q m)
          (ConcretePrimeRowBridge.idealGenerator F) (u.val * ConcretePrimeRowBridge.idealGenerator I))
        W X‖^2) ≤
      C * (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq) : ℝ)^2 *
        ‖(4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar : ℂ)‖^2 *
        (Ideal.absNorm (maskIdeal q m F) : ℝ)^ε *
        (K*(Ideal.absNorm (maskIdeal q m F) : ℝ))^(10*deltaLoss+ε) *
        (K+K^2*(Ideal.absNorm (maskIdeal q m F) : ℝ)/X) := by
  letI : Finite (Eis ⧸ Ideal.span {reflectionConductor q}) :=
    ConcreteTraceCRT.finite_quotient_span (reflectionConductor_ne_zero q hq)
  letI : Fintype (Eis ⧸ Ideal.span {reflectionConductor q}) := Fintype.ofFinite _
  obtain ⟨C,hC,henergy⟩ := AngularCompletedModels.completed_energy_of_exact_models angularOrder
    W a b ha hsupp hW deltaLoss ε 1 completedRamifiedStep
    (fixedCuspLevelBound (reflectionConductor q)) hδ hε (by norm_num)
    completedRamifiedStep_gt_one (reflectionLevelBound_ge_one q hq)
  refine ⟨C,hC,?_⟩
  intro χ hk hχ m hm F hF u K X hK hX rows hrows
  exact henergy _ K X hK hX rows F (maskIdeal q m F) (maskIdeal_ne_zero q m hm F hF.ne_zero)
    (mask_bad q m F) (fun I hI => ⟨(hrows I hI).1,(hrows I hI).2.2⟩) _ _
    (actual_exactModels angularOrder q hq χ hk hχ m hm F hF u W a b ha hsupp hW
      K X (by linarith) rows hrows)

/-- Every actual character of type -n admits the required finite conductor;
the periodicity premise of the uniform fixed-conductor estimate is discharged. -/
theorem completed_character_row_energy (χ : AngularCharacter) (angularOrder : ℕ)
    (hk : χ.k = -(angularOrder : ℤ))
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ε : ℝ) (hδ : 0 < deltaLoss) (hε : 0 < ε) :
    let q := finiteConductor χ
    let hq := finiteConductor_ne_zero χ
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : Eis), m ≠ 0 → ∀ (F : Ideal Eis), Squarefree F → ∀ (u : Eisˣ),
      ∀ (K X : ℝ), 1 ≤ K → 1 ≤ X → ∀ rows : Finset (Ideal Eis),
      (∀ I ∈ rows, I ≠ 0 ∧ K/2 ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ K) →
      (∑ I ∈ rows, ‖completedT
        (rowTwist χ.elementHom.toMonoidHom (maskElement q m)
          (ConcretePrimeRowBridge.idealGenerator F) (u.val * ConcretePrimeRowBridge.idealGenerator I))
        W X‖^2) ≤
      C * (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq) : ℝ)^2 *
        ‖(4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar : ℂ)‖^2 *
        (Ideal.absNorm (maskIdeal q m F) : ℝ)^ε *
        (K*(Ideal.absNorm (maskIdeal q m F) : ℝ))^(10*deltaLoss+ε) *
        (K+K^2*(Ideal.absNorm (maskIdeal q m F) : ℝ)/X) := by
  obtain ⟨C,hC,h⟩ := completed_angular_row_energy angularOrder (finiteConductor χ)
    (finiteConductor_ne_zero χ) W a b ha hsupp hW deltaLoss ε hδ hε
  exact ⟨C,hC,h χ hk (finiteResidue_factors_fixedConductor χ)⟩

end OAI.CubicEisenstein.AngularPhysicalRowEnergy
