import AngularDyadicModels

/-! A completed mean-square bound for actual angular row coefficients over
arbitrary finite nonzero ideal rows up to K. All dyadic model membership is
discharged; the angular order and finite conductor are fixed. -/
noncomputable section
open scoped Classical BigOperators ContDiff

namespace OAI.CubicEisenstein.AngularPhysicalMeanSquare
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open CanonicalRowCompletion CanonicalRowCompletion.ActualFiber
open SevenEighths.Angular AngularCompletedCoefficient AngularPhysicalRowEnergy
local notation "Eis" => ActualEisensteinCubic.O

theorem actual_exactDyadicModels (angularOrder q : ℕ) (hq : q ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {reflectionConductor q})]
    (χ : AngularCharacter) (hk : χ.k = -(angularOrder : ℤ))
    (hχ : CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q)
      (finiteResidueHom χ))
    (m : Eis) (hm : m ≠ 0) (F : Ideal Eis) (hF : Squarefree F) (u : Eisˣ)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (K X : ℝ) (hX : 0 < X) (rows : Finset (Ideal Eis))
    (hrows : ∀ I ∈ rows, I ≠ 0) :
    AngularDyadicModels.HasExactCompletedDyadicModels angularOrder
      (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
      rows K X 1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q))
      F (maskIdeal q m F) W
      (fun J => rowTwist χ.elementHom.toMonoidHom (maskElement q m)
        (ConcretePrimeRowBridge.idealGenerator F) (u.val * ConcretePrimeRowBridge.idealGenerator J))
      (4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar) := by
  intro j hj
  exact actual_exactModels angularOrder q hq χ hk hχ m hm F hF u W a b ha hsupp hW
    ((2 : ℝ)^j) X hX (completedRowDyad rows j) (completedRowDyad_bounds rows j hrows)

theorem completed_angular_mean_square (angularOrder q : ℕ) (hq : q ≠ 0)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (χ : AngularCharacter), χ.k = -(angularOrder : ℤ) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q)
        (finiteResidueHom χ) →
      ∀ (m : Eis), m ≠ 0 → ∀ (F : Ideal Eis), Squarefree F → ∀ (u : Eisˣ),
      ∀ (K X : ℝ), 1 ≤ K → 1 ≤ X → ∀ rows : Finset (Ideal Eis),
      (∀ I ∈ rows, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ K) →
      (∑ I ∈ rows, ‖completedT
        (rowTwist χ.elementHom.toMonoidHom (maskElement q m)
          (ConcretePrimeRowBridge.idealGenerator F) (u.val * ConcretePrimeRowBridge.idealGenerator I))
        W X‖^2) ≤
      C * (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq) : ℝ)^2 *
        ‖(4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar : ℂ)‖^2 *
        (K*(Ideal.absNorm (maskIdeal q m F) : ℝ))^ε *
        (K+K^2*(Ideal.absNorm (maskIdeal q m F) : ℝ)/X) := by
  let : Finite (Eis ⧸ Ideal.span {reflectionConductor q}) :=
    ConcreteTraceCRT.finite_quotient_span (reflectionConductor_ne_zero q hq)
  let : Fintype (Eis ⧸ Ideal.span {reflectionConductor q}) := Fintype.ofFinite _
  obtain ⟨C,hC,henergy⟩ := AngularDyadicModels.completed_mean_square_of_exact_reflection angularOrder
    W a b ha hsupp hW ε 1 completedRamifiedStep
    (fixedCuspLevelBound (reflectionConductor q)) hε (by norm_num)
    completedRamifiedStep_gt_one (reflectionLevelBound_ge_one q hq)
  refine ⟨C,hC,?_⟩
  intro χ hk hχ m hm F hF u K X hK hX rows hrows
  exact henergy _ K X hK hX rows F (maskIdeal q m F) (maskIdeal_ne_zero q m hm F hF.ne_zero)
    (mask_bad q m F) hrows _ _
    (actual_exactDyadicModels angularOrder q hq χ hk hχ m hm F hF u W a b ha hsupp hW
      K X (by linarith) rows (fun I hI => (hrows I hI).1))

theorem completed_character_mean_square (χ : AngularCharacter) (angularOrder : ℕ)
    (hk : χ.k = -(angularOrder : ℤ))
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε : ℝ) (hε : 0 < ε) :
    let q := finiteConductor χ
    let hq := finiteConductor_ne_zero χ
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : Eis), m ≠ 0 → ∀ (F : Ideal Eis), Squarefree F → ∀ (u : Eisˣ),
      ∀ (K X : ℝ), 1 ≤ K → 1 ≤ X → ∀ rows : Finset (Ideal Eis),
      (∀ I ∈ rows, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ K) →
      (∑ I ∈ rows, ‖completedT
        (rowTwist χ.elementHom.toMonoidHom (maskElement q m)
          (ConcretePrimeRowBridge.idealGenerator F) (u.val * ConcretePrimeRowBridge.idealGenerator I))
        W X‖^2) ≤
      C * (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq) : ℝ)^2 *
        ‖(4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar : ℂ)‖^2 *
        (K*(Ideal.absNorm (maskIdeal q m F) : ℝ))^ε *
        (K+K^2*(Ideal.absNorm (maskIdeal q m F) : ℝ)/X) := by
  obtain ⟨C,hC,h⟩ := completed_angular_mean_square angularOrder (finiteConductor χ)
    (finiteConductor_ne_zero χ) W a b ha hsupp hW ε hε
  exact ⟨C,hC,h χ hk (finiteResidue_factors_fixedConductor χ)⟩

end OAI.CubicEisenstein.AngularPhysicalMeanSquare
