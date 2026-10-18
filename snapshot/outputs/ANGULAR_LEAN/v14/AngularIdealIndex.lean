import AngularStratumSeries

/-! Exact reindexing of the actual angular stratum model from supported
physical frequencies to the ideal-index series used in branch energy.
The original primary-support restriction and finite phase selector remain. -/

noncomputable section
open scoped Classical BigOperators ContDiff MatrixGroups

namespace OAI.CubicEisenstein.AngularIdealIndex

open SevenEighths.Angular ActualEisensteinCubic CompletedGauss CompletedDyadic
open ConcreteTraceCRT CubicJacobiGlobal LocalReflectionBrackets
open AngularStratumModel AngularStratumSeries AngularControlledStratum

local notation "Eis" => ActualEisensteinCubic.O
variable {c : Eis} {h : Eis ⧸ Ideal.span {c}} (G : FixedFourierGeometry c h)

theorem angularArray_tsum_full_index (n : ℕ) (v : G.PhaseResidue)
    (w : CuspIdealIndex → ℂ) :
    (∑' t : CuspIdealIndex,
      angularArray G n v t.1 t.2.1 t.2.2.1.val t.2.2.2.val * w t) =
    ∑' t : ThetaFullIndex,
      angularArray G n v t.1 t.2.1 t.2.2.1.val t.2.2.2.val * w (thetaFullToIdealIndex t) := by
  have he := fixedCuspArrayWithPhase_tsum_full_index (fun _ => G.shape.index)
    (fun u => G.staticPhase v u)
    (fun t : CuspIdealIndex =>
      alpha (fixedCuspArrayIndex t.1 t.2.1 t.2.2.1.val t.2.2.2.val)^n * w t)
  change (∑' t : CuspIdealIndex, G.array v t.1 t.2.1 t.2.2.1.val t.2.2.2.val *
    (alpha (fixedCuspArrayIndex t.1 t.2.1 t.2.2.1.val t.2.2.2.val)^n * w t)) =
    ∑' t : ThetaFullIndex, G.array v t.1 t.2.1 t.2.2.1.val t.2.2.2.val *
      (alpha (fixedCuspArrayIndex t.1 t.2.1 t.2.2.1.val t.2.2.2.val)^n *
        w (thetaFullToIdealIndex t)) at he
  calc
    _ = ∑' t : CuspIdealIndex, G.array v t.1 t.2.1 t.2.2.1.val t.2.2.2.val *
        (alpha (fixedCuspArrayIndex t.1 t.2.1 t.2.2.1.val t.2.2.2.val)^n * w t) := by
      apply tsum_congr
      intro t
      rw [angularArray]
      ring
    _ = _ := he
    _ = _ := by
      apply tsum_congr
      intro t
      rw [angularArray]
      ring

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N : Eis}

/-- Literal constructed stratum equality on the ideal index set. This is
an exact model identity; the later finite grouping and energy are separate. -/
theorem angularReflectedValue_eq_ideal_series (n : ℕ)
    (D : ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (j : ι → ℕ) (W : ℝ → ℂ) (X : ℝ) :
    angularReflectedValue n D G.shape hp G.denominator_ne_zero hg j W X =
    (thetaDerivativeScalar⁻¹ * fixedRadialCoefficientScalar *
      G.shape.stratumShapeFactor (G.c0 * ∏ i, p i)) *
      ∑' t : CuspIdealIndex,
        (angularModelRowPhase G n D hp hg j t.1 t.2.1 *
          ∑ e : ι → Fin 3,
            angularArray G n (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1) * D.U))
              t.1 t.2.1 t.2.2.1.val t.2.2.2.val *
            reflectedBranch (fun i => Ideal.span {p i}) hg j e
              (primaryGenerator t.2.2.1.val) (primaryGenerator t.2.2.2.val)) /
          ((ramifiedScale 1 completedRamifiedStep t.2.1 *
            Real.sqrt (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ) : ℝ) : ℂ) *
        AngularReflectionKernel.paperKernel n (Vstar W)
          ((X / (G.levelScale * (Ideal.absNorm (Ideal.span {∏ i, p i}) : ℝ)^2)) *
            (ramifiedScale 1 completedRamifiedStep t.2.1)^3 *
            (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ)^3) := by
  rw [angularReflectedValue_eq_model_series]
  apply congrArg (fun z : ℂ => (thetaDerivativeScalar⁻¹ * fixedRadialCoefficientScalar *
    G.shape.stratumShapeFactor (G.c0 * ∏ i, p i)) * z)
  let v : G.PhaseResidue := Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1) * D.U)
  let w : CuspIdealIndex → ℂ := fun t =>
    (angularModelRowPhase G n D hp hg j t.1 t.2.1 *
      ∑ e : ι → Fin 3, reflectedBranch (fun i => Ideal.span {p i}) hg j e
        (primaryGenerator t.2.2.1.val) (primaryGenerator t.2.2.2.val)) /
      ((ramifiedScale 1 completedRamifiedStep t.2.1 *
        Real.sqrt (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ) : ℝ) : ℂ) *
    AngularReflectionKernel.paperKernel n (Vstar W)
      ((X / (G.levelScale * (Ideal.absNorm (Ideal.span {∏ i, p i}) : ℝ)^2)) *
        (ramifiedScale 1 completedRamifiedStep t.2.1)^3 *
        (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ)^3)
  calc
    _ = ∑' t : ThetaFullIndex,
        angularArray G n v t.1 t.2.1 t.2.2.1.val t.2.2.2.val * w (thetaFullToIdealIndex t) := by
      apply tsum_congr
      intro t
      simp only [w, v, thetaFullToIdealIndex, primaryCubePairToMellinIndex, ←Finset.mul_sum]
      ring
    _ = ∑' t : CuspIdealIndex,
        angularArray G n v t.1 t.2.1 t.2.2.1.val t.2.2.2.val * w t :=
      (angularArray_tsum_full_index G n v w).symm
    _ = _ := by
      apply tsum_congr
      intro t
      simp only [w, v, ←Finset.mul_sum]
      ring

end OAI.CubicEisenstein.AngularIdealIndex
