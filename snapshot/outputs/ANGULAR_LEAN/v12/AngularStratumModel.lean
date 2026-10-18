import AngularControlledStratum
import OAI.NumberTheory.DirichletL.Eisenstein.ReflectionFibers

/-! Exact angular coefficients in the actual conductor-stratum model. The
column array depends only on fixed geometry/residue, unit, valuation and two
column ideals. The conductor angular phase is placed in the row phase. -/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators Topology ContDiff MatrixGroups

namespace OAI.CubicEisenstein.AngularStratumModel

open SevenEighths.Angular ActualEisensteinCubic ConcreteTraceCRT
open CompletedGauss CompletedDyadic CubicKubota CubicJacobiGlobal
open LocalReflectionBrackets ShortDraftCusp
open AngularPhysicalSmoothedReflection AngularCuspPhase AngularControlledStratum

local notation "Eis" => ActualEisensteinCubic.O

theorem alpha_norm_le_one (a : Eis) : ‖alpha a‖ ≤ 1 := by
  by_cases ha : a = 0
  · subst a
    simp [alpha, FiniteGaussPhase.angularFactor]
  · exact (norm_alpha ha).le

def angularArray {c : Eis} {h : Eis ⧸ Ideal.span {c}}
    (G : FixedFourierGeometry c h) (n : ℕ) (v : G.PhaseResidue)
    (u : Eisˣ) (m : ℕ) (I J : Ideal Eis) : ℂ :=
  alpha (fixedCuspArrayIndex u m I J)^n * G.array v u m I J

theorem angularArray_norm_le_one {c : Eis} {h : Eis ⧸ Ideal.span {c}}
    (G : FixedFourierGeometry c h) (n : ℕ) (v : G.PhaseResidue)
    (u : Eisˣ) (m : ℕ) (I J : Ideal Eis) :
    ‖angularArray G n v u m I J‖ ≤ 1 := by
  rw [angularArray, norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (alpha_norm_le_one _))).trans
      (G.array_norm_le_one v u m I J)

theorem stratumAngularPhase_norm {H : SL(2,Eis)} (s : FixedCuspShape H)
    (c : Eis) (hc : c ≠ 0) : ‖stratumAngularPhase s c‖ = 1 := by
  have hu : ‖eisEmbedding (s.upper 0 0)‖ = 1 := by
    rcases s.upper_unit with ⟨u, hu⟩
    rw [←hu]
    exact GaussGeneratorTransport.norm_eisEmbedding_unit u
  have hF : ‖thetaFrequencyScale‖ ≠ 0 := thetaBesselScale_pos.ne'
  rw [stratumAngularPhase, norm_mul, norm_mul, norm_neg, norm_pow, hu,
    one_pow, norm_zpow, norm_alpha hc, one_zpow, one_mul, norm_div, norm_star]
  simpa only [one_mul] using div_self hF

variable {c : Eis} {h : Eis ⧸ Ideal.span {c}} (G : FixedFourierGeometry c h)
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N : Eis}

def angularModelRowPhase (n : ℕ) (D : ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (j : ι → ℕ) (u : Eisˣ) (m : ℕ) : ℂ :=
  stratumAngularPhase G.shape (G.c0 * ∏ i, p i)^n *
    D.modelRowPhase G.shape hp hg j u m

theorem angularModelRowPhase_norm (n : ℕ)
    (D : ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * G.c0 ∣ N) (hr : lambda^2 ∣ (∏ i, p i) - 1)
    (hbase : if G.mode then lambda^2 ∣ G.a0 - 1 else lambda^2 ∣ G.c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (u : Eisˣ) (m : ℕ) :
    ‖angularModelRowPhase G n D hp hg j u m‖ = 1 := by
  have hc : G.c0 * ∏ i, p i ≠ 0 :=
    mul_ne_zero G.denominator_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  rw [angularModelRowPhase, norm_mul, norm_pow, stratumAngularPhase_norm G.shape _ hc,
    one_pow, one_mul, D.modelRowPhase_norm hN hr hbase G.shape hp hg hchar j hj]

/-- Literal model coefficient, with the angular factor split between the
row phase and the column array. No row parameter occurs in angularArray. -/
theorem angular_model_coefficient (n : ℕ)
    (D : ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ)
    (u : Eisˣ) (m : ℕ) (I J : Ideal Eis) :
    stratumAngularPhase G.shape (G.c0 * ∏ i, p i)^n *
      alpha (fixedCuspArrayIndex u m I J)^n *
      (G.shape.amplitude u m I J *
        (star D.fixedFactor * A4BadPhase G.c0 G.denominator_ne_zero
          (D.matrix (fun _ => 1) 1 1) D.U (G.dualNumerator u m I J)) *
        D.bracketProduct hp hg j (G.dualNumerator u m I J)) =
    angularModelRowPhase G n D hp hg j u m *
      ∑ e : ι → Fin 3,
        angularArray G n (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1) * D.U)) u m I J *
        reflectedBranch (fun i => Ideal.span {p i}) hg j e (primaryGenerator I) (primaryGenerator J) := by
  rw [G.stratum_model_coefficient D hp hg j u m I J]
  simp only [angularModelRowPhase, angularArray, ←mul_assoc, ←Finset.mul_sum]
  ring

end OAI.CubicEisenstein.AngularStratumModel
