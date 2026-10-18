import AngularPhysicalSmoothedReflection
import OAI.NumberTheory.DirichletL.RowCompletion.FixedCuspBranches

/-! Exact extra angular phase in the physical reflection scalar. In a fixed
cusp stratum it is independent of the finite Fourier variable. This retains
the original level-two character to the first power. -/

noncomputable section
open scoped Classical BigOperators MatrixGroups

namespace OAI.CubicEisenstein.AngularCuspPhase

open SevenEighths.Angular CompletedGauss CubicKubota EisensteinEmbedding ConcreteTraceCRT
open AngularProjectedReflection AngularDualRadialCoefficients
open AngularPhysicalSmoothedReflection

local notation "Eis" => ActualEisensteinCubic.O

def datumAngularPhase (d : SourceCuspDatum) : ℂ :=
  (-(d.heightScale : ℂ) / (d.matrix 1 0)^2) *
    (thetaFrequencyScale / star thetaFrequencyScale)

def stratumAngularPhase {H : SL(2,Eis)} (s : FixedCuspShape H) (c : Eis) : ℂ :=
  -(eisEmbedding (s.upper 0 0))^2 * (alpha c)^(-2 : ℤ) *
    (thetaFrequencyScale / star thetaFrequencyScale)

theorem datumMultiplier_succ (n : ℕ) (d : SourceCuspDatum) :
    datumMultiplier (n + 1) d =
      d.multiplier * ((-1 : ℂ) / (d.matrix 1 0)^2)^n := by
  simp only [datumMultiplier, SourceCuspDatum.multiplier, Nat.mul_add,
    Nat.mul_one, pow_add, pow_mul, pow_one, div_pow]
  ring

theorem datum_geometric_scalar_split (n : ℕ) (d : SourceCuspDatum) :
    datumMultiplier (n + 1) d * (d.heightScale : ℂ)^(n + 1) *
        ((thetaBesselScale / sourceCuspRadialScale d.index : ℝ) : ℂ)^(n + 2) =
      (d.multiplier * (d.heightScale : ℂ) * (sourceCuspScale d.index : ℂ)^2) *
        ((-(d.heightScale : ℂ) / (d.matrix 1 0)^2) *
          (sourceCuspScale d.index : ℂ))^n := by
  rw [datumMultiplier_succ, sourceCusp_scale_ratio]
  simp only [pow_add, pow_one, neg_div, neg_mul]
  ring

theorem extraScale_normalization (j : Fin 3) :
    (sourceCuspScale j : ℂ) * extraScale j /
        (-2 * Real.pi * Complex.I * star thetaFrequencyScale) =
      thetaFrequencyScale / star thetaFrequencyScale := by
  have hS : (sourceCuspScale j : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne'
  have hF : thetaFrequencyScale ≠ 0 := norm_pos_iff.mp thetaBesselScale_pos
  unfold extraScale
  field_simp [hS, hF, star_ne_zero.mpr hF, Real.pi_ne_zero, Complex.I_ne_zero]

theorem datum_normalized_scalar_split (n : ℕ) (d : SourceCuspDatum) :
    ((datumMultiplier (n + 1) d * (d.heightScale : ℂ)^(n + 1) *
        ((thetaBesselScale / sourceCuspRadialScale d.index : ℝ) : ℂ)^(n + 2)) *
        extraScale d.index^n) /
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n) =
    (d.multiplier * (d.heightScale : ℂ) * (sourceCuspScale d.index : ℂ)^2 /
      thetaDerivativeScalar) * datumAngularPhase d^n := by
  rw [datum_geometric_scalar_split]
  calc
    _ = (d.multiplier * (d.heightScale : ℂ) * (sourceCuspScale d.index : ℂ)^2 /
        thetaDerivativeScalar) *
      ((-(d.heightScale : ℂ) / (d.matrix 1 0)^2) *
        ((sourceCuspScale d.index : ℂ) * extraScale d.index /
          (-2 * Real.pi * Complex.I * star thetaFrequencyScale)))^n := by
        simp only [mul_pow, div_pow]; ring
    _ = _ := by rw [extraScale_normalization]; rfl

theorem datumAngularPhase_norm (d : SourceCuspDatum) :
    ‖datumAngularPhase d‖ = 1 := by
  have hz : ‖d.matrix 1 0‖ ≠ 0 := norm_ne_zero_iff.mpr d.lower_ne_zero
  have hF : ‖thetaFrequencyScale‖ ≠ 0 := thetaBesselScale_pos.ne'
  simp only [datumAngularPhase, norm_mul, norm_div, norm_neg, norm_pow, norm_star]
  rw [Complex.norm_of_nonneg d.heightScale_pos.le, SourceCuspDatum.heightScale]
  field_simp

theorem datum_height_phase {H : SL(2,Eis)} (s : FixedCuspShape H)
    (g : levelTwo) (c : Eis) (hc : c ≠ 0)
    (hg : ((g : SL(2,Eis)) * H) 1 0 = c) :
    ((s.datum g (by rwa [hg])).heightScale : ℂ) /
        ((s.datum g (by rwa [hg])).matrix 1 0)^2 =
      (eisEmbedding (s.upper 0 0))^2 * (alpha c)^(-2 : ℤ) := by
  rw [s.datum_heightScale, s.datum_matrix, integralComplexMatrix_apply,
    upper_right_removed_bottom _ _ s.lower_zero, hg, map_mul]
  have hC := eisEmbedding_ne_zero hc
  have hN : (‖eisEmbedding c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hC)
  have hU := eisEmbedding_ne_zero s.lower_unit.ne_zero
  have hd : eisEmbedding (s.upper 0 0) * eisEmbedding (s.upper 1 1) = 1 := by
    rw [←map_mul, upper_diagonal_product _ s.lower_zero, map_one]
  have hp : eisEmbedding (s.upper 0 0)^2 * eisEmbedding (s.upper 1 1)^2 = 1 := by
    rw [←mul_pow, hd, one_pow]
  simp only [alpha, FiniteGaussPhase.angularFactor, zpow_neg, zpow_ofNat,
    Complex.ofReal_pow]
  field_simp [hC, hN, hU]
  linear_combination -hp

theorem datumAngularPhase_eq_stratum {H : SL(2,Eis)} (s : FixedCuspShape H)
    (g : levelTwo) (c : Eis) (hc : c ≠ 0)
    (hg : ((g : SL(2,Eis)) * H) 1 0 = c) :
    datumAngularPhase (s.datum g (by rwa [hg])) = stratumAngularPhase s c := by
  unfold datumAngularPhase stratumAngularPhase
  rw [neg_div, datum_height_phase s g c hc hg]
  ring

/-- The entire angular correction is constant on a fixed lower-entry stratum;
the character of g is exactly the original first-power multiplier. -/
theorem normalized_scalar_common_row {H : SL(2,Eis)} (s : FixedCuspShape H)
    (g : levelTwo) (c : Eis) (hc : c ≠ 0)
    (hg : ((g : SL(2,Eis)) * H) 1 0 = c) (n : ℕ) :
    let d := s.datum g (by rwa [hg])
    ((datumMultiplier (n + 1) d * (d.heightScale : ℂ)^(n + 1) *
        ((thetaBesselScale / sourceCuspRadialScale d.index : ℝ) : ℂ)^(n + 2)) *
        extraScale d.index^n) /
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n) =
    ((sourceCuspScale s.index : ℂ)^2 / thetaDerivativeScalar) *
      s.stratumShapeFactor c * stratumAngularPhase s c^n *
        star (levelTwoComplexCharacter g) := by
  dsimp only
  rw [datum_normalized_scalar_split, datumAngularPhase_eq_stratum s g c hc hg]
  have hheight : (s.datum g (by rwa [hg])).heightScale =
      (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
    rw [s.datum_heightScale, hg,
      ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  rw [hheight, s.datum_common_row_factor g c hc hg]
  change _ * ((sourceCuspScale s.index : ℂ)^2) / _ * _ = _
  ring

theorem stratumAngularPhase_product {H : SL(2,Eis)} (s : FixedCuspShape H)
    (a b : Eis) (n : ℕ) :
    stratumAngularPhase s (a * b)^n =
      stratumAngularPhase s a^n * ((alpha b)^(-2 : ℤ))^n := by
  simp only [stratumAngularPhase, alpha_mul, mul_zpow, mul_pow]
  ring

theorem full_frequency_angle (p : ThetaFullIndex) (n : ℕ) :
    alpha (thetaFullFrequency p)^n =
      alpha (p.1 : Eis)^n * (alpha ActualEisensteinCubic.lambda)^(p.2.1 * n) *
        alpha (CompletedGauss.primaryGenerator p.2.2.1.val)^n *
          alpha (CompletedGauss.primaryGenerator p.2.2.2.val)^(3 * n) := by
  have hpow (a : Eis) (m : ℕ) : alpha (a^m) = alpha a^m := by
    induction m with
    | zero => simp only [pow_zero, alpha_one]
    | succ m hm => rw [pow_succ, alpha_mul, hm, pow_succ]
  simp only [thetaFullFrequency, alpha_mul, hpow, mul_pow, pow_mul]

end OAI.CubicEisenstein.AngularCuspPhase
