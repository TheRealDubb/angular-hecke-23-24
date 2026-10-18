import AngularProjectedMellin
import AngularFiniteAllOrderMellin
import OAI.NumberTheory.DirichletL.Eisenstein.EntireMellinProfile

/-! The actual finite projector at every positive derivative order has
literal rational-cusp data, a reflected finite sum, and an entire Mellin
transform. The cusp data use levelTwo, not an assumed levelThree lift.
The three physical scales and their full Bessel constants are retained. -/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Classical BigOperators MatrixGroups Topology

namespace OAI.CubicEisenstein.AngularProjectedReflection

open SevenEighths.Angular AngularFiniteProjector AngularProjectedMellin AngularCompletedCoefficient
open AngularHigherProfiles AngularHigherMellin AngularMellinOrderAlgebra
open AngularFiniteCuspSecondReflection AngularFiniteAllOrderReflection
open AngularSourceSecondMellin AngularFiniteCuspSecondMellin AngularProfileScaling
open CubicKubota EisensteinEmbedding ConcreteTraceCRT

local notation "Eis" => ActualEisensteinCubic.O

/-- The literal level-two character and lower matrix entry at order `order`. -/
def datumMultiplier (order : ℕ) (d : SourceCuspDatum) : ℂ :=
  star (levelTwoComplexCharacter d.gamma) * (-1 : ℂ) ^ order /
    (d.matrix 1 0) ^ (2 * order)

def datumDualProfile (order : ℕ) (d : SourceCuspDatum) : ℝ → ℂ :=
  zProfile (fun w => cubicSourceConjugateFunction (representative d.index • w))
    order d.dualPoint

/-- The reflected profile is the actual finite cusp source with its
scale 1,3,3 and unchanged full Bessel constant. -/
theorem datumDualProfile_scaled (order : ℕ) (d : SourceCuspDatum)
    (v : ℝ) (hv : 0 < v) :
    datumDualProfile order d v =
      ((sourceCuspScale d.index : ℂ)⁻¹) ^ order *
        zProfile (fun w => star ((sourceCuspCoefficients d.index).fullFunction
          (sourceCuspBesselConstant d.index) w)) order
          (d.dualPoint / (sourceCuspScale d.index : ℂ)) (v / sourceCuspScale d.index) := by
  change zProfile (fun w => star (cubicSourceResidualFunction (representative d.index • w)))
    order d.dualPoint v = _
  rw [zProfile_star]
  change star (barProfile (fun w => cubicSourceResidualFunction (representative d.index • w))
    order d.dualPoint v) = _
  rw [finite_barProfile_eq d.index order d.dualPoint v hv, zProfile_star]
  simp only [star_mul, star_pow, Complex.star_def, map_inv₀, Complex.conj_ofReal]
  ring

/-- Every order of the actual level-two cusp transport; no source
smoothness or cusp-existence premise remains. -/
theorem datum_reflection (order : ℕ) (d : SourceCuspDatum) (v : ℝ) (hv : 0 < v) :
    barProfile cubicSourceConjugateFunction order d.point v =
      reflected ((2 * order : ℕ) : ℂ) (datumMultiplier order d) d.heightScale
        (datumDualProfile order d) v := by
  have hp : 0 < (d.heightScale * v)⁻¹ := inv_pos.mpr (mul_pos d.heightScale_pos hv)
  have he := AngularSourceAllOrderReflection.cuspDerivative_of_transform order
    cubicSourceConjugateFunction d.matrix (representative d.index)
    (star (levelTwoComplexCharacter d.gamma))
    (fun w => by
      change cubicSourceConjugateFunction
        ((integralComplexMatrix (d.gamma : SL(2,Eis)) * representative d.index) • w) = _
      rw [mul_smul, cubicSourceConjugateFunction_levelTwo])
    d.lower_ne_zero v hv (fun m p hp => by
      convert! conjugate_finiteSplit_contDiffAt m d.index p hp using 1)
  rw [barProfile_positive _ _ _ _ hv, reflected, datumDualProfile,
    zProfile_positive _ _ _ _ hp]
  change _ = datumMultiplier order d * ((v : ℂ) ^ (-((2 * order : ℕ) : ℂ)) * _)
  rw [show d.point = d.matrix 0 0 / d.matrix 1 0 from rfl, he, order_prefactor]
  simp only [datumMultiplier, SourceCuspDatum.heightScale, SourceCuspDatum.dualPoint,
    one_div, mul_assoc, Nat.cast_mul, Nat.cast_ofNat, neg_mul]

theorem datum_mellin_entire (n : ℕ) (d : SourceCuspDatum) :
    (∀ s : ℂ, MellinConvergent
      (barProfile cubicSourceConjugateFunction (n + 1) d.point) s) ∧
    Differentiable ℂ (mellin (barProfile cubicSourceConjugateFunction (n + 1) d.point)) := by
  have hf := conjugate_profiles_regular n d.point
  have hg := finite_conjugate_profiles_regular d.index n d.dualPoint
  exact mellin_entire _ _ d.heightScale residualCuspDecayRate
    (residualCuspDecayRate / sourceCuspScale d.index) d.heightScale_pos
    residualCuspDecayRate_pos (div_pos residualCuspDecayRate_pos (sourceCuspScale_pos d.index))
    _ _ hf.1 hg.2.1 hf.2.2.1 hg.2.2.2 (datum_reflection (n + 1) d)

theorem datumDualProfile_mellin_entire (n : ℕ) (d : SourceCuspDatum) :
    (∀ s : ℂ, MellinConvergent (datumDualProfile (n + 1) d) s) ∧
    Differentiable ℂ (mellin (datumDualProfile (n + 1) d)) := by
  have hf := conjugate_profiles_regular n d.point
  have hg := finite_conjugate_profiles_regular d.index n d.dualPoint
  have hk : levelTwoComplexCharacter d.gamma ≠ 0 := by
    intro hz
    have hn := norm_levelTwoComplexCharacter d.gamma
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  have hA : datumMultiplier (n + 1) d ≠ 0 :=
    order_prefactor_ne_zero _ _ (star_ne_zero.mpr hk) d.lower_ne_zero (n + 1)
  exact mellin_entire _ _ d.heightScale
    (residualCuspDecayRate / sourceCuspScale d.index) residualCuspDecayRate d.heightScale_pos
    (div_pos residualCuspDecayRate_pos (sourceCuspScale_pos d.index)) residualCuspDecayRate_pos
    _ _ hg.2.1 hf.1 hg.2.2.2 hf.2.2.1
    (reflected_nat_reverse (2 * (n + 1)) _ hA _ d.heightScale_pos _ _
      (datum_reflection (n + 1) d))

/-- Original rational-cusp construction discharges the data for every
actual Fourier translation, including the zero quotient class. -/
theorem translation_mellin_entire (n : ℕ) (c : Eis) (hc : c ≠ 0)
    (h : Eis ⧸ Ideal.span {c}) :
    (∀ s : ℂ, MellinConvergent
      (barProfile cubicSourceConjugateFunction (n + 1) (thetaFourierTranslation c h)) s) ∧
    Differentiable ℂ (mellin
      (barProfile cubicSourceConjugateFunction (n + 1) (thetaFourierTranslation c h))) := by
  rw [← finiteTwistCusp_point c hc h]
  exact datum_mellin_entire n (finiteTwistCusp c hc h)

def reflectedFiniteProjector (χ : AngularCharacter) (n : ℕ) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})] (v : ℝ) : ℂ :=
  ∑ h : Eis ⧸ Ideal.span {c},
    finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient (finiteResidueHom χ) c) h *
      reflected ((2 * (n + 1) : ℕ) : ℂ) (datumMultiplier (n + 1) (finiteTwistCusp c hc h))
        (finiteTwistCusp c hc h).heightScale
        (datumDualProfile (n + 1) (finiteTwistCusp c hc h)) v

theorem finiteProjector_reflection (χ : AngularCharacter) (n : ℕ) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})] (v : ℝ) (hv : 0 < v) :
    finiteProjector χ n c hc v = reflectedFiniteProjector χ n c hc v := by
  unfold finiteProjector reflectedFiniteProjector
  apply Finset.sum_congr rfl
  intro h hh
  rw [← finiteTwistCusp_point c hc h, datum_reflection (n + 1) _ v hv]

/-- Actual finite projector: all complex Mellin parameters converge and
the Mellin transform is entire. Finite interchange uses proved integrability. -/
theorem finiteProjector_mellin_entire (χ : AngularCharacter) (n : ℕ) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})] :
    (∀ s : ℂ, MellinConvergent (finiteProjector χ n c hc) s) ∧
    Differentiable ℂ (mellin (finiteProjector χ n c hc)) := by
  apply finite_mellin_entire
  intro h
  exact translation_mellin_entire n c hc h

theorem finiteProjector_mellin_sum (χ : AngularCharacter) (n : ℕ) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})] (s : ℂ) :
    mellin (finiteProjector χ n c hc) s =
      ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient (finiteResidueHom χ) c) h *
          mellin (barProfile cubicSourceConjugateFunction (n + 1) (thetaFourierTranslation c h)) s := by
  let weight := finiteAdditiveFourierCoeff (quotientTrace c hc)
    (fixedThetaQuotient (finiteResidueHom χ) c)
  have hi (h : Eis ⧸ Ideal.span {c}) : IntegrableOn
      (fun v : ℝ => (v : ℂ) ^ (s - 1) * (weight h *
        barProfile cubicSourceConjugateFunction (n + 1) (thetaFourierTranslation c h) v)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using
      ((translation_mellin_entire n c hc h).1 s).const_smul (weight h)
  unfold mellin finiteProjector
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun h hh => hi h)]
  apply Finset.sum_congr rfl
  intro h hh
  simpa only [mellin, smul_eq_mul] using mellin_const_smul
    (barProfile cubicSourceConjugateFunction (n + 1) (thetaFourierTranslation c h)) s (weight h)

/-- The reflected Mellin finite sum retains the literal lower entry,
level-two character, cusp representative and dual physical Z-profile. -/
theorem finiteProjector_mellin_reflection (χ : AngularCharacter) (n : ℕ) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})] (s : ℂ) :
    mellin (finiteProjector χ n c hc) s =
      ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient (finiteResidueHom χ) c) h *
          (datumMultiplier (n + 1) (finiteTwistCusp c hc h) *
            ((finiteTwistCusp c hc h).heightScale : ℂ) ^ (((2 * (n + 1) : ℕ) : ℂ) - s) *
              mellin (datumDualProfile (n + 1) (finiteTwistCusp c hc h))
                (((2 * (n + 1) : ℕ) : ℂ) - s)) := by
  rw [finiteProjector_mellin_sum]
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  rw [← finiteTwistCusp_point c hc h]
  rw [CompletedGauss.mellin_eq_of_positive_eq _ _ (datum_reflection (n + 1) (finiteTwistCusp c hc h)) s,
    reflected_mellin _ _ _ _ (finiteTwistCusp c hc h).heightScale_pos]

/-- Entire shifted physical Mellin transform. Its agreement with the
gamma-series formula, under the type and modulus conditions, is the frozen
v8 theorem `AngularProjectedMellin.finiteProjector_mellin`. -/
theorem finiteProjector_shifted_mellin_entire (χ : AngularCharacter) (n : ℕ) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})] :
    Differentiable ℂ (fun s => mellin (finiteProjector χ n c hc) (2 * s + (n : ℂ))) := by
  exact (finiteProjector_mellin_entire χ n c hc).2.comp
    ((differentiable_const (2 : ℂ)).mul differentiable_id |>.add_const (n : ℂ))

end OAI.CubicEisenstein.AngularProjectedReflection
