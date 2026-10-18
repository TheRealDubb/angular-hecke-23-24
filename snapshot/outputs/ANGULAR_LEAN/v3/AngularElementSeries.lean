import AngularSeries
import OAI.NumberTheory.DirichletL.CubicSieve.ResidualSectors

/-!
# The actual element Dirichlet series and the six-unit reindexing

For every unit-compatible angular character, absolute convergence on Re(s)>1
is transported from its actual ideal Dirichlet series through the bijection
between nonzero elements and units times nonzero ideals. The element series is
then proved equal to six times the ideal series. Element summability is a
conclusion, not an assumed input to the reindexing theorem.

These are identities in the half-plane of absolute convergence. They do not
define an analytic continuation or assert a zero-free theorem below 1.
-/

namespace OAI.SevenEighths.Angular.AngularCharacter

noncomputable section
open scoped BigOperators Classical
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open UnrestrictedIdealReindex (NonzeroIdeal NonzeroElement)

/-- The physical angular element term, including its explicit zero mask. -/
def elementDirichletTerm (χ : AngularCharacter) (s : ℂ) (a : O) : ℂ :=
  χ.elementCoeff a / (Ideal.absNorm (Ideal.span ({a} : Set O)) : ℂ) ^ s

@[simp] theorem elementDirichletTerm_zero (χ : AngularCharacter) (s : ℂ) :
    χ.elementDirichletTerm s 0 = 0 := by
  simp [elementDirichletTerm]

theorem elementDirichletTerm_eq_idealTerm (χ : AngularCharacter) (s : ℂ) (a : O) :
    χ.elementDirichletTerm s a = χ.idealTerm s (Ideal.span ({a} : Set O)) := by
  simp only [elementDirichletTerm, idealTerm, idealHom_span]

theorem elementDirichletTerm_unit_mul (χ : AngularCharacter) (s : ℂ)
    (u : Oˣ) (a : O) :
    χ.elementDirichletTerm s ((u : O) * a) = χ.elementDirichletTerm s a := by
  rw [elementDirichletTerm, elementDirichletTerm, elementCoeff_unit_mul,
    Ideal.span_singleton_mul_left_unit u.isUnit]

theorem elementDirichletTerm_generator (χ : AngularCharacter) (s : ℂ)
    (I : Ideal O) :
    χ.elementDirichletTerm s (idealGenerator I) = χ.idealTerm s I := by
  rw [elementDirichletTerm_eq_idealTerm, span_idealGenerator]

theorem elementDirichletTerm_unit_generator (χ : AngularCharacter) (s : ℂ)
    (u : Oˣ) (I : NonzeroIdeal) :
    χ.elementDirichletTerm s ((u : O) * idealGenerator I.val) = χ.idealTerm s I.val := by
  rw [elementDirichletTerm_eq_idealTerm, UnrestrictedIdealReindex.span_unit_generator]

theorem elementDirichletTerm_unitIdealEquiv (χ : AngularCharacter) (s : ℂ)
    (p : Oˣ × NonzeroIdeal) :
    χ.elementDirichletTerm s (UnrestrictedIdealReindex.unitIdealEquiv p).val =
      χ.idealTerm s p.2.val := by
  change χ.elementDirichletTerm s ((p.1 : O) * idealGenerator p.2.val) = _
  exact χ.elementDirichletTerm_unit_generator s p.1 p.2

theorem summable_norm_elementDirichletTerm_nonzero (χ : AngularCharacter)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun a : NonzeroElement => ‖χ.elementDirichletTerm s a.val‖) := by
  let : Finite Oˣ := PrimaryIdealUnitReindex.finite_units
  have hI : Summable (fun I : NonzeroIdeal => ‖χ.idealTerm s I.val‖) :=
    (χ.summable_norm s hs).subtype _
  have hp : Summable (fun p : Oˣ × NonzeroIdeal =>
      ‖χ.elementDirichletTerm s (UnrestrictedIdealReindex.unitIdealEquiv p).val‖) := by
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
    constructor
    · intro u
      exact hI.congr (fun I =>
        (congrArg norm (χ.elementDirichletTerm_unitIdealEquiv s (u, I))).symm)
    · exact Summable.of_finite
  exact UnrestrictedIdealReindex.unitIdealEquiv.summable_iff.mp hp

/-- Absolute convergence is inherited from the actual ideal coefficients and
the finite unit fibers. No element-summability assumption is used. -/
theorem summable_norm_elementDirichletTerm (χ : AngularCharacter)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun a : O => ‖χ.elementDirichletTerm s a‖) := by
  have hnonzero := χ.summable_norm_elementDirichletTerm_nonzero s hs
  have hsupport : Function.support (fun a : O => ‖χ.elementDirichletTerm s a‖) ⊆
      {a : O | a ≠ 0} := by
    intro a ha hzero
    exact ha (by simp [hzero])
  exact ((hasSum_subtype_iff_of_support_subset hsupport).mp hnonzero.hasSum).summable

theorem summable_elementDirichletTerm (χ : AngularCharacter)
    (s : ℂ) (hs : 1 < s.re) : Summable (χ.elementDirichletTerm s) :=
  (χ.summable_norm_elementDirichletTerm s hs).of_norm

theorem norm_elementDirichletTerm_eq (χ : AngularCharacter) (s : ℂ)
    {a : O} (ha : a ≠ 0) :
    ‖χ.elementDirichletTerm s a‖ = ‖χ.elementCoeff a‖ /
      (Ideal.absNorm (Ideal.span ({a} : Set O)) : ℝ) ^ s.re := by
  have hI : Ideal.span ({a} : Set O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr ha
  have hN : (0 : ℝ) < Ideal.absNorm (Ideal.span ({a} : Set O)) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp : ‖(Ideal.absNorm (Ideal.span ({a} : Set O)) : ℂ) ^ s‖ =
      (Ideal.absNorm (Ideal.span ({a} : Set O)) : ℝ) ^ s.re := by
    simpa only [Complex.ofReal_natCast] using Complex.norm_cpow_eq_rpow_re_of_pos hN s
  rw [elementDirichletTerm, norm_div, hp]

theorem elementDirichletTerm_eq_embedding (χ : AngularCharacter) (s : ℂ) (a : O) :
    χ.elementDirichletTerm s a = χ.elementCoeff a /
      ((‖ConcreteTraceCRT.eisEmbedding a‖ ^ 2 : ℝ) : ℂ) ^ s := by
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  simp only [Complex.ofReal_natCast, elementDirichletTerm]

/-- The zero mask makes this norm expression valid even at the zero element. -/
theorem norm_elementDirichletTerm_eq_embedding (χ : AngularCharacter) (s : ℂ) (a : O) :
    ‖χ.elementDirichletTerm s a‖ = ‖χ.elementCoeff a‖ /
      (‖ConcreteTraceCRT.eisEmbedding a‖ ^ 2) ^ s.re := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [norm_elementDirichletTerm_eq χ s ha,
      ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]

theorem norm_elementDirichletTerm_le (χ : AngularCharacter) (s : ℂ)
    {a : O} (ha : a ≠ 0) :
    ‖χ.elementDirichletTerm s a‖ ≤
      1 / (Ideal.absNorm (Ideal.span ({a} : Set O)) : ℝ) ^ s.re := by
  rw [norm_elementDirichletTerm_eq χ s ha]
  exact div_le_div_of_nonneg_right (χ.norm_elementCoeff_le_one a)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem tsum_nonzero_idealTerm_eq_series (χ : AngularCharacter) (s : ℂ) :
    (∑' I : NonzeroIdeal, χ.idealTerm s I.val) = χ.series s := by
  rw [series_eq_tsum]
  apply tsum_subtype_eq_of_support_subset
  intro I hI hzero
  exact hI (by simp [hzero, idealTerm])

/-- Six associates of each nonzero Eisenstein ideal account for the exact
factor 6. Summability is supplied by the theorem above. -/
theorem tsum_elementDirichletTerm_eq_six_series (χ : AngularCharacter)
    (s : ℂ) (hs : 1 < s.re) :
    (∑' a : O, χ.elementDirichletTerm s a) = (6 : ℂ) * χ.series s := by
  rw [UnrestrictedIdealReindex.tsum_unit_invariant_of_zero (χ.elementDirichletTerm s)
    (χ.summable_elementDirichletTerm s hs) (χ.elementDirichletTerm_zero s)
    (χ.elementDirichletTerm_unit_mul s)]
  congr 1
  calc
    (∑' I : NonzeroIdeal, χ.elementDirichletTerm s (idealGenerator I.val)) =
        ∑' I : NonzeroIdeal, χ.idealTerm s I.val := by
      exact tsum_congr (fun I => χ.elementDirichletTerm_generator s I.val)
    _ = χ.series s := χ.tsum_nonzero_idealTerm_eq_series s

theorem hasSum_elementDirichletTerm (χ : AngularCharacter)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (χ.elementDirichletTerm s) ((6 : ℂ) * χ.series s) := by
  rw [← χ.tsum_elementDirichletTerm_eq_six_series s hs]
  exact (χ.summable_elementDirichletTerm s hs).hasSum

end
end OAI.SevenEighths.Angular.AngularCharacter
