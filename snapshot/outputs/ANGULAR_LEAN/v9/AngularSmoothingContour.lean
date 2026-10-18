import AngularShiftedBesselReflection
import AngularProjectedReflection

/-! Global contour shift for the actual angular normalization. The initial
identity retains its nontrivial derivative scalar. Left-line integrability
is explicit here and is discharged separately by physical dual reflection. -/

noncomputable section
open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

namespace OAI.CubicEisenstein.AngularSmoothingContour

open CompletedGauss AngularShiftedBesselReflection AngularProjectedReflection
open AngularFiniteProjector SevenEighths.Angular

theorem continuedDirichlet_eq_shift (n : ℕ) (F : ℝ → ℂ) (q : ℝ) (s : ℂ) :
    continuedDirichlet n F q s = continuedBesselDirichlet F q (s + (n : ℂ) / 2) := by
  unfold continuedDirichlet continuedBesselDirichlet
  congr 2
  ring

theorem continuedDirichlet_differentiable (n : ℕ) (F : ℝ → ℂ) (q : ℝ) (hq : 0 < q)
    (hF : Differentiable ℂ (mellin F)) :
    Differentiable ℂ (continuedDirichlet n F q) := by
  have h := (continuedBesselDirichlet_differentiable F q hq hF).comp
    (show Differentiable ℂ (fun s : ℂ => s + (n : ℂ) / 2) from by fun_prop)
  simpa only [Function.comp_def, ← continuedDirichlet_eq_shift] using h

theorem continuedDirichlet_strip_bound (n : ℕ) (F : ℝ → ℂ) (q : ℝ) (hq : 0 < q)
    (a b : ℝ) (hF : ∀ s : ℂ, MellinConvergent F s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Set.Icc a b →
      ‖continuedDirichlet n F q s‖ ≤ C * Real.exp (2 * Real.pi * |s.im|) := by
  obtain ⟨C, hC, hb⟩ := continuedBesselDirichlet_strip_bound F q hq
    (a + (n : ℝ) / 2) (b + (n : ℝ) / 2) (hF _) (hF _)
  refine ⟨C, hC, ?_⟩
  intro s hs
  have ht : (s + (n : ℂ) / 2).re ∈ Set.Icc (a + (n : ℝ) / 2) (b + (n : ℝ) / 2) := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re, Set.mem_Icc]
    constructor <;> linarith [hs.1, hs.2]
  simpa only [← continuedDirichlet_eq_shift, Complex.add_im, Complex.div_ofNat_im,
    Complex.natCast_im, zero_div, add_zero] using hb (s + (n : ℂ) / 2) ht

theorem smoothingIntegrand_differentiable (n : ℕ) (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : Differentiable ℂ (mellin F)) (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) : Differentiable ℂ (smoothingIntegrand n F q V X) := by
  have hm := (CubicReflectionKernel.compact_source_mellin_differentiable V a b ha hVs hV).comp
    (show Differentiable ℂ (fun s : ℂ=>s-1/2) from by fun_prop)
  have hp : Differentiable ℂ (fun s : ℂ=>(X:ℂ)^(s-1/2)) :=
    (show Differentiable ℂ (fun s : ℂ=>s-1/2) from by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  exact (hm.mul hp).mul (continuedDirichlet_differentiable n F q hq hF)

theorem smoothingIntegrand_strip_bound (n : ℕ) (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (lo hi : ℝ) (hF : ∀s : ℂ,MellinConvergent F s)
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,s.re∈Set.Icc lo hi →
      ‖smoothingIntegrand n F q V X s‖≤C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Cd,hCd,hd⟩ := continuedDirichlet_strip_bound n F q hq lo hi hF
  have hVc (s : ℂ) := CubicReflectionKernel.compact_source_mellin_convergent V a b ha hVs hV s
  obtain ⟨Cv,hCv,hv⟩ := VerticalContourShift.mellin_uniform_strip_bound V (lo-1/2) (hi-1/2)
    (hVc _) (hVc _)
  let Cx : ℝ := X^(lo-1/2)+X^(hi-1/2)
  have hCx : 0≤Cx := by dsimp [Cx];positivity
  refine ⟨Cv*Cx*Cd,mul_nonneg (mul_nonneg hCv hCx) hCd,?_⟩
  intro s hs
  have hvb : ‖mellin V (s-1/2)‖≤Cv := hv (s-1/2)
    (by simp;linarith [hs.1]) (by simp;linarith [hs.2])
  have hxb : ‖(X:ℂ)^(s-1/2)‖≤Cx := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    have he : (s-1/2).re=s.re-1/2 := by simp
    rw [he]
    exact VerticalContourShift.rpow_between_endpoints X (lo-1/2) (hi-1/2) (s.re-1/2) hX
      (by linarith [hs.1]) (by linarith [hs.2])
  rw [smoothingIntegrand,norm_mul,norm_mul]
  calc
    _≤(Cv*Cx)*(Cd*Real.exp (2*Real.pi*|s.im|)) :=
      mul_le_mul (mul_le_mul hvb hxb (norm_nonneg _) hCv) (hd s hs)
        (norm_nonneg _) (mul_nonneg hCv hCx)
    _=_ := by ring

theorem smoothingIntegrand_contour_eq (n : ℕ) (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : ∀s : ℂ,MellinConvergent F s) (hFe : Differentiable ℂ (mellin F))
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) (lo hi : ℝ) (hlh : lo≤hi)
    (hl : Integrable (fun t : ℝ=>smoothingIntegrand n F q V X ((lo:ℂ)+t*Complex.I)))
    (hh : Integrable (fun t : ℝ=>smoothingIntegrand n F q V X ((hi:ℂ)+t*Complex.I))) :
    (∫t : ℝ,smoothingIntegrand n F q V X ((lo:ℂ)+t*Complex.I))=
      ∫t : ℝ,smoothingIntegrand n F q V X ((hi:ℂ)+t*Complex.I) := by
  obtain ⟨C,hC,hb⟩ := smoothingIntegrand_strip_bound n F q hq lo hi hF V a b ha hVs hV X hX
  apply VerticalContourShift.integral_eq_of_exponential_strip_growth
    (smoothingIntegrand n F q V X) lo hi (2*Real.pi) C hlh (by positivity) hC
  · intro z hz1 hz2
    exact (smoothingIntegrand_differentiable n F q hq hFe V a b ha hVs hV X hX) z
  · exact hl
  · exact hh
  · intro σ hσ t
    simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero,
      Complex.add_im,Complex.mul_im,mul_one,zero_add] using
      hb ((σ:ℂ)+t*Complex.I) (by simpa using hσ)


/-- The actual finite projector has the same initial completed sum, with
its exact order-dependent scalar. This is an equality of convergent integrals. -/
theorem finiteProjector_initial_integrable (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (c : ActualEisensteinCubic.O) (hc : c ≠ 0)
    [Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : ActualEisensteinCubic.O)} * χ.modulus)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    Integrable (fun t : ℝ => smoothingIntegrand n (finiteProjector χ n c hc)
      thetaBesselScale (Vstar W) X ((2 : ℂ) + t * Complex.I)) := by
  have hi := (completedT_initial_mellin_integrable χ.elementHom.toMonoidHom
    χ.norm_elementCoeff_le_one W a b ha hWs hW X hX).const_mul
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n)
  apply hi.congr
  filter_upwards with t
  rw [smoothingIntegrand, continuedDirichlet_finiteProjector χ n hk c hc hcQ _ (by norm_num),
    show (2 : ℂ) + t * Complex.I - 1 / 2 = 3 / 2 + t * Complex.I by ring]
  ring

theorem finiteProjector_initial_mellin (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (c : ActualEisensteinCubic.O) (hc : c ≠ 0)
    [Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : ActualEisensteinCubic.O)} * χ.modulus)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
      completedT χ.elementHom.toMonoidHom W X =
        (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
          smoothingIntegrand n (finiteProjector χ n c hc) thetaBesselScale (Vstar W) X
            ((2 : ℂ) + t * Complex.I) := by
  have hid (t : ℝ) :
      smoothingIntegrand n (finiteProjector χ n c hc) thetaBesselScale (Vstar W) X
        ((2 : ℂ) + t * Complex.I) =
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
        (mellin (Vstar W) ((3 / 2 : ℂ) + t * Complex.I) *
          (X : ℂ) ^ ((3 / 2 : ℂ) + t * Complex.I) *
            completedDirichletSeries χ.elementHom.toMonoidHom ((2 : ℂ) + t * Complex.I)) := by
    rw [smoothingIntegrand, continuedDirichlet_finiteProjector χ n hk c hc hcQ _ (by norm_num),
      show (2 : ℂ) + t * Complex.I - 1 / 2 = 3 / 2 + t * Complex.I by ring]
    ring
  simp_rw [hid]
  rw [integral_const_mul, completedT_initial_mellin χ.elementHom.toMonoidHom
    χ.norm_elementCoeff_le_one W a b ha hWs hW X hX]
  ring

/-- Global shift of the actual physical projector, retaining the exact
scalar and explicit left-line integrability. No reflection model is substituted. -/
theorem finiteProjector_mellin_shift (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (c : ActualEisensteinCubic.O) (hc : c ≠ 0)
    [Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : ActualEisensteinCubic.O)} * χ.modulus)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) (lo : ℝ) (hlo : lo ≤ 2)
    (hleft : Integrable (fun t : ℝ => smoothingIntegrand n (finiteProjector χ n c hc)
      thetaBesselScale (Vstar W) X ((lo : ℂ) + t * Complex.I))) :
    (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
      completedT χ.elementHom.toMonoidHom W X =
        (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
          smoothingIntegrand n (finiteProjector χ n c hc) thetaBesselScale (Vstar W) X
            ((lo : ℂ) + t * Complex.I) := by
  have hF := finiteProjector_mellin_entire χ n c hc
  have he := smoothingIntegrand_contour_eq n (finiteProjector χ n c hc)
    thetaBesselScale thetaBesselScale_pos hF.1 hF.2 (Vstar W) a b ha
    (Vstar_support W a b hWs) (Vstar_contDiff W a b ha hWs hW) X hX lo 2 hlo
    hleft (finiteProjector_initial_integrable χ n hk c hc hcQ W a b ha hWs hW X hX)
  rw [he]
  exact finiteProjector_initial_mellin χ n hk c hc hcQ W a b ha hWs hW X hX

end OAI.CubicEisenstein.AngularSmoothingContour
