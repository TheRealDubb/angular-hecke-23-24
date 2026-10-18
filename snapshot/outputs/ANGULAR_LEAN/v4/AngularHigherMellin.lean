import AngularAnalyticFoundation
import OAI.NumberTheory.DirichletL.Eisenstein.ReflectedCuspMellin

/-! Genuine Mellin convergence and entire dependence for a reflected profile
of arbitrary complex weight. Positive-height reflection, continuity and decay
are explicit hypotheses; a totalized integral identity is not used as a
substitute for convergence. Weight 2*j is the higher cusp derivative case. -/

noncomputable section
open Filter MeasureTheory Asymptotics Set
open scoped Classical Topology

namespace OAI.CubicEisenstein.AngularHigherMellin

def reflected (weight A : ℂ) (Q : ℝ) (g : ℝ → ℂ) (v : ℝ) : ℂ :=
  A * ((v : ℂ) ^ (-weight) * g ((Q * v)⁻¹))

theorem reflected_mellin (weight A s : ℂ) (Q : ℝ) (hQ : 0 < Q)
    (g : ℝ → ℂ) :
    mellin (reflected weight A Q g) s =
      A * (Q : ℂ) ^ (weight - s) * mellin g (weight - s) := by
  have he : reflected weight A Q g =
      fun v : ℝ => A • ((v : ℂ) ^ (-weight) • g ((Q * v)⁻¹)) := rfl
  rw [he, mellin_const_smul, mellin_cpow_smul]
  have hm := mellin_comp_mul_left (fun v : ℝ => g v⁻¹) (s + -weight) hQ
  rw [mellin_comp_inv] at hm
  rw [hm]
  simp only [smul_eq_mul]
  rw [show -(s + -weight) = weight - s by ring]
  ring

theorem reflected_mellinConvergent (weight A s : ℂ) (Q : ℝ) (hQ : 0 < Q)
    (g : ℝ → ℂ) (hg : MellinConvergent g (weight - s)) :
    MellinConvergent (reflected weight A Q g) s := by
  have hinv : MellinConvergent (fun t : ℝ => g t⁻¹) (s - weight) := by
    have hh := (MellinConvergent.comp_rpow (f := g) (s := s - weight)
      (a := -1) (by norm_num : (-1 : ℝ) ≠ 0)).mpr
        (show MellinConvergent g ((s - weight) / (-1 : ℝ)) by
          simpa only [show ((s - weight) / (-1 : ℝ) : ℂ) = weight - s by
            push_cast; ring] using hg)
    simpa only [Real.rpow_neg_one] using hh
  have hscale := (MellinConvergent.comp_mul_left (f := fun t : ℝ => g t⁻¹)
    (s := s - weight) hQ).mpr hinv
  have hpow := (MellinConvergent.cpow_smul (f := fun t : ℝ => g (Q * t)⁻¹)
    (s := s) (a := -weight)).mpr (by simpa only [sub_eq_add_neg] using hscale)
  convert! hpow.const_smul A using 1

theorem truncation_reflection_ae (weight A : ℂ) (Q : ℝ) (hQ : 0 < Q)
    (f g : ℝ → ℂ)
    (hfg : ∀ v : ℝ, 0 < v → f v = reflected weight A Q g v) :
    f =ᵐ[volume.restrict (Ioi 0)]
      (fun v => truncatedCuspProfile 1 f v +
        reflected weight A Q (truncatedCuspProfile (1 / Q) g) v) := by
  have hne : ∀ᵐ v : ℝ ∂volume.restrict (Ioi 0), v ≠ 1 :=
    ae_restrict_of_ae (Measure.ae_ne volume 1)
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hne] with v hv hv1
  have hrel : 1 / Q < (Q * v)⁻¹ ↔ v < 1 := by
    rw [inv_eq_one_div, div_lt_div_iff₀ hQ (mul_pos hQ hv)]
    constructor <;> intro hh <;> nlinarith
  by_cases hhi : 1 < v
  · have hlo : ¬1 / Q < (Q * v)⁻¹ := fun hh => not_lt_of_ge hhi.le (hrel.mp hh)
    simp only [truncatedCuspProfile, ite_eq_left hhi, reflected, ite_eq_right hlo,
      mul_zero, add_zero]
  · have hlo : 1 / Q < (Q * v)⁻¹ := hrel.mpr (lt_of_le_of_ne (le_of_not_gt hhi) hv1)
    simp only [truncatedCuspProfile, ite_eq_right hhi, reflected, ite_eq_left hlo, zero_add]
    exact hfg v hv

theorem mellin_entire (weight A : ℂ) (Q decayF decayG : ℝ)
    (hQ : 0 < Q) (hdecayF : 0 < decayF) (hdecayG : 0 < decayG)
    (f g : ℝ → ℂ) (hf : ContinuousOn f (Ioi 0)) (hg : ContinuousOn g (Ioi 0))
    (hfbound : f =O[atTop] (fun v : ℝ => Real.exp (-decayF * v)))
    (hgbound : g =O[atTop] (fun v : ℝ => Real.exp (-decayG * v)))
    (hfg : ∀ v : ℝ, 0 < v → f v = reflected weight A Q g v) :
    (∀ s : ℂ, MellinConvergent f s) ∧ Differentiable ℂ (mellin f) := by
  obtain ⟨hfc, hfd⟩ := truncatedCuspProfile_mellin_entire
    1 decayF (by norm_num) hdecayF f hf hfbound
  obtain ⟨hgc, hgd⟩ := truncatedCuspProfile_mellin_entire
    (1 / Q) decayG (by positivity) hdecayG g hg hgbound
  have hae := truncation_reflection_ae weight A Q hQ f g hfg
  have hresult (s : ℂ) : HasMellin f s
      (mellin (truncatedCuspProfile 1 f) s +
        A * (Q : ℂ) ^ (weight - s) *
          mellin (truncatedCuspProfile (1 / Q) g) (weight - s)) := by
    have hr := reflected_mellinConvergent weight A s Q hQ
      (truncatedCuspProfile (1 / Q) g) (hgc (weight - s))
    have hsum := hasMellin_add (hfc s) hr
    constructor
    · apply hsum.1.congr
      filter_upwards [hae] with v hv
      exact congrArg (fun z : ℂ => (v : ℂ) ^ (s - 1) • z) hv.symm
    · have he : mellin f s = mellin (fun v => truncatedCuspProfile 1 f v +
          reflected weight A Q (truncatedCuspProfile (1 / Q) g) v) s := by
        unfold mellin
        apply integral_congr_ae
        filter_upwards [hae] with v hv
        rw [hv]
      rw [he, hsum.2, reflected_mellin _ _ _ _ hQ]
  refine ⟨fun s => (hresult s).1, ?_⟩
  have he : mellin f = fun s : ℂ => mellin (truncatedCuspProfile 1 f) s +
      A * (Q : ℂ) ^ (weight - s) *
        mellin (truncatedCuspProfile (1 / Q) g) (weight - s) :=
    funext (fun s => (hresult s).2)
  rw [he]
  let : NeZero (Q : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hQ.ne'⟩
  have hp := (differentiable_const_cpow_of_neZero (Q : ℂ)).comp
    ((differentiable_const weight).sub differentiable_id)
  exact hfd.add (((differentiable_const A).mul hp).mul
    (hgd.comp ((differentiable_const weight).sub differentiable_id)))

end OAI.CubicEisenstein.AngularHigherMellin
