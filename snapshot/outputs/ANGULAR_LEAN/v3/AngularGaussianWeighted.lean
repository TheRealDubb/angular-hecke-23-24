import AngularGaussianSchwartz

/-! Actual polynomial Gaussian Schwartz functions and their real directional
derivatives. The angular Fourier identities are proved in the next module. -/

noncomputable section
open scoped SchwartzMap FourierTransform ContDiff
open LineDeriv

namespace OAI.SevenEighths.Angular.GaussianFourier

open GaussianSchwartz

@[simp] theorem gaussian_apply_real (a : ℝ) (ha : 0 < a) (z : ℂ) :
    gaussian a ha z = (Real.exp (-(Real.pi * a) * ‖z‖ ^ 2) : ℂ) := rfl

def weighted (L : ℂ →L[ℝ] ℂ) (a : ℝ) (ha : 0 < a) (m : ℕ) : SchwartzMap ℂ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun z => (L z) ^ m) (gaussian a ha)

@[simp] theorem weighted_apply (L : ℂ →L[ℝ] ℂ) (a : ℝ) (ha : 0 < a)
    (m : ℕ) (z : ℂ) : weighted L a ha m z = (L z) ^ m * gaussian a ha z := by
  exact SchwartzMap.smulLeftCLM_apply_apply (by fun_prop) _ _

def holo (a : ℝ) (ha : 0 < a) (m : ℕ) : SchwartzMap ℂ ℂ :=
  weighted (ContinuousLinearMap.id ℝ ℂ) a ha m

def anti (a : ℝ) (ha : 0 < a) (m : ℕ) : SchwartzMap ℂ ℂ :=
  weighted (Complex.conjCLE : ℂ →L[ℝ] ℂ) a ha m

@[simp] theorem holo_apply (a : ℝ) (ha : 0 < a) (m : ℕ) (z : ℂ) :
    holo a ha m z = z ^ m * gaussian a ha z := by simp [holo]

@[simp] theorem anti_apply (a : ℝ) (ha : 0 < a) (m : ℕ) (z : ℂ) :
    anti a ha m z = (star z) ^ m * gaussian a ha z := by
  simp [anti]

theorem weighted_integrable (L : ℂ →L[ℝ] ℂ) (a : ℝ) (ha : 0 < a) (m : ℕ) :
    MeasureTheory.Integrable (fun z : ℂ => (L z) ^ m * gaussian a ha z) := by
  convert (weighted L a ha m).integrable (μ := MeasureTheory.volume) using 1
  funext z
  exact (weighted_apply L a ha m z).symm

end OAI.SevenEighths.Angular.GaussianFourier
