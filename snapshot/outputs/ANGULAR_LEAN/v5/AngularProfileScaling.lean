import AngularFiniteCuspSecondReflection
import AngularHigherProfiles
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-! Exact real dilation of horizontal Wirtinger profiles. The generic dilation
identities respect Lean's totalized derivatives; their physical applications
use the already proved Bessel derivative and regularity witnesses. -/

noncomputable section
open scoped Classical Topology

namespace OAI.CubicEisenstein.AngularProfileScaling

open AngularBesselDerivatives AngularHigherProfiles
open AngularFiniteCuspSecondReflection

theorem directional_deriv_div (f : ℂ → ℂ) (s : ℝ) (z direction : ℂ) :
    deriv (fun t : ℝ => f ((z + (t : ℂ) * direction) / (s : ℂ))) 0 =
      (s : ℂ)⁻¹ * deriv (fun t : ℝ => f (z / (s : ℂ) + (t : ℂ) * direction)) 0 := by
  have h := deriv_comp_mul_left s⁻¹
    (fun t : ℝ => f (z / (s : ℂ) + (t : ℂ) * direction)) 0
  simp only [mul_zero, Complex.real_smul, Complex.ofReal_inv] at h
  convert! h using 1
  congr 1
  funext t
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem wirtingerBar_div (f : ℂ → ℂ) (s : ℝ) (z : ℂ) :
    horizontalWirtingerBar (fun w => f (w / (s : ℂ))) z =
      (s : ℂ)⁻¹ * horizontalWirtingerBar f (z / (s : ℂ)) := by
  have h1 := directional_deriv_div f s z 1
  simp only [mul_one] at h1
  rw [horizontalWirtingerBar, horizontalWirtingerBar, h1, directional_deriv_div]
  ring

theorem wirtingerZ_div (f : ℂ → ℂ) (s : ℝ) (z : ℂ) :
    horizontalWirtingerZ (fun w => f (w / (s : ℂ))) z =
      (s : ℂ)⁻¹ * horizontalWirtingerZ f (z / (s : ℂ)) := by
  have h1 := directional_deriv_div f s z 1
  simp only [mul_one] at h1
  rw [horizontalWirtingerZ, horizontalWirtingerZ, h1, directional_deriv_div]
  ring

theorem iteratedBar_div (f : ℂ → ℂ) (s : ℝ) (n : ℕ) :
    iteratedBar n (fun w => f (w / (s : ℂ))) =
      fun z => ((s : ℂ)⁻¹) ^ n * iteratedBar n f (z / (s : ℂ)) := by
  induction n with
  | zero => funext z; simp [iteratedBar]
  | succ n ih =>
      funext z
      simp only [iteratedBar, ih, horizontalWirtingerBar_const_mul, wirtingerBar_div, pow_succ]
      ring

theorem iteratedZ_div (f : ℂ → ℂ) (s : ℝ) (n : ℕ) :
    iteratedZ n (fun w => f (w / (s : ℂ))) =
      fun z => ((s : ℂ)⁻¹) ^ n * iteratedZ n f (z / (s : ℂ)) := by
  induction n with
  | zero => funext z; simp [iteratedZ]
  | succ n ih =>
      funext z
      simp only [iteratedZ, ih, horizontalWirtingerZ_const_mul, wirtingerZ_div, pow_succ]
      ring

/-- Actual finite-cusp bar profile, at positive height, with its precise scale. -/
theorem finite_barProfile_eq (j : Fin 3) (n : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    barProfile (fun w => cubicSourceResidualFunction (representative j • w)) n z v =
      ((sourceCuspScale j : ℂ)⁻¹) ^ n *
        barProfile ((sourceCuspCoefficients j).fullFunction (sourceCuspBesselConstant j)) n
          (z / (sourceCuspScale j : ℂ)) (v / sourceCuspScale j) := by
  have hs := sourceCuspScale_pos j
  have he : (fun w => cubicSourceResidualFunction (representative j • upperPoint w v hv)) =
      (fun w => (sourceCuspCoefficients j).fullFunction (sourceCuspBesselConstant j)
        (upperPoint (w / (sourceCuspScale j : ℂ)) (v / sourceCuspScale j) (div_pos hv hs))) := by
    funext w
    exact sourceCusp_bessel_expansion j v hv w
  rw [barProfile_positive _ _ _ _ hv, he, barProfile_positive _ _ _ _ (div_pos hv hs)]
  convert! congrFun (iteratedBar_div
    (fun w => (sourceCuspCoefficients j).fullFunction (sourceCuspBesselConstant j)
      (upperPoint w (v / sourceCuspScale j) (div_pos hv hs))) (sourceCuspScale j) n) z using 1

/-- Actual finite-cusp Z profile, at positive height, with its precise scale. -/
theorem finite_zProfile_eq (j : Fin 3) (n : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    zProfile (fun w => cubicSourceResidualFunction (representative j • w)) n z v =
      ((sourceCuspScale j : ℂ)⁻¹) ^ n *
        zProfile ((sourceCuspCoefficients j).fullFunction (sourceCuspBesselConstant j)) n
          (z / (sourceCuspScale j : ℂ)) (v / sourceCuspScale j) := by
  have hs := sourceCuspScale_pos j
  have he : (fun w => cubicSourceResidualFunction (representative j • upperPoint w v hv)) =
      (fun w => (sourceCuspCoefficients j).fullFunction (sourceCuspBesselConstant j)
        (upperPoint (w / (sourceCuspScale j : ℂ)) (v / sourceCuspScale j) (div_pos hv hs))) := by
    funext w
    exact sourceCusp_bessel_expansion j v hv w
  rw [zProfile_positive _ _ _ _ hv, he, zProfile_positive _ _ _ _ (div_pos hv hs)]
  convert! congrFun (iteratedZ_div
    (fun w => (sourceCuspCoefficients j).fullFunction (sourceCuspBesselConstant j)
      (upperPoint w (v / sourceCuspScale j) (div_pos hv hs))) (sourceCuspScale j) n) z using 1

end OAI.CubicEisenstein.AngularProfileScaling
