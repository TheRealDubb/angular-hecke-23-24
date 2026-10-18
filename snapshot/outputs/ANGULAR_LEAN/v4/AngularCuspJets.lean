import AngularBesselDerivatives

/-!
# Pure Wirtinger jets of the actual inverse-cusp coordinates

All denominators are the concrete `v² + ‖z‖²` from OAI's
`inverseCuspCoordinates`. Positive height makes the rational coordinate
functions smooth everywhere. The results below compute actual derivatives;
they do not assume a coordinate-jet contract or joint regularity of a Bessel
series after a height-changing pullback.
-/

noncomputable section
open scoped Classical Topology
open Complex

namespace OAI.CubicEisenstein.AngularCuspJets

open AngularBesselDerivatives

def denominator (v : ℝ) (z : ℂ) : ℂ := (v : ℂ) ^ 2 + z * star z

theorem denominator_eq (v : ℝ) (z : ℂ) :
    denominator v z = ((v ^ 2 + ‖z‖ ^ 2 : ℝ) : ℂ) := by
  simp [denominator, Complex.mul_conj', Complex.ofReal_add,
    Complex.ofReal_pow]

theorem denominator_ne_zero (v : ℝ) (hv : 0 < v) (z : ℂ) :
    denominator v z ≠ 0 := by
  rw [denominator_eq]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))

/-- A concrete family closed under the pure antiholomorphic derivative. -/
def kernel (v : ℝ) (p q : ℕ) (z : ℂ) : ℂ := z ^ p / denominator v z ^ (q + 1)

theorem denominator_contDiff (v : ℝ) : ContDiff ℝ ⊤ (denominator v) := by
  have hc : ContDiff ℝ ⊤ (fun _ : ℂ => (v : ℂ) ^ 2) := contDiff_const
  convert! (hc.add
    ((contDiff_id : ContDiff ℝ ⊤ (fun z : ℂ => z)).mul Complex.conjCLE.contDiff)) using 1

theorem kernel_contDiff (v : ℝ) (hv : 0 < v) (p q : ℕ) :
    ContDiff ℝ ⊤ (kernel v p q) := by
  have h := ((contDiff_id : ContDiff ℝ ⊤ (fun z : ℂ => z)).pow p).mul
    (((denominator_contDiff v).pow (q + 1)).inv
      (fun z => pow_ne_zero (q + 1) (denominator_ne_zero v hv z)))
  convert! h using 1

theorem kernel_line_hasDerivAt (v : ℝ) (hv : 0 < v) (p q : ℕ)
    (z direction : ℂ) :
    HasDerivAt (fun t : ℝ => kernel v p q (z + (t : ℂ) * direction))
      ((((p : ℂ) * z ^ (p - 1) * direction) * denominator v z ^ (q + 1) -
        z ^ p * ((q + 1 : ℕ) : ℂ) * denominator v z ^ q *
          (direction * star z + z * star direction)) /
        (denominator v z ^ (q + 1)) ^ 2) 0 := by
  have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * direction) direction 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const direction).const_add z)
  have hd : HasDerivAt (fun t : ℝ => denominator v (z + (t : ℂ) * direction))
      (direction * star z + z * star direction) 0 := by
    simpa [denominator] using (hl.mul hl.star).const_add ((v : ℂ) ^ 2)
  convert! (hl.pow p).div (hd.pow (q + 1))
    (by simpa using pow_ne_zero (q + 1) (denominator_ne_zero v hv z)) using 1
  simp [mul_assoc]

theorem kernel_wirtingerBar (v : ℝ) (hv : 0 < v) (p q : ℕ) (z : ℂ) :
    horizontalWirtingerBar (kernel v p q) z =
      -((q + 1 : ℕ) : ℂ) * kernel v (p + 1) (q + 1) z := by
  have h1 := (kernel_line_hasDerivAt v hv p q z 1).deriv
  have hI := (kernel_line_hasDerivAt v hv p q z Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerBar, h1, hI]
  simp only [star_one, Complex.star_def, Complex.conj_I]
  unfold kernel
  have hd := denominator_ne_zero v hv z
  simp only [pow_succ]
  field_simp [hd]
  simp only [Complex.I_sq]
  ring

theorem iteratedBar_const_mul (j : ℕ) (a : ℂ) (f : ℂ → ℂ) :
    iteratedBar j (fun z => a * f z) = fun z => a * iteratedBar j f z := by
  induction j with
  | zero => rfl
  | succ j ih =>
      funext z
      simp only [iteratedBar, ih, horizontalWirtingerBar_const_mul]

theorem iteratedBar_succ_inner (j : ℕ) (f : ℂ → ℂ) :
    iteratedBar (j + 1) f = iteratedBar j (horizontalWirtingerBar f) := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg horizontalWirtingerBar ih

/-- Every fixed pure derivative of the rational kernel, with its exact coefficient. -/
theorem iteratedBar_kernel (v : ℝ) (hv : 0 < v) (p q j : ℕ) :
    iteratedBar j (kernel v p q) = fun z =>
      (-1 : ℂ) ^ j * ((q + 1).ascFactorial j : ℂ) * kernel v (p + j) (q + j) z := by
  induction j with
  | zero => simp [iteratedBar]
  | succ j ih =>
      funext z
      simp only [iteratedBar, ih, horizontalWirtingerBar_const_mul,
        kernel_wirtingerBar v hv, Nat.ascFactorial_succ, Nat.cast_mul,
        pow_succ]
      rw [show p + j + 1 = p + (j + 1) by omega,
        show q + j + 1 = q + (j + 1) by omega]
      push_cast
      ring

theorem kernel_zero_of_pos (v : ℝ) (p q : ℕ) (hp : 0 < p) : kernel v p q 0 = 0 := by
  simp [kernel, zero_pow (Nat.ne_of_gt hp)]

theorem iteratedBar_kernel_zero (v : ℝ) (hv : 0 < v) (p q j : ℕ)
    (h : 0 < p + j) : iteratedBar j (kernel v p q) 0 = 0 := by
  simp only [iteratedBar_kernel v hv, kernel_zero_of_pos v _ _ h, mul_zero]

def antiKernel (v : ℝ) (z : ℂ) : ℂ := star z / denominator v z

theorem antiKernel_line_hasDerivAt (v : ℝ) (hv : 0 < v) (z direction : ℂ) :
    HasDerivAt (fun t : ℝ => antiKernel v (z + (t : ℂ) * direction))
      ((star direction * denominator v z -
        star z * (direction * star z + z * star direction)) / denominator v z ^ 2) 0 := by
  have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * direction) direction 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const direction).const_add z)
  have hd : HasDerivAt (fun t : ℝ => denominator v (z + (t : ℂ) * direction))
      (direction * star z + z * star direction) 0 := by
    simpa [denominator] using (hl.mul hl.star).const_add ((v : ℂ) ^ 2)
  convert! hl.star.div hd (by simpa using denominator_ne_zero v hv z) using 1
  simp

theorem antiKernel_wirtingerBar (v : ℝ) (hv : 0 < v) (z : ℂ) :
    horizontalWirtingerBar (antiKernel v) z = (v : ℂ) ^ 2 * kernel v 0 1 z := by
  have h1 := (antiKernel_line_hasDerivAt v hv z 1).deriv
  have hI := (antiKernel_line_hasDerivAt v hv z Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerBar, h1, hI]
  simp only [star_one, Complex.star_def, Complex.conj_I]
  unfold kernel
  have hd := denominator_ne_zero v hv z
  field_simp [hd]
  simp only [denominator, Complex.star_def, Complex.I_sq]
  ring

theorem horizontalWirtingerBar_const_sub (a : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    horizontalWirtingerBar (fun w => a - f w) z = -horizontalWirtingerBar f z := by
  simp only [horizontalWirtingerBar, deriv_const_sub]
  ring

theorem horizontal_coordinate (c d : ℂ) (v : ℝ) (z : ℂ) :
    (inverseCuspCoordinates c d v z).1 = -d / c - (c ^ 2)⁻¹ * antiKernel v z := by
  simp only [inverseCuspCoordinates, antiKernel, denominator_eq, div_eq_mul_inv, mul_inv_rev]
  ring

theorem conjugate_coordinate (c d : ℂ) (v : ℝ) (z : ℂ) :
    star (inverseCuspCoordinates c d v z).1 =
      star (-d / c) - (star c ^ 2)⁻¹ * kernel v 1 0 z := by
  rw [horizontal_coordinate]
  simp [antiKernel, kernel, denominator_eq, mul_comm]

theorem height_coordinate (c d : ℂ) (v : ℝ) (z : ℂ) :
    ((inverseCuspCoordinates c d v z).2 : ℂ) =
      ((v / ‖c‖ ^ 2 : ℝ) : ℂ) * kernel v 0 0 z := by
  simp [inverseCuspCoordinates, kernel, denominator_eq,
    Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm]

/-- The first pure antiholomorphic derivative of the actual horizontal coordinate. -/
theorem horizontal_coordinate_wirtingerBar (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    horizontalWirtingerBar (fun z => (inverseCuspCoordinates c d v z).1) =
      fun z => (-(c ^ 2)⁻¹ * (v : ℂ) ^ 2) * kernel v 0 1 z := by
  funext z
  simp only [horizontal_coordinate, horizontalWirtingerBar_const_sub,
    horizontalWirtingerBar_const_mul, antiKernel_wirtingerBar v hv]
  ring

theorem horizontal_coordinate_first_jet (c d : ℂ) (hc : c ≠ 0)
    (v : ℝ) (hv : 0 < v) :
    iteratedBar 1 (fun z => (inverseCuspCoordinates c d v z).1) 0 =
      -1 / (c ^ 2 * (v : ℂ) ^ 2) := by
  change horizontalWirtingerBar (fun z => (inverseCuspCoordinates c d v z).1) 0 = _
  rw [horizontal_coordinate_wirtingerBar c d v hv]
  simp only [kernel, denominator, pow_zero, zero_mul, add_zero]
  field_simp [hc, Complex.ofReal_ne_zero.mpr hv.ne']
  ring

/-- All pure horizontal coordinate jets of order at least two vanish at the cusp center. -/
theorem horizontal_coordinate_pure_jet_zero (c d : ℂ) (v : ℝ) (hv : 0 < v)
    (j : ℕ) (hj : 1 ≤ j) :
    iteratedBar (j + 1) (fun z => (inverseCuspCoordinates c d v z).1) 0 = 0 := by
  simp only [iteratedBar_succ_inner, horizontal_coordinate_wirtingerBar c d v hv,
    iteratedBar_const_mul, iteratedBar_kernel_zero v hv 0 1 j (by omega), mul_zero]

/-- The conjugate horizontal coordinate has no positive pure antiholomorphic jet at zero. -/
theorem conjugate_coordinate_pure_jet_zero (c d : ℂ) (v : ℝ) (hv : 0 < v)
    (j : ℕ) :
    iteratedBar (j + 1) (fun z => star (inverseCuspCoordinates c d v z).1) 0 = 0 := by
  have hfirst : horizontalWirtingerBar
      (fun z => star (inverseCuspCoordinates c d v z).1) =
      fun z => (star c ^ 2)⁻¹ * kernel v 2 1 z := by
    funext z
    simp only [conjugate_coordinate, horizontalWirtingerBar_const_sub,
      horizontalWirtingerBar_const_mul, kernel_wirtingerBar v hv]
    norm_num
  simp only [iteratedBar_succ_inner, hfirst, iteratedBar_const_mul,
    iteratedBar_kernel_zero v hv 2 1 j (by omega), mul_zero]

/-- The actual height has no positive pure antiholomorphic jet at the cusp center. -/
theorem height_coordinate_pure_jet_zero (c d : ℂ) (v : ℝ) (hv : 0 < v)
    (j : ℕ) (hj : 0 < j) :
    iteratedBar j (fun z => ((inverseCuspCoordinates c d v z).2 : ℂ)) 0 = 0 := by
  simp only [height_coordinate, iteratedBar_const_mul,
    iteratedBar_kernel_zero v hv 0 0 j (by omega), mul_zero]

theorem horizontal_coordinate_second_jet_zero (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    iteratedBar 2 (fun z => (inverseCuspCoordinates c d v z).1) 0 = 0 :=
  horizontal_coordinate_pure_jet_zero c d v hv 1 le_rfl

theorem height_coordinate_second_jet_zero (c d : ℂ) (v : ℝ) (hv : 0 < v) :
    iteratedBar 2 (fun z => ((inverseCuspCoordinates c d v z).2 : ℂ)) 0 = 0 :=
  height_coordinate_pure_jet_zero c d v hv 2 (by norm_num)

end OAI.CubicEisenstein.AngularCuspJets
