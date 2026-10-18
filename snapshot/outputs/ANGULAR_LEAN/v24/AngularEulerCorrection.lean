import AngularWeightedMellin
import OAI.NumberTheory.DirichletL.Hecke.MobiusEulerCorrection

/-! Actual angular Euler correction: convergent, nonvanishing and analytic
on Re(s)>0. This alone does not assert nonvanishing of an L-function. -/
noncomputable section
namespace OAI.CubicEisenstein.AngularEulerCorrection
open scoped BigOperators Classical Topology
open Filter Asymptotics MeasureTheory
open ActualEisensteinCubic
open SevenEighths.Angular
open SmoothMobiusCorrection (PrimeIdeal primeNormPower primeDensity norm_primeNormPower
  primeDensity_norm_le_one one_sub_ne_zero prime_norm_series_summable prime_norm_pos prime_norm_two_le)

def primeCharacterTerm  (χ : AngularCharacter) (P : PrimeIdeal) (s : ℂ) : ℂ :=
  χ.idealHom P.val * primeNormPower P s

lemma primeCharacterTerm_norm_le  (χ : AngularCharacter) (P : PrimeIdeal)
    (s : ℂ) (σ : ℝ) (hs : σ≤s.re) :
    ‖primeCharacterTerm χ P s‖≤(Ideal.absNorm P.val:ℝ)^(-σ) := by
  rw [primeCharacterTerm,norm_mul,norm_primeNormPower]
  have hn1 : (1:ℝ)≤Ideal.absNorm P.val := by exact_mod_cast (by have:=prime_norm_two_le P;omega)
  calc
    _ ≤ 1*(Ideal.absNorm P.val:ℝ)^(-s.re) :=
      mul_le_mul_of_nonneg_right (χ.norm_idealHom_le_one _) (by positivity)
    _ ≤ _ := by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hs)

lemma primeCharacterTerm_norm_lt_one  (χ : AngularCharacter) (P : PrimeIdeal)
    (s : ℂ) (hs : 0<s.re) : ‖primeCharacterTerm χ P s‖<1 := by
  apply (primeCharacterTerm_norm_le χ P s s.re le_rfl).trans_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg (by have:=prime_norm_two_le P;exact_mod_cast (by omega:1<Ideal.absNorm P.val)) (by linarith)

lemma correctionDenominator_ne_zero  (χ : AngularCharacter) (P : PrimeIdeal)
    (s : ℂ) (hs : 0<s.re) : 1-primeDensity P*primeCharacterTerm χ P s≠0 := by
  apply one_sub_ne_zero
  rw [norm_mul]
  calc
    _ ≤ 1*‖primeCharacterTerm χ P s‖ :=
      mul_le_mul_of_nonneg_right (primeDensity_norm_le_one P) (norm_nonneg _)
    _ < 1 := by rw [one_mul];exact primeCharacterTerm_norm_lt_one χ P s hs

def correctionTerm  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) : ℂ :=
  if P.val∈S then 0 else
    -((1:ℂ)/(Ideal.absNorm P.val:ℂ))*primeCharacterTerm χ P s /
      (1-primeDensity P*primeCharacterTerm χ P s)

def eulerCorrection  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O)) (s : ℂ) : ℂ :=
  ∏' P : PrimeIdeal, (1+correctionTerm χ S P s)

lemma correctionTerm_factor  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) (hs : 0<s.re) :
    1+correctionTerm χ S P s =
      if P.val∈S then 1 else (1-primeCharacterTerm χ P s)/(1-primeDensity P*primeCharacterTerm χ P s) := by
  by_cases hP : P.val∈S
  · simp [correctionTerm,hP]
  · simp only [correctionTerm,ite_eq_right hP]
    have hd := correctionDenominator_ne_zero χ P s hs
    apply (eq_div_iff hd).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hd]
    dsimp [primeDensity]
    ring

lemma correctionFactor_ne_zero  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) (hs : 0<s.re) : 1+correctionTerm χ S P s≠0 := by
  rw [correctionTerm_factor χ S P s hs]
  split_ifs
  · exact one_ne_zero
  · exact div_ne_zero (one_sub_ne_zero (primeCharacterTerm_norm_lt_one χ P s hs))
      (correctionDenominator_ne_zero χ P s hs)

lemma correctionTerm_uniform_bound  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (σ : ℝ) (hσ : 0<σ) (P : PrimeIdeal) (s : ℂ) (hs : σ≤s.re) :
    ‖correctionTerm χ S P s‖ ≤
      (1-(2:ℝ)^(-σ))⁻¹*(Ideal.absNorm P.val:ℝ)^(-(1+σ)) := by
  have hn := prime_norm_pos P
  have hn2 : (2:ℝ)≤Ideal.absNorm P.val := by exact_mod_cast prime_norm_two_le P
  have hr : (2:ℝ)^(-σ)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr0 : 0<1-(2:ℝ)^(-σ) := sub_pos.mpr hr
  have hx := primeCharacterTerm_norm_le χ P s σ hs
  have hx2 : ‖primeCharacterTerm χ P s‖≤(2:ℝ)^(-σ) := hx.trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by linarith))
  have hd : 1-(2:ℝ)^(-σ)≤‖1-primeDensity P*primeCharacterTerm χ P s‖ := by
    have hb : ‖primeDensity P*primeCharacterTerm χ P s‖≤(2:ℝ)^(-σ) := by
      rw [norm_mul]
      calc
        _ ≤ 1*‖primeCharacterTerm χ P s‖ :=
          mul_le_mul_of_nonneg_right (primeDensity_norm_le_one P) (norm_nonneg _)
        _ ≤ _ := by simpa using hx2
    have hh := norm_sub_norm_le (1:ℂ) (primeDensity P*primeCharacterTerm χ P s)
    simpa only [norm_one] using (show 1-(2:ℝ)^(-σ) ≤ ‖(1:ℂ)‖-‖primeDensity P*primeCharacterTerm χ P s‖ from by simpa using sub_le_sub_left hb 1) |>.trans hh
  by_cases hP : P.val∈S
  · simp only [correctionTerm,ite_eq_left hP,norm_zero]
    positivity
  · rw [correctionTerm,ite_eq_right hP,norm_div,norm_mul,norm_neg,norm_div,norm_one,Complex.norm_natCast]
    calc
      _ ≤ ((1:ℝ)/(Ideal.absNorm P.val:ℝ)*(Ideal.absNorm P.val:ℝ)^(-σ))/(1-(2:ℝ)^(-σ)) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hx (by positivity)) hr0 hd
      _ = _ := by
        rw [show -(1+σ)=(-1)+(-σ) by ring,Real.rpow_add hn,Real.rpow_neg_one]
        ring

lemma correctionTerm_summable  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 0<s.re) : Summable (fun P : PrimeIdeal => ‖correctionTerm χ S P s‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => correctionTerm_uniform_bound χ S s.re hs P s le_rfl)
  exact (prime_norm_series_summable s.re hs).mul_left _

theorem eulerCorrection_ne_zero  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 0<s.re) : eulerCorrection χ S s≠0 :=
  tprod_one_add_ne_zero_of_summable (fun P => correctionFactor_ne_zero χ S P s hs)
    (correctionTerm_summable χ S s hs)

lemma primeCharacterTerm_differentiable  (χ : AngularCharacter)
    (P : PrimeIdeal) : Differentiable ℂ (primeCharacterTerm χ P) := by
  have hn : (Ideal.absNorm P.val:ℂ)≠0 := by
    exact_mod_cast (ne_of_gt (prime_norm_pos P))
  exact ((differentiable_id.neg).const_cpow (Or.inl hn)).const_mul _

lemma correctionTerm_differentiableOn  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (P : PrimeIdeal) (σ : ℝ) (hσ : 0≤σ) :
    DifferentiableOn ℂ (correctionTerm χ S P) {s:ℂ | σ<s.re} := by
  unfold correctionTerm
  by_cases hP : P.val∈S
  · simpa only [ite_eq_left hP] using (differentiableOn_const (𝕜 := ℂ) (s := {s:ℂ | σ<s.re}) (c := (0:ℂ)))
  · simp only [ite_eq_right hP]
    intro s hs
    have hx := primeCharacterTerm_differentiable χ P s
    convert ((hx.const_mul (-((1:ℂ)/(Ideal.absNorm P.val:ℂ)))).div
      ((differentiableAt_const (1:ℂ)).sub (hx.const_mul (primeDensity P)))
      (correctionDenominator_ne_zero χ P s (lt_of_le_of_lt hσ hs))).differentiableWithinAt using 1

lemma eulerCorrection_locally_uniform  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (σ : ℝ) (hσ : 0<σ) :
    HasProdLocallyUniformlyOn (fun P s => 1+correctionTerm χ S P s)
      (eulerCorrection χ S) {s:ℂ | σ<s.re} := by
  have hu := (prime_norm_series_summable σ hσ).mul_left ((1-(2:ℝ)^(-σ))⁻¹)
  exact hu.hasProdLocallyUniformlyOn_one_add
    (isOpen_lt continuous_const Complex.continuous_re)
    (Filter.Eventually.of_forall (fun P s hs => correctionTerm_uniform_bound χ S σ hσ P s hs.le))
    (fun P => (correctionTerm_differentiableOn χ S P σ hσ.le).continuousOn)

theorem eulerCorrection_differentiableOn_halfplane  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (σ : ℝ) (hσ : 0<σ) :
    DifferentiableOn ℂ (eulerCorrection χ S) {s:ℂ | σ<s.re} := by
  apply (eulerCorrection_locally_uniform χ S σ hσ).differentiableOn
  · apply Filter.Eventually.of_forall
    intro t
    change DifferentiableOn ℂ (fun z => ∏ P ∈ t, (1+correctionTerm χ S P z)) _
    apply DifferentiableOn.fun_finsetProd
    intro P hP
    exact (differentiableOn_const (𝕜 := ℂ) (c := (1:ℂ))).add
      (correctionTerm_differentiableOn χ S P σ hσ.le)
  · exact isOpen_lt continuous_const Complex.continuous_re

theorem eulerCorrection_differentiableOn  (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : DifferentiableOn ℂ (eulerCorrection χ S) {s:ℂ | 0<s.re} := by
  intro s hs
  have hh := eulerCorrection_differentiableOn_halfplane χ S (s.re/2) (by dsimp at hs;linarith)
  exact (hh.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show s∈{z:ℂ | s.re/2<z.re} by dsimp at *;linarith))).differentiableWithinAt
theorem eulerCorrection_analytic  (χ : AngularCharacter) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    AnalyticOnNhd ℂ (eulerCorrection χ S) {s : ℂ | 0<s.re} :=
  (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).mpr
    (eulerCorrection_differentiableOn χ S)

end OAI.CubicEisenstein.AngularEulerCorrection
