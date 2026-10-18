import AngularPolynomialKernel
import OAI.NumberTheory.DirichletL.CubicSieve.RankMargins

/-! Polynomial height control for the actual shifted angular reflection
kernel. The degree is chosen before the live height; the uniform source
certificate also chooses it before the supported smooth source. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
namespace OAI.CubicEisenstein.AngularHeight
open CompletedHeight CompletedGauss ActualEisensteinCubic CompletedDyadic
open CanonicalQuadraticSieve

def HasUniformPolynomialKernel (angularOrder : ℕ) {κ : Type*} (P : κ→ℝ→ℝ→ℂ) : Prop :=
  (∀w t,ContDiffOn ℝ ∞ (AngularReflectionKernel.paperKernel angularOrder (Vstar (P w t))) (Set.Ioi 0)) ∧
  ∀ A K : ℕ,∃n : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀t : ℝ,∀i≤K,∀x : ℝ,0<x →
    (1+x)^A*‖LocalLogFourier.eulerDeriv (AngularReflectionKernel.paperKernel angularOrder (Vstar (P w t))) i x‖≤
      C*(1+‖t‖)^n

theorem normTwistedSource_uniform_polynomial_kernel (angularOrder : ℕ) (a b : ℝ) (ha : 0<a) :
    HasUniformPolynomialKernel angularOrder (fun W : SupportedSmoothSource a b => normTwistedSource W.val) := by
  constructor
  · intro W t
    exact (normTwistedSource_polynomial_kernel angularOrder W.val a b ha W.property.1 W.property.2).1 t
  · intro A K
    obtain ⟨s,D,hD,hkernel⟩ := AngularReflectionKernel.paperKernel_euler_source_uniform_weighted_bound angularOrder a b ha A K
    obtain ⟨n,hn⟩ := normTwistedSource_uniform_degree a b ha s
    refine ⟨n,?_⟩
    intro W
    let S := vstarSchwartz W.val a b ha W.property.1 W.property.2
    have hS : Function.support (S : ℝ→ℂ)⊆Set.Icc a b := Vstar_support W.val a b W.property.1
    let G := uniformTwistedSchwartz S a b ha hS (S.smooth ⊤)
    obtain ⟨C,hC,hsource⟩ := hn S hS (S.smooth ⊤)
    have hlink (t : ℝ) : (G t : ℝ→ℂ)=Vstar (normTwistedSource W.val t) := by
      funext x
      rw [show G t x=uniformTwistedSchwartz S a b ha hS (S.smooth ⊤) t x from rfl,
        uniformTwistedSchwartz_apply]
      change FourierBridge.logPhase t (Real.log x)*((Real.sqrt x:ℂ)*W.val x)=
        (Real.sqrt x:ℂ)*(FourierBridge.logPhase t (Real.log x)*W.val x)
      ring
    have hGs (t : ℝ) : Function.support (G t : ℝ→ℂ)⊆Set.Icc a b := by
      intro x hx
      change G t x≠0 at hx
      rw [show G t x=uniformTwistedSchwartz S a b ha hS (S.smooth ⊤) t x from rfl,
        uniformTwistedSchwartz_apply] at hx
      exact hS (normTwistedSource_support S t hx)
    refine ⟨D*C,mul_pos hD hC,?_⟩
    intro t i hi x hx
    rw [←hlink t]
    exact (hkernel (G t) (hGs t) i hi x hx).trans
      ((mul_le_mul_of_nonneg_left (hsource t) hD.le).trans_eq (by ring))

theorem uniform_polynomial_kernel_log_separation (angularOrder : ℕ) {κ ι : Type*} [Fintype ι]
    (P : κ→ℝ→ℝ→ℂ) (hP : HasUniformPolynomialKernel angularOrder P)
    (V : ι→ℝ→ℂ) (slope M : ι→ℝ) (hM : ∀i,0≤M i)
    (hV : ∀i y,V i y≠0 → |y|≤M i) (A J : ℕ) :
    ∃n : ℕ,∀w : κ,∃C : ℝ,0≤C ∧ ∀θ R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀y : ι→ℝ,(∏i,V i (y i))*AngularReflectionKernel.paperKernel angularOrder (Vstar (P w θ))
          (R*Real.exp (∑i,slope i*y i))=
        ∫t : ℝ,(∏i,V i (y i)*FourierBridge.logPhase t (slope i*y i))*B t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖B t‖) ∧
      (1+R)^A*(∫t : ℝ,(1+‖t‖)^J*‖B t‖)≤C*(1+‖θ‖)^n ∧
      (∀t : ℝ,(1+R)^A*(1+‖t‖)^J*‖B t‖≤C*(1+‖θ‖)^n) := by
  obtain ⟨n,hn⟩ := hP.2 A (J+(volume : Measure ℝ).integrablePower)
  obtain ⟨C,hC,hsep⟩ := LocalLogFourier.coupled_positive_log_separation_linear_constant
    V slope M hM hV A J
  refine ⟨n,?_⟩
  intro w
  obtain ⟨D,hD,hkernel⟩ := hn w
  refine ⟨C*D,mul_nonneg hC hD.le,?_⟩
  intro θ R hR
  obtain ⟨B,hB,hi,hb,hp⟩ := hsep (AngularReflectionKernel.paperKernel angularOrder (Vstar (P w θ))) (hP.1 w θ)
    (D*(1+‖θ‖)^n) (by positivity) (hkernel θ) R hR
  refine ⟨B,hB,hi,?_,?_⟩
  · exact hb.trans_eq (by ring)
  · intro t
    exact (hp t).trans_eq (by ring)

theorem uniform_polynomial_kernel_three_window (angularOrder : ℕ) {κ : Type*}
    (P : κ→ℝ→ℝ→ℂ) (hP : HasUniformPolynomialKernel angularOrder P)
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂) (A : ℕ) :
    ∃n : ℕ,∀w : κ,∃C : ℝ,0≤C ∧ ∀θ R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀r u v : ℝ,V₀ r*V₁ u*V₂ v*AngularReflectionKernel.paperKernel angularOrder (Vstar (P w θ))
        (R*Real.exp (-2*r+u+3*v))=
        ∫t : ℝ,(V₀ r*FourierBridge.logPhase t (-2*r))*
          (V₁ u*FourierBridge.logPhase t u)*(V₂ v*FourierBridge.logPhase t (3*v))*B t) ∧
      (1+R)^A*(∫t : ℝ,‖B t‖)≤C*(1+‖θ‖)^n := by
  let V : Fin 3→ℝ→ℂ := ![V₀,V₁,V₂]
  let slope : Fin 3→ℝ := ![-2,1,3]
  let M : Fin 3→ℝ := ![M₀,M₁,M₂]
  have hm : ∀i,0≤M i := by intro i; fin_cases i <;> assumption
  have hv : ∀i y,V i y≠0 → |y|≤M i := by intro i; fin_cases i <;> assumption
  obtain ⟨n,hn⟩ := uniform_polynomial_kernel_log_separation angularOrder P hP V slope M hm hv A 0
  refine ⟨n,?_⟩
  intro w
  obtain ⟨C,hC,h⟩ := hn w
  refine ⟨C,hC,?_⟩
  intro θ R hR
  obtain ⟨B,hB,hi,hbound,hpoint⟩ := h θ R hR
  refine ⟨B,?_,by simpa only [pow_zero,one_mul] using hbound⟩
  intro r u v
  simpa [V,slope,Fin.prod_univ_succ,Fin.sum_univ_succ,mul_assoc,add_assoc] using hB ![r,u,v]

end OAI.CubicEisenstein.AngularHeight
