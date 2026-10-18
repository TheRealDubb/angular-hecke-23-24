# Exact theorem and scope

The field is K = Q(sqrt(-3)), with its Eisenstein integer ring O. The Lean
`AngularCharacter` consists of an integer k, a nonzero integral ideal modulus,
a finite residue character, and the unit-compatibility equation

    alpha(u)^k * residue(u mod modulus) = 1  for every global unit u.

For nonzero elements, the physical coefficient is
`alpha(a)^k * residue(a mod modulus)`. The coefficient at zero is defined as
zero; unit compatibility lets these coefficients descend to ideals. The
function in the theorem is `FamilyContinuation.LFunction`, linked by the source
chain to the actual ideal Dirichlet series in its half-plane of convergence.
See [AngularCharacter.lean](snapshot/outputs/ANGULAR_LEAN/v1/AngularCharacter.lean)
and the definition dependencies listed in SOURCE_CLOSURE.json.

The principal theorem is exactly:

```lean
theorem physical_seed (χ : AngularCharacter) (s : ℂ)
    (hs : (23:ℝ)/24 < s.re)
    (hpole : χ.k = 0 → χ.residue = 1 → s ≠ 1) :
    FamilyContinuation.LFunction χ s ≠ 0
```

Its qualified name is
`OAI.SevenEighths.Angular.FullFamilySeed.physical_seed`.
The inequality is strict. No claim is made on Re(s) = 23/24.
All integer angular types admitted by the compatibility equation are covered;
there is no primitivity assumption in this statement.

The sole exception is the actual type-zero principal pole at s = 1. Type-zero
nonprincipal functions are included at s = 1. A totalized value at a pole is
not being classified as an analytic zero.

For every real unitary norm-twist parameter tau the second theorem is exactly:

```lean
theorem physical_seed_norm_twist (χ : AngularCharacter) (τ : ℝ) (s : ℂ)
    (hs : (23:ℝ)/24 < s.re)
    (hpole : χ.k = 0 → χ.residue = 1 → s ≠ 1+(τ:ℂ)*I) :
    NormTwist.LFunction χ τ s ≠ 0
```

Its qualified name is
`OAI.SevenEighths.Angular.FullFamilySeed.physical_seed_norm_twist`.
The twist uses the shift s -> s - i*tau, so the principal pole shifts to
1 + i*tau. The bound is independent of the selected character in this
qualitative nonvanishing statement. No quantitative estimates uniform in
growing angular order, nor effective uniform thresholds for such estimates,
are claimed by this release.

The adjacent source proves nonprincipal entireness and half-plane transport.
The final v30 bundle contains 14 theorem targets across two modules. This
target count is not the size of the entire proof dependency closure.

The claim is 23/24 = 0.958333..., not 7/8, 0.8748389, GRH, or RH. The stronger
angular target remains unfinished. The theorem refers to the explicit Lean
family and continuation above, not an unspecified collection of all Hecke
characters over arbitrary number fields.
