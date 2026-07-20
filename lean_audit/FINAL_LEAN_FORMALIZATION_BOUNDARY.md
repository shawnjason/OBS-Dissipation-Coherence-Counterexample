# Final Lean Formalization Boundary

## Proved by the Lean project

- The concrete finite-generator current-weighted three-factor theorem.
- The strict thermodynamic and phase refinements.
- The current-weighted localization inequality and its exact equality case.
- The matched-subdivision parameterization, response, stationary transport,
  entropy preservation, and resistance obstruction in their stated symbolic
  domains.
- The exact local-invariants obstruction.
- The conditional susceptibility algebra in its documented scope.

The manuscript-facing core theorem is
`BidirectionalRowMarkovData.rowMarkov_paperCore`.

## Not claimed as Lean-verified

- The explicit 12-state witness spectrum.
- Arb/Acb entropy or spectral interval computations.
- Rouché-disk causal-window certification.
- Gershgorin causal-window auditing.
- Role-layer classifications for lengths `L = 3, …, 12`.

These remain external exact or validated computational certificates.  None is
introduced into the Lean proof chain as an axiom.

## Submission wording

> The general current-weighted factorization, its strict inequalities, and the
> equality characterization of the localization refinement were formalized in
> Lean 4 against Mathlib. The witness-specific spectral and interval claims
> remain independently certified by exact and validated numerical methods.

