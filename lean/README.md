# OBSMechanismLean v0.2 — closed paper core

Lean 4 formalization companion for the OBS dissipation–coherence mechanism.
Version 0.2 closes the generator-to-edge interface for the current-weighted
paper theorem while preserving the matched-subdivision and full-companion
modules from v0.1.

## Resolution

**RESOLVED — PAPER CORE FORMALIZED**

From one finite `BidirectionalRowMarkovData` value and one nonreal backward
eigenmode, the project defines `sigma`, `C`, `D`, `B`, `K`, `H`, `N`, `M`,
`Y`, `tau`, `kappa`, `etaCur`, and `eta`, then proves:

```text
Y = tau * kappa * etaCur
1 < tau
1 < kappa
eta <= etaCur
etaCur < Y
```

The primary declaration is
`BidirectionalRowMarkovData.rowMarkov_currentWeighted_threeFactor_closed`.
Its inputs are only the finite bidirectional row-Markov data, mode coordinates,
decay/frequency parameters, the two backward eigen-equations, a nonzero mode
coordinate, and `b != 0`. It accepts none of the six v0.1 bridge assumptions.

## Reproduce

Pinned environment: Lean `v4.29.0`, Lake `5.0.0`, Mathlib commit
`8a178386ffc0f5fef0b77738bb5449d50efeea95`.

```bash
cd OBSMechanismLean_v0.2_core_closed
export PATH="$HOME/.elan/bin:$PATH"
lake update
lake exe cache get
bash build_wsl.sh
```

The recorded clean build completed **8,275 jobs** with no warnings or errors.
`build_wsl.sh` removes only the root project's `.lake/build`; dependency caches
are preserved.

## New v0.2 modules

- `ConcreteEdgeData.lean`: common support and all concrete paper quantities.
- `ConcreteEntropy.lean`: concrete strict `2*C < sigma`.
- `ConcreteCauchy.lean`: explicit `OrderedSupport × Fin 2` arrays and
  `B^2 <= D*K`.
- `ConcretePhase.lean`: positive deficit from `B != 0`, `K < H`, and
  `B^2 < D*H`.
- `ConcreteLocalization.lean`: `H <= M*C`, localization comparison, and exact
  endpoint-max equality condition.
- `GeneratorThreeFactor.lean`: closed generator theorem and paper wrappers.
- `RegressionExamples.lean`: five exact adversarial examples.

See `PAPER_CROSSWALK.md`, `GAP_CLOSURE_REPORT.md`, and
`FINAL_THEOREM_SIGNATURES.md`.

## Scope boundary

Witness-specific interval arithmetic, the 12-state spectrum, Rouché disks,
Gershgorin causal-window checks, and finite role-layer certificates remain
external validated computations. No such fact is introduced as a Lean axiom.

