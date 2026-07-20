# Final Public-Theorem Audit

## Audited declarations

- `BidirectionalRowMarkovData.rowMarkov_currentWeighted_threeFactor_closed`
- `BidirectionalRowMarkovData.rowMarkov_Y_eq_tau_mul_kappa_mul_etaCur`
- `BidirectionalRowMarkovData.rowMarkov_Y_gt_etaCur_ge_eta`
- `BidirectionalRowMarkovData.rowMarkov_paperCore`
- `BidirectionalRowMarkovData.rowMarkov_etaCur_eq_eta_iff`
- immediate certificate dependency `generatorCoreCertificates`
- structure `BidirectionalRowMarkovData`

All names above are in namespace `OBS.CoreBranch`.

## Signature result

The closed public interface assumes only:

- a finite state type;
- one `BidirectionalRowMarkovData` value;
- real mode coordinates `x` and `y` and parameters `a` and `b`;
- the real and imaginary backward eigen-equations;
- existence of a nonzero mode coordinate;
- `b ≠ 0`.

The former inputs `hthermo`, `hBrep`, `hDrep`, `hKrep`, `hKH`, and `hlocal`
are absent.  They are not present under different names in the generator
structure, a bundled assumption, or the public theorem parameters.

## Internally derived chain

`generatorCoreCertificates` and its concrete dependencies derive:

- `2 * C < sigma` in `ConcreteEntropy.lean`;
- `B² ≤ D*K` through explicit `B`, `D`, and `K` representations in
  `ConcreteCauchy.lean`;
- `K < H` and `B² < D*H` in `ConcretePhase.lean`;
- `H ≤ M*C` in `ConcreteLocalization.lean`;
- `Y = tau*kappa*etaCur` and `Y > etaCur ≥ eta` in
  `GeneratorThreeFactor.lean`;
- `etaCur = eta` exactly when the endpoints of every nonzero-current ordered
  pair have maximal amplitude.

## Axiom audit

The following commands were run after the clean build:

```lean
#print axioms OBS.CoreBranch.BidirectionalRowMarkovData.rowMarkov_currentWeighted_threeFactor_closed
#print axioms OBS.CoreBranch.BidirectionalRowMarkovData.rowMarkov_paperCore
#print axioms OBS.CoreBranch.BidirectionalRowMarkovData.rowMarkov_etaCur_eq_eta_iff
```

Each declaration reported exactly:

```text
[propext, Classical.choice, Quot.sound]
```

These are standard Lean foundational axioms used by Mathlib.  No project axiom,
proof bypass, or imported version of a former bridge assumption was reported.

## Verdict

No former bridge assumption remains in the final public interface, directly or
indirectly as a project-defined axiom or structure field.

