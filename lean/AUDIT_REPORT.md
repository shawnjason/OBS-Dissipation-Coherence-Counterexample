# Audit Report

## Resolution

**RESOLVED — PAPER CORE FORMALIZED**

The generator-level OBS dissipation–coherence core is closed in Lean.  The
public theorem derives the thermodynamic, Cauchy, strict phase-deficit, and
localization bridges from one finite bidirectional row-Markov generator and a
nonreal backward eigenmode.  None of the six former bridge assumptions is a
field of the generator structure or an input to the closed public theorems.

## Mechanical audit

- Lean 4.29.0, commit `98dc76e3c0a9b856c9b98726b713fb04fab16740`.
- Lake 5.0.0.
- Mathlib revision `8a178386ffc0f5fef0b77738bb5449d50efeea95`.
- Clean umbrella build: PASS, 8,275 jobs, no warnings or errors.
- Source audit: PASS across 29 project Lean files.
- Forbidden tokens: `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, and
  `sorryAx`; none occur in project Lean source.
- Closed-signature audit: PASS for five public theorems and the
  `BidirectionalRowMarkovData` structure.
- Exact build evidence: `CLEAN_BUILD_TRANSCRIPT.txt`.

## Interface audit

The closed public inputs are exactly:

- a finite state type;
- `R : BidirectionalRowMarkovData I`;
- real mode coordinates `x y : I → ℝ` and scalars `a b : ℝ`;
- the real and imaginary backward eigen-equations;
- existence of a nonzero mode coordinate;
- `b ≠ 0`.

The former inputs `hthermo`, `hBrep`, `hDrep`, `hKrep`, `hKH`, and `hlocal`
are derived internally.  Manual inspection and the enhanced signature audit
also confirm that no equivalent theorem conclusion was moved into the
generator structure.  Its only additional structural hypothesis is positive
flow in both directions when traffic is positive.

## Mathematical convention audit

- `rate i j` is row-forward and `backwardAction f i = Σj rate i j (f j-f i)`.
- Ordered-pair factors are explicit:
  `C = 1/2 Σ j²/T`, `H = 1/4 Σ (j²/T)(Aᵢ+Aⱼ)`,
  `K = 1/8 Σ (j²/T)|vᵢ+vⱼ|²`, and
  `sigma = 1/2 Σ j log(flowᵢⱼ/flowⱼᵢ)`.
- Entropy logarithms are evaluated only on positive-traffic support; both
  directed flows are positive there.  Sparse absent edges require no
  `log (0/0)` convention.
- The explicit weighted Cauchy construction has weight `T/2` and components
  `(Δx,-j S_y/4)` and `(Δy,j S_x/4)`; it yields the exact `B`, `D`, and `K`
  representations and `B² ≤ DK`.
- Nonzero `B` yields `2C < sigma`, `K < H`, and hence `B² < DH`.
- `H ≤ MC` is proved termwise, and equality of `etaCur` and `eta` is
  characterized exactly by maximal endpoint amplitude on every nonzero-current
  ordered pair.

## Regression audit

`RegressionExamples.lean` compiles exact small examples for:

1. a reversible chain with `B = 0`;
2. a sparse bidirectional chain with an absent edge;
3. nonzero current with zero phase/difference contribution;
4. localization saturation;
5. ordered-pair versus once-per-edge factor conversion.

These are focused convention regressions, not numerical witness
reformalizations.  Witness-specific numerical ledgers remain external to this
core package, as documented in `FORMALIZATION_STATUS.md`.

## Independent hostile review

An independent adversarial source review found no critical mathematical or
Lean defect.  It marked factor/sign conventions, support/log safety,
strictness, localization equality, final signatures, and proof-bypass checks
as passing.  Its documentation findings were addressed by refreshing this
report, `GAP_LEDGER.md`, `SOURCE_CORRESPONDENCE.md`, `THEOREM_MAP.csv`, the
final signature sheet, and package hashes.

