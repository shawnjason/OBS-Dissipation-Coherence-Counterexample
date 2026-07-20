# Source Correspondence and Conventions

## Generator convention

`RowMarkovData.rate i j` is the row-forward jump rate from `i` to `j`.
The backward action is

```text
(Q f)(i) = sum_j rate(i,j) * (f(j) - f(i)).
```

The stationary flow is `flow i j = pi i * rate i j`. Stationarity is stored
as equality of total incoming and outgoing flow at every state. The current and
traffic are

```text
current i j = flow i j - flow j i
traffic i j = flow i j + flow j i.
```

The project proves that nonzero current forces positive traffic under
nonnegative rates and positive stationary weights.

## Eigenmode convention

The complex mode `v = x + i*y` and eigenvalue `-a + i*b` are represented by
two real backward-action equations. `WeightedRealMode` is their flow-weighted
form. The exact compiled identities are

```text
a * modeNorm = modeD / 2
b * modeNorm = modeB.
```

`modeD` sums over all ordered pairs. Pair reversal combines the two flows into
the once-per-unordered-edge traffic convention. `modeB` contains an explicit
factor `1/2`; the antisymmetry of current and phase makes this equal to the
once-per-edge manuscript sum.

## Current-weighted factors

The algebraic layer uses

```text
tau       = sigma / (2*C)
kappa     = D*H / B^2
eta_cur   = N*C / H
eta       = N / M
Y         = sigma*a / b^2.
```

`threeFactor_identity` proves `Y = tau*kappa*eta_cur` from the exact
eigenmode identities and nonzero denominators.  The closed generator-level
assembly `rowMarkov_currentWeighted_threeFactor_closed` derives the concrete
thermodynamic, Cauchy, strict phase, and localization bridges internally.
`rowMarkov_paperCore` is the manuscript-facing theorem.

## Matched subdivision convention

The matched branch uses the manuscript's `zI-Q` convention. For an oriented
edge with forward/backward rates `p,q`, the endpoint response is

```text
[[ p, -p], [-q, q]].
```

The inserted state has rates `p1,q1,p2,q2` and escape rate
`s = q1 + p2`. Positive zero-frequency matching is classified by a unique
`alpha` in `(0,1)` with the exact parameterization formalized in
`zeroMatch_iff_parametrized`.

Stationary currents use `piU*p - piV*q`. The affinity theorem preserves the
path rate ratio, and the entropy theorem multiplies the preserved current by
the preserved logarithmic affinity. Normalizing after insertion rescales old
stationary masses and fluxes; the project does not claim that old normalized
probabilities remain unchanged.

## Exact local obstruction

`LocalObstruction.lean` uses exact rational three-state row generators and
normalized uniform stationary laws. Determinants and adjugate pairings are
expanded exactly over `Fin 3`. The oscillatory algebraic number is represented
as

```text
iSqrtThree = Complex.I * Real.sqrt 3,
```

with the exact relation `iSqrtThree^2 = -3`. Polynomial reduction by this
relation proves the right-context motion real part `+5/2`; rational exact
arithmetic proves the left-context motion `-5`. No floating-point
normalization is used.

## Source packet mapping

- OBS mechanism paper and Gu slack note -> `OBS/CoreBranch/`.
- Matched subdivision theorem and spectral spacer source ->
  `OBS/MatchedSubdivision/`.
- Susceptibility/Evans formulas and local obstruction ledger ->
  `OBS/FullCompanion/`.
- Witness-specific numerical ledgers remain external as stated in
  `FORMALIZATION_STATUS.md`.

## v0.2 concrete generator closure

The ordered-support convention is fixed by
`BidirectionalRowMarkovData.OrderedSupport`:

- `C = (1/2) * Σ_ordered j²/T`;
- `H = (1/4) * Σ_ordered (j²/T)(A_i+A_j)`;
- `K = (1/8) * Σ_ordered (j²/T)|v_i+v_j|²`;
- `sigma = (1/2) * Σ_ordered j log(flow_ij/flow_ji)`.

The factor conversions are proved in `ConcreteEntropy.lean`,
`ConcreteCauchy.lean`, and `ConcretePhase.lean`. Entropy logarithms are evaluated
only on `OrderedSupport`; `flow_pos_on_support` supplies both positive directed
flows. Sparse absent edges therefore require no `log (0/0)` convention.

The explicit Cauchy components use weight `T/2` and
`(Δx, -j*S_y/4)`, `(Δy, j*S_x/4)`. Their dot product is the existing ordered
`modeB`, their weighted first norm is `modeD`, and their reciprocal-weight
second norm is concrete `K`.

The manuscript-facing closure is `rowMarkov_paperCore`; see
`PAPER_CROSSWALK.md` for the equation-level map.
