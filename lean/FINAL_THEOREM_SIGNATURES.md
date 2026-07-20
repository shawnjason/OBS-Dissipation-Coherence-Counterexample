# Final Closed Theorem Signatures

Namespace:
`OBS.CoreBranch.BidirectionalRowMarkovData`.

For every theorem below, Lean supplies `[Fintype I]` and the namespace fixes
`R : BidirectionalRowMarkovData I`.  The mathematical inputs are:

```text
x y : I → ℝ
a b : ℝ
hreal : ∀ i, backwardAction x i = -a*x i - b*y i
himag : ∀ i, backwardAction y i =  b*x i - a*y i
hcoord : ∃ i, x i ≠ 0 ∨ y i ≠ 0
hb : b ≠ 0
```

No theorem below accepts `hthermo`, `hBrep`, `hDrep`, `hKrep`, `hKH`,
`hlocal`, or a bundled equivalent.

## `rowMarkov_currentWeighted_threeFactor_closed`

```text
sigma*a/b² = (sigma/(2C))*(D*H/B²)*(N*C/H)
∧ 1 < sigma/(2C)
∧ 1 < D*H/B²
∧ N/M ≤ N*C/H
∧ N*C/H < sigma*a/b²
```

## `rowMarkov_Y_eq_tau_mul_kappa_mul_etaCur`

```text
Y = tau * kappa * etaCur
```

## `rowMarkov_Y_gt_etaCur_ge_eta`

```text
etaCur < Y ∧ eta ≤ etaCur
```

## `rowMarkov_paperCore`

```text
Y = tau * kappa * etaCur
∧ 1 < tau
∧ 1 < kappa
∧ eta ≤ etaCur
∧ etaCur < Y
```

## `rowMarkov_etaCur_eq_eta_iff`

```text
etaCur = eta ↔
  ∀ i j, current i j ≠ 0 →
    amplitude i = M ∧ amplitude j = M
```

The certificate theorem `generatorCoreCertificates` derives positivity,
nondegeneracy, strict thermodynamic and phase inequalities, localization, and
both exact eigenmode identities used by these public results.

