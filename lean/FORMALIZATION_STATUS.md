# Formalization status

## Resolution label

**RESOLVED — PAPER CORE FORMALIZED**

Mandatory gaps G-001 through G-005 are closed by concrete theorems sharing one
finite Markov generator, one stationary law, one ordered positive-traffic
support, and one backward eigenmode.

## Closed generator interface

`rowMarkov_currentWeighted_threeFactor_closed` assumes only:

- `[Fintype I]`;
- `R : BidirectionalRowMarkovData I`;
- mode coordinates `x y : I → ℝ` and parameters `a b : ℝ`;
- the real and imaginary backward eigen-equations;
- `∃ i, x i ≠ 0 ∨ y i ≠ 0`;
- `b ≠ 0`.

It does not accept `hthermo`, `hBrep`, `hDrep`, `hKrep`, `hKH`, `hlocal`,
or an equivalent bundled field.

## Compiled paper-facing declarations

- `rowMarkov_currentWeighted_threeFactor_closed`
- `rowMarkov_Y_eq_tau_mul_kappa_mul_etaCur`
- `rowMarkov_Y_gt_etaCur_ge_eta`
- `rowMarkov_paperCore`
- `rowMarkov_etaCur_eq_eta_iff`

The equality theorem states that `etaCur = eta` exactly when both endpoints of
every nonzero-current ordered state pair have maximal squared mode amplitude.

## Preserved lower layers

The v0.1 conditional assembly theorems remain available as reusable lower-level
results. Matched subdivision, resistance, susceptibility algebra, and the exact
local-sign obstruction are preserved and pass the same umbrella build.

## External only

The exact 12-state witness spectrum, interval/ball arithmetic, causal-window
certificate, and role-layer finite classifications are not Lean claims in this
package.

## Build evidence

- Ubuntu 24.04.4 LTS under WSL2.
- Lean 4.29.0, commit `98dc76e3c0a9b856c9b98726b713fb04fab16740`.
- Lake 5.0.0.
- Mathlib `8a178386ffc0f5fef0b77738bb5449d50efeea95`.
- Clean root build: **8,275 jobs**, no warnings, no errors.
- Proof-bypass audit: PASS across 29 project Lean files.
- Closed-signature audit: PASS across five public closed theorem signatures
  and the concrete generator structure.
