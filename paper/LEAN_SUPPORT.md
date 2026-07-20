# Lean support in manuscript v0.2.4

The companion Lean project is `OBS_Lean_Core_Closed_Package_v0.2_2026-07-20.zip`, pinned to Lean 4.29.0 and Mathlib revision `8a178386...`.

## Machine-checked symbolic results

- generator-level three-factor identity;
- strict inequalities `tau > 1`, `kappa > 1`;
- refinement `Y > eta_cur >= eta`;
- equality characterization for `eta_cur = eta`;
- matched-subdivision response and stationary identities;
- exact local-sign obstruction.

The public declarations include:

- `rowMarkov_paperCore`;
- `rowMarkov_etaCur_eq_eta_iff`.

## Boundary

Lean does not verify the explicit 12-state spectrum, logarithmic Arb/Acb entropy bounds, Rouché/Gershgorin causal-window root isolation, or the fixed-profile role-family length certificates. Those are separate validated-computation results.

The finalized project was independently rebuilt from a deleted root-project build directory under Lean 4.29.0 and the pinned Mathlib revision. The build completed successfully with 8,275 jobs, zero warnings, zero errors, zero proof-bypass findings, and no former bridge assumptions in the closed public interface. The complete audit is included in `lean_audit/`.
