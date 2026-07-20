# Core-interface gap closure report

| Gap | Status | Compiling evidence |
|---|---|---|
| G-001 | **CLOSED** | `BidirectionalRowMarkovData`, `OrderedSupport`, and concrete `sigma`, `C`, `D`, `B`, `K`, `H`, `N`, `M`, `eta`, `etaCur` in `ConcreteEdgeData.lean` |
| G-002 | **CLOSED** | `concrete_B_cauchy_representation`, `concrete_D_cauchy_representation`, `concrete_K_cauchy_representation`, `concrete_B_sq_le_DK` |
| G-003 | **CLOSED** | `two_C_lt_sigma_of_backward_eigenmode`, derived from positive support flows and the nonreal eigenmode |
| G-004 | **CLOSED** | `exists_positive_phase_deficit_of_B_ne_zero`, `concrete_K_lt_H_of_B_ne_zero`, `concrete_B_sq_lt_DH_of_B_ne_zero` |
| G-005 | **CLOSED** | `H_le_M_mul_C`, `eta_le_etaCur`, `etaCur_eq_eta_iff_endpoint_max_all_pairs'` |

## Integration evidence

`generatorCoreCertificates` derives every positivity, eigenmode identity, and
bridge fact internally. `rowMarkov_currentWeighted_threeFactor_closed` passes
those derived facts to the already-audited algebraic core.

The final public theorem signature contains no thermodynamic inequality,
arbitrary Cauchy arrays, phase-deficit witness, or localization inequality.

## Regression evidence

`RegressionExamples.lean` compiles exact tests for:

1. a reversible chain with vanishing `B`;
2. a sparse bidirectional chain with an absent edge;
3. nonzero current with zero phase contribution and zero mode difference;
4. saturation of the abstract localization bound;
5. the ordered-pair factor `1/2` on three states.

## Build gate

Clean umbrella build: **PASS — 8,275 jobs, no warnings or errors**.

