# OBS paper-core crosswalk

All objects below come from one `BidirectionalRowMarkovData` value and the same
real/imaginary backward eigenmode coordinates. The ordered-support definitions
carry the explicit factors that remove double counting.

| Paper object or claim | Lean definition/theorem | File |
|---|---|---|
| \(N_v\) | `BidirectionalRowMarkovData.N` | `OBS/CoreBranch/ConcreteEdgeData.lean` |
| \(D\) | `BidirectionalRowMarkovData.D`; `concrete_D_cauchy_representation` | `OBS/CoreBranch/ConcreteCauchy.lean` |
| \(B\) | `BidirectionalRowMarkovData.B`; `concrete_B_support_representation`; `concrete_B_cauchy_representation` | `OBS/CoreBranch/ConcreteCauchy.lean` |
| \(C\) | `BidirectionalRowMarkovData.C`; `C_eq_half_sum_current_sq_div_traffic` | `OBS/CoreBranch/ConcreteEntropy.lean` |
| \(K\) | `BidirectionalRowMarkovData.K`; `concrete_K_cauchy_representation`; `concrete_K_parallelogram_representation` | `OBS/CoreBranch/ConcreteCauchy.lean`, `ConcretePhase.lean` |
| \(H\) | `BidirectionalRowMarkovData.H`; `concrete_H_parallelogram_representation` | `OBS/CoreBranch/ConcretePhase.lean` |
| \(M\) | `BidirectionalRowMarkovData.M`; `amplitude_le_M` | `OBS/CoreBranch/ConcreteEdgeData.lean` |
| \(\sigma\) | `BidirectionalRowMarkovData.sigma` | `OBS/CoreBranch/ConcreteEdgeData.lean` |
| \(2C<\sigma\) | `two_C_lt_sigma_of_backward_eigenmode` | `OBS/CoreBranch/ConcreteEntropy.lean` |
| \(B^2\le DK\) | `concrete_B_sq_le_DK` | `OBS/CoreBranch/ConcreteCauchy.lean` |
| \(K<H\) from \(B\ne0\) | `concrete_K_lt_H_of_B_ne_zero` | `OBS/CoreBranch/ConcretePhase.lean` |
| \(B^2<DH\) | `concrete_B_sq_lt_DH_of_B_ne_zero` | `OBS/CoreBranch/ConcretePhase.lean` |
| \(H\le MC\) | `H_le_M_mul_C` | `OBS/CoreBranch/ConcreteLocalization.lean` |
| \(\eta_{\rm cur}\ge\eta\) | `eta_le_etaCur` | `OBS/CoreBranch/ConcreteLocalization.lean` |
| \(Y=\tau\kappa\eta_{\rm cur}\) | `rowMarkov_Y_eq_tau_mul_kappa_mul_etaCur` | `OBS/CoreBranch/GeneratorThreeFactor.lean` |
| \(Y>\eta_{\rm cur}\ge\eta\) | `rowMarkov_Y_gt_etaCur_ge_eta` | `OBS/CoreBranch/GeneratorThreeFactor.lean` |
| Bundled paper core | `rowMarkov_paperCore` | `OBS/CoreBranch/GeneratorThreeFactor.lean` |
| Equality condition | `rowMarkov_etaCur_eq_eta_iff` | `OBS/CoreBranch/GeneratorThreeFactor.lean` |

## Manuscript-ready reproducibility wording

> The general current-weighted factorization, its strict inequalities, and the
> equality characterization of the localization refinement were formalized in
> Lean 4 against Mathlib. The witness-specific spectral and interval claims
> remain independently certified by exact and validated numerical methods.

This package does not claim that Lean verifies the 12-state witness, its
causal-window spectrum, or its interval/ball-arithmetic certificates.

