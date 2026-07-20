# Gap Ledger

| ID | Status | Gap | Consequence / required closure |
|---|---|---|---|
| G-001 | **Closed** | One `BidirectionalRowMarkovData` and `OrderedSupport` define every concrete paper quantity. | `ConcreteEdgeData.lean`; used by the final generator theorem. |
| G-002 | **Closed** | Explicit `OrderedSupport × Fin 2` Cauchy arrays represent `B`, `D`, and `K`. | `concrete_B_sq_le_DK`. |
| G-003 | **Closed** | Strict entropy cost is summed only over positive bidirectional support. | `two_C_lt_sigma_of_backward_eigenmode`. |
| G-004 | **Closed** | `B != 0` yields a nonzero current-phase summand and positive mode-difference deficit. | `concrete_K_lt_H_of_B_ne_zero`, `concrete_B_sq_lt_DH_of_B_ne_zero`. |
| G-005 | **Closed** | Concrete maximum and current weights yield localization comparison and exact equality. | `H_le_M_mul_C`, `etaCur_eq_eta_iff_endpoint_max_all_pairs'`. |
| G-006 | Open, secondary | The Gu-slack theorem is an exact algebraic regrouping, not a complete shared generator/edge-data correspondence. | Do not identify adjacent Gu factors individually with `kappa` and `eta_cur/eta`. |
| G-007 | Open, full companion | Susceptibility assumes a differentiated root equation and nonzero denominator. | Root-branch existence, simplicity-to-local-branch construction, and differentiability remain unproved. |
| G-008 | Deliberately external | 12-state characteristic polynomial, Arb/Acb enclosures, logarithm bounds, Rouche disks, Gershgorin window, spectrum isolation, and role-layer classifications. | These remain validated external certificates and are not Lean claims. |
| G-009 | Optional refinement | Constructive nonzero outer-product factorization is used instead of `Matrix.rank = 1`. | The exact response theorem is retained; only the library-level rank formulation is absent. |
| G-010 | Optional refinement | Denominator singularity is proved instead of a `RatFunc` pole-order theorem. | Exact singular location is formalized, not pole multiplicity. |
| G-011 | Optional refinement | No secondary square-root/optimizer theorem for subdivision tuning. | Mandatory matched-subdivision identities are unaffected. |

No manuscript equation was found false in the formalized scope. The mandatory
core interface is closed; secondary and witness-specific gaps retain the scope
labels shown above.
