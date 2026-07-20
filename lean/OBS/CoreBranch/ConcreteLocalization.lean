import OBS.CoreBranch.ConcreteEdgeData
import OBS.CoreBranch.FiniteWeighted

/-!
# Concrete current-weighted localization

The generic weighted-average lemmas are instantiated with the actual
ordered-edge current weights.  This closes the localization bridge without a
caller-supplied local inequality or equality characterization.
-/

namespace OBS.CoreBranch

open scoped BigOperators

variable {I : Type*} [Fintype I]

namespace BidirectionalRowMarkovData

variable (R : BidirectionalRowMarkovData I)

/-- Concrete endpoint localization bound `H ≤ M*C`. -/
theorem H_le_M_mul_C (x y : I → ℝ) : R.H x y ≤ R.M x y * R.C := by
  exact weighted_endpointAverage_le_max
    R.currentWeight
    (fun e : R.OrderedSupport ↦ R.amplitude x y e.val.1)
    (fun e : R.OrderedSupport ↦ R.amplitude x y e.val.2)
    (R.M x y)
    R.currentWeight_nonneg
    (fun e ↦ R.amplitude_le_M x y e.val.1)
    (fun e ↦ R.amplitude_le_M x y e.val.2)

/-- Concrete current-weighted localization dominates ordinary localization. -/
theorem etaCur_ge_eta_concrete
    (x y : I → ℝ)
    (hN : 0 ≤ R.N x y) (hH : 0 < R.H x y) (hM : 0 < R.M x y) :
    R.N x y / R.M x y ≤ R.N x y * R.C / R.H x y := by
  exact etaCur_ge_eta hN hH hM (R.H_le_M_mul_C x y)

/-- Named-ratio form of the concrete localization comparison. -/
theorem eta_le_etaCur
    (x y : I → ℝ)
    (hN : 0 ≤ R.N x y) (hH : 0 < R.H x y) (hM : 0 < R.M x y) :
    R.eta x y ≤ R.etaCur x y := by
  simpa [eta, etaCur] using R.etaCur_ge_eta_concrete x y hN hH hM

/-- Exact equality condition: both endpoints of every nonzero-current edge
carry the maximal squared mode amplitude. -/
theorem H_eq_M_mul_C_iff (x y : I → ℝ) :
    R.H x y = R.M x y * R.C ↔
      ∀ e : R.OrderedSupport,
        R.toRowMarkovData.current e.val.1 e.val.2 ≠ 0 →
          R.amplitude x y e.val.1 = R.M x y ∧
            R.amplitude x y e.val.2 = R.M x y := by
  rw [H, C]
  constructor
  · intro h e hcurrent
    have hall := (weighted_endpointAverage_eq_iff
      R.currentWeight
      (fun e : R.OrderedSupport ↦ R.amplitude x y e.val.1)
      (fun e : R.OrderedSupport ↦ R.amplitude x y e.val.2)
      (R.M x y)
      R.currentWeight_nonneg
      (fun q ↦ R.amplitude_le_M x y q.val.1)
      (fun q ↦ R.amplitude_le_M x y q.val.2)).mp h
    exact hall e ((R.currentWeight_pos_iff e).2 hcurrent)
  · intro hend
    apply (weighted_endpointAverage_eq_iff
      R.currentWeight
      (fun e : R.OrderedSupport ↦ R.amplitude x y e.val.1)
      (fun e : R.OrderedSupport ↦ R.amplitude x y e.val.2)
      (R.M x y)
      R.currentWeight_nonneg
      (fun q ↦ R.amplitude_le_M x y q.val.1)
      (fun q ↦ R.amplitude_le_M x y q.val.2)).2
    intro e hweight
    exact hend e ((R.currentWeight_pos_iff e).1 hweight)

/-- Pair-indexed form of the exact endpoint-max characterization. -/
theorem H_eq_M_mul_C_iff_all_pairs (x y : I → ℝ) :
    R.H x y = R.M x y * R.C ↔
      ∀ i j, R.toRowMarkovData.current i j ≠ 0 →
        R.amplitude x y i = R.M x y ∧ R.amplitude x y j = R.M x y := by
  constructor
  · intro h i j hij
    let e : R.OrderedSupport :=
      ⟨(i, j), R.toRowMarkovData.traffic_pos_of_current_ne_zero hij⟩
    exact (R.H_eq_M_mul_C_iff x y).mp h e hij
  · intro h
    apply (R.H_eq_M_mul_C_iff x y).2
    intro e he
    exact h e.val.1 e.val.2 he

/-- Equality of the concrete localization ratios is equivalent to the exact
endpoint-max condition. -/
theorem etaCur_eq_eta_iff_endpoint_max
    (x y : I → ℝ)
    (hN : 0 < R.N x y) (hH : 0 < R.H x y) (hM : 0 < R.M x y) :
    R.N x y * R.C / R.H x y = R.N x y / R.M x y ↔
      ∀ e : R.OrderedSupport,
        R.toRowMarkovData.current e.val.1 e.val.2 ≠ 0 →
          R.amplitude x y e.val.1 = R.M x y ∧
            R.amplitude x y e.val.2 = R.M x y := by
  rw [etaCur_eq_eta_iff_H_eq_MC hN hH hM]
  exact R.H_eq_M_mul_C_iff x y

/-- Pair-indexed form of equality for the concrete localization ratios. -/
theorem etaCur_eq_eta_iff_endpoint_max_all_pairs
    (x y : I → ℝ)
    (hN : 0 < R.N x y) (hH : 0 < R.H x y) (hM : 0 < R.M x y) :
    R.N x y * R.C / R.H x y = R.N x y / R.M x y ↔
      ∀ i j, R.toRowMarkovData.current i j ≠ 0 →
        R.amplitude x y i = R.M x y ∧ R.amplitude x y j = R.M x y := by
  rw [etaCur_eq_eta_iff_H_eq_MC hN hH hM]
  exact R.H_eq_M_mul_C_iff_all_pairs x y

/-- Named-ratio form of the exact endpoint-max equality condition. -/
theorem etaCur_eq_eta_iff_endpoint_max_all_pairs'
    (x y : I → ℝ)
    (hN : 0 < R.N x y) (hH : 0 < R.H x y) (hM : 0 < R.M x y) :
    R.etaCur x y = R.eta x y ↔
      ∀ i j, R.toRowMarkovData.current i j ≠ 0 →
        R.amplitude x y i = R.M x y ∧ R.amplitude x y j = R.M x y := by
  change (R.N x y * R.C / R.H x y = R.N x y / R.M x y) ↔ _
  exact R.etaCur_eq_eta_iff_endpoint_max_all_pairs x y hN hH hM

end BidirectionalRowMarkovData

end OBS.CoreBranch
