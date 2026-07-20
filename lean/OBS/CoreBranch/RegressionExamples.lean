import OBS.CoreBranch.ConcreteLocalization

/-!
# Exact regression examples for the concrete edge interface

These rational examples exercise reversibility, sparse support, the distinction
between current and phase variation, localization saturation, and the ordered
pair factor `1/2`. They are tests only and are not used by the general theorem.
-/

namespace OBS.CoreBranch.RegressionExamples

open scoped BigOperators

inductive TestState where
  | s0 | s1 | s2
  deriving DecidableEq, Fintype

open TestState

theorem testState_univ :
    (Finset.univ : Finset TestState) = {s0, s1, s2} := by
  decide

/-- A reversible three-state path with the edge `s0--s2` absent. -/
def sparseRate : TestState → TestState → ℝ
  | s0, s1 | s1, s0 | s1, s2 | s2, s1 => 1
  | _, _ => 0

noncomputable def uniformPi : TestState → ℝ := fun _ ↦ 1 / 3

noncomputable def sparseRow : RowMarkovData TestState where
  rate := sparseRate
  pi := uniformPi
  rate_nonneg := by
    intro i j
    cases i <;> cases j <;> norm_num [sparseRate]
  rate_diag_zero := by
    intro i
    cases i <;> norm_num [sparseRate]
  pi_pos := by intro i; norm_num [uniformPi]
  pi_normalized := by
    simp [uniformPi, testState_univ]
  stationary := by
    intro i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change uniformPi i * sparseRate i j = uniformPi j * sparseRate j i
    rw [show sparseRate i j = sparseRate j i by
      cases i <;> cases j <;> rfl]
    simp [uniformPi]

theorem sparse_flow_symmetric (i j : TestState) :
    sparseRow.flow i j = sparseRow.flow j i := by
  cases i <;> cases j <;>
    norm_num [sparseRow, sparseRate, uniformPi, RowMarkovData.flow]

noncomputable def sparseBidirectional : BidirectionalRowMarkovData TestState where
  toRowMarkovData := sparseRow
  flow_pos_of_traffic_pos := by
    intro i j hij
    change 0 < sparseRow.traffic i j at hij
    have hsym := sparse_flow_symmetric i j
    have hforward : 0 < sparseRow.flow i j := by
      simp only [RowMarkovData.traffic] at hij
      nlinarith
    exact ⟨hforward, by simpa [hsym] using hforward⟩

/-- Regression 1: a reversible sparse chain has zero phase/current pairing. -/
theorem reversible_sparse_B_eq_zero (x y : TestState → ℝ) :
    sparseBidirectional.B x y = 0 := by
  unfold BidirectionalRowMarkovData.B modeB
  apply mul_eq_zero_of_right
  unfold pairSum
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  change (sparseBidirectional.toRowMarkovData.flow i j -
      sparseBidirectional.toRowMarkovData.flow j i) *
        (x i * y j - y i * x j) = 0
  have hsym : sparseBidirectional.toRowMarkovData.flow i j =
      sparseBidirectional.toRowMarkovData.flow j i := by
    change sparseRow.flow i j = sparseRow.flow j i
    exact sparse_flow_symmetric i j
  rw [hsym, sub_self, zero_mul]

/-- Regression 2: the sparse path retains an actually absent edge. -/
theorem sparse_absent_edge : sparseRow.traffic s0 s2 = 0 := by
  norm_num [sparseRow, sparseRate, uniformPi, RowMarkovData.traffic,
    RowMarkovData.flow]

/-- A bidirectional nonequilibrium cycle: clockwise rate `2`, reverse rate `1`. -/
def cycleRate : TestState → TestState → ℝ
  | s0, s1 | s1, s2 | s2, s0 => 2
  | s1, s0 | s2, s1 | s0, s2 => 1
  | _, _ => 0

noncomputable def cycleRow : RowMarkovData TestState where
  rate := cycleRate
  pi := uniformPi
  rate_nonneg := by
    intro i j
    cases i <;> cases j <;> norm_num [cycleRate]
  rate_diag_zero := by
    intro i
    cases i <;> norm_num [cycleRate]
  pi_pos := by intro i; norm_num [uniformPi]
  pi_normalized := by
    simp [uniformPi, testState_univ]
  stationary := by
    intro i
    cases i <;> simp [uniformPi, cycleRate, testState_univ] <;> norm_num

def flatX : TestState → ℝ := fun _ ↦ 1
def flatY : TestState → ℝ := fun _ ↦ 0

/-- Regression 3: nonzero current alone does not imply positive phase deficit. -/
theorem current_nonzero_but_phase_and_difference_zero :
    cycleRow.current s0 s1 ≠ 0 ∧
      flatX s0 * flatY s1 - flatY s0 * flatX s1 = 0 ∧
      (flatX s1 - flatX s0) ^ 2 + (flatY s1 - flatY s0) ^ 2 = 0 := by
  norm_num [cycleRow, cycleRate, uniformPi, flatX, flatY,
    RowMarkovData.current, RowMarkovData.flow]

/-- Regression 4: a two-edge family saturates endpoint localization at `M`. -/
theorem synthetic_localization_saturation :
    (∑ _e : Fin 2, (1 : ℝ) * (((3 : ℝ) + 3) / 2)) =
      3 * ∑ _e : Fin 2, (1 : ℝ) := by
  norm_num [Fin.sum_univ_two]

def symmetricDirectedCost : TestState → TestState → ℝ
  | s0, s0 | s1, s1 | s2, s2 => 0
  | _, _ => 1

/-- Regression 5: half of six oriented terms equals three undirected terms. -/
theorem three_state_ordered_half_conversion :
    (1 / 2 : ℝ) * pairSum symmetricDirectedCost =
      symmetricDirectedCost s0 s1 + symmetricDirectedCost s1 s2 +
        symmetricDirectedCost s2 s0 := by
  have hsum : pairSum symmetricDirectedCost = (6 : ℝ) := by
    simp [pairSum, symmetricDirectedCost, testState_univ]
    norm_num
  norm_num [hsum, symmetricDirectedCost]

end OBS.CoreBranch.RegressionExamples
