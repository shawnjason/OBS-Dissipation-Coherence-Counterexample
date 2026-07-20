import OBS.CoreBranch.ConcreteCauchy
import OBS.CoreBranch.PhaseDeficit
import OBS.CoreBranch.AlgebraicCore

/-!
# Concrete phase deficit

The parallelogram deficit is instantiated on the same ordered positive-traffic
support as the concrete Cauchy encoding.  Nonzero total phase coupling gives a
support edge on which both the current and the phase term are nonzero; this is
the positive deficit witness required for strictness.
-/

namespace OBS.CoreBranch

open scoped BigOperators

variable {I : Type*} [Fintype I]

namespace BidirectionalRowMarkovData

variable (R : BidirectionalRowMarkovData I)

def phaseSumSq (x y : I → ℝ) (e : R.OrderedSupport) : ℝ :=
  (x e.val.1 + x e.val.2) ^ 2 + (y e.val.1 + y e.val.2) ^ 2

def phaseDiffSq (x y : I → ℝ) (e : R.OrderedSupport) : ℝ :=
  (x e.val.2 - x e.val.1) ^ 2 + (y e.val.2 - y e.val.1) ^ 2

theorem phase_parallelogram (x y : I → ℝ) (e : R.OrderedSupport) :
    R.phaseSumSq x y e + R.phaseDiffSq x y e =
      2 * (R.amplitude x y e.val.1 + R.amplitude x y e.val.2) := by
  simp only [phaseSumSq, phaseDiffSq, amplitude]
  ring

theorem phaseDiffSq_nonneg (x y : I → ℝ) (e : R.OrderedSupport) :
    0 ≤ R.phaseDiffSq x y e := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem concrete_K_parallelogram_representation (x y : I → ℝ) :
    R.K x y = ∑ e : R.OrderedSupport,
      R.currentWeight e / 4 * R.phaseSumSq x y e := by
  rw [K]
  apply Finset.sum_congr rfl
  intro e _
  simp only [currentWeight, phaseSumSq]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem concrete_H_parallelogram_representation (x y : I → ℝ) :
    R.H x y = ∑ e : R.OrderedSupport,
      R.currentWeight e / 2 *
        (R.amplitude x y e.val.1 + R.amplitude x y e.val.2) := by
  rw [H]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Exact concrete identity `H - K = Σ currentWeight/4 * |v_j-v_i|²`. -/
theorem concrete_H_sub_K_identity (x y : I → ℝ) :
    R.H x y - R.K x y = ∑ e : R.OrderedSupport,
      R.currentWeight e / 4 * R.phaseDiffSq x y e := by
  rw [R.concrete_H_parallelogram_representation x y,
    R.concrete_K_parallelogram_representation x y]
  exact H_sub_K_identity
    R.currentWeight (fun e ↦ R.amplitude x y e.val.1)
    (fun e ↦ R.amplitude x y e.val.2) (R.phaseSumSq x y)
    (R.phaseDiffSq x y) (R.phase_parallelogram x y)

/-- Nonzero concrete `B` exposes a support summand with nonzero current-phase
product, stronger than merely exposing a nonzero current. -/
theorem exists_current_mul_phase_ne_zero_of_B_ne_zero
    (x y : I → ℝ) (hB : R.B x y ≠ 0) :
    ∃ e : R.OrderedSupport,
      R.toRowMarkovData.current e.val.1 e.val.2 *
        (x e.val.1 * y e.val.2 - y e.val.1 * x e.val.2) ≠ 0 := by
  by_contra h
  push Not at h
  apply hB
  rw [R.concrete_B_support_representation x y]
  apply Finset.sum_eq_zero
  intro e _
  have he := h e
  calc
    R.toRowMarkovData.current e.val.1 e.val.2 / 2 *
        (x e.val.1 * y e.val.2 - y e.val.1 * x e.val.2) =
      (R.toRowMarkovData.current e.val.1 e.val.2 *
        (x e.val.1 * y e.val.2 - y e.val.1 * x e.val.2)) / 2 := by ring
    _ = 0 := by rw [he]; norm_num

theorem phaseDiffSq_pos_of_phase_ne_zero
    (x y : I → ℝ) (e : R.OrderedSupport)
    (hphase : x e.val.1 * y e.val.2 - y e.val.1 * x e.val.2 ≠ 0) :
    0 < R.phaseDiffSq x y e := by
  have hnot : ¬ (x e.val.2 - x e.val.1 = 0 ∧
      y e.val.2 - y e.val.1 = 0) := by
    rintro ⟨hx, hy⟩
    apply hphase
    have hx' : x e.val.2 = x e.val.1 := sub_eq_zero.mp hx
    have hy' : y e.val.2 = y e.val.1 := sub_eq_zero.mp hy
    rw [hx', hy']
    ring
  rcases not_and_or.mp hnot with hx | hy
  · unfold phaseDiffSq
    nlinarith [sq_pos_of_ne_zero hx,
      sq_nonneg (y e.val.2 - y e.val.1)]
  · unfold phaseDiffSq
    nlinarith [sq_nonneg (x e.val.2 - x e.val.1),
      sq_pos_of_ne_zero hy]

/-- Nonzero `B` produces the exact positive coefficient/deficit witness. -/
theorem exists_positive_phase_deficit_of_B_ne_zero
    (x y : I → ℝ) (hB : R.B x y ≠ 0) :
    ∃ e : R.OrderedSupport,
      0 < R.currentWeight e ∧ 0 < R.phaseDiffSq x y e := by
  rcases R.exists_current_mul_phase_ne_zero_of_B_ne_zero x y hB with
    ⟨e, he⟩
  have hj : R.toRowMarkovData.current e.val.1 e.val.2 ≠ 0 :=
    fun hzero ↦ he (by rw [hzero]; ring)
  have hphase : x e.val.1 * y e.val.2 - y e.val.1 * x e.val.2 ≠ 0 :=
    fun hzero ↦ he (by rw [hzero]; ring)
  exact ⟨e, (R.currentWeight_pos_iff e).2 hj,
    R.phaseDiffSq_pos_of_phase_ne_zero x y e hphase⟩

/-- Concrete strict parallelogram deficit `K < H`, derived from `B ≠ 0`. -/
theorem concrete_K_lt_H_of_B_ne_zero
    (x y : I → ℝ) (hB : R.B x y ≠ 0) :
    R.K x y < R.H x y := by
  rw [R.concrete_K_parallelogram_representation x y,
    R.concrete_H_parallelogram_representation x y]
  exact K_lt_H_of_exists_positive_deficit
    R.currentWeight (fun e ↦ R.amplitude x y e.val.1)
    (fun e ↦ R.amplitude x y e.val.2) (R.phaseSumSq x y)
    (R.phaseDiffSq x y) R.currentWeight_nonneg
    (R.phaseDiffSq_nonneg x y) (R.phase_parallelogram x y)
    (R.exists_positive_phase_deficit_of_B_ne_zero x y hB)

/-- Concrete strict phase coupling `B² < D H`. -/
theorem concrete_B_sq_lt_DH_of_B_ne_zero
    (x y : I → ℝ) (hB : R.B x y ≠ 0) :
    (R.B x y) ^ 2 < R.D x y * R.H x y := by
  have hBK := R.concrete_B_sq_le_DK x y
  have hDpos : 0 < R.D x y := by
    by_contra hnot
    have hDzero : R.D x y = 0 :=
      le_antisymm (le_of_not_gt hnot) (R.concrete_D_nonneg x y)
    rw [hDzero, zero_mul] at hBK
    exact (not_lt_of_ge hBK) (sq_pos_of_ne_zero hB)
  exact phaseCoupling_sq_lt_DH_of_lt hDpos hBK
    (R.concrete_K_lt_H_of_B_ne_zero x y hB)

end BidirectionalRowMarkovData

end OBS.CoreBranch
