import Mathlib

/-!
# Finite phase-deficit algebra

This module abstracts only the parallelogram identity.  It can be instantiated
with `leftSq = |v_i|^2`, `rightSq = |v_j|^2`,
`sumSq = |v_i+v_j|^2`, and `diffSq = |v_j-v_i|^2`.
-/

namespace OBS.CoreBranch

open scoped BigOperators

variable {E : Type*} [Fintype E]

/-- Exact identity `H - K = deficit` for arbitrary finite edge data. -/
theorem H_sub_K_identity
    (coeff leftSq rightSq sumSq diffSq : E → ℝ)
    (hpar : ∀ e, sumSq e + diffSq e = 2 * (leftSq e + rightSq e)) :
    (∑ e, coeff e / 2 * (leftSq e + rightSq e)) -
        ∑ e, coeff e / 4 * sumSq e =
      ∑ e, coeff e / 4 * diffSq e := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hp := hpar e
  have hdiff : 2 * (leftSq e + rightSq e) - sumSq e = diffSq e := by
    linarith
  calc
    coeff e / 2 * (leftSq e + rightSq e) - coeff e / 4 * sumSq e =
        coeff e / 4 * (2 * (leftSq e + rightSq e) - sumSq e) := by ring
    _ = coeff e / 4 * diffSq e := by rw [hdiff]

/-- The exact deficit is nonnegative under nonnegative coefficients and squared differences. -/
theorem K_le_H_of_parallelogram
    (coeff leftSq rightSq sumSq diffSq : E → ℝ)
    (hcoeff : ∀ e, 0 ≤ coeff e) (hdiff : ∀ e, 0 ≤ diffSq e)
    (hpar : ∀ e, sumSq e + diffSq e = 2 * (leftSq e + rightSq e)) :
    ∑ e, coeff e / 4 * sumSq e ≤
      ∑ e, coeff e / 2 * (leftSq e + rightSq e) := by
  have hdef : 0 ≤ ∑ e, coeff e / 4 * diffSq e := by
    apply Finset.sum_nonneg
    intro e _
    exact mul_nonneg (div_nonneg (hcoeff e) (by norm_num)) (hdiff e)
  rw [← H_sub_K_identity coeff leftSq rightSq sumSq diffSq hpar] at hdef
  linarith

/-- A positive coefficient on a genuinely varying edge makes `K < H`. -/
theorem K_lt_H_of_exists_positive_deficit
    (coeff leftSq rightSq sumSq diffSq : E → ℝ)
    (hcoeff : ∀ e, 0 ≤ coeff e) (hdiff : ∀ e, 0 ≤ diffSq e)
    (hpar : ∀ e, sumSq e + diffSq e = 2 * (leftSq e + rightSq e))
    (hex : ∃ e, 0 < coeff e ∧ 0 < diffSq e) :
    ∑ e, coeff e / 4 * sumSq e <
      ∑ e, coeff e / 2 * (leftSq e + rightSq e) := by
  have hdef : 0 < ∑ e, coeff e / 4 * diffSq e := by
    apply Finset.sum_pos'
    · intro e _
      exact mul_nonneg (div_nonneg (hcoeff e) (by norm_num)) (hdiff e)
    · rcases hex with ⟨e, hce, hde⟩
      exact ⟨e, Finset.mem_univ e, mul_pos (div_pos hce (by norm_num)) hde⟩
  rw [← H_sub_K_identity coeff leftSq rightSq sumSq diffSq hpar] at hdef
  linarith

end OBS.CoreBranch
