import Mathlib

/-!
# Finite current-weighted localization algebra

The edge type is arbitrary and finite.  `leftAmp` and `rightAmp` are the
squared endpoint amplitudes, so this file stays entirely over `ℝ`.
-/

namespace OBS.CoreBranch

open scoped BigOperators

section WeightedAverage

variable {E : Type*} [Fintype E]

/-- A weighted average of endpoint amplitudes is bounded by their common maximum. -/
theorem weighted_endpointAverage_le_max
    (w leftAmp rightAmp : E → ℝ) (M : ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (hl : ∀ e, leftAmp e ≤ M)
    (hr : ∀ e, rightAmp e ≤ M) :
    ∑ e, w e * ((leftAmp e + rightAmp e) / 2) ≤ M * ∑ e, w e := by
  calc
    ∑ e, w e * ((leftAmp e + rightAmp e) / 2) ≤ ∑ e, w e * M := by
      refine Finset.sum_le_sum fun e _ ↦ ?_
      apply mul_le_mul_of_nonneg_left _ (hw e)
      linarith [hl e, hr e]
    _ = M * ∑ e, w e := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring

/-- Exact deficit identity behind the current-weighted localization bound. -/
theorem weighted_endpointAverage_deficit
    (w leftAmp rightAmp : E → ℝ) (M : ℝ) :
    M * (∑ e, w e) - ∑ e, w e * ((leftAmp e + rightAmp e) / 2) =
      ∑ e, w e * (((M - leftAmp e) + (M - rightAmp e)) / 2) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

/--
Equality holds exactly when both endpoints of every positive-weight edge are
at the common maximum.
-/
theorem weighted_endpointAverage_eq_iff
    (w leftAmp rightAmp : E → ℝ) (M : ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (hl : ∀ e, leftAmp e ≤ M)
    (hr : ∀ e, rightAmp e ≤ M) :
    (∑ e, w e * ((leftAmp e + rightAmp e) / 2) = M * ∑ e, w e) ↔
      ∀ e, 0 < w e → leftAmp e = M ∧ rightAmp e = M := by
  classical
  constructor
  · intro hsum e hwe
    let deficit : E → ℝ := fun x ↦
      w x * (((M - leftAmp x) + (M - rightAmp x)) / 2)
    have hdef_nonneg : ∀ x, 0 ≤ deficit x := by
      intro x
      change 0 ≤ w x * (((M - leftAmp x) + (M - rightAmp x)) / 2)
      exact mul_nonneg (hw x) (by linarith [hl x, hr x])
    have hdef_sum : ∑ x, deficit x = 0 := by
      rw [← weighted_endpointAverage_deficit w leftAmp rightAmp M]
      linarith
    have hle : deficit e ≤ ∑ x, deficit x := by
      exact Finset.single_le_sum (fun x _ ↦ hdef_nonneg x) (Finset.mem_univ e)
    have hdef_e : deficit e = 0 := by
      apply le_antisymm
      · simpa [hdef_sum] using hle
      · exact hdef_nonneg e
    have hbracket : ((M - leftAmp e) + (M - rightAmp e)) / 2 = 0 := by
      have hwne : w e ≠ 0 := ne_of_gt hwe
      exact (mul_eq_zero.mp (by simpa [deficit] using hdef_e)).resolve_left hwne
    constructor <;> linarith [hl e, hr e]
  · intro hend
    apply le_antisymm
    · exact weighted_endpointAverage_le_max w leftAmp rightAmp M hw hl hr
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e _
      by_cases hwe : w e = 0
      · simp [hwe]
      · have hwpos : 0 < w e := lt_of_le_of_ne (hw e) (Ne.symm hwe)
        rcases hend e hwpos with ⟨hle, hre⟩
        rw [hle, hre]
        exact le_of_eq (by ring)

end WeightedAverage

section LocalizationRatios

/-- `H ≤ M*C` implies the current-weighted localization comparison. -/
theorem etaCur_ge_eta
    {N C H M : ℝ}
    (hN : 0 ≤ N) (hH : 0 < H) (hM : 0 < M)
    (hHC : H ≤ M * C) :
    N / M ≤ N * C / H := by
  rw [div_le_div_iff₀ hM hH]
  have hmul := mul_nonneg hN (sub_nonneg.mpr hHC)
  nlinarith

/-- Equality of the two localization ratios is exactly equality in `H ≤ M*C`. -/
theorem etaCur_eq_eta_iff_H_eq_MC
    {N C H M : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hM : 0 < M) :
    N * C / H = N / M ↔ H = M * C := by
  constructor
  · intro h
    field_simp at h
    nlinarith
  · intro h
    have hC : C ≠ 0 := by
      intro hC0
      rw [hC0, mul_zero] at h
      linarith
    rw [h]
    field_simp [hC]

end LocalizationRatios

end OBS.CoreBranch
