import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Scalar entropy-current inequality

The proof uses Mathlib's certified odd-power lower bounds for
`(1/2) * log ((1+r)/(1-r))`.  The `n = 1` truncation proves the weak bound;
the `n = 2` truncation proves strictness away from `r = 0`.
-/

namespace OBS.CoreBranch

/-- For ordered positive fluxes, the logarithmic mean bound in skew coordinates. -/
private theorem log_ratio_ge_two_skew
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hyx : y ≤ x) :
    2 * ((x - y) / (x + y)) ≤ Real.log (x / y) := by
  let r : ℝ := (x - y) / (x + y)
  have hsum : 0 < x + y := add_pos hx hy
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (sub_nonneg.mpr hyx) hsum.le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [div_lt_one hsum]
    linarith
  have hseries := Real.sum_range_le_log_div hr0 hr1 1
  have hmobius : (1 + r) / (1 - r) = x / y := by
    dsimp [r]
    field_simp [ne_of_gt hsum, ne_of_gt hy]
    ring
  norm_num [Finset.sum_range_succ] at hseries
  rw [hmobius] at hseries
  nlinarith

/-- The preceding logarithmic bound is strict when the two fluxes differ. -/
private theorem log_ratio_gt_two_skew
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hyx : y < x) :
    2 * ((x - y) / (x + y)) < Real.log (x / y) := by
  let r : ℝ := (x - y) / (x + y)
  have hsum : 0 < x + y := add_pos hx hy
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (sub_nonneg.mpr hyx.le) hsum.le
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos (sub_pos.mpr hyx) hsum
  have hr1 : r < 1 := by
    dsimp [r]
    rw [div_lt_one hsum]
    linarith
  have hseries := Real.sum_range_le_log_div hr0 hr1 2
  have hmobius : (1 + r) / (1 - r) = x / y := by
    dsimp [r]
    field_simp [ne_of_gt hsum, ne_of_gt hy]
    ring
  norm_num [Finset.sum_range_succ] at hseries
  rw [hmobius] at hseries
  have hcubic : 0 < r ^ 3 / 3 := by positivity
  nlinarith

/-- Ordered form of the scalar entropy-current inequality. -/
private theorem entropy_current_le_of_le
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hyx : y ≤ x) :
    2 * (x - y) ^ 2 / (x + y) ≤ (x - y) * Real.log (x / y) := by
  have hlog := log_ratio_ge_two_skew hx hy hyx
  have hmul := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hyx)
  calc
    2 * (x - y) ^ 2 / (x + y) =
        (x - y) * (2 * ((x - y) / (x + y))) := by
          field_simp [ne_of_gt (add_pos hx hy)]
    _ ≤ (x - y) * Real.log (x / y) := hmul

/-- Ordered strict form of the scalar entropy-current inequality. -/
private theorem entropy_current_lt_of_lt
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hyx : y < x) :
    2 * (x - y) ^ 2 / (x + y) < (x - y) * Real.log (x / y) := by
  have hlog := log_ratio_gt_two_skew hx hy hyx
  have hmul := mul_lt_mul_of_pos_left hlog (sub_pos.mpr hyx)
  calc
    2 * (x - y) ^ 2 / (x + y) =
        (x - y) * (2 * ((x - y) / (x + y))) := by
          field_simp [ne_of_gt (add_pos hx hy)]
    _ < (x - y) * Real.log (x / y) := hmul

/--
For positive directional fluxes, entropy production dominates twice the
quadratic current cost.
-/
theorem entropy_current_le
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2 * (x - y) ^ 2 / (x + y) ≤ (x - y) * Real.log (x / y) := by
  rcases le_total y x with hyx | hxy
  · exact entropy_current_le_of_le hx hy hyx
  · have hswap := entropy_current_le_of_le hy hx hxy
    rw [Real.log_div hy.ne' hx.ne'] at hswap
    rw [Real.log_div hx.ne' hy.ne']
    convert hswap using 1 <;> ring

/-- Strict scalar inequality whenever the two positive fluxes differ. -/
theorem entropy_current_lt_of_ne
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    2 * (x - y) ^ 2 / (x + y) < (x - y) * Real.log (x / y) := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hswap := entropy_current_lt_of_lt hy hx hlt
    rw [Real.log_div hy.ne' hx.ne'] at hswap
    rw [Real.log_div hx.ne' hy.ne']
    convert hswap using 1 <;> ring
  · exact entropy_current_lt_of_lt hx hy hgt

/-- Equality occurs exactly at zero current, i.e. `x = y`. -/
theorem entropy_current_eq_iff
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x - y) * Real.log (x / y) = 2 * (x - y) ^ 2 / (x + y) ↔ x = y := by
  constructor
  · intro h
    by_contra hne
    have hlt := entropy_current_lt_of_ne hx hy hne
    linarith
  · rintro rfl
    simp

section FiniteSum

open scoped BigOperators

variable {E : Type*} [Fintype E]

/-- Edgewise entropy-current inequalities sum without any connectivity assumption. -/
theorem sum_entropy_current_le
    (x y : E → ℝ) (hx : ∀ e, 0 < x e) (hy : ∀ e, 0 < y e) :
    ∑ e, 2 * (x e - y e) ^ 2 / (x e + y e) ≤
      ∑ e, (x e - y e) * Real.log (x e / y e) := by
  exact Finset.sum_le_sum fun e _ ↦ entropy_current_le (hx e) (hy e)

/-- One nonzero stationary current makes the summed inequality strict. -/
theorem sum_entropy_current_lt_of_exists_ne
    (x y : E → ℝ) (hx : ∀ e, 0 < x e) (hy : ∀ e, 0 < y e)
    (hne : ∃ e, x e ≠ y e) :
    ∑ e, 2 * (x e - y e) ^ 2 / (x e + y e) <
      ∑ e, (x e - y e) * Real.log (x e / y e) := by
  apply Finset.sum_lt_sum
  · intro e _
    exact entropy_current_le (hx e) (hy e)
  · rcases hne with ⟨e, he⟩
    exact ⟨e, Finset.mem_univ e, entropy_current_lt_of_ne (hx e) (hy e) he⟩

/-- The finite summed inequality is an equality iff every edge current vanishes. -/
theorem sum_entropy_current_eq_iff
    (x y : E → ℝ) (hx : ∀ e, 0 < x e) (hy : ∀ e, 0 < y e) :
    (∑ e, (x e - y e) * Real.log (x e / y e) =
      ∑ e, 2 * (x e - y e) ^ 2 / (x e + y e)) ↔ ∀ e, x e = y e := by
  constructor
  · intro h e
    by_contra he
    have hlt := sum_entropy_current_lt_of_exists_ne x y hx hy ⟨e, he⟩
    linarith
  · intro h
    simp [h]

end FiniteSum

end OBS.CoreBranch
