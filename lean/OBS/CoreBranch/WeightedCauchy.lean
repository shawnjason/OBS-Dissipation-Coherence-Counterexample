import Mathlib

/-!
# Explicit finite weighted Cauchy layer

The mode-specific square-root weighting is intentionally separated from this
lemma.  A caller supplies the two real component arrays whose scalar product
is `B`, and whose squared norms are `D` and `K`.
-/

namespace OBS.CoreBranch

open scoped BigOperators

variable {E : Type*} [Fintype E]

/-- Cauchy--Schwarz for a finite real family, in the exact squared form used by OBS. -/
theorem finite_sum_mul_sq_le
    (f g : E → ℝ) :
    (∑ e, f e * g e) ^ 2 ≤ (∑ e, f e ^ 2) * ∑ e, g e ^ 2 := by
  simpa using (Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ f g)

/-- Weighted finite Cauchy--Schwarz with strictly positive denominators. -/
theorem weighted_sum_mul_sq_le
    (T u v : E → ℝ) (hT : ∀ e, 0 < T e) :
    (∑ e, u e * v e) ^ 2 ≤
      (∑ e, T e * u e ^ 2) * ∑ e, v e ^ 2 / T e := by
  let f : E → ℝ := fun e ↦ √(T e) * u e
  let g : E → ℝ := fun e ↦ v e / √(T e)
  have hdot : ∑ e, f e * g e = ∑ e, u e * v e := by
    apply Finset.sum_congr rfl
    intro e _
    dsimp [f, g]
    have hsqrt : √(T e) ≠ 0 := (Real.sqrt_pos.2 (hT e)).ne'
    field_simp [hsqrt]
  have hfnorm : ∑ e, f e ^ 2 = ∑ e, T e * u e ^ 2 := by
    apply Finset.sum_congr rfl
    intro e _
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt (hT e).le]
  have hgnorm : ∑ e, g e ^ 2 = ∑ e, v e ^ 2 / T e := by
    apply Finset.sum_congr rfl
    intro e _
    dsimp [g]
    rw [div_pow, Real.sq_sqrt (hT e).le]
  have hcs := finite_sum_mul_sq_le f g
  rwa [hdot, hfnorm, hgnorm] at hcs

/-- Direct `B² ≤ D K` interface for a positive weighted encoding. -/
theorem weighted_phaseCoupling_sq_le_DK
    (B D K : ℝ) (T u v : E → ℝ) (hT : ∀ e, 0 < T e)
    (hB : B = ∑ e, u e * v e)
    (hD : D = ∑ e, T e * u e ^ 2)
    (hK : K = ∑ e, v e ^ 2 / T e) :
    B ^ 2 ≤ D * K := by
  rw [hB, hD, hK]
  exact weighted_sum_mul_sq_le T u v hT

/-- Named `B² ≤ D K` interface for an explicit finite Cauchy encoding. -/
theorem phaseCoupling_sq_le_DK
    (B D K : ℝ) (f g : E → ℝ)
    (hB : B = ∑ e, f e * g e)
    (hD : D = ∑ e, f e ^ 2)
    (hK : K = ∑ e, g e ^ 2) :
    B ^ 2 ≤ D * K := by
  rw [hB, hD, hK]
  exact finite_sum_mul_sq_le f g

/-- The two squared norms in a finite Cauchy encoding are nonnegative. -/
theorem cauchy_norms_nonneg
    (D K : ℝ) (f g : E → ℝ)
    (hD : D = ∑ e, f e ^ 2)
    (hK : K = ∑ e, g e ^ 2) :
    0 ≤ D ∧ 0 ≤ K := by
  constructor
  · rw [hD]
    exact Finset.sum_nonneg fun e _ ↦ sq_nonneg (f e)
  · rw [hK]
    exact Finset.sum_nonneg fun e _ ↦ sq_nonneg (g e)

end OBS.CoreBranch
