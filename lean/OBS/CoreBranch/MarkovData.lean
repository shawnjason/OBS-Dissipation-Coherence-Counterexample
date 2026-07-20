import OBS.CoreBranch.EigenmodeIdentities

/-!
# Finite row-forward Markov data

This module is the convention bridge between rates and the low-level weighted
real-mode algebra.  Rates are row-forward: `rate i j` is the jump rate
`i → j`, while `backwardAction` is the backward action on observables.
The diagonal rate is stored as zero; the negative escape rate is implicit in
the difference form of `backwardAction`.
-/

namespace OBS.CoreBranch

open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- Finite row-forward rate data with a positive normalized stationary law. -/
structure RowMarkovData (I : Type*) [Fintype I] where
  rate : I → I → ℝ
  pi : I → ℝ
  rate_nonneg : ∀ i j, 0 ≤ rate i j
  rate_diag_zero : ∀ i, rate i i = 0
  pi_pos : ∀ i, 0 < pi i
  pi_normalized : ∑ i, pi i = 1
  stationary : ∀ i,
    pi i * (∑ j, rate i j) = ∑ j, pi j * rate j i

namespace RowMarkovData

variable (M : RowMarkovData I)

/-- Stationary directed flow `a_ij = pi_i k_ij`. -/
def flow (i j : I) : ℝ := M.pi i * M.rate i j

/-- Antisymmetric stationary current in the orientation `i → j`. -/
def current (i j : I) : ℝ := M.flow i j - M.flow j i

/-- Symmetric stationary traffic. -/
def traffic (i j : I) : ℝ := M.flow i j + M.flow j i

/-- Backward-generator action on a real observable. -/
def backwardAction (v : I → ℝ) (i : I) : ℝ :=
  ∑ j, M.rate i j * (v j - v i)

@[simp] theorem current_swap (i j : I) : M.current j i = -M.current i j := by
  simp [current]

@[simp] theorem traffic_swap (i j : I) : M.traffic j i = M.traffic i j := by
  simp [traffic]
  ring

theorem flow_nonneg (i j : I) : 0 ≤ M.flow i j :=
  mul_nonneg (M.pi_pos i).le (M.rate_nonneg i j)

theorem traffic_nonneg (i j : I) : 0 ≤ M.traffic i j :=
  add_nonneg (M.flow_nonneg i j) (M.flow_nonneg j i)

/-- The stored stationary equation is exactly incoming/outgoing flow balance. -/
theorem flow_stationary (i : I) :
    ∑ j, M.flow i j = ∑ j, M.flow j i := by
  rw [show (∑ j, M.flow i j) = M.pi i * (∑ j, M.rate i j) by
    rw [Finset.mul_sum]
    rfl]
  simpa [flow] using M.stationary i

/-- A nonzero current cannot live on a zero-traffic pair. -/
theorem traffic_pos_of_current_ne_zero {i j : I}
    (hcurrent : M.current i j ≠ 0) : 0 < M.traffic i j := by
  have hfi := M.flow_nonneg i j
  have hfj := M.flow_nonneg j i
  by_contra hnot
  have hle : M.traffic i j ≤ 0 := le_of_not_gt hnot
  change M.flow i j + M.flow j i ≤ 0 at hle
  have hfi0 : M.flow i j = 0 := by
    nlinarith
  have hfj0 : M.flow j i = 0 := by
    nlinarith
  apply hcurrent
  simp [current, hfi0, hfj0]

/--
A real/imaginary backward eigen-equation becomes the weighted flow equation
used by `WeightedRealMode` after multiplication by the stationary weights.
-/
theorem weightedRealMode_of_backward_eigen_equations
    (x y : I → ℝ) (a b : ℝ)
    (hreal : ∀ i, M.backwardAction x i = -a * x i - b * y i)
    (himag : ∀ i, M.backwardAction y i = b * x i - a * y i) :
    WeightedRealMode M.flow M.pi x y a b := by
  constructor
  · intro i
    calc
      ∑ j, M.flow i j * (x j - x i) =
          M.pi i * M.backwardAction x i := by
            simp only [flow, backwardAction]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = M.pi i * (-a * x i - b * y i) := by rw [hreal i]
  · intro i
    calc
      ∑ j, M.flow i j * (y j - y i) =
          M.pi i * M.backwardAction y i := by
            simp only [flow, backwardAction]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = M.pi i * (b * x i - a * y i) := by rw [himag i]

/-- Positive stationary weights give positive mode norm from one nonzero coordinate. -/
theorem modeNorm_pos_of_exists_coordinate_ne_zero
    (x y : I → ℝ)
    (hne : ∃ i, x i ≠ 0 ∨ y i ≠ 0) :
    0 < modeNorm M.pi x y := by
  simp only [modeNorm]
  rcases hne with ⟨i, hxi | hyi⟩
  · apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (M.pi_pos j).le
        (add_nonneg (sq_nonneg (x j)) (sq_nonneg (y j)))
    · refine ⟨i, Finset.mem_univ i, mul_pos (M.pi_pos i) ?_⟩
      nlinarith [sq_pos_of_ne_zero hxi, sq_nonneg (y i)]
  · apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (M.pi_pos j).le
        (add_nonneg (sq_nonneg (x j)) (sq_nonneg (y j)))
    · refine ⟨i, Finset.mem_univ i, mul_pos (M.pi_pos i) ?_⟩
      nlinarith [sq_nonneg (x i), sq_pos_of_ne_zero hyi]

end RowMarkovData

end OBS.CoreBranch
