import Mathlib

/-!
# Stationary-flow eigenmode identities

The complex mode is represented by real and imaginary coordinates `x,y`.
`flow i j = π_i k_ij` is allowed to include zero diagonal entries.  Stationarity
is exactly equality of incoming and outgoing flow at every vertex.
-/

namespace OBS.CoreBranch

open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- Sum over all ordered pairs. -/
def pairSum (f : I → I → ℝ) : ℝ := ∑ i, ∑ j, f i j

@[simp] theorem pairSum_add (f g : I → I → ℝ) :
    pairSum (fun i j ↦ f i j + g i j) = pairSum f + pairSum g := by
  simp [pairSum, Finset.sum_add_distrib]

@[simp] theorem pairSum_sub (f g : I → I → ℝ) :
    pairSum (fun i j ↦ f i j - g i j) = pairSum f - pairSum g := by
  simp [pairSum, Finset.sum_sub_distrib]

@[simp] theorem pairSum_const_mul (c : ℝ) (f : I → I → ℝ) :
    pairSum (fun i j ↦ c * f i j) = c * pairSum f := by
  simp [pairSum, Finset.mul_sum]

theorem pairSum_congr {f g : I → I → ℝ} (h : ∀ i j, f i j = g i j) :
    pairSum f = pairSum g := by
  simp only [pairSum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact h i j

theorem pairSum_swap (f : I → I → ℝ) :
    pairSum (fun i j ↦ f j i) = pairSum f := by
  simp only [pairSum]
  rw [Finset.sum_comm]

/-- Stationarity transports a vertex observable from the arrival to the departure index. -/
theorem stationary_transport
    (flow : I → I → ℝ)
    (hstat : ∀ i, ∑ j, flow i j = ∑ j, flow j i)
    (f : I → ℝ) :
    pairSum (fun i j ↦ flow i j * f j) =
      pairSum (fun i j ↦ flow i j * f i) := by
  calc
    pairSum (fun i j ↦ flow i j * f j) =
        ∑ j, f j * ∑ i, flow i j := by
          rw [pairSum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ j, f j * ∑ i, flow j i := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hstat j]
    _ = pairSum (fun i j ↦ flow i j * f i) := by
          rw [pairSum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring

/-- Scalar stationary Dirichlet identity. -/
theorem stationary_dirichlet_identity
    (flow : I → I → ℝ)
    (hstat : ∀ i, ∑ j, flow i j = ∑ j, flow j i)
    (x : I → ℝ) :
    pairSum (fun i j ↦ flow i j * x i * (x j - x i)) =
      -(1 / 2 : ℝ) * pairSum (fun i j ↦ flow i j * (x j - x i) ^ 2) := by
  let A := pairSum (fun i j ↦ flow i j * (x i * x j))
  let Xi := pairSum (fun i j ↦ flow i j * x i ^ 2)
  let Xj := pairSum (fun i j ↦ flow i j * x j ^ 2)
  have htransport : Xj = Xi := stationary_transport flow hstat (fun i ↦ x i ^ 2)
  have hlhs : pairSum (fun i j ↦ flow i j * x i * (x j - x i)) = A - Xi := by
    calc
      pairSum (fun i j ↦ flow i j * x i * (x j - x i)) =
          pairSum (fun i j ↦ flow i j * (x i * x j) - flow i j * x i ^ 2) := by
            apply pairSum_congr
            intro i j
            ring
      _ = A - Xi := by simp [A, Xi]
  have hrhs : pairSum (fun i j ↦ flow i j * (x j - x i) ^ 2) =
      Xj - 2 * A + Xi := by
    calc
      pairSum (fun i j ↦ flow i j * (x j - x i) ^ 2) =
          pairSum (fun i j ↦
            (flow i j * x j ^ 2 - 2 * (flow i j * (x i * x j))) +
              flow i j * x i ^ 2) := by
                apply pairSum_congr
                intro i j
                ring
      _ = Xj - 2 * A + Xi := by simp [A, Xi, Xj]
  rw [hlhs, hrhs, htransport]
  ring

/-- The antisymmetric current-phase sum is the imaginary weighted form. -/
theorem stationary_phase_identity
    (flow : I → I → ℝ) (x y : I → ℝ) :
    pairSum (fun i j ↦ flow i j * (x i * y j - y i * x j)) =
      (1 / 2 : ℝ) * pairSum (fun i j ↦
        (flow i j - flow j i) * (x i * y j - y i * x j)) := by
  have hrev : pairSum (fun i j ↦ flow j i * (x i * y j - y i * x j)) =
      -pairSum (fun i j ↦ flow i j * (x i * y j - y i * x j)) := by
    calc
      pairSum (fun i j ↦ flow j i * (x i * y j - y i * x j)) =
          pairSum (fun i j ↦ flow i j * (x j * y i - y j * x i)) := by
            rw [← pairSum_swap (fun i j ↦ flow j i * (x i * y j - y i * x j))]
      _ = -pairSum (fun i j ↦ flow i j * (x i * y j - y i * x j)) := by
            calc
              pairSum (fun i j ↦ flow i j * (x j * y i - y j * x i)) =
                  pairSum (fun i j ↦ -(flow i j * (x i * y j - y i * x j))) := by
                    apply pairSum_congr
                    intro i j
                    ring
              _ = -pairSum (fun i j ↦ flow i j * (x i * y j - y i * x j)) := by
                    simp [pairSum]
  have hsplit : pairSum (fun i j ↦
      (flow i j - flow j i) * (x i * y j - y i * x j)) =
      pairSum (fun i j ↦ flow i j * (x i * y j - y i * x j)) -
        pairSum (fun i j ↦ flow j i * (x i * y j - y i * x j)) := by
    rw [← pairSum_sub]
    apply pairSum_congr
    intro i j
    ring
  rw [hsplit, hrev]
  ring

/-- Weighted real-coordinate form of a nonreal eigenmode. -/
structure WeightedRealMode (flow : I → I → ℝ) (pi x y : I → ℝ)
    (a b : ℝ) : Prop where
  real_eq : ∀ i, ∑ j, flow i j * (x j - x i) = pi i * (-a * x i - b * y i)
  imag_eq : ∀ i, ∑ j, flow i j * (y j - y i) = pi i * (b * x i - a * y i)

def modeNorm (pi x y : I → ℝ) : ℝ := ∑ i, pi i * (x i ^ 2 + y i ^ 2)

def modeD (flow : I → I → ℝ) (x y : I → ℝ) : ℝ :=
  pairSum (fun i j ↦ flow i j * ((x j - x i) ^ 2 + (y j - y i) ^ 2))

noncomputable def modeB (flow : I → I → ℝ) (x y : I → ℝ) : ℝ :=
  (1 / 2 : ℝ) * pairSum (fun i j ↦
    (flow i j - flow j i) * (x i * y j - y i * x j))

/-- Exact weighted eigenmode identities `a*N = D/2` and `b*N = B`. -/
theorem weighted_eigenmode_identities
    (flow : I → I → ℝ) (pi x y : I → ℝ) (a b : ℝ)
    (hstat : ∀ i, ∑ j, flow i j = ∑ j, flow j i)
    (hmode : WeightedRealMode flow pi x y a b) :
    a * modeNorm pi x y = modeD flow x y / 2 ∧
      b * modeNorm pi x y = modeB flow x y := by
  have hxdir := stationary_dirichlet_identity flow hstat x
  have hydir := stationary_dirichlet_identity flow hstat y
  have hreal :
      pairSum (fun i j ↦ flow i j *
        (x i * (x j - x i) + y i * (y j - y i))) =
        -a * modeNorm pi x y := by
    calc
      pairSum (fun i j ↦ flow i j *
          (x i * (x j - x i) + y i * (y j - y i))) =
          ∑ i, (x i * (∑ j, flow i j * (x j - x i)) +
            y i * (∑ j, flow i j * (y j - y i))) := by
              simp only [pairSum]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = -a * modeNorm pi x y := by
              dsimp [modeNorm]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [hmode.real_eq i, hmode.imag_eq i]
              ring
  have himag :
      pairSum (fun i j ↦ flow i j * (x i * y j - y i * x j)) =
        b * modeNorm pi x y := by
    simp only [pairSum]
    calc
      ∑ i, ∑ j, flow i j * (x i * y j - y i * x j) =
          ∑ i, (x i * (∑ j, flow i j * (y j - y i)) -
            y i * (∑ j, flow i j * (x j - x i))) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = b * modeNorm pi x y := by
              dsimp [modeNorm]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [hmode.real_eq i, hmode.imag_eq i]
              ring
  constructor
  · dsimp [modeD]
    have hsplit :
        pairSum (fun i j ↦ flow i j *
          (x i * (x j - x i) + y i * (y j - y i))) =
          pairSum (fun i j ↦ flow i j * x i * (x j - x i)) +
            pairSum (fun i j ↦ flow i j * y i * (y j - y i)) := by
      rw [← pairSum_add]
      apply pairSum_congr
      intro i j
      ring
    have hDsplit :
        pairSum (fun i j ↦ flow i j *
          ((x j - x i) ^ 2 + (y j - y i) ^ 2)) =
          pairSum (fun i j ↦ flow i j * (x j - x i) ^ 2) +
            pairSum (fun i j ↦ flow i j * (y j - y i) ^ 2) := by
      rw [← pairSum_add]
      apply pairSum_congr
      intro i j
      ring
    rw [hsplit, hxdir, hydir] at hreal
    rw [hDsplit]
    nlinarith
  · dsimp [modeB]
    rw [← stationary_phase_identity flow x y]
    exact himag.symm

/-- A nonzero-frequency mode with positive norm has nonzero phase/current coupling. -/
theorem modeB_ne_zero_of_nonreal
    {flow : I → I → ℝ} {pi x y : I → ℝ} {b : ℝ}
    (hN : 0 < modeNorm pi x y) (hb : b ≠ 0)
    (hid : b * modeNorm pi x y = modeB flow x y) :
    modeB flow x y ≠ 0 := by
  rw [← hid]
  exact mul_ne_zero hb hN.ne'

/-- Nonzero phase/current coupling forces at least one nonzero ordered-pair current. -/
theorem exists_nonzero_current_of_modeB_ne_zero
    {flow : I → I → ℝ} {x y : I → ℝ}
    (hB : modeB flow x y ≠ 0) :
    ∃ i j, flow i j - flow j i ≠ 0 := by
  by_contra h
  push Not at h
  apply hB
  simp [modeB, pairSum, h]

end OBS.CoreBranch
