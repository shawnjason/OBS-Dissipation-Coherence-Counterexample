import OBS.CoreBranch.MarkovData

/-!
# Concrete ordered-edge data

This module fixes the ordered-pair normalization used by the generator-level
OBS theorem.  Sums are restricted to pairs of positive traffic, so sparse
generators require no artificial positivity assumption on absent edges.
-/

namespace OBS.CoreBranch

open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- Row-forward Markov data whose positive-traffic edges have both directed
flows positive.  This is the concrete support condition needed for logarithms
of forward/reverse flow ratios. -/
structure BidirectionalRowMarkovData (I : Type*) [Fintype I]
    extends RowMarkovData I where
  flow_pos_of_traffic_pos : ∀ i j,
    0 < toRowMarkovData.traffic i j →
      0 < toRowMarkovData.flow i j ∧ 0 < toRowMarkovData.flow j i

namespace BidirectionalRowMarkovData

variable (R : BidirectionalRowMarkovData I)

/-- Ordered pairs carrying positive symmetric traffic. -/
def OrderedSupport := {p : I × I // 0 < R.toRowMarkovData.traffic p.1 p.2}

noncomputable instance : Fintype R.OrderedSupport :=
  Subtype.fintype _

theorem orderedSupport_nonempty_iff : Nonempty R.OrderedSupport ↔
    ∃ i j, 0 < R.toRowMarkovData.traffic i j := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.val.1, e.val.2, e.property⟩
  · rintro ⟨i, j, hij⟩
    exact ⟨⟨(i, j), hij⟩⟩

/-- Squared mode amplitude at a state. -/
def amplitude (_R : BidirectionalRowMarkovData I)
    (x y : I → ℝ) (i : I) : ℝ := x i ^ 2 + y i ^ 2

/-- The common current-weight used in `C` and `H`. -/
noncomputable def currentWeight (e : R.OrderedSupport) : ℝ :=
  R.toRowMarkovData.current e.val.1 e.val.2 ^ 2 /
    (2 * R.toRowMarkovData.traffic e.val.1 e.val.2)

/-- Ordered-support entropy production, with the factor `1/2` that removes
double counting of the two orientations. -/
noncomputable def sigma : ℝ :=
  (1 / 2 : ℝ) * ∑ e : R.OrderedSupport,
    R.toRowMarkovData.current e.val.1 e.val.2 *
      Real.log
        (R.toRowMarkovData.flow e.val.1 e.val.2 /
          R.toRowMarkovData.flow e.val.2 e.val.1)

/-- Current-over-traffic cost `C = (1/2) Σ_ordered j²/T`. -/
noncomputable def C : ℝ := ∑ e : R.OrderedSupport, R.currentWeight e

/-- Concrete Dirichlet energy, using the established full ordered-flow form. -/
def D (x y : I → ℝ) : ℝ := modeD R.toRowMarkovData.flow x y

/-- Concrete current/phase pairing, using the established full ordered form. -/
noncomputable def B (x y : I → ℝ) : ℝ := modeB R.toRowMarkovData.flow x y

/-- Phase-coupling square norm
`K = (1/8) Σ_ordered (j²/T) |v_i+v_j|²`. -/
noncomputable def K (x y : I → ℝ) : ℝ :=
  ∑ e : R.OrderedSupport,
    R.toRowMarkovData.current e.val.1 e.val.2 ^ 2 /
        (8 * R.toRowMarkovData.traffic e.val.1 e.val.2) *
      ((x e.val.1 + x e.val.2) ^ 2 + (y e.val.1 + y e.val.2) ^ 2)

/-- Local current-weighted mode energy
`H = (1/4) Σ_ordered (j²/T) (|v_i|²+|v_j|²)`. -/
noncomputable def H (x y : I → ℝ) : ℝ :=
  ∑ e : R.OrderedSupport,
    R.currentWeight e *
      ((R.amplitude x y e.val.1 + R.amplitude x y e.val.2) / 2)

/-- Stationary mode norm. -/
def N (x y : I → ℝ) : ℝ := modeNorm R.toRowMarkovData.pi x y

/-- Maximum squared mode amplitude on the finite state space. -/
noncomputable def M (x y : I → ℝ) : ℝ :=
  (insert 0 (Finset.univ.image (R.amplitude x y))).max' (by simp)

/-- Ordinary localization ratio `η = N/M`. -/
noncomputable def eta (x y : I → ℝ) : ℝ := R.N x y / R.M x y

/-- Current-weighted localization ratio `η_cur = N*C/H`. -/
noncomputable def etaCur (x y : I → ℝ) : ℝ := R.N x y * R.C / R.H x y

theorem flow_pos_on_support (e : R.OrderedSupport) :
    0 < R.toRowMarkovData.flow e.val.1 e.val.2 ∧
      0 < R.toRowMarkovData.flow e.val.2 e.val.1 :=
  R.flow_pos_of_traffic_pos e.val.1 e.val.2 e.property

theorem currentWeight_nonneg (e : R.OrderedSupport) :
    0 ≤ R.currentWeight e := by
  exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) e.property.le)

theorem currentWeight_pos_iff (e : R.OrderedSupport) :
    0 < R.currentWeight e ↔ R.toRowMarkovData.current e.val.1 e.val.2 ≠ 0 := by
  rw [currentWeight]
  constructor
  · intro h hj
    rw [hj] at h
    norm_num at h
  · intro hj
    exact div_pos (sq_pos_of_ne_zero hj) (mul_pos (by norm_num) e.property)

theorem C_nonneg : 0 ≤ R.C := by
  unfold C
  exact Finset.sum_nonneg fun e _ ↦ R.currentWeight_nonneg e

theorem C_pos_of_exists_current_ne_zero
    (hcurrent : ∃ i j, R.toRowMarkovData.current i j ≠ 0) : 0 < R.C := by
  rcases hcurrent with ⟨i, j, hij⟩
  let e : R.OrderedSupport :=
    ⟨(i, j), R.toRowMarkovData.traffic_pos_of_current_ne_zero hij⟩
  unfold C
  apply Finset.sum_pos'
  · intro q _
    exact R.currentWeight_nonneg q
  · exact ⟨e, Finset.mem_univ e, (R.currentWeight_pos_iff e).2 hij⟩

theorem C_pos_of_B_ne_zero (x y : I → ℝ) (hB : R.B x y ≠ 0) : 0 < R.C := by
  apply R.C_pos_of_exists_current_ne_zero
  exact exists_nonzero_current_of_modeB_ne_zero hB

theorem amplitude_nonneg (x y : I → ℝ) (i : I) :
    0 ≤ R.amplitude x y i := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem D_nonneg (x y : I → ℝ) : 0 ≤ R.D x y := by
  unfold D modeD pairSum
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (R.toRowMarkovData.flow_nonneg i j)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem K_nonneg (x y : I → ℝ) : 0 ≤ R.K x y := by
  unfold K
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg
    (div_nonneg (sq_nonneg _)
      (mul_nonneg (by norm_num) e.property.le))
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem H_nonneg (x y : I → ℝ) : 0 ≤ R.H x y := by
  unfold H
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg (R.currentWeight_nonneg e)
    (div_nonneg
      (add_nonneg (R.amplitude_nonneg x y e.val.1)
        (R.amplitude_nonneg x y e.val.2))
      (by norm_num))

theorem N_nonneg (x y : I → ℝ) : 0 ≤ R.N x y := by
  unfold N modeNorm
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (R.toRowMarkovData.pi_pos i).le (R.amplitude_nonneg x y i)

theorem amplitude_le_M (x y : I → ℝ) (i : I) :
    R.amplitude x y i ≤ R.M x y := by
  classical
  exact Finset.le_max' (insert 0 (Finset.univ.image (R.amplitude x y)))
    (R.amplitude x y i) (by simp) 

theorem M_nonneg (x y : I → ℝ) : 0 ≤ R.M x y := by
  classical
  exact Finset.le_max' (insert 0 (Finset.univ.image (R.amplitude x y))) 0 (by simp)

theorem M_pos_of_exists_coordinate_ne_zero
    (x y : I → ℝ) (hne : ∃ i, x i ≠ 0 ∨ y i ≠ 0) :
    0 < R.M x y := by
  rcases hne with ⟨i, hxi | hyi⟩
  · exact lt_of_lt_of_le (by
      unfold amplitude
      nlinarith [sq_pos_of_ne_zero hxi, sq_nonneg (y i)])
      (R.amplitude_le_M x y i)
  · exact lt_of_lt_of_le (by
      unfold amplitude
      nlinarith [sq_nonneg (x i), sq_pos_of_ne_zero hyi])
      (R.amplitude_le_M x y i)

end BidirectionalRowMarkovData

end OBS.CoreBranch
