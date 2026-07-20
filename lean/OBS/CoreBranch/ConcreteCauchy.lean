import OBS.CoreBranch.ConcreteEdgeData
import OBS.CoreBranch.WeightedCauchy

/-!
# Concrete ordered-support Cauchy encoding

The component type is `OrderedSupport × Fin 2`.  Its positive weight is
`traffic / 2`; the two real components are the difference coordinates paired
with the current-weighted sum coordinates.  The normalization below is the
ordered-pair normalization, so the resulting squared norms are exactly the
concrete `D` and `K` of `ConcreteEdgeData`.
-/

namespace OBS.CoreBranch

open scoped BigOperators

variable {I : Type*} [Fintype I]

namespace BidirectionalRowMarkovData

variable (R : BidirectionalRowMarkovData I)

/-- Two real Cauchy components for every ordered positive-traffic pair. -/
abbrev ConcreteComponent := R.OrderedSupport × Fin 2

/-- Positive Cauchy weight `T_ij / 2`, repeated for the two components. -/
noncomputable def cauchyWeight (q : R.ConcreteComponent) : ℝ :=
  R.toRowMarkovData.traffic q.1.val.1 q.1.val.2 / 2

/-- Difference-coordinate component. -/
def cauchyU (x y : I → ℝ) (q : R.ConcreteComponent) : ℝ :=
  if q.2 = 0 then
    x q.1.val.2 - x q.1.val.1
  else
    y q.1.val.2 - y q.1.val.1

/-- Current-weighted sum-coordinate component. -/
noncomputable def cauchyV (x y : I → ℝ) (q : R.ConcreteComponent) : ℝ :=
  if q.2 = 0 then
    -(R.toRowMarkovData.current q.1.val.1 q.1.val.2 *
      (y q.1.val.1 + y q.1.val.2)) / 4
  else
    R.toRowMarkovData.current q.1.val.1 q.1.val.2 *
      (x q.1.val.1 + x q.1.val.2) / 4

theorem cauchyWeight_pos (q : R.ConcreteComponent) :
    0 < R.cauchyWeight q := by
  exact div_pos q.1.property (by norm_num)

/-- A full ordered-pair summand which vanishes off positive traffic can be
summed on `OrderedSupport` without changing its value. -/
theorem sum_orderedSupport_eq_pairSum_of_zero
    (f : I → I → ℝ)
    (hzero : ∀ i j, ¬ 0 < R.toRowMarkovData.traffic i j → f i j = 0) :
    (∑ e : R.OrderedSupport, f e.val.1 e.val.2) = pairSum f := by
  classical
  let p : I × I → Prop := fun e ↦ 0 < R.toRowMarkovData.traffic e.1 e.2
  have hcomp :
      (∑ e : {e : I × I // ¬ p e}, f e.val.1 e.val.2) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    exact hzero e.val.1 e.val.2 e.property
  have hsplit := Fintype.sum_subtype_add_sum_subtype p
    (fun e : I × I ↦ f e.1 e.2)
  calc
    (∑ e : R.OrderedSupport, f e.val.1 e.val.2) =
        (∑ e : {e : I × I // p e}, f e.val.1 e.val.2) := by rfl
    _ = (∑ e : {e : I × I // p e}, f e.val.1 e.val.2) +
          ∑ e : {e : I × I // ¬ p e}, f e.val.1 e.val.2 := by
            rw [hcomp, add_zero]
    _ = ∑ e : I × I, f e.1 e.2 := hsplit
    _ = pairSum f := by
      simpa only [pairSum] using Fintype.sum_prod_type' f

theorem current_eq_zero_of_traffic_not_pos (i j : I)
    (h : ¬ 0 < R.toRowMarkovData.traffic i j) :
    R.toRowMarkovData.current i j = 0 := by
  have hTnonneg := R.toRowMarkovData.traffic_nonneg i j
  have hTzero : R.toRowMarkovData.traffic i j = 0 :=
    le_antisymm (le_of_not_gt h) hTnonneg
  have hf := R.toRowMarkovData.flow_nonneg i j
  have hr := R.toRowMarkovData.flow_nonneg j i
  have hsum : R.toRowMarkovData.flow i j +
      R.toRowMarkovData.flow j i = 0 := by
    simpa [RowMarkovData.traffic] using hTzero
  have hfzero : R.toRowMarkovData.flow i j = 0 := by nlinarith
  have hrzero : R.toRowMarkovData.flow j i = 0 := by nlinarith
  simp [RowMarkovData.current, hfzero, hrzero]

theorem concrete_B_support_representation (x y : I → ℝ) :
    R.B x y = ∑ e : R.OrderedSupport,
      R.toRowMarkovData.current e.val.1 e.val.2 / 2 *
        (x e.val.1 * y e.val.2 - y e.val.1 * x e.val.2) := by
  have hsupp := R.sum_orderedSupport_eq_pairSum_of_zero
    (fun i j ↦ R.toRowMarkovData.current i j / 2 *
      (x i * y j - y i * x j)) (by
        intro i j hij
        change R.toRowMarkovData.current i j / 2 *
          (x i * y j - y i * x j) = 0
        rw [R.current_eq_zero_of_traffic_not_pos i j hij]
        ring)
  rw [hsupp]
  simp only [B]
  unfold modeB
  rw [← pairSum_const_mul]
  apply pairSum_congr
  intro i j
  simp only [RowMarkovData.current]
  ring

/-- Exact concrete phase-pairing representation `B = Σ u v`. -/
theorem concrete_B_cauchy_representation (x y : I → ℝ) :
    R.B x y = ∑ q : R.ConcreteComponent,
      R.cauchyU x y q * R.cauchyV x y q := by
  rw [R.concrete_B_support_representation x y]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  have hone : (1 : Fin 2) ≠ 0 := by decide
  simp only [Fin.sum_univ_two, cauchyU, cauchyV,
    if_neg hone, ite_true]
  ring_nf

omit [Fintype I] in
private theorem symmetric_difference_sq (x y : I → ℝ) (i j : I) :
    (x j - x i) ^ 2 + (y j - y i) ^ 2 =
      (x i - x j) ^ 2 + (y i - y j) ^ 2 := by ring

private theorem pairSum_reverse_difference (x y : I → ℝ) :
    pairSum (fun i j ↦ R.toRowMarkovData.flow j i *
      ((x j - x i) ^ 2 + (y j - y i) ^ 2)) =
    pairSum (fun i j ↦ R.toRowMarkovData.flow i j *
      ((x j - x i) ^ 2 + (y j - y i) ^ 2)) := by
  calc
    pairSum (fun i j ↦ R.toRowMarkovData.flow j i *
        ((x j - x i) ^ 2 + (y j - y i) ^ 2)) =
      pairSum (fun i j ↦ R.toRowMarkovData.flow i j *
        ((x i - x j) ^ 2 + (y i - y j) ^ 2)) := by
          rw [← pairSum_swap (fun i j ↦ R.toRowMarkovData.flow j i *
            ((x j - x i) ^ 2 + (y j - y i) ^ 2))]
    _ = pairSum (fun i j ↦ R.toRowMarkovData.flow i j *
        ((x j - x i) ^ 2 + (y j - y i) ^ 2)) := by
          apply pairSum_congr
          intro i j
          rw [symmetric_difference_sq]

private theorem traffic_half_difference_pairSum (x y : I → ℝ) :
    pairSum (fun i j ↦ R.toRowMarkovData.traffic i j / 2 *
      ((x j - x i) ^ 2 + (y j - y i) ^ 2)) = R.D x y := by
  rw [show R.D x y = pairSum (fun i j ↦ R.toRowMarkovData.flow i j *
      ((x j - x i) ^ 2 + (y j - y i) ^ 2)) by rfl]
  have hrev := R.pairSum_reverse_difference x y
  rw [show pairSum (fun i j ↦ R.toRowMarkovData.traffic i j / 2 *
      ((x j - x i) ^ 2 + (y j - y i) ^ 2)) =
      (1 / 2 : ℝ) *
        (pairSum (fun i j ↦ R.toRowMarkovData.flow i j *
          ((x j - x i) ^ 2 + (y j - y i) ^ 2)) +
         pairSum (fun i j ↦ R.toRowMarkovData.flow j i *
          ((x j - x i) ^ 2 + (y j - y i) ^ 2))) by
        rw [← pairSum_add]
        rw [← pairSum_const_mul]
        apply pairSum_congr
        intro i j
        simp only [RowMarkovData.traffic]
        ring]
  rw [hrev]
  ring

/-- Exact concrete Dirichlet representation `D = Σ w u²`. -/
theorem concrete_D_cauchy_representation (x y : I → ℝ) :
    R.D x y = ∑ q : R.ConcreteComponent,
      R.cauchyWeight q * (R.cauchyU x y q) ^ 2 := by
  rw [Fintype.sum_prod_type]
  rw [show (∑ e : R.OrderedSupport, ∑ k : Fin 2,
      R.cauchyWeight (e, k) * (R.cauchyU x y (e, k)) ^ 2) =
      ∑ e : R.OrderedSupport,
        R.toRowMarkovData.traffic e.val.1 e.val.2 / 2 *
          ((x e.val.2 - x e.val.1) ^ 2 +
            (y e.val.2 - y e.val.1) ^ 2) by
        apply Finset.sum_congr rfl
        intro e _
        have hone : (1 : Fin 2) ≠ 0 := by decide
        simp only [Fin.sum_univ_two, cauchyWeight, cauchyU,
          if_neg hone, ite_true]
        ring_nf]
  symm
  calc
    (∑ e : R.OrderedSupport,
        R.toRowMarkovData.traffic e.val.1 e.val.2 / 2 *
          ((x e.val.2 - x e.val.1) ^ 2 +
            (y e.val.2 - y e.val.1) ^ 2)) =
      pairSum (fun i j ↦ R.toRowMarkovData.traffic i j / 2 *
        ((x j - x i) ^ 2 + (y j - y i) ^ 2)) := by
          exact R.sum_orderedSupport_eq_pairSum_of_zero
            (fun i j ↦ R.toRowMarkovData.traffic i j / 2 *
              ((x j - x i) ^ 2 + (y j - y i) ^ 2)) (by
                intro i j hij
                have hzero : R.toRowMarkovData.traffic i j = 0 :=
                  le_antisymm (le_of_not_gt hij)
                    (R.toRowMarkovData.traffic_nonneg i j)
                change R.toRowMarkovData.traffic i j / 2 *
                  ((x j - x i) ^ 2 + (y j - y i) ^ 2) = 0
                rw [hzero]
                ring)
    _ = R.D x y := R.traffic_half_difference_pairSum x y

/-- Exact concrete phase norm representation `K = Σ v²/w`. -/
theorem concrete_K_cauchy_representation (x y : I → ℝ) :
    R.K x y = ∑ q : R.ConcreteComponent,
      (R.cauchyV x y q) ^ 2 / R.cauchyWeight q := by
  rw [Fintype.sum_prod_type]
  rw [K]
  apply Finset.sum_congr rfl
  intro e _
  have hone : (1 : Fin 2) ≠ 0 := by decide
  simp only [Fin.sum_univ_two, cauchyV, cauchyWeight,
    if_neg hone, ite_true]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- Concrete weighted Cauchy inequality `B² ≤ D K`. -/
theorem concrete_B_sq_le_DK (x y : I → ℝ) :
    (R.B x y) ^ 2 ≤ R.D x y * R.K x y := by
  exact weighted_phaseCoupling_sq_le_DK
    (R.B x y) (R.D x y) (R.K x y)
    R.cauchyWeight (R.cauchyU x y) (R.cauchyV x y)
    R.cauchyWeight_pos
    (R.concrete_B_cauchy_representation x y)
    (R.concrete_D_cauchy_representation x y)
    (R.concrete_K_cauchy_representation x y)

theorem concrete_D_nonneg (x y : I → ℝ) : 0 ≤ R.D x y := by
  rw [R.concrete_D_cauchy_representation x y]
  exact Finset.sum_nonneg fun q _ ↦
    mul_nonneg (R.cauchyWeight_pos q).le (sq_nonneg _)

theorem concrete_K_nonneg (x y : I → ℝ) : 0 ≤ R.K x y := by
  rw [R.concrete_K_cauchy_representation x y]
  exact Finset.sum_nonneg fun q _ ↦
    div_nonneg (sq_nonneg _) (R.cauchyWeight_pos q).le

end BidirectionalRowMarkovData

end OBS.CoreBranch
