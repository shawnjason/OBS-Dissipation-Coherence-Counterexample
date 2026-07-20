import OBS.CoreBranch.ConcreteEdgeData
import OBS.CoreBranch.EntropyCurrent

/-!
# Concrete entropy-production bridge

This file specializes the scalar entropy-current inequality to the ordered
positive-traffic support of a finite row-forward Markov generator.  The
normalizations are those used by the paper: ordered pairs are counted twice,
so both the quadratic current cost and entropy production carry a factor
`1 / 2`.
-/

namespace OBS.CoreBranch

open scoped BigOperators

section Normalization

variable {E : Type*} [Fintype E]

/--
The normalized ordered-support form of the strict entropy-current inequality.
The hypotheses are deliberately stated in terms of the two directional
positive fluxes, making this lemma reusable by any concrete support model.
-/
theorem two_halfCurrentCost_lt_halfEntropy
    (forward reverse : E → ℝ)
    (hforward : ∀ e, 0 < forward e)
    (hreverse : ∀ e, 0 < reverse e)
    (hne : ∃ e, forward e ≠ reverse e) :
    2 * ((1 / 2 : ℝ) *
        ∑ e, (forward e - reverse e) ^ 2 / (forward e + reverse e)) <
      (1 / 2 : ℝ) *
        ∑ e, (forward e - reverse e) * Real.log (forward e / reverse e) := by
  have hsum := sum_entropy_current_lt_of_exists_ne
    forward reverse hforward hreverse hne
  have hquad :
      (∑ e, 2 * (forward e - reverse e) ^ 2 /
        (forward e + reverse e)) =
        2 * ∑ e, (forward e - reverse e) ^ 2 /
          (forward e + reverse e) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  calc
    2 * ((1 / 2 : ℝ) *
        ∑ e, (forward e - reverse e) ^ 2 / (forward e + reverse e)) =
        (1 / 2 : ℝ) *
          ∑ e, 2 * (forward e - reverse e) ^ 2 /
            (forward e + reverse e) := by
              rw [hquad]
              ring
    _ < (1 / 2 : ℝ) *
        ∑ e, (forward e - reverse e) *
          Real.log (forward e / reverse e) :=
      mul_lt_mul_of_pos_left hsum (by norm_num)

end Normalization

namespace BidirectionalRowMarkovData

variable {I : Type*} [Fintype I]

/-- A nonzero concrete phase/current pairing supplies an edge of the positive
traffic support with nonzero stationary current. -/
theorem exists_support_current_ne_zero
    (R : BidirectionalRowMarkovData I) (x y : I → ℝ)
    (hB : R.B x y ≠ 0) :
    ∃ e : R.OrderedSupport,
      R.toRowMarkovData.current e.val.1 e.val.2 ≠ 0 := by
  have hB' : modeB R.toRowMarkovData.flow x y ≠ 0 := by
    simpa [B] using hB
  rcases exists_nonzero_current_of_modeB_ne_zero hB' with ⟨i, j, hij⟩
  exact ⟨⟨(i, j), R.toRowMarkovData.traffic_pos_of_current_ne_zero hij⟩, hij⟩

/-- The concrete ordered-pair normalization of `C` agrees with one half of
the unnormalized quadratic current cost. -/
theorem C_eq_half_sum_current_sq_div_traffic
    (R : BidirectionalRowMarkovData I) :
    R.C = (1 / 2 : ℝ) * ∑ e : R.OrderedSupport,
      R.toRowMarkovData.current e.val.1 e.val.2 ^ 2 /
        R.toRowMarkovData.traffic e.val.1 e.val.2 := by
  classical
  rw [C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [currentWeight]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/--
Concrete strict thermodynamic factor.  Bidirectionality makes both directional
flows positive on the support, while `B ≠ 0` supplies the strict edge.
-/
theorem two_C_lt_sigma_of_B_ne_zero
    (R : BidirectionalRowMarkovData I) (x y : I → ℝ)
    (hB : R.B x y ≠ 0) :
    2 * R.C < R.sigma := by
  let forward : R.OrderedSupport → ℝ := fun e ↦
    R.toRowMarkovData.flow e.val.1 e.val.2
  let reverse : R.OrderedSupport → ℝ := fun e ↦
    R.toRowMarkovData.flow e.val.2 e.val.1
  have hforward : ∀ e, 0 < forward e := fun e ↦
    (R.flow_pos_on_support e).1
  have hreverse : ∀ e, 0 < reverse e := fun e ↦
    (R.flow_pos_on_support e).2
  have hne : ∃ e, forward e ≠ reverse e := by
    rcases R.exists_support_current_ne_zero x y hB with ⟨e, he⟩
    refine ⟨e, ?_⟩
    exact sub_ne_zero.mp he
  have hstrict := two_halfCurrentCost_lt_halfEntropy
    forward reverse hforward hreverse hne
  rw [R.C_eq_half_sum_current_sq_div_traffic] at *
  simpa only [forward, reverse, sigma, RowMarkovData.current,
    RowMarkovData.traffic] using hstrict

/--
Generator-level form of strict entropy production.  A nonzero-frequency
backward eigenmode has `B ≠ 0`, so the preceding concrete support theorem
applies without accepting a thermodynamic bridge hypothesis.
-/
theorem two_C_lt_sigma_of_backward_eigenmode
    (R : BidirectionalRowMarkovData I) (x y : I → ℝ) (a b : ℝ)
    (hreal : ∀ i, R.toRowMarkovData.backwardAction x i =
      -a * x i - b * y i)
    (himag : ∀ i, R.toRowMarkovData.backwardAction y i =
      b * x i - a * y i)
    (hcoord : ∃ i, x i ≠ 0 ∨ y i ≠ 0)
    (hb : b ≠ 0) :
    2 * R.C < R.sigma := by
  have hmode := R.toRowMarkovData.weightedRealMode_of_backward_eigen_equations
    x y a b hreal himag
  have hN : 0 < modeNorm R.toRowMarkovData.pi x y :=
    R.toRowMarkovData.modeNorm_pos_of_exists_coordinate_ne_zero x y hcoord
  have hid := weighted_eigenmode_identities
    R.toRowMarkovData.flow R.toRowMarkovData.pi x y a b
    R.toRowMarkovData.flow_stationary hmode
  have hBmode : modeB R.toRowMarkovData.flow x y ≠ 0 :=
    modeB_ne_zero_of_nonreal hN hb hid.2
  apply R.two_C_lt_sigma_of_B_ne_zero x y
  simpa [B] using hBmode

end BidirectionalRowMarkovData

end OBS.CoreBranch
