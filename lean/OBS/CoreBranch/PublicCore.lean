import OBS.CoreBranch.EigenmodeIdentities
import OBS.CoreBranch.EntropyCurrent
import OBS.CoreBranch.MarkovData
import OBS.CoreBranch.PhaseDeficit
import OBS.CoreBranch.PhaseCouplingAssembly
import OBS.CoreBranch.ThreeFactorCore
import OBS.CoreBranch.GeneratorThreeFactor

/-!
# Public current-weighted core assembly

This module retains the conditional assembly API for compatibility and reuse.
The primary closed generator-level theorem is
`BidirectionalRowMarkovData.rowMarkov_paperCore` in
`GeneratorThreeFactor.lean`; it derives the thermodynamic, Cauchy, strict
phase, and localization bridges internally.
-/

namespace OBS.CoreBranch

open scoped BigOperators

variable {I E : Type*} [Fintype I] [Fintype E]

/--
Assemble the exact eigenmode identities, explicit finite Cauchy certificate,
strict phase deficit, thermodynamic strictness, and localization comparison.
-/
theorem currentWeighted_threeFactor
    (flow : I → I → ℝ) (pi x y : I → ℝ) (a b : ℝ)
    (sigma C H M K : ℝ) (f g : E → ℝ)
    (hstat : ∀ i, ∑ j, flow i j = ∑ j, flow j i)
    (hmode : WeightedRealMode flow pi x y a b)
    (hN : 0 < modeNorm pi x y)
    (hC : 0 < C) (hH : 0 < H) (hM : 0 < M) (hb : b ≠ 0)
    (hthermo : 2 * C < sigma)
    (hBrep : modeB flow x y = ∑ e, f e * g e)
    (hDrep : modeD flow x y = ∑ e, f e ^ 2)
    (hKrep : K = ∑ e, g e ^ 2)
    (hKH : K < H)
    (hlocal : H ≤ M * C) :
    sigma * a / b ^ 2 =
        (sigma / (2 * C)) *
          (modeD flow x y * H / modeB flow x y ^ 2) *
          (modeNorm pi x y * C / H) ∧
      1 < sigma / (2 * C) ∧
      1 < modeD flow x y * H / modeB flow x y ^ 2 ∧
      modeNorm pi x y / M ≤ modeNorm pi x y * C / H ∧
      modeNorm pi x y * C / H < sigma * a / b ^ 2 := by
  have hids := weighted_eigenmode_identities flow pi x y a b hstat hmode
  have hBne : modeB flow x y ≠ 0 :=
    modeB_ne_zero_of_nonreal hN hb hids.2
  have hphase : modeB flow x y ^ 2 < modeD flow x y * H :=
    phaseCoupling_sq_lt_DH_of_cauchy
      (modeB flow x y) (modeD flow x y) K H f g
      hBne hBrep hDrep hKrep hKH
  exact threeFactor_core hN hC hH hM hBne hb hids.1 hids.2
    hthermo hphase hlocal

/--
Version where `K < H` is itself obtained from explicit finite
parallelogram/deficit data.
-/
theorem currentWeighted_threeFactor_of_phaseData
    (flow : I → I → ℝ) (pi x y : I → ℝ) (a b : ℝ)
    (sigma C H M K : ℝ) (f g : E → ℝ)
    (coeff leftSq rightSq sumSq diffSq : E → ℝ)
    (hstat : ∀ i, ∑ j, flow i j = ∑ j, flow j i)
    (hmode : WeightedRealMode flow pi x y a b)
    (hN : 0 < modeNorm pi x y)
    (hC : 0 < C) (hH : 0 < H) (hM : 0 < M) (hb : b ≠ 0)
    (hthermo : 2 * C < sigma)
    (hBrep : modeB flow x y = ∑ e, f e * g e)
    (hDrep : modeD flow x y = ∑ e, f e ^ 2)
    (hKrep : K = ∑ e, g e ^ 2)
    (hcoeff : ∀ e, 0 ≤ coeff e) (hdiff : ∀ e, 0 ≤ diffSq e)
    (hpar : ∀ e, sumSq e + diffSq e = 2 * (leftSq e + rightSq e))
    (hex : ∃ e, 0 < coeff e ∧ 0 < diffSq e)
    (hKphase : K = ∑ e, coeff e / 4 * sumSq e)
    (hHphase : H = ∑ e, coeff e / 2 * (leftSq e + rightSq e))
    (hlocal : H ≤ M * C) :
    sigma * a / b ^ 2 =
        (sigma / (2 * C)) *
          (modeD flow x y * H / modeB flow x y ^ 2) *
          (modeNorm pi x y * C / H) ∧
      1 < sigma / (2 * C) ∧
      1 < modeD flow x y * H / modeB flow x y ^ 2 ∧
      modeNorm pi x y / M ≤ modeNorm pi x y * C / H ∧
      modeNorm pi x y * C / H < sigma * a / b ^ 2 := by
  have hKHraw := K_lt_H_of_exists_positive_deficit
    coeff leftSq rightSq sumSq diffSq hcoeff hdiff hpar hex
  have hKH : K < H := by
    rw [hKphase, hHphase]
    exact hKHraw
  exact currentWeighted_threeFactor flow pi x y a b sigma C H M K f g
    hstat hmode hN hC hH hM hb hthermo hBrep hDrep hKrep hKH hlocal

/--
Row-Markov entry point.  This discharges stationary-flow balance, weighted
mode equations, and norm positivity from `RowMarkovData` and real/imaginary
backward eigen-equations.
-/
theorem rowMarkov_currentWeighted_threeFactor
    (R : RowMarkovData I) (x y : I → ℝ) (a b : ℝ)
    (sigma C H M K : ℝ) (f g : E → ℝ)
    (hreal : ∀ i, R.backwardAction x i = -a * x i - b * y i)
    (himag : ∀ i, R.backwardAction y i = b * x i - a * y i)
    (hcoord : ∃ i, x i ≠ 0 ∨ y i ≠ 0)
    (hC : 0 < C) (hH : 0 < H) (hM : 0 < M) (hb : b ≠ 0)
    (hthermo : 2 * C < sigma)
    (hBrep : modeB R.flow x y = ∑ e, f e * g e)
    (hDrep : modeD R.flow x y = ∑ e, f e ^ 2)
    (hKrep : K = ∑ e, g e ^ 2)
    (hKH : K < H)
    (hlocal : H ≤ M * C) :
    sigma * a / b ^ 2 =
        (sigma / (2 * C)) *
          (modeD R.flow x y * H / modeB R.flow x y ^ 2) *
          (modeNorm R.pi x y * C / H) ∧
      1 < sigma / (2 * C) ∧
      1 < modeD R.flow x y * H / modeB R.flow x y ^ 2 ∧
      modeNorm R.pi x y / M ≤ modeNorm R.pi x y * C / H ∧
      modeNorm R.pi x y * C / H < sigma * a / b ^ 2 := by
  have hmode : WeightedRealMode R.flow R.pi x y a b :=
    R.weightedRealMode_of_backward_eigen_equations x y a b hreal himag
  have hN : 0 < modeNorm R.pi x y :=
    R.modeNorm_pos_of_exists_coordinate_ne_zero x y hcoord
  exact currentWeighted_threeFactor R.flow R.pi x y a b sigma C H M K f g
    R.flow_stationary hmode hN hC hH hM hb hthermo hBrep hDrep hKrep hKH hlocal

end OBS.CoreBranch
