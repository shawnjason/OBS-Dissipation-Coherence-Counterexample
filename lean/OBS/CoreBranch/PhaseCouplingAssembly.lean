import OBS.CoreBranch.WeightedCauchy
import OBS.CoreBranch.AlgebraicCore

/-!
# Phase-coupling assembly

This file assembles finite Cauchy with the exact positive phase deficit.  It
does not assume that arbitrary arrays are Markov edge data.  The concrete
generator realization is supplied by `ConcreteCauchy.lean` and
`ConcretePhase.lean`.
-/

namespace OBS.CoreBranch

open scoped BigOperators

variable {E : Type*} [Fintype E]

/-- `B ≠ 0`, finite Cauchy, and `K < H` imply the strict phase slack. -/
theorem phaseCoupling_sq_lt_DH_of_cauchy
    (B D K H : ℝ) (f g : E → ℝ)
    (hBne : B ≠ 0)
    (hB : B = ∑ e, f e * g e)
    (hD : D = ∑ e, f e ^ 2)
    (hK : K = ∑ e, g e ^ 2)
    (hKH : K < H) :
    B ^ 2 < D * H := by
  have hBK : B ^ 2 ≤ D * K := phaseCoupling_sq_le_DK B D K f g hB hD hK
  have hnorms := cauchy_norms_nonneg D K f g hD hK
  have hBsq : 0 < B ^ 2 := sq_pos_of_ne_zero hBne
  have hDpos : 0 < D := by
    by_contra hDnpos
    have hDzero : D = 0 := le_antisymm (le_of_not_gt hDnpos) hnorms.1
    rw [hDzero, zero_mul] at hBK
    linarith
  exact phaseCoupling_sq_lt_DH_of_lt hDpos hBK hKH

end OBS.CoreBranch
