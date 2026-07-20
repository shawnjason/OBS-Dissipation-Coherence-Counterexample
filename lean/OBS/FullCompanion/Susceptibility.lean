import Mathlib

/-!
# Conditional simple-root susceptibility algebra

This module isolates the algebraic step in the simple-root calculation.  It
does **not** assert existence of a differentiable root branch.  Instead, the
public theorems take the differentiated null-vector equation as a hypothesis
and solve it, under the exact nonzero-denominator condition, for the branch
derivative.  All transposes in the manuscript calculation are algebraic
transposes; consequently the scalar pairings below have no conjugation.
-/

namespace OBS.FullCompanion

section Field

variable {K : Type*} [Field K]

/-- The matched-subdivision scalar filter, with `eps = 1 / s`. -/
def matchedFilter (eps z : K) : K := eps * z / (1 + eps * z)

/-- The numerator occurring in the `eps`-susceptibility formula. -/
def epsNumerator (eps z yTc dTx : K) : K :=
  z / (1 + eps * z) ^ 2 * yTc * dTx

/-- The rank-one contribution to the `z` derivative of the Schur matrix. -/
def zRankOneCoefficient (eps z : K) : K :=
  eps / (1 + eps * z) ^ 2

/--
Conditional susceptibility formula in scalar-pairing form.

`den` is the exact algebraic-transpose pairing
`yᵀ[S₀'(z) + eps/(1+eps*z)^2 c dᵀ]x`.  The hypothesis `hlinearized` is exactly
what results after differentiating the null-vector equation and multiplying
on the left by `yᵀ`.  Thus branch existence/differentiability is deliberately
outside this theorem; once that equation is available, the quotient is exact.
-/
theorem susceptibility_of_linearized
    (eps z yTc dTx den dz : K)
    (hden : den ≠ 0)
    (hlinearized : den * dz + epsNumerator eps z yTc dTx = 0) :
    dz = -epsNumerator eps z yTc dTx / den := by
  apply (eq_div_iff hden).2
  linear_combination hlinearized

/-- The contraction-endpoint specialization `eps = 0`. -/
theorem susceptibility_at_contraction
    (z yTc dTx den dz : K)
    (hden : den ≠ 0)
    (hlinearized : den * dz + z * yTc * dTx = 0) :
    dz = -(z * yTc * dTx) / den := by
  apply (eq_div_iff hden).2
  linear_combination hlinearized

/-- The equivalent conditional formula when the family parameter is `s`. -/
theorem susceptibility_in_escape_rate
    (s z yTc dTx den dz : K)
    (hden : den ≠ 0)
    (hlinearized : den * dz - z / (z + s) ^ 2 * yTc * dTx = 0) :
    dz = (z / (z + s) ^ 2 * yTc * dTx) / den := by
  apply (eq_div_iff hden).2
  linear_combination hlinearized

/-- Subtracting two exact branch derivatives gives the relative derivative. -/
theorem relative_susceptibility
    (zRot zRel chiRot chiRel : K)
    (hRot : zRot = chiRot) (hRel : zRel = chiRel) :
    zRot - zRel = chiRot - chiRel := by
  rw [hRot, hRel]

end Field

end OBS.FullCompanion
