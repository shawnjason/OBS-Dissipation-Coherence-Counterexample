import Mathlib

/-!
# OBS current-weighted algebraic core

This file isolates the scalar algebra used after the analytic and finite-sum
estimates have been established.  It deliberately has no Markov-generator or
eigenvector interface: those hypotheses are supplied as exact identities.
-/

namespace OBS.CoreBranch

/-- The exact nonnegative phase deficit upgrades `B^2 <= D*K` to `B^2 <= D*H`. -/
theorem phaseCoupling_sq_le_DH
    {B D K H : ℝ}
    (hD : 0 ≤ D) (hBK : B ^ 2 ≤ D * K) (hKH : K ≤ H) :
    B ^ 2 ≤ D * H := by
  exact hBK.trans (mul_le_mul_of_nonneg_left hKH hD)

/-- A positive phase deficit makes the phase-coupling bound strict. -/
theorem phaseCoupling_sq_lt_DH_of_lt
    {B D K H : ℝ}
    (hD : 0 < D) (hBK : B ^ 2 ≤ D * K) (hKH : K < H) :
    B ^ 2 < D * H := by
  exact hBK.trans_lt (mul_lt_mul_of_pos_left hKH hD)

/--
The three-factor identity in a denominator-explicit form.

`a*N = D/2` and `b*N = B` are precisely the two eigenmode identities.
-/
theorem threeFactor_identity
    {sigma a b N D B C H : ℝ}
    (hC : C ≠ 0) (hH : H ≠ 0) (hB : B ≠ 0) (hb : b ≠ 0)
    (haN : a * N = D / 2) (hbN : b * N = B) :
    sigma * a / b ^ 2 =
      (sigma / (2 * C)) * (D * H / B ^ 2) * (N * C / H) := by
  have hBsq : B ^ 2 = b ^ 2 * N ^ 2 := by
    rw [← hbN]
    ring
  have hD : D = 2 * (a * N) := by
    linarith [haN]
  field_simp
  rw [hBsq, hD]
  ring

/-- The product form of the OBS violation criterion. -/
theorem product_lt_one_iff_last_lt_inv
    {tau kappa etaCur : ℝ}
    (htau : 0 < tau) (hkappa : 0 < kappa) :
    tau * kappa * etaCur < 1 ↔ etaCur < 1 / (tau * kappa) := by
  rw [lt_div_iff₀ (mul_pos htau hkappa)]
  ring_nf

/-- The sharp criterion after rewriting `Y` by the exact three-factor identity. -/
theorem obsViolation_iff_etaCur_lt
    {Y tau kappa etaCur : ℝ}
    (hY : Y = tau * kappa * etaCur)
    (htau : 0 < tau) (hkappa : 0 < kappa) :
    Y < 1 ↔ etaCur < 1 / (tau * kappa) := by
  rw [hY]
  exact product_lt_one_iff_last_lt_inv htau hkappa

/-- Strict factor slacks imply the corrected strict lower bound. -/
theorem threeFactor_strict_bound
    {Y tau kappa etaCur eta : ℝ}
    (hY : Y = tau * kappa * etaCur)
    (htau : 1 < tau) (hkappa : 1 < kappa)
    (hetaCur : 0 < etaCur) (hlocal : eta ≤ etaCur) :
    etaCur < Y ∧ eta ≤ etaCur := by
  constructor
  · rw [hY]
    have hprod_pos : 0 < (tau - 1) * (kappa - 1) :=
      mul_pos (sub_pos.mpr htau) (sub_pos.mpr hkappa)
    have hprod : 1 < tau * kappa := by
      nlinarith
    nlinarith [mul_lt_mul_of_pos_right hprod hetaCur]
  · exact hlocal

/-- Gu's two adjacent slacks equal the project's regrouped two slacks. -/
theorem guSlack_regrouping
    {C G B M D H : ℝ}
    (hB : B ≠ 0) (hG : G ≠ 0) (hH : H ≠ 0) :
    (C * G / B ^ 2) * (M * D / G) =
      (D * H / B ^ 2) * (M * C / H) := by
  field_simp

end OBS.CoreBranch
