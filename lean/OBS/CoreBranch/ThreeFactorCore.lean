import OBS.CoreBranch.AlgebraicCore
import OBS.CoreBranch.FiniteWeighted

/-!
# Assembled algebraic three-factor theorem

The public theorem here starts from the exact eigenmode identities and the
three independently proved scalar/finite-sum estimates.  A generator-level
module should discharge those hypotheses.
-/

namespace OBS.CoreBranch

/-- The complete current-weighted factor conclusion from its exact core inputs. -/
theorem threeFactor_core
    {sigma a b N D B C H M : ℝ}
    (hN : 0 < N) (hC : 0 < C) (hH : 0 < H) (hM : 0 < M)
    (hB : B ≠ 0) (hb : b ≠ 0)
    (haN : a * N = D / 2) (hbN : b * N = B)
    (hthermo : 2 * C < sigma)
    (hphase : B ^ 2 < D * H)
    (hlocal : H ≤ M * C) :
    sigma * a / b ^ 2 =
        (sigma / (2 * C)) * (D * H / B ^ 2) * (N * C / H) ∧
      1 < sigma / (2 * C) ∧
      1 < D * H / B ^ 2 ∧
      N / M ≤ N * C / H ∧
      N * C / H < sigma * a / b ^ 2 := by
  have hid := threeFactor_identity (sigma := sigma) hC.ne' hH.ne' hB hb haN hbN
  have htau : 1 < sigma / (2 * C) := by
    rw [lt_div_iff₀ (mul_pos (by norm_num) hC)]
    simpa [mul_comm] using hthermo
  have hBsq : 0 < B ^ 2 := sq_pos_of_ne_zero hB
  have hkappa : 1 < D * H / B ^ 2 := by
    rw [lt_div_iff₀ hBsq]
    simpa using hphase
  have heta : N / M ≤ N * C / H :=
    etaCur_ge_eta hN.le hH hM hlocal
  have hetaPos : 0 < N * C / H := div_pos (mul_pos hN hC) hH
  have hstrict := threeFactor_strict_bound hid htau hkappa hetaPos heta
  exact ⟨hid, htau, hkappa, heta, hstrict.1⟩

end OBS.CoreBranch
