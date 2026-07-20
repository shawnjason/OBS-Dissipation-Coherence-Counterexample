import OBS.MatchedSubdivision.Stationary
import OBS.MatchedSubdivision.Response

noncomputable section

/-! Exact traffic and resistance defect for a finite positive matched subdivision. -/

namespace OBS.MatchedSubdivision

def traffic1 (T J α : ℝ) : ℝ := (T + J * (1 - α)) / α
def traffic2 (T J α : ℝ) : ℝ := (T - J * α) / (1 - α)

/-- The first inserted-edge traffic in endpoint flux coordinates. -/
theorem subdivision_traffic_first
    {πu πv p q α s : ℝ}
    (hs : s ≠ 0) (hα0 : α ≠ 0) (hα1 : 1 - α ≠ 0) :
    πu * (p / α) + insertedMass πu πv p q α s * ((1 - α) * s) =
      traffic1 (πu * p + πv * q) (stationaryCurrent πu πv p q) α := by
  simp [insertedMass, traffic1, stationaryCurrent]
  field_simp
  ring

/-- The second inserted-edge traffic in endpoint flux coordinates. -/
theorem subdivision_traffic_second
    {πu πv p q α s : ℝ}
    (hs : s ≠ 0) (hα0 : α ≠ 0) (hα1 : 1 - α ≠ 0) :
    insertedMass πu πv p q α s * (α * s) + πv * (q / (1 - α)) =
      traffic2 (πu * p + πv * q) (stationaryCurrent πu πv p q) α := by
  simp [insertedMass, traffic2, stationaryCurrent]
  field_simp
  ring

/-- Positivity of `T₁` derived from positive endpoint fluxes. -/
theorem traffic1_pos
    {f g α : ℝ} (hf : 0 < f) (hg : 0 < g) (hα0 : 0 < α) (hαlt : α < 1) :
    0 < traffic1 (f + g) (f - g) α := by
  rw [show traffic1 (f + g) (f - g) α = (f * (2 - α) + g * α) / α by
    simp [traffic1]; ring]
  have htwo : 0 < 2 - α := by linarith
  have hnum : 0 < f * (2 - α) + g * α :=
    add_pos (mul_pos hf htwo) (mul_pos hg hα0)
  exact div_pos hnum hα0

/-- Positivity of `T₂` derived from positive endpoint fluxes. -/
theorem traffic2_pos
    {f g α : ℝ} (hf : 0 < f) (hg : 0 < g) (hα0 : 0 < α) (hαlt : α < 1) :
    0 < traffic2 (f + g) (f - g) α := by
  rw [show traffic2 (f + g) (f - g) α =
      (f * (1 - α) + g * (1 + α)) / (1 - α) by
    simp [traffic2]; ring]
  have hleft : 0 < 1 - α := sub_pos.mpr hαlt
  have hright : 0 < 1 + α := by linarith
  have hnum : 0 < f * (1 - α) + g * (1 + α) :=
    add_pos (mul_pos hf hleft) (mul_pos hg hright)
  exact div_pos hnum hleft

/-- Exact resistance defect. -/
theorem subdivision_resistance_defect
    {T J α : ℝ}
    (hT : T ≠ 0) (hT1 : traffic1 T J α ≠ 0) (hT2 : traffic2 T J α ≠ 0) :
    1 / traffic1 T J α + 1 / traffic2 T J α - 1 / T =
      J ^ 2 / (T * traffic1 T J α * traffic2 T J α) := by
  have hparts1 : T + J * (1 - α) ≠ 0 ∧ α ≠ 0 := by
    simpa [traffic1] using hT1
  have hparts2 : T - J * α ≠ 0 ∧ 1 - α ≠ 0 := by
    simpa [traffic2] using hT2
  have hnum1 : T + J * (1 - α) ≠ 0 := hparts1.1
  have hnum2 : T - J * α ≠ 0 := hparts2.1
  have hα0 : α ≠ 0 := hparts1.2
  have hα1 : 1 - α ≠ 0 := hparts2.2
  unfold traffic1 traffic2
  field_simp [hT, hα0, hα1, hnum1, hnum2]
  ring

/-- A nonzero current strictly increases resistance for positive endpoint fluxes. -/
theorem subdivision_resistance_strict
    {f g α : ℝ}
    (hf : 0 < f) (hg : 0 < g) (hα0 : 0 < α) (hαlt : α < 1)
    (hJ : f - g ≠ 0) :
    1 / (f + g) <
      1 / traffic1 (f + g) (f - g) α + 1 / traffic2 (f + g) (f - g) α := by
  have hT : 0 < f + g := by positivity
  have hT1 := traffic1_pos hf hg hα0 hαlt
  have hT2 := traffic2_pos hf hg hα0 hαlt
  have hdef := subdivision_resistance_defect
    (J := f - g) (T := f + g) (α := α)
    (ne_of_gt hT) (ne_of_gt hT1) (ne_of_gt hT2)
  have hnum : 0 < (f - g) ^ 2 := sq_pos_of_ne_zero hJ
  have hden : 0 < (f + g) * traffic1 (f + g) (f - g) α *
      traffic2 (f + g) (f - g) α := mul_pos (mul_pos hT hT1) hT2
  have hpos : 0 < (f - g) ^ 2 /
      ((f + g) * traffic1 (f + g) (f - g) α * traffic2 (f + g) (f - g) α) := by
    exact div_pos hnum hden
  linarith

/-- Within the finite positive parameter range, equality occurs exactly at equilibrium. -/
theorem subdivision_resistance_eq_iff_current_zero
    {f g α : ℝ}
    (hf : 0 < f) (hg : 0 < g) (hα0 : 0 < α) (hαlt : α < 1) :
    1 / traffic1 (f + g) (f - g) α + 1 / traffic2 (f + g) (f - g) α =
      1 / (f + g) ↔ f - g = 0 := by
  have hT : 0 < f + g := by positivity
  have hT1 := traffic1_pos hf hg hα0 hαlt
  have hT2 := traffic2_pos hf hg hα0 hαlt
  have hdef := subdivision_resistance_defect
    (J := f - g) (T := f + g) (α := α)
    (ne_of_gt hT) (ne_of_gt hT1) (ne_of_gt hT2)
  constructor
  · intro heq
    by_contra hJ
    have hlt := subdivision_resistance_strict hf hg hα0 hαlt hJ
    linarith
  · intro hJ
    have hzero := hdef
    rw [hJ]
    rw [hJ] at hzero
    norm_num at hzero
    apply sub_eq_zero.mp
    simpa only [one_div] using hzero

end OBS.MatchedSubdivision
