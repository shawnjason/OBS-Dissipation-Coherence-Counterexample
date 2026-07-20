import OBS.MatchedSubdivision.Basic

noncomputable section

/-! Stationary current, affinity, entropy, mass, and normalization identities. -/

namespace OBS.MatchedSubdivision

def insertedMass (πu πv p q α s : ℝ) : ℝ :=
  (πu * p / α + πv * q / (1 - α)) / s

def stationaryCurrent (πu πv p q : ℝ) : ℝ := πu * p - πv * q

/-- The current on the first inserted edge equals the old edge current. -/
theorem subdivision_current_first
    { πu πv p q α s : ℝ}
    (hs : s ≠ 0) (hα0 : α ≠ 0) (hα1 : 1 - α ≠ 0) :
    πu * (p / α) - insertedMass πu πv p q α s * ((1 - α) * s) =
      stationaryCurrent πu πv p q := by
  simp [insertedMass, stationaryCurrent]
  field_simp
  ring

/-- The current on the second inserted edge equals the old edge current. -/
theorem subdivision_current_second
    {πu πv p q α s : ℝ}
    (hs : s ≠ 0) (hα0 : α ≠ 0) (hα1 : 1 - α ≠ 0) :
    insertedMass πu πv p q α s * (α * s) - πv * (q / (1 - α)) =
      stationaryCurrent πu πv p q := by
  simp [insertedMass, stationaryCurrent]
  field_simp
  ring

/-- The inserted-state stationarity balance. -/
theorem insertedMass_balance
    {πu πv p q α s : ℝ}
    (hs : s ≠ 0) (hα0 : α ≠ 0) (hα1 : 1 - α ≠ 0) :
    insertedMass πu πv p q α s * s =
      πu * (p / α) + πv * (q / (1 - α)) := by
  simp [insertedMass]
  field_simp

/-- The product of forward/backward path rates has the old edge ratio. -/
theorem matched_path_rate_ratio
    {p q α s : ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hs : s ≠ 0)
    (hα0 : α ≠ 0) (hα1 : 1 - α ≠ 0) :
    ((p / α) * (α * s)) / (((1 - α) * s) * (q / (1 - α))) = p / q := by
  field_simp

/-- Total logarithmic path affinity is exactly preserved. -/
theorem subdivision_affinity_preserved
    {p q α s : ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hs : s ≠ 0)
    (hα0 : α ≠ 0) (hα1 : 1 - α ≠ 0) :
    Real.log (((p / α) * (α * s)) / (((1 - α) * s) * (q / (1 - α)))) =
      Real.log (p / q) := by
  rw [matched_path_rate_ratio hp hq hs hα0 hα1]

/-- Unnormalized segment entropy `J · affinity` is preserved. -/
theorem subdivision_entropy_preserved
    {J p q α s : ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hs : s ≠ 0)
    (hα0 : α ≠ 0) (hα1 : 1 - α ≠ 0) :
    J * Real.log (((p / α) * (α * s)) /
      (((1 - α) * s) * (q / (1 - α)))) = J * Real.log (p / q) := by
  rw [subdivision_affinity_preserved hp hq hs hα0 hα1]

/-- Current, total affinity, and unnormalized segment entropy, bundled together. -/
theorem subdivision_stationary_preservation
    {πu πv p q α s : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 < s) (hα0 : 0 < α) (hαlt : α < 1) :
    πu * (p / α) - insertedMass πu πv p q α s * ((1 - α) * s) =
        stationaryCurrent πu πv p q ∧
    insertedMass πu πv p q α s * (α * s) - πv * (q / (1 - α)) =
        stationaryCurrent πu πv p q ∧
    Real.log (((p / α) * (α * s)) / (((1 - α) * s) * (q / (1 - α)))) =
        Real.log (p / q) ∧
    stationaryCurrent πu πv p q *
        Real.log (((p / α) * (α * s)) / (((1 - α) * s) * (q / (1 - α)))) =
      stationaryCurrent πu πv p q * Real.log (p / q) := by
  have hs0 := ne_of_gt hs
  have hα0' := ne_of_gt hα0
  have hα1' : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hαlt)
  exact ⟨subdivision_current_first hs0 hα0' hα1',
    subdivision_current_second hs0 hα0' hα1',
    subdivision_affinity_preserved (ne_of_gt hp) (ne_of_gt hq) hs0 hα0' hα1',
    subdivision_entropy_preserved (J := stationaryCurrent πu πv p q)
      (ne_of_gt hp) (ne_of_gt hq) hs0 hα0' hα1'⟩

/-- The numerator controlling inserted mass is positive for positive data. -/
theorem insertedMass_numerator_pos
    {πu πv p q α : ℝ}
    (hπu : 0 < πu) (hπv : 0 < πv) (hp : 0 < p) (hq : 0 < q)
    (hα0 : 0 < α) (hαlt : α < 1) :
    0 < πu * p / α + πv * q / (1 - α) := by
  have hα1 : 0 < 1 - α := sub_pos.mpr hαlt
  have hu : 0 < πu * p / α := div_pos (mul_pos hπu hp) hα0
  have hv : 0 < πv * q / (1 - α) := div_pos (mul_pos hπv hq) hα1
  exact add_pos hu hv

/-- Every desired positive unnormalized inserted mass has a unique positive `s`. -/
theorem arbitrary_positive_insertedMass
    {πu πv p q α m : ℝ}
    (hπu : 0 < πu) (hπv : 0 < πv) (hp : 0 < p) (hq : 0 < q)
    (hα0 : 0 < α) (hαlt : α < 1) (hm : 0 < m) :
    ∃! s : ℝ, 0 < s ∧ insertedMass πu πv p q α s = m := by
  let A := πu * p / α + πv * q / (1 - α)
  have hA : 0 < A := insertedMass_numerator_pos hπu hπv hp hq hα0 hαlt
  refine ⟨A / m, ?_, ?_⟩
  · constructor
    · exact div_pos hA hm
    · change A / (A / m) = m
      field_simp [ne_of_gt hA, ne_of_gt hm]
  · intro s hsMass
    rcases hsMass with ⟨hs, heq⟩
    dsimp [insertedMass] at heq
    change A / s = m at heq
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hm0 : m ≠ 0 := ne_of_gt hm
    apply (eq_div_iff hm0).2
    have hAm : A = m * s := (div_eq_iff hs0).mp heq
    simpa [mul_comm] using hAm.symm

/-- If old mass is one, old plus inserted normalized mass is again one. -/
theorem subdivision_normalized_total_mass {m : ℝ} (hm : 0 < m) :
    1 / (1 + m) + m / (1 + m) = 1 := by
  have hden : 1 + m ≠ 0 := by positivity
  field_simp [hden]

/-- Every old stationary flux is scaled by exactly `(1+m)⁻¹`. -/
theorem subdivision_normalized_flux_scaling
    {π k m : ℝ} :
    (π / (1 + m)) * k = (π * k) / (1 + m) := by
  ring

end OBS.MatchedSubdivision
