import OBS.MatchedSubdivision.Basic

noncomputable section

/-! Exact finite-frequency response algebra for a matched subdivision. -/

namespace OBS.MatchedSubdivision

/-- The residue matrix in the exact dynamic defect. -/
def residue (p q α : ℝ) : Mat2 :=
  ⟨p * (1 - α) / α, p, q, q * α / (1 - α)⟩

structure Vec2 where
  x0 : ℝ
  x1 : ℝ

def outer (c d : Vec2) : Mat2 :=
  ⟨c.x0 * d.x0, c.x0 * d.x1, c.x1 * d.x0, c.x1 * d.x1⟩

def residueColumn (p q α : ℝ) : Vec2 :=
  ⟨p, q * α / (1 - α)⟩

def residueRow (α : ℝ) : Vec2 := ⟨(1 - α) / α, 1⟩

/-- A rank-one certificate that does not depend on matrix-rank automation. -/
def ConstructiveRankOne (A : Mat2) : Prop :=
  ∃ c d : Vec2, c ≠ ⟨0, 0⟩ ∧ d ≠ ⟨0, 0⟩ ∧ A = outer c d

/-- Constructive rank-one certificate: an explicit outer-product factorization. -/
theorem residue_outerProduct
    {p q α : ℝ} (hα0 : α ≠ 0) (hα1 : 1 - α ≠ 0) :
    residue p q α = outer (residueColumn p q α) (residueRow α) := by
  ext <;> simp [residue, outer, residueColumn, residueRow] <;> field_simp

/-- For positive contracted rate `p`, the displayed residue is genuinely rank one, not zero. -/
theorem residue_constructiveRankOne
    {p q α : ℝ} (hp : 0 < p) (hα0 : α ≠ 0) (hα1 : 1 - α ≠ 0) :
    ConstructiveRankOne (residue p q α) := by
  refine ⟨residueColumn p q α, residueRow α, ?_, ?_, residue_outerProduct hα0 hα1⟩
  · intro hc
    have hentry := congrArg Vec2.x0 hc
    simp [residueColumn] at hentry
    linarith
  · intro hd
    have hentry := congrArg Vec2.x1 hd
    simp [residueRow] at hentry

/-- The residue is nonzero whenever the forward contracted rate is positive. -/
theorem residue_ne_zero {p q α : ℝ} (hp : 0 < p) :
    residue p q α ≠ ⟨0, 0, 0, 0⟩ := by
  intro h
  have hentry := congrArg Mat2.a01 h
  simp [residue] at hentry
  linarith

def defectScale (z s : ℝ) : ℝ := z / (z + s)

def defectResponse (z s p q α : ℝ) : Mat2 :=
  Mat2.scale (defectScale z s) (residue p q α)

/-- Exact rank-one response identity in the `zI - Q` convention. -/
theorem subdivision_response_difference
    {z p q s α : ℝ}
    (hzs : z + s ≠ 0) (hα0 : α ≠ 0) (hα1 : 1 - α ≠ 0) :
    subdivisionResponse z (p / α) ((1 - α) * s) (α * s) (q / (1 - α)) s =
      Mat2.add (edgeResponse p q) (defectResponse z s p q α) := by
  ext <;>
    simp [subdivisionResponse, edgeResponse, defectResponse, defectScale, residue,
      Mat2.add, Mat2.scale] <;>
    field_simp <;> ring

/-- Static matching is visible directly in the exact defect formula. -/
@[simp] theorem defectResponse_zero (s p q α : ℝ) :
    defectResponse 0 s p q α = ⟨0, 0, 0, 0⟩ := by
  ext <;> simp [defectResponse, defectScale, Mat2.scale]

/-- The scalar response filter has derivative `1/s` at zero. -/
theorem defectScale_hasDerivAt_zero {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun z : ℝ => defectScale z s) (1 / s) 0 := by
  have hden : HasDerivAt (fun z : ℝ => z + s) 1 0 :=
    (hasDerivAt_id (0 : ℝ)).add_const s
  have h := (hasDerivAt_id (0 : ℝ)).div hden (by simpa using hs)
  convert h using 1
  all_goals simp
  field_simp

/-- Entrywise derivative of the exact dynamic defect. -/
theorem subdivision_firstMoment_a01 {s p q α : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun z : ℝ => (defectResponse z s p q α).a01) (p / s) 0 := by
  have h := (defectScale_hasDerivAt_zero hs).mul_const p
  convert h using 1
  all_goals simp
  ring

/-- The matrix derivative at zero is `Rα / s`, stated entrywise. -/
theorem subdivision_firstMoment {s p q α : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun z : ℝ => (defectResponse z s p q α).a00)
        ((residue p q α).a00 / s) 0 ∧
    HasDerivAt (fun z : ℝ => (defectResponse z s p q α).a01)
        ((residue p q α).a01 / s) 0 ∧
    HasDerivAt (fun z : ℝ => (defectResponse z s p q α).a10)
        ((residue p q α).a10 / s) 0 ∧
    HasDerivAt (fun z : ℝ => (defectResponse z s p q α).a11)
        ((residue p q α).a11 / s) 0 := by
  have hbase := defectScale_hasDerivAt_zero hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hbase.mul_const (residue p q α).a00
    convert h using 1
    all_goals simp
    ring
  · have h := hbase.mul_const (residue p q α).a01
    convert h using 1
    all_goals simp
    ring
  · have h := hbase.mul_const (residue p q α).a10
    convert h using 1
    all_goals simp
    ring
  · have h := hbase.mul_const (residue p q α).a11
    convert h using 1
    all_goals simp
    ring

/-- The first admittance moment cannot vanish for finite positive matched data. -/
theorem subdivision_firstMoment_ne_zero
    {s p : ℝ} (hs : 0 < s) (hp : 0 < p) : p / s ≠ 0 := by
  exact ne_of_gt (div_pos hp hs)

/-- No finite positive matched subdivision preserves the first admittance moment. -/
theorem no_finite_firstMoment_preservation
    {s p q α : ℝ} (hs : 0 < s) (hp : 0 < p) :
    ∃ d : ℝ,
      HasDerivAt (fun z : ℝ => (defectResponse z s p q α).a01) d 0 ∧ d ≠ 0 := by
  refine ⟨p / s, subdivision_firstMoment_a01 (ne_of_gt hs), ?_⟩
  exact subdivision_firstMoment_ne_zero hs hp

/-- The unique singular point of the displayed scalar formula is `z = -s`. -/
theorem defectScale_denominator_ne_zero_iff {z s : ℝ} :
    z + s ≠ 0 ↔ z ≠ -s := by
  constructor
  · intro hsum heq
    apply hsum
    linarith
  · intro hneq hsum
    apply hneq
    linarith

end OBS.MatchedSubdivision
