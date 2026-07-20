import Mathlib

noncomputable section

/-!
# Positive matched two-edge subdivisions

This file uses the row-forward `zI - Q` convention.  The scalar predicate
`ZeroFrequencyMatch` records the four entries of the zero-frequency Schur
response, after using the internal escape identity `s = q₁ + p₂`.
-/

namespace OBS.MatchedSubdivision

/-- A deliberately small concrete type for a real `2 × 2` boundary response. -/
@[ext]
structure Mat2 where
  a00 : ℝ
  a01 : ℝ
  a10 : ℝ
  a11 : ℝ

namespace Mat2

def add (A B : Mat2) : Mat2 :=
  ⟨A.a00 + B.a00, A.a01 + B.a01, A.a10 + B.a10, A.a11 + B.a11⟩

def sub (A B : Mat2) : Mat2 :=
  ⟨A.a00 - B.a00, A.a01 - B.a01, A.a10 - B.a10, A.a11 - B.a11⟩

def scale (c : ℝ) (A : Mat2) : Mat2 :=
  ⟨c * A.a00, c * A.a01, c * A.a10, c * A.a11⟩

@[simp] theorem add_a00 (A B : Mat2) : (add A B).a00 = A.a00 + B.a00 := rfl
@[simp] theorem add_a01 (A B : Mat2) : (add A B).a01 = A.a01 + B.a01 := rfl
@[simp] theorem add_a10 (A B : Mat2) : (add A B).a10 = A.a10 + B.a10 := rfl
@[simp] theorem add_a11 (A B : Mat2) : (add A B).a11 = A.a11 + B.a11 := rfl

@[simp] theorem sub_a00 (A B : Mat2) : (sub A B).a00 = A.a00 - B.a00 := rfl
@[simp] theorem sub_a01 (A B : Mat2) : (sub A B).a01 = A.a01 - B.a01 := rfl
@[simp] theorem sub_a10 (A B : Mat2) : (sub A B).a10 = A.a10 - B.a10 := rfl
@[simp] theorem sub_a11 (A B : Mat2) : (sub A B).a11 = A.a11 - B.a11 := rfl

@[simp] theorem scale_a00 (c : ℝ) (A : Mat2) : (scale c A).a00 = c * A.a00 := rfl
@[simp] theorem scale_a01 (c : ℝ) (A : Mat2) : (scale c A).a01 = c * A.a01 := rfl
@[simp] theorem scale_a10 (c : ℝ) (A : Mat2) : (scale c A).a10 = c * A.a10 := rfl
@[simp] theorem scale_a11 (c : ℝ) (A : Mat2) : (scale c A).a11 = c * A.a11 := rfl

end Mat2

/-- The contracted bidirectional edge contribution in the `zI - Q` convention. -/
def edgeResponse (p q : ℝ) : Mat2 := ⟨p, -p, -q, q⟩

/-- Schur response obtained after eliminating the inserted degree-two state. -/
def subdivisionResponse
    (z p₁ q₁ p₂ q₂ s : ℝ) : Mat2 :=
  ⟨p₁ * (z + p₂) / (z + s),
   -(p₁ * p₂) / (z + s),
   -(q₁ * q₂) / (z + s),
   q₂ * (z + q₁) / (z + s)⟩

/-- The scalar equations equivalent to equality of the zero-frequency responses. -/
def ZeroFrequencyMatch
    (p q p₁ q₁ p₂ q₂ s : ℝ) : Prop :=
  q₁ + p₂ = s ∧ p₁ * p₂ / s = p ∧ q₁ * q₂ / s = q

/-- With `s = q₁ + p₂`, the scalar matching equations are exactly matrix DC equality. -/
theorem zeroFrequencyMatch_iff_response_eq
    {p q p₁ q₁ p₂ q₂ s : ℝ} (hsum : q₁ + p₂ = s) :
    ZeroFrequencyMatch p q p₁ q₁ p₂ q₂ s ↔
      subdivisionResponse 0 p₁ q₁ p₂ q₂ s = edgeResponse p q := by
  constructor
  · rintro ⟨_, hforward, hbackward⟩
    ext
    · simpa [subdivisionResponse, edgeResponse] using hforward
    · simp only [subdivisionResponse, edgeResponse, zero_add]
      rw [neg_div]
      exact congrArg (fun x : ℝ => -x) hforward
    · simp only [subdivisionResponse, edgeResponse, zero_add]
      rw [neg_div]
      exact congrArg (fun x : ℝ => -x) hbackward
    · simpa [subdivisionResponse, edgeResponse, mul_comm] using hbackward
  · intro hmatrix
    have h01 := congrArg Mat2.a01 hmatrix
    have h10 := congrArg Mat2.a10 hmatrix
    refine ⟨hsum, ?_, ?_⟩
    · simp only [subdivisionResponse, edgeResponse, zero_add] at h01
      rw [neg_div] at h01
      exact neg_injective h01
    · simp only [subdivisionResponse, edgeResponse, zero_add] at h10
      rw [neg_div] at h10
      exact neg_injective h10

/-- The displayed matched parameterization always has the prescribed DC response. -/
theorem parametrized_zeroFrequencyMatch
    {p q s α : ℝ} (hs : s ≠ 0) (hα0 : α ≠ 0) (hα1 : 1 - α ≠ 0) :
    ZeroFrequencyMatch p q (p / α) ((1 - α) * s) (α * s) (q / (1 - α)) s := by
  constructor
  · ring
  constructor
  · field_simp
  · field_simp

/--
Complete positive classification of zero-frequency matched subdivisions.

The unique parameter is `α = p₂ / s`.  Positivity of `q₁,p₂` and
`q₁ + p₂ = s` forces `0 < α < 1`.
-/
theorem zeroMatch_iff_parametrized
    {p q p₁ q₁ p₂ q₂ s : ℝ}
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hp₂ : 0 < p₂) (hq₂ : 0 < q₂) (hs : 0 < s) :
    ZeroFrequencyMatch p q p₁ q₁ p₂ q₂ s ↔
      ∃! α : ℝ,
        0 < α ∧ α < 1 ∧
        p₁ = p / α ∧ q₁ = (1 - α) * s ∧
        p₂ = α * s ∧ q₂ = q / (1 - α) := by
  constructor
  · rintro ⟨hsum, hforward, hbackward⟩
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hp₂0 : p₂ ≠ 0 := ne_of_gt hp₂
    have hq₁0 : q₁ ≠ 0 := ne_of_gt hq₁
    have hp₂lt : p₂ < s := by linarith
    refine ⟨p₂ / s, ?_, ?_⟩
    · refine ⟨div_pos hp₂ hs, (div_lt_one hs).2 hp₂lt, ?_⟩
      constructor
      · calc
          p₁ = (p₁ * p₂ / s) / (p₂ / s) := by field_simp
          _ = p / (p₂ / s) := by rw [hforward]
      constructor
      · field_simp
        linarith
      constructor
      · field_simp
      · calc
          q₂ = (q₁ * q₂ / s) / (q₁ / s) := by field_simp
          _ = q / (q₁ / s) := by rw [hbackward]
          _ = q / (1 - p₂ / s) := by
            congr 1
            field_simp
            linarith
    · intro β hβ
      rcases hβ with ⟨_, _, _, _, hp₂β, _⟩
      calc
        β = p₂ / s := by rw [hp₂β]; field_simp
        _ = p₂ / s := rfl
  · rintro ⟨α, ⟨hα0, hαlt, hp₁, hq₁', hp₂', hq₂⟩, _⟩
    rw [hp₁, hq₁', hp₂', hq₂]
    exact parametrized_zeroFrequencyMatch (ne_of_gt hs) (ne_of_gt hα0) (by linarith)

/-- In a positive match, the matching parameter can be recovered from `q₁` too. -/
theorem zeroMatch_alpha_complement
    {q₁ p₂ s : ℝ} (hs : s ≠ 0) (h : q₁ + p₂ = s) :
    1 - p₂ / s = q₁ / s := by
  field_simp
  linarith

end OBS.MatchedSubdivision
