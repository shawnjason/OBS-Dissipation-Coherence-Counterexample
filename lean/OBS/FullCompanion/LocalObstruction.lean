import Mathlib
import OBS.FullCompanion.Susceptibility

/-!
# Exact three-state obstruction to a local root-motion sign rule

Everything in this file is exact.  The oscillatory algebraic number is encoded
as `(-9 + i√3)/2`; no floating-point evaluation occurs.  The generator is
row-forward.  `directlyIrreducible` is stronger than graph irreducibility: it
says every off-diagonal rate is strictly positive, and hence immediately
supplies a one-step path between every two distinct states.
-/

namespace OBS.FullCompanion.LocalObstruction

structure Context where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  deriving DecidableEq

def rightContext : Context := ⟨1, 2, 2, 1⟩
def leftContext : Context := ⟨2, 3, 2, 1⟩

/-- Row-forward three-state generator from the manuscript. -/
def generator (x : Context) : Fin 3 → Fin 3 → ℚ :=
  ![![-(2 + x.a), 2, x.a],
    ![1, -(1 + x.c), x.c],
    ![x.b, x.d, -(x.b + x.d)]]

def uniform : Fin 3 → ℚ := ![1 / 3, 1 / 3, 1 / 3]

/-- Positive, normalized left invariant law for a row-forward generator. -/
def IsStationaryLaw (Q : Fin 3 → Fin 3 → ℚ) (π : Fin 3 → ℚ) : Prop :=
  (∀ i, 0 < π i) ∧ (∑ i, π i = 1) ∧
    (∀ j, ∑ i, π i * Q i j = 0)

/-- Every row sums to zero, for arbitrary context rates. -/
theorem generator_row_sum_zero (x : Context) :
    ∀ i, ∑ j, generator x i j = 0 := by
  intro i
  fin_cases i <;> simp [generator, Fin.sum_univ_succ]

/-- Uniform stationarity of the right context, in row-forward convention. -/
theorem right_uniform_stationary :
    ∀ j, ∑ i, uniform i * generator rightContext i j = 0 := by
  intro j
  fin_cases j <;> norm_num [uniform, generator, rightContext, Fin.sum_univ_succ]

/-- Uniform stationarity of the left context, in row-forward convention. -/
theorem left_uniform_stationary :
    ∀ j, ∑ i, uniform i * generator leftContext i j = 0 := by
  intro j
  fin_cases j <;> norm_num [uniform, generator, leftContext, Fin.sum_univ_succ]

theorem right_uniform_is_stationary_law :
    IsStationaryLaw (generator rightContext) uniform := by
  refine ⟨?_, ?_, right_uniform_stationary⟩
  · intro i
    fin_cases i <;> norm_num [uniform]
  · norm_num [uniform, Fin.sum_univ_succ]

theorem left_uniform_is_stationary_law :
    IsStationaryLaw (generator leftContext) uniform := by
  refine ⟨?_, ?_, left_uniform_stationary⟩
  · intro i
    fin_cases i <;> norm_num [uniform]
  · norm_num [uniform, Fin.sum_univ_succ]

/-- A direct, checkable strengthening of irreducibility for a three-state rate matrix. -/
def DirectlyIrreducible (Q : Fin 3 → Fin 3 → ℚ) : Prop :=
  ∀ i j, i ≠ j → 0 < Q i j

theorem right_generator_directly_irreducible :
    DirectlyIrreducible (generator rightContext) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [generator, rightContext]

theorem left_generator_directly_irreducible :
    DirectlyIrreducible (generator leftContext) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [generator, leftContext]

/-- Exact row-generator and one-step irreducibility certificate for `R`. -/
theorem right_is_irreducible_markov_generator :
    (∀ i, ∑ j, generator rightContext i j = 0) ∧
      DirectlyIrreducible (generator rightContext) :=
  ⟨generator_row_sum_zero rightContext, right_generator_directly_irreducible⟩

/-- Exact row-generator and one-step irreducibility certificate for `L`. -/
theorem left_is_irreducible_markov_generator :
    (∀ i, ∑ j, generator leftContext i j = 0) ∧
      DirectlyIrreducible (generator leftContext) :=
  ⟨generator_row_sum_zero leftContext, left_generator_directly_irreducible⟩

/-! ## Exact local invariant packet -/

structure LocalInvariants where
  p : ℚ
  q : ℚ
  alpha : ℚ
  piU : ℚ
  piV : ℚ
  forwardFlow : ℚ
  backwardFlow : ℚ
  current : ℚ
  traffic : ℚ
  affinityRatio : ℚ
  insertedMassNumerator : ℚ
  matchedP1 : ℚ
  matchedQ1OverS : ℚ
  matchedP2OverS : ℚ
  matchedQ2 : ℚ
  response00 : ℚ
  response01 : ℚ
  response10 : ℚ
  response11 : ℚ
  resistanceDefect : ℚ
  deriving DecidableEq

/--
The packet is computed from the actual local entries of the context generator
and the certified uniform invariant law.  `affinityRatio = 2` is the exact
argument of the real logarithm used for affinity.
-/
def localInvariants (x : Context) : LocalInvariants :=
  let p := generator x 0 1
  let q := generator x 1 0
  let alpha : ℚ := 1 / 2
  let piU := uniform 0
  let piV := uniform 1
  let f := piU * p
  let g := piV * q
  { p := p
    q := q
    alpha := alpha
    piU := piU
    piV := piV
    forwardFlow := f
    backwardFlow := g
    current := f - g
    traffic := f + g
    affinityRatio := p / q
    insertedMassNumerator := piU * p / alpha + piV * q / (1 - alpha)
    matchedP1 := p / alpha
    matchedQ1OverS := 1 - alpha
    matchedP2OverS := alpha
    matchedQ2 := q / (1 - alpha)
    response00 := p
    response01 := -p
    response10 := -q
    response11 := q
    resistanceDefect :=
      let T := f + g
      let J := f - g
      let T1 := (T + J * (1 - alpha)) / alpha
      let T2 := (T - J * alpha) / (1 - alpha)
      J ^ 2 / (T * T1 * T2) }

theorem right_local_invariants_exact :
    localInvariants rightContext =
      { p := 2, q := 1, alpha := 1 / 2, piU := 1 / 3, piV := 1 / 3
        forwardFlow := 2 / 3, backwardFlow := 1 / 3
        current := 1 / 3, traffic := 1, affinityRatio := 2
        insertedMassNumerator := 2
        matchedP1 := 4, matchedQ1OverS := 1 / 2
        matchedP2OverS := 1 / 2, matchedQ2 := 2
        response00 := 2, response01 := -2, response10 := -1, response11 := 1
        resistanceDefect := 1 / 35 } := by
  norm_num [localInvariants, generator, uniform, rightContext]

theorem left_local_invariants_exact :
    localInvariants leftContext =
      { p := 2, q := 1, alpha := 1 / 2, piU := 1 / 3, piV := 1 / 3
        forwardFlow := 2 / 3, backwardFlow := 1 / 3
        current := 1 / 3, traffic := 1, affinityRatio := 2
        insertedMassNumerator := 2
        matchedP1 := 4, matchedQ1OverS := 1 / 2
        matchedP2OverS := 1 / 2, matchedQ2 := 2
        response00 := 2, response01 := -2, response10 := -1, response11 := 1
        resistanceDefect := 1 / 35 } := by
  norm_num [localInvariants, generator, uniform, leftContext]

theorem same_local_invariants :
    localInvariants rightContext = localInvariants leftContext := by
  rw [right_local_invariants_exact, left_local_invariants_exact]

theorem same_local_affinity :
    Real.log (localInvariants rightContext).affinityRatio =
      Real.log (localInvariants leftContext).affinityRatio := by
  rw [same_local_invariants]

theorem right_local_affinity_exact :
    Real.log (localInvariants rightContext).affinityRatio = Real.log 2 := by
  rw [right_local_invariants_exact]
  norm_num

theorem left_local_affinity_exact :
    Real.log (localInvariants leftContext).affinityRatio = Real.log 2 := by
  rw [left_local_invariants_exact]
  norm_num

/-- Both contexts have the exact inserted unnormalised mass law `2 / s`. -/
theorem same_inserted_mass_law (s : ℚ) (hs : 0 < s) :
    (localInvariants rightContext).insertedMassNumerator / s = 2 / s ∧
    (localInvariants leftContext).insertedMassNumerator / s = 2 / s ∧
    0 < 2 / s := by
  refine ⟨?_, ?_, div_pos (by norm_num) hs⟩
  · norm_num [localInvariants, generator, uniform, rightContext]
  · norm_num [localInvariants, generator, uniform, leftContext]

/-! ## Exact Evans and rank-one update polynomials -/

/-- Explicit three-by-three determinant formula. -/
def det3 {R : Type*} [CommRing R] (m : Fin 3 → Fin 3 → R) : R :=
  m 0 0 * (m 1 1 * m 2 2 - m 1 2 * m 2 1)
    - m 0 1 * (m 1 0 * m 2 2 - m 1 2 * m 2 0)
    + m 0 2 * (m 1 0 * m 2 1 - m 1 1 * m 2 0)

theorem det3_eq_matrix_det {R : Type*} [CommRing R]
    (m : Matrix (Fin 3) (Fin 3) R) : det3 m = Matrix.det m := by
  rw [Matrix.det_fin_three]
  simp only [det3]
  ring

def shifted (x : Context) (z : ℂ) : Fin 3 → Fin 3 → ℂ :=
  fun i j => (if i = j then z else 0) - (generator x i j : ℚ)

def evans (x : Context) (z : ℂ) : ℂ := det3 (shifted x z)

theorem evans_eq_matrix_det (x : Context) (z : ℂ) :
    evans x z = Matrix.det (shifted x z) :=
  det3_eq_matrix_det (shifted x z)

/-- `dᵀ adj(zI-Q) c` for `c=(2,1,0)` and `d=(1,1,0)`, expanded exactly. -/
def updatePoly (x : Context) (z : ℂ) : ℂ :=
  let m := shifted x z
  2 * (m 1 1 * m 2 2 - m 1 2 * m 2 1)
    - (m 0 1 * m 2 2 - m 0 2 * m 2 1)
    - 2 * (m 1 0 * m 2 2 - m 1 2 * m 2 0)
    + (m 0 0 * m 2 2 - m 0 2 * m 2 0)

def updateC : Fin 3 → ℂ := ![2, 1, 0]
def updateD : Fin 3 → ℂ := ![1, 1, 0]

/-- The expanded update polynomial really is `dᵀ adj(zI-Q) c`. -/
theorem updatePoly_eq_adjugate_pairing (x : Context) (z : ℂ) :
    updatePoly x z =
      dotProduct updateD ((Matrix.adjugate (shifted x z)).mulVec updateC) := by
  rw [Matrix.adjugate_fin_three]
  simp [updatePoly, updateC, updateD, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem right_evans_polynomial (z : ℂ) :
    evans rightContext z = z * (z ^ 2 + 9 * z + 21) := by
  simp [evans, det3, shifted, generator, rightContext]
  ring

theorem left_evans_polynomial (z : ℂ) :
    evans leftContext z = z * (z + 5) * (z + 6) := by
  simp [evans, det3, shifted, generator, leftContext]
  ring

theorem right_update_polynomial (z : ℂ) :
    updatePoly rightContext z = 3 * z ^ 2 + 22 * z + 42 := by
  simp [updatePoly, shifted, generator, rightContext]
  ring

theorem left_update_polynomial (z : ℂ) :
    updatePoly leftContext z = 3 * z ^ 2 + 26 * z + 60 := by
  simp [updatePoly, shifted, generator, leftContext]
  ring

/-! ## Exact algebraic roots and motions -/

noncomputable def iSqrtThree : ℂ := Complex.I * (Real.sqrt 3 : ℝ)

theorem iSqrtThree_sq : iSqrtThree ^ 2 = -3 := by
  have hsR : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsC : ((Real.sqrt (3 : ℝ) : ℂ) ^ 2) = 3 := by
    exact_mod_cast hsR
  calc
    iSqrtThree ^ 2 = Complex.I ^ 2 * ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 := by
      simp only [iSqrtThree, mul_pow]
    _ = (-1) * 3 := by
      rw [show (Complex.I : ℂ) ^ 2 = -1 by simp]
      rw [hsC]
    _ = -3 := by norm_num

theorem iSqrtThree_re : iSqrtThree.re = 0 := by
  simp [iSqrtThree]

noncomputable def rightRoot : ℂ := (-9 + iSqrtThree) / 2
noncomputable def rightMotion : ℂ := (5 + iSqrtThree) / 2

def rightEvansPrime (z : ℂ) : ℂ := 3 * z ^ 2 + 18 * z + 21
def leftEvansPrime (z : ℂ) : ℂ := 3 * z ^ 2 + 22 * z + 30

theorem rightRoot_quadratic : rightRoot ^ 2 + 9 * rightRoot + 21 = 0 := by
  simp only [rightRoot]
  field_simp
  linear_combination iSqrtThree_sq

theorem right_root_exact : evans rightContext rightRoot = 0 := by
  rw [right_evans_polynomial]
  rw [rightRoot_quadratic]
  ring

theorem rightEvansPrime_at_root :
    rightEvansPrime rightRoot = (-3 - 9 * iSqrtThree) / 2 := by
  simp only [rightEvansPrime, rightRoot]
  field_simp
  ring_nf
  rw [iSqrtThree_sq]
  norm_num
  ring

theorem right_root_simple : rightEvansPrime rightRoot ≠ 0 := by
  intro h
  rw [rightEvansPrime_at_root] at h
  have hre := congrArg Complex.re h
  norm_num [iSqrtThree_re] at hre

/-- Exact differentiated Evans equation at the oscillatory root. -/
theorem right_motion_linearized :
    rightEvansPrime rightRoot * rightMotion +
      rightRoot * updatePoly rightContext rightRoot = 0 := by
  rw [right_update_polynomial]
  simp only [rightEvansPrime, rightRoot, rightMotion]
  field_simp
  have hcub : iSqrtThree ^ 3 = -3 * iSqrtThree := by
    calc
      iSqrtThree ^ 3 = iSqrtThree * iSqrtThree ^ 2 := by ring
      _ = iSqrtThree * (-3) := by rw [iSqrtThree_sq]
      _ = -3 * iSqrtThree := by ring
  ring_nf
  rw [hcub, iSqrtThree_sq]
  ring

theorem right_motion_quotient :
    rightMotion =
      -(rightRoot * updatePoly rightContext rightRoot) /
        rightEvansPrime rightRoot := by
  have h := susceptibility_at_contraction
    rightRoot (updatePoly rightContext rightRoot) 1
    (rightEvansPrime rightRoot) rightMotion right_root_simple
    (by simpa [mul_assoc] using right_motion_linearized)
  simpa using h

theorem right_motion_real : rightMotion.re = 5 / 2 := by
  norm_num [rightMotion, iSqrtThree_re]

theorem right_motion_positive : 0 < rightMotion.re := by
  rw [right_motion_real]
  norm_num

theorem left_root_five_exact : evans leftContext (-5) = 0 := by
  rw [left_evans_polynomial]
  norm_num

theorem left_root_six_exact : evans leftContext (-6) = 0 := by
  rw [left_evans_polynomial]
  norm_num

theorem left_root_five_simple : leftEvansPrime (-5) ≠ 0 := by
  norm_num [leftEvansPrime]

theorem left_root_six_simple : leftEvansPrime (-6) ≠ 0 := by
  norm_num [leftEvansPrime]

theorem left_motion_five_linearized :
    leftEvansPrime (-5) * (-5) +
      (-5) * updatePoly leftContext (-5) = 0 := by
  rw [left_update_polynomial]
  norm_num [leftEvansPrime]

theorem left_motion_five_quotient :
    (-5 : ℂ) =
      -((-5) * updatePoly leftContext (-5)) /
        leftEvansPrime (-5) := by
  have h := susceptibility_at_contraction
    (-5 : ℂ) (updatePoly leftContext (-5)) 1
    (leftEvansPrime (-5)) (-5) left_root_five_simple
    (by simpa [mul_assoc] using left_motion_five_linearized)
  simpa using h

theorem left_motion_five_negative : ((-5 : ℂ).re) < 0 := by norm_num

theorem left_motion_six_linearized :
    leftEvansPrime (-6) * 12 +
      (-6) * updatePoly leftContext (-6) = 0 := by
  rw [left_update_polynomial]
  norm_num [leftEvansPrime]

theorem left_motion_six_quotient :
    (12 : ℂ) =
      -((-6) * updatePoly leftContext (-6)) /
        leftEvansPrime (-6) := by
  have h := susceptibility_at_contraction
    (-6 : ℂ) (updatePoly leftContext (-6)) 1
    (leftEvansPrime (-6)) 12 left_root_six_simple
    (by simpa [mul_assoc] using left_motion_six_linearized)
  simpa using h

/--
Existential obstruction in its precise logical form: two exact, directly
irreducible Markov contexts share the complete listed local packet while an
exact finite-root motion is positive in one and negative in the other.
-/
theorem exists_same_local_data_opposite_motion :
    ∃ (r l : Context) (zr zl dr dl : ℂ),
      DirectlyIrreducible (generator r) ∧
      DirectlyIrreducible (generator l) ∧
      IsStationaryLaw (generator r) uniform ∧
      IsStationaryLaw (generator l) uniform ∧
      localInvariants r = localInvariants l ∧
      evans r zr = 0 ∧ evans l zl = 0 ∧
      rightEvansPrime zr ≠ 0 ∧ leftEvansPrime zl ≠ 0 ∧
      rightEvansPrime zr * dr + zr * updatePoly r zr = 0 ∧
      leftEvansPrime zl * dl + zl * updatePoly l zl = 0 ∧
      0 < dr.re ∧ dl.re < 0 := by
  refine ⟨rightContext, leftContext, rightRoot, (-5 : ℂ),
    rightMotion, (-5 : ℂ),
    right_generator_directly_irreducible,
    left_generator_directly_irreducible,
    right_uniform_is_stationary_law, left_uniform_is_stationary_law,
    same_local_invariants, right_root_exact, left_root_five_exact,
    right_root_simple, left_root_five_simple,
    right_motion_linearized, left_motion_five_linearized,
    right_motion_positive, ?_⟩
  norm_num

end OBS.FullCompanion.LocalObstruction
