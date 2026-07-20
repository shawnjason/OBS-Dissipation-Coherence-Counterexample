import OBS.CoreBranch.ConcreteEntropy
import OBS.CoreBranch.ConcretePhase
import OBS.CoreBranch.ConcreteLocalization
import OBS.CoreBranch.ThreeFactorCore

/-!
# Closed generator-level current-weighted theorem

Every scalar in this module is defined from one bidirectional finite Markov
generator and one real-coordinate eigenmode.  The public theorem accepts no
thermodynamic, Cauchy-representation, phase-deficit, or localization bridge.
-/

namespace OBS.CoreBranch

variable {I : Type*} [Fintype I]

namespace BidirectionalRowMarkovData

variable (R : BidirectionalRowMarkovData I)

/-- Paper factor `Y = sigma*a/b^2`. -/
noncomputable def Y (a b : ℝ) : ℝ := R.sigma * a / b ^ 2

/-- Thermodynamic factor `tau = sigma/(2*C)`. -/
noncomputable def tau : ℝ := R.sigma / (2 * R.C)

/-- Phase/Cauchy factor `kappa = D*H/B^2`. -/
noncomputable def kappa (x y : I → ℝ) : ℝ :=
  R.D x y * R.H x y / (R.B x y) ^ 2

/-- All nondegeneracy and bridge facts, derived from the concrete generator
and backward eigenmode rather than accepted as theorem inputs. -/
theorem generatorCoreCertificates
    (x y : I → ℝ) (a b : ℝ)
    (hreal : ∀ i, R.toRowMarkovData.backwardAction x i =
      -a * x i - b * y i)
    (himag : ∀ i, R.toRowMarkovData.backwardAction y i =
      b * x i - a * y i)
    (hcoord : ∃ i, x i ≠ 0 ∨ y i ≠ 0)
    (hb : b ≠ 0) :
    0 < R.N x y ∧
      R.B x y ≠ 0 ∧
      0 < R.C ∧
      0 < R.H x y ∧
      0 < R.M x y ∧
      2 * R.C < R.sigma ∧
      (R.B x y) ^ 2 < R.D x y * R.H x y ∧
      R.H x y ≤ R.M x y * R.C ∧
      a * R.N x y = R.D x y / 2 ∧
      b * R.N x y = R.B x y := by
  have hmode : WeightedRealMode R.toRowMarkovData.flow
      R.toRowMarkovData.pi x y a b :=
    R.toRowMarkovData.weightedRealMode_of_backward_eigen_equations
      x y a b hreal himag
  have hN : 0 < R.N x y := by
    simpa [N] using
      R.toRowMarkovData.modeNorm_pos_of_exists_coordinate_ne_zero x y hcoord
  have hidsRaw := weighted_eigenmode_identities
    R.toRowMarkovData.flow R.toRowMarkovData.pi x y a b
    R.toRowMarkovData.flow_stationary hmode
  have hids : a * R.N x y = R.D x y / 2 ∧
      b * R.N x y = R.B x y := by
    simpa [N, D, B] using hidsRaw
  have hB : R.B x y ≠ 0 := by
    rw [← hids.2]
    exact mul_ne_zero hb hN.ne'
  have hC : 0 < R.C := R.C_pos_of_B_ne_zero x y hB
  have hKH : R.K x y < R.H x y :=
    R.concrete_K_lt_H_of_B_ne_zero x y hB
  have hH : 0 < R.H x y :=
    lt_of_le_of_lt (R.K_nonneg x y) hKH
  have hM : 0 < R.M x y :=
    R.M_pos_of_exists_coordinate_ne_zero x y hcoord
  have hthermo : 2 * R.C < R.sigma :=
    R.two_C_lt_sigma_of_B_ne_zero x y hB
  have hphase : (R.B x y) ^ 2 < R.D x y * R.H x y :=
    R.concrete_B_sq_lt_DH_of_B_ne_zero x y hB
  exact ⟨hN, hB, hC, hH, hM, hthermo, hphase,
    R.H_le_M_mul_C x y, hids.1, hids.2⟩

/--
The closed generator-level three-factor theorem.  Its only mathematical inputs
are the bidirectional row-Markov data, a backward eigenmode in real
coordinates, a nonzero mode coordinate, and `b ≠ 0`.
-/
theorem rowMarkov_currentWeighted_threeFactor_closed
    (x y : I → ℝ) (a b : ℝ)
    (hreal : ∀ i, R.toRowMarkovData.backwardAction x i =
      -a * x i - b * y i)
    (himag : ∀ i, R.toRowMarkovData.backwardAction y i =
      b * x i - a * y i)
    (hcoord : ∃ i, x i ≠ 0 ∨ y i ≠ 0)
    (hb : b ≠ 0) :
    R.sigma * a / b ^ 2 =
        (R.sigma / (2 * R.C)) *
          (R.D x y * R.H x y / (R.B x y) ^ 2) *
          (R.N x y * R.C / R.H x y) ∧
      1 < R.sigma / (2 * R.C) ∧
      1 < R.D x y * R.H x y / (R.B x y) ^ 2 ∧
      R.N x y / R.M x y ≤ R.N x y * R.C / R.H x y ∧
      R.N x y * R.C / R.H x y < R.sigma * a / b ^ 2 := by
  rcases R.generatorCoreCertificates x y a b hreal himag hcoord hb with
    ⟨hN, hB, hC, hH, hM, hthermo, hphase, hlocal, haN, hbN⟩
  exact threeFactor_core hN hC hH hM hB hb haN hbN
    hthermo hphase hlocal

/-- Paper-facing identity `Y = tau*kappa*etaCur`. -/
theorem rowMarkov_Y_eq_tau_mul_kappa_mul_etaCur
    (x y : I → ℝ) (a b : ℝ)
    (hreal : ∀ i, R.toRowMarkovData.backwardAction x i =
      -a * x i - b * y i)
    (himag : ∀ i, R.toRowMarkovData.backwardAction y i =
      b * x i - a * y i)
    (hcoord : ∃ i, x i ≠ 0 ∨ y i ≠ 0)
    (hb : b ≠ 0) :
    R.Y a b = R.tau * R.kappa x y * R.etaCur x y := by
  have h := R.rowMarkov_currentWeighted_threeFactor_closed
    x y a b hreal himag hcoord hb
  simpa [Y, tau, kappa, etaCur] using h.1

/-- Paper-facing strict/refined bound `Y > etaCur ≥ eta`. -/
theorem rowMarkov_Y_gt_etaCur_ge_eta
    (x y : I → ℝ) (a b : ℝ)
    (hreal : ∀ i, R.toRowMarkovData.backwardAction x i =
      -a * x i - b * y i)
    (himag : ∀ i, R.toRowMarkovData.backwardAction y i =
      b * x i - a * y i)
    (hcoord : ∃ i, x i ≠ 0 ∨ y i ≠ 0)
    (hb : b ≠ 0) :
    R.etaCur x y < R.Y a b ∧ R.eta x y ≤ R.etaCur x y := by
  have h := R.rowMarkov_currentWeighted_threeFactor_closed
    x y a b hreal himag hcoord hb
  constructor
  · simpa [Y, etaCur] using h.2.2.2.2
  · simpa [eta, etaCur] using h.2.2.2.1

/-- Bundled manuscript statement, including both strict factors. -/
theorem rowMarkov_paperCore
    (x y : I → ℝ) (a b : ℝ)
    (hreal : ∀ i, R.toRowMarkovData.backwardAction x i =
      -a * x i - b * y i)
    (himag : ∀ i, R.toRowMarkovData.backwardAction y i =
      b * x i - a * y i)
    (hcoord : ∃ i, x i ≠ 0 ∨ y i ≠ 0)
    (hb : b ≠ 0) :
    R.Y a b = R.tau * R.kappa x y * R.etaCur x y ∧
      1 < R.tau ∧
      1 < R.kappa x y ∧
      R.eta x y ≤ R.etaCur x y ∧
      R.etaCur x y < R.Y a b := by
  have h := R.rowMarkov_currentWeighted_threeFactor_closed
    x y a b hreal himag hcoord hb
  simpa [Y, tau, kappa, eta, etaCur] using h

/-- Generator-level exact equality characterization for the localization
refinement, stated on all nonzero-current ordered state pairs. -/
theorem rowMarkov_etaCur_eq_eta_iff
    (x y : I → ℝ) (a b : ℝ)
    (hreal : ∀ i, R.toRowMarkovData.backwardAction x i =
      -a * x i - b * y i)
    (himag : ∀ i, R.toRowMarkovData.backwardAction y i =
      b * x i - a * y i)
    (hcoord : ∃ i, x i ≠ 0 ∨ y i ≠ 0)
    (hb : b ≠ 0) :
    R.etaCur x y = R.eta x y ↔
      ∀ i j, R.toRowMarkovData.current i j ≠ 0 →
        R.amplitude x y i = R.M x y ∧
          R.amplitude x y j = R.M x y := by
  rcases R.generatorCoreCertificates x y a b hreal himag hcoord hb with
    ⟨hN, _hB, _hC, hH, hM, _hthermo, _hphase,
      _hlocal, _haN, _hbN⟩
  exact R.etaCur_eq_eta_iff_endpoint_max_all_pairs' x y hN hH hM

end BidirectionalRowMarkovData

end OBS.CoreBranch
