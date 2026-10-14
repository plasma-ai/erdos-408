import Erdos821.Blueprint.Classical

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- The occupied cells are finite before any analytic estimate is used. -/
theorem occupied_finite (s : Finset ℕ) (b : ℕ → ℂ) (threshold Tmax : ℝ) :
    (occupied s b threshold Tmax).Finite := by
  apply (Set.finite_Icc (⌈-Tmax - 1⌉ : ℤ) ⌊Tmax⌋).subset
  intro j hj
  obtain ⟨t, hjt, htj, ht, _⟩ := hj
  have ht' := abs_le.mp ht
  constructor
  · apply Int.ceil_le.mpr
    linarith
  · apply Int.le_floor.mpr
    linarith

/-- Each occupied cell has a witness, with its closed interval and time bound. -/
theorem occupied_witnesses (s : Finset ℕ) (b : ℕ → ℂ) (threshold Tmax : ℝ) :
    ∃ t : ℤ → ℝ, ∀ j ∈ occupied s b threshold Tmax,
      (j : ℝ) ≤ t j ∧ t j ≤ (j : ℝ) + 1 ∧ |t j| ≤ Tmax ∧
      threshold < ‖primePolynomial s b (t j)‖ := by
  classical
  choose t ht using fun j : occupied s b threshold Tmax => j.property
  refine ⟨fun j => if h : j ∈ occupied s b threshold Tmax then t ⟨j, h⟩ else 0, ?_⟩
  intro j hj
  simpa only [dite_eq_left hj] using ht ⟨j, hj⟩

/-- Selecting from cells with a common residue modulo three gives separated times. -/
theorem cell_times_separated (t : ℤ → ℝ) (j k : ℤ)
    (hj : (j : ℝ) ≤ t j ∧ t j ≤ (j : ℝ) + 1)
    (hk : (k : ℝ) ≤ t k ∧ t k ≤ (k : ℝ) + 1)
    (hne : j ≠ k) (hmod : j % 3 = k % 3) :
    1 ≤ |t j - t k| := by
  have hgap : j + 3 ≤ k ∨ k + 3 ≤ j := by omega
  rcases hgap with hgap | hgap
  · have hgap' : (j : ℝ) + 3 ≤ k := by exact_mod_cast hgap
    have h : t j - t k ≤ -1 := by linarith
    exact (le_abs_self (-(t j - t k))).trans' (by linarith) |>.trans_eq (abs_neg _)
  · have hgap' : (k : ℝ) + 3 ≤ j := by exact_mod_cast hgap
    exact (le_abs_self (t j - t k)).trans' (by linarith)

end Erdos821.P5Core
