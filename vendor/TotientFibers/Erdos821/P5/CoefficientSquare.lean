import Erdos821.P5.Basic

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core

/-- The dyadic harmonic coefficient-square mass is O(1/P), with an explicit constant. -/
theorem harmonic_coefficient_square (s : Finset ℕ) (b : ℕ → ℂ) (P : ℝ)
    (hP : 1 ≤ P) (hs : ∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P)
    (hb : ∀ p ∈ s, ‖b p‖ ≤ 1) :
    (∑ p ∈ s, ‖b p‖ ^ 2 / (p : ℝ) ^ 2) ≤ 3 / P := by
  have hPpos : 0 < P := by linarith
  have hcard : s.card ≤ ⌊2 * P⌋₊ + 1 := by
    calc
      s.card ≤ (Finset.range (⌊2 * P⌋₊ + 1)).card := by
        apply Finset.card_le_card
        intro p hp
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (hs p hp).2))
      _ = _ := Finset.card_range _
  have hcardreal : (s.card : ℝ) ≤ 3 * P := by
    have hfloor := Nat.floor_le (show 0 ≤ 2 * P by positivity)
    have hcard' : (s.card : ℝ) ≤ (⌊2 * P⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
    linarith
  have hlocal (p : ℕ) (hp : p ∈ s) : ‖b p‖ ^ 2 / (p : ℝ) ^ 2 ≤ 1 / P ^ 2 := by
    calc
      _ ≤ 1 / (p : ℝ) ^ 2 := div_le_div_of_nonneg_right
        (by simpa using pow_le_pow_left₀ (norm_nonneg (b p)) (hb p hp) 2) (sq_nonneg _)
      _ ≤ _ := one_div_le_one_div_of_le (sq_pos_of_pos hPpos)
        (pow_le_pow_left₀ hPpos.le (hs p hp).1 2)
  calc
    _ ≤ ∑ _p ∈ s, 1 / P ^ 2 := Finset.sum_le_sum hlocal
    _ = (s.card : ℝ) * (1 / P ^ 2) := by simp
    _ ≤ (3 * P) * (1 / P ^ 2) := mul_le_mul_of_nonneg_right hcardreal (by positivity)
    _ = _ := by field_simp

end Erdos821.P5Core
