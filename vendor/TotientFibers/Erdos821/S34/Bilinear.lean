import OAI.NumberTheory.PrimeGaps.AdditiveSieve
import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace Erdos821.S34.Proofs

/-- Rational approximation gives circular separation on every integer block
of diameter at most r/2. This is the spacing input to the additive large sieve. -/
theorem rational_frequency_separation (α β : ℝ) (u d q : ℤ) (r : ℕ)
    (hr : 1 ≤ r) (hu : Nat.Coprime u.natAbs r)
    (hα : α = (u : ℝ) / r + β) (hβ : |β| ≤ 1 / (r : ℝ) ^ 2)
    (hd : d ≠ 0) (hspan : |(d : ℝ)| ≤ (r : ℝ) / 2) :
    1 / (2 * (r : ℝ)) ≤ |α * d - q| := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  have hdabs : d.natAbs < r := by
    have h : |(d : ℝ)| < (r : ℝ) := by linarith
    have hi : |d| < (r : ℤ) := by exact_mod_cast h
    have hi' : (d.natAbs : ℤ) < r := by simpa only [Int.natCast_natAbs] using hi
    exact_mod_cast hi'
  have hnum : u * d - q * (r : ℤ) ≠ 0 := by
    intro hz
    have hdiv : (r : ℤ) ∣ u * d := ⟨q, by nlinarith [hz]⟩
    have hdiv' : r ∣ u.natAbs * d.natAbs := by
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdiv
    have hrd := hu.symm.dvd_of_dvd_mul_left hdiv'
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hd) hrd
    omega
  have hnumabs : (1 : ℝ) ≤ |((u * d - q * (r : ℤ) : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hnum
  have hbase : 1 / (r : ℝ) ≤ |(u : ℝ) / r * d - q| := by
    have heq : (u : ℝ) / r * d - q = ((u * d - q * (r : ℤ) : ℤ) : ℝ) / r := by
      push_cast
      field_simp
    rw [heq, abs_div, abs_of_pos hrpos]
    exact div_le_div_of_nonneg_right hnumabs hrpos.le
  have herror : |β * (d : ℝ)| ≤ 1 / (2 * (r : ℝ)) := by
    calc
      _ = |β| * |(d : ℝ)| := abs_mul _ _
      _ ≤ (1 / (r : ℝ) ^ 2) * ((r : ℝ) / 2) :=
        mul_le_mul hβ hspan (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have heq : (u : ℝ) / r * d - q = (α * d - q) - β * d := by rw [hα]; ring
  rw [heq] at hbase
  have htri : |α * d - q - β * d| ≤ |α * d - q| + |β * d| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (α * d - q) 0 (β * d)
  have hhalf : 1 / (r : ℝ) = 2 * (1 / (2 * (r : ℝ))) := by field_simp
  linarith

end Erdos821.S34.Proofs
