import Mathlib

set_option autoImplicit false

namespace Erdos821.S34Core

theorem scaled_dirichlet_approximation (α Z S : ℝ)
    (hZ : 0 < Z) (hS : 0 < S) (hZS : 1 ≤ Z / S) :
    ∃ (u : ℤ) (r : ℕ) (β : ℝ),
      1 ≤ r ∧ Nat.Coprime u.natAbs r ∧ (r : ℝ) ≤ Z / S ∧
      α = (u : ℝ) / r + β ∧ |β| ≤ (r : ℝ) ^ (-2 : ℤ) ∧ |β| * Z ≤ 2 * S / r := by
  let N := ⌊Z / S⌋₊
  have hN : 0 < N := by
    have hn : 1 ≤ N := Nat.le_floor (by simpa using hZS)
    omega
  obtain ⟨q, hq, hqr⟩ := Real.exists_rat_abs_sub_le_and_den_le α hN
  have hr : 0 < (q.den : ℝ) := by exact_mod_cast Rat.pos q
  have hNle : (q.den : ℝ) ≤ (N : ℝ) := by exact_mod_cast hqr
  have hNfloor : (N : ℝ) ≤ Z / S := Nat.floor_le (by positivity)
  have hNnext : Z / S < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcast : (q : ℝ) = (q.num : ℝ) / q.den := by exact Rat.cast_def q
  refine ⟨q.num, q.den, α - q, by exact_mod_cast Rat.pos q,
    q.reduced, hNle.trans hNfloor, ?_, ?_, ?_⟩
  · rw [← hcast]
    ring
  · calc
      _ ≤ 1 / (((N : ℝ) + 1) * q.den) := hq
      _ ≤ 1 / (q.den : ℝ) ^ 2 := by
        apply one_div_le_one_div_of_le (sq_pos_of_pos hr)
        nlinarith
      _ = _ := by simp [zpow_neg, zpow_natCast, one_div]
  · have hmul : Z ≤ ((N : ℝ) + 1) * S := ((div_lt_iff₀ hS).mp hNnext).le
    have hden : 0 < ((N : ℝ) + 1) * q.den := by positivity
    calc
      _ ≤ (1 / (((N : ℝ) + 1) * q.den)) * Z := mul_le_mul_of_nonneg_right hq hZ.le
      _ = Z / (((N : ℝ) + 1) * q.den) := by ring
      _ ≤ S / q.den := by
        apply (div_le_iff₀ hden).mpr
        field_simp
        nlinarith
      _ ≤ 2 * S / q.den := by
        apply div_le_div_of_nonneg_right _ hr.le
        linarith

end Erdos821.S34Core
