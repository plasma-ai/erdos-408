import Erdos821.S2.HighRankTask

noncomputable section
open scoped BigOperators

namespace Erdos821.S2High

open Erdos821.Blueprint.Graph

theorem eta_bounds (F : FixedData) (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ eta F n i ∧ eta F n i ≤ 1 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt F.q := Real.sqrt_nonneg _
  have hsqrt_lt_one : Real.sqrt F.q < 1 := by
    have h := Real.sqrt_lt_sqrt F.q_pos.le F.q_lt
    simpa only [Real.sqrt_one] using h
  have hq_nonneg : 0 ≤ F.q := F.q_pos.le
  unfold eta visitQ
  split_ifs <;> constructor <;> nlinarith [F.q_lt]

theorem one_sub_div_pos_and_inv_le (e p : ℝ) (hp : 0 < p) (he : 0 ≤ e)
    (he' : 2 * e ≤ p) :
    0 < 1 - e / p ∧ (1 - e / p)⁻¹ ≤ 1 + 2 * e / p := by
  have hy : 0 ≤ e / p := div_nonneg he hp.le
  have hy' : e / p ≤ 1 / 2 := (div_le_iff₀ hp).2 (by nlinarith)
  have hpos : 0 < 1 - e / p := by linarith
  constructor
  · exact hpos
  · rw [← one_mul (1 - e / p)⁻¹]
    apply (mul_inv_le_iff₀ hpos).2
    have hnonneg : 0 ≤ 1 - 2 * (e / p) := by linarith
    have hprod := mul_nonneg hy hnonneg
    calc
      1 ≤ 1 + (e / p) * (1 - 2 * (e / p)) := by linarith
      _ = (1 + 2 * e / p) * (1 - e / p) := by ring


end Erdos821.S2High
