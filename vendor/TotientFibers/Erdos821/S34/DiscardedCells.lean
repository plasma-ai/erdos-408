import Erdos821.S34.FrameTasks
import Erdos821.S34.BilinearBlocks

set_option autoImplicit false

open scoped BigOperators Classical

namespace Erdos821.S34Core

theorem discarded_cell_mass {α κ : Type*} [Fintype α] [DecidableEq κ]
    (w : α → ℝ) (cell : α → κ) (ξ : ℝ) (hξ : 0 ≤ ξ) :
    (∑ x, if frameCellMass w cell (cell x) < ξ then w x else 0) ≤
      ((Finset.univ.image cell).card : ℝ) * ξ := by
  rw [Erdos821.S34.Proofs.sum_filter_partition Finset.univ cell]
  calc
    _ ≤ ∑ _ ∈ Finset.univ.image cell, ξ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : frameCellMass w cell j < ξ
      · calc
          _ = ∑ x ∈ Finset.univ.filter (fun x => cell x = j), w x := by
            apply Finset.sum_congr rfl
            intro x hx
            have heq := (Finset.mem_filter.mp hx).2
            simp [heq, hj]
          _ = frameCellMass w cell j := by rw [Finset.sum_filter]; rfl
          _ ≤ ξ := hj.le
      · have hz : (∑ x ∈ Finset.univ.filter (fun x => cell x = j),
            if frameCellMass w cell (cell x) < ξ then w x else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          have heq := (Finset.mem_filter.mp hx).2
          simp [heq, hj]
        rw [hz]
        exact hξ
    _ = _ := by simp

theorem comparison_parameter_choices (A d κ C₄ : ℝ) :
    ∃ B q s h ξ D : ℝ,
      A + 2 * (d + 1) + 10 < B ∧
      2 * (B + κ + 10) + d + 1 < q ∧
      2 * (B + κ + 10) + d + 1 < s ∧
      4 * q + max s C₄ + B + 10 < h ∧
      2 * B + d + 1 + h + 10 < ξ ∧
      B + ξ + (5 / 2 : ℝ) * q + 10 < D := by
  let B := A + 2 * (d + 1) + 11
  let q := 2 * (B + κ + 10) + d + 2
  let s := q
  let h := 4 * q + max s C₄ + B + 11
  let ξ := 2 * B + d + 1 + h + 11
  let D := B + ξ + (5 / 2 : ℝ) * q + 11
  exact ⟨B, q, s, h, ξ, D, by dsimp [B]; linarith,
    by dsimp [q]; linarith, by dsimp [s, q]; linarith,
    by dsimp [h]; linarith, by dsimp [ξ]; linarith, by dsimp [D]; linarith⟩

end Erdos821.S34Core
