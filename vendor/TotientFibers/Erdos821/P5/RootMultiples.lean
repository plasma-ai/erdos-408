import Erdos821.P5.SharedReindex
import Mathlib.Data.Finset.Preimage

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core

/-- Exact source-root set after dividing the roots divisible by D. -/
def strippedRoots (S : Finset ℤ) (D : ℕ) : Finset ℤ :=
  (S.filter (fun n => (D : ℤ) ∣ n)).image (fun n => n / (D : ℤ))

theorem mem_strippedRoots {S : Finset ℤ} {D : ℕ} (hD : D ≠ 0) (w : ℤ) :
    w ∈ strippedRoots S D ↔ (D : ℤ) * w ∈ S := by
  have hDZ : (D : ℤ) ≠ 0 := by exact_mod_cast hD
  constructor
  · intro hw
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hnS, hnD⟩ := Finset.mem_filter.mp hn
    simpa only [Int.mul_ediv_cancel' hnD] using hnS
  · intro hw
    apply Finset.mem_image.mpr
    refine ⟨(D : ℤ) * w, Finset.mem_filter.mpr ⟨hw, dvd_mul_right _ _⟩, ?_⟩
    exact Int.mul_ediv_cancel_left w hDZ

theorem strippedRoots_positive {S : Finset ℤ} {D : ℕ} (hD : 0 < D)
    (hS : ∀ n ∈ S, 0 < n) {w : ℤ} (hw : w ∈ strippedRoots S D) : 0 < w := by
  have hDZ : (0 : ℤ) < D := by exact_mod_cast hD
  exact (mul_pos_iff_of_pos_left hDZ).mp (hS _ ((mem_strippedRoots hD.ne' w).mp hw))

/-- A summand supported on multiples of D reindexes without any endpoint
rounding or extension of the finite source range. -/
theorem sum_strip_multiples {R : Type*} [AddCommMonoid R]
    (S : Finset ℤ) (D : ℕ) (hD : D ≠ 0) (f : ℤ → R)
    (hf : ∀ n ∈ S, ¬(D : ℤ) ∣ n → f n = 0) :
    (∑ n ∈ S, f n) = ∑ w ∈ strippedRoots S D, f ((D : ℤ) * w) := by
  have hDZ : (D : ℤ) ≠ 0 := by exact_mod_cast hD
  calc
    _ = ∑ n ∈ S.filter (fun n => (D : ℤ) ∣ n), f n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hd : (D : ℤ) ∣ n
      · simp only [hd, if_true]
      · simp only [hd, if_false, hf n hn hd]
    _ = _ := by
      symm
      unfold strippedRoots
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [Int.mul_ediv_cancel' (Finset.mem_filter.mp hn).2]
      · intro n hn m hm hnm
        have hnD := (Finset.mem_filter.mp hn).2
        have hmD := (Finset.mem_filter.mp hm).2
        have h := congrArg (fun w => (D : ℤ) * w) hnm
        simpa only [Int.mul_ediv_cancel' hnD, Int.mul_ediv_cancel' hmD] using h

end Erdos821.P5Core
