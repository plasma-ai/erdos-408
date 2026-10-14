import Erdos821.S2.Definitions

/-! Equality-rank combinatorics for the distinct-birth expansion. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2

/-- The sign sum of permutations preserving numerical values is their
injectivity indicator. This is the cancellation step behind the block expansion. -/
theorem value_preserving_sign_sum {α : Type*} [Fintype α] [DecidableEq α]
    (value : α → ℕ) :
    (if Function.Injective value then (1 : ℤ) else 0) =
      ∑ σ : Equiv.Perm α, (Equiv.Perm.sign σ : ℤ) *
        ∏ i, (if value (σ i) = value i then (1 : ℤ) else 0) := by
  classical
  let M : Matrix α α ℤ := fun i j => if value i = value j then 1 else 0
  have hdet : (if Function.Injective value then (1 : ℤ) else 0) = M.det := by
    by_cases hv : Function.Injective value
    · have hM : M = 1 := by
        ext i j
        simp only [M, Matrix.one_apply, hv.eq_iff]
      simp [hv, hM]
    · obtain ⟨i, j, hij, hvij⟩ := Function.not_injective_iff.mp hv
      have hr : M i = M j := by
        funext k
        simp [M, hij]
      simp only [hv, ↓reduceIte]
      exact (Matrix.det_zero_of_row_eq hvij hr).symm
  exact hdet.trans (by simpa only [M, Int.cast_id] using Matrix.det_apply' M)


end Erdos821.S2
