import Mathlib

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Empty

/-- A finite product sum factors into the product of its one-coordinate sums. -/
theorem sum_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)] {R : Type*} [CommSemiring R]
    (f : ∀ i, β i → R) :
    (∑ x : ∀ i, β i, ∏ i, f i (x i)) = ∏ i, ∑ b, f i b := by
  classical
  calc
    _ = ∑ x ∈ Fintype.piFinset (fun i => (Finset.univ : Finset (β i))),
        ∏ i, f i (x i) := by simp [Fintype.piFinset_univ]
    _ = _ := by
      rw [← Finset.prod_univ_sum (fun i => (Finset.univ : Finset (β i))) f]

/-- Prescribing zero on selected coordinates leaves exactly the unconstrained
complementary coordinates. -/
def zeroCoordinatesEquiv {α : Type*} [DecidableEq α] {β : α → Type*}
    [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Zero (β a)]
    (S : α → Prop) [DecidablePred S] :
    {x : (a : α) → β a // ∀ a, S a → x a = 0} ≃
      (∀ a : {a : α // ¬ S a}, β a.1) where
  toFun x := (Equiv.piEquivPiSubtypeProd S β x.1).2
  invFun z := ⟨(Equiv.piEquivPiSubtypeProd S β).symm ((fun _ => 0), z), by
    intro a ha
    simp [Equiv.piEquivPiSubtypeProd, ha]
  ⟩
  left_inv x := by
    apply Subtype.ext
    funext a
    by_cases ha : S a
    · simp [Equiv.piEquivPiSubtypeProd, ha, x.2 a ha]
    · simp [Equiv.piEquivPiSubtypeProd, ha]
  right_inv z := by
    funext a
    simp [Equiv.piEquivPiSubtypeProd, a.2]


end Erdos821.S2Empty
