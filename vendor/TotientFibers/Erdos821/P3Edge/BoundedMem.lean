import Mathlib

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

-- Finite set of multisets with bounded card over a finite alphabet.
lemma finite_multiset_bounded (α : Type*) [Fintype α] [DecidableEq α] (N : ℕ) :
    Set.Finite {z : Multiset α | z.card ≤ N} := by
  classical
  -- Work with subtype
  let S : Set (Multiset α) := {z | z.card ≤ N}
  suffices h : Finite S by exact h
  -- Inject counts into finite pi type
  let F := (a : α) → Fin (N + 1)
  have hF : Fintype F := inferInstance
  have hFinF : Finite F := inferInstance
  let f : S → F := fun z a =>
    ⟨z.val.count a, Nat.lt_succ_of_le (le_trans (Multiset.count_le_card a z.val) z.property)⟩
  have hfinj : Function.Injective f := by
    intro ⟨z1, h1⟩ ⟨z2, h2⟩ heq
    simp only [S, Set.mem_setOf_eq] at h1 h2
    -- heq : f ⟨z1,h1'⟩ = f ⟨z2,h2'⟩, need counts equal
    have hcount : ∀ a : α, z1.count a = z2.count a := by
      intro a
      have h : f ⟨z1, h1⟩ a = f ⟨z2, h2⟩ a := by rw [heq]
      simp only [f] at h
      exact congrArg Fin.val h
    -- Multisets determined by counts
    have heqz : z1 = z2 := by
      ext a
      exact hcount a
    simp [heqz]
  exact Finite.of_injective f hfinj

end Erdos821.P3Edge
