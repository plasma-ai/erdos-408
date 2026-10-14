import Erdos821.P3Clean.Structure

/-! The cutoff leaves a finite memory state space, without choosing ordered representatives. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

instance finite_bounded_multiset {α : Type*} [Finite α] (B : ℕ) :
    Finite {z : Multiset α // z.card ≤ B} := by
  let encode (z : {z : Multiset α // z.card ≤ B}) :
      (j : Fin (B + 1)) × Sym α j.val :=
    ⟨⟨z.val.card, Nat.lt_succ_of_le z.property⟩, ⟨z.val, rfl⟩⟩
  apply Finite.of_injective encode
  intro z w h
  apply Subtype.ext
  exact congrArg (fun c : (j : Fin (B + 1)) × Sym α j.val => c.2.val) h

instance finite_truncated_memory (P : PrimeGroups) (M B : ℕ) :
    Finite {s : P.MemoryState M // P.memorySize s ≤ B} := by
  let encode (s : {s : P.MemoryState M // P.memorySize s ≤ B}) :
      P.SmallResidues × P.Labels M × ((g : P.BigGroup) → {z : P.Memory g.val // z.card ≤ B}) :=
    (s.val.1, s.val.2.1, fun g => ⟨s.val.2.2 g, by
      apply le_trans _ s.property
      exact Finset.single_le_sum (fun h _ => Nat.zero_le ((s.val.2.2 h).card)) (Finset.mem_univ g)⟩)
  apply Finite.of_injective encode
  intro s t h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun c => c.1) h
  · apply Prod.ext
    · exact congrArg (fun c => c.2.1) h
    · funext g
      exact congrArg (fun c => (c.2.2 g).val) h


end Erdos821.P3Clean
