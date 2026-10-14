import Erdos821.S2.MemoryGhost
import Erdos821.Blueprint.Graph

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Adj

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {P : PrimeGroups} {g : P.Group}

/-- Index enumeration counts each particle value correctly. -/
lemma count_eq_card_filter (z : P.Memory g) (u : P.Particle g) :
    z.count u = (Finset.univ.filter (fun i : Fin z.card => memoryEntry z i = u)).card := by
  have hlen : z.toList.length = z.card := Multiset.length_toList z
  have hcount : z.count u = z.toList.count u := by
    conv_lhs => rw [← Multiset.coe_toList z]
    rw [Multiset.coe_count]
  rw [hcount]
  let v : List.Vector (P.Particle g) z.card := ⟨z.toList, by rw [hlen]⟩
  have hvec : v.toList.count u = z.toList.count u := rfl
  have hcard := Fin.card_filter_univ_eq_vector_get_eq_count u v
  rw [← hvec, ← hcard]
  have heq : ∀ i : Fin z.card, v.get i = memoryEntry z i := by
    intro i
    unfold memoryEntry
    rfl
  have hfilter : Finset.univ.filter (fun i : Fin z.card => v.get i = u) =
      Finset.univ.filter (fun i : Fin z.card => memoryEntry z i = u) := by
    apply Finset.filter_congr
    intro i _
    rw [heq i]
  rw [hfilter]

/-- Deletion keeps exactly the unremoved indices. -/
lemma delete_card (z : P.Memory g) (A : Finset (Fin z.card)) :
    (deleteMemoryIndices z A).card = (Finset.univ \ A).card := by
  unfold deleteMemoryIndices
  rw [Multiset.coe_card, List.length_map, Finset.length_toList]

/-- Deletion count per particle value via remaining indices. -/
lemma delete_count_eq (s : P.Memory g) (A : Finset (Fin s.card))
    (v : P.Particle g) :
    (deleteMemoryIndices s A).count v =
    ((Finset.univ \ A).filter (fun i => memoryEntry s i = v)).card := by
  unfold deleteMemoryIndices
  have h1 : ((((Finset.univ \ A).toList.map (memoryEntry s) : List (P.Particle g)) : P.Memory g))
      = (((Finset.univ \ A).val).map (memoryEntry s)) := by
    rw [← Finset.coe_toList, Multiset.map_coe]
  rw [h1, Multiset.count_map]
  have hpred : (((Finset.univ \ A).val).filter (fun a => v = memoryEntry s a))
      = (((Finset.univ \ A).val).filter (fun a => memoryEntry s a = v)) := by
    apply Multiset.filter_congr
    intro a _
    exact eq_comm
  rw [hpred]
  have h2 : ((((Finset.univ \ A).val).filter (fun i => memoryEntry s i = v)).card)
      = (((Finset.univ \ A).filter (fun i => memoryEntry s i = v)).card) := by
    rw [← Finset.filter_val]
    rfl
  rw [h2]

/-- Ordered birth batch has the declared length. -/
lemma birth_card {b : ℕ} (p : Fin b → P.Prime g) :
    (zeroBirthBatch (P := P) (g := g) p).card = b := by
  unfold zeroBirthBatch
  rw [Multiset.coe_card]
  simp


end Erdos821.P3Adj
