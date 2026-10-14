import Erdos821.S2.PrimeIndices

/-! The visit choices reconstructed from finite prime lifespans. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

namespace ResiduePath

variable {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n)

theorem memoryBefore_member_form (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup)
    (z : P.Particle g.val) (hz : z ∈ Q.memoryBefore S i g) :
    ∃ p ∈ Q.pendingBeforePrimes S i g,
      z = (⟨p, ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val) := by
  have he := Q.memoryBefore_eq_map S i g
  have hm := Eq.mp (congrArg (fun m : P.Memory g.val => z ∈ m) he) hz
  obtain ⟨p, hp, he⟩ := Multiset.mem_map.mp hm
  exact ⟨p, hp, he.symm⟩

def ghostBatchLabels (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup)
    (h : Fin (Q.ghostBirthPrimes S i g).card) : P.Prime g.val :=
  (Q.ghostBirthPrimes S i g).toList.get ⟨h.val, by simpa using h.isLt⟩

theorem ghostBatchLabels_enumeration (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) :
    List.ofFn (Q.ghostBatchLabels S i g) = (Q.ghostBirthPrimes S i g).toList := by
  let v : List.Vector (P.Prime g.val) (Q.ghostBirthPrimes S i g).card :=
    ⟨(Q.ghostBirthPrimes S i g).toList, Finset.length_toList _⟩
  have he : Q.ghostBatchLabels S i g = v.get := by funext h; rfl
  rw [he, ← List.Vector.toList_ofFn, List.Vector.ofFn_get]
  rfl

theorem ghostBatch_eq_map (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) :
    zeroBirthBatch (Q.ghostBatchLabels S i g) = (Q.ghostBirthPrimes S i g).val.map
      (fun p => (⟨p, 0⟩ : P.Particle g.val)) := by
  unfold zeroBirthBatch
  rw [List.ofFn_comp' (Q.ghostBatchLabels S i g) (fun p => (⟨p, 0⟩ : P.Particle g.val))]
  rw [Q.ghostBatchLabels_enumeration]
  rw [← Multiset.map_coe, Finset.coe_toList]

def ghostTerminationIndices (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) :
    Finset (Fin (Q.memoryBefore S i g).card) :=
  Finset.univ.filter (fun h => (memoryEntry (Q.memoryBefore S i g) h).1 ∈ Q.ghostStopPrimes S i g)

def reconstructedGhostChoice (S : LifespanAssignment P n) (hS : Q.lifespanValid S)
    (y : P.SmallResidues) (i : Fin (n + 1)) : GhostChoice (Q.stateBefore S y i) (Q.stateAfter S y i) :=
  ⟨Q.ghostTerminationIndices S i,
    ⟨(fun g : P.BigGroup => (⟨(Q.ghostBirthPrimes S i g).card,
      Nat.lt_succ_of_le (Q.ghostBirthPrimes_card_le S hS i g)⟩ : Fin ((Q.memoryAfter S i g).card + 1))),
      Q.ghostBatchLabels S i⟩⟩

theorem ghostStop_residue_zero (S : LifespanAssignment P n) (hS : Q.lifespanValid S)
    (i : Fin (n + 1)) (g : P.BigGroup) (p : P.Prime g.val) (hp : p ∈ Q.ghostStopPrimes S i g) :
    ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val) = 0 := by
  have hb := (Finset.mem_filter.mp hp).2
  have hs := hS g p
  rcases he : S g p with _ | ⟨birth, stop⟩
  · simp only [he, ghostStopAt] at hb
  · rw [he] at hb hs
    obtain ⟨rfl, _⟩ := hb
    exact hs.2.2.2.1

theorem ghostTerminationIndices_zero (S : LifespanAssignment P n) (hS : Q.lifespanValid S)
    (i : Fin (n + 1)) (g : P.BigGroup) :
    Q.ghostTerminationIndices S i g ⊆ zeroMemoryIndices (Q.memoryBefore S i g) := by
  intro h hh
  have hs := (Finset.mem_filter.mp hh).2
  have hm := Q.memoryBefore_member_form S i g (memoryEntry (Q.memoryBefore S i g) h)
    (memoryEntry_mem (Q.memoryBefore S i g) h)
  obtain ⟨p, _, he⟩ := hm
  have hp : p ∈ Q.ghostStopPrimes S i g := by simpa only [he] using hs
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [he]
  exact Q.ghostStop_residue_zero S hS i g p hp


theorem ghost_pending_sets (S : LifespanAssignment P n) (hS : Q.lifespanValid S)
    (i : Fin (n + 1)) (g : P.BigGroup) :
    (Q.pendingBeforePrimes S i g \ Q.ghostStopPrimes S i g) ∪ Q.ghostBirthPrimes S i g =
      Q.pendingAfterPrimes S i g := by
  ext p
  simp only [Finset.mem_union, Finset.mem_sdiff, pendingBeforePrimes, pendingAfterPrimes,
    ghostStopPrimes, ghostBirthPrimes, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Q.ghost_occupancy_update g p (S g p) (hS g p) i

theorem ghost_pending_disjoint (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) :
    Disjoint (Q.pendingBeforePrimes S i g \ Q.ghostStopPrimes S i g) (Q.ghostBirthPrimes S i g) := by
  apply Finset.disjoint_left.mpr
  intro p hp hb
  have hpre := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
  have hborn := (Finset.mem_filter.mp hb).2
  rcases he : S g p with _ | ⟨birth, stop⟩
  · simp only [he, pendingBefore] at hpre
  · rw [he] at hpre hborn
    obtain ⟨rfl, _⟩ := hborn
    exact lt_irrefl _ hpre.1

theorem ghostBorn_particle_zero (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup)
    (p : P.Prime g.val) (hp : p ∈ Q.ghostBirthPrimes S i g) :
    (⟨p, ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val) = ⟨p, 0⟩ := by
  have hb := (Finset.mem_filter.mp hp).2
  rcases he : S g p with _ | ⟨birth, stop⟩
  · simp only [he, ghostBirthAt] at hb
  · rw [he] at hb
    obtain ⟨rfl, _⟩ := hb
    simp only [he, spanAnchor, sub_self, Int.cast_zero]

theorem ghostDeleted_eq_map (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) :
    deleteMemoryIndices (Q.memoryBefore S i g) (Q.ghostTerminationIndices S i g) =
      (Q.pendingBeforePrimes S i g \ Q.ghostStopPrimes S i g).val.map
        (fun p => (⟨p, ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val)) := by
  let R : P.Particle g.val → Prop := fun z => z.1 ∈ Q.ghostStopPrimes S i g
  have hi : Q.ghostTerminationIndices S i g = Finset.univ.filter
      (fun h => R (memoryEntry (Q.memoryBefore S i g) h)) := by
    ext h
    simp only [ghostTerminationIndices, Finset.mem_filter, Finset.mem_univ, true_and, R]
  have hd := deleteMemoryIndices_filter (P := P) (g := g.val) (Q.memoryBefore S i g) R
  rw [hi]
  calc
    _ = (Q.memoryBefore S i g).filter (fun z => ¬ R z) := by
      convert hd using 1
      · congr 1
        ext h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      · apply Multiset.ext.mpr
        intro z
        by_cases hz : ¬ R z
        · simp only [Multiset.count_filter, ite_eq_left hz]
        · simp only [Multiset.count_filter, ite_eq_right hz]
    _ = _ := by
      rw [memoryBefore_eq_map, Multiset.filter_map]
      change ((Q.pendingBeforePrimes S i g).filter (fun p => p ∉ Q.ghostStopPrimes S i g)).val.map _ = _
      congr 2
      ext p
      simp

theorem reconstructed_ghost_memory (S : LifespanAssignment P n) (hS : Q.lifespanValid S)
    (i : Fin (n + 1)) (g : P.BigGroup) :
    deleteMemoryIndices (Q.memoryBefore S i g) (Q.ghostTerminationIndices S i g) +
      zeroBirthBatch (Q.ghostBatchLabels S i g) = Q.memoryAfter S i g := by
  rw [ghostDeleted_eq_map, ghostBatch_eq_map, memoryAfter_eq_map]
  have hb : (Q.ghostBirthPrimes S i g).val.map (fun p => (⟨p, 0⟩ : P.Particle g.val)) =
      (Q.ghostBirthPrimes S i g).val.map
        (fun p => (⟨p, ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val)) := by
    apply Multiset.map_congr rfl
    intro p hp
    exact (Q.ghostBorn_particle_zero S i g p hp).symm
  have hu : (Q.pendingBeforePrimes S i g \ Q.ghostStopPrimes S i g).val +
      (Q.ghostBirthPrimes S i g).val = (Q.pendingAfterPrimes S i g).val := by
    rw [← Q.ghost_pending_sets S hS i g, Finset.union_val]
    apply Multiset.add_eq_union_iff_disjoint.mpr
    apply Multiset.disjoint_left.mpr
    intro p hp ht
    exact Finset.disjoint_left.mp (Q.ghost_pending_disjoint S i g) hp ht
  rw [hb, ← Multiset.map_add, hu]

theorem reconstructedGhostChoice_valid (S : LifespanAssignment P n) (hS : Q.lifespanValid S)
    (y : P.SmallResidues) (i : Fin (n + 1)) : ghostChoiceValid (Q.reconstructedGhostChoice S hS y i) := by
  intro g
  exact ⟨Q.ghostTerminationIndices_zero S hS i g, Q.reconstructed_ghost_memory S hS i g⟩

end ResiduePath


end Erdos821.S2Core
