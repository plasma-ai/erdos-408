import Erdos821.S2.HistoryResourceTasks
import Erdos821.S2.HistoryBirths

/-! Termination removes precisely the selected old indices; births add fresh primes. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups}

theorem memory_indices_partition {g : P.Group} (z : P.Memory g) (B : Finset (Fin z.card)) :
    deleteMemoryIndices z B + B.val.map (memoryEntry z) = z := by
  have hb : B.val ≤ (Finset.univ : Finset (Fin z.card)).val :=
    (Multiset.le_iff_subset B.nodup).mpr (fun i _ => Finset.mem_univ i)
  have he : (Finset.univ \ B).val + B.val = (Finset.univ : Finset (Fin z.card)).val :=
    Multiset.sub_add_cancel hb
  rw [deleteMemoryIndices_eq_map, ← Multiset.map_add, he, memoryEntry_enumeration]

def selectedPendingPrimes {g : P.Group} (z : P.Memory g) (B : Finset (Fin z.card)) :
    Multiset (P.Prime g) := B.val.map (fun i => (memoryEntry z i).1)

theorem pendingPrimes_add_ghost {g : P.Group} (z w : P.Memory g) :
    pendingPrimes (z + w) = pendingPrimes z + pendingPrimes w :=
  Multiset.map_add _ _ _

theorem pendingPrimes_birthBatch {g : P.Group} {b : ℕ} (p : Fin b → P.Prime g) :
    pendingPrimes (zeroBirthBatch p) = ∑ i : Fin b, ({p i} : Multiset (P.Prime g)) := by
  calc
    _ = (List.ofFn p : Multiset (P.Prime g)) := by
      simp only [pendingPrimes, zeroBirthBatch, Multiset.map_coe, List.map_ofFn, Function.comp_def]
    _ = (Finset.univ : Finset (Fin b)).val.map p := by
      rw [Finset.val_univ_fin, Multiset.map_coe, List.ofFn_eq_map]
    _ = _ := (sum_singletons_eq_map Finset.univ p).symm

theorem ghost_live_conservation {M : ℕ} {s t : P.MemoryState M}
    (c : GhostChoice s t) (hc : ghostChoiceValid c) (g : P.BigGroup) :
    pendingPrimes (t.2.2 g) + selectedPendingPrimes (s.2.2 g) (c.1 g) =
      pendingPrimes (s.2.2 g) + ∑ h : Fin (c.2.1 g).val, ({c.2.2 g h} : Multiset (P.Prime g.val)) := by
  have hs : pendingPrimes (deleteMemoryIndices (s.2.2 g) (c.1 g)) +
      selectedPendingPrimes (s.2.2 g) (c.1 g) = pendingPrimes (s.2.2 g) := by
    have he := congrArg pendingPrimes (memory_indices_partition (s.2.2 g) (c.1 g))
    simpa only [pendingPrimes, Multiset.map_add, Multiset.map_map, Function.comp_def,
      selectedPendingPrimes] using he
  have ht : pendingPrimes (t.2.2 g) = pendingPrimes (deleteMemoryIndices (s.2.2 g) (c.1 g)) +
      ∑ h : Fin (c.2.1 g).val, ({c.2.2 g h} : Multiset (P.Prime g.val)) := by
    have he := congrArg pendingPrimes (hc g).2
    simpa only [pendingPrimes_add_ghost, pendingPrimes_birthBatch] using he.symm
  rw [ht, add_right_comm, hs]


end Erdos821.S2Core
