import Erdos821.S2.SpanLifecycle

/-! Prime lookup in a memory with no repeated prime values. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups}

theorem pendingPrimes_enumeration {g : P.Group} (z : P.Memory g) :
    pendingPrimes z = (Finset.univ : Finset (Fin z.card)).val.map (fun i => (memoryEntry z i).1) := by
  have he := congrArg pendingPrimes (memoryEntry_enumeration z)
  simpa only [pendingPrimes, Multiset.map_map, Function.comp_def] using he.symm

theorem memoryEntry_mem {g : P.Group} (z : P.Memory g) (i : Fin z.card) : memoryEntry z i ∈ z := by
  have he : memoryEntry z i ∈ (Finset.univ : Finset (Fin z.card)).val.map (memoryEntry z) :=
    Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  rwa [memoryEntry_enumeration] at he

theorem pendingPrime_mem_iff {g : P.Group} (z : P.Memory g) (p : P.Prime g) :
    p ∈ pendingPrimes z ↔ ∃ i : Fin z.card, (memoryEntry z i).1 = p := by
  rw [pendingPrimes_enumeration]
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]

theorem memoryEntry_prime_injective {g : P.Group} (z : P.Memory g) (hz : (pendingPrimes z).Nodup) :
    Function.Injective (fun i : Fin z.card => (memoryEntry z i).1) := by
  rw [pendingPrimes_enumeration] at hz
  intro i j he
  exact Multiset.inj_on_of_nodup_map hz i (Finset.mem_univ i) j (Finset.mem_univ j) he

def primeIndex {g : P.Group} (z : P.Memory g) (p : P.Prime g) (hp : p ∈ pendingPrimes z) : Fin z.card :=
  Classical.choose ((pendingPrime_mem_iff z p).mp hp)

theorem primeIndex_spec {g : P.Group} (z : P.Memory g) (p : P.Prime g) (hp : p ∈ pendingPrimes z) :
    (memoryEntry z (primeIndex z p hp)).1 = p :=
  Classical.choose_spec ((pendingPrime_mem_iff z p).mp hp)

theorem primeIndex_unique {g : P.Group} (z : P.Memory g) (hz : (pendingPrimes z).Nodup)
    (p : P.Prime g) (hp : p ∈ pendingPrimes z) (i : Fin z.card) (hi : (memoryEntry z i).1 = p) :
    primeIndex z p hp = i :=
  memoryEntry_prime_injective z hz ((primeIndex_spec z p hp).trans hi.symm)

theorem primeIndex_injective {g : P.Group} (z : P.Memory g) :
    Function.Injective (fun p : {p : P.Prime g // p ∈ pendingPrimes z} => primeIndex z p.val p.property) := by
  intro p q he
  apply Subtype.ext
  calc
    p.val = (memoryEntry z (primeIndex z p.val p.property)).1 := (primeIndex_spec z p.val p.property).symm
    _ = (memoryEntry z (primeIndex z q.val q.property)).1 := congrArg (fun i => (memoryEntry z i).1) he
    _ = q.val := primeIndex_spec z q.val q.property

theorem deleteMemoryIndices_filter {g : P.Group} (z : P.Memory g) (R : P.Particle g → Prop) :
    deleteMemoryIndices z (Finset.univ.filter (fun i => R (memoryEntry z i))) =
      z.filter (fun u => ¬ R u) := by
  have hs : (Finset.univ : Finset (Fin z.card)) \ Finset.univ.filter (fun i => R (memoryEntry z i)) =
      Finset.univ.filter (fun i => ¬ R (memoryEntry z i)) := by
    ext i
    simp
  rw [deleteMemoryIndices_eq_map, hs]
  calc
    _ = ((Finset.univ : Finset (Fin z.card)).val.map (memoryEntry z)).filter (fun u => ¬ R u) := by
      rw [Multiset.filter_map]
      rfl
    _ = _ := by rw [memoryEntry_enumeration]


end Erdos821.S2Core
