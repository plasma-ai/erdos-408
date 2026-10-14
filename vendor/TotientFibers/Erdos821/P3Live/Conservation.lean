import Erdos821.S2.HistoryResourceTasks
import Erdos821.S2.MemoryEdge
import Erdos821.S2.MemoryIndices

set_option autoImplicit false

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups}

/-- Finset sum of singletons equals the mapped finset value. -/
theorem slotPrimes_eq_val_map {M : ℕ} {g : P.Group}
    (a : Fin M → P.Prime g) (s : Finset (Fin M)) :
    slotPrimes a s = s.val.map (fun i => a i) := by
  unfold slotPrimes
  rw [Finset.sum_eq_multiset_sum]
  have h : s.1.map (fun i => ({a i} : Multiset (P.Prime g)))
      = (s.1.map (fun i => a i)).map (fun p => ({p} : Multiset (P.Prime g))) := by
    rw [Multiset.map_map]
    rfl
  rw [h, Multiset.sum_map_singleton]

theorem activePrimes_eq_slotPrimes_univ {M : ℕ} (a : P.Labels M) (g : P.Group) :
    activePrimes a g = slotPrimes (a g) Finset.univ :=
  rfl

/-- Translation preserves the prime projection. -/
theorem pendingPrimes_translate (delta : ℤ) {g : P.Group} (w : P.Memory g) :
    pendingPrimes (translateMemory delta w) = pendingPrimes w := by
  unfold pendingPrimes translateMemory
  rw [Multiset.map_map]
  have h : ((fun u : P.Particle g => u.1) ∘ translateParticle delta)
      = (fun u : P.Particle g => u.1) := by
    funext u
    rfl
  rw [h]

theorem pendingPrimes_add {g : P.Group} (a b : P.Memory g) :
    pendingPrimes (a + b) = pendingPrimes a + pendingPrimes b :=
  Multiset.map_add _ _ _

/-- Stored memory contributes exactly the stored slot primes. -/
theorem pendingPrimes_stored {M : ℕ} {g : P.Group}
    (a : Fin M → P.Prime g) (B : Finset (Fin M)) :
    pendingPrimes (storedMemory (P := P) a B) = slotPrimes a B := by
  unfold pendingPrimes storedMemory
  have hlist : ((B.toList.map (fun i => (⟨a i, 0⟩ : P.Particle g))).map (fun u => u.1))
      = B.toList.map (fun i => a i) := by
    rw [List.map_map]
    rfl
  have hmap : Multiset.map (fun u : P.Particle g => u.1)
      ((B.toList.map (fun i => (⟨a i, 0⟩ : P.Particle g)) : List (P.Particle g)) : Multiset (P.Particle g))
      = ((B.toList.map (fun i => (⟨a i, 0⟩ : P.Particle g))).map (fun u => u.1) : List (P.Prime g)) := by
    rw [Multiset.map_coe]
  rw [hmap, hlist]
  have hcoe : ((B.toList.map (fun i => a i) : List (P.Prime g)) : Multiset (P.Prime g))
      = B.val.map (fun i => a i) := by
    rw [← Multiset.map_coe, Finset.coe_toList]
  rw [hcoe, ← slotPrimes_eq_val_map]

/-- Source pending splits into deleted pending plus retrieved primes. -/
theorem pendingPrimes_delete_add {g : P.Group} (z : P.Memory g)
    (B : Finset (Fin z.card)) :
    pendingPrimes z =
      pendingPrimes (deleteMemoryIndices z B)
        + B.val.map (fun k => (memoryEntry z k).1) := by
  classical
  set f : Fin z.card → P.Prime g := fun k => (memoryEntry z k).1 with hf
  have hsrc : pendingPrimes z = slotPrimes f Finset.univ := by
    have he := memoryEntry_enumeration (P := P) z
    unfold pendingPrimes
    have h1 : z.map (fun u : P.Particle g => u.1)
        = (Finset.univ.val.map (memoryEntry z)).map (fun u : P.Particle g => u.1) := by
      rw [he]
    rw [h1, Multiset.map_map]
    rw [← slotPrimes_eq_val_map]
    rfl
  have hdel : pendingPrimes (deleteMemoryIndices z B) =
      slotPrimes f (Finset.univ \ B) := by
    have hd := deleteMemoryIndices_eq_map (P := P) z B
    unfold pendingPrimes
    rw [hd, Multiset.map_map]
    rw [← slotPrimes_eq_val_map]
    rfl
  have hret : B.val.map (fun k => (memoryEntry z k).1) = slotPrimes f B := by
    rw [slotPrimes_eq_val_map]
  rw [hsrc, hdel, hret]
  exact (Finset.sum_sdiff (Finset.subset_univ B)).symm

/-- Promoted target slots carry exactly the retrieved primes. -/
theorem promoted_eq_retrieved {M : ℕ} {s : P.MemoryState M}
    (c : TransferChoice s) (g : P.BigGroup)
    (Tact : Fin M → P.Prime g.val)
    (hInj : Function.Injective (c.2.2 g))
    (hRet : ∀ i : {i : Fin M // i ∈ c.2.1 g},
      (memoryEntry (s.2.2 g) (c.2.2 g i)).1 = Tact i.val) :
    slotPrimes Tact (c.2.1 g)
      = (retrievedIndices c g).val.map (fun k => (memoryEntry (s.2.2 g) k).1) := by
  classical
  have hdef : retrievedIndices c g = Finset.univ.image (c.2.2 g) := rfl
  rw [hdef, ← slotPrimes_eq_val_map]
  have hInjOn : Set.InjOn (c.2.2 g) (↑(Finset.univ : Finset {i : Fin M // i ∈ c.2.1 g})) := by
    exact hInj.injOn
  have himage : slotPrimes (fun k : Fin (s.2.2 g).card => (memoryEntry (s.2.2 g) k).1)
      (Finset.univ.image (c.2.2 g))
      = ∑ j : {i : Fin M // i ∈ c.2.1 g},
        ({(memoryEntry (s.2.2 g) (c.2.2 g j)).1} : Multiset (P.Prime g.val)) := by
    unfold slotPrimes
    rw [Finset.sum_image hInjOn]
  rw [himage]
  have hval : (∑ j : {i : Fin M // i ∈ c.2.1 g},
        ({(memoryEntry (s.2.2 g) (c.2.2 g j)).1} : Multiset (P.Prime g.val)))
      = (∑ j : {i : Fin M // i ∈ c.2.1 g},
        ({Tact j.val} : Multiset (P.Prime g.val))) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hRet j]
  rw [hval]
  have hatt : (Finset.univ : Finset {i : Fin M // i ∈ c.2.1 g}) = (c.2.1 g).attach :=
    rfl
  rw [hatt]
  exact (Finset.sum_attach (c.2.1 g) (fun i => ({Tact i} : Multiset (P.Prime g.val)))).symm

theorem EdgeLiveConservationTask_proof : EdgeLiveConservationTask := by
  classical
  intro F P J m A ν forward u s t c hvalid g
  obtain ⟨_, _, hcompat, _, _, hg⟩ := hvalid
  obtain ⟨hStores, hPromMem, hInj, hRetFull, hMemEq⟩ := hg g
  have hRet : ∀ i : {i : Fin (J + F.ell) // i ∈ c.2.1 g},
      (memoryEntry (s.2.2 g) (c.2.2 g i)).1 = t.2.1 g.val i.val := by
    intro i
    exact (hRetFull i).1
  set Shared : Finset (Fin (J + F.ell)) :=
    Finset.univ.filter (ν.shared g.val) with hSharedDef
  set Unshared : Finset (Fin (J + F.ell)) :=
    Finset.univ.filter (fun i => ¬ ν.shared g.val i) with hUnsharedDef
  set Ds : Finset (Fin (J + F.ell)) :=
    unsharedDroppedSlots ν g.val (c.1 g) with hDsDef
  set Dt : Finset (Fin (J + F.ell)) :=
    unsharedDroppedSlots ν g.val (c.2.1 g) with hDtDef
  have hStoresSub : c.1 g ⊆ Unshared := by
    intro i hi
    rw [hUnsharedDef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hStores i hi).1
  have hPromSub : c.2.1 g ⊆ Unshared := by
    intro i hi
    rw [hUnsharedDef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hPromMem i hi
  have hDsEq : Unshared \ c.1 g = Ds := by
    rw [hDsDef, hUnsharedDef]
    unfold unsharedDroppedSlots
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
  have hDtEq : Unshared \ c.2.1 g = Dt := by
    rw [hDtDef, hUnsharedDef]
    unfold unsharedDroppedSlots
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
  have hSharedEq : slotPrimes (s.2.1 g.val) Shared
      = slotPrimes (t.2.1 g.val) Shared := by
    show (∑ i ∈ Shared, ({s.2.1 g.val i} : Multiset _))
      = (∑ i ∈ Shared, ({t.2.1 g.val i} : Multiset _))
    apply Finset.sum_congr rfl
    intro i hi
    have hmem : ν.shared g.val i := by
      rw [hSharedDef] at hi
      simpa using (Finset.mem_filter.mp hi).2
    have heq : s.2.1 g.val i = t.2.1 g.val i := hcompat g.val i hmem
    rw [heq]
  have hS_split : slotPrimes (s.2.1 g.val) Shared
        + slotPrimes (s.2.1 g.val) Unshared
      = slotPrimes (s.2.1 g.val) Finset.univ := by
    show (∑ i ∈ Shared, ({s.2.1 g.val i} : Multiset _))
        + (∑ i ∈ Unshared, ({s.2.1 g.val i} : Multiset _))
      = (∑ i ∈ (Finset.univ : Finset (Fin (J + F.ell))),
        ({s.2.1 g.val i} : Multiset _))
    rw [hSharedDef, hUnsharedDef]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hT_split : slotPrimes (t.2.1 g.val) Shared
        + slotPrimes (t.2.1 g.val) Unshared
      = slotPrimes (t.2.1 g.val) Finset.univ := by
    show (∑ i ∈ Shared, ({t.2.1 g.val i} : Multiset _))
        + (∑ i ∈ Unshared, ({t.2.1 g.val i} : Multiset _))
      = (∑ i ∈ (Finset.univ : Finset (Fin (J + F.ell))),
        ({t.2.1 g.val i} : Multiset _))
    rw [hSharedDef, hUnsharedDef]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hS_unshared : slotPrimes (s.2.1 g.val) Unshared
      = slotPrimes (s.2.1 g.val) (c.1 g) + slotPrimes (s.2.1 g.val) Ds := by
    show (∑ i ∈ Unshared, ({s.2.1 g.val i} : Multiset _))
      = (∑ i ∈ c.1 g, ({s.2.1 g.val i} : Multiset _))
        + (∑ i ∈ Ds, ({s.2.1 g.val i} : Multiset _))
    have h : (∑ i ∈ Unshared \ c.1 g, ({s.2.1 g.val i} : Multiset (P.Prime g.val)))
        + (∑ i ∈ c.1 g, ({s.2.1 g.val i} : Multiset (P.Prime g.val)))
        = (∑ i ∈ Unshared, ({s.2.1 g.val i} : Multiset (P.Prime g.val))) :=
      Finset.sum_sdiff hStoresSub
    rw [hDsEq] at h
    rw [add_comm] at h
    exact h.symm.trans (by rw [add_comm])
  have hT_unshared : slotPrimes (t.2.1 g.val) Unshared
      = slotPrimes (t.2.1 g.val) (c.2.1 g) + slotPrimes (t.2.1 g.val) Dt := by
    show (∑ i ∈ Unshared, ({t.2.1 g.val i} : Multiset _))
      = (∑ i ∈ c.2.1 g, ({t.2.1 g.val i} : Multiset _))
        + (∑ i ∈ Dt, ({t.2.1 g.val i} : Multiset _))
    have h : (∑ i ∈ Unshared \ c.2.1 g, ({t.2.1 g.val i} : Multiset (P.Prime g.val)))
        + (∑ i ∈ c.2.1 g, ({t.2.1 g.val i} : Multiset (P.Prime g.val)))
        = (∑ i ∈ Unshared, ({t.2.1 g.val i} : Multiset (P.Prime g.val))) :=
      Finset.sum_sdiff hPromSub
    rw [hDtEq] at h
    rw [add_comm] at h
    exact h.symm.trans (by rw [add_comm])
  have hSP : pendingPrimes (s.2.2 g)
      = pendingPrimes (deleteMemoryIndices (s.2.2 g) (retrievedIndices c g))
        + slotPrimes (t.2.1 g.val) (c.2.1 g) := by
    have hdel := pendingPrimes_delete_add (s.2.2 g) (retrievedIndices c g)
    have hprom := promoted_eq_retrieved c g (t.2.1 g.val) hInj hRet
    rw [← hprom] at hdel
    exact hdel
  have hTP : pendingPrimes (t.2.2 g)
      = pendingPrimes (deleteMemoryIndices (s.2.2 g) (retrievedIndices c g))
        + slotPrimes (s.2.1 g.val) (c.1 g) := by
    rw [hMemEq, pendingPrimes_translate, pendingPrimes_add,
      pendingPrimes_stored]
  have hSA : activePrimes s.2.1 g.val = slotPrimes (s.2.1 g.val) Finset.univ := rfl
  have hTA : activePrimes t.2.1 g.val = slotPrimes (t.2.1 g.val) Finset.univ := rfl
  rw [hSA, hTA]
  rw [← hS_split, ← hT_split, hS_unshared, hT_unshared, hSP, hTP, hSharedEq]
  ac_rfl


end Erdos821.S2Core
