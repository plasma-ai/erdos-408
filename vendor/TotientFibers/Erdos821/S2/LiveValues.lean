import Erdos821.S2.GhostResources

/-! Live prime multiplicities are bounded by the original performed births. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem multiset_map_sum {α β ι : Type*} (s : Finset ι) (f : ι → Multiset α) (g : α → β) :
    (∑ i ∈ s, f i).map g = ∑ i ∈ s, (f i).map g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, Multiset.map_add]

theorem activePrimes_act {M : ℕ} (π : P.Permutations M) (a : P.Labels M) (g : P.Group) :
    activePrimes (P.act π a) g = activePrimes a g := by
  exact Equiv.sum_comp (π g) (fun i => ({a g i} : Multiset (P.Prime g)))

def groupLivePrimes {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup) : Multiset (P.Prime g.val) :=
  activePrimes s.2.1 g.val + pendingPrimes (s.2.2 g)

def liveValues {M : ℕ} (s : P.MemoryState M) : Multiset ℕ :=
  ∑ g : P.BigGroup, (groupLivePrimes s g).map Subtype.val

def ghostNewValues {M : ℕ} {s t : P.MemoryState M} (c : GhostChoice s t) : Multiset ℕ :=
  ∑ g : P.BigGroup, ∑ h : Fin (c.2.1 g).val, {(c.2.2 g h).val}

def edgeNewValues {J ell m : ℕ} (ν : Pattern P J ell m) (a : P.Labels (J + ell))
    (prom : P.BigGroup → Finset (Fin (J + ell))) : Multiset ℕ :=
  ∑ g : P.BigGroup, ∑ h ∈ unsharedDroppedSlots ν g.val (prom g), {(a g.val h).val}

theorem liveValues_permActive {M : ℕ} (π : P.Permutations M) (s : P.MemoryState M) :
    liveValues (permuteActive π s) = liveValues s := by
  simp only [liveValues, groupLivePrimes, permuteActive, activePrimes_act]

theorem ghost_liveValues_le {M : ℕ} {s t : P.MemoryState M}
    (c : GhostChoice s t) (hc : ghostChoiceValid c) (ha : s.2.1 = t.2.1) :
    liveValues t ≤ liveValues s + ghostNewValues c := by
  have hg (g : P.BigGroup) : groupLivePrimes t g ≤ groupLivePrimes s g +
      ∑ h : Fin (c.2.1 g).val, ({c.2.2 g h} : Multiset (P.Prime g.val)) := by
    have hp : pendingPrimes (t.2.2 g) ≤ pendingPrimes (s.2.2 g) +
        ∑ h : Fin (c.2.1 g).val, ({c.2.2 g h} : Multiset (P.Prime g.val)) := by
      rw [← ghost_live_conservation c hc g]
      exact Multiset.le_add_right _ _
    dsimp only [groupLivePrimes]
    rw [← ha]
    calc
      _ ≤ activePrimes s.2.1 g.val + (pendingPrimes (s.2.2 g) +
          ∑ h : Fin (c.2.1 g).val, ({c.2.2 g h} : Multiset (P.Prime g.val))) := add_le_add (le_refl _) hp
      _ = _ := by ac_rfl
  simp only [liveValues, ghostNewValues, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  have he := Multiset.map_le_map (f := Subtype.val) (hg g)
  simpa only [Multiset.map_add, multiset_map_sum, Multiset.map_singleton] using he

theorem edge_liveValues_le (hTask : EdgeLiveConservationTask) (A : Model F P J m)
    (ν : Pattern P J F.ell m) (forward : Bool) (u : P.Aux J)
    (s t : P.MemoryState (J + F.ell)) (c : TransferChoice s) (hc : rawEdgeValid A ν forward u s t c) :
    liveValues t ≤ liveValues s + edgeNewValues ν t.2.1 c.2.1 := by
  simp only [liveValues, edgeNewValues, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  have hp : groupLivePrimes t g ≤ groupLivePrimes s g +
      slotPrimes (t.2.1 g.val) (unsharedDroppedSlots ν g.val (c.2.1 g)) := by
    calc
      _ ≤ groupLivePrimes t g + slotPrimes (s.2.1 g.val)
          (unsharedDroppedSlots ν g.val (c.1 g)) := Multiset.le_add_right _ _
      _ = _ := hTask F P J m A ν forward u s t c hc g
  have he := Multiset.map_le_map (f := Subtype.val) hp
  simpa only [Multiset.map_add, slotPrimes, multiset_map_sum, Multiset.map_singleton] using he

namespace MemoryHistory

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)

theorem ghost_liveValues_le (hH : H.Valid) (i : Fin (n + 1)) :
    liveValues (H.after i) ≤ liveValues (H.before i) + H.ghostBirthValues i :=
  Erdos821.S2Core.ghost_liveValues_le (H.ghost i) (hH.2.2.1 i).2.2 (hH.2.2.1 i).2.1

theorem edge_liveValues_le (hTask : EdgeLiveConservationTask) (hH : H.Valid) (i : Fin n) :
    liveValues (H.before i.succ) ≤ liveValues (H.after i.castSucc) + H.freshBirthValues i := by
  have he := Erdos821.S2Core.edge_liveValues_le hTask A (A.pattern (H.edge i).2.2.1)
    (edgeForward i) (H.edge i).2.2.2.1 (permuteActive (H.edge i).1 (H.after i.castSucc))
    (permuteActive (H.edge i).2.1 (H.before i.succ)) (H.edge i).2.2.2.2 (hH.2.2.2 i).1
  rw [liveValues_permActive, liveValues_permActive] at he
  exact he

end MemoryHistory


end Erdos821.S2Core
