import Erdos821.S2.MemoryIndices

/-! Index-level conservation needed to reconstruct original prime lifespans. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups}

def activePrimes {M : ℕ} (a : P.Labels M) (g : P.Group) : Multiset (P.Prime g) :=
  ∑ i : Fin M, {a g i}

def pendingPrimes {g : P.Group} (z : P.Memory g) : Multiset (P.Prime g) := z.map (fun u => u.1)

def slotPrimes {M : ℕ} {g : P.Group} (a : Fin M → P.Prime g) (slots : Finset (Fin M)) : Multiset (P.Prime g) :=
  ∑ i ∈ slots, {a i}

def unsharedDroppedSlots {J ell m : ℕ} (ν : Pattern P J ell m) (g : P.Group)
    (stores : Finset (Fin (J + ell))) : Finset (Fin (J + ell)) :=
  Finset.univ.filter (fun i => ¬ ν.shared g i ∧ i ∉ stores)

/-- Retrievals cancel once against the old pending indices. Stores cancel once
against unshared source slots. The equality keeps all numerical multiplicities. -/
def EdgeLiveConservationTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J m : ℕ) (A : Model F P J m)
    (ν : Pattern P J F.ell m) (forward : Bool) (u : P.Aux J)
    (s t : P.MemoryState (J + F.ell)) (c : TransferChoice s),
    rawEdgeValid A ν forward u s t c → ∀ g : P.BigGroup,
      activePrimes t.2.1 g.val + pendingPrimes (t.2.2 g) +
        slotPrimes (s.2.1 g.val) (unsharedDroppedSlots ν g.val (c.1 g)) =
      activePrimes s.2.1 g.val + pendingPrimes (s.2.2 g) +
        slotPrimes (t.2.1 g.val) (unsharedDroppedSlots ν g.val (c.2.1 g))

end Erdos821.S2Core

