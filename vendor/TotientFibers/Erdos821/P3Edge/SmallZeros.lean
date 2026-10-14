import Erdos821.S2.MemoryEdge
import Mathlib

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

-- Small physical states have at least M zeros per small group.
lemma small_zeros_ge (P : PrimeGroups) {M : ℕ} (y : P.SmallResidues) (a : P.Labels M)
    (hphys : P.smallPhysical y a) (g : P.SmallGroup) :
    M ≤ ((Finset.univ.filter (fun p : P.Prime g.val => y g p = 0)).card) := by
  classical
  -- a g.val : Fin M → Prime, injective with y=0
  obtain ⟨hinj, hzero⟩ := hphys g
  -- Range of a is subset of zeros, card range = M (since injective, Fintype Fin M)
  have hsub : Finset.image (a g.val) Finset.univ ⊆ Finset.univ.filter (fun p : P.Prime g.val => y g p = 0) := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hzero i
  have hcard_range : (Finset.image (a g.val) Finset.univ).card = M := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  calc M = (Finset.image (a g.val) Finset.univ).card := hcard_range.symm
    _ ≤ ((Finset.univ.filter (fun p : P.Prime g.val => y g p = 0)).card) := Finset.card_le_card hsub

end Erdos821.P3Edge
