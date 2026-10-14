import Erdos821.P3Edge.ColBound

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

-- Column valid set is finite via bounded memories.
lemma col_valid_set_finite (A : Model F P J m) {n : ℕ} (i : Fin n)
    (t : P.MemoryState (J + F.ell)) :
    Set.Finite {s : P.MemoryState (J + F.ell) | ∃ c : EdgeChoice A s, edgeChoiceValid A .all i s t c} := by
  classical
  let bound : (g : P.BigGroup) → ℕ := fun g => (t.2.2 g).card + (J + F.ell)
  have hmem_fin : ∀ g : P.BigGroup, Set.Finite {z : P.Memory (g : P.Group) | z.card ≤ bound g} := by
    intro g
    exact finite_multiset_bounded (P.Particle (g : P.Group)) (bound g)
  have hpi : Set.Finite (Set.univ.pi (fun g : P.BigGroup => {z : P.Memory (g : P.Group) | z.card ≤ bound g})) :=
    Set.Finite.pi (fun g => hmem_fin g)
  have hsmall : Set.Finite (Set.univ : Set P.SmallResidues) := Set.finite_univ
  have hlabels : Set.Finite (Set.univ : Set (P.Labels (J + F.ell))) := Set.finite_univ
  have hprod_labels : Set.Finite ((Set.univ : Set (P.Labels (J + F.ell))) ×ˢ (Set.univ.pi (fun g : P.BigGroup => {z : P.Memory (g : P.Group) | z.card ≤ bound g}))) :=
    hlabels.prod hpi
  have hprod : Set.Finite ((Set.univ : Set P.SmallResidues) ×ˢ ((Set.univ : Set (P.Labels (J + F.ell))) ×ˢ (Set.univ.pi (fun g : P.BigGroup => {z : P.Memory (g : P.Group) | z.card ≤ bound g})))) :=
    hsmall.prod hprod_labels
  have hsub : {s : P.MemoryState (J + F.ell) | ∃ c : EdgeChoice A s, edgeChoiceValid A .all i s t c} ⊆
      (Set.univ : Set P.SmallResidues) ×ˢ ((Set.univ : Set (P.Labels (J + F.ell))) ×ˢ (Set.univ.pi (fun g : P.BigGroup => {z : P.Memory (g : P.Group) | z.card ≤ bound g}))) := by
    intro s hs
    obtain ⟨c, hc⟩ := hs
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_pi, Set.mem_setOf_eq, true_and] at ⊢
    intro g _
    have hb := source_card_bound A i s t c hc g
    simp only [bound] at hb ⊢
    exact hb
  exact hprod.subset hsub

end Erdos821.P3Edge
