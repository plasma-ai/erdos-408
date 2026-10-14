import Erdos821.P3Edge.RowSupport

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def mkTarget (A : Model F P J m) {n : ℕ} (i : Fin n)
    (s : P.MemoryState (J + F.ell)) :
    EdgeChoice A s × P.Labels (J + F.ell) → P.MemoryState (J + F.ell) :=
  fun p => (targetSmall A i s p.1, p.2, fun g => targetMem A i s p.1 g)

lemma mkTarget_eq (A : Model F P J m) {n : ℕ} (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s)
    (h : edgeChoiceValid A .all i s t c) :
    t = mkTarget A i s (c, t.2.1) := by
  have h1 : t.1 = targetSmall A i s c := valid_target_small A i s t c h
  have h3 : t.2.2 = fun g => targetMem A i s c g := by
    funext g
    exact valid_target_mem A i s t c h g
  simp only [mkTarget]
  apply Prod.ext
  · exact h1
  · apply Prod.ext
    · rfl
    · exact h3

lemma row_valid_set_finite (A : Model F P J m) {n : ℕ} (i : Fin n)
    (s : P.MemoryState (J + F.ell)) :
    Set.Finite {t : P.MemoryState (J + F.ell) | ∃ c : EdgeChoice A s, edgeChoiceValid A .all i s t c} := by
  classical
  have hsub : {t : P.MemoryState (J + F.ell) | ∃ c : EdgeChoice A s, edgeChoiceValid A .all i s t c} ⊆
      Set.image (mkTarget A i s) Set.univ := by
    intro t ht
    obtain ⟨c, hc⟩ := ht
    exact ⟨(c, t.2.1), Set.mem_univ _, (mkTarget_eq A i s t c hc).symm⟩
  exact (Set.finite_univ.image _).subset hsub

end Erdos821.P3Edge
