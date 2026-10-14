import Erdos821.P3Edge.BoundedMem
import Erdos821.P3Edge.RowSummable

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

lemma card_le_of_valid (s t b c : ℕ) (M : ℕ) (hb : b ≤ M) (hc : c ≤ M)
    (h : t = s - b + c) : s ≤ t + M := by
  omega

lemma source_card_bound (A : Model F P J m) {n : ℕ} (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s)
    (h : edgeChoiceValid A .all i s t c) (g : P.BigGroup) :
    (s.2.2 g).card ≤ (t.2.2 g).card + (J + F.ell) := by
  have h2 : rawEdgeValid A (A.pattern c.2.2.1) (edgeForward i) c.2.2.2.1
      (permuteActive c.1 s) (permuteActive c.2.1 t) c.2.2.2.2 := by
    simpa [edgeChoiceValid] using h.1
  have hcard := rawEdgeValid_memory_card A (A.pattern c.2.2.1) (edgeForward i)
    c.2.2.2.1 (permuteActive c.1 s) (permuteActive c.2.1 t) c.2.2.2.2 h2 g
  -- hcard : (permute t).2.2 g card = (permute s).2.2 g card - ... + ...
  -- permute preserves memories definitionally
  have ht : ((permuteActive c.2.1 t).2.2 g).card = (t.2.2 g).card := rfl
  have hs : ((permuteActive c.1 s).2.2 g).card = (s.2.2 g).card := rfl
  rw [ht, hs] at hcard
  -- B, C cards ≤ J+ell
  have hb : (c.2.2.2.2.2.1 g).card ≤ J + F.ell := by
    calc (c.2.2.2.2.2.1 g).card ≤ Fintype.card (Fin (J + F.ell)) := Finset.card_le_univ _
      _ = J + F.ell := Fintype.card_fin _
  have hc : (c.2.2.2.2.1 g).card ≤ J + F.ell := by
    calc (c.2.2.2.2.1 g).card ≤ Fintype.card (Fin (J + F.ell)) := Finset.card_le_univ _
      _ = J + F.ell := Fintype.card_fin _
  -- hcard : tcard = scard - bcard + ccard
  exact card_le_of_valid _ _ _ _ _ hb hc hcard

end Erdos821.P3Edge
