import Erdos408.OneSided.Moment.Chain

/-!
# The history expansion with visit-dependent coefficients

The phased operators of `Moment/Phased.lean` carry at each visit and each edge the phases of
their own addresses, so their coefficients depend on the position in the product. This file
expands such products into histories.

* `foldr_finRange_eq_sum_history`: for ghost coefficients `G j` at each visit `j` and edge
  coefficients `E j` at each edge `j`, the product `𝒢^{G₀} ℰ^{E₀} 𝒢^{G₁} ⋯ ℰ^{E_{N-1}} 𝒢^{G_N}`
  applied to `f` at `s` is `∑_h ∏_j G_j(visit_j, h.1 j) ∏_j E_j(…, h.2 j) f(end(s, h))`.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

section History

variable {x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B : ℕ}

/-- The visits of a history after its first edge are the visits of its tail from the state
after that edge. -/
private theorem chainVisit_cons_succ {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    (c : GhostChoice x d) (e : EdgeChoice x d Y d₀ u v r) (h : History x d Y d₀ u v r N)
    (j : Fin (N + 1)) :
    chainVisit (N := N + 1) s (Fin.cons c h.1, Fin.cons e h.2) j.succ =
      chainVisit (chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s c) e) h j := by
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
    simp only [chainVisit] at ih ⊢
    rw [Fin.induction_succ, Fin.induction_succ, ← Fin.succ_castSucc, ih]
    simp

/-- The end of a history is the end of its tail from the state after its first edge. -/
private theorem chainEnd_cons {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    (c : GhostChoice x d) (e : EdgeChoice x d Y d₀ u v r) (h : History x d Y d₀ u v r N) :
    chainEnd (N := N + 1) s (Fin.cons c h.1, Fin.cons e h.2) =
      chainEnd (chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s c) e) h := by
  rw [chainEnd, ← Fin.succ_last, chainVisit_cons_succ]
  rfl

/-- A history with no edges is a single ghost choice. -/
private theorem sum_histories_zero (F : History x d Y d₀ u v r 0 → ℂ) :
    ∑ h ∈ histories x d Y d₀ u v r B 0, F h =
      ∑ c ∈ multBox B ×ˢ multBox B, F (fun _ => c, Fin.elim0) := by
  refine sum_nbij' (fun h => h.1 0) (fun c => (fun _ => c, Fin.elim0)) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    simp only [histories, mem_product, Fintype.mem_piFinset] at hh ⊢
    exact hh.1 0
  · intro c hc
    simp only [histories, mem_product, Fintype.mem_piFinset] at hc ⊢
    exact ⟨fun _ => hc, fun i => i.elim0⟩
  · intro h _
    exact Prod.ext (funext fun k => by rw [Fin.fin_one_eq_zero k]) (Subsingleton.elim _ _)
  · intro c _
    rfl
  · intro h _
    congr 1
    exact Prod.ext (funext fun k => by rw [Fin.fin_one_eq_zero k]) (Subsingleton.elim _ _)

/-- A history with `N + 1` edges is a first ghost choice, a first edge choice, and a history
with `N` edges. -/
private theorem sum_histories_succ {N : ℕ} (F : History x d Y d₀ u v r (N + 1) → ℂ) :
    ∑ h ∈ histories x d Y d₀ u v r B (N + 1), F h =
      ∑ c ∈ multBox B ×ˢ multBox B, ∑ e ∈ edgeChoices x d Y d₀ u v r,
        ∑ h ∈ histories x d Y d₀ u v r B N, F (Fin.cons c h.1, Fin.cons e h.2) := by
  simp only [← sum_product']
  refine sum_nbij' (fun h => (h.1 0, h.2 0, Fin.tail h.1, Fin.tail h.2))
    (fun t => (Fin.cons t.1 t.2.2.1, Fin.cons t.2.1 t.2.2.2)) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    simp only [histories, mem_product, Fintype.mem_piFinset] at hh ⊢
    exact ⟨hh.1 0, hh.2 0, fun i => hh.1 _, fun i => hh.2 _⟩
  · intro t ht
    simp only [histories, mem_product, Fintype.mem_piFinset] at ht ⊢
    exact ⟨fun i => Fin.cases ht.1 ht.2.2.1 i, fun i => Fin.cases ht.2.1 ht.2.2.2 i⟩
  · intro h _
    simp
  · intro t _
    simp
  · intro h _
    simp

/-- The history expansion with visit-dependent coefficients: with ghost coefficients `G j` at
the visits and edge coefficients `E j` at the edges, `𝒢^{G₀} ℰ^{E₀} ⋯ ℰ^{E_{N-1}} 𝒢^{G_N} f (s)`
is `∑_h ∏_j G_j(visit_j(s, h), h.1 j) ∏_j E_j(…, h.2 j) f(end(s, h))`. -/
theorem foldr_finRange_eq_sum_history (f : ChainState x d Y d₀ u v r B → ℂ) (N : ℕ) :
    ∀ (G : Fin (N + 1) → ChainState x d Y d₀ u v r B → GhostChoice x d → ℂ)
      (E : Fin N → ChainState x d Y d₀ u v r B → EdgeChoice x d Y d₀ u v r → ℂ)
      (s : ChainState x d Y d₀ u v r B),
      (List.finRange N).foldr
          (fun j g => choiceOp (multBox B ×ˢ multBox B) (G j.castSucc)
            (chainGhostOut x d Y d₀ u v r B)
            (choiceOp (edgeChoices x d Y d₀ u v r) (E j) (chainEdgeOut x d Y d₀ u v r B) g))
          (choiceOp (multBox B ×ˢ multBox B) (G (Fin.last N)) (chainGhostOut x d Y d₀ u v r B)
            f) s =
        ∑ h ∈ histories x d Y d₀ u v r B N,
          (∏ j : Fin (N + 1), G j (chainVisit s h j) (h.1 j)) *
            (∏ j : Fin N,
              E j (chainGhostOut x d Y d₀ u v r B (chainVisit s h j.castSucc) (h.1 j.castSucc))
                (h.2 j)) *
            f (chainEnd s h) := by
  induction N with
  | zero =>
    intro G E s
    rw [sum_histories_zero]
    simp only [List.finRange_zero, List.foldr_nil, choiceOp, Fin.prod_univ_succ,
      Fin.prod_univ_zero, mul_one]
    rfl
  | succ N ih =>
    intro G E s
    -- peel off `𝒢^{G₀} ℰ^{E₀}` and expand the rest from the state after the first edge
    rw [List.finRange_succ, List.foldr_cons, List.foldr_map, sum_histories_succ]
    simp only [← Fin.succ_castSucc, ← Fin.succ_last, Fin.castSucc_zero]
    rw [funext (ih (fun j => G j.succ) (fun j => E j.succ))]
    have h0 : ∀ h : History x d Y d₀ u v r N, ∀ c e,
        chainVisit (N := N + 1) s (Fin.cons c h.1, Fin.cons e h.2) 0 = s := fun _ _ _ => rfl
    simp only [choiceOp, Fin.prod_univ_succ (n := N + 1), Fin.prod_univ_succ (n := N),
      ← Fin.succ_castSucc, Fin.castSucc_zero, chainVisit_cons_succ, chainEnd_cons, Fin.cons_succ,
      Fin.cons_zero, h0, mul_sum]
    exact sum_congr rfl fun c _ => sum_congr rfl fun e _ => sum_congr rfl fun h _ => by ring

end History

end Erdos408.OneSided
