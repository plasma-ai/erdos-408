module

public import Erdos408.OneSided.Moment.Chain

/-!
# Prescribed births and row iteration

The bookkeeping of M10 at high rank (`exists_realized_history_le` in `Moment/Phased.lean`,
PD `mem:rank-absolute`).

* A *prescription* `π : Option ℕ` at a birth address asks that the birth there is `π`, or
  asks nothing (`π = none`). Its indicator is `presInd π o`, and its cost is the atom
  `atomCost c ν π`: `c ν(p)` for `π = some p`, and `1` for `none`.
* `sum_history_le_of_rows`: the chronological row iteration. For nonnegative ghost
  coefficients `G j` and edge coefficients `E j` whose weighted row sums are at most `R_G h`
  and `R_E h`, the history sum `∑_h ∏_j G_j ∏_j E_j f(end)` with `f ≤ h` is at most
  `R_G^{N+1} R_E^N h(s)`, with constants depending on the operation. Nothing is imposed at
  the end beyond `f ≤ h`.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

/-! ### Prescriptions -/

/-- The indicator `[o = π]` of a birth `o` against a prescription `π`; it is one when
nothing is prescribed (`π = none`). -/
def presInd (π o : Option ℕ) : ℝ := if π = none ∨ o = π then 1 else 0

/-- The cost of a prescription: the atom `c ν(p)` for a prescribed prime `p`, and `1` when
nothing is prescribed. -/
def atomCost (c : ℝ) (ν : ℕ → ℝ) (π : Option ℕ) : ℝ := π.elim 1 fun p => c * ν p

/-- The prescription indicator is nonnegative. -/
theorem presInd_nonneg (π o : Option ℕ) : 0 ≤ presInd π o := by
  unfold presInd
  split_ifs <;> norm_num

/-- The prescription indicator is at most one. -/
theorem presInd_le_one (π o : Option ℕ) : presInd π o ≤ 1 := by
  unfold presInd
  split_ifs <;> norm_num

/-- With nothing prescribed the indicator is one. -/
theorem presInd_none (o : Option ℕ) : presInd none o = 1 :=
  ite_eq_left (Or.inl rfl)

/-- With the prime `p` prescribed the indicator is `[o = p]`. -/
theorem presInd_some (p : ℕ) (o : Option ℕ) :
    presInd (some p) o = if o = some p then 1 else 0 := by
  unfold presInd
  simp

/-- The atom cost is nonnegative. -/
theorem atomCost_nonneg {c : ℝ} {ν : ℕ → ℝ} (hc : 0 ≤ c) (hν : ∀ p, 0 ≤ ν p) (π : Option ℕ) :
    0 ≤ atomCost c ν π := by
  cases π with
  | none => exact zero_le_one
  | some p => exact mul_nonneg hc (hν p)

/-- The atom cost is monotone in the constant. -/
theorem atomCost_mono {c c' : ℝ} {ν : ℕ → ℝ} (hcc : c ≤ c') (hν : ∀ p, 0 ≤ ν p)
    (π : Option ℕ) : atomCost c ν π ≤ atomCost c' ν π := by
  cases π with
  | none => exact le_rfl
  | some p => exact mul_le_mul_of_nonneg_right hcc (hν p)

/-! ### Row iteration over histories -/

section Rows

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
private theorem sum_histories_zero (F : History x d Y d₀ u v r 0 → ℝ) :
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
private theorem sum_histories_succ {N : ℕ} (F : History x d Y d₀ u v r (N + 1) → ℝ) :
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

/-- **The row iteration**: for nonnegative ghost coefficients `G j` and edge coefficients
`E j` whose weighted row sums against `h` are at most `a_j h` and `b_j h`, and for `f ≤ h`,
`∑_h ∏_j G_j(visit_j, h.1 j) ∏_j E_j(…, h.2 j) f(end(s, h)) ≤ ∏_j a_j ∏_j b_j h(s)`. -/
theorem sum_history_le_of_rows {h f : ChainState x d Y d₀ u v r B → ℝ} (hf : ∀ t, f t ≤ h t)
    (N : ℕ) :
    ∀ (G : Fin (N + 1) → ChainState x d Y d₀ u v r B → GhostChoice x d → ℝ)
      (E : Fin N → ChainState x d Y d₀ u v r B → EdgeChoice x d Y d₀ u v r → ℝ)
      (a : Fin (N + 1) → ℝ) (b : Fin N → ℝ),
      (∀ j t c, 0 ≤ G j t c) → (∀ j t e, 0 ≤ E j t e) → (∀ j, 0 ≤ a j) → (∀ j, 0 ≤ b j) →
      (∀ j t, ∑ c ∈ multBox B ×ˢ multBox B,
        G j t c * h (chainGhostOut x d Y d₀ u v r B t c) ≤ a j * h t) →
      (∀ j t, ∑ e ∈ edgeChoices x d Y d₀ u v r,
        E j t e * h (chainEdgeOut x d Y d₀ u v r B t e) ≤ b j * h t) →
      ∀ s : ChainState x d Y d₀ u v r B,
        ∑ hh ∈ histories x d Y d₀ u v r B N,
          (∏ j : Fin (N + 1), G j (chainVisit s hh j) (hh.1 j)) *
            (∏ j : Fin N, E j (chainGhostOut x d Y d₀ u v r B (chainVisit s hh j.castSucc)
              (hh.1 j.castSucc)) (hh.2 j)) *
            f (chainEnd s hh) ≤ (∏ j, a j) * (∏ j, b j) * h s := by
  induction N with
  | zero =>
    intro G E a b hG0 _ _ _ hG _ s
    rw [sum_histories_zero]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    -- one ghost choice, then `f ≤ h`
    calc ∑ c ∈ multBox B ×ˢ multBox B, G 0 s c * f (chainGhostOut x d Y d₀ u v r B s c)
        ≤ ∑ c ∈ multBox B ×ˢ multBox B, G 0 s c * h (chainGhostOut x d Y d₀ u v r B s c) :=
          sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hf _) (hG0 _ _ _)
      _ ≤ a 0 * h s := hG 0 s
  | succ N ih =>
    intro G E a b hG0 hE0 ha hb hG hE s
    rw [sum_histories_succ]
    have h0 : ∀ hh : History x d Y d₀ u v r N, ∀ c e,
        chainVisit (N := N + 1) s (Fin.cons c hh.1, Fin.cons e hh.2) 0 = s := fun _ _ _ => rfl
    simp only [Fin.prod_univ_succ (n := N + 1), Fin.prod_univ_succ (n := N),
      ← Fin.succ_castSucc, Fin.castSucc_zero, chainVisit_cons_succ, chainEnd_cons, Fin.cons_succ,
      Fin.cons_zero, h0]
    set P := (∏ j : Fin (N + 1), a j.succ) * ∏ j : Fin N, b j.succ with hP
    have hP0 : 0 ≤ P :=
      mul_nonneg (prod_nonneg fun j _ => ha _) (prod_nonneg fun j _ => hb _)
    -- peel off the first ghost and edge, and iterate on the tail from the state after them
    calc _
        = ∑ c ∈ multBox B ×ˢ multBox B, ∑ e ∈ edgeChoices x d Y d₀ u v r,
          G 0 s c * E 0 (chainGhostOut x d Y d₀ u v r B s c) e *
            ∑ hh ∈ histories x d Y d₀ u v r B N,
              (∏ j : Fin (N + 1), G j.succ (chainVisit (chainEdgeOut x d Y d₀ u v r B
                  (chainGhostOut x d Y d₀ u v r B s c) e) hh j) (hh.1 j)) *
                (∏ j : Fin N, E j.succ (chainGhostOut x d Y d₀ u v r B (chainVisit
                  (chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s c) e) hh
                    j.castSucc) (hh.1 j.castSucc)) (hh.2 j)) *
                f (chainEnd (chainEdgeOut x d Y d₀ u v r B
                  (chainGhostOut x d Y d₀ u v r B s c) e) hh) := by
          refine sum_congr rfl fun c _ => sum_congr rfl fun e _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun hh _ => ?_
          simp only [Fin.prod_univ_succ (n := N)]
          ring
      _ ≤ ∑ c ∈ multBox B ×ˢ multBox B, ∑ e ∈ edgeChoices x d Y d₀ u v r,
          G 0 s c * E 0 (chainGhostOut x d Y d₀ u v r B s c) e *
            (P * h (chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s c) e)) :=
          sum_le_sum fun c _ => sum_le_sum fun e _ =>
            mul_le_mul_of_nonneg_left
              (ih (fun j => G j.succ) (fun j => E j.succ) (fun j => a j.succ)
                (fun j => b j.succ) (fun j => hG0 j.succ) (fun j => hE0 j.succ)
                (fun j => ha j.succ) (fun j => hb j.succ) (fun j => hG j.succ)
                (fun j => hE j.succ) _)
              (mul_nonneg (hG0 _ _ _) (hE0 _ _ _))
      _ = P * ∑ c ∈ multBox B ×ˢ multBox B, G 0 s c *
            ∑ e ∈ edgeChoices x d Y d₀ u v r, E 0 (chainGhostOut x d Y d₀ u v r B s c) e *
              h (chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s c) e) := by
          rw [mul_sum]
          refine sum_congr rfl fun c _ => ?_
          rw [mul_sum, mul_sum]
          exact sum_congr rfl fun e _ => by ring
      _ ≤ P * ∑ c ∈ multBox B ×ˢ multBox B, G 0 s c *
            (b 0 * h (chainGhostOut x d Y d₀ u v r B s c)) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun c _ =>
            mul_le_mul_of_nonneg_left (hE 0 _) (hG0 _ _ _)) hP0
      _ = P * b 0 * ∑ c ∈ multBox B ×ˢ multBox B,
            G 0 s c * h (chainGhostOut x d Y d₀ u v r B s c) := by
          rw [mul_sum, mul_sum]
          exact sum_congr rfl fun c _ => by ring
      _ ≤ P * b 0 * (a 0 * h s) := mul_le_mul_of_nonneg_left (hG 0 s) (mul_nonneg hP0 (hb 0))
      _ = _ := by
          rw [hP]
          simp only [Fin.prod_univ_succ (n := N)]
          ring

end Rows

end Erdos408.OneSided
