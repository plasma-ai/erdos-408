module

public import Erdos408.OneSided.Moment.Chain

/-!
# Distinct births as a running condition

S3 restricts the history sum to histories with pairwise distinct births (`distinctSum`,
`BirthsDistinct`). This file turns that global condition into a running one, so that the
history sum can be peeled one visit at a time.

* The performed births of a history form a multiset: the initial labels (`initBirths`), the
  primes of each ghost batch (`batchBirths`) and the fresh labels of each edge (`freshBirths`).
  When every batch fits into its `B` addresses, which holds on every history of nonzero
  weight, `BirthsDistinct` says exactly that this multiset has no duplicates
  (`birthsDistinct_iff_nodup`).
* `distinctFold n t s Bn` is the history sum of `𝒢_t ℰ 𝒢_{t+1} ⋯ ℰ 𝒢_{t+n}` from `s`, ending in
  `𝐛`, restricted to histories whose births are distinct and avoid the multiset `Bn` of
  primes born before. It satisfies the obvious one-step recursion by definition, and equals
  the restricted history sum (`distinctFold_eq_sum`). Hence
  `distinctSum = ∑_s μ(s) 𝐛(s) distinctFold N 0 s (initial labels of s)`
  (`distinctSum_eq_sum_distinctFold`).
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

section Births

variable (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

/-- The multiset of an optional birth. -/
def optBirth : Option ℕ → Multiset ℕ
  | none => 0
  | some p => {p}

/-- Births are distinct exactly when the multiset of performed births has no duplicates. -/
theorem birthsDistinct_iff_nodup {α : Type*} [Fintype α] (β : α → Option ℕ) :
    BirthsDistinct β ↔ (∑ a, optBirth (β a)).Nodup := by
  classical
  -- the multiplicity of `p` counts the addresses with birth `p`
  have hcount : ∀ p, Multiset.count p (∑ a, optBirth (β a)) = #{a | β a = some p} := by
    intro p
    rw [Multiset.count_sum', card_eq_sum_ones, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    cases h : β a with
    | none => simp [optBirth]
    | some p' =>
      by_cases hp : p' = p
      · simp [optBirth, hp]
      · simp [optBirth, hp, Ne.symm hp]
  rw [Multiset.nodup_iff_count_le_one]
  simp only [hcount, card_le_one, mem_filter, mem_univ, true_and, BirthsDistinct]
  exact ⟨fun h p a ha a' ha' => h a a' p ha ha', fun h a a' p ha ha' => h p a ha a' ha'⟩

variable {x d}

/-- The primes of a ghost batch, with multiplicity. -/
def batchBirths (n : Particle x d → ℕ) : Multiset ℕ :=
  ∑ xp : Particle x d, Multiset.replicate (n xp) xp.1.1

variable {Y d₀ u v r}

/-- The fresh labels of an edge choice. -/
def freshBirths (c : EdgeChoice x d Y d₀ u v r) : Multiset ℕ :=
  ∑ i, if (c.2.2.2.1 i).2 then 0 else {(c.2.2.2.1 i).1}

/-- The initial labels. -/
def initBirths {J : ℕ} (act : Lists K J) : Multiset ℕ := ∑ i, ∑ k, {act i k}

/-- The births of a history after its start: its ghost batches and its fresh labels. -/
def newBirths {N : ℕ} (h : History x d Y d₀ u v r N) : Multiset ℕ :=
  ∑ j, batchBirths (h.1 j).2 + ∑ j, freshBirths (h.2 j)

/-- The sorted batch lists the primes of the batch. -/
theorem coe_batchPrimes (n : Particle x d → ℕ) : (batchPrimes x d n : Multiset ℕ) = batchBirths n :=
  Multiset.sort_eq _ _

/-- The length of a batch is its total multiplicity. -/
theorem length_batchPrimes (n : Particle x d → ℕ) :
    (batchPrimes x d n).length = ∑ xp, n xp := by
  rw [← Multiset.coe_card, coe_batchPrimes, batchBirths, Multiset.card_sum]
  simp

/-- The first `B` entries of a list of length at most `B`, as optional births, give back the
list. -/
theorem sum_optBirth_getElem? (l : List ℕ) (hl : l.length ≤ B) :
    ∑ k : Fin B, optBirth l[k.1]? = (l : Multiset ℕ) := by
  induction l generalizing B with
  | nil => simp [optBirth]
  | cons a l ih =>
    obtain ⟨B, rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by simp at hl; omega⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getElem?_cons_zero, Fin.val_succ, List.getElem?_cons_succ]
    rw [ih B (by simpa using hl)]
    simp [optBirth]

/-- With every batch within its `B` addresses, `BirthsDistinct` is the absence of duplicates
among the initial labels and the new births. -/
theorem birthsDistinct_iff {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    (h : History x d Y d₀ u v r N) (hb : ∀ j, (batchPrimes x d (h.1 j).2).length ≤ B) :
    BirthsDistinct (births s h) ↔ (initBirths s.2.1.1 + newBirths h).Nodup := by
  rw [birthsDistinct_iff_nodup]
  -- the three kinds of addresses
  have hsum : ∑ a, optBirth (births s h a) = initBirths s.2.1.1 + newBirths h := by
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, births, newBirths, initBirths,
      freshBirths]
    congr 1
    rw [add_comm]
    congr 1
    · exact sum_congr rfl fun j _ => by
        rw [sum_optBirth_getElem? B _ (hb j), coe_batchPrimes]
    · refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
      split_ifs <;> rfl
  rw [hsum]

/-- On a history of nonzero weight every ghost choice is valid, so every batch fits into its
`B` addresses. -/
theorem length_batchPrimes_le {N : ℕ} {s : ChainState x d Y d₀ u v r B}
    {h : History x d Y d₀ u v r N} (hw : chainWeight q A₀ s h ≠ 0) (j : Fin (N + 1)) :
    (batchPrimes x d (h.1 j).2).length ≤ B := by
  classical
  have hg : chainGhostCoef q x d Y d₀ u v r B N j (chainVisit s h j) (h.1 j) ≠ 0 :=
    fun h0 => hw (by rw [chainWeight, prod_eq_zero (mem_univ j) h0, zero_mul])
  have hv : GhostValid (HitsAt x d (chainVisit s h j).1.1) B (chainVisit s h j).2.2.1 (h.1 j) := by
    by_contra hv
    exact hg (by rw [chainGhostCoef, ghostCoef, ite_eq_right hv])
  rw [length_batchPrimes]
  refine le_trans (sum_le_sum fun xp _ => ?_) hv.2.2
  exact Nat.le_add_left _ _

/-! ### The running form -/

variable (Y d₀ u v r) in
open scoped Classical in
/-- The history sum of `𝒢_t ℰ ⋯ ℰ 𝒢_{t+n}` from `s`, ending in `𝐛`, over the histories whose
births are distinct and avoid the earlier births `Bn`. -/
def distinctFold (N : ℕ) : ℕ → ℕ → ChainState x d Y d₀ u v r B → Multiset ℕ → ℂ
  | 0, t, s, Bn => ∑ g ∈ multBox B ×ˢ multBox B,
      chainGhostCoef q x d Y d₀ u v r B N t s g * (if (Bn + batchBirths g.2).Nodup then 1 else 0) *
        chainInit x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s g)
  | n + 1, t, s, Bn => ∑ g ∈ multBox B ×ˢ multBox B, ∑ c ∈ edgeChoices x d Y d₀ u v r,
      chainGhostCoef q x d Y d₀ u v r B N t s g *
        chainEdgeCoef q A₀ x d Y d₀ u v r B N (chainGhostOut x d Y d₀ u v r B s g) c *
        (if (Bn + batchBirths g.2 + freshBirths c).Nodup then 1 else 0) *
        distinctFold N n (t + 1)
          (chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s g) c)
          (Bn + batchBirths g.2 + freshBirths c)

/-- The weight of a history with the ghost indices shifted by `t`. -/
def offsetWeight (M t : ℕ) {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    (h : History x d Y d₀ u v r N) : ℂ :=
  (∏ j : Fin (N + 1), chainGhostCoef q x d Y d₀ u v r B M (j + t) (chainVisit s h j) (h.1 j)) *
    ∏ j : Fin N, chainEdgeCoef q A₀ x d Y d₀ u v r B M
      (chainGhostOut x d Y d₀ u v r B (chainVisit s h j.castSucc) (h.1 j.castSucc)) (h.2 j)

/-- The visits of a history after its first edge are the visits of its tail. -/
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

/-- The end of a history is the end of its tail. -/
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

open scoped Classical in
/-- `distinctFold` is the history sum restricted to births that are distinct and avoid `Bn`. -/
theorem distinctFold_eq_sum (N : ℕ) :
    ∀ (n t : ℕ) (s : ChainState x d Y d₀ u v r B) (Bn : Multiset ℕ),
      distinctFold q A₀ Y d₀ u v r B N n t s Bn =
        ∑ h ∈ histories x d Y d₀ u v r B n, offsetWeight q A₀ B N t s h *
          (if (Bn + newBirths h).Nodup then 1 else 0) *
          chainInit x d Y d₀ u v r B (chainEnd s h) := by
  intro n
  induction n with
  | zero =>
    intro t s Bn
    rw [sum_histories_zero]
    simp only [distinctFold, offsetWeight, newBirths, Fin.prod_univ_succ, Fin.prod_univ_zero,
      mul_one, Fin.val_zero, zero_add, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  | succ n ih =>
    intro t s Bn
    rw [sum_histories_succ]
    simp only [distinctFold, ih, mul_sum]
    refine sum_congr rfl fun c _ => sum_congr rfl fun e _ => sum_congr rfl fun h _ => ?_
    -- the first visit and edge, and the births of the tail
    have h0 : chainVisit (N := n + 1) s (Fin.cons c h.1, Fin.cons e h.2) 0 = s := rfl
    have hw : offsetWeight q A₀ B N t s (N := n + 1) (Fin.cons c h.1, Fin.cons e h.2) =
        chainGhostCoef q x d Y d₀ u v r B N t s c *
          chainEdgeCoef q A₀ x d Y d₀ u v r B N (chainGhostOut x d Y d₀ u v r B s c) e *
          offsetWeight q A₀ B N (t + 1)
            (chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s c) e) h := by
      simp only [offsetWeight, Fin.prod_univ_succ (n := n + 1), Fin.prod_univ_succ (n := n),
        chainVisit_cons_succ, Fin.cons_succ, Fin.cons_zero, Fin.val_succ, Fin.val_zero,
        ← Fin.succ_castSucc, Fin.castSucc_zero, h0, zero_add]
      simp only [add_assoc, add_comm 1 t]
      ring
    have hb : newBirths (N := n + 1) (Fin.cons c h.1, Fin.cons e h.2) =
        batchBirths c.2 + freshBirths e + newBirths h := by
      simp only [newBirths, Fin.sum_univ_succ (n := n + 1), Fin.sum_univ_succ (n := n),
        Fin.cons_zero, Fin.cons_succ]
      abel
    rw [hw, hb, chainEnd_cons, ← add_assoc Bn, ← add_assoc Bn]
    -- the running condition is implied by the final one
    by_cases hnd : (Bn + batchBirths c.2 + freshBirths e + newBirths h).Nodup
    · rw [ite_eq_left hnd, ite_eq_left (Multiset.nodup_add.1 hnd).1]
      ring
    · rw [ite_eq_right hnd]
      split_ifs <;> ring

open scoped Classical in
/-- The distinct-birth history sum through the running form. -/
theorem distinctSum_eq_sum_distinctFold (N : ℕ) :
    distinctSum q A₀ x d Y d₀ u v r B N =
      ∑ s, (chainMeasure q x d Y d₀ u v r B N s : ℂ) * chainInit x d Y d₀ u v r B s *
        distinctFold q A₀ Y d₀ u v r B N N 0 s (initBirths s.2.1.1) := by
  rw [distinctSum]
  refine sum_congr rfl fun s _ => ?_
  rw [distinctFold_eq_sum, sum_filter]
  congr 1
  refine sum_congr rfl fun h _ => ?_
  have hw : offsetWeight q A₀ B N 0 s h = chainWeight q A₀ s h := by
    simp [offsetWeight, chainWeight]
  rw [hw]
  by_cases h0 : chainWeight q A₀ s h = 0
  · simp [h0]
  · rw [birthsDistinct_iff B s h (length_batchPrimes_le q A₀ B h0)]
    split_ifs <;> simp

end Births

end Erdos408.OneSided
