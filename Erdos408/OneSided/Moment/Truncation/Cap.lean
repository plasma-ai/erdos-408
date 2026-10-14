import Erdos408.OneSided.Moment.Chain

/-!
# Changing the memory cap

The first step of M3 (`eventually_distinctSum_truncation` in `Moment/Memory.lean`, PD
`mem:truncation-error`): for caps `B ≤ B'`, the distinct-birth history sums differ by the
histories of the cap-`B'` chain that leave the memories of size at most `B`.

* `capEmbed`: a chain state with cap `B` is a state with cap `B'` whose memory has size at
  most `B`.
* `StaysBelow B s h`: every visit of the history `h` from `s`, and every state after one of
  its ghosts, has memory size at most `B`.
* `chainVisit_capEmbed_of_staysBelow`, `chainWeight_capEmbed_of_staysBelow`: along a history
  that stays below `B`, the two chains pass through the same states with the same
  coefficients. `staysBelow_capEmbed_of_ne_zero`: a history of nonzero weight in the cap-`B`
  chain stays below `B` in the cap-`B'` chain.
* `distinctSum_sub_eq`: `distinctSum(B') - distinctSum(B)` is the sum over the distinct-birth
  histories of the cap-`B'` chain that do not stay below `B`.
* `lt_of_not_staysBelow`: such a history from an empty memory has `B < K N + ∑_j |batch_j|`,
  since an edge stores at most `K` particles and a ghost adds its batch.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

section Cap

variable {q A₀ x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B B' : ℕ}

/-! ### Visits -/

/-- The first visit of a history is its start. -/
theorem chainVisit_zero {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    (h : History x d Y d₀ u v r N) : chainVisit s h 0 = s :=
  rfl

/-- The visit after an edge is the edge output of the state after the preceding ghost. -/
theorem chainVisit_succ {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    (h : History x d Y d₀ u v r N) (j : Fin N) :
    chainVisit s h j.succ = chainEdgeOut x d Y d₀ u v r B
      (chainGhostOut x d Y d₀ u v r B (chainVisit s h j.castSucc) (h.1 j.castSucc)) (h.2 j) := by
  simp only [chainVisit, Fin.induction_succ]

/-! ### The embedding -/

/-- The embedding of the chain states with cap `B` into those with cap `B' ≥ B`. -/
def capEmbed (hB : B ≤ B') (s : ChainState x d Y d₀ u v r B) : ChainState x d Y d₀ u v r B' :=
  (s.1, s.2.1, ⟨s.2.2.1, mem_memStates.2 ((mem_memStates.1 s.2.2.2).trans hB)⟩)

/-- The embedding is injective. -/
theorem capEmbed_injective (hB : B ≤ B') :
    Function.Injective (capEmbed (x := x) (d := d) (Y := Y) (d₀ := d₀) (u := u) (v := v)
      (r := r) hB) := by
  rintro ⟨z, l, S⟩ ⟨z', l', S'⟩ h
  simp only [capEmbed, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, h⟩ := h
  have hS : S = S' := Subtype.ext (Subtype.mk.inj h)
  rw [hS]

/-- A state with memory size at most `B` is embedded. -/
theorem mem_range_capEmbed (hB : B ≤ B') {s : ChainState x d Y d₀ u v r B'}
    (hs : memSize s.2.2.1 ≤ B) : s ∈ Set.range (capEmbed hB) :=
  ⟨(s.1, s.2.1, ⟨s.2.2.1, mem_memStates.2 hs⟩), rfl⟩

/-- An embedded state has memory size at most `B`. -/
theorem memSize_capEmbed_le (hB : B ≤ B') (s : ChainState x d Y d₀ u v r B) :
    memSize (capEmbed hB s).2.2.1 ≤ B :=
  mem_memStates.1 s.2.2.2

/-! ### One ghost step -/

/-- A ghost choice valid for the cap `B` is valid for every larger cap. -/
theorem GhostValid.mono {X : Type*} [Fintype X] [DecidableEq X] {hit : X → Prop}
    [DecidablePred hit] {S : X → ℕ} {c : (X → ℕ) × (X → ℕ)} (h : GhostValid hit B S c)
    (hB : B ≤ B') : GhostValid hit B' S c :=
  ⟨h.1, h.2.1, h.2.2.trans hB⟩

/-- A valid ghost choice creates a batch of size at most the cap. -/
theorem GhostValid.memSize_le {X : Type*} [Fintype X] [DecidableEq X] {hit : X → Prop}
    [DecidablePred hit] {S : X → ℕ} {c : (X → ℕ) × (X → ℕ)} (h : GhostValid hit B S c) :
    memSize c.2 ≤ B :=
  le_trans (sum_le_sum fun x _ => by omega) h.2.2

/-- The memory of a valid ghost output. -/
theorem ghostOut_val_of_valid {X : Type*} [Fintype X] [DecidableEq X] {hit : X → Prop}
    [DecidablePred hit] {S : MemState X B} {c : (X → ℕ) × (X → ℕ)}
    (h : GhostValid hit B S.1 c) : (ghostOut hit B S c).1 = fun x => S.1 x - c.1 x + c.2 x := by
  rw [ghostOut, dite_eq_left h]

/-- An invalid ghost choice leaves the memory unchanged. -/
theorem ghostOut_val_of_not {X : Type*} [Fintype X] [DecidableEq X] {hit : X → Prop}
    [DecidablePred hit] {S : MemState X B} {c : (X → ℕ) × (X → ℕ)}
    (h : ¬ GhostValid hit B S.1 c) : (ghostOut hit B S c).1 = S.1 := by
  rw [ghostOut, dite_eq_right h]

/-- A ghost choice of nonzero coefficient is valid. -/
theorem ghostValid_of_chainGhostCoef_ne_zero {N j : ℕ} {t : ChainState x d Y d₀ u v r B}
    {c : GhostChoice x d} (hc : chainGhostCoef q x d Y d₀ u v r B N j t c ≠ 0) :
    GhostValid (HitsAt x d t.1.1) B t.2.2.1 c := by
  by_contra hv
  exact hc (by rw [chainGhostCoef, ghostCoef, ite_eq_right hv])

/-- For a ghost choice valid for the cap `B'` exactly when it is valid for the cap `B`, the
cap-`B'` ghost output of the embedded state is the embedded cap-`B` output. -/
private theorem chainGhostOut_capEmbed_of_iff (hB : B ≤ B') (t : ChainState x d Y d₀ u v r B)
    (c : GhostChoice x d)
    (hiff : GhostValid (HitsAt x d t.1.1) B' t.2.2.1 c ↔
      GhostValid (HitsAt x d t.1.1) B t.2.2.1 c) :
    chainGhostOut x d Y d₀ u v r B' (capEmbed hB t) c =
      capEmbed hB (chainGhostOut x d Y d₀ u v r B t c) := by
  refine Prod.ext rfl (Prod.ext rfl (Subtype.ext ?_))
  change (ghostOut (HitsAt x d t.1.1) B' (capEmbed hB t).2.2 c).1 =
    (ghostOut (HitsAt x d t.1.1) B t.2.2 c).1
  by_cases hv : GhostValid (HitsAt x d t.1.1) B' t.2.2.1 c
  · rw [ghostOut_val_of_valid (S := (capEmbed hB t).2.2) hv,
      ghostOut_val_of_valid (S := t.2.2) (hiff.1 hv)]
    rfl
  · rw [ghostOut_val_of_not (S := (capEmbed hB t).2.2) hv,
      ghostOut_val_of_not (S := t.2.2) (fun h => hv (hiff.2 h))]
    rfl

/-- For a ghost choice valid for the cap `B'` exactly when it is valid for the cap `B`, the two
coefficients agree. -/
private theorem chainGhostCoef_capEmbed_of_iff (hB : B ≤ B') (t : ChainState x d Y d₀ u v r B)
    (c : GhostChoice x d)
    (hiff : GhostValid (HitsAt x d t.1.1) B' t.2.2.1 c ↔ GhostValid (HitsAt x d t.1.1) B t.2.2.1 c)
    (N j : ℕ) :
    chainGhostCoef q x d Y d₀ u v r B' N j (capEmbed hB t) c =
      chainGhostCoef q x d Y d₀ u v r B N j t c := by
  by_cases hv : GhostValid (HitsAt x d t.1.1) B' t.2.2.1 c
  · rw [chainGhostCoef, chainGhostCoef, ghostCoef, ghostCoef,
      ite_eq_left (show GhostValid (HitsAt x d (capEmbed hB t).1.1) B' (capEmbed hB t).2.2.1 c
        from hv), ite_eq_left (hiff.1 hv)]
    rfl
  · rw [chainGhostCoef, chainGhostCoef, ghostCoef, ghostCoef,
      ite_eq_right (show ¬ GhostValid (HitsAt x d (capEmbed hB t).1.1) B'
        (capEmbed hB t).2.2.1 c from hv), ite_eq_right (fun h => hv (hiff.2 h))]

/-- If the cap-`B'` ghost output of the embedded state has memory size at most `B`, the
choice is valid for the cap `B'` exactly when it is valid for the cap `B`. -/
private theorem ghostValid_iff_of_le (hB : B ≤ B') (t : ChainState x d Y d₀ u v r B)
    (c : GhostChoice x d)
    (hc : memSize (chainGhostOut x d Y d₀ u v r B' (capEmbed hB t) c).2.2.1 ≤ B) :
    GhostValid (HitsAt x d t.1.1) B' t.2.2.1 c ↔ GhostValid (HitsAt x d t.1.1) B t.2.2.1 c := by
  refine ⟨fun hv => ⟨hv.1, hv.2.1, ?_⟩, fun hv => hv.mono hB⟩
  have h := hc
  change memSize (ghostOut (HitsAt x d t.1.1) B' (capEmbed hB t).2.2 c).1 ≤ B at h
  rw [ghostOut_val_of_valid (S := (capEmbed hB t).2.2) hv] at h
  exact h

/-- **The ghost step under the embedding**: if the ghost output of the cap-`B'` chain has
memory size at most `B`, it is the embedded output of the cap-`B` chain. -/
theorem chainGhostOut_capEmbed (hB : B ≤ B') (t : ChainState x d Y d₀ u v r B)
    (c : GhostChoice x d)
    (hc : memSize (chainGhostOut x d Y d₀ u v r B' (capEmbed hB t) c).2.2.1 ≤ B) :
    chainGhostOut x d Y d₀ u v r B' (capEmbed hB t) c =
      capEmbed hB (chainGhostOut x d Y d₀ u v r B t c) :=
  chainGhostOut_capEmbed_of_iff hB t c (ghostValid_iff_of_le hB t c hc)

/-- If the ghost output of the cap-`B'` chain has memory size at most `B`, the two ghost
coefficients agree. -/
theorem chainGhostCoef_capEmbed (hB : B ≤ B') (t : ChainState x d Y d₀ u v r B)
    (c : GhostChoice x d)
    (hc : memSize (chainGhostOut x d Y d₀ u v r B' (capEmbed hB t) c).2.2.1 ≤ B) (N j : ℕ) :
    chainGhostCoef q x d Y d₀ u v r B' N j (capEmbed hB t) c =
      chainGhostCoef q x d Y d₀ u v r B N j t c :=
  chainGhostCoef_capEmbed_of_iff hB t c (ghostValid_iff_of_le hB t c hc) N j

/-- A ghost choice of nonzero coefficient in the cap-`B` chain has an output of memory size at
most `B` in the cap-`B'` chain. -/
theorem memSize_chainGhostOut_capEmbed_le (hB : B ≤ B') {N j : ℕ}
    {t : ChainState x d Y d₀ u v r B} {c : GhostChoice x d}
    (hc : chainGhostCoef q x d Y d₀ u v r B N j t c ≠ 0) :
    memSize (chainGhostOut x d Y d₀ u v r B' (capEmbed hB t) c).2.2.1 ≤ B := by
  have hv := ghostValid_of_chainGhostCoef_ne_zero hc
  rw [chainGhostOut_capEmbed_of_iff hB t c ⟨fun _ => hv, fun h => h.mono hB⟩]
  exact memSize_capEmbed_le hB _

/-! ### One edge step -/

/-- An edge choice admissible for the cap `B` is admissible for the embedded state. -/
theorem edgeValid_capEmbed (hB : B ≤ B') {t : ChainState x d Y d₀ u v r B}
    {c : EdgeChoice x d Y d₀ u v r} (h : EdgeValid x d Y d₀ u v r B t c) :
    EdgeValid x d Y d₀ u v r B' (capEmbed hB t) c :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    mem_memStates.2 ((mem_memStates.1 h.2.2.2.2.2.2.2.2.2).trans hB)⟩

/-- An edge choice admissible for the embedded state, with a new memory of size at most `B`,
is admissible for the cap `B`. -/
theorem edgeValid_of_capEmbed (hB : B ≤ B') {t : ChainState x d Y d₀ u v r B}
    {c : EdgeChoice x d Y d₀ u v r} (h : EdgeValid x d Y d₀ u v r B' (capEmbed hB t) c)
    (hm : memSize (edgeMem t c) ≤ B) : EdgeValid x d Y d₀ u v r B t c :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, mem_memStates.2 hm⟩

/-- If the edge output of the cap-`B'` chain has memory size at most `B`, the choice is
admissible for the cap `B'` exactly when it is admissible for the cap `B`. -/
private theorem edgeValid_iff_of_le (hB : B ≤ B') (t : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r)
    (hc : memSize (chainEdgeOut x d Y d₀ u v r B' (capEmbed hB t) c).2.2.1 ≤ B) :
    EdgeValid x d Y d₀ u v r B' (capEmbed hB t) c ↔ EdgeValid x d Y d₀ u v r B t c := by
  refine ⟨fun hv => edgeValid_of_capEmbed hB hv ?_, edgeValid_capEmbed hB⟩
  have h := hc
  rw [chainEdgeOut, dite_eq_left hv] at h
  exact h

/-- For an edge choice admissible for the embedded state exactly when it is admissible for
the cap `B`, the outputs correspond and the coefficients agree. -/
private theorem chainEdge_capEmbed_of_iff (hB : B ≤ B') (t : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r)
    (hiff : EdgeValid x d Y d₀ u v r B' (capEmbed hB t) c ↔ EdgeValid x d Y d₀ u v r B t c) :
    chainEdgeOut x d Y d₀ u v r B' (capEmbed hB t) c =
        capEmbed hB (chainEdgeOut x d Y d₀ u v r B t c) ∧
      ∀ N, chainEdgeCoef q A₀ x d Y d₀ u v r B' N (capEmbed hB t) c =
        chainEdgeCoef q A₀ x d Y d₀ u v r B N t c := by
  by_cases hv : EdgeValid x d Y d₀ u v r B' (capEmbed hB t) c
  · refine ⟨?_, fun N => ?_⟩
    · rw [chainEdgeOut, chainEdgeOut, dite_eq_left hv, dite_eq_left (hiff.1 hv)]
      rfl
    · rw [chainEdgeCoef, chainEdgeCoef, ite_eq_left hv, ite_eq_left (hiff.1 hv)]
      rfl
  · refine ⟨?_, fun N => ?_⟩
    · rw [chainEdgeOut, chainEdgeOut, dite_eq_right hv, dite_eq_right (fun h => hv (hiff.2 h))]
    · rw [chainEdgeCoef, chainEdgeCoef, ite_eq_right hv, ite_eq_right (fun h => hv (hiff.2 h))]

/-- **The edge step under the embedding**: if the edge output of the cap-`B'` chain has
memory size at most `B`, it is the embedded output of the cap-`B` chain. -/
theorem chainEdgeOut_capEmbed (hB : B ≤ B') (t : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r)
    (hc : memSize (chainEdgeOut x d Y d₀ u v r B' (capEmbed hB t) c).2.2.1 ≤ B) :
    chainEdgeOut x d Y d₀ u v r B' (capEmbed hB t) c =
      capEmbed hB (chainEdgeOut x d Y d₀ u v r B t c) :=
  (chainEdge_capEmbed_of_iff (q := 0) (A₀ := 0) hB t c (edgeValid_iff_of_le hB t c hc)).1

/-- If the edge output of the cap-`B'` chain has memory size at most `B`, the two edge
coefficients agree. -/
theorem chainEdgeCoef_capEmbed (hB : B ≤ B') (t : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r)
    (hc : memSize (chainEdgeOut x d Y d₀ u v r B' (capEmbed hB t) c).2.2.1 ≤ B) (N : ℕ) :
    chainEdgeCoef q A₀ x d Y d₀ u v r B' N (capEmbed hB t) c =
      chainEdgeCoef q A₀ x d Y d₀ u v r B N t c :=
  (chainEdge_capEmbed_of_iff hB t c (edgeValid_iff_of_le hB t c hc)).2 N

/-- An edge choice of nonzero coefficient in the cap-`B` chain has an output of memory size at
most `B` in the cap-`B'` chain. -/
theorem memSize_chainEdgeOut_capEmbed_le (hB : B ≤ B') {N : ℕ}
    {t : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : chainEdgeCoef q A₀ x d Y d₀ u v r B N t c ≠ 0) :
    memSize (chainEdgeOut x d Y d₀ u v r B' (capEmbed hB t) c).2.2.1 ≤ B := by
  have hv : EdgeValid x d Y d₀ u v r B t c := by
    by_contra hv
    exact hc (by rw [chainEdgeCoef, ite_eq_right hv])
  rw [(chainEdge_capEmbed_of_iff (q := q) (A₀ := A₀) hB t c
    ⟨fun _ => hv, edgeValid_capEmbed hB⟩).1]
  exact memSize_capEmbed_le hB _

/-! ### Histories -/

variable (B) in
/-- The history `h` from `s` **stays below `B`**: every visit, and every state after a ghost,
has memory size at most `B`. -/
def StaysBelow {N : ℕ} (s : ChainState x d Y d₀ u v r B') (h : History x d Y d₀ u v r N) :
    Prop :=
  ∀ j, memSize (chainVisit s h j).2.2.1 ≤ B ∧
    memSize (chainGhostOut x d Y d₀ u v r B' (chainVisit s h j) (h.1 j)).2.2.1 ≤ B

/-- Along a history that stays below `B`, the cap-`B'` chain visits the embedded states of the
cap-`B` chain. -/
theorem chainVisit_capEmbed_of_staysBelow (hB : B ≤ B') {N : ℕ}
    {s : ChainState x d Y d₀ u v r B} {h : History x d Y d₀ u v r N}
    (hs : StaysBelow B (capEmbed hB s) h) (j : Fin (N + 1)) :
    chainVisit (capEmbed hB s) h j = capEmbed hB (chainVisit s h j) := by
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
    have hg := chainGhostOut_capEmbed hB (chainVisit s h j.castSucc) (h.1 j.castSucc)
      (by have := (hs j.castSucc).2; rwa [ih] at this)
    have he := chainEdgeOut_capEmbed hB
      (chainGhostOut x d Y d₀ u v r B (chainVisit s h j.castSucc) (h.1 j.castSucc)) (h.2 j)
      (by have := (hs j.succ).1; rwa [chainVisit_succ, ih, hg] at this)
    rw [chainVisit_succ, chainVisit_succ, ih, hg, he]

/-- Along a history that stays below `B`, the two chains have the same weight and embedded
ends. -/
theorem chainWeight_capEmbed_of_staysBelow (hB : B ≤ B') {N : ℕ}
    {s : ChainState x d Y d₀ u v r B} {h : History x d Y d₀ u v r N}
    (hs : StaysBelow B (capEmbed hB s) h) :
    chainWeight q A₀ (capEmbed hB s) h = chainWeight q A₀ s h ∧
      chainEnd (capEmbed hB s) h = capEmbed hB (chainEnd s h) := by
  have hv := chainVisit_capEmbed_of_staysBelow hB hs
  have hc : ∀ j, memSize (chainGhostOut x d Y d₀ u v r B' (capEmbed hB (chainVisit s h j))
      (h.1 j)).2.2.1 ≤ B := fun j => by have := (hs j).2; rwa [hv j] at this
  have hg : ∀ j, chainGhostOut x d Y d₀ u v r B' (chainVisit (capEmbed hB s) h j) (h.1 j) =
      capEmbed hB (chainGhostOut x d Y d₀ u v r B (chainVisit s h j) (h.1 j)) := fun j => by
    rw [hv j]
    exact chainGhostOut_capEmbed hB _ _ (hc j)
  refine ⟨?_, ?_⟩
  · rw [chainWeight, chainWeight]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine prod_congr rfl fun j _ => ?_
      rw [hv j]
      exact chainGhostCoef_capEmbed hB _ _ (hc j) _ _
    · refine prod_congr rfl fun j _ => ?_
      rw [hg j.castSucc]
      refine chainEdgeCoef_capEmbed hB _ (h.2 j) ?_ N
      have := (hs j.succ).1
      rwa [chainVisit_succ, hg j.castSucc] at this
  · unfold chainEnd
    exact hg (Fin.last N)

/-- A history of nonzero weight in the cap-`B` chain has nonzero coefficients. -/
theorem coef_ne_zero_of_chainWeight_ne_zero {N : ℕ} {s : ChainState x d Y d₀ u v r B}
    {h : History x d Y d₀ u v r N} (hw : chainWeight q A₀ s h ≠ 0) :
    (∀ j : Fin (N + 1), chainGhostCoef q x d Y d₀ u v r B N j (chainVisit s h j) (h.1 j) ≠ 0) ∧
      ∀ j : Fin N, chainEdgeCoef q A₀ x d Y d₀ u v r B N
        (chainGhostOut x d Y d₀ u v r B (chainVisit s h j.castSucc) (h.1 j.castSucc))
          (h.2 j) ≠ 0 := by
  unfold chainWeight at hw
  rw [mul_ne_zero_iff, prod_ne_zero_iff, prod_ne_zero_iff] at hw
  exact ⟨fun j => hw.1 j (mem_univ j), fun j => hw.2 j (mem_univ j)⟩

/-- A history of nonzero weight in the cap-`B` chain stays below `B` in the cap-`B'` chain: by
induction it visits the embedded states there. -/
theorem staysBelow_capEmbed_of_ne_zero (hB : B ≤ B') {N : ℕ}
    {s : ChainState x d Y d₀ u v r B} {h : History x d Y d₀ u v r N}
    (hw : chainWeight q A₀ s h ≠ 0) : StaysBelow B (capEmbed hB s) h := by
  obtain ⟨hG, hE⟩ := coef_ne_zero_of_chainWeight_ne_zero hw
  have hv : ∀ j, chainVisit (capEmbed hB s) h j = capEmbed hB (chainVisit s h j) := by
    intro j
    induction j using Fin.induction with
    | zero => rfl
    | succ j ih =>
      have hg := chainGhostOut_capEmbed hB (chainVisit s h j.castSucc) (h.1 j.castSucc)
        (memSize_chainGhostOut_capEmbed_le hB (hG j.castSucc))
      have he := chainEdgeOut_capEmbed hB _ (h.2 j)
        (memSize_chainEdgeOut_capEmbed_le hB (hE j))
      rw [chainVisit_succ, chainVisit_succ, ih, hg, he]
  intro j
  rw [hv j, chainGhostOut_capEmbed hB _ _ (memSize_chainGhostOut_capEmbed_le hB (hG j))]
  exact ⟨memSize_capEmbed_le hB _, memSize_capEmbed_le hB _⟩

/-- A history of nonzero weight in the cap-`B` chain whose edge choices are drawn from the edge
choice set is a history of the cap-`B` chain: its ghost choices are valid, so their
multiplicities are at most `B`. -/
theorem mem_histories_of_ne_zero {N : ℕ} {s : ChainState x d Y d₀ u v r B}
    {h : History x d Y d₀ u v r N} (hw : chainWeight q A₀ s h ≠ 0)
    (hh : ∀ j, h.2 j ∈ edgeChoices x d Y d₀ u v r) : h ∈ histories x d Y d₀ u v r B N := by
  obtain ⟨hG, -⟩ := coef_ne_zero_of_chainWeight_ne_zero hw
  simp only [histories, mem_product, Fintype.mem_piFinset]
  refine ⟨fun j => ?_, hh⟩
  have hv := ghostValid_of_chainGhostCoef_ne_zero (hG j)
  have hS := mem_memStates.1 (chainVisit s h j).2.2.2
  simp only [multBox, Fintype.mem_piFinset, mem_range]
  refine ⟨fun xp => ?_, fun xp => ?_⟩
  · have h₁ := hv.1 xp
    have h₂ := le_memSize (chainVisit s h j).2.2.1 xp
    unfold hitPart at h₁
    split_ifs at h₁ <;> omega
  · have h₁ := le_memSize (h.1 j).2 xp
    have h₂ := hv.memSize_le
    omega

/-! ### Births -/

/-- Distinctness of births is unchanged under an injective relabeling of the addresses, when
the addresses outside its range are not performed. -/
theorem birthsDistinct_comp_iff {α β : Type*} {φ : α → β} (hφ : Function.Injective φ)
    {b : β → Option ℕ} (hb : ∀ a ∉ Set.range φ, b a = none) :
    BirthsDistinct (b ∘ φ) ↔ BirthsDistinct b := by
  constructor
  · intro h a a' p ha ha'
    obtain ⟨c, rfl⟩ : a ∈ Set.range φ := by
      by_contra hc
      rw [hb a hc] at ha
      exact absurd ha (by simp)
    obtain ⟨c', rfl⟩ : a' ∈ Set.range φ := by
      by_contra hc
      rw [hb a' hc] at ha'
      exact absurd ha' (by simp)
    rw [h c c' p ha ha']
  · intro h c c' p hc hc'
    exact hφ (h _ _ p hc hc')

/-- A ghost batch has as many primes as particles. -/
theorem batchPrimes_length_eq_memSize (n : Particle x d → ℕ) :
    (batchPrimes x d n).length = memSize n := by
  simp [batchPrimes, memSize, Multiset.card_sum]

/-- When every ghost batch has at most `B` particles, the births of a history are distinct in
the cap-`B` chain if and only if they are distinct in the cap-`B'` chain: the extra batch
indices are not performed. -/
theorem birthsDistinct_capEmbed_iff (hB : B ≤ B') {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    {h : History x d Y d₀ u v r N} (hh : ∀ j, memSize (h.1 j).2 ≤ B) :
    BirthsDistinct (births (capEmbed hB s) h) ↔ BirthsDistinct (births s h) := by
  set φ : BirthAddr (K := K) x B N → BirthAddr (K := K) x B' N :=
    Sum.map id (Sum.map id (Prod.map id (Fin.castLE hB))) with hφ
  have hinj : Function.Injective φ :=
    Function.Injective.sumMap Function.injective_id
      (Function.Injective.sumMap Function.injective_id
        (Function.Injective.prodMap Function.injective_id (Fin.castLE_injective hB)))
  have hcomp : births (capEmbed hB s) h ∘ φ = births s h := by
    funext a
    rcases a with ⟨i, k⟩ | ⟨j, i⟩ | ⟨j, k⟩ <;> rfl
  rw [← hcomp, birthsDistinct_comp_iff hinj]
  rintro (⟨i, k⟩ | ⟨j, i⟩ | ⟨j, k⟩) ha
  · exact absurd ⟨Sum.inl (i, k), rfl⟩ ha
  · exact absurd ⟨Sum.inr (Sum.inl (j, i)), rfl⟩ ha
  · have hk : B ≤ k.1 := by
      by_contra hk
      exact ha ⟨Sum.inr (Sum.inr (j, ⟨k.1, by omega⟩)), rfl⟩
    show (batchPrimes x d (h.1 j).2)[k.1]? = none
    rw [List.getElem?_eq_none_iff, batchPrimes_length_eq_memSize]
    exact (hh j).trans hk

/-! ### The comparison -/

open scoped Classical in
/-- The inner history sums: from a cap-`B` state, the distinct-birth histories of the cap-`B`
chain give the distinct-birth histories of the cap-`B'` chain from the embedded state that stay
below `B`. -/
theorem sum_histories_capEmbed (hB : B ≤ B') (N : ℕ) (s : ChainState x d Y d₀ u v r B) :
    ∑ h ∈ (histories x d Y d₀ u v r B N).filter (fun h => BirthsDistinct (births s h)),
        chainWeight q A₀ s h * chainInit x d Y d₀ u v r B (chainEnd s h) =
      ∑ h ∈ ((histories x d Y d₀ u v r B' N).filter
          (fun h => BirthsDistinct (births (capEmbed hB s) h))).filter
          (fun h => StaysBelow B (capEmbed hB s) h),
        chainWeight q A₀ (capEmbed hB s) h *
          chainInit x d Y d₀ u v r B' (chainEnd (capEmbed hB s) h) := by
  set F : History x d Y d₀ u v r N → ℂ := fun h =>
    if BirthsDistinct (births (capEmbed hB s) h) ∧ StaysBelow B (capEmbed hB s) h then
      chainWeight q A₀ (capEmbed hB s) h *
        chainInit x d Y d₀ u v r B' (chainEnd (capEmbed hB s) h)
    else 0 with hF
  have hsub : histories x d Y d₀ u v r B N ⊆ histories x d Y d₀ u v r B' N := by
    intro h hh
    simp only [histories, mem_product, Fintype.mem_piFinset, multBox, mem_range] at hh ⊢
    exact ⟨fun j => ⟨fun xp => by have := (hh.1 j).1 xp; omega,
      fun xp => by have := (hh.1 j).2 xp; omega⟩, hh.2⟩
  rw [filter_filter, sum_filter, sum_filter]
  -- on the cap-`B` histories the two summands agree
  have hcongr : ∀ h ∈ histories x d Y d₀ u v r B N,
      (if BirthsDistinct (births s h) then
        chainWeight q A₀ s h * chainInit x d Y d₀ u v r B (chainEnd s h) else 0) = F h := by
    intro h _
    by_cases hw : chainWeight q A₀ s h = 0
    · rw [hF]
      dsimp only
      split_ifs with h₁ h₂ h₂
      · rw [(chainWeight_capEmbed_of_staysBelow hB h₂.2).1, hw, zero_mul, zero_mul]
      · rw [hw, zero_mul]
      · rw [(chainWeight_capEmbed_of_staysBelow hB h₂.2).1, hw, zero_mul]
      · rfl
    · have hs := staysBelow_capEmbed_of_ne_zero hB hw
      obtain ⟨hw', he'⟩ := chainWeight_capEmbed_of_staysBelow (q := q) (A₀ := A₀) hB hs
      have hbatch : ∀ j, memSize (h.1 j).2 ≤ B := fun j =>
        (ghostValid_of_chainGhostCoef_ne_zero
          ((coef_ne_zero_of_chainWeight_ne_zero hw).1 j)).memSize_le
      rw [hF]
      dsimp only
      rw [birthsDistinct_capEmbed_iff hB s hbatch, hw', he']
      simp only [hs, and_true]
      rfl
  rw [sum_congr rfl hcongr]
  -- off the cap-`B` histories the summand vanishes
  refine sum_subset hsub fun h hh hh' => ?_
  split_ifs with h₁
  · by_contra hne
    have hw : chainWeight q A₀ (capEmbed hB s) h ≠ 0 := left_ne_zero_of_mul hne
    rw [(chainWeight_capEmbed_of_staysBelow hB h₁.2).1] at hw
    refine hh' (mem_histories_of_ne_zero hw fun j => ?_)
    exact (Fintype.mem_piFinset.1 (mem_product.1 hh).2) j
  · rfl

open scoped Classical in
/-- **The cap comparison**: for caps `B ≤ B'`, `distinctSum(B') - distinctSum(B)` is the sum
over the distinct-birth histories of the cap-`B'` chain that do not stay below `B`. -/
theorem distinctSum_sub_eq (hB : B ≤ B') (N : ℕ) :
    distinctSum q A₀ x d Y d₀ u v r B' N - distinctSum q A₀ x d Y d₀ u v r B N =
      ∑ s, (chainMeasure q x d Y d₀ u v r B' N s : ℂ) * chainInit x d Y d₀ u v r B' s *
        ∑ h ∈ ((histories x d Y d₀ u v r B' N).filter
            (fun h => BirthsDistinct (births s h))).filter (fun h => ¬ StaysBelow B s h),
          chainWeight q A₀ s h * chainInit x d Y d₀ u v r B' (chainEnd s h) := by
  -- the cap-`B` sum is the sum over the embedded states of the histories staying below `B`
  have hB' : distinctSum q A₀ x d Y d₀ u v r B N =
      ∑ s, (chainMeasure q x d Y d₀ u v r B' N s : ℂ) * chainInit x d Y d₀ u v r B' s *
        ∑ h ∈ ((histories x d Y d₀ u v r B' N).filter
            (fun h => BirthsDistinct (births s h))).filter (fun h => StaysBelow B s h),
          chainWeight q A₀ s h * chainInit x d Y d₀ u v r B' (chainEnd s h) := by
    unfold distinctSum
    refine Fintype.sum_of_injective (capEmbed hB) (capEmbed_injective hB) _ _ (fun s hs => ?_)
      (fun s => ?_)
    · have h0 : chainInit x d Y d₀ u v r B' s = 0 := by
        unfold chainInit
        refine ite_eq_right fun h => absurd (mem_range_capEmbed hB ?_) hs
        rw [h.2]
        exact Nat.zero_le _
      rw [h0, mul_zero, zero_mul]
    · rw [sum_histories_capEmbed hB N s]
      rfl
  rw [hB']
  unfold distinctSum
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun s _ => ?_
  rw [← mul_sub, ← sum_filter_add_sum_filter_not _ (fun h => StaysBelow B s h), add_sub_cancel_left]

/-! ### Memory growth -/

variable (x d Y d₀ u v r) in
/-- The number of ghost births of a history: the total size of its batches. -/
def ghostBirths {N : ℕ} (h : History x d Y d₀ u v r N) : ℕ := ∑ j, memSize (h.1 j).2

/-- A ghost adds at most its batch to the memory. -/
theorem memSize_chainGhostOut_le_add (t : ChainState x d Y d₀ u v r B) (c : GhostChoice x d) :
    memSize (chainGhostOut x d Y d₀ u v r B t c).2.2.1 ≤ memSize t.2.2.1 + memSize c.2 := by
  by_cases hv : GhostValid (HitsAt x d t.1.1) B t.2.2.1 c
  · simp only [chainGhostOut, ghostOut, hv, dite_true]
    unfold memSize
    rw [← sum_add_distrib]
    exact sum_le_sum fun xp _ => by omega
  · simp only [chainGhostOut, ghostOut, hv, dite_false]
    exact Nat.le_add_right _ _

/-- The stored particles of an edge number at most `K`. -/
theorem sum_card_stored_le (t : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    ∑ xp : Particle x d, (c.2.1.filter fun i => edgeStored t c i = xp.1).card ≤ K := by
  classical
  simp only [card_filter]
  rw [sum_comm]
  calc ∑ i ∈ c.2.1, ∑ xp : Particle x d, (if edgeStored t c i = xp.1 then 1 else 0)
      ≤ ∑ _i ∈ c.2.1, 1 := by
        refine sum_le_sum fun i _ => ?_
        rw [← card_filter]
        refine card_le_one.2 fun a ha b hb => Subtype.ext ?_
        rw [← (mem_filter.1 ha).2, ← (mem_filter.1 hb).2]
    _ = c.2.1.card := by rw [card_eq_sum_ones]
    _ ≤ K := by
        have := card_le_univ c.2.1
        rwa [Fintype.card_fin] at this

/-- An edge adds at most `K` particles to the memory. -/
theorem memSize_chainEdgeOut_le_add (t : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r) :
    memSize (chainEdgeOut x d Y d₀ u v r B t c).2.2.1 ≤ memSize t.2.2.1 + K := by
  by_cases hv : EdgeValid x d Y d₀ u v r B t c
  · simp only [chainEdgeOut, hv, dite_true]
    calc memSize (edgeMem t c)
        ≤ ∑ xp, (t.2.2.1 xp + (c.2.1.filter fun i => edgeStored t c i = xp.1).card) :=
          sum_le_sum fun xp _ => by unfold edgeMem; omega
      _ ≤ memSize t.2.2.1 + K := by
          rw [sum_add_distrib]
          exact Nat.add_le_add_left (sum_card_stored_le t c) _
  · simp only [chainEdgeOut, hv, dite_false]
    exact Nat.le_add_right _ _

/-- The memory size at visit `j` is at most the initial size, `K` per edge so far, and the
batches so far. -/
theorem memSize_chainVisit_le {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    (h : History x d Y d₀ u v r N) (j : Fin (N + 1)) :
    memSize (chainVisit s h j).2.2.1 ≤
      memSize s.2.2.1 + K * j + ∑ i, if i.1 < j.1 then memSize (h.1 i).2 else 0 := by
  induction j using Fin.induction with
  | zero => simp [chainVisit_zero]
  | succ j ih =>
    rw [chainVisit_succ]
    have hsplit : ∑ i : Fin (N + 1), (if i.1 < j.succ.1 then memSize (h.1 i).2 else 0) =
        (∑ i : Fin (N + 1), if i.1 < j.castSucc.1 then memSize (h.1 i).2 else 0) +
          memSize (h.1 j.castSucc).2 := by
      have : ∀ i : Fin (N + 1), (if i.1 < j.succ.1 then memSize (h.1 i).2 else 0) =
          (if i.1 < j.castSucc.1 then memSize (h.1 i).2 else 0) +
            if i = j.castSucc then memSize (h.1 i).2 else 0 := by
        intro i
        by_cases hi : i = j.castSucc
        · subst hi
          simp
        · have : i.1 ≠ j.1 := fun h' => hi (Fin.ext h')
          simp only [Fin.val_succ, Fin.val_castSucc, hi, ite_false, add_zero]
          by_cases h₁ : i.1 < j.1
          · simp [h₁, show i.1 < j.1 + 1 by omega]
          · simp [h₁, show ¬ i.1 < j.1 + 1 by omega]
      rw [sum_congr rfl fun i _ => this i, sum_add_distrib, sum_ite_eq']
      simp
    have h₁ := memSize_chainEdgeOut_le_add
      (chainGhostOut x d Y d₀ u v r B (chainVisit s h j.castSucc) (h.1 j.castSucc)) (h.2 j)
    have h₂ := memSize_chainGhostOut_le_add (chainVisit s h j.castSucc) (h.1 j.castSucc)
    rw [hsplit, Fin.val_succ, Nat.mul_succ]
    simp only [Fin.val_castSucc] at ih ⊢
    linarith

/-- **Leaving the low memories needs ghost births**: a history from an empty memory that does
not stay below `B` has `B < K N + ∑_j |batch_j|`. -/
theorem lt_of_not_staysBelow {N : ℕ} {s : ChainState x d Y d₀ u v r B'}
    (hs : memSize s.2.2.1 = 0) {h : History x d Y d₀ u v r N}
    (hh : ¬ StaysBelow B s h) : B < K * N + ghostBirths x d Y d₀ u v r h := by
  unfold StaysBelow at hh
  push Not at hh
  obtain ⟨j, hj⟩ := hh
  have hv := memSize_chainVisit_le s h j
  have hg := memSize_chainGhostOut_le_add (chainVisit s h j) (h.1 j)
  -- `∑_{i < j} |batch_i| + |batch_j| ≤ ∑_i |batch_i|`
  have hsum : (∑ i : Fin (N + 1), if i.1 < j.1 then memSize (h.1 i).2 else 0) +
      memSize (h.1 j).2 ≤ ghostBirths x d Y d₀ u v r h := by
    unfold ghostBirths
    calc (∑ i : Fin (N + 1), if i.1 < j.1 then memSize (h.1 i).2 else 0) + memSize (h.1 j).2
        = ∑ i : Fin (N + 1), ((if i.1 < j.1 then memSize (h.1 i).2 else 0) +
            if i = j then memSize (h.1 i).2 else 0) := by
          simp [sum_add_distrib]
      _ ≤ ∑ i, memSize (h.1 i).2 := by
          refine sum_le_sum fun i _ => ?_
          by_cases h₁ : i = j
          · subst h₁
            simp
          · simp only [h₁, ite_false, add_zero]
            split_ifs <;> omega
  have hjN : K * j.1 ≤ K * N := Nat.mul_le_mul_left K (Nat.lt_succ_iff.1 j.2)
  by_cases h₁ : B < memSize (chainVisit s h j).2.2.1
  · rw [hs] at hv
    linarith
  · have h₂ := hj (by omega)
    rw [hs] at hv
    linarith

end Cap

end Erdos408.OneSided
