import Erdos821.S2.LifespanClassificationTask
import Erdos821.P3Live.Anchors
import Erdos821.S2.PrimeIndices

/-! The actual history has one contiguous lifetime for each big prime. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

namespace MemoryHistory

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)

def birthPrefixBefore (i : Fin (n + 1)) : Multiset ℕ :=
  H.initialBirthValues +
    (∑ j : Fin (n + 1), if j.val < i.val then H.ghostBirthValues j else 0) +
    (∑ e : Fin n, if e.val < i.val then H.freshBirthValues e else 0)

def birthPrefixAfter (i : Fin (n + 1)) : Multiset ℕ :=
  H.initialBirthValues +
    (∑ j : Fin (n + 1), if j.val ≤ i.val then H.ghostBirthValues j else 0) +
    (∑ e : Fin n, if e.val < i.val then H.freshBirthValues e else 0)

theorem liveValues_prefix (hH : H.Valid) (i : Fin (n + 1)) :
    liveValues (H.before i) ≤ H.birthPrefixBefore i ∧
      liveValues (H.after i) ≤ H.birthPrefixAfter i := by
  exact finite_multiset_growth n H.initialBirthValues
    (fun i => liveValues (H.before i)) (fun i => liveValues (H.after i))
    H.ghostBirthValues H.freshBirthValues (H.initial_liveValues hH)
    (H.ghost_liveValues_le hH) (H.edge_liveValues_le EdgeLiveConservationTask_proof hH) i

private theorem ghostPrefix_le_all (i : Fin (n + 1)) :
    (∑ j : Fin (n + 1), if j.val ≤ i.val then H.ghostBirthValues j else 0) ≤
      ∑ j : Fin (n + 1), H.ghostBirthValues j := by
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> simp

private theorem ghostPrefix_lt_le_all (i : Fin (n + 1)) :
    (∑ j : Fin (n + 1), if j.val < i.val then H.ghostBirthValues j else 0) ≤
      ∑ j : Fin (n + 1), H.ghostBirthValues j := by
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> simp

private theorem freshPrefix_lt_le_all (i : Fin (n + 1)) :
    (∑ e : Fin n, if e.val < i.val then H.freshBirthValues e else 0) ≤
      ∑ e : Fin n, H.freshBirthValues e := by
  apply Finset.sum_le_sum
  intro e _
  split_ifs <;> simp

private theorem freshPrefix_le_all (i : Fin n) :
    (∑ e : Fin n, if e.val ≤ i.val then H.freshBirthValues e else 0) ≤
      ∑ e : Fin n, H.freshBirthValues e := by
  apply Finset.sum_le_sum
  intro e _
  split_ifs <;> simp

theorem birthPrefixBefore_add_ghost_le (i : Fin (n + 1)) :
    H.birthPrefixBefore i + H.ghostBirthValues i ≤ H.birthValues := by
  have hid :
      (∑ j : Fin (n + 1), if j.val < i.val then H.ghostBirthValues j else 0) +
          H.ghostBirthValues i =
        ∑ j : Fin (n + 1), if j.val ≤ i.val then H.ghostBirthValues j else 0 :=
    (sum_fin_through (n + 1) H.ghostBirthValues i).symm
  have hg := H.ghostPrefix_le_all i
  have hf := H.freshPrefix_lt_le_all i
  calc
    _ = H.initialBirthValues +
        (∑ j : Fin (n + 1), if j.val ≤ i.val then H.ghostBirthValues j else 0) +
        (∑ e : Fin n, if e.val < i.val then H.freshBirthValues e else 0) := by
          simp only [birthPrefixBefore]
          rw [← hid]
          ac_rfl
    _ ≤ H.initialBirthValues + (∑ j : Fin (n + 1), H.ghostBirthValues j) +
        (∑ e : Fin n, H.freshBirthValues e) := by
          exact add_le_add (add_le_add (le_refl _) hg) hf
    _ = H.birthValues := rfl

theorem birthPrefixAfter_add_fresh_le (i : Fin n) :
    H.birthPrefixAfter i.castSucc + H.freshBirthValues i ≤ H.birthValues := by
  have hid :
      (∑ e : Fin n, if e.val < i.val then H.freshBirthValues e else 0) +
          H.freshBirthValues i =
        ∑ e : Fin n, if e.val ≤ i.val then H.freshBirthValues e else 0 :=
    (sum_fin_through n H.freshBirthValues i).symm
  have hg := H.ghostPrefix_le_all i.castSucc
  have hf := H.freshPrefix_le_all i
  calc
    _ = H.initialBirthValues +
        (∑ j : Fin (n + 1), if j.val ≤ i.castSucc.val then H.ghostBirthValues j else 0) +
        (∑ e : Fin n, if e.val ≤ i.val then H.freshBirthValues e else 0) := by
          simp only [birthPrefixAfter]
          rw [← hid]
          ac_rfl
    _ ≤ H.initialBirthValues + (∑ j : Fin (n + 1), H.ghostBirthValues j) +
        (∑ e : Fin n, H.freshBirthValues e) := by
          exact add_le_add (add_le_add (le_refl _) hg) hf
    _ = H.birthValues := rfl

theorem birthPrefixBefore_ghost_disjoint (hd : H.DistinctBirths) (i : Fin (n + 1)) :
    Disjoint (H.birthPrefixBefore i) (H.ghostBirthValues i) := by
  have hn := Multiset.nodup_of_le (H.birthPrefixBefore_add_ghost_le i) hd
  exact (Multiset.nodup_add.mp hn).2.2

theorem birthPrefixAfter_fresh_disjoint (hd : H.DistinctBirths) (i : Fin n) :
    Disjoint (H.birthPrefixAfter i.castSucc) (H.freshBirthValues i) := by
  have hn := Multiset.nodup_of_le (H.birthPrefixAfter_add_fresh_le i) hd
  exact (Multiset.nodup_add.mp hn).2.2


theorem birthPrefixAfter_mono (i j : Fin (n + 1)) (hij : i ≤ j) :
    H.birthPrefixAfter i ≤ H.birthPrefixAfter j := by
  have hg :
      (∑ k : Fin (n + 1), if k.val ≤ i.val then H.ghostBirthValues k else 0) ≤
        ∑ k : Fin (n + 1), if k.val ≤ j.val then H.ghostBirthValues k else 0 := by
    apply Finset.sum_le_sum
    intro k _
    by_cases hj : k.val ≤ j.val <;> by_cases hi : k.val ≤ i.val <;>
      simp [hi, hj] <;> omega
  have hf :
      (∑ e : Fin n, if e.val < i.val then H.freshBirthValues e else 0) ≤
        ∑ e : Fin n, if e.val < j.val then H.freshBirthValues e else 0 := by
    apply Finset.sum_le_sum
    intro e _
    by_cases hj : e.val < j.val <;> by_cases hi : e.val < i.val <;>
      simp [hi, hj] <;> omega
  unfold birthPrefixAfter
  exact add_le_add (add_le_add (le_refl _) hg) hf

theorem birthPrefixAfter_castSucc_le_before_succ (i : Fin n) :
    H.birthPrefixAfter i.castSucc ≤ H.birthPrefixBefore i.succ := by
  have hg :
      (∑ k : Fin (n + 1), if k.val ≤ i.castSucc.val then H.ghostBirthValues k else 0) =
        ∑ k : Fin (n + 1), if k.val < i.succ.val then H.ghostBirthValues k else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.lt_succ_iff]
  have hf :
      (∑ e : Fin n, if e.val < i.val then H.freshBirthValues e else 0) ≤
        ∑ e : Fin n, if e.val < i.succ.val then H.freshBirthValues e else 0 := by
    apply Finset.sum_le_sum
    intro e _
    by_cases hlt : e.val < i.val
    · simp [hlt, Nat.le_of_lt hlt]
    · simp [hlt]
  unfold birthPrefixAfter birthPrefixBefore
  rw [hg]
  exact add_le_add (add_le_add (le_refl _) le_rfl) hf


theorem birthPrefixAfter_le_before_of_lt (b j : Fin (n + 1)) (hbj : b < j) :
    H.birthPrefixAfter b ≤ H.birthPrefixBefore j := by
  have hg :
      (∑ k : Fin (n + 1), if k.val ≤ b.val then H.ghostBirthValues k else 0) ≤
        ∑ k : Fin (n + 1), if k.val < j.val then H.ghostBirthValues k else 0 := by
    apply Finset.sum_le_sum
    intro k _
    by_cases hleft : k.val ≤ b.val
    · have hright : k.val < j.val := by
        exact lt_of_le_of_lt hleft (Fin.lt_iff_val_lt_val.mp hbj)
      simp [hleft, hright]
    · simp [hleft]
  have hf :
      (∑ e : Fin n, if e.val < b.val then H.freshBirthValues e else 0) ≤
        ∑ e : Fin n, if e.val < j.val then H.freshBirthValues e else 0 := by
    apply Finset.sum_le_sum
    intro e _
    by_cases hleft : e.val < b.val
    · have hright : e.val < j.val := lt_trans hleft (Fin.lt_iff_val_lt_val.mp hbj)
      simp [hleft, hright]
    · simp [hleft]
  unfold birthPrefixAfter birthPrefixBefore
  exact add_le_add (add_le_add (le_refl _) hg) hf

theorem no_ghost_birth_after_prefix_lt (hd : H.DistinctBirths)
    (b j : Fin (n + 1)) (hbj : b < j) {p : ℕ} (hp : p ∈ H.birthPrefixAfter b) :
    p ∉ H.ghostBirthValues j := by
  have hp' : p ∈ H.birthPrefixBefore j :=
    Multiset.mem_of_le (H.birthPrefixAfter_le_before_of_lt b j hbj) hp
  exact (Multiset.disjoint_left.mp (H.birthPrefixBefore_ghost_disjoint hd j)) hp'

theorem ghost_live_predecessor_lt (hH : H.Valid) (hd : H.DistinctBirths)
    (b j : Fin (n + 1)) (hbj : b < j) {p : ℕ}
    (hp : p ∈ H.birthPrefixAfter b) (hNext : p ∈ liveValues (H.after j)) :
    p ∈ liveValues (H.before j) := by
  have hnot := H.no_ghost_birth_after_prefix_lt hd b j hbj hp
  have hmem := Multiset.mem_of_le (H.ghost_liveValues_le hH j) hNext
  rcases Multiset.mem_add.mp hmem with hprev | hnew
  · exact hprev
  · exact (hnot hnew).elim

theorem activePrime_iff_visit (i : Fin (n + 1)) (g : P.BigGroup) (p : P.Prime g.val) :
    p ∈ activePrimes (H.before i).2.1 g.val ↔ i ∈ H.toResiduePath.activeVisits g p := by
  simp [activePrimes, ResiduePath.activeVisits, MemoryHistory.toResiduePath, eq_comm]

theorem no_fresh_after_prefix (hd : H.DistinctBirths) (b : Fin (n + 1)) (i : Fin n)
    (hbi : b ≤ i.castSucc) {p : ℕ} (hp : p ∈ H.birthPrefixAfter b) :
    p ∉ H.freshBirthValues i := by
  have hp' : p ∈ H.birthPrefixAfter i.castSucc :=
    Multiset.mem_of_le (H.birthPrefixAfter_mono b i.castSucc hbi) hp
  exact (Multiset.disjoint_left.mp (H.birthPrefixAfter_fresh_disjoint hd i)) hp'

theorem no_ghost_after_prefix (hd : H.DistinctBirths) (b : Fin (n + 1)) (i : Fin n)
    (hbi : b ≤ i.castSucc) {p : ℕ} (hp : p ∈ H.birthPrefixAfter b) :
    p ∉ H.ghostBirthValues i.succ := by
  have hp' : p ∈ H.birthPrefixBefore i.succ :=
    Multiset.mem_of_le
      ((H.birthPrefixAfter_mono b i.castSucc hbi).trans
        (H.birthPrefixAfter_castSucc_le_before_succ i)) hp
  exact (Multiset.disjoint_left.mp (H.birthPrefixBefore_ghost_disjoint hd i.succ)) hp'

theorem edge_live_predecessor (hH : H.Valid) (hd : H.DistinctBirths)
    (b : Fin (n + 1)) (i : Fin n) (hbi : b ≤ i.castSucc) {p : ℕ}
    (hp : p ∈ H.birthPrefixAfter b) (hNext : p ∈ liveValues (H.before i.succ)) :
    p ∈ liveValues (H.after i.castSucc) := by
  have hnot := H.no_fresh_after_prefix hd b i hbi hp
  have hmem := Multiset.mem_of_le (H.edge_liveValues_le EdgeLiveConservationTask_proof hH i) hNext
  rcases Multiset.mem_add.mp hmem with hprev | hnew
  · exact hprev
  · exact (hnot hnew).elim

theorem ghost_live_predecessor (hH : H.Valid) (hd : H.DistinctBirths)
    (b : Fin (n + 1)) (i : Fin n) (hbi : b ≤ i.castSucc) {p : ℕ}
    (hp : p ∈ H.birthPrefixAfter b) (hNext : p ∈ liveValues (H.after i.succ)) :
    p ∈ liveValues (H.before i.succ) := by
  have hnot := H.no_ghost_after_prefix hd b i hbi hp
  have hmem := Multiset.mem_of_le (H.ghost_liveValues_le hH i.succ) hNext
  rcases Multiset.mem_add.mp hmem with hprev | hnew
  · exact hprev
  · exact (hnot hnew).elim



theorem birthPrefixBefore_le_after (i : Fin (n + 1)) :
    H.birthPrefixBefore i ≤ H.birthPrefixAfter i := by
  have hg :
      (∑ k : Fin (n + 1), if k.val < i.val then H.ghostBirthValues k else 0) ≤
        ∑ k : Fin (n + 1), if k.val ≤ i.val then H.ghostBirthValues k else 0 := by
    apply Finset.sum_le_sum
    intro k _
    by_cases hlt : k.val < i.val <;> by_cases hle : k.val ≤ i.val <;>
      simp [hlt, hle] <;> omega
  unfold birthPrefixBefore birthPrefixAfter
  exact add_le_add (add_le_add (le_refl _) hg) le_rfl

/-- The finite global live-prime multiset contains every prime in one group. -/
theorem groupLive_mem_liveValues {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    {p : P.Prime g.val} (hp : p ∈ groupLivePrimes s g) : p.val ∈ liveValues s := by
  have hle : (groupLivePrimes s g).map Subtype.val ≤ liveValues s := by
    unfold liveValues
    exact Finset.single_le_sum (f := fun h : P.BigGroup => (groupLivePrimes s h).map Subtype.val)
      (fun _ _ => Multiset.zero_le _) (Finset.mem_univ g)
  exact Multiset.mem_of_le hle (Multiset.mem_map.mpr ⟨p, hp, rfl⟩)

/-- A numerical prime in the global live multiset belongs to its unique group. -/
theorem liveValues_mem_groupLive {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (p : P.Prime g.val) (hp : p.val ∈ liveValues s) : p ∈ groupLivePrimes s g := by
  simp only [liveValues, Multiset.mem_sum, Finset.mem_univ, true_and] at hp
  rcases hp with ⟨h, hp⟩
  rcases Multiset.mem_map.mp hp with ⟨q, hq, hval⟩
  have hgroup : h.val = g.val := by
    by_contra hne
    have hqg : q.val ∈ P.primes g.val := by rw [hval]; exact p.property
    exact (Finset.disjoint_left.mp (P.disjoint h.val g.val hne)) q.property hqg
  have hh : h = g := Subtype.ext hgroup
  subst h
  have hqeq : q = p := Subtype.ext hval
  rw [hqeq] at hq
  exact hq

def liveVisits (g : P.BigGroup) (p : P.Prime g.val) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i =>
    p.val ∈ liveValues (H.before i) ∨ p.val ∈ liveValues (H.after i))

def lifeSpan (g : P.BigGroup) (p : P.Prime g.val) : PrimeSpan n := by
  classical
  let L := H.liveVisits g p
  exact if h : L.Nonempty then some (L.min' h, L.max' h) else none

def lifeAssignment : LifespanAssignment P n := fun g p => H.lifeSpan g p

theorem liveVisits_mem {g : P.BigGroup} {p : P.Prime g.val} {i : Fin (n + 1)}
    (hi : i ∈ H.liveVisits g p) :
    p.val ∈ liveValues (H.before i) ∨ p.val ∈ liveValues (H.after i) :=
  (Finset.mem_filter.mp hi).2

theorem activeVisits_subset_liveVisits {hH : H.Valid} (g : P.BigGroup) (p : P.Prime g.val) :
    (H.toResiduePath.activeVisits g p) ⊆ H.liveVisits g p := by
  intro i hi
  have hlabel : ∃ j : Fin (J + F.ell), (H.before i).2.1 g.val j = p := by
    change i ∈ Finset.univ.filter
      (fun i => ∃ j : Fin (J + F.ell), (H.before i).2.1 g.val j = p) at hi
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨j, hj⟩ := hlabel
  have hpAct : p ∈ activePrimes (H.before i).2.1 g.val := by
    unfold activePrimes
    simp only [Multiset.mem_sum]
    exact ⟨j, Finset.mem_univ j, Multiset.mem_singleton.mpr hj.symm⟩
  have hpLive : p ∈ groupLivePrimes (H.before i) g :=
    Multiset.mem_add.mpr (Or.inl hpAct)
  have hpGlobal := groupLive_mem_liveValues (H.before i) g hpLive
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl hpGlobal⟩


theorem slotPrimes_mem_active {M : ℕ} (a : P.Labels M) (g : P.Group)
    (B : Finset (Fin M)) {p : P.Prime g} (hp : p ∈ slotPrimes (a g) B) :
    p ∈ activePrimes a g := by
  rw [slotPrimes_eq_val_map] at hp
  rcases Multiset.mem_map.mp hp with ⟨i, hi, hpi⟩
  unfold activePrimes
  simp only [Multiset.mem_sum]
  exact ⟨i, Finset.mem_univ i, Multiset.mem_singleton.mpr hpi.symm⟩

theorem edge_pending_live_backward (hH : H.Valid) (hd : H.DistinctBirths)
    (i : Fin n) (g : P.BigGroup) (p : P.Prime g.val)
    (hp : p ∈ pendingPrimes ((H.before i.succ).2.2 g)) :
    p.val ∈ liveValues (H.after i.castSucc) := by
  let ss := permuteActive (H.edge i).1 (H.after i.castSucc)
  let tt := permuteActive (H.edge i).2.1 (H.before i.succ)
  let ν := A.pattern (H.edge i).2.2.1
  let u := (H.edge i).2.2.2.1
  let c := (H.edge i).2.2.2.2
  have hraw : rawEdgeValid A ν (edgeForward i) u ss tt c := (hH.2.2.2 i).1
  have hcons := EdgeLiveConservationTask_proof F P J m A ν (edgeForward i) u
    ss tt c hraw g
  have hpT : p ∈ pendingPrimes (tt.2.2 g) := by simpa [tt, permuteActive] using hp
  have hND := H.liveValues_nodup_of_distinct hH hd i.succ
  have hdisT0 := big_live_structure (H.before i.succ) hND.1 g
  have hdisT : Disjoint (activePrimes tt.2.1 g.val) (pendingPrimes (tt.2.2 g)) := by
    simpa [tt, permuteActive, activePrimes_act] using hdisT0.2.2
  have hL : p ∈ activePrimes tt.2.1 g.val + pendingPrimes (tt.2.2 g) +
      slotPrimes (ss.2.1 g.val) (unsharedDroppedSlots ν g.val (c.1 g)) := by
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr hpT)))
  rw [hcons] at hL
  rcases Multiset.mem_add.mp hL with hS | hTD
  · rcases Multiset.mem_add.mp hS with hSA | hSP
    · have hgroup : p ∈ groupLivePrimes (H.after i.castSucc) g := by
        unfold groupLivePrimes
        exact Multiset.mem_add.mpr (Or.inl (by simpa [ss, permuteActive, activePrimes_act] using hSA))
      exact groupLive_mem_liveValues (H.after i.castSucc) g hgroup
    · have hgroup : p ∈ groupLivePrimes (H.after i.castSucc) g := by
        unfold groupLivePrimes
        exact Multiset.mem_add.mpr (Or.inr (by simpa [ss, permuteActive] using hSP))
      exact groupLive_mem_liveValues (H.after i.castSucc) g hgroup
  · have hActive : p ∈ activePrimes tt.2.1 g.val :=
      slotPrimes_mem_active tt.2.1 g.val _ hTD
    exact False.elim ((Multiset.disjoint_left.mp hdisT) hActive hpT)

theorem edge_pending_live_forward (hH : H.Valid) (hd : H.DistinctBirths)
    (i : Fin n) (g : P.BigGroup) (p : P.Prime g.val)
    (hp : p ∈ pendingPrimes ((H.after i.castSucc).2.2 g)) :
    p.val ∈ liveValues (H.before i.succ) := by
  let ss := permuteActive (H.edge i).1 (H.after i.castSucc)
  let tt := permuteActive (H.edge i).2.1 (H.before i.succ)
  let ν := A.pattern (H.edge i).2.2.1
  let u := (H.edge i).2.2.2.1
  let c := (H.edge i).2.2.2.2
  have hraw : rawEdgeValid A ν (edgeForward i) u ss tt c := (hH.2.2.2 i).1
  have hcons := EdgeLiveConservationTask_proof F P J m A ν (edgeForward i) u
    ss tt c hraw g
  have hpS : p ∈ pendingPrimes (ss.2.2 g) := by simpa [ss, permuteActive] using hp
  have hND := H.liveValues_nodup_of_distinct hH hd i.castSucc
  have hdisS0 := big_live_structure (H.after i.castSucc) hND.2 g
  have hdisS : Disjoint (activePrimes ss.2.1 g.val) (pendingPrimes (ss.2.2 g)) := by
    simpa [ss, permuteActive, activePrimes_act] using hdisS0.2.2
  have hR : p ∈ activePrimes ss.2.1 g.val + pendingPrimes (ss.2.2 g) +
      slotPrimes (tt.2.1 g.val) (unsharedDroppedSlots ν g.val (c.2.1 g)) := by
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr hpS)))
  have hL : p ∈ activePrimes tt.2.1 g.val + pendingPrimes (tt.2.2 g) +
      slotPrimes (ss.2.1 g.val) (unsharedDroppedSlots ν g.val (c.1 g)) := by
    simpa only [hcons] using hR
  rcases Multiset.mem_add.mp hL with hT | hSD
  · rcases Multiset.mem_add.mp hT with hTA | hTP
    · have hgroup : p ∈ groupLivePrimes (H.before i.succ) g := by
        unfold groupLivePrimes
        exact Multiset.mem_add.mpr (Or.inl (by simpa [tt, permuteActive, activePrimes_act] using hTA))
      exact groupLive_mem_liveValues (H.before i.succ) g hgroup
    · have hgroup : p ∈ groupLivePrimes (H.before i.succ) g := by
        unfold groupLivePrimes
        exact Multiset.mem_add.mpr (Or.inr (by simpa [tt, permuteActive] using hTP))
      exact groupLive_mem_liveValues (H.before i.succ) g hgroup
  · have hActive : p ∈ activePrimes ss.2.1 g.val := slotPrimes_mem_active ss.2.1 g.val _ hSD
    exact False.elim ((Multiset.disjoint_left.mp hdisS) hActive hpS)


theorem no_pendingBefore_min (hH : H.Valid) (hd : H.DistinctBirths)
    (g : P.BigGroup) (p : P.Prime g.val) (hL : (H.liveVisits g p).Nonempty) :
    p ∉ pendingPrimes ((H.before ((H.liveVisits g p).min' hL)).2.2 g) := by
  let b := (H.liveVisits g p).min' hL
  intro hp
  by_cases hb0 : b = 0
  · have hpB : p ∈ pendingPrimes ((H.before b).2.2 g) := by
      change p ∈ pendingPrimes ((H.before b).2.2 g)
      exact hp
    have hp0 : p ∈ pendingPrimes ((H.before 0).2.2 g) := by
      simpa only [hb0] using hpB
    have hzero := hH.1 g
    have hzeroP : pendingPrimes ((H.before 0).2.2 g) = 0 := by
      calc
        _ = pendingPrimes (0 : P.Memory g.val) := congrArg pendingPrimes hzero
        _ = 0 := by simp [pendingPrimes]
    have hp0 := Eq.mp (congrArg (fun z : Multiset (P.Prime g.val) => p ∈ z) hzeroP) hp0
    simpa using hp0
  · have hbpos : 0 < b.val := by
      by_contra h
      have heq : b.val = 0 := Nat.eq_zero_of_not_pos h
      exact hb0 (Fin.ext heq)
    let e : Fin n := ⟨b.val - 1, by have := b.isLt; omega⟩
    have he : e.succ = b := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp [e]
      omega
    have hpE : p ∈ pendingPrimes ((H.before e.succ).2.2 g) := by rw [he]; exact hp
    have hprev := H.edge_pending_live_backward hH hd e g p hpE
    have hprevVisit : e.castSucc ∈ H.liveVisits g p :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hprev⟩
    have hmin : b ≤ e.castSucc := Finset.min'_le _ _ hprevVisit
    have hltVal : e.castSucc.val < b.val := by
      simp only [Fin.val_castSucc]
      dsimp [e]
      omega
    have hlt : e.castSucc < b := Fin.lt_iff_val_lt_val.mpr hltVal
    exact (not_lt_of_ge hmin) hlt

theorem no_pendingAfter_max (hH : H.Valid) (hd : H.DistinctBirths)
    (g : P.BigGroup) (p : P.Prime g.val) (hL : (H.liveVisits g p).Nonempty) :
    p ∉ pendingPrimes ((H.after ((H.liveVisits g p).max' hL)).2.2 g) := by
  let s := (H.liveVisits g p).max' hL
  intro hp
  by_cases hlast : s = Fin.last n
  · have hpS : p ∈ pendingPrimes ((H.after s).2.2 g) := by
      change p ∈ pendingPrimes ((H.after s).2.2 g)
      exact hp
    have hpLast : p ∈ pendingPrimes ((H.after (Fin.last n)).2.2 g) := by
      simpa only [hlast] using hpS
    have hzero := hH.2.1 g
    have hzeroP : pendingPrimes ((H.after (Fin.last n)).2.2 g) = 0 := by
      calc
        _ = pendingPrimes (0 : P.Memory g.val) := congrArg pendingPrimes hzero
        _ = 0 := by simp [pendingPrimes]
    have hp0 := Eq.mp (congrArg (fun z : Multiset (P.Prime g.val) => p ∈ z) hzeroP) hpLast
    simpa using hp0
  · have hslt : s.val < n := by
      have hsle : s.val ≤ n := Nat.lt_succ_iff.mp s.isLt
      have hsne : s.val ≠ n := by
        intro heq
        apply hlast
        exact Fin.ext heq
      omega
    let e : Fin n := ⟨s.val, hslt⟩
    have he : e.castSucc = s := Fin.ext rfl
    have hpE : p ∈ pendingPrimes ((H.after e.castSucc).2.2 g) := by rw [he]; exact hp
    have hnext := H.edge_pending_live_forward hH hd e g p hpE
    have hnextVisit : e.succ ∈ H.liveVisits g p :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hnext⟩
    have hmax : e.succ ≤ s := Finset.le_max' _ _ hnextVisit
    have hlt : s < e.succ := by
      apply Fin.lt_iff_val_lt_val.mpr
      dsimp [e]
      omega
    exact (not_lt_of_ge hmax) hlt

theorem first_noactive_pendingAfter (hH : H.Valid) (hd : H.DistinctBirths)
    (g : P.BigGroup) (p : P.Prime g.val) (hL : (H.liveVisits g p).Nonempty)
    (hAct : p ∉ activePrimes (H.before ((H.liveVisits g p).min' hL)).2.1 g.val) :
    p ∈ pendingPrimes ((H.after ((H.liveVisits g p).min' hL)).2.2 g) := by
  let b := (H.liveVisits g p).min' hL
  have hAt := H.liveVisits_mem (Finset.min'_mem (H.liveVisits g p) hL)
  have hActAfter : p ∉ activePrimes (H.after b).2.1 g.val := by
    have heq := (hH.2.2.1 b).2.1
    intro ha
    apply hAct
    simpa only [← heq] using ha
  have hBeforeNot : p ∉ pendingPrimes ((H.before b).2.2 g) := by
    simpa [b] using H.no_pendingBefore_min hH hd g p hL
  rcases hAt with hBefore | hAfter
  · have hgroup := liveValues_mem_groupLive (H.before b) g p hBefore
    rcases Multiset.mem_add.mp hgroup with hActive | hPending
    · exact (hAct hActive).elim
    · exact (hBeforeNot hPending).elim
  · have hgroup := liveValues_mem_groupLive (H.after b) g p hAfter
    rcases Multiset.mem_add.mp hgroup with hActive | hPending
    · exact (hActAfter hActive).elim
    · exact hPending

theorem last_noactive_pendingBefore (hH : H.Valid) (hd : H.DistinctBirths)
    (g : P.BigGroup) (p : P.Prime g.val) (hL : (H.liveVisits g p).Nonempty)
    (hAct : p ∉ activePrimes (H.before ((H.liveVisits g p).max' hL)).2.1 g.val) :
    p ∈ pendingPrimes ((H.before ((H.liveVisits g p).max' hL)).2.2 g) := by
  let s := (H.liveVisits g p).max' hL
  have hAt := H.liveVisits_mem (Finset.max'_mem (H.liveVisits g p) hL)
  have hActAfter : p ∉ activePrimes (H.after s).2.1 g.val := by
    have heq := (hH.2.2.1 s).2.1
    intro ha
    apply hAct
    simpa only [← heq] using ha
  have hAfterNot : p ∉ pendingPrimes ((H.after s).2.2 g) := by
    simpa [s] using H.no_pendingAfter_max hH hd g p hL
  rcases hAt with hBefore | hAfter
  · have hgroup := liveValues_mem_groupLive (H.before s) g p hBefore
    rcases Multiset.mem_add.mp hgroup with hActive | hPending
    · exact (hAct hActive).elim
    · exact hPending
  · have hgroup := liveValues_mem_groupLive (H.after s) g p hAfter
    rcases Multiset.mem_add.mp hgroup with hActive | hPending
    · exact (hActAfter hActive).elim
    · exact (hAfterNot hPending).elim

theorem ghostBirth_particle_zero_at_first (hH : H.Valid) (hd : H.DistinctBirths)
    (g : P.BigGroup) (p : P.Prime g.val) (hL : (H.liveVisits g p).Nonempty)
    (hAct : p ∉ activePrimes (H.before ((H.liveVisits g p).min' hL)).2.1 g.val) :
    ∃ z ∈ (H.after ((H.liveVisits g p).min' hL)).2.2 g,
      z.1 = p ∧ z.2 = 0 := by
  let b := (H.liveVisits g p).min' hL
  have hpAfter := H.first_noactive_pendingAfter hH hd g p hL hAct
  rcases Multiset.mem_map.mp hpAfter with ⟨z, hzAfter, hzPrime⟩
  have hGhost := (hH.2.2.1 b).2.2 g
  have hEq := hGhost.2
  have hzSum : z ∈ deleteMemoryIndices ((H.before b).2.2 g) ((H.ghost b).1 g) +
      zeroBirthBatch ((H.ghost b).2.2 g) :=
    Eq.mp (congrArg (fun m : P.Memory g.val => z ∈ m) hEq).symm hzAfter
  rcases Multiset.mem_add.mp hzSum with hzDel | hzBirth
  · have hpart := memory_indices_partition ((H.before b).2.2 g) ((H.ghost b).1 g)
    have hdelLe : deleteMemoryIndices ((H.before b).2.2 g) ((H.ghost b).1 g) ≤
        (H.before b).2.2 g := by
      have hle := Multiset.le_add_right
        (deleteMemoryIndices ((H.before b).2.2 g) ((H.ghost b).1 g))
        (((H.ghost b).1 g).val.map (memoryEntry ((H.before b).2.2 g)))
      rw [hpart] at hle
      exact hle
    have hzBefore := Multiset.mem_of_le hdelLe hzDel
    have hpBefore : p ∈ pendingPrimes ((H.before b).2.2 g) :=
      Multiset.mem_map.mpr ⟨z, hzBefore, hzPrime⟩
    have hnone := H.no_pendingBefore_min hH hd g p hL
    exact (hnone (by simpa [b] using hpBefore)).elim
  · obtain ⟨j, hzEq⟩ := (zeroBirthBatch_mem _ _).mp hzBirth
    have hBatchLe : zeroBirthBatch ((H.ghost b).2.2 g) ≤ (H.after b).2.2 g :=
      Eq.mp (congrArg (fun m : P.Memory g.val =>
        zeroBirthBatch ((H.ghost b).2.2 g) ≤ m) hEq) (Multiset.le_add_left _ _)
    have hzMem := Multiset.mem_of_le hBatchLe hzBirth
    have hz0 : z.2 = 0 := by rw [hzEq]
    exact ⟨z, hzMem, hzPrime, hz0⟩

theorem ghostStop_particle_zero_at_last (hH : H.Valid) (hd : H.DistinctBirths)
    (g : P.BigGroup) (p : P.Prime g.val) (hL : (H.liveVisits g p).Nonempty)
    (hAct : p ∉ activePrimes (H.before ((H.liveVisits g p).max' hL)).2.1 g.val) :
    ∃ z ∈ (H.before ((H.liveVisits g p).max' hL)).2.2 g,
      z.1 = p ∧ z.2 = 0 := by
  let s := (H.liveVisits g p).max' hL
  have hpBefore := H.last_noactive_pendingBefore hH hd g p hL hAct
  rcases Multiset.mem_map.mp hpBefore with ⟨z, hzBefore, hzPrime⟩
  have hGhost := (hH.2.2.1 s).2.2 g
  have hEq := hGhost.2
  have hzNotAfter : z ∉ (H.after s).2.2 g := by
    intro hz
    have hpAfter : p ∈ pendingPrimes ((H.after s).2.2 g) :=
      Multiset.mem_map.mpr ⟨z, hz, hzPrime⟩
    exact (H.no_pendingAfter_max hH hd g p hL) (by simpa [s] using hpAfter)
  have hPart : z ∈ deleteMemoryIndices ((H.before s).2.2 g) ((H.ghost s).1 g) +
      ((H.ghost s).1 g).val.map (memoryEntry ((H.before s).2.2 g)) := by
    rw [memory_indices_partition]
    exact hzBefore
  rcases Multiset.mem_add.mp hPart with hzDel | hzSelected
  · have hdelLe : deleteMemoryIndices ((H.before s).2.2 g) ((H.ghost s).1 g) ≤
        (H.after s).2.2 g :=
      Eq.mp (congrArg (fun m : P.Memory g.val =>
        deleteMemoryIndices ((H.before s).2.2 g) ((H.ghost s).1 g) ≤ m) hEq)
        (Multiset.le_add_right _ _)
    exact (hzNotAfter (Multiset.mem_of_le hdelLe hzDel)).elim
  · rcases Multiset.mem_map.mp hzSelected with ⟨j, hj, hzj⟩
    have hjB : j ∈ (H.ghost s).1 g := by simpa using hj
    have hjZero : (memoryEntry ((H.before s).2.2 g) j).2 = 0 := by
      have hsubset := hGhost.1
      have hmem := hsubset hjB
      simpa [zeroMemoryIndices] using (Finset.mem_filter.mp hmem).2
    have hzZero : z.2 = 0 := by rw [← hzj]; exact hjZero
    exact ⟨z, hzBefore, hzPrime, hzZero⟩

theorem active_anchor_hit (hAnch : ∀ i, H.AnchorInvariant i (H.before i) ∧
      H.AnchorInvariant i (H.after i))
    (g : P.BigGroup) (p : P.Prime g.val) (i : Fin (n + 1))
    (hi : i ∈ H.toResiduePath.activeVisits g p) :
    (H.toResiduePath.offset i : ZMod p.val) = (H.anchorOffset p.val : ZMod p.val) := by
  have hlabel : ∃ j : Fin (J + F.ell), (H.before i).2.1 g.val j = p := by
    change i ∈ Finset.univ.filter
      (fun i => ∃ j : Fin (J + F.ell), (H.before i).2.1 g.val j = p) at hi
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨j, hj⟩ := hlabel
  have h := (hAnch i).1.1 g j
  cases hj
  exact h

theorem birthAnchor_zero (hAnch : ∀ i, H.AnchorInvariant i (H.before i) ∧
      H.AnchorInvariant i (H.after i))
    (g : P.BigGroup) (p : P.Prime g.val) (i : Fin (n + 1))
    (z : P.Particle g.val) (hz : z ∈ (H.after i).2.2 g)
    (hp : z.1 = p) (hz0 : z.2 = 0) :
    ((H.toResiduePath.offset i - H.anchorOffset p.val : ℤ) : ZMod p.val) = 0 := by
  have hInv := (hAnch i).2.2 g z hz
  cases hp
  exact hInv.symm.trans hz0

theorem stopAnchor_zero (hAnch : ∀ i, H.AnchorInvariant i (H.before i) ∧
      H.AnchorInvariant i (H.after i))
    (g : P.BigGroup) (p : P.Prime g.val) (i : Fin (n + 1))
    (z : P.Particle g.val) (hz : z ∈ (H.before i).2.2 g)
    (hp : z.1 = p) (hz0 : z.2 = 0) :
    ((H.toResiduePath.offset i - H.anchorOffset p.val : ℤ) : ZMod p.val) = 0 := by
  have hInv := (hAnch i).1.2 g z hz
  cases hp
  exact hInv.symm.trans hz0

theorem birthPrefixAfter_at_first (hH : H.Valid) (g : P.BigGroup) (p : P.Prime g.val)
    (hL : (H.liveVisits g p).Nonempty) :
    p.val ∈ H.birthPrefixAfter ((H.liveVisits g p).min' hL) := by
  let b := (H.liveVisits g p).min' hL
  have hAt := H.liveVisits_mem (Finset.min'_mem (H.liveVisits g p) hL)
  rcases hAt with hBefore | hAfter
  · have hprefix := (H.liveValues_prefix hH b).1
    have hp := Multiset.mem_of_le hprefix hBefore
    exact Multiset.mem_of_le (H.birthPrefixBefore_le_after b) hp
  · exact Multiset.mem_of_le (H.liveValues_prefix hH b).2 hAfter

theorem firstOffset_eq_anchor (hH : H.Valid) (hd : H.DistinctBirths)
    (hAnch : ∀ i, H.AnchorInvariant i (H.before i) ∧ H.AnchorInvariant i (H.after i))
    (g : P.BigGroup) (p : P.Prime g.val) (hL : (H.liveVisits g p).Nonempty) :
    (H.toResiduePath.offset ((H.liveVisits g p).min' hL) : ZMod p.val) =
      (H.anchorOffset p.val : ZMod p.val) := by
  let b := (H.liveVisits g p).min' hL
  by_cases hAct : p ∈ activePrimes (H.before b).2.1 g.val
  · have hVisit := (H.activePrime_iff_visit b g p).mp hAct
    exact H.active_anchor_hit hAnch g p b hVisit
  · obtain ⟨z, hz, hzp, hz0⟩ := H.ghostBirth_particle_zero_at_first hH hd g p hL (by simpa [b] using hAct)
    have hzero := H.birthAnchor_zero hAnch g p b z hz hzp hz0
    exact sub_eq_zero.mp (by simpa only [Int.cast_sub] using hzero)

theorem lastOffset_eq_anchor (hH : H.Valid) (hd : H.DistinctBirths)
    (hAnch : ∀ i, H.AnchorInvariant i (H.before i) ∧ H.AnchorInvariant i (H.after i))
    (g : P.BigGroup) (p : P.Prime g.val) (hL : (H.liveVisits g p).Nonempty) :
    (H.toResiduePath.offset ((H.liveVisits g p).max' hL) : ZMod p.val) =
      (H.anchorOffset p.val : ZMod p.val) := by
  let s := (H.liveVisits g p).max' hL
  by_cases hAct : p ∈ activePrimes (H.before s).2.1 g.val
  · have hVisit := (H.activePrime_iff_visit s g p).mp hAct
    exact H.active_anchor_hit hAnch g p s hVisit
  · obtain ⟨z, hz, hzp, hz0⟩ := H.ghostStop_particle_zero_at_last hH hd g p hL (by simpa [s] using hAct)
    have hzero := H.stopAnchor_zero hAnch g p s z hz hzp hz0
    exact sub_eq_zero.mp (by simpa only [Int.cast_sub] using hzero)

theorem lifeAssignment_lifespanValid (hH : H.Valid) (hd : H.DistinctBirths)
    (hAnchor : HistoryAnchorTask) : H.toResiduePath.lifespanValid H.lifeAssignment := by
  let hAnch : ∀ i, H.AnchorInvariant i (H.before i) ∧ H.AnchorInvariant i (H.after i) :=
    hAnchor F P J m n A H hH hd
  intro g p
  by_cases hL : (H.liveVisits g p).Nonempty
  · let L := H.liveVisits g p
    let birth := L.min' hL
    let stop := L.max' hL
    have hS : H.lifeAssignment g p = some (birth, stop) := by
      simp [lifeAssignment, lifeSpan, L, birth, stop, hL]
    rw [hS]
    unfold ResiduePath.spanValid
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.min'_le L stop (Finset.max'_mem L hL)
    · intro hEmpty
      by_contra hlt
      have hsb : stop ≤ birth := not_lt.mp hlt
      have hEq : birth = stop := le_antisymm (Finset.min'_le L stop (Finset.max'_mem L hL)) hsb
      have hNoAct : p ∉ activePrimes (H.before birth).2.1 g.val := by
        intro hAct
        have hVisit := (H.activePrime_iff_visit birth g p).mp hAct
        rw [hEmpty] at hVisit
        exact Finset.notMem_empty _ hVisit
      have hBirthPending := H.first_noactive_pendingAfter hH hd g p hL (by simpa [L, birth] using hNoAct)
      have hStopNoPending := H.no_pendingAfter_max hH hd g p hL
      exact hStopNoPending (by simpa [L, birth, stop, hEq] using hBirthPending)
    · intro i hi
      have hmem : i ∈ L := H.activeVisits_subset_liveVisits (hH := hH) g p hi
      exact ⟨Finset.min'_le L i hmem, Finset.le_max' L i hmem⟩
    · have hBirth := H.firstOffset_eq_anchor hH hd hAnch g p hL
      have hStop := H.lastOffset_eq_anchor hH hd hAnch g p hL
      rw [Int.cast_sub, hStop, hBirth]
      simp
    · intro i hi
      have hBirth := H.firstOffset_eq_anchor hH hd hAnch g p hL
      have hHit := H.active_anchor_hit hAnch g p i hi
      rw [Int.cast_sub, hHit, hBirth]
      simp
  · have hS : H.lifeAssignment g p = none := by
      simp [lifeAssignment, lifeSpan, hL]
    rw [hS]
    unfold ResiduePath.spanValid
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact hL ⟨i, H.activeVisits_subset_liveVisits (hH := hH) g p hi⟩


theorem live_interval_global (hH : H.Valid) (hd : H.DistinctBirths) (p : ℕ) :
    ∀ j : Fin (n + 1), ∀ b : Fin (n + 1), b ≤ j →
      p ∈ H.birthPrefixAfter b →
      (p ∈ liveValues (H.before j) ∨ p ∈ liveValues (H.after j)) →
      ∀ k : Fin (n + 1), b ≤ k → k ≤ j →
        p ∈ liveValues (H.before k) ∨ p ∈ liveValues (H.after k) := by
  intro j
  induction j using Fin.induction with
  | zero =>
      intro b hb hp hEnd k hbk hkj
      have hb0 : b = 0 := le_antisymm hb (Fin.zero_le b)
      have hk0 : k = 0 := le_antisymm hkj (Fin.zero_le k)
      subst b
      subst k
      exact hEnd
  | succ j ih =>
      intro b hbj hp hEnd k hbk hkj
      by_cases hke : k = j.succ
      · subst k
        exact hEnd
      · have hkj' : k ≤ j.castSucc := by
          apply Fin.le_iff_val_le_val.mpr
          have hle := Fin.le_iff_val_le_val.mp hkj
          have hne : k.val ≠ j.val + 1 := by
            intro he
            apply hke
            apply Fin.ext
            simpa only [Fin.val_succ] using he
          have hbound : k.val ≤ j.val := by
            simp only [Fin.val_succ] at hle
            omega
          simpa only [Fin.val_castSucc] using hbound
        have hbj' : b ≤ j.castSucc := hbk.trans hkj'
        have hAfterPrev : p ∈ liveValues (H.after j.castSucc) := by
          rcases hEnd with hBefore | hAfter
          · exact H.edge_live_predecessor hH hd b j hbj' hp hBefore
          · have hBefore : p ∈ liveValues (H.before j.succ) :=
              H.ghost_live_predecessor hH hd b j hbj' hp hAfter
            exact H.edge_live_predecessor hH hd b j hbj' hp hBefore
        have hPrev := ih b hbj' hp (Or.inr hAfterPrev)
        exact hPrev k hbk hkj'


theorem live_before_between (hH : H.Valid) (hd : H.DistinctBirths)
    (g : P.BigGroup) (p : P.Prime g.val) (hL : (H.liveVisits g p).Nonempty)
    (i : Fin (n + 1))
    (hb : (H.liveVisits g p).min' hL ≤ i)
    (hi : i ≤ (H.liveVisits g p).max' hL)
    (hstrict : (H.liveVisits g p).min' hL < i) :
    p.val ∈ liveValues (H.before i) := by
  let b := (H.liveVisits g p).min' hL
  let s := (H.liveVisits g p).max' hL
  have hbs : b ≤ s := Finset.min'_le _ s (Finset.max'_mem _ hL)
  have hpref := H.birthPrefixAfter_at_first hH g p hL
  have hend := H.liveVisits_mem (Finset.max'_mem (H.liveVisits g p) hL)
  have hAt := H.live_interval_global hH hd p s b hbs hpref hend i (by simpa [b] using hb)
    (by simpa [s] using hi)
  rcases hAt with hBefore | hAfter
  · exact hBefore
  · exact H.ghost_live_predecessor_lt hH hd b i (by simpa [b] using hstrict) hpref hAfter

theorem live_after_before_stop (hH : H.Valid) (hd : H.DistinctBirths)
    (g : P.BigGroup) (p : P.Prime g.val) (hL : (H.liveVisits g p).Nonempty)
    (i : Fin n)
    (hb : (H.liveVisits g p).min' hL ≤ i.castSucc)
    (hi : i.castSucc < (H.liveVisits g p).max' hL) :
    p.val ∈ liveValues (H.after i.castSucc) := by
  let b := (H.liveVisits g p).min' hL
  let s := (H.liveVisits g p).max' hL
  have hbs : b ≤ s := Finset.min'_le _ s (Finset.max'_mem _ hL)
  have hpref := H.birthPrefixAfter_at_first hH g p hL
  have hend := H.liveVisits_mem (Finset.max'_mem (H.liveVisits g p) hL)
  have hnext : i.succ ≤ s := by
    apply Fin.le_iff_val_le_val.mpr
    have hlt0 := Fin.lt_iff_val_lt_val.mp (by simpa [s] using hi)
    have hlt : i.val < s.val := by simpa only [Fin.val_castSucc] using hlt0
    simpa only [Fin.val_succ] using (Nat.succ_le_of_lt hlt)
  have hAt := H.live_interval_global hH hd p s b hbs hpref hend i.succ
    (by simpa [b] using (hb.trans (Fin.castSucc_le_succ i))) (by simpa [s] using hnext)
  rcases hAt with hBefore | hAfter
  · exact H.edge_live_predecessor hH hd b i (by simpa [b] using hb) hpref hBefore
  · have hBefore : p.val ∈ liveValues (H.before i.succ) :=
      H.ghost_live_predecessor hH hd b i (by simpa [b] using hb) hpref hAfter
    exact H.edge_live_predecessor hH hd b i (by simpa [b] using hb) hpref hBefore


theorem pendingBefore_iff_memory (hH : H.Valid) (hd : H.DistinctBirths)
    (g : P.BigGroup) (p : P.Prime g.val) (i : Fin (n + 1)) :
    H.toResiduePath.pendingBefore g p (H.lifeAssignment g p) i ↔
      p ∈ pendingPrimes ((H.before i).2.2 g) := by
  by_cases hL : (H.liveVisits g p).Nonempty
  · let birth := (H.liveVisits g p).min' hL
    let stop := (H.liveVisits g p).max' hL
    have hS : H.lifeAssignment g p = some (birth, stop) := by
      simp [lifeAssignment, lifeSpan, birth, stop, hL]
    rw [hS]
    simp only [ResiduePath.pendingBefore]
    constructor
    · rintro ⟨hbi, his, hnot⟩
      have hBefore := H.live_before_between hH hd g p hL i hbi.le his hbi
      have hAct : p ∉ activePrimes (H.before i).2.1 g.val := by
        intro ha
        exact hnot ((H.activePrime_iff_visit i g p).mp ha)
      have hgroup := liveValues_mem_groupLive (H.before i) g p hBefore
      rcases Multiset.mem_add.mp hgroup with ha | hpending
      · exact (hAct ha).elim
      · exact hpending
    · intro hpending
      have hgroup : p ∈ groupLivePrimes (H.before i) g := by
        unfold groupLivePrimes
        exact Multiset.mem_add.mpr (Or.inr hpending)
      have hglobal := groupLive_mem_liveValues (H.before i) g hgroup
      have hiLive : i ∈ H.liveVisits g p :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl hglobal⟩
      have hbi : birth ≤ i := by
        exact Finset.min'_le _ _ hiLive
      have his : i ≤ stop := Finset.le_max' _ _ hiLive
      have hstrict : birth < i := by
        by_contra hn
        have heq : i = birth := le_antisymm (not_lt.mp hn) hbi
        have hnone := H.no_pendingBefore_min hH hd g p hL
        exact hnone (by simpa [birth, heq] using hpending)
      have hnd := H.liveValues_nodup_of_distinct hH hd i
      have hstruct := big_live_structure (H.before i) hnd.1 g
      have hnot : i ∉ H.toResiduePath.activeVisits g p := by
        intro hv
        have ha := (H.activePrime_iff_visit i g p).mpr hv
        exact (Multiset.disjoint_left.mp hstruct.2.2) ha hpending
      exact ⟨hstrict, his, hnot⟩
  · have hS : H.lifeAssignment g p = none := by
      simp [lifeAssignment, lifeSpan, hL]
    rw [hS]
    simp only [ResiduePath.pendingBefore]
    constructor
    · intro hfalse
      exact hfalse.elim
    · intro hpending
      have hgroup : p ∈ groupLivePrimes (H.before i) g := by
        unfold groupLivePrimes
        exact Multiset.mem_add.mpr (Or.inr hpending)
      have hglobal := groupLive_mem_liveValues (H.before i) g hgroup
      have hiLive : i ∈ H.liveVisits g p :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl hglobal⟩
      exact hL ⟨i, hiLive⟩

theorem pendingAfter_iff_memory (hH : H.Valid) (hd : H.DistinctBirths)
    (g : P.BigGroup) (p : P.Prime g.val) (i : Fin (n + 1)) :
    H.toResiduePath.pendingAfter g p (H.lifeAssignment g p) i ↔
      p ∈ pendingPrimes ((H.after i).2.2 g) := by
  by_cases hL : (H.liveVisits g p).Nonempty
  · let birth := (H.liveVisits g p).min' hL
    let stop := (H.liveVisits g p).max' hL
    have hS : H.lifeAssignment g p = some (birth, stop) := by
      simp [lifeAssignment, lifeSpan, birth, stop, hL]
    rw [hS]
    simp only [ResiduePath.pendingAfter]
    constructor
    · rintro ⟨hbi, his, hnot⟩
      have hilt : i.val < n := by
        have hlt := Fin.lt_iff_val_lt_val.mp his
        have hstop := stop.isLt
        omega
      let e : Fin n := ⟨i.val, hilt⟩
      have he : e.castSucc = i := Fin.ext rfl
      have hAfter := H.live_after_before_stop hH hd g p hL e
        (by simpa [birth, he] using hbi) (by simpa [stop, he] using his)
      have hActAfter : p ∉ activePrimes (H.after i).2.1 g.val := by
        intro ha
        have heq := (hH.2.2.1 i).2.1
        have hb : p ∈ activePrimes (H.before i).2.1 g.val := by
          simpa only [← heq] using ha
        exact hnot ((H.activePrime_iff_visit i g p).mp hb)
      have hgroup := liveValues_mem_groupLive (H.after i) g p hAfter
      rcases Multiset.mem_add.mp hgroup with ha | hpending
      · exact (hActAfter ha).elim
      · exact hpending
    · intro hpending
      have hgroup : p ∈ groupLivePrimes (H.after i) g := by
        unfold groupLivePrimes
        exact Multiset.mem_add.mpr (Or.inr hpending)
      have hglobal := groupLive_mem_liveValues (H.after i) g hgroup
      have hiLive : i ∈ H.liveVisits g p :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr hglobal⟩
      have hbi : birth ≤ i := Finset.min'_le _ _ hiLive
      have his : i ≤ stop := Finset.le_max' _ _ hiLive
      have hstrict : i < stop := by
        by_contra hn
        have heq : i = stop := le_antisymm his (not_lt.mp hn)
        have hnone := H.no_pendingAfter_max hH hd g p hL
        exact hnone (by simpa [stop, heq] using hpending)
      have hnd := H.liveValues_nodup_of_distinct hH hd i
      have hstruct := big_live_structure (H.after i) hnd.2 g
      have hnot : i ∉ H.toResiduePath.activeVisits g p := by
        intro hv
        have hb := (H.activePrime_iff_visit i g p).mpr hv
        have heq := (hH.2.2.1 i).2.1
        rw [heq] at hb
        exact (Multiset.disjoint_left.mp hstruct.2.2) hb hpending
      exact ⟨hbi, hstrict, hnot⟩
  · have hS : H.lifeAssignment g p = none := by
      simp [lifeAssignment, lifeSpan, hL]
    rw [hS]
    simp only [ResiduePath.pendingAfter]
    constructor
    · intro hfalse
      exact hfalse.elim
    · intro hpending
      have hgroup : p ∈ groupLivePrimes (H.after i) g := by
        unfold groupLivePrimes
        exact Multiset.mem_add.mpr (Or.inr hpending)
      have hglobal := groupLive_mem_liveValues (H.after i) g hgroup
      have hiLive : i ∈ H.liveVisits g p :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr hglobal⟩
      exact hL ⟨i, hiLive⟩




theorem memory_eq_anchor_map_before (i : Fin (n + 1)) (g : P.BigGroup)
    (hAnch : H.AnchorInvariant i (H.before i)) :
    (H.before i).2.2 g =
      (pendingPrimes ((H.before i).2.2 g)).map
        (fun p => (⟨p, ((H.toResiduePath.offset i - H.anchorOffset p.val : ℤ) : ZMod p.val)⟩ : P.Particle g.val)) := by
  let z := (H.before i).2.2 g
  calc
    z = (Finset.univ : Finset (Fin z.card)).val.map (memoryEntry z) :=
      (memoryEntry_enumeration z).symm
    _ = Finset.univ.val.map (fun k : Fin z.card =>
        (⟨(memoryEntry z k).1,
          ((H.toResiduePath.offset i - H.anchorOffset (memoryEntry z k).1.val : ℤ) :
            ZMod (memoryEntry z k).1.val)⟩ : P.Particle g.val)) := by
          apply Multiset.map_congr rfl
          intro k hk
          have he := hAnch.2 g (memoryEntry z k) (_root_.Erdos821.S2Core.memoryEntry_mem z k)
          exact Sigma.ext rfl (heq_of_eq he)
    _ = _ := by
      rw [_root_.Erdos821.S2Core.pendingPrimes_enumeration z, Multiset.map_map]
      rfl

theorem memory_eq_anchor_map_after (i : Fin (n + 1)) (g : P.BigGroup)
    (hAnch : H.AnchorInvariant i (H.after i)) :
    (H.after i).2.2 g =
      (pendingPrimes ((H.after i).2.2 g)).map
        (fun p => (⟨p, ((H.toResiduePath.offset i - H.anchorOffset p.val : ℤ) : ZMod p.val)⟩ : P.Particle g.val)) := by
  let z := (H.after i).2.2 g
  calc
    z = (Finset.univ : Finset (Fin z.card)).val.map (memoryEntry z) :=
      (memoryEntry_enumeration z).symm
    _ = Finset.univ.val.map (fun k : Fin z.card =>
        (⟨(memoryEntry z k).1,
          ((H.toResiduePath.offset i - H.anchorOffset (memoryEntry z k).1.val : ℤ) :
            ZMod (memoryEntry z k).1.val)⟩ : P.Particle g.val)) := by
          apply Multiset.map_congr rfl
          intro k hk
          have he := hAnch.2 g (memoryEntry z k) (_root_.Erdos821.S2Core.memoryEntry_mem z k)
          exact Sigma.ext rfl (heq_of_eq he)
    _ = _ := by
      rw [_root_.Erdos821.S2Core.pendingPrimes_enumeration z, Multiset.map_map]
      rfl

theorem pendingBeforePrimes_val_eq (hH : H.Valid) (hd : H.DistinctBirths)
    (g : P.BigGroup) (i : Fin (n + 1)) :
    (H.toResiduePath.pendingBeforePrimes H.lifeAssignment i g).val =
      pendingPrimes ((H.before i).2.2 g) := by
  have hnd : (pendingPrimes ((H.before i).2.2 g)).Nodup :=
    (big_live_structure (H.before i) (H.liveValues_nodup_of_distinct hH hd i).1 g).2.1
  have hs : H.toResiduePath.pendingBeforePrimes H.lifeAssignment i g =
      (pendingPrimes ((H.before i).2.2 g)).toFinset := by
    ext p
    simp only [ResiduePath.pendingBeforePrimes, Finset.mem_filter, Finset.mem_univ,
      true_and, Multiset.mem_toFinset]
    exact H.pendingBefore_iff_memory hH hd g p i
  rw [hs, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]

theorem pendingAfterPrimes_val_eq (hH : H.Valid) (hd : H.DistinctBirths)
    (g : P.BigGroup) (i : Fin (n + 1)) :
    (H.toResiduePath.pendingAfterPrimes H.lifeAssignment i g).val =
      pendingPrimes ((H.after i).2.2 g) := by
  have hnd : (pendingPrimes ((H.after i).2.2 g)).Nodup :=
    (big_live_structure (H.after i) (H.liveValues_nodup_of_distinct hH hd i).2 g).2.1
  have hs : H.toResiduePath.pendingAfterPrimes H.lifeAssignment i g =
      (pendingPrimes ((H.after i).2.2 g)).toFinset := by
    ext p
    simp only [ResiduePath.pendingAfterPrimes, Finset.mem_filter, Finset.mem_univ,
      true_and, Multiset.mem_toFinset]
    exact H.pendingAfter_iff_memory hH hd g p i
  rw [hs, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]

theorem memoryBefore_lifecycle_eq (hH : H.Valid) (hd : H.DistinctBirths)
    (hAnchor : HistoryAnchorTask) (i : Fin (n + 1)) (g : P.BigGroup) :
    H.toResiduePath.memoryBefore H.lifeAssignment i g = (H.before i).2.2 g := by
  let hAnch : ∀ i, H.AnchorInvariant i (H.before i) ∧ H.AnchorInvariant i (H.after i) :=
    hAnchor F P J m n A H hH hd
  calc
    H.toResiduePath.memoryBefore H.lifeAssignment i g =
        (H.toResiduePath.pendingBeforePrimes H.lifeAssignment i g).val.map
          (fun p => (⟨p, ((H.toResiduePath.offset i -
            H.toResiduePath.spanAnchor (H.lifeAssignment g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val)) :=
      H.toResiduePath.memoryBefore_eq_map H.lifeAssignment i g
    _ = (pendingPrimes ((H.before i).2.2 g)).map
          (fun p => (⟨p, ((H.toResiduePath.offset i -
            H.toResiduePath.spanAnchor (H.lifeAssignment g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val)) := by
      rw [H.pendingBeforePrimes_val_eq hH hd g i]
    _ = (pendingPrimes ((H.before i).2.2 g)).map
          (fun p => (⟨p, ((H.toResiduePath.offset i - H.anchorOffset p.val : ℤ) : ZMod p.val)⟩ : P.Particle g.val)) := by
      apply Multiset.map_congr rfl
      intro p hp
      have hBefore := (H.pendingBefore_iff_memory hH hd g p i).2 hp
      have hnon : (H.liveVisits g p).Nonempty := by
        by_contra hnon
        have hnone : H.lifeAssignment g p = none := by
          simp [lifeAssignment, lifeSpan, hnon]
        simp [hnone, ResiduePath.pendingBefore] at hBefore
      have hLifeEq : H.lifeAssignment g p =
          some ((H.liveVisits g p).min' hnon, (H.liveVisits g p).max' hnon) := by
        simp [lifeAssignment, lifeSpan, hnon]
      have hBirth := H.firstOffset_eq_anchor hH hd hAnch g p hnon
      have hRes' :
          ((H.toResiduePath.offset i - H.toResiduePath.offset ((H.liveVisits g p).min' hnon) : ℤ) : ZMod p.val) =
            ((H.toResiduePath.offset i - H.anchorOffset p.val : ℤ) : ZMod p.val) := by
        rw [Int.cast_sub, Int.cast_sub, hBirth]
      have hRes :
          ((H.toResiduePath.offset i - H.toResiduePath.spanAnchor (H.lifeAssignment g p) : ℤ) : ZMod p.val) =
            ((H.toResiduePath.offset i - H.anchorOffset p.val : ℤ) : ZMod p.val) := by
        simpa [ResiduePath.spanAnchor, hLifeEq] using hRes'
      exact Sigma.ext rfl (heq_of_eq hRes)
    _ = (H.before i).2.2 g := (H.memory_eq_anchor_map_before i g (hAnch i).1).symm

theorem memoryAfter_lifecycle_eq (hH : H.Valid) (hd : H.DistinctBirths)
    (hAnchor : HistoryAnchorTask) (i : Fin (n + 1)) (g : P.BigGroup) :
    H.toResiduePath.memoryAfter H.lifeAssignment i g = (H.after i).2.2 g := by
  let hAnch : ∀ i, H.AnchorInvariant i (H.before i) ∧ H.AnchorInvariant i (H.after i) :=
    hAnchor F P J m n A H hH hd
  calc
    H.toResiduePath.memoryAfter H.lifeAssignment i g =
        (H.toResiduePath.pendingAfterPrimes H.lifeAssignment i g).val.map
          (fun p => (⟨p, ((H.toResiduePath.offset i -
            H.toResiduePath.spanAnchor (H.lifeAssignment g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val)) :=
      H.toResiduePath.memoryAfter_eq_map H.lifeAssignment i g
    _ = (pendingPrimes ((H.after i).2.2 g)).map
          (fun p => (⟨p, ((H.toResiduePath.offset i -
            H.toResiduePath.spanAnchor (H.lifeAssignment g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val)) := by
      rw [H.pendingAfterPrimes_val_eq hH hd g i]
    _ = (pendingPrimes ((H.after i).2.2 g)).map
          (fun p => (⟨p, ((H.toResiduePath.offset i - H.anchorOffset p.val : ℤ) : ZMod p.val)⟩ : P.Particle g.val)) := by
      apply Multiset.map_congr rfl
      intro p hp
      have hAfter := (H.pendingAfter_iff_memory hH hd g p i).2 hp
      have hnon : (H.liveVisits g p).Nonempty := by
        by_contra hnon
        have hnone : H.lifeAssignment g p = none := by
          simp [lifeAssignment, lifeSpan, hnon]
        simp [hnone, ResiduePath.pendingAfter] at hAfter
      have hLifeEq : H.lifeAssignment g p =
          some ((H.liveVisits g p).min' hnon, (H.liveVisits g p).max' hnon) := by
        simp [lifeAssignment, lifeSpan, hnon]
      have hBirth := H.firstOffset_eq_anchor hH hd hAnch g p hnon
      have hRes' :
          ((H.toResiduePath.offset i - H.toResiduePath.offset ((H.liveVisits g p).min' hnon) : ℤ) : ZMod p.val) =
            ((H.toResiduePath.offset i - H.anchorOffset p.val : ℤ) : ZMod p.val) := by
        rw [Int.cast_sub, Int.cast_sub, hBirth]
      have hRes :
          ((H.toResiduePath.offset i - H.toResiduePath.spanAnchor (H.lifeAssignment g p) : ℤ) : ZMod p.val) =
            ((H.toResiduePath.offset i - H.anchorOffset p.val : ℤ) : ZMod p.val) := by
        simpa [ResiduePath.spanAnchor, hLifeEq] using hRes'
      exact Sigma.ext rfl (heq_of_eq hRes)
    _ = (H.after i).2.2 g := (H.memory_eq_anchor_map_after i g (hAnch i).2).symm

theorem lifespanClassificationTask_proof : LifespanClassificationTask := by
  intro hAnchor F P J m n A H hH hd
  refine ⟨H.lifeAssignment, H.lifeAssignment_lifespanValid hH hd hAnchor, ?_⟩
  intro i g
  exact ⟨H.memoryBefore_lifecycle_eq hH hd hAnchor i g,
    H.memoryAfter_lifecycle_eq hH hd hAnchor i g⟩

end MemoryHistory

theorem LifespanClassificationTask_proof : LifespanClassificationTask :=
  MemoryHistory.lifespanClassificationTask_proof


end Erdos821.S2Core
