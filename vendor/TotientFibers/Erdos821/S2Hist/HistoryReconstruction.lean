import Erdos821.S2.HistoryReconstructionTask

noncomputable section

namespace Erdos821.S2Hist

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
variable {A : Model F P J m} (H : MemoryHistory A n)

theorem reconstructed_before_eq
    (hH : H.Valid) (S : LifespanAssignment P n)
    (hS : H.toResiduePath.lifespanValid S)
    (hm : ∀ i g, H.toResiduePath.memoryBefore S i g = (H.before i).2.2 g ∧
      H.toResiduePath.memoryAfter S i g = (H.after i).2.2 g)
    (i : Fin (n + 1)) :
    (H.toResiduePath.reconstructedHistory S hS (H.before 0).1).before i = H.before i := by
  change H.toResiduePath.stateBefore S (H.before 0).1 i = H.before i
  apply Prod.ext
  · exact (H.small_residue_translation hH i).symm
  · apply Prod.ext
    · rfl
    · funext g
      exact (hm i g).1

theorem reconstructed_after_eq
    (hH : H.Valid) (S : LifespanAssignment P n)
    (hS : H.toResiduePath.lifespanValid S)
    (hm : ∀ i g, H.toResiduePath.memoryBefore S i g = (H.before i).2.2 g ∧
      H.toResiduePath.memoryAfter S i g = (H.after i).2.2 g)
    (i : Fin (n + 1)) :
    (H.toResiduePath.reconstructedHistory S hS (H.before 0).1).after i = H.after i := by
  change H.toResiduePath.stateAfter S (H.before 0).1 i = H.after i
  apply Prod.ext
  · exact (H.small_residue_translation hH i).symm.trans (hH.2.2.1 i).1
  · apply Prod.ext
    · exact (hH.2.2.1 i).2.1
    · funext g
      exact (hm i g).2

theorem initial_small_compatible (hn : 0 < n) (hH : H.Valid) :
    H.toResiduePath.SmallCompatible (H.before 0).1 := by
  intro i
  have hs := H.smallPhysical_before hn hH i
  rw [H.small_residue_translation hH i] at hs
  simpa [MemoryHistory.toResiduePath] using hs

def birthAddressBeforeVisit (i : Fin (n + 1)) :
    BirthAddress P (J + F.ell) n H.birthBound → Prop
  | .inl _ => True
  | .inr (.inl (e, _, _)) => e.val < i.val
  | .inr (.inr (j, _, _)) => j.val < i.val

theorem birthAddressBeforeVisit_mono (i j : Fin (n + 1)) (hij : i.val ≤ j.val)
    (a : BirthAddress P (J + F.ell) n H.birthBound)
    (ha : birthAddressBeforeVisit (H := H) i a) :
    birthAddressBeforeVisit (H := H) j a := by
  cases a with
  | inl x => trivial
  | inr a =>
    cases a with
    | inl x => exact lt_of_lt_of_le ha hij
    | inr x => exact lt_of_lt_of_le ha hij

theorem pendingPrime_mem_liveValues {M : ℕ} (s : P.MemoryState M)
    (g : P.BigGroup) (p : P.Prime g.val)
    (hp : p ∈ pendingPrimes (s.2.2 g)) : p.val ∈ liveValues s := by
  simp only [liveValues, Multiset.mem_sum, Finset.mem_univ, true_and,
    Multiset.mem_map]
  refine ⟨g, p, ?_, rfl⟩
  simp only [groupLivePrimes, Multiset.mem_add]
  exact Or.inr hp

theorem liveValue_origin_before (hH : H.Valid) (hd : H.DistinctBirths)
    (i : Fin (n + 1)) (p : ℕ) (hp : p ∈ liveValues (H.before i)) :
    ∃ a : BirthAddress P (J + F.ell) n H.birthBound,
      H.addressPerformed H.birthBound a ∧ H.addressValue H.birthBound a = p ∧
        birthAddressBeforeVisit (H := H) i a := by
  classical
  have htr : H.Truncated H.birthBound := H.distinct_truncated hH hd
  revert p
  induction i using Fin.induction with
  | zero =>
      intro p hp
      rw [H.initial_liveValues hH] at hp
      simp only [MemoryHistory.initialBirthValues, Multiset.mem_sum, Finset.mem_univ,
        true_and, Multiset.mem_sum, Finset.mem_univ, true_and,
        Multiset.mem_singleton] at hp
      obtain ⟨g, j, rfl⟩ := hp
      exact ⟨.inl (g, j), True.intro, rfl, True.intro⟩
  | succ i ih =>
      intro p hp
      have hbound : liveValues (H.before i.succ) ≤
          liveValues (H.before i.castSucc) + H.ghostBirthValues i.castSucc +
            H.freshBirthValues i := by
        calc
          _ ≤ liveValues (H.after i.castSucc) + H.freshBirthValues i :=
            H.edge_liveValues_le EdgeLiveConservationTask_proof hH i
          _ ≤ (liveValues (H.before i.castSucc) + H.ghostBirthValues i.castSucc) +
              H.freshBirthValues i :=
            add_le_add (H.ghost_liveValues_le hH i.castSucc) (le_refl _)
      have hp' := Multiset.mem_of_le hbound hp
      rcases Multiset.mem_add.mp hp' with hpOld | hpFresh
      · rcases Multiset.mem_add.mp hpOld with hpOld | hpGhost
        · obtain ⟨a, hperf, hvalue, hbefore⟩ := ih p hpOld
          exact ⟨a, hperf, hvalue,
            birthAddressBeforeVisit_mono (H := H) i.castSucc i.succ (by simp) a hbefore⟩
        · simp only [MemoryHistory.ghostBirthValues, Multiset.mem_sum, Finset.mem_univ,
            true_and, Multiset.mem_sum, Finset.mem_univ, true_and,
            Multiset.mem_singleton] at hpGhost
          obtain ⟨g, h, rfl⟩ := hpGhost
          let hB : Fin H.birthBound :=
            ⟨h.val, lt_of_lt_of_le h.isLt (H.ghostBatch_le H.birthBound htr i.castSucc g)⟩
          refine ⟨.inr (.inr (i.castSucc, g, hB)), ?_, ?_, ?_⟩
          · exact h.isLt
          · simp [MemoryHistory.addressValue, hB]
          · simp [birthAddressBeforeVisit]
      · simp only [MemoryHistory.freshBirthValues, Multiset.mem_sum, Finset.mem_univ,
          true_and, Multiset.mem_sum, Finset.mem_univ,
          true_and, Multiset.mem_singleton] at hpFresh
        obtain ⟨g, h, hh, rfl⟩ := hpFresh
        refine ⟨.inr (.inl (i, g, h)), hh, rfl, ?_⟩
        simp [birthAddressBeforeVisit]

theorem actual_ghost_birth_not_before (hH : H.Valid) (hd : H.DistinctBirths)
    (i : Fin (n + 1)) (g : P.BigGroup) (h : Fin ((H.ghost i).2.1 g).val) :
    (H.ghost i).2.2 g h ∉ pendingPrimes ((H.before i).2.2 g) := by
  classical
  intro hmem
  have hpLive := pendingPrime_mem_liveValues (H.before i) g ((H.ghost i).2.2 g h) hmem
  obtain ⟨a, haPerf, haVal, haBefore⟩ :=
    liveValue_origin_before (H := H) hH hd i _ hpLive
  have htr := H.distinct_truncated hH hd
  let hB : Fin H.birthBound :=
    ⟨h.val, lt_of_lt_of_le h.isLt (H.ghostBatch_le H.birthBound htr i g)⟩
  let a' : BirthAddress P (J + F.ell) n H.birthBound := .inr (.inr (i, g, hB))
  have ha'Perf : H.addressPerformed H.birthBound a' := h.isLt
  have ha'Val : H.addressValue H.birthBound a' = ((H.ghost i).2.2 g h).val := by
    simp [a', MemoryHistory.addressValue, hB]
  have hinj := (H.distinctBirths_iff_addresses H.birthBound htr).mp hd
  have heq := hinj
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, haPerf⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha'Perf⟩)
    (haVal.trans ha'Val.symm)
  have hbad : ¬ birthAddressBeforeVisit (H := H) i a' := by
    simp [a', birthAddressBeforeVisit]
  exact hbad (heq ▸ haBefore)

theorem memoryEntry_mem_delete_iff {g : P.Group} (z : P.Memory g)
    (B : Finset (Fin z.card)) (hz : (pendingPrimes z).Nodup)
    (i : Fin z.card) :
    memoryEntry z i ∈ deleteMemoryIndices z B ↔ i ∉ B := by
  rw [deleteMemoryIndices_eq_map]
  constructor
  · intro hi
    rcases Multiset.mem_map.mp hi with ⟨j, hj, hEntry⟩
    have hPrime : (memoryEntry z j).1 = (memoryEntry z i).1 :=
      congrArg (fun x : P.Particle g => x.1) hEntry
    have hji := memoryEntry_prime_injective z hz hPrime
    have hjVal : j ∈ (Finset.univ \ B).val := by
      simpa only [Finset.sdiff_val] using hj
    have hj' : j ∈ Finset.univ \ B := Finset.mem_val.mp hjVal
    intro hiB
    exact (Finset.mem_sdiff.mp hj').2 (hji ▸ hiB)
  · intro hi
    apply Multiset.mem_map.mpr
    refine ⟨i, ?_, rfl⟩
    have hiFin : i ∈ Finset.univ \ B :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
    have hiVal : i ∈ (Finset.univ \ B).val := Finset.mem_val.mpr hiFin
    simpa only [Finset.sdiff_val] using hiVal

theorem canonical_ghost_birth_not_before (Q : ResiduePath A n)
    (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup)
    (p : P.Prime g.val) (hp : p ∈ Q.ghostBirthPrimes S i g) :
    p ∉ pendingPrimes (Q.memoryBefore S i g) := by
  classical
  intro hmem
  rw [Q.pendingPrimes_memoryBefore] at hmem
  have hbefore : Q.pendingBefore g p (S g p) i := by
    have hfin : p ∈ Q.pendingBeforePrimes S i g := Finset.mem_val.mp hmem
    simpa [ResiduePath.pendingBeforePrimes] using hfin
  have hborn : Q.ghostBirthAt g p (S g p) i :=
    (Finset.mem_filter.mp hp).2
  cases hs : S g p with
  | none =>
      simp [ResiduePath.ghostBirthAt, hs] at hborn
  | some pair =>
      rcases pair with ⟨b, e⟩
      rw [hs] at hbefore hborn
      simp only [ResiduePath.pendingBefore, ResiduePath.ghostBirthAt] at hbefore hborn
      omega

theorem ghostChoice_selected_iff_not_target {M : ℕ}
    {s t : P.MemoryState M} (c : GhostChoice s t)
    (hc : ghostChoiceValid c) (g : P.BigGroup)
    (hsrc : (pendingPrimes (s.2.2 g)).Nodup)
    (hfresh : ∀ h : Fin (c.2.1 g).val,
      c.2.2 g h ∉ pendingPrimes (s.2.2 g))
    (i : Fin (s.2.2 g).card) :
    i ∈ c.1 g ↔ memoryEntry (s.2.2 g) i ∉ t.2.2 g := by
  classical
  let z := memoryEntry (s.2.2 g) i
  have hdelete := memoryEntry_mem_delete_iff (s.2.2 g) (c.1 g) hsrc i
  constructor
  · intro hi htarget
    have hleft : z ∈ deleteMemoryIndices (s.2.2 g) (c.1 g) +
        zeroBirthBatch (c.2.2 g) := by
      rw [(hc g).2]
      exact htarget
    rcases Multiset.mem_add.mp hleft with hdel | hbatch
    · exact (hdelete.mp hdel) hi
    · have hprime : z.1 ∈ pendingPrimes (zeroBirthBatch (c.2.2 g)) :=
        Multiset.mem_map.mpr ⟨z, hbatch, rfl⟩
      rw [pendingPrimes_birthBatch] at hprime
      simp only [Multiset.mem_sum, Finset.mem_univ, true_and,
        Multiset.mem_singleton] at hprime
      obtain ⟨j, hj⟩ := hprime
      have hsrcMem : z.1 ∈ pendingPrimes (s.2.2 g) :=
        Multiset.mem_map.mpr ⟨z, memoryEntry_mem (s.2.2 g) i, rfl⟩
      exact hfresh j (hj ▸ hsrcMem)
  · intro hnotTarget
    by_contra hnotSelected
    have hdel := hdelete.mpr hnotSelected
    have hleft : z ∈ deleteMemoryIndices (s.2.2 g) (c.1 g) +
        zeroBirthBatch (c.2.2 g) := Multiset.mem_add.mpr (Or.inl hdel)
    rw [(hc g).2] at hleft
    exact hnotTarget hleft

theorem ghostChoice_deletions_eq {M : ℕ}
    {s t : P.MemoryState M} (c d : GhostChoice s t)
    (hc : ghostChoiceValid c) (hd : ghostChoiceValid d)
    (hsrc : ∀ g : P.BigGroup, (pendingPrimes (s.2.2 g)).Nodup)
    (hfc : ∀ g h, c.2.2 g h ∉ pendingPrimes (s.2.2 g))
    (hfd : ∀ g h, d.2.2 g h ∉ pendingPrimes (s.2.2 g)) :
    c.1 = d.1 := by
  classical
  funext g
  apply Finset.ext
  intro i
  exact Iff.trans
    (ghostChoice_selected_iff_not_target c hc g (hsrc g) (hfc g) i)
    (ghostChoice_selected_iff_not_target d hd g (hsrc g) (hfd g) i).symm

theorem batch_perm_of_map_eq {α : Type*} {b₁ b₂ : ℕ}
    (p : Fin b₁ → α) (q : Fin b₂ → α) (hcount : b₁ = b₂)
    (hrange : (Finset.univ : Finset (Fin b₁)).val.map p =
      (Finset.univ : Finset (Fin b₂)).val.map q)
    (hp : Function.Injective p) (hq : Function.Injective q) :
    ∃ sigma : Equiv.Perm (Fin b₂),
      ∀ i, q (sigma i) = p (Fin.cast hcount.symm i) := by
  classical
  cases hcount
  have hmatch (i : Fin b₁) : ∃ j : Fin b₁, q j = p i := by
    have hi : p i ∈ (Finset.univ : Finset (Fin b₁)).val.map q := by
      rw [← hrange]
      exact Multiset.mem_map.mpr ⟨i, Finset.mem_val.mpr (Finset.mem_univ _), rfl⟩
    rcases Multiset.mem_map.mp hi with ⟨j, _, hqj⟩
    exact ⟨j, hqj⟩
  let f : Fin b₁ → Fin b₁ := fun i => Classical.choose (hmatch i)
  have hspec (i : Fin b₁) : q (f i) = p i := Classical.choose_spec (hmatch i)
  have hbij : Function.Bijective f := by
    constructor
    · intro i j hij
      apply hp
      calc
        p i = q (f i) := (hspec i).symm
        _ = q (f j) := congrArg q hij
        _ = p j := hspec j
    · intro j
      have hj : q j ∈ (Finset.univ : Finset (Fin b₁)).val.map p := by
        rw [hrange]
        exact Multiset.mem_map.mpr ⟨j, Finset.mem_val.mpr (Finset.mem_univ _), rfl⟩
      rcases Multiset.mem_map.mp hj with ⟨i, _, hpi⟩
      refine ⟨i, ?_⟩
      apply hq
      calc
        q (f i) = p i := hspec i
        _ = q j := hpi
  refine ⟨Equiv.ofBijective f hbij, ?_⟩
  intro i
  exact hspec i

theorem history_pending_prime_nodup (hH : H.Valid) (hd : H.DistinctBirths)
    (i : Fin (n + 1)) (g : P.BigGroup) :
    (pendingPrimes ((H.before i).2.2 g)).Nodup := by
  have hlive := H.liveValues_nodup_of_distinct hH hd i
  exact (big_live_structure (H.before i) hlive.1 g).2.1

theorem actual_ghost_batch_injective (hH : H.Valid) (hd : H.DistinctBirths)
    (i : Fin (n + 1)) (g : P.BigGroup) :
    Function.Injective ((H.ghost i).2.2 g) := by
  classical
  intro h k he
  have htr := H.distinct_truncated hH hd
  let embed (j : Fin ((H.ghost i).2.1 g).val) : Fin H.birthBound :=
    ⟨j.val, lt_of_lt_of_le j.isLt (H.ghostBatch_le H.birthBound htr i g)⟩
  let addr (j : Fin ((H.ghost i).2.1 g).val) :
      BirthAddress P (J + F.ell) n H.birthBound := .inr (.inr (i, g, embed j))
  have hperf (j : Fin ((H.ghost i).2.1 g).val) :
      H.addressPerformed H.birthBound (addr j) := by
    change (embed j).val < ((H.ghost i).2.1 g).val
    simp [embed]
  have hval (j : Fin ((H.ghost i).2.1 g).val) :
      H.addressValue H.birthBound (addr j) = ((H.ghost i).2.2 g j).val := by
    simp [addr, embed, MemoryHistory.addressValue]
  have hinj := (H.distinctBirths_iff_addresses H.birthBound htr).mp hd
  have haddr := hinj
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hperf h⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hperf k⟩)
    ((hval h).trans ((congrArg Subtype.val he).trans (hval k).symm))
  have hsum := Sum.inr.inj haddr
  have htuple := Sum.inr.inj hsum
  have hpair := congrArg Prod.snd htuple
  have hembed := congrArg Prod.snd hpair
  apply Fin.ext
  simpa [embed] using congrArg Fin.val hembed

theorem canonical_ghost_batch_injective (Q : ResiduePath A n)
    (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) :
    Function.Injective (Q.ghostBatchLabels S i g) := by
  intro h k he
  have hlist := (Q.ghostBirthPrimes S i g).nodup_toList
  have hget : (Q.ghostBirthPrimes S i g).toList.get
      ⟨h.val, by simpa using h.isLt⟩ = (Q.ghostBirthPrimes S i g).toList.get
      ⟨k.val, by simpa using k.isLt⟩ := by
    simpa [ResiduePath.ghostBatchLabels] using congrArg Subtype.val he
  have hidx := (hlist.get_inj_iff).mp hget
  apply Fin.ext
  have hvalEq := congrArg
    (fun j : Fin (Q.ghostBirthPrimes S i g).toList.length => j.val) hidx
  simpa using hvalEq

theorem ghostChoice_reorder {M : ℕ} {s t : P.MemoryState M}
    (c d : GhostChoice s t) (hc : ghostChoiceValid c) (hd : ghostChoiceValid d)
    (hsrc : ∀ g : P.BigGroup, (pendingPrimes (s.2.2 g)).Nodup)
    (hfc : ∀ g h, c.2.2 g h ∉ pendingPrimes (s.2.2 g))
    (hfd : ∀ g h, d.2.2 g h ∉ pendingPrimes (s.2.2 g))
    (hic : ∀ g, Function.Injective (c.2.2 g))
    (hid : ∀ g, Function.Injective (d.2.2 g)) :
    ∃ sigma : (g : P.BigGroup) → Equiv.Perm (Fin ((d.2.1 g).val)),
      c = reorderGhostChoice d sigma := by
  classical
  have hdelete := ghostChoice_deletions_eq c d hc hd hsrc hfc hfd
  have hcount : c.2.1 = d.2.1 := by
    funext g
    apply Fin.ext
    have hcCard := ghostChoiceValid_memory_card c hc g
    have hdCard := ghostChoiceValid_memory_card d hd g
    rw [hdelete] at hcCard
    omega
  have hbatch (g : P.BigGroup) :
      zeroBirthBatch (c.2.2 g) = zeroBirthBatch (d.2.2 g) := by
    have hsum := (hc g).2.trans ((hd g).2).symm
    rw [hdelete] at hsum
    exact add_left_cancel hsum
  have hrange (g : P.BigGroup) :
      (Finset.univ : Finset (Fin ((c.2.1 g).val))).val.map (c.2.2 g) =
        (Finset.univ : Finset (Fin ((d.2.1 g).val))).val.map (d.2.2 g) := by
    calc
      _ = ∑ h : Fin ((c.2.1 g).val), ({c.2.2 g h} : Multiset (P.Prime g.val)) :=
        (sum_singletons_eq_map Finset.univ (c.2.2 g)).symm
      _ = pendingPrimes (zeroBirthBatch (c.2.2 g)) :=
        (pendingPrimes_birthBatch (c.2.2 g)).symm
      _ = pendingPrimes (zeroBirthBatch (d.2.2 g)) :=
        congrArg (pendingPrimes (P := P)) (hbatch g)
      _ = ∑ h : Fin ((d.2.1 g).val), ({d.2.2 g h} : Multiset (P.Prime g.val)) :=
        pendingPrimes_birthBatch (d.2.2 g)
      _ = _ := sum_singletons_eq_map Finset.univ (d.2.2 g)
  have hperm (g : P.BigGroup) :
      ∃ sigma : Equiv.Perm (Fin ((d.2.1 g).val)),
        ∀ i, d.2.2 g (sigma i) =
          c.2.2 g (Fin.cast (congrArg Fin.val (congrFun hcount g)).symm i) :=
    batch_perm_of_map_eq (c.2.2 g) (d.2.2 g)
      (congrArg Fin.val (congrFun hcount g)) (hrange g) (hic g) (hid g)
  let sigma : (g : P.BigGroup) → Equiv.Perm (Fin ((d.2.1 g).val)) :=
    fun g => Classical.choose (hperm g)
  have hsigma (g : P.BigGroup) :
      ∀ i, d.2.2 g (sigma g i) =
        c.2.2 g (Fin.cast (congrArg Fin.val (congrFun hcount g)).symm i) :=
    Classical.choose_spec (hperm g)
  refine ⟨sigma, ?_⟩
  rcases c with ⟨cDel, ⟨cCount, cBatch⟩⟩
  rcases d with ⟨dDel, ⟨dCount, dBatch⟩⟩
  cases hcount
  unfold reorderGhostChoice
  apply Prod.ext
  · exact hdelete
  · apply Sigma.ext
    · rfl
    · have hbatchEq : cBatch = fun g i => dBatch g (sigma g i) := by
        funext g i
        exact (hsigma g i).symm
      exact heq_of_eq hbatchEq

theorem ghostChoice_reorder_heq {M : ℕ} {s s' t t' : P.MemoryState M}
    (hs : s = s') (ht : t = t')
    (c : GhostChoice s t) (d : GhostChoice s' t')
    (hc : ghostChoiceValid c) (hd : ghostChoiceValid d)
    (hsrc : ∀ g : P.BigGroup, (pendingPrimes (s.2.2 g)).Nodup)
    (hfc : ∀ g h, c.2.2 g h ∉ pendingPrimes (s.2.2 g))
    (hfd : ∀ g h, d.2.2 g h ∉ pendingPrimes (s'.2.2 g))
    (hic : ∀ g, Function.Injective (c.2.2 g))
    (hid : ∀ g, Function.Injective (d.2.2 g)) :
    ∃ sigma : (g : P.BigGroup) → Equiv.Perm (Fin ((d.2.1 g).val)),
      HEq c (reorderGhostChoice d sigma) := by
  cases hs
  cases ht
  obtain ⟨sigma, he⟩ := ghostChoice_reorder c d hc hd hsrc hfc hfd hic hid
  exact ⟨sigma, heq_of_eq he⟩

theorem reconstructed_ghost_reorder_exists (hH : H.Valid) (hd : H.DistinctBirths)
    (S : LifespanAssignment P n) (hS : H.toResiduePath.lifespanValid S)
    (hm : ∀ i g, H.toResiduePath.memoryBefore S i g = (H.before i).2.2 g ∧
      H.toResiduePath.memoryAfter S i g = (H.after i).2.2 g) :
    ∃ sigma : (H.toResiduePath.reconstructedHistory S hS (H.before 0).1).BatchOrders,
      ∀ i, HEq (H.ghost i)
        (reorderGhostChoice
          ((H.toResiduePath.reconstructedHistory S hS (H.before 0).1).ghost i) (sigma i)) := by
  classical
  let Q := H.toResiduePath
  let K := Q.reconstructedHistory S hS (H.before 0).1
  have hghost (i : Fin (n + 1)) :
      ∃ sigma : (g : P.BigGroup) →
          Equiv.Perm (Fin ((K.ghost i).2.1 g).val),
        HEq (H.ghost i) (reorderGhostChoice (K.ghost i) sigma) := by
    have hbefore := reconstructed_before_eq (H := H) hH S hS hm i
    have hafter := reconstructed_after_eq (H := H) hH S hS hm i
    have hsrc : ∀ g : P.BigGroup, (pendingPrimes ((H.before i).2.2 g)).Nodup :=
      fun g => history_pending_prime_nodup (H := H) hH hd i g
    have hfc : ∀ g h, (H.ghost i).2.2 g h ∉ pendingPrimes ((H.before i).2.2 g) :=
      fun g h => actual_ghost_birth_not_before (H := H) hH hd i g h
    have hfd : ∀ g h, (K.ghost i).2.2 g h ∉ pendingPrimes ((K.before i).2.2 g) := by
      intro g h
      have hpBirth : Q.ghostBatchLabels S i g h ∈ Q.ghostBirthPrimes S i g := by
        have hget : Q.ghostBatchLabels S i g h ∈
            List.ofFn (Q.ghostBatchLabels S i g) :=
          List.mem_ofFn.mpr ⟨h, rfl⟩
        rw [Q.ghostBatchLabels_enumeration] at hget
        exact Finset.mem_toList.mp hget
      change Q.ghostBatchLabels S i g h ∉ pendingPrimes (Q.memoryBefore S i g)
      exact canonical_ghost_birth_not_before Q S i g _ hpBirth
    obtain ⟨sigma, hEq⟩ := ghostChoice_reorder_heq hbefore.symm hafter.symm
      (H.ghost i) (K.ghost i)
      ((hH.2.2.1 i).2.2) (Q.reconstructedGhostChoice_valid S hS (H.before 0).1 i)
      hsrc hfc hfd
      (fun g => actual_ghost_batch_injective (H := H) hH hd i g)
      (fun g => canonical_ghost_batch_injective Q S i g)
    exact ⟨sigma, hEq⟩
  let sigma : K.BatchOrders := fun i => Classical.choose (hghost i)
  refine ⟨sigma, ?_⟩
  intro i
  exact Classical.choose_spec (hghost i)

theorem memoryHistory_eq_of_fields {H K : MemoryHistory A n}
    (hbefore : H.before = K.before) (hafter : H.after = K.after)
    (hghost : ∀ i, HEq (H.ghost i) (K.ghost i))
    (hedge : ∀ i, HEq (H.edge i) (K.edge i)) : H = K := by
  cases H with
  | mk before after ghost edge =>
    cases K with
    | mk before' after' ghost' edge' =>
      have hbefore' : before = before' := hbefore
      have hafter' : after = after' := hafter
      subst before'
      subst after'
      have hghost' : ghost = ghost' := funext fun i => eq_of_heq (hghost i)
      subst ghost'
      have hedge' : edge = edge' := funext fun i => eq_of_heq (hedge i)
      subst edge'
      rfl

theorem pendingPrimes_delete_le {g : P.Group} (z : P.Memory g)
    (B : Finset (Fin z.card)) :
    pendingPrimes (deleteMemoryIndices z B) ≤ pendingPrimes z := by
  calc
    _ ≤ pendingPrimes (deleteMemoryIndices z B) +
        B.val.map (fun k => (memoryEntry z k).1) := Multiset.le_add_right _ _
    _ = pendingPrimes z := (pendingPrimes_delete_add z B).symm

theorem activePrimes_mem_of_index {M : ℕ} (a : P.Labels M)
    (g : P.Group) (i : Fin M) : a g i ∈ activePrimes a g := by
  simp [activePrimes]

theorem slotPrimes_mem_iff {M : ℕ} {g : P.Group}
    (a : Fin M → P.Prime g) (B : Finset (Fin M)) (p : P.Prime g) :
    p ∈ slotPrimes a B ↔ ∃ i, i ∈ B ∧ a i = p := by
  rw [slotPrimes_eq_val_map]
  simp only [Multiset.mem_map, Finset.mem_val]

theorem pendingBefore_iff_pendingPrimes (Q : ResiduePath A n)
    (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup)
    (p : P.Prime g.val) (z : P.Memory g.val)
    (hmem : Q.memoryBefore S i g = z) :
    Q.pendingBefore g p (S g p) i ↔ p ∈ pendingPrimes z := by
  constructor
  · intro hp
    have hpFin : p ∈ Q.pendingBeforePrimes S i g := by
      simpa [ResiduePath.pendingBeforePrimes] using hp
    have hpCanon : p ∈ pendingPrimes (Q.memoryBefore S i g) := by
      rw [Q.pendingPrimes_memoryBefore]
      exact Finset.mem_val.mpr hpFin
    rw [hmem] at hpCanon
    exact hpCanon
  · intro hp
    have hpCanon : p ∈ pendingPrimes (Q.memoryBefore S i g) := by
      rw [hmem]
      exact hp
    rw [Q.pendingPrimes_memoryBefore] at hpCanon
    have hpFin := Finset.mem_val.mp hpCanon
    simpa [ResiduePath.pendingBeforePrimes] using hpFin

theorem pendingAfter_iff_pendingPrimes (Q : ResiduePath A n)
    (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup)
    (p : P.Prime g.val) (z : P.Memory g.val)
    (hmem : Q.memoryAfter S i g = z) :
    Q.pendingAfter g p (S g p) i ↔ p ∈ pendingPrimes z := by
  constructor
  · intro hp
    have hpFin : p ∈ Q.pendingAfterPrimes S i g := by
      simpa [ResiduePath.pendingAfterPrimes] using hp
    have hpCanon : p ∈ pendingPrimes (Q.memoryAfter S i g) := by
      rw [Q.pendingPrimes_memoryAfter]
      exact Finset.mem_val.mpr hpFin
    rw [hmem] at hpCanon
    exact hpCanon
  · intro hp
    have hpCanon : p ∈ pendingPrimes (Q.memoryAfter S i g) := by
      rw [hmem]
      exact hp
    rw [Q.pendingPrimes_memoryAfter] at hpCanon
    have hpFin := Finset.mem_val.mp hpCanon
    simpa [ResiduePath.pendingAfterPrimes] using hpFin

theorem history_edge_pending_primes_eq (hH : H.Valid) (i : Fin n) (g : P.BigGroup) :
    pendingPrimes ((H.before i.succ).2.2 g) =
      pendingPrimes (deleteMemoryIndices ((H.after i.castSucc).2.2 g)
        (retrievedIndices (H.edge i).2.2.2.2 g)) +
        slotPrimes ((permuteActive (H.edge i).1 (H.after i.castSucc)).2.1 g.val)
          ((H.edge i).2.2.2.2.1 g) := by
  have hraw : rawEdgeValid A (A.pattern (H.edge i).2.2.1) (edgeForward i)
      (H.edge i).2.2.2.1 (permuteActive (H.edge i).1 (H.after i.castSucc))
      (permuteActive (H.edge i).2.1 (H.before i.succ)) (H.edge i).2.2.2.2 :=
    (hH.2.2.2 i).1
  obtain ⟨_, _, _, _, _, hgroups⟩ := hraw
  obtain ⟨_, _, _, _, hmem⟩ := hgroups g
  simp only [permuteActive] at hmem
  have hp := congrArg (pendingPrimes (P := P) (g := g.val)) hmem
  rw [pendingPrimes_translate, pendingPrimes_add, pendingPrimes_stored] at hp
  exact hp

theorem history_edge_store_slots_eq (hH : H.Valid) (hd : H.DistinctBirths)
    (S : LifespanAssignment P n) (hS : H.toResiduePath.lifespanValid S)
    (hm : ∀ i g, H.toResiduePath.memoryBefore S i g = (H.before i).2.2 g ∧
      H.toResiduePath.memoryAfter S i g = (H.after i).2.2 g)
    (i : Fin n) :
    (H.edge i).2.2.2.2.1 = H.toResiduePath.storeSlots S i := by
  classical
  let Q := H.toResiduePath
  let c := (H.edge i).2.2.2.2
  let source := permuteActive (H.edge i).1 (H.after i.castSucc)
  let target := permuteActive (H.edge i).2.1 (H.before i.succ)
  have hsourceLabels : source.2.1 = Q.source i := by
    change P.act (H.edge i).1 (H.after i.castSucc).2.1 =
      P.act (H.edge i).1 (H.before i.castSucc).2.1
    exact congrArg (P.act (H.edge i).1) ((hH.2.2.1 i.castSucc).2.1).symm
  have hraw : rawEdgeValid A (A.pattern (H.edge i).2.2.1) (edgeForward i)
      (H.edge i).2.2.2.1 source target c := by
    simpa [source, target, c] using (hH.2.2.2 i).1
  obtain ⟨_, _, _, _, _, hgroups⟩ := hraw
  have hLiveSource : (liveValues source).Nodup := by
    rw [show liveValues source = liveValues (H.after i.castSucc) from by
      simp [source, liveValues_permActive]]
    exact (H.liveValues_nodup_of_distinct hH hd i.castSucc).2
  have hPrimeUpdate := history_edge_pending_primes_eq (H := H) hH i
  rw [hsourceLabels] at hPrimeUpdate
  apply funext
  intro g
  obtain ⟨hStoreAllowed, _, _, _, _⟩ := hgroups g
  have hSourceStruct := big_live_structure source hLiveSource g
  have hSourceDisjoint :
      Disjoint (activePrimes (Q.source i) g.val) (pendingPrimes (source.2.2 g)) := by
    rw [← hsourceLabels]
    exact hSourceStruct.2.2
  have hSourceInj : Function.Injective (Q.source i g.val) := by
    intro k l he
    apply hSourceStruct.1
    simpa [hsourceLabels] using he
  apply Finset.ext
  intro j
  have hStoreActual : j ∈ c.1 g ↔
      Q.source i g.val j ∈ pendingPrimes ((H.before i.succ).2.2 g) := by
    constructor
    · intro hj
      rw [hPrimeUpdate g]
      exact Multiset.mem_add.mpr (Or.inr
        ((slotPrimes_mem_iff (Q.source i g.val) (c.1 g) _).2 ⟨j, hj, rfl⟩))
    · intro hp
      rw [hPrimeUpdate g] at hp
      rcases Multiset.mem_add.mp hp with hpDel | hpStore
      · have hpOld : (Q.source i g.val j) ∈ pendingPrimes ((H.after i.castSucc).2.2 g) :=
          Multiset.mem_of_le (pendingPrimes_delete_le ((H.after i.castSucc).2.2 g)
            (retrievedIndices c g)) hpDel
        have hpActive : Q.source i g.val j ∈ activePrimes (Q.source i) g.val :=
          activePrimes_mem_of_index (Q.source i) g.val j
        have hNoMem := (Multiset.disjoint_left.mp hSourceDisjoint hpActive)
        exact False.elim (hNoMem hpOld)
      · obtain ⟨k, hk, hEq⟩ :=
          (slotPrimes_mem_iff (Q.source i g.val) (c.1 g) (Q.source i g.val j)).mp hpStore
        have hkj : k = j := hSourceInj hEq
        subst k
        exact hk
  have hPend := pendingBefore_iff_pendingPrimes Q S i.succ g
    (Q.source i g.val j) ((H.before i.succ).2.2 g) (hm i.succ g).1
  change j ∈ c.1 g ↔ j ∈ Q.storeSlots S i g
  rw [ResiduePath.storeSlots, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hj
    refine ⟨(hStoreAllowed j hj).1, ?_⟩
    exact hPend.mpr (hStoreActual.mp hj)
  · rintro ⟨hshared, hpending⟩
    exact hStoreActual.mpr (hPend.mp hpending)

theorem history_edge_promotion_slots_eq (hH : H.Valid) (hd : H.DistinctBirths)
    (S : LifespanAssignment P n)
    (hm : ∀ i g, H.toResiduePath.memoryBefore S i g = (H.before i).2.2 g ∧
      H.toResiduePath.memoryAfter S i g = (H.after i).2.2 g)
    (i : Fin n) :
    (H.edge i).2.2.2.2.2.1 = H.toResiduePath.promotionSlots S i := by
  classical
  let Q := H.toResiduePath
  let c := (H.edge i).2.2.2.2
  let source := permuteActive (H.edge i).1 (H.after i.castSucc)
  let target := permuteActive (H.edge i).2.1 (H.before i.succ)
  have hsourceLabels : source.2.1 = Q.source i := by
    change P.act (H.edge i).1 (H.after i.castSucc).2.1 =
      P.act (H.edge i).1 (H.before i.castSucc).2.1
    exact congrArg (P.act (H.edge i).1) ((hH.2.2.1 i.castSucc).2.1).symm
  have htargetLabels : target.2.1 = Q.target i := rfl
  have hraw : rawEdgeValid A (A.pattern (H.edge i).2.2.1) (edgeForward i)
      (H.edge i).2.2.2.1 source target c := by
    simpa [source, target, c] using (hH.2.2.2 i).1
  obtain ⟨_, _, hcompat, _, _, hgroups⟩ := hraw
  have hLiveSource : (liveValues source).Nodup := by
    rw [show liveValues source = liveValues (H.after i.castSucc) from by
      simp [source, liveValues_permActive]]
    exact (H.liveValues_nodup_of_distinct hH hd i.castSucc).2
  have hLiveTarget : (liveValues target).Nodup := by
    rw [show liveValues target = liveValues (H.before i.succ) from by
      simp [target, liveValues_permActive]]
    exact (H.liveValues_nodup_of_distinct hH hd i.succ).1
  have hPrimeUpdate := history_edge_pending_primes_eq (H := H) hH i
  rw [hsourceLabels] at hPrimeUpdate
  have hPrimeUpdate' (g : P.BigGroup) :
      pendingPrimes (target.2.2 g) =
        pendingPrimes (deleteMemoryIndices (source.2.2 g) (retrievedIndices c g)) +
          slotPrimes (Q.source i g.val) (c.1 g) := by
    simpa [source, target, c, permuteActive] using hPrimeUpdate g
  apply funext
  intro g
  obtain ⟨_, hPromotionAllowed, _, hRet, _⟩ := hgroups g
  have hSourceStruct := big_live_structure source hLiveSource g
  have hTargetStruct := big_live_structure target hLiveTarget g
  have hSourceInj : Function.Injective (Q.source i g.val) := by
    intro j k hEq
    apply hSourceStruct.1
    simpa [hsourceLabels] using hEq
  have hTargetInj : Function.Injective (Q.target i g.val) := by
    intro j k hEq
    apply hTargetStruct.1
    simpa [htargetLabels] using hEq
  have hSourceDisjoint :
      Disjoint (activePrimes (Q.source i) g.val) (pendingPrimes (source.2.2 g)) := by
    rw [← hsourceLabels]
    exact hSourceStruct.2.2
  have hTargetDisjoint :
      Disjoint (activePrimes (Q.target i) g.val) (pendingPrimes (target.2.2 g)) := by
    rw [← htargetLabels]
    exact hTargetStruct.2.2
  have hPromActual (j : Fin (J + F.ell)) :
      j ∈ c.2.1 g ↔ Q.target i g.val j ∈ pendingPrimes ((H.after i.castSucc).2.2 g) := by
    constructor
    · intro hj
      let u : {k : Fin (J + F.ell) // k ∈ c.2.1 g} := ⟨j, hj⟩
      have hEntry := (hRet u).1
      have hEntryMem := memoryEntry_mem (source.2.2 g) (c.2.2 g u)
      have hPrimeMem : (memoryEntry (source.2.2 g) (c.2.2 g u)).1 ∈
          pendingPrimes (source.2.2 g) :=
        Multiset.mem_map.mpr ⟨_, hEntryMem, rfl⟩
      rw [hEntry, htargetLabels] at hPrimeMem
      simpa [source, permuteActive] using hPrimeMem
    · intro hp
      have hpSource : Q.target i g.val j ∈ pendingPrimes (source.2.2 g) := by
        simpa [source, permuteActive] using hp
      have hUnshared : ¬ (A.pattern (H.edge i).2.2.1).shared g.val j := by
        intro hs
        have hsame : Q.source i g.val j = Q.target i g.val j := by
          calc
            _ = source.2.1 g.val j := (congrFun (congrFun hsourceLabels g.val) j).symm
            _ = target.2.1 g.val j := hcompat g.val j hs
            _ = _ := congrFun (congrFun htargetLabels g.val) j
        have hpSource : Q.source i g.val j ∈ pendingPrimes ((source.2.2 g)) := by
          rw [hsame]
          exact hpSource
        have hpActive : Q.source i g.val j ∈ activePrimes (Q.source i) g.val :=
          activePrimes_mem_of_index (Q.source i) g.val j
        exact (Multiset.disjoint_left.mp hSourceDisjoint hpActive) hpSource
      obtain ⟨k, hEntryPrime⟩ :=
        (pendingPrime_mem_iff (source.2.2 g) (Q.target i g.val j)).mp hpSource
      have hkRetrieved : k ∈ retrievedIndices c g := by
        by_contra hk
        have hEntryDelete : memoryEntry ((source.2.2 g)) k ∈
            deleteMemoryIndices (source.2.2 g) (retrievedIndices c g) :=
          (memoryEntry_mem_delete_iff ((source.2.2 g)) (retrievedIndices c g)
            hSourceStruct.2.1 k).2 hk
        have hpDelete : (memoryEntry ((source.2.2 g)) k).1 ∈
            pendingPrimes (deleteMemoryIndices (source.2.2 g) (retrievedIndices c g)) :=
          Multiset.mem_map.mpr ⟨_, hEntryDelete, rfl⟩
        have hpTarget : Q.target i g.val j ∈ pendingPrimes (target.2.2 g) := by
          rw [hPrimeUpdate' g]
          exact Multiset.mem_add.mpr (Or.inl (by simpa [hEntryPrime] using hpDelete))
        have hpTargetActive : Q.target i g.val j ∈ activePrimes (Q.target i) g.val :=
          activePrimes_mem_of_index (Q.target i) g.val j
        exact (Multiset.disjoint_left.mp hTargetDisjoint hpTargetActive) hpTarget
      change k ∈ Finset.univ.image (c.2.2 g) at hkRetrieved
      rcases Finset.mem_image.mp hkRetrieved with ⟨u, _, hidx⟩
      have hTargetEq : Q.target i g.val u.val = Q.target i g.val j := by
        calc
          _ = target.2.1 g.val u.val := (congrFun (congrFun htargetLabels g.val) u.val).symm
          _ = (memoryEntry ((source.2.2 g)) (c.2.2 g u)).1 := by
            exact (hRet u).1.symm
          _ = (memoryEntry ((source.2.2 g)) k).1 :=
            congrArg (fun a => (memoryEntry ((source.2.2 g)) a).1) hidx
          _ = Q.target i g.val j := hEntryPrime
      have huEq : u.val = j := hTargetInj hTargetEq
      simpa [huEq] using u.property
  apply Finset.ext
  intro j
  have hPendJ := pendingAfter_iff_pendingPrimes Q S i.castSucc g
    (Q.target i g.val j) ((H.after i.castSucc).2.2 g) (hm i.castSucc g).2
  have hPendFin : Q.target i g.val j ∈ Q.pendingAfterPrimes S i.castSucc g ↔
      Q.target i g.val j ∈ pendingPrimes ((H.after i.castSucc).2.2 g) := by
    exact Iff.trans (by simp [ResiduePath.pendingAfterPrimes]) hPendJ
  change j ∈ c.2.1 g ↔ j ∈ Q.promotionSlots S i g
  rw [ResiduePath.promotionSlots, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hj
    refine ⟨(hPromotionAllowed j hj), ?_⟩
    exact hPendFin.mpr (hPromActual j |>.mp hj)
  · rintro ⟨_, hpending⟩
    exact hPromActual j |>.mpr (hPendFin.mp hpending)

theorem memoryEntry_cast_eq {g : P.Group} {z w : P.Memory g} (h : z = w)
    (i : Fin z.card) :
    memoryEntry w (Fin.cast (congrArg Multiset.card h) i) = memoryEntry z i := by
  cases h
  rfl

theorem history_edge_promotion_index_eq (hH : H.Valid) (hd : H.DistinctBirths)
    (S : LifespanAssignment P n)
    (hm : ∀ i g, H.toResiduePath.memoryBefore S i g = (H.before i).2.2 g ∧
      H.toResiduePath.memoryAfter S i g = (H.after i).2.2 g)
    (hProm : ∀ i, (H.edge i).2.2.2.2.2.1 = H.toResiduePath.promotionSlots S i)
    (i : Fin n) (g : P.BigGroup)
    (j : {j : Fin (J + F.ell) // j ∈ (H.edge i).2.2.2.2.2.1 g}) :
    (H.edge i).2.2.2.2.2.2 g j =
      Fin.cast (congrArg Multiset.card (hm i.castSucc g).2)
        (H.toResiduePath.promotionIndex S i g ⟨j.val, by
          rw [← congrFun (hProm i) g]
          exact j.property⟩) := by
  classical
  let Q := H.toResiduePath
  let c := (H.edge i).2.2.2.2
  let source := permuteActive (H.edge i).1 (H.after i.castSucc)
  let target := permuteActive (H.edge i).2.1 (H.before i.succ)
  have htargetLabels : target.2.1 = Q.target i := rfl
  have hraw : rawEdgeValid A (A.pattern (H.edge i).2.2.1) (edgeForward i)
      (H.edge i).2.2.2.1 source target c := by
    simpa [source, target, c] using (hH.2.2.2 i).1
  obtain ⟨_, _, _, _, _, hgroups⟩ := hraw
  obtain ⟨_, _, _, hRet, _⟩ := hgroups g
  have hLiveSource : (liveValues source).Nodup := by
    rw [show liveValues source = liveValues (H.after i.castSucc) from by
      simp [source, liveValues_permActive]]
    exact (H.liveValues_nodup_of_distinct hH hd i.castSucc).2
  have hSourceStruct := big_live_structure source hLiveSource g
  have hjCan : j.val ∈ Q.promotionSlots S i g := by
    rw [← congrFun (hProm i) g]
    exact j.property
  let jCan : {k : Fin (J + F.ell) // k ∈ Q.promotionSlots S i g} :=
    ⟨j.val, hjCan⟩
  have hPrimeEq :
      (memoryEntry ((H.after i.castSucc).2.2 g) (c.2.2 g j)).1 =
        (memoryEntry ((H.after i.castSucc).2.2 g)
          (Fin.cast (congrArg Multiset.card (hm i.castSucc g).2)
            (Q.promotionIndex S i g jCan))).1 := by
    calc
      _ = Q.target i g.val j.val := by
        simpa [source, target, c, htargetLabels, permuteActive, Q,
          MemoryHistory.toResiduePath, ResiduePath.target] using (hRet j).1
      _ = (memoryEntry (Q.memoryAfter S i.castSucc g)
          (Q.promotionIndex S i g jCan)).1 :=
        (Q.promotionIndex_spec S i g jCan).symm
      _ = _ := by
        rw [memoryEntry_cast_eq (hm i.castSucc g).2 (Q.promotionIndex S i g jCan)]
  exact memoryEntry_prime_injective ((H.after i.castSucc).2.2 g)
    hSourceStruct.2.1 hPrimeEq

def finsetSubtypeCast {α : Type*} {s t : Finset α} (h : s = t)
    (x : {x // x ∈ s}) : {x // x ∈ t} := ⟨x.val, h ▸ x.property⟩

theorem transferChoice_heq_of_components {M : ℕ}
    {s s' : P.MemoryState M} (c : TransferChoice s) (d : TransferChoice s')
    (hMem : s.2.2 = s'.2.2) (hStore : c.1 = d.1) (hProm : c.2.1 = d.2.1)
    (hIndex : ∀ g (j : {j : Fin M // j ∈ c.2.1 g}),
      c.2.2 g j = Fin.cast (congrArg Multiset.card (congrFun hMem g)).symm
        (d.2.2 g (finsetSubtypeCast (congrFun hProm g) j))) : HEq c d := by
  rcases s with ⟨sSmall, sLabels, sMem⟩
  rcases s' with ⟨sSmall', sLabels', sMem'⟩
  rcases c with ⟨cStore, ⟨cPromotion, cIndex⟩⟩
  rcases d with ⟨dStore, ⟨dPromotion, dIndex⟩⟩
  cases hStore
  cases hProm
  cases hMem
  have hindex : cIndex = dIndex := by
    funext g j
    simpa [finsetSubtypeCast] using hIndex g j
  let IndexFamily : ((g : P.BigGroup) → Finset (Fin M)) → Type := fun B =>
    (g : P.BigGroup) → (j : {j : Fin M // j ∈ B g}) → Fin (sMem g).card
  have hmiddle : (Sigma.mk cPromotion cIndex : Sigma IndexFamily) =
      Sigma.mk cPromotion dIndex := by
    rw [hindex]
  have hchoice : (Prod.mk cStore (Sigma.mk cPromotion cIndex) :
      TransferChoice (sSmall, sLabels, sMem)) =
      Prod.mk cStore (Sigma.mk cPromotion dIndex) := congrArg (Prod.mk cStore) hmiddle
  exact heq_of_eq hchoice

theorem history_edge_transfer_choice_heq (hH : H.Valid) (hd : H.DistinctBirths)
    (S : LifespanAssignment P n) (hS : H.toResiduePath.lifespanValid S)
    (hm : ∀ i g, H.toResiduePath.memoryBefore S i g = (H.before i).2.2 g ∧
      H.toResiduePath.memoryAfter S i g = (H.after i).2.2 g)
    (i : Fin n) :
    HEq (H.edge i).2.2.2.2
      (H.toResiduePath.reconstructedTransferChoice S (H.before 0).1 i) := by
  classical
  let Q := H.toResiduePath
  let c := (H.edge i).2.2.2.2
  let d := Q.reconstructedTransferChoice S (H.before 0).1 i
  have hStore := history_edge_store_slots_eq (H := H) hH hd S hS hm i
  have hPromAll : ∀ e, (H.edge e).2.2.2.2.2.1 = Q.promotionSlots S e :=
    fun e => history_edge_promotion_slots_eq (H := H) hH hd S hm e
  have hProm := hPromAll i
  have hSourceMem : ((H.after i.castSucc).2.2) = (Q.memoryAfter S i.castSucc) := by
    funext g
    exact (hm i.castSucc g).2.symm
  have hIndex (g : P.BigGroup) (j : {j : Fin (J + F.ell) // j ∈ c.2.1 g}) :
      c.2.2 g j =
        Fin.cast (congrArg Multiset.card (congrFun hSourceMem g)).symm
          (d.2.2 g (finsetSubtypeCast (congrFun hProm g) j)) := by
    have he := history_edge_promotion_index_eq (H := H) hH hd S hm hPromAll i g j
    simpa [Q, c, d, ResiduePath.reconstructedTransferChoice, finsetSubtypeCast] using he
  exact transferChoice_heq_of_components c d hSourceMem hStore hProm hIndex

universe u v

theorem prod_heq_of_components {α α' : Type u} {β β' : Type v}
    (a : α) (b : β) (a' : α') (b' : β')
    (ha : HEq a a') (hb : HEq b b') : HEq (a, b) (a', b') := by
  cases ha
  cases hb
  rfl

theorem edgeChoice_heq_of_fields {s s' : P.MemoryState (J + F.ell)}
    (e : EdgeChoice A s) (f : EdgeChoice A s')
    (hsource : e.1 = f.1) (htarget : e.2.1 = f.2.1)
    (hpattern : e.2.2.1 = f.2.2.1) (hfree : e.2.2.2.1 = f.2.2.2.1)
    (htransfer : HEq e.2.2.2.2 f.2.2.2.2) : HEq e f :=
  prod_heq_of_components _ _ _ _ (heq_of_eq hsource)
    (prod_heq_of_components _ _ _ _ (heq_of_eq htarget)
      (prod_heq_of_components _ _ _ _ (heq_of_eq hpattern)
        (prod_heq_of_components _ _ _ _ (heq_of_eq hfree) htransfer)))

theorem history_edge_choice_heq (hH : H.Valid) (hd : H.DistinctBirths)
    (S : LifespanAssignment P n) (hS : H.toResiduePath.lifespanValid S)
    (hm : ∀ i g, H.toResiduePath.memoryBefore S i g = (H.before i).2.2 g ∧
      H.toResiduePath.memoryAfter S i g = (H.after i).2.2 g)
    (i : Fin n) :
    HEq (H.edge i)
      ((H.toResiduePath.reconstructedHistory S hS (H.before 0).1).edge i) := by
  have htransfer := history_edge_transfer_choice_heq (H := H) hH hd S hS hm i
  exact edgeChoice_heq_of_fields (H.edge i)
    ((H.toResiduePath.reconstructedHistory S hS (H.before 0).1).edge i)
    rfl rfl rfl rfl htransfer

theorem HistoryReconstructionTask_proof : HistoryReconstructionTask := by
  classical
  intro hClass hAnchor F P J m n A H hn hH hd hk
  let Q := H.toResiduePath
  obtain ⟨S, hS, hm⟩ := hClass hAnchor F P J m n A H hH hd
  have hy := initial_small_compatible (H := H) hn hH
  let K := Q.reconstructedHistory S hS (H.before 0).1
  have hbefore : K.before = H.before := funext fun i =>
    reconstructed_before_eq (H := H) hH S hS hm i
  have hafter : K.after = H.after := funext fun i =>
    reconstructed_after_eq (H := H) hH S hS hm i
  obtain ⟨sigma, hGhost⟩ :=
    reconstructed_ghost_reorder_exists (H := H) hH hd S hS hm
  let K' := K.reorderBatches sigma
  have hbefore' : H.before = K'.before := by
    simpa [K', MemoryHistory.reorderBatches] using hbefore.symm
  have hafter' : H.after = K'.after := by
    simpa [K', MemoryHistory.reorderBatches] using hafter.symm
  have hghost' : ∀ i, HEq (H.ghost i) (K'.ghost i) := by
    intro i
    simpa [K', MemoryHistory.reorderBatches] using hGhost i
  have hedge' : ∀ i, HEq (H.edge i) (K'.edge i) := by
    intro i
    simpa [K', MemoryHistory.reorderBatches] using
      (history_edge_choice_heq (H := H) hH hd S hS hm i)
  refine ⟨S, hS, hy, ⟨sigma, ?_⟩⟩
  exact memoryHistory_eq_of_fields hbefore' hafter' hghost' hedge'


end Erdos821.S2Hist

end
