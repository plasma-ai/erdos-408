import Erdos821.S2.SpanEdgeMemoryTask
import Erdos821.S2.PhysicalCompatibility
import Erdos821.S2.HistoryProjection

set_option autoImplicit false

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- Stored memory as a finset map. -/
theorem storedMemory_eq_map {M : ℕ} {g : P.Group} (a : Fin M → P.Prime g)
    (B : Finset (Fin M)) :
    storedMemory (P := P) a B =
      B.val.map (fun i => (⟨a i, 0⟩ : P.Particle g)) := by
  unfold storedMemory
  have h : ((B.toList.map (fun i => (⟨a i, 0⟩ : P.Particle g))) : Multiset (P.Particle g))
      = B.val.map (fun i => (⟨a i, 0⟩ : P.Particle g)) := by
    rw [← Multiset.map_coe, Finset.coe_toList]
  exact h

/-- Translation distributes over addition. -/
theorem translateMemory_add (delta : ℤ) {g : P.Group} (a b : P.Memory g) :
    translateMemory delta (a + b) = translateMemory delta a + translateMemory delta b := by
  unfold translateMemory
  rw [Multiset.map_add]

/-- Translation of a finset map. -/
theorem translateMemory_map (delta : ℤ) {g : P.Group} {α : Type*}
    (s : Finset α) (f : α → P.Particle g) :
    translateMemory delta (s.val.map f) = s.val.map (fun x => translateParticle delta (f x)) := by
  simp only [translateMemory, Multiset.map_map, Function.comp_def]

/-- The two cover conditions across one edge coincide. -/
theorem edge_cover_iff_aux {n : ℕ} (i : Fin n) (birth stop : Fin (n + 1)) :
    (birth ≤ i.castSucc ∧ i.castSucc < stop) ↔
      (birth < i.succ ∧ i.succ ≤ stop) := by
  simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, by omega⟩

namespace ResiduePath

variable {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n)

/-- Source labels cover exactly the active visit at `castSucc`. -/
theorem source_active_iff (i : Fin n) (g : P.BigGroup) (p : P.Prime g.val) :
    (∃ j : Fin (J + F.ell), Q.source i g.val j = p) ↔
      i.castSucc ∈ Q.activeVisits g p := by
  simp only [activeVisits, ResiduePath.source, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨(Q.sourcePerm i g.val) j, hj⟩
  · rintro ⟨j₀, hj₀⟩
    refine ⟨(Q.sourcePerm i g.val).symm j₀, ?_⟩
    have he : (Q.sourcePerm i g.val) ((Q.sourcePerm i g.val).symm j₀) = j₀ :=
      Equiv.apply_symm_apply _ _
    simp only [PrimeGroups.act] at hj₀ ⊢
    rw [he]
    exact hj₀

/-- Target labels cover exactly the active visit at `succ`. -/
theorem target_active_iff (i : Fin n) (g : P.BigGroup) (p : P.Prime g.val) :
    (∃ j : Fin (J + F.ell), Q.target i g.val j = p) ↔
      i.succ ∈ Q.activeVisits g p := by
  simp only [activeVisits, ResiduePath.target, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨(Q.targetPerm i g.val) j, hj⟩
  · rintro ⟨j₀, hj₀⟩
    refine ⟨(Q.targetPerm i g.val).symm j₀, ?_⟩
    have he : (Q.targetPerm i g.val) ((Q.targetPerm i g.val).symm j₀) = j₀ :=
      Equiv.apply_symm_apply _ _
    simp only [PrimeGroups.act] at hj₀ ⊢
    rw [he]
    exact hj₀

/-- Birth bound below `succ` is the same as below-or-equal `castSucc`. -/
theorem birth_lt_succ_iff (i : Fin n) (birth : Fin (n + 1)) :
    birth < i.succ ↔ birth ≤ i.castSucc := by
  rw [Fin.lt_def, Fin.le_def, Fin.val_succ, Fin.val_castSucc]
  omega

/-- `castSucc` strictly below `stop` is the same as `succ` below-or-equal `stop`. -/
theorem castSucc_lt_stop_iff (i : Fin n) (stop : Fin (n + 1)) :
    i.castSucc < stop ↔ i.succ ≤ stop := by
  rw [Fin.lt_def, Fin.le_def, Fin.val_succ, Fin.val_castSucc]
  omega

/-- The two cover conditions across one edge coincide. -/
theorem edge_cover_iff (i : Fin n) (birth stop : Fin (n + 1)) :
    (birth ≤ i.castSucc ∧ i.castSucc < stop) ↔
      (birth < i.succ ∧ i.succ ≤ stop) :=
  edge_cover_iff_aux i birth stop

/-- When neither endpoint is active, pending before/after coincide. -/
theorem pending_edge_iff_inactive (S : LifespanAssignment P n) (i : Fin n)
    (g : P.BigGroup) (p : P.Prime g.val)
    (h0 : i.castSucc ∉ Q.activeVisits g p) (h1 : i.succ ∉ Q.activeVisits g p) :
    Q.pendingAfter g p (S g p) i.castSucc ↔
      Q.pendingBefore g p (S g p) i.succ := by
  rcases he : S g p with _ | ⟨birth, stop⟩
  · simp only [pendingAfter, pendingBefore]
  · simp only [pendingAfter, pendingBefore, h0, h1, not_false_eq_true,
      and_true]
    exact edge_cover_iff_aux i birth stop

/-- Active at `castSucc` forbids pending-after there. -/
theorem not_pendingAfter_of_active (i : Fin n) (g : P.BigGroup) (p : P.Prime g.val)
    (span : PrimeSpan n) (h : i.castSucc ∈ Q.activeVisits g p) :
    ¬ Q.pendingAfter g p span i.castSucc := by
  rcases span with _ | ⟨birth, stop⟩
  · exact not_false
  · simp only [pendingAfter]
    rintro ⟨_, _, hnot⟩
    exact hnot h

/-- Active at `succ` forbids pending-before there. -/
theorem not_pendingBefore_of_active (i : Fin n) (g : P.BigGroup) (p : P.Prime g.val)
    (span : PrimeSpan n) (h : i.succ ∈ Q.activeVisits g p) :
    ¬ Q.pendingBefore g p span i.succ := by
  rcases span with _ | ⟨birth, stop⟩
  · exact not_false
  · simp only [pendingBefore]
    rintro ⟨_, _, hnot⟩
    exact hnot h

/-- Pending-after implies inactive at that visit. -/
theorem pendingAfter_not_active (S : LifespanAssignment P n) (i : Fin (n + 1))
    (g : P.BigGroup) (p : P.Prime g.val)
    (h : Q.pendingAfter g p (S g p) i) : i ∉ Q.activeVisits g p := by
  rcases he : S g p with _ | ⟨birth, stop⟩
  · rw [he] at h
    simp only [pendingAfter] at h
  · rw [he] at h
    simp only [pendingAfter] at h
    exact h.2.2

/-- Pending-before implies inactive at that visit. -/
theorem pendingBefore_not_active (S : LifespanAssignment P n) (i : Fin (n + 1))
    (g : P.BigGroup) (p : P.Prime g.val)
    (h : Q.pendingBefore g p (S g p) i) : i ∉ Q.activeVisits g p := by
  rcases he : S g p with _ | ⟨birth, stop⟩
  · rw [he] at h
    simp only [pendingBefore] at h
  · rw [he] at h
    simp only [pendingBefore] at h
    exact h.2.2

/-- A prime active at both endpoints occupies one shared canonical slot.
Uses `p ∤ k` to force `p ∣ D`. -/
theorem double_active_shared (S : LifespanAssignment P n)
    (hq : Q.Valid) (hS : Q.lifespanValid S)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (i : Fin n) (g : P.BigGroup) (p : P.Prime g.val)
    (h0 : i.castSucc ∈ Q.activeVisits g p) (h1 : i.succ ∈ Q.activeVisits g p) :
    ∃ j : Fin (J + F.ell),
      Q.source i g.val j = p ∧ Q.target i g.val j = p ∧
        (A.pattern (Q.pattern i)).shared g.val j := by
  -- unique source/target witnesses
  obtain ⟨js, hjs⟩ := (Q.source_active_iff i g p).mpr h0
  obtain ⟨jt, hjt⟩ := (Q.target_active_iff i g p).mpr h1
  -- span must be `some`, since `none` forces empty active visits
  have hSome : ∃ birth stop : Fin (n + 1), S g p = some (birth, stop) := by
    rcases he : S g p with _ | ⟨birth, stop⟩
    · exfalso
      have hAV := hS g p
      rw [he] at hAV
      simp only [spanValid] at hAV
      rw [hAV] at h0
      exact Finset.notMem_empty _ h0
    · exact ⟨_, _, rfl⟩
  obtain ⟨birth, stop, heSpan⟩ := hSome
  have hSpan := hS g p
  rw [heSpan] at hSpan
  obtain ⟨hle, _, hbound, hstop, hhit⟩ := hSpan
  have h0hit : ((Q.offset i.castSucc - Q.offset birth : ℤ) : ZMod p.val) = 0 :=
    hhit _ h0
  have h1hit : ((Q.offset i.succ - Q.offset birth : ℤ) : ZMod p.val) = 0 :=
    hhit _ h1
  have hOff : Q.offset i.succ = Q.offset i.castSucc + Q.step i :=
    residuePath_offset_succ Q i
  have hStepZero : ((Q.step i : ℤ) : ZMod p.val) = 0 := by
    have he : (Q.offset i.succ - Q.offset birth : ℤ) =
        (Q.offset i.castSucc - Q.offset birth : ℤ) + Q.step i := by
      rw [hOff]; ring
    have hcast : ((Q.offset i.succ - Q.offset birth : ℤ) : ZMod p.val) =
        ((Q.offset i.castSucc - Q.offset birth : ℤ) : ZMod p.val) +
          ((Q.step i : ℤ) : ZMod p.val) := by
      rw [he, Int.cast_add]
    rw [h0hit, h1hit] at hcast
    simpa using hcast.symm
  have hDvdStep : (p.val : ℤ) ∣ Q.step i :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hStepZero
  -- unfold the step into `± k * D`
  set ν := A.pattern (Q.pattern i) with hν
  set Dnat := ν.D (Q.source i) (Q.free i) with hD
  have hStepEq : Q.step i =
      if edgeForward i then A.k * (Dnat : ℤ) else -(A.k * (Dnat : ℤ)) := by
    simp only [ResiduePath.step, edgeDelta, hν, hD]
  have hDvdKD : (p.val : ℤ) ∣ A.k * (Dnat : ℤ) := by
    rw [hStepEq] at hDvdStep
    by_cases hf : edgeForward i = true
    · simp only [hf] at hDvdStep
      exact hDvdStep
    · simp only [hf] at hDvdStep
      exact dvd_neg.mp hDvdStep
  have hPrimeNat : Nat.Prime p.val := P.prime g.val p.val p.property
  have hPrimeInt : Prime (p.val : ℤ) := Nat.prime_iff_prime_int.mp hPrimeNat
  have hOr := (Prime.dvd_mul hPrimeInt).mp hDvdKD
  have hDvdDInt : (p.val : ℤ) ∣ (Dnat : ℤ) := by
    rcases hOr with h | h
    · exfalso
      exact hk g p h
    · exact h
  have hDvdD : p.val ∣ Dnat := (Int.natCast_dvd_natCast).mp hDvdDInt
  -- shared slot via physical compatibility
  have hSrcInj : ∀ gg : P.Group, Function.Injective (Q.source i gg) :=
    fun gg => Q.source_injective hq i gg
  have hCompat := (hq.2 i).1
  have hBan := (hq.2 i).2
  have heVal : (Q.source i g.val js).val = p.val := congrArg Subtype.val hjs
  have hDvdSrc : (Q.source i g.val js).val ∣ ν.D (Q.source i) (Q.free i) := by
    rw [heVal]
    exact hDvdD
  have hSharedS : ν.shared g.val js :=
    (source_label_dvd_D_iff ν (Q.source i) (Q.target i) (Q.free i)
      hSrcInj hBan g.val js).mp hDvdSrc
  have hEqS : Q.source i g.val js = Q.target i g.val js :=
    hCompat g.val js hSharedS
  have hTgtJs' : Q.target i g.val js = p := by rw [← hEqS, hjs]
  exact ⟨js, hjs, hTgtJs', hSharedS⟩

end ResiduePath

theorem SpanEdgeMemoryTask_proof : SpanEdgeMemoryTask := by
  intro F P J m n A Q S hValid hLife hk i g
  -- abbreviations
  set i0 : Fin (n + 1) := i.castSucc with hi0
  set i1 : Fin (n + 1) := i.succ with hi1
  set off0 : ℤ := Q.offset i0 with hoff0
  set off1 : ℤ := Q.offset i1 with hoff1
  set delta : ℤ := Q.step i with hdelta
  have hOff : off1 = off0 + delta := residuePath_offset_succ Q i
  have hSrcInj : Function.Injective (Q.source i g.val) :=
    Q.source_injective hValid i g.val
  have hTgtInj : Function.Injective (Q.target i g.val) :=
    Q.target_injective hValid i g.val
  have hCompat : (A.pattern (Q.pattern i)).compatible (Q.source i) (Q.target i) :=
    (hValid.2 i).1
  have hBan : (A.pattern (Q.pattern i)).ban (Q.source i) (Q.target i) (Q.free i) :=
    (hValid.2 i).2
  -- memories and slots
  set memAfter : P.Memory g.val := Q.memoryAfter S i0 g with hmemAfter
  set memBeforeNext : P.Memory g.val := Q.memoryBefore S i1 g with hmemBefore
  set store : Finset (Fin (J + F.ell)) := Q.storeSlots S i g with hstore
  set prom : Finset (Fin (J + F.ell)) := Q.promotionSlots S i g with hprom
  set Pafter : Finset (P.Prime g.val) := Q.pendingAfterPrimes S i0 g with hPafter
  set Pbefore : Finset (P.Prime g.val) := Q.pendingBeforePrimes S i1 g with hPbefore
  -- Nodup of pending primes
  have hAfterNodup : (pendingPrimes memAfter).Nodup := by
    rw [hmemAfter, Q.pendingPrimes_memoryAfter]
    exact Finset.nodup _
  have hPrimeInj : Function.Injective
      (fun k : Fin memAfter.card => (memoryEntry memAfter k).1) :=
    memoryEntry_prime_injective memAfter hAfterNodup
  -- embeddings for image finsets
  set srcEmb : Fin (J + F.ell) ↪ P.Prime g.val := ⟨Q.source i g.val, hSrcInj⟩ with hsrcEmb
  set tgtEmb : Fin (J + F.ell) ↪ P.Prime g.val := ⟨Q.target i g.val, hTgtInj⟩ with htgtEmb
  set StoreVals : Finset (P.Prime g.val) := store.map srcEmb with hStoreVals
  set PromVals : Finset (P.Prime g.val) := prom.map tgtEmb with hPromVals
  -- particle maps
  set f0 : P.Prime g.val → P.Particle g.val :=
    fun p => (⟨p, ((off0 - Q.spanAnchor (S g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val) with hf0
  set f1 : P.Prime g.val → P.Particle g.val :=
    fun p => (⟨p, ((off1 - Q.spanAnchor (S g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val) with hf1
  have hmemAfterEq : memAfter = Pafter.val.map f0 := Q.memoryAfter_eq_map S i0 g
  have hmemBeforeEq : memBeforeNext = Pbefore.val.map f1 := Q.memoryBefore_eq_map S i1 g
  -- retrieved indices
  set TR : TransferChoice (Q.stateAfter S (fun _ _ => 0) i0) :=
    Q.reconstructedTransferChoice S (fun _ _ => 0) i with hTR
  have hRdef : retrievedIndices TR g = Finset.univ.image (Q.promotionIndex S i g) := rfl
  -- promotion prime membership
  have hPromMem : ∀ j : {j : Fin (J + F.ell) // j ∈ prom},
      Q.target i g.val j.val ∈ pendingPrimes memAfter :=
    fun j => Q.promotion_prime_mem S i g j
  -- Step 1: PromVals ⊆ Pafter, StoreVals ⊆ Pbefore
  have hPromSub : PromVals ⊆ Pafter := by
    intro p hp
    obtain ⟨j, hjProm, heq⟩ := Finset.mem_map.mp hp
    have hTgtMem : Q.target i g.val j ∈ Pafter :=
      (Finset.mem_filter.mp hjProm).2.2
    -- heq : tgtEmb j = p, i.e. target j = p
    have heq' : Q.target i g.val j = p := heq
    rw [← heq']
    exact hTgtMem
  have hStoreSub : StoreVals ⊆ Pbefore := by
    intro p hp
    obtain ⟨j, hjStore, heq⟩ := Finset.mem_map.mp hp
    have hPend : Q.pendingBefore g (Q.source i g.val j) (S g (Q.source i g.val j)) i1 :=
      (Finset.mem_filter.mp hjStore).2.2
    have hMem : Q.source i g.val j ∈ Pbefore := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hPend⟩
    have heq' : Q.source i g.val j = p := heq
    rw [← heq']
    exact hMem
  -- Step 2: promotion/store values are exactly single-active pending primes
  -- If `p ∈ Pafter` and active next, then its target slot is unshared, hence in `prom`.
  have hPromOfActive : ∀ p : P.Prime g.val,
      p ∈ Pafter → i1 ∈ Q.activeVisits g p → p ∈ PromVals := by
    intro p hPafterMem hActive
    obtain ⟨j, hjt⟩ := (Q.target_active_iff i g p).mpr hActive
    have hTgtMem : Q.target i g.val j ∈ Pafter := hjt ▸ hPafterMem
    -- unshared: shared would force source active, contradicting `p ∈ Pafter`
    have hNotShared : ¬ (A.pattern (Q.pattern i)).shared g.val j := by
      intro hSh
      have hEq : Q.source i g.val j = Q.target i g.val j :=
        hCompat g.val j hSh
      rw [hjt] at hEq
      have hSrcActive : i0 ∈ Q.activeVisits g p := by
        rw [← hEq]
        exact Q.source_activeVisit i g j
      have hNot : i0 ∉ Q.activeVisits g p :=
        Q.pendingAfter_not_active S i0 g p (Finset.mem_filter.mp hPafterMem).2
      exact hNot hSrcActive
    have hjProm : j ∈ prom := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hNotShared, hTgtMem⟩
    apply Finset.mem_map.mpr
    exact ⟨j, hjProm, hjt⟩
  -- If `p ∈ Pbefore` and active before, then its source slot is unshared, hence in `store`.
  have hStoreOfActive : ∀ p : P.Prime g.val,
      p ∈ Pbefore → i0 ∈ Q.activeVisits g p → p ∈ StoreVals := by
    intro p hPbeforeMem hActive
    obtain ⟨j, hjs⟩ := (Q.source_active_iff i g p).mpr hActive
    have hPend : Q.pendingBefore g (Q.source i g.val j) (S g (Q.source i g.val j)) i1 := by
      rw [hjs]
      exact (Finset.mem_filter.mp hPbeforeMem).2
    have hNotShared : ¬ (A.pattern (Q.pattern i)).shared g.val j := by
      intro hSh
      have hEq : Q.source i g.val j = Q.target i g.val j :=
        hCompat g.val j hSh
      rw [hjs] at hEq
      have hTgtActive : i1 ∈ Q.activeVisits g p := by
        rw [hEq]
        exact Q.target_activeVisit i g j
      have hNot : i1 ∉ Q.activeVisits g p :=
        Q.pendingBefore_not_active S i1 g p (Finset.mem_filter.mp hPbeforeMem).2
      exact hNot hTgtActive
    have hjStore : j ∈ store := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hNotShared, hPend⟩
    apply Finset.mem_map.mpr
    exact ⟨j, hjStore, hjs⟩
  -- Step 3: characterizations via active visits
  have hPromIff : ∀ p : P.Prime g.val,
      p ∈ PromVals ↔ (p ∈ Pafter ∧ i1 ∈ Q.activeVisits g p) := by
    intro p
    constructor
    · intro hp
      obtain ⟨j, hjProm, heq⟩ := Finset.mem_map.mp hp
      have hTgtEq : Q.target i g.val j = p := heq
      have hPafterMem : Q.target i g.val j ∈ Pafter :=
        (Finset.mem_filter.mp hjProm).2.2
      have hP : p ∈ Pafter := hTgtEq ▸ hPafterMem
      have hAct : i1 ∈ Q.activeVisits g p := hTgtEq ▸ Q.target_activeVisit i g j
      exact ⟨hP, hAct⟩
    · rintro ⟨hP, hAct⟩
      exact hPromOfActive p hP hAct
  have hStoreIff : ∀ p : P.Prime g.val,
      p ∈ StoreVals ↔ (p ∈ Pbefore ∧ i0 ∈ Q.activeVisits g p) := by
    intro p
    constructor
    · intro hp
      obtain ⟨j, hjStore, heq⟩ := Finset.mem_map.mp hp
      have hSrcEq : Q.source i g.val j = p := heq
      have hPend : Q.pendingBefore g (Q.source i g.val j) (S g (Q.source i g.val j)) i1 :=
        (Finset.mem_filter.mp hjStore).2.2
      have hP : p ∈ Pbefore := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hSrcEq ▸ hPend⟩
      have hAct : i0 ∈ Q.activeVisits g p := hSrcEq ▸ Q.source_activeVisit i g j
      exact ⟨hP, hAct⟩
    · rintro ⟨hP, hAct⟩
      exact hStoreOfActive p hP hAct
  -- Step 4: pending-before splits into survivors plus stores
  have hPbeforeEq : Pbefore = (Pafter \ PromVals) ∪ StoreVals := by
    ext p
    constructor
    · intro hPmem
      have hPendBefore := (Finset.mem_filter.mp hPmem).2
      have hNot1 : i1 ∉ Q.activeVisits g p :=
        Q.pendingBefore_not_active S i1 g p hPendBefore
      by_cases h0 : i0 ∈ Q.activeVisits g p
      · -- active before: a store
        have hStoreMem := hStoreOfActive p hPmem h0
        exact Finset.mem_union.mpr (Or.inr hStoreMem)
      · -- inactive both: a survivor
        have hPendAfter : Q.pendingAfter g p (S g p) i0 :=
          (Q.pending_edge_iff_inactive S i g p h0 hNot1).mpr hPendBefore
        have hPafterMem : p ∈ Pafter := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hPendAfter⟩
        have hNotProm : p ∉ PromVals := by
          intro hProm
          obtain ⟨_, hAct⟩ := (hPromIff p).mp hProm
          exact hNot1 hAct
        have hSurv : p ∈ Pafter \ PromVals :=
          Finset.mem_sdiff.mpr ⟨hPafterMem, hNotProm⟩
        exact Finset.mem_union.mpr (Or.inl hSurv)
    · intro hMem
      rcases Finset.mem_union.mp hMem with hSurv | hStore
      · -- survivor: pending-after + inactive both gives pending-before
        have hPafterMem := (Finset.mem_sdiff.mp hSurv).1
        have hNotProm := (Finset.mem_sdiff.mp hSurv).2
        have hPendAfter := (Finset.mem_filter.mp hPafterMem).2
        have hNot0 : i0 ∉ Q.activeVisits g p :=
          Q.pendingAfter_not_active S i0 g p hPendAfter
        -- must be inactive next, else promotion
        have hNot1 : i1 ∉ Q.activeVisits g p := by
          by_contra hAct
          exact hNotProm (hPromOfActive p hPafterMem hAct)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Q.pending_edge_iff_inactive S i g p hNot0 hNot1).mp hPendAfter⟩
      · exact hStoreSub hStore
  have hDisj : Disjoint (Pafter \ PromVals) StoreVals := by
    apply Finset.disjoint_left.mpr
    intro p hSurv hStore
    have hPafterMem := (Finset.mem_sdiff.mp hSurv).1
    have hPendAfter := (Finset.mem_filter.mp hPafterMem).2
    have hNot0 : i0 ∉ Q.activeVisits g p :=
      Q.pendingAfter_not_active S i0 g p hPendAfter
    obtain ⟨_, hAct⟩ := (hStoreIff p).mp hStore
    exact hNot0 hAct
  -- Step 5: retrieved indices are exactly the promotion-prime indices
  have hRetFilter : retrievedIndices TR g =
      Finset.univ.filter (fun k : Fin memAfter.card =>
        (memoryEntry memAfter k).1 ∈ PromVals) := by
    ext k
    constructor
    · intro hkMem
      obtain ⟨a, _, haEq⟩ := Finset.mem_image.mp (hRdef ▸ hkMem)
      -- a : {j // j ∈ prom}, promotionIndex a = k
      have hPrimeEq : (memoryEntry memAfter k).1 = Q.target i g.val a.val := by
        rw [← haEq]
        exact Q.promotionIndex_spec S i g a
      have hProm : Q.target i g.val a.val ∈ PromVals := by
        apply Finset.mem_map.mpr
        exact ⟨a.val, a.property, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hPrimeEq ▸ hProm⟩
    · intro hkMem
      have hkPrime : (memoryEntry memAfter k).1 ∈ PromVals :=
        (Finset.mem_filter.mp hkMem).2
      obtain ⟨j, hjProm, heq⟩ := Finset.mem_map.mp hkPrime
      -- heq : target j = prime k
      have hi : (memoryEntry memAfter k).1 = Q.target i g.val j := heq.symm
      have hmemHp : Q.target i g.val j ∈ pendingPrimes memAfter :=
        Q.promotion_prime_mem S i g ⟨j, hjProm⟩
      have hUniq : Q.promotionIndex S i g ⟨j, hjProm⟩ = k :=
        primeIndex_unique memAfter hAfterNodup _ hmemHp k hi
      apply hRdef ▸ Finset.mem_image.mpr
      exact ⟨⟨j, hjProm⟩, Finset.mem_univ _, hUniq⟩
  -- Step 6: deletion keeps exactly the surviving pending primes (via index-prime bijection)
  -- Every old index particle equals `f0` of its prime.
  have hEntryEq : ∀ k : Fin memAfter.card,
      memoryEntry memAfter k = f0 ((memoryEntry memAfter k).1) := by
    intro k
    have hmem := memoryEntry_mem memAfter k
    obtain ⟨p, hpPafter, heq⟩ := Q.memoryAfter_member_form S i0 g _ hmem
    -- heq : memoryEntry k = ⟨p, ...⟩, which is `f0 p` up to `off0`/`f0` set equations.
    have heqF0 : memoryEntry memAfter k = f0 p := by
      rw [heq]
    have hPrime : p = (memoryEntry memAfter k).1 := by
      rw [heqF0]
    calc memoryEntry memAfter k = f0 p := heqF0
      _ = f0 ((memoryEntry memAfter k).1) := by rw [← hPrime]
  -- Prime projection is a bijection `univ → Pafter`.
  set primeEmb : Fin memAfter.card ↪ P.Prime g.val :=
    ⟨fun k => (memoryEntry memAfter k).1, hPrimeInj⟩ with hprimeEmb
  have hUnivMap : Finset.univ.map primeEmb = Pafter := by
    ext p
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, heq⟩
      -- prime k = p, need p ∈ Pafter (since prime k ∈ Pafter via pendingPrimes)
      have hPrimeMem : (memoryEntry memAfter k).1 ∈ Pafter := by
        have hpend : (memoryEntry memAfter k).1 ∈ pendingPrimes memAfter := by
          apply Multiset.mem_map.mpr
          exact ⟨memoryEntry memAfter k, memoryEntry_mem memAfter k, rfl⟩
        rw [Q.pendingPrimes_memoryAfter] at hpend
        exact hpend
      exact heq ▸ hPrimeMem
    · intro hPafterMem
      -- p ∈ Pafter = pendingPrimes, so ∃ k with prime k = p
      have hpend : p ∈ pendingPrimes memAfter := by
        rw [Q.pendingPrimes_memoryAfter]
        exact Finset.mem_val.mpr hPafterMem
      obtain ⟨k, hk⟩ := (pendingPrime_mem_iff memAfter p).mp hpend
      exact ⟨k, hk⟩
  -- Retrieved image is exactly promotion values.
  have hRMap : (retrievedIndices TR g).map primeEmb = PromVals := by
    ext p
    constructor
    · intro hp
      obtain ⟨k, hkR, heq⟩ := Finset.mem_map.mp hp
      -- k ∈ R, prime k = p, need p ∈ PromVals (since k ∈ R → prime k ∈ PromVals via hRetFilter)
      have hPrimeProm : (memoryEntry memAfter k).1 ∈ PromVals := by
        have hkMem : k ∈ Finset.univ.filter
            (fun k : Fin memAfter.card => (memoryEntry memAfter k).1 ∈ PromVals) := by
          rw [← hRetFilter]
          exact hkR
        exact (Finset.mem_filter.mp hkMem).2
      exact heq ▸ hPrimeProm
    · intro hPromMem
      have hPromMem' : p ∈ prom.map tgtEmb := hPromVals ▸ hPromMem
      obtain ⟨j, hjProm, heqTgt⟩ := Finset.mem_map.mp hPromMem'
      -- j ∈ prom, target j = p, need k ∈ R with prime k = p
      -- Use promotionIndex for j: k = promotionIndex ⟨j, hjProm⟩ ∈ R with prime = target j = p.
      apply Finset.mem_map.mpr
      refine ⟨Q.promotionIndex S i g ⟨j, hjProm⟩, ?_, ?_⟩
      · -- promotionIndex ∈ R via image
        apply hRdef ▸ Finset.mem_image.mpr
        exact ⟨⟨j, hjProm⟩, Finset.mem_univ _, rfl⟩
      · -- prime of promotionIndex = target j = p
        have hSpec := Q.promotionIndex_spec S i g ⟨j, hjProm⟩
        have heqTgt' : Q.target i g.val j = p := heqTgt
        have hEq : (memoryEntry memAfter (Q.promotionIndex S i g ⟨j, hjProm⟩)).1 = p :=
          hSpec.trans heqTgt'
        exact hEq
  -- Survivors as a mapped image.
  have hMapSdiff : ((Finset.univ \ retrievedIndices TR g).map primeEmb) =
      ((Finset.univ.map primeEmb) \ ((retrievedIndices TR g).map primeEmb)) :=
    Finset.map_sdiff _ _
  have hSurvMap : (Finset.univ \ retrievedIndices TR g).map primeEmb =
      Pafter \ PromVals := by
    rw [hMapSdiff, hUnivMap, hRMap]
  -- Deletion in terms of surviving primes.
  have hEqMap : deleteMemoryIndices memAfter (retrievedIndices TR g) =
      ((Finset.univ \ retrievedIndices TR g).val.map (memoryEntry memAfter)) :=
    deleteMemoryIndices_eq_map _ _
  have hDeleteEq : deleteMemoryIndices memAfter (retrievedIndices TR g) =
      (Pafter \ PromVals).val.map f0 := by
    rw [hEqMap]
    -- `(univ \ R).val.map memoryEntry = ((univ \ R).map primeEmb).val.map f0`
    have hMapEntry : ((Finset.univ \ retrievedIndices TR g).val.map (memoryEntry memAfter)) =
        (((Finset.univ \ retrievedIndices TR g).map primeEmb).val.map f0) := by
      have hmv : ((((Finset.univ \ retrievedIndices TR g).map primeEmb).val)) =
          (((Finset.univ \ retrievedIndices TR g).val.map ⇑primeEmb)) :=
        Finset.map_val _ _
      have hmm : ((((Finset.univ \ retrievedIndices TR g).val.map ⇑primeEmb).map f0)) =
          (((Finset.univ \ retrievedIndices TR g).val.map (f0 ∘ ⇑primeEmb))) :=
        Multiset.map_map _ _ _
      rw [hmv, hmm]
      apply Multiset.map_congr rfl
      intro k _
      exact hEntryEq k
    rw [hMapEntry, hSurvMap]
  -- Translation of survivors: `f0 ↦ f1` via `delta`.
  have hTransSurv : translateMemory delta ((Pafter \ PromVals).val.map f0) =
      (Pafter \ PromVals).val.map f1 := by
    rw [translateMemory_map]
    apply Multiset.map_congr rfl
    intro p _
    have hZ : (((off0 - Q.spanAnchor (S g p) : ℤ)):ZMod p.val) + ((delta : ℤ):ZMod p.val) =
        (((off1 - Q.spanAnchor (S g p) : ℤ)):ZMod p.val) := by
      have e1 : off1 - Q.spanAnchor (S g p) = (off0 - Q.spanAnchor (S g p)) + delta := by
        linear_combination hOff
      rw [e1, Int.cast_add]
    show translateParticle delta (f0 p) = f1 p
    have e0 : f0 p = (⟨p, (((off0 - Q.spanAnchor (S g p) : ℤ)):ZMod p.val)⟩ :
        P.Particle g.val) := rfl
    have e1' : f1 p = (⟨p, (((off1 - Q.spanAnchor (S g p) : ℤ)):ZMod p.val)⟩ :
        P.Particle g.val) := rfl
    have et : translateParticle delta
        (⟨p, (((off0 - Q.spanAnchor (S g p) : ℤ)):ZMod p.val)⟩ : P.Particle g.val) =
        (⟨p, (((off0 - Q.spanAnchor (S g p) : ℤ)):ZMod p.val) + ((delta : ℤ):ZMod p.val)⟩ :
          P.Particle g.val) := rfl
    rw [e0, e1', et]
    exact congrArg (fun r : ZMod p.val => (⟨p, r⟩ : P.Particle g.val)) hZ
  -- Stored slots translate to `f1` of their source primes (source visit is a hit).
  have hStoreResidue : ∀ j : Fin (J + F.ell),
      ((((off0 - Q.spanAnchor (S g (Q.source i g.val j)) : ℤ)) :
        ZMod (Q.source i g.val j).val)) = 0 :=
    fun j => Q.span_active_hit S hLife i0 g _ (Q.source_activeVisit i g j)
  have hStorePt : ∀ j ∈ store,
      translateParticle delta (⟨Q.source i g.val j, 0⟩ : P.Particle g.val) =
        f1 (Q.source i g.val j) := by
    intro j _
    have hHit := hStoreResidue j
    have hZj : (0 : ZMod (Q.source i g.val j).val) + ((delta : ℤ):ZMod _) =
        (((off1 - Q.spanAnchor (S g (Q.source i g.val j)) : ℤ)) :
          ZMod (Q.source i g.val j).val) := by
      rw [← hHit, ← Int.cast_add]
      congr 1
      linear_combination -hOff
    have e1' : f1 (Q.source i g.val j) =
        (⟨Q.source i g.val j,
          (((off1 - Q.spanAnchor (S g (Q.source i g.val j)) : ℤ)) :
            ZMod (Q.source i g.val j).val)⟩ : P.Particle g.val) := rfl
    have et : translateParticle delta
        (⟨Q.source i g.val j, 0⟩ : P.Particle g.val) =
        (⟨Q.source i g.val j, (0 : ZMod (Q.source i g.val j).val) + ((delta : ℤ):ZMod _)⟩ :
          P.Particle g.val) := rfl
    rw [et, e1']
    exact congrArg (fun r : ZMod (Q.source i g.val j).val =>
      (⟨Q.source i g.val j, r⟩ : P.Particle g.val)) hZj
  have hStoreTrans : translateMemory delta (storedMemory (Q.source i g.val) store) =
      StoreVals.val.map f1 := by
    rw [storedMemory_eq_map, translateMemory_map]
    have hSV : StoreVals.val = store.val.map ⇑srcEmb := Finset.map_val _ _
    have hmmS : ((store.val.map ⇑srcEmb).map f1) =
        (store.val.map (f1 ∘ ⇑srcEmb)) :=
      Multiset.map_map _ _ _
    rw [hStoreVals] at hSV
    rw [hSV, hmmS]
    apply Multiset.map_congr rfl
    intro j hj
    exact hStorePt j (Finset.mem_val.mp hj)
  -- Finset union as multiset sum.
  have huVal : (Pafter \ PromVals).val + StoreVals.val = Pbefore.val := by
    rw [hPbeforeEq, Finset.union_val]
    apply Multiset.add_eq_union_iff_disjoint.mpr
    apply Multiset.disjoint_left.mpr
    intro p hp ht
    exact Finset.disjoint_left.mp hDisj hp ht
  rw [hmemBeforeEq, translateMemory_add, hDeleteEq, hTransSurv, hStoreTrans,
    ← Multiset.map_add, huVal]


end Erdos821.S2Core
