import Erdos821.S2.HistoryAnchors
import Erdos821.S2.HistoryProjection
import Erdos821.S2.LiveGrowth
import Erdos821.S2.PhysicalCompatibility
import Erdos821.P3Live.Conservation

set_option autoImplicit false

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- Permuting active slots reindexes the anchor condition bijectively; pending is unchanged. -/
theorem anchorInvariant_permute {n : ℕ} {A : Model F P J m} (H : MemoryHistory A n)
    (i : Fin (n + 1)) (s : P.MemoryState (J + F.ell)) (π : P.Permutations (J + F.ell)) :
    H.AnchorInvariant i s ↔ H.AnchorInvariant i (permuteActive π s) := by
  constructor
  · rintro ⟨hact, hpend⟩
    refine ⟨?_, ?_⟩
    · intro g j
      exact hact g ((π g.val) j)
    · intro g z hz
      exact hpend g z hz
  · rintro ⟨hact, hpend⟩
    refine ⟨?_, ?_⟩
    · intro g j
      have hj := hact g (((π g.val).symm) j)
      have he : (π g.val) (((π g.val).symm) j) = j := Equiv.apply_symm_apply (π g.val) j
      have hj2 :
          (H.toResiduePath.offset i : ZMod ((s.2.1 g.val ((π g.val) (((π g.val).symm) j))).val)) =
            (H.anchorOffset ((s.2.1 g.val ((π g.val) (((π g.val).symm) j))).val) :
              ZMod ((s.2.1 g.val ((π g.val) (((π g.val).symm) j))).val)) := hj
      rw [he] at hj2
      exact hj2
    · intro g z hz
      exact hpend g z hz

/-- Membership in a zero-residue birth batch is an explicit birth index. -/
theorem zeroBirthBatch_mem {g : P.Group} {b : ℕ} (p : Fin b → P.Prime g)
    (z : P.Particle g) : z ∈ zeroBirthBatch p ↔ ∃ h : Fin b, z = ⟨p h, 0⟩ := by
  constructor
  · intro hz
    simp only [zeroBirthBatch, Multiset.mem_coe, List.mem_ofFn] at hz
    obtain ⟨h, hh⟩ := hz
    exact ⟨h, hh.symm⟩
  · rintro ⟨h, rfl⟩
    simp only [zeroBirthBatch, Multiset.mem_coe, List.mem_ofFn]
    exact ⟨h, rfl⟩

/-- Stored slots contribute exactly the zero-residue particles at those slots. -/
theorem storedMemory_mem {M : ℕ} {g : P.Group} (a : Fin M → P.Prime g)
    (B : Finset (Fin M)) (z : P.Particle g) :
    z ∈ storedMemory a B ↔ ∃ k ∈ B, z = ⟨a k, 0⟩ := by
  constructor
  · intro hz
    simp only [storedMemory, Multiset.mem_coe, List.mem_map] at hz
    obtain ⟨k, hk, hkz⟩ := hz
    have hkB : k ∈ B := by
      have : k ∈ B.toList := by
        simpa using hk
      simpa [Finset.mem_toList] using this
    exact ⟨k, hkB, hkz.symm⟩
  · rintro ⟨k, hkB, rfl⟩
    simp only [storedMemory, Multiset.mem_coe, List.mem_map]
    exact ⟨k, by simpa [Finset.mem_toList] using hkB, rfl⟩

/-- Translation preserves the prime and adds `delta` to the residue. -/
theorem translateMemory_mem (delta : ℤ) {g : P.Group} (w : P.Memory g)
    (z : P.Particle g) : z ∈ translateMemory delta w ↔ ∃ w0 ∈ w, translateParticle delta w0 = z := by
  simp only [translateMemory, Multiset.mem_map]

/-- Every indexed particle occurs in its multiset. -/
theorem anchorsMemoryEntry_mem {g : P.Group} (z : P.Memory g) (k : Fin z.card) :
    memoryEntry z k ∈ z := by
  have hget : z.toList.get ⟨k.val, by simpa using k.isLt⟩ ∈ z.toList :=
    List.get_mem _ _
  have hmem : memoryEntry z k ∈ z.toList := hget
  have hcoe : memoryEntry z k ∈ ((z.toList : List (P.Particle g)) : Multiset (P.Particle g)) :=
    Multiset.mem_coe.mpr hmem
  have heq : ((z.toList : List (P.Particle g)) : Multiset (P.Particle g)) = z :=
    Multiset.coe_toList z
  rw [heq] at hcoe
  exact hcoe

/-- A shared prime divides `D`, so the edge displacement vanishes modulo that prime. -/
theorem edgeDelta_cast_zero (A : Model F P J m)
    (ν : Pattern P J F.ell m) (forward : Bool) (a : P.Labels (J + F.ell)) (u : P.Aux J)
    (p : ℕ) (hdvd : p ∣ ν.D a u) : ((edgeDelta A ν forward a u : ℤ) : ZMod p) = 0 := by
  have hD : ((ν.D a u : ℕ) : ZMod p) = 0 := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hDz : (((ν.D a u : ℕ) : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_natCast, hD]
  unfold edgeDelta
  split
  · rw [Int.cast_mul, hDz, mul_zero]
  · rw [Int.cast_neg, Int.cast_mul, hDz, mul_zero, neg_zero]

/-- Permuting labels preserves injectivity. -/
theorem permute_labels_injective {M : ℕ} (a : P.Labels M) (π : P.Permutations M)
    (hinj : ∀ g : P.Group, Function.Injective (a g)) (g : P.Group) :
    Function.Injective ((P.act π a) g) :=
  (hinj g).comp (π g).injective

/-- The residue-path step equals the raw edge displacement on permuted labels. -/
theorem residue_step_eq_delta {n : ℕ} {A : Model F P J m} (H : MemoryHistory A n)
    (hH : H.Valid) (i : Fin n) :
    H.toResiduePath.step i =
      edgeDelta A (A.pattern (H.edge i).2.2.1) (edgeForward i)
        ((permuteActive (H.edge i).1 (H.after i.castSucc)).2.1) (H.edge i).2.2.2.1 := by
  simp only [ResiduePath.step, ResiduePath.source, MemoryHistory.toResiduePath,
    permuteActive]
  have hEq : (H.before i.castSucc).2.1 = (H.after i.castSucc).2.1 :=
    (hH.2.2.1 i.castSucc).2.1
  rw [hEq]

/-- Offset recurrence with the actual edge displacement. -/
theorem offset_succ_eq_delta {n : ℕ} {A : Model F P J m} (H : MemoryHistory A n)
    (hH : H.Valid) (i : Fin n) :
    H.toResiduePath.offset i.succ =
      H.toResiduePath.offset i.castSucc +
        edgeDelta A (A.pattern (H.edge i).2.2.1) (edgeForward i)
          ((permuteActive (H.edge i).1 (H.after i.castSucc)).2.1) (H.edge i).2.2.2.1 := by
  rw [← residue_step_eq_delta H hH i, residuePath_offset_succ]

/-- Edge carries the anchor forward: shared slots use vanishing displacement,
promotions use the zero-residue check, fresh slots are new births. -/
theorem anchor_edge_forward {n : ℕ} {A : Model F P J m} (H : MemoryHistory A n)
    (hH : H.Valid) (hd : H.DistinctBirths) (i : Fin n)
    (hInv : H.AnchorInvariant i.castSucc (H.after i.castSucc)) :
    H.AnchorInvariant i.succ (H.before i.succ) := by
  -- permuted source/target and raw validity
  let πs := (H.edge i).1
  let πt := (H.edge i).2.1
  let ν := A.pattern (H.edge i).2.2.1
  let u := (H.edge i).2.2.2.1
  let tr := (H.edge i).2.2.2.2
  let ss := permuteActive πs (H.after i.castSucc)
  let tt := permuteActive πt (H.before i.succ)
  have hInvSS : H.AnchorInvariant i.castSucc ss :=
    (anchorInvariant_permute H i.castSucc _ πs).mp hInv
  have hRaw : rawEdgeValid A ν (edgeForward i) u ss tt tr := (hH.2.2.2 i).1
  have hOffset : H.toResiduePath.offset i.succ =
      H.toResiduePath.offset i.castSucc +
        edgeDelta A ν (edgeForward i) ss.2.1 u :=
    offset_succ_eq_delta H hH i
  -- prove for permuted target, then transfer back
  have hTT : H.AnchorInvariant i.succ tt := by
    obtain ⟨hactS, hpendS⟩ := hInvSS
    obtain ⟨_, _, hCompat, hBan, _, hG⟩ := hRaw
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hPathValid := H.toResiduePath_valid_of_distinct hn hH hd
    -- target injectivity for D-divisibility
    have hinjT : ∀ g : P.Group, Function.Injective (tt.2.1 g) := by
      intro g
      have hBeforeInj : Function.Injective ((H.before i.succ).2.1 g) :=
        hPathValid.1 i.succ g
      -- tt.2.1 g = (before succ).2.1 g ∘ πt g
      have hEq : tt.2.1 g = (H.before i.succ).2.1 g ∘ (πt g) := rfl
      rw [hEq]
      exact hBeforeInj.comp (πt g).injective
    refine ⟨?_, ?_⟩
    · -- active: shared / promoted / fresh
      intro g j
      by_cases hShared : ν.shared g.val j
      · -- shared: same prime, displacement vanishes mod p
        have hEqPrime : ss.2.1 g.val j = tt.2.1 g.val j := hCompat g.val j hShared
        have hdvd : (tt.2.1 g.val j).val ∣ ν.D ss.2.1 u := by
          have hIff := target_label_dvd_D_iff ν ss.2.1 tt.2.1 u hinjT hCompat hBan g.val j
          exact hIff.mpr hShared
        have hDeltaZero : ((edgeDelta A ν (edgeForward i) ss.2.1 u : ℤ) :
            ZMod ((tt.2.1 g.val j).val)) = 0 := by
          have hDvd2 : ((tt.2.1 g.val j).val) ∣ ν.D ss.2.1 u := hdvd
          have hz := edgeDelta_cast_zero A ν (edgeForward i) ss.2.1 u
            ((tt.2.1 g.val j).val) hDvd2
          exact hz
        have hSrc := hactS g j
        -- transport source invariant to target prime
        rw [hEqPrime] at hSrc
        -- offset recurrence cast to ZMod p
        have hOff : (H.toResiduePath.offset i.succ : ZMod ((tt.2.1 g.val j).val)) =
            (H.toResiduePath.offset i.castSucc : ZMod ((tt.2.1 g.val j).val)) +
              ((edgeDelta A ν (edgeForward i) ss.2.1 u : ℤ) : ZMod ((tt.2.1 g.val j).val)) := by
          have hInt : H.toResiduePath.offset i.succ =
              H.toResiduePath.offset i.castSucc +
                edgeDelta A ν (edgeForward i) ss.2.1 u := by
            have ho := hOffset
            -- hOffset uses ss.2.1 via let; unfold lets (defeq)
            exact ho
          rw [hInt, Int.cast_add]
        rw [hDeltaZero, add_zero] at hOff
        rw [hOff]
        exact hSrc
      · by_cases hProm : j ∈ tr.2.1 g
        · -- promoted: retrieved pending had zero translated residue
          have hgT := hG g
          obtain ⟨_, _, _, hRetFull, _⟩ := hgT
          have hRet := hRetFull ⟨j, hProm⟩
          obtain ⟨hPrimeEq, hZero, _⟩ := hRet
          -- z0 is the retrieved source pending particle
          set z0 := memoryEntry (ss.2.2 g) (tr.2.2 g ⟨j, hProm⟩) with hz0def
          have hzSS : z0 ∈ ss.2.2 g := anchorsMemoryEntry_mem _ _
          have hPend := hpendS g z0 hzSS
          -- arithmetic in ZMod (z0.1.val): offset succ = anchor
          have hGoalZ : (H.toResiduePath.offset i.succ : ZMod ((z0.1.val))) =
              (H.anchorOffset (z0.1.val) : ZMod ((z0.1.val))) := by
            have hOffZ : (H.toResiduePath.offset i.succ : ZMod ((z0.1.val))) =
                (H.toResiduePath.offset i.castSucc : ZMod ((z0.1.val))) +
                  ((edgeDelta A ν (edgeForward i) ss.2.1 u : ℤ) : ZMod ((z0.1.val))) := by
              rw [hOffset, Int.cast_add]
            have hPendZ : z0.2 =
                (H.toResiduePath.offset i.castSucc : ZMod ((z0.1.val))) -
                  (H.anchorOffset (z0.1.val) : ZMod ((z0.1.val))) := by
              rw [hPend, Int.cast_sub]
            have hZeroZ : z0.2 +
                ((edgeDelta A ν (edgeForward i) ss.2.1 u : ℤ) : ZMod ((z0.1.val))) = 0 := hZero
            linear_combination hOffZ - hPendZ + hZeroZ
          -- transport along prime equality to target slot
          rw [hPrimeEq] at hGoalZ
          exact hGoalZ
        · -- fresh: new birth at next offset
          have hFreshMem : j ∈ H.freshTargetSlots i g := by
            simp only [MemoryHistory.freshTargetSlots, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨hShared, hProm⟩
          let a : BirthAddress P (J + F.ell) n H.birthBound :=
            .inr (.inl (i, g, j))
          have haPerf : H.addressPerformed H.birthBound a := hFreshMem
          have haVal : H.addressValue H.birthBound a = ((tt.2.1 g.val j).val) := rfl
          have hEq2 := H.anchorOffset_eq_birth hH hd a _ haPerf haVal
          have hBirthOff : H.birthOffset a = H.toResiduePath.offset i.succ := rfl
          have hAnchor : H.anchorOffset ((tt.2.1 g.val j).val) =
              H.toResiduePath.offset i.succ := by
            rw [← hBirthOff, ← hEq2]
          -- goal is offset succ = anchor; symmetry of hAnchor cast
          have hGoal : (H.toResiduePath.offset i.succ : ZMod ((tt.2.1 g.val j).val)) =
              (H.anchorOffset ((tt.2.1 g.val j).val) : ZMod ((tt.2.1 g.val j).val)) := by
            rw [hAnchor]
          exact hGoal
    · -- pending: surviving translated + stored
      intro g z hz
      have hgT := hG g
      obtain ⟨_, _, _, _, hMemEq⟩ := hgT
      -- tt pending = translate (delete + stored)
      have hTTeq : tt.2.2 g = translateMemory (edgeDelta A ν (edgeForward i) ss.2.1 u)
          (deleteMemoryIndices (ss.2.2 g) (retrievedIndices tr g) +
            storedMemory (ss.2.1 g.val) (tr.1 g)) := hMemEq
      have hzmem : z ∈ translateMemory (edgeDelta A ν (edgeForward i) ss.2.1 u)
          (deleteMemoryIndices (ss.2.2 g) (retrievedIndices tr g) +
            storedMemory (ss.2.1 g.val) (tr.1 g)) := hTTeq ▸ hz
      obtain ⟨w, hwmem, hzEq⟩ := (translateMemory_mem _ _ _).mp hzmem
      rw [Multiset.mem_add] at hwmem
      rcases hwmem with hDel | hStore
      · -- surviving: translated survivor keeps anchor, offset shifts by delta
        have hPart := memory_indices_partition (ss.2.2 g) (retrievedIndices tr g)
        have hwSS : w ∈ ss.2.2 g := by
          rw [← hPart]
          exact Multiset.mem_add.mpr (Or.inl hDel)
        have hPendW := hpendS g w hwSS
        -- z = translate w, so primes equal and residues add delta
        subst hzEq
        -- after subst, z is (translateParticle delta w); show residue law
        show (translateParticle (edgeDelta A ν (edgeForward i) ss.2.1 u) w).2 =
          (((H.toResiduePath.offset i.succ -
            H.anchorOffset ((translateParticle (edgeDelta A ν (edgeForward i) ss.2.1 u) w).1.val) : ℤ) :
            ZMod (((translateParticle (edgeDelta A ν (edgeForward i) ss.2.1 u) w).1.val))))
        -- translate preserves prime, adds delta to residue (definitional)
        have hPrime : ((translateParticle (edgeDelta A ν (edgeForward i) ss.2.1 u) w).1.val) =
            (w.1.val) := rfl
        have hRes : ((translateParticle (edgeDelta A ν (edgeForward i) ss.2.1 u) w).2) =
            w.2 + ((edgeDelta A ν (edgeForward i) ss.2.1 u : ℤ) : ZMod (w.1.val)) := rfl
        -- rewrite goal using prime preservation (defeq, but make explicit)
        have hGoalEq : (((H.toResiduePath.offset i.succ -
            H.anchorOffset ((translateParticle (edgeDelta A ν (edgeForward i) ss.2.1 u) w).1.val) : ℤ) :
            ZMod (((translateParticle (edgeDelta A ν (edgeForward i) ss.2.1 u) w).1.val)))) =
            (((H.toResiduePath.offset i.succ - H.anchorOffset (w.1.val) : ℤ) : ZMod (w.1.val))) := rfl
        rw [hGoalEq, hRes]
        -- arithmetic: (offset castSucc - anchor) + delta = offset succ - anchor
        have hOff : H.toResiduePath.offset i.succ =
            H.toResiduePath.offset i.castSucc +
              edgeDelta A ν (edgeForward i) ss.2.1 u := hOffset
        have hArith : (w.2 + ((edgeDelta A ν (edgeForward i) ss.2.1 u : ℤ) : ZMod (w.1.val))) =
            (((H.toResiduePath.offset i.succ - H.anchorOffset (w.1.val) : ℤ) : ZMod (w.1.val))) := by
          have hOffZ : (H.toResiduePath.offset i.succ : ZMod (w.1.val)) =
              (H.toResiduePath.offset i.castSucc : ZMod (w.1.val)) +
                ((edgeDelta A ν (edgeForward i) ss.2.1 u : ℤ) : ZMod (w.1.val)) := by
            rw [hOff, Int.cast_add]
          have hPendZ : w.2 =
              (H.toResiduePath.offset i.castSucc : ZMod (w.1.val)) -
                (H.anchorOffset (w.1.val) : ZMod (w.1.val)) := by
            rw [hPendW, Int.cast_sub]
          -- w.2 + delta = (offset castSucc - anchor) + delta = offset succ - anchor
          have hEq : w.2 + ((edgeDelta A ν (edgeForward i) ss.2.1 u : ℤ) : ZMod (w.1.val)) =
              (H.toResiduePath.offset i.succ : ZMod (w.1.val)) -
                (H.anchorOffset (w.1.val) : ZMod (w.1.val)) := by
            linear_combination hPendZ - hOffZ
          rw [hEq, ← Int.cast_sub]
        exact hArith
      · -- stored: zero-residue store translated by delta, anchor from source active
        obtain ⟨k, hkMem, hwEq⟩ := (storedMemory_mem _ _ _).mp hStore
        subst hwEq
        -- w = ⟨ss active k, 0⟩, z = translate w
        subst hzEq
        show (translateParticle (edgeDelta A ν (edgeForward i) ss.2.1 u) (⟨ss.2.1 g.val k, 0⟩ : P.Particle g.val)).2 =
          (((H.toResiduePath.offset i.succ -
            H.anchorOffset ((translateParticle (edgeDelta A ν (edgeForward i) ss.2.1 u)
              (⟨ss.2.1 g.val k, 0⟩ : P.Particle g.val)).1.val) : ℤ) :
            ZMod (((translateParticle (edgeDelta A ν (edgeForward i) ss.2.1 u)
              (⟨ss.2.1 g.val k, 0⟩ : P.Particle g.val)).1.val))))
        have hActK := hactS g k
        -- anchor of stored prime equals source offset
        have hPrimeStore : ((translateParticle (edgeDelta A ν (edgeForward i) ss.2.1 u)
            (⟨ss.2.1 g.val k, 0⟩ : P.Particle g.val)).1.val) = ((ss.2.1 g.val k).val) := rfl
        have hResStore : (translateParticle (edgeDelta A ν (edgeForward i) ss.2.1 u)
            (⟨ss.2.1 g.val k, 0⟩ : P.Particle g.val)).2 =
            ((edgeDelta A ν (edgeForward i) ss.2.1 u : ℤ) : ZMod ((ss.2.1 g.val k).val)) := by
          show (0 : ZMod ((ss.2.1 g.val k).val)) +
            ((edgeDelta A ν (edgeForward i) ss.2.1 u : ℤ) : ZMod ((ss.2.1 g.val k).val)) = _
          rw [zero_add]
        -- rewrite goal to source prime (defeq)
        have hGoalStore : (((H.toResiduePath.offset i.succ -
            H.anchorOffset ((translateParticle (edgeDelta A ν (edgeForward i) ss.2.1 u)
              (⟨ss.2.1 g.val k, 0⟩ : P.Particle g.val)).1.val) : ℤ) :
            ZMod (((translateParticle (edgeDelta A ν (edgeForward i) ss.2.1 u)
              (⟨ss.2.1 g.val k, 0⟩ : P.Particle g.val)).1.val)))) =
            (((H.toResiduePath.offset i.succ - H.anchorOffset ((ss.2.1 g.val k).val) : ℤ) :
              ZMod ((ss.2.1 g.val k).val))) := rfl
        rw [hGoalStore, hResStore]
        -- delta = offset succ - anchor since offset castSucc = anchor
        have hOff : H.toResiduePath.offset i.succ =
            H.toResiduePath.offset i.castSucc +
              edgeDelta A ν (edgeForward i) ss.2.1 u := hOffset
        have hOffZ : (H.toResiduePath.offset i.succ : ZMod ((ss.2.1 g.val k).val)) =
            (H.toResiduePath.offset i.castSucc : ZMod ((ss.2.1 g.val k).val)) +
              ((edgeDelta A ν (edgeForward i) ss.2.1 u : ℤ) : ZMod ((ss.2.1 g.val k).val)) := by
          rw [hOff, Int.cast_add]
        -- hActK : offset castSucc = anchor (as ZMod)
        have hEq : ((edgeDelta A ν (edgeForward i) ss.2.1 u : ℤ) : ZMod ((ss.2.1 g.val k).val)) =
            (((H.toResiduePath.offset i.succ - H.anchorOffset ((ss.2.1 g.val k).val) : ℤ) :
              ZMod ((ss.2.1 g.val k).val))) := by
          have hSub : (((H.toResiduePath.offset i.succ - H.anchorOffset ((ss.2.1 g.val k).val) : ℤ) :
              ZMod ((ss.2.1 g.val k).val))) =
              (H.toResiduePath.offset i.succ : ZMod ((ss.2.1 g.val k).val)) -
                (H.anchorOffset ((ss.2.1 g.val k).val) : ZMod ((ss.2.1 g.val k).val)) := by
            rw [Int.cast_sub]
          rw [hSub, hOffZ]
          linear_combination -hActK
        exact hEq
  exact (anchorInvariant_permute H i.succ _ πt).mpr hTT

/-- Ghost keeps active labels and offset; pending splits into survivors plus zero-residue births. -/
theorem anchor_ghost_forward {n : ℕ} {A : Model F P J m} (H : MemoryHistory A n)
    (hH : H.Valid) (hd : H.DistinctBirths) (i : Fin (n + 1))
    (hInv : H.AnchorInvariant i (H.before i)) : H.AnchorInvariant i (H.after i) := by
  obtain ⟨hactB, hpendB⟩ := hInv
  have hActEq : (H.before i).2.1 = (H.after i).2.1 := (hH.2.2.1 i).2.1
  have hGhost := (hH.2.2.1 i).2.2
  refine ⟨?_, ?_⟩
  · intro g j
    have h := hactB g j
    have heq : (H.before i).2.1 g.val j = (H.after i).2.1 g.val j := by rw [hActEq]
    rw [heq] at h
    exact h
  · intro g z hz
    have hg := hGhost g
    obtain ⟨_, hEq⟩ := hg
    -- after pending = delete + births
    have hAfter : (H.after i).2.2 g =
        deleteMemoryIndices ((H.before i).2.2 g) ((H.ghost i).1 g) +
          zeroBirthBatch ((H.ghost i).2.2 g) := hEq.symm
    -- case split on membership in sum
    have hzmem : z ∈ deleteMemoryIndices ((H.before i).2.2 g) ((H.ghost i).1 g) +
        zeroBirthBatch ((H.ghost i).2.2 g) := hAfter ▸ hz
    rw [Multiset.mem_add] at hzmem
    rcases hzmem with hDel | hBirth
    · -- surviving: in before, apply IH (same offset, same particle)
      have hPart := memory_indices_partition ((H.before i).2.2 g) ((H.ghost i).1 g)
      have hBefore : z ∈ (H.before i).2.2 g := by
        rw [← hPart]
        exact Multiset.mem_add.mpr (Or.inl hDel)
      exact hpendB g z hBefore
    · -- new birth: residue 0, anchor = offset i
      obtain ⟨h0, hz0⟩ := (zeroBirthBatch_mem _ _).mp hBirth
      subst hz0
      -- anchor of this birth prime equals offset i
      have hAnchor : H.anchorOffset ((((H.ghost i).2.2 g h0).val)) = H.toResiduePath.offset i := by
        have hTrunc : H.Truncated H.birthBound := H.distinct_truncated hH hd
        have hLe : (((H.ghost i).2.1 g).val) ≤ H.birthBound :=
          H.ghostBatch_le H.birthBound hTrunc i g
        have hltB : h0.val < H.birthBound := lt_of_lt_of_le h0.isLt hLe
        let a : BirthAddress P (J + F.ell) n H.birthBound :=
          .inr (.inr (i, g, ⟨h0.val, hltB⟩))
        have haPerf : H.addressPerformed H.birthBound a := h0.isLt
        have haVal : H.addressValue H.birthBound a = (((H.ghost i).2.2 g h0).val) := by
          show (if hh : (⟨h0.val, hltB⟩ : Fin H.birthBound).val < (((H.ghost i).2.1 g).val)
            then ((((H.ghost i).2.2 g ⟨(⟨h0.val, hltB⟩ : Fin H.birthBound).val, hh⟩).val)) else 0) =
            ((((H.ghost i).2.2 g h0).val))
          rw [dite_eq_left h0.isLt]
        have hEq2 := H.anchorOffset_eq_birth hH hd a _ haPerf haVal
        -- birthOffset for ghost address is offset i
        have hBirthOff : H.birthOffset a = H.toResiduePath.offset i := rfl
        rw [hEq2, hBirthOff]
      -- residue is 0 = offset - anchor
      show (0 : ZMod ((((H.ghost i).2.2 g h0).val))) =
        (((H.toResiduePath.offset i - H.anchorOffset ((((H.ghost i).2.2 g h0).val)) : ℤ) :
          ZMod ((((H.ghost i).2.2 g h0).val))))
      simp [hAnchor]

/-- Every valid distinct-birth history keeps all big anchors at their birth offsets. -/
theorem HistoryAnchorTask_proof : HistoryAnchorTask := by
  intro F P J m n A H hH hd i
  induction i using Fin.induction with
  | zero =>
    have hBefore0 : H.AnchorInvariant 0 (H.before 0) := H.anchorInvariant_initial hH hd
    exact ⟨hBefore0, anchor_ghost_forward H hH hd 0 hBefore0⟩
  | succ i ih =>
    have hBeforeSucc : H.AnchorInvariant i.succ (H.before i.succ) :=
      anchor_edge_forward H hH hd i ih.2
    exact ⟨hBeforeSucc, anchor_ghost_forward H hH hd i.succ hBeforeSucc⟩


end Erdos821.S2Core
