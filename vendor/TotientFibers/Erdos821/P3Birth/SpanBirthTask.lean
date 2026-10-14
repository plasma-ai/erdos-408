import Erdos821.S2.SpanBirthTask
import Erdos821.S2.HistoryBirths

/-! Birth addresses in a reconstructed lifespan history are globally injective. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Birth

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}
variable {A : Model F P J m} {n : ℕ}

namespace MemoryHistory

variable (H : Erdos821.S2Core.MemoryHistory A n)

/-- A finite cutoff large enough for every memory and every ghost batch. -/
def birthCutoff : ℕ :=
  ∑ i : Fin (n + 1),
    (P.memorySize (H.before i) + P.memorySize (H.after i) +
      ∑ g : P.BigGroup, ((H.ghost i).2.1 g).val)

theorem birthCutoff_truncated : H.Truncated (birthCutoff H) := by
  intro i
  have hterm := Finset.single_le_sum
    (f := fun j : Fin (n + 1) =>
      P.memorySize (H.before j) + P.memorySize (H.after j) +
        ∑ g : P.BigGroup, ((H.ghost j).2.1 g).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hterm' :
      P.memorySize (H.before i) + P.memorySize (H.after i) +
        ∑ g : P.BigGroup, ((H.ghost i).2.1 g).val ≤ birthCutoff H := by
    simpa [birthCutoff] using hterm
  constructor <;> omega

theorem birthCutoff_batch_le (i : Fin (n + 1)) (g : P.BigGroup) :
    ((H.ghost i).2.1 g).val ≤ birthCutoff H := by
  have hgroup := Finset.single_le_sum
    (f := fun h : P.BigGroup => ((H.ghost i).2.1 h).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
  have hterm := Finset.single_le_sum
    (f := fun j : Fin (n + 1) =>
      P.memorySize (H.before j) + P.memorySize (H.after j) +
        ∑ h : P.BigGroup, ((H.ghost j).2.1 h).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hterm' :
      P.memorySize (H.before i) + P.memorySize (H.after i) +
        ∑ h : P.BigGroup, ((H.ghost i).2.1 h).val ≤ birthCutoff H := by
    simpa [birthCutoff] using hterm
  omega

end MemoryHistory

/-- An initially active label has lifespan start zero. -/
theorem initial_birth_at_zero
    (Q : Erdos821.S2Core.ResiduePath A n) (S : LifespanAssignment P n)
    (hS : Q.lifespanValid S) (g : P.BigGroup) (h : Fin (J + F.ell)) :
    ∃ stop, S g (Q.labels 0 g.val h) = some (0, stop) := by
  let p := Q.labels 0 g.val h
  have hactive : (0 : Fin (n + 1)) ∈ Q.activeVisits g p := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, ⟨h, rfl⟩⟩
  rcases hs : S g p with _ | ⟨birth, stop⟩
  · have hnone : Q.activeVisits g p = ∅ := by
      simpa [ResiduePath.spanValid, hs] using hS g p
    simp [hnone] at hactive
  · have hspan : Q.spanValid g p (some (birth, stop)) := by
      simpa [hs] using hS g p
    have hbirth := (hspan.2.2.1 0 hactive).1
    have hb0 : birth = 0 := by
      apply Fin.ext
      have hbirthVal : birth.val ≤ 0 := by
        simpa using (Fin.le_iff_val_le_val).mp hbirth
      simpa using Nat.le_antisymm hbirthVal (Nat.zero_le _)
    exact ⟨stop, by simpa [hb0]⟩

/-- A fresh active target can only occur at its assigned lifespan start. -/
theorem fresh_birth_at_target
    (Q : Erdos821.S2Core.ResiduePath A n) (S : LifespanAssignment P n)
    (hQ : Q.Valid) (hS : Q.lifespanValid S)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (y : P.SmallResidues) (i : Fin n) (g : P.BigGroup) (h : Fin (J + F.ell))
    (hfresh : h ∈ (Q.reconstructedHistory S hS y).freshTargetSlots i g) :
    ∃ stop, S g (Q.target i g.val h) = some (i.succ, stop) := by
  let p := Q.target i g.val h
  have hactiveTarget : i.succ ∈ Q.activeVisits g p :=
    Q.target_activeVisit i g h
  have hfreshParts :
      ¬ (A.pattern (Q.pattern i)).shared g.val h ∧ h ∉ Q.promotionSlots S i g := by
    have hparts := (Finset.mem_filter.mp hfresh).2
    simpa [ResiduePath.reconstructedHistory, ResiduePath.reconstructedTransferChoice] using hparts
  rcases hs : S g p with _ | ⟨birth, stop⟩
  · have hnone : Q.activeVisits g p = ∅ := by
      simpa [ResiduePath.spanValid, hs] using hS g p
    simp [hnone] at hactiveTarget
  · have hspan : Q.spanValid g p (some (birth, stop)) := by
      simpa [hs] using hS g p
    have hbirth_le := (hspan.2.2.1 i.succ hactiveTarget).1
    by_cases hb : birth = i.succ
    · exact ⟨stop, by simpa [hb]⟩
    · have hbirth_le_i : birth ≤ i.castSucc := by
        have hleVal : birth.val ≤ i.succ.val := Fin.le_iff_val_le_val.mp hbirth_le
        have hneVal : birth.val ≠ i.succ.val := fun he => hb (Fin.ext he)
        change birth.val ≤ i.val
        simp only [Fin.val_succ] at hleVal hneVal
        omega
      by_cases hactive : i.castSucc ∈ Q.activeVisits g p
      · obtain ⟨j₀, hj₀⟩ := (Finset.mem_filter.mp hactive).2
        let j : Fin (J + F.ell) := (Q.sourcePerm i g.val).symm j₀
        have hsource : Q.source i g.val j = p := by
          dsimp [j]
          simp [ResiduePath.source, PrimeGroups.act, hj₀]
        let κ : ℤ := if edgeForward i then A.k else -A.k
        let D : ℕ := (A.pattern (Q.pattern i)).D (Q.source i) (Q.free i)
        have hstep : Q.step i = κ * (D : ℤ) := by
          dsimp [κ, D, ResiduePath.step, edgeDelta]
          split <;> ring
        have hkκ : ¬ (p.val : ℤ) ∣ κ := by
          dsimp [κ]
          by_cases hf : edgeForward i
          · simpa [hf] using hk g p
          · simpa [hf] using hk g p
        have hsource_hit := Q.span_active_hit S hS i.castSucc g p hactive
        have htarget_hit := Q.span_active_hit S hS i.succ g p hactiveTarget
        have hsource_dvd : (p.val : ℤ) ∣
            Q.offset i.castSucc - Q.spanAnchor (S g p) :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hsource_hit
        have htarget_dvd : (p.val : ℤ) ∣
            Q.offset i.succ - Q.spanAnchor (S g p) :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp htarget_hit
        have hdisplacement :
            (Q.offset i.castSucc - Q.spanAnchor (S g p)) + κ * (D : ℤ) =
              Q.offset i.succ - Q.spanAnchor (S g p) := by
          rw [residuePath_offset_succ, hstep]
          ring
        have htarget_dvd' : (p.val : ℤ) ∣
            (Q.offset i.castSucc - Q.spanAnchor (S g p)) + κ * (D : ℤ) := by
          rw [hdisplacement]
          exact htarget_dvd
        have hsource_dvd' : ((Q.source i g.val j).val : ℤ) ∣
            Q.offset i.castSucc - Q.spanAnchor (S g p) := by
          simpa [hsource] using hsource_dvd
        have htarget_dvd'' : ((Q.source i g.val j).val : ℤ) ∣
            (Q.offset i.castSucc - Q.spanAnchor (S g p)) + κ * (D : ℤ) := by
          simpa [hsource] using htarget_dvd'
        have hkSource : ¬ ((Q.source i g.val j).val : ℤ) ∣ κ := by
          simpa [hsource] using hkκ
        have hshared := active_both_shared (A.pattern (Q.pattern i))
          (Q.source i) (Q.target i) (Q.free i)
          (fun g₀ => Q.source_injective hQ i g₀)
          (fun g₀ => Q.target_injective hQ i g₀)
          (hQ.2 i).1 (hQ.2 i).2 g.val j h (by simpa [p] using hsource)
          (Q.offset i.castSucc - Q.spanAnchor (S g p)) κ
          hsource_dvd' htarget_dvd'' hkSource
        exact (hfreshParts.1 hshared.2.1).elim
      · have hstop : i.castSucc < stop := by
          have hle : i.succ ≤ stop := (hspan.2.2.1 i.succ hactiveTarget).2
          change i.val < stop.val
          have hleVal : i.succ.val ≤ stop.val := Fin.le_iff_val_le_val.mp hle
          simp only [Fin.val_succ] at hleVal
          omega
        have hpendingSpan : Q.pendingAfter g p (S g p) i.castSucc := by
          rw [hs]
          exact ⟨hbirth_le_i, hstop, hactive⟩
        have hpending : p ∈ Q.pendingAfterPrimes S i.castSucc g := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpendingSpan⟩
        have hpromotion : h ∈ Q.promotionSlots S i g := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ h, hfreshParts.1, hpending⟩
        exact (hfreshParts.2 hpromotion).elim

/-- The ghost batch enumerates each selected prime at most once. -/
theorem ghostBatchLabels_injective
    (Q : Erdos821.S2Core.ResiduePath A n) (S : LifespanAssignment P n)
    (i : Fin (n + 1)) (g : P.BigGroup) :
    Function.Injective (Q.ghostBatchLabels S i g) := by
  let ps := Q.ghostBirthPrimes S i g
  let idx : Fin ps.card → Fin ps.toList.length := fun h =>
    ⟨h.val, by simpa using h.isLt⟩
  have hnodup : ps.toList.Nodup := Finset.nodup_toList ps
  intro h k he
  have hvalues : (ps.toList.get (idx h)).val = (ps.toList.get (idx k)).val :=
    congrArg Subtype.val he
  have hget : ps.toList.get (idx h) = ps.toList.get (idx k) := Subtype.ext hvalues
  have hidx : idx h = idx k := hnodup.get_inj_iff.mp hget
  apply Fin.ext
  simpa [idx] using congrArg Fin.val hidx

def ghostAddress (B : ℕ) : BirthAddress P (J + F.ell) n B → Prop
  | .inl _ => False
  | .inr (.inl _) => False
  | .inr (.inr _) => True

def addressVisit (B : ℕ) : BirthAddress P (J + F.ell) n B → Fin (n + 1)
  | .inl _ => 0
  | .inr (.inl (i, _, _)) => i.succ
  | .inr (.inr (i, _, _)) => i

/-- The prime identity recorded by an address; ghost addresses are partial
outside the performed domain. -/
def addressPrime (Q : Erdos821.S2Core.ResiduePath A n) (S : LifespanAssignment P n)
    (B : ℕ) : BirthAddress P (J + F.ell) n B → Option (Σ g : P.BigGroup, P.Prime g.val)
  | .inl (g, h) => some ⟨g, Q.labels 0 g.val h⟩
  | .inr (.inl (i, g, h)) => some ⟨g, Q.target i g.val h⟩
  | .inr (.inr (i, g, h)) =>
      if hh : h.val < (Q.ghostBirthPrimes S i g).card then
        some ⟨g, Q.ghostBatchLabels S i g ⟨h.val, hh⟩⟩
      else none

/-- Every performed address records its prime's assigned start and whether
that start is active or ghosted. -/
theorem address_birth_classification
    (Q : Erdos821.S2Core.ResiduePath A n) (S : LifespanAssignment P n)
    (hQ : Q.Valid) (hS : Q.lifespanValid S)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (y : P.SmallResidues) (B : ℕ)
    (a : BirthAddress P (J + F.ell) n B)
    (ha : (Q.reconstructedHistory S hS y).addressPerformed B a) :
    ∃ g : P.BigGroup, ∃ p : P.Prime g.val, ∃ b : Fin (n + 1),
      addressPrime Q S B a = some ⟨g, p⟩ ∧
      (Q.reconstructedHistory S hS y).addressValue B a = p.val ∧
      (∃ stop, S g p = some (b, stop)) ∧
      b = addressVisit (P := P) (J := J) (F := F) (n := n) B a ∧
      (ghostAddress (P := P) (J := J) (F := F) (n := n) B a ↔
        b ∉ Q.activeVisits g p) := by
  cases a with
  | inl addr =>
      rcases addr with ⟨g, h⟩
      let p := Q.labels 0 g.val h
      have hactive : (0 : Fin (n + 1)) ∈ Q.activeVisits g p := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, ⟨h, rfl⟩⟩
      obtain ⟨stop, hspan⟩ := initial_birth_at_zero Q S hS g h
      refine ⟨g, p, 0, ?_, ?_, ⟨stop, hspan⟩, rfl, ?_⟩
      · rfl
      · rfl
      · simp [ghostAddress, hactive]
  | inr rest =>
      cases rest with
      | inl addr =>
          rcases addr with ⟨i, g, h⟩
          have hfresh : h ∈ (Q.reconstructedHistory S hS y).freshTargetSlots i g := by
            simpa [MemoryHistory.addressPerformed] using ha
          obtain ⟨stop, hspan⟩ := fresh_birth_at_target Q S hQ hS hk y i g h hfresh
          let p := Q.target i g.val h
          have hactive : i.succ ∈ Q.activeVisits g p := Q.target_activeVisit i g h
          refine ⟨g, p, i.succ, ?_, ?_, ⟨stop, hspan⟩, rfl, ?_⟩
          · rfl
          · simp [MemoryHistory.addressValue, ResiduePath.reconstructedHistory,
              ResiduePath.target, ResiduePath.stateBefore, permuteActive,
              PrimeGroups.act, p]
          · simp [ghostAddress, hactive]
      | inr addr =>
          rcases addr with ⟨i, g, h⟩
          have hbatch : h.val <
              (((Q.reconstructedHistory S hS y).ghost i).2.1 g).val := by
            simpa [MemoryHistory.addressPerformed] using ha
          have hindex : h.val < (Q.ghostBirthPrimes S i g).card := by
            simpa [ResiduePath.reconstructedHistory,
              ResiduePath.reconstructedGhostChoice] using hbatch
          let p := Q.ghostBatchLabels S i g ⟨h.val, hindex⟩
          have hmem : p ∈ Q.ghostBirthPrimes S i g := by
            dsimp [p, ResiduePath.ghostBatchLabels]
            exact Finset.mem_toList.mp (List.get_mem _ _)
          have hborn : Q.ghostBirthAt g p (S g p) i := (Finset.mem_filter.mp hmem).2
          rcases hs : S g p with _ | ⟨birth, stop⟩
          · simp [ResiduePath.ghostBirthAt, hs] at hborn
          · have hborn' : birth = i ∧ i ∉ Q.activeVisits g p := by
              simpa [hs, ResiduePath.ghostBirthAt] using hborn
            rcases hborn' with ⟨hbirth, hnotactive⟩
            have hs' : S g p = some (i, stop) := by
              rw [hs, hbirth]
            have hvalue :
                (Q.reconstructedHistory S hS y).addressValue B
                  (.inr (.inr (i, g, h))) = p.val := by
              simp [MemoryHistory.addressValue, ResiduePath.reconstructedHistory,
                ResiduePath.reconstructedGhostChoice, hindex, p,
                ResiduePath.ghostBatchLabels]
            exact ⟨g, p, i, by simp [addressPrime, hindex, p], hvalue,
              ⟨stop, hs'⟩, rfl, by simp [ghostAddress, hnotactive]⟩

/-- Equal numerical birth values come from the same performed address. -/
theorem performed_address_value_injective
    (Q : Erdos821.S2Core.ResiduePath A n) (S : LifespanAssignment P n)
    (hQ : Q.Valid) (hS : Q.lifespanValid S)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (y : P.SmallResidues) (B : ℕ) :
    Set.InjOn (fun a =>
      (Q.reconstructedHistory S hS y).addressValue B a)
      (Finset.univ.filter ((Q.reconstructedHistory S hS y).addressPerformed B)) := by
  let H := Q.reconstructedHistory S hS y
  intro a ha b hb hab
  have haPerf : H.addressPerformed B a := (Finset.mem_filter.mp ha).2
  have hbPerf : H.addressPerformed B b := (Finset.mem_filter.mp hb).2
  obtain ⟨ga, pa, ba, hprimeA, hvalA, hspanA, hvisitA, hghostA⟩ :=
    address_birth_classification Q S hQ hS hk y B a (by simpa [H] using haPerf)
  obtain ⟨gb, pb, bb, hprimeB, hvalB, hspanB, hvisitB, hghostB⟩ :=
    address_birth_classification Q S hQ hS hk y B b (by simpa [H] using hbPerf)
  have hval : pa.val = pb.val := by
    calc
      pa.val = H.addressValue B a := hvalA.symm
      _ = H.addressValue B b := hab
      _ = pb.val := hvalB
  have hgroups : ga = gb := by
    apply Subtype.ext
    exact prime_group_eq pa pb hval
  subst gb
  have hprimes : pa = pb := Subtype.ext hval
  subst pb
  have hspanA' := hspanA
  have hspanB' := hspanB
  rcases hspanA' with ⟨sa, hsa⟩
  rcases hspanB' with ⟨sb, hsb⟩
  have hpair : (ba, sa) = (bb, sb) := Option.some.inj (hsa.symm.trans hsb)
  have hbirth : ba = bb := congrArg Prod.fst hpair
  have hvisitEq : addressVisit (P := P) (J := J) (F := F) (n := n) B a =
      addressVisit (P := P) (J := J) (F := F) (n := n) B b := by
    calc
      _ = ba := hvisitA.symm
      _ = bb := hbirth
      _ = _ := hvisitB
  have hsameGhost : ghostAddress (P := P) (J := J) (F := F) (n := n) B a ↔
      ghostAddress (P := P) (J := J) (F := F) (n := n) B b := by
    calc
      _ ↔ ba ∉ Q.activeVisits ga pa := hghostA
      _ ↔ bb ∉ Q.activeVisits ga pa := by rw [hbirth]
      _ ↔ _ := hghostB.symm
  have hprimeAddress : addressPrime Q S B a = addressPrime Q S B b :=
    hprimeA.trans hprimeB.symm
  cases a with
  | inl xa =>
      rcases xa with ⟨ga', haSlot⟩
      cases b with
      | inl xb =>
          rcases xb with ⟨gb', hbSlot⟩
          have hraw : (Q.labels 0 ga'.val haSlot).val =
              (Q.labels 0 gb'.val hbSlot).val := by
            simpa [H, MemoryHistory.addressValue, ResiduePath.reconstructedHistory,
              ResiduePath.stateBefore] using hab
          have hgroup : ga' = gb' := by
            apply Subtype.ext
            exact prime_group_eq (Q.labels 0 ga'.val haSlot)
              (Q.labels 0 gb'.val hbSlot) hraw
          subst gb'
          have hlabels : Q.labels 0 ga'.val haSlot = Q.labels 0 ga'.val hbSlot :=
            Subtype.ext hraw
          have hslot := (hQ.1 0 ga'.val) hlabels
          subst hbSlot
          rfl
      | inr rb =>
          cases rb with
          | inl xb =>
              rcases xb with ⟨i, gb', hbSlot⟩
              have htime := hvisitEq
              change (0 : Fin (n + 1)) = i.succ at htime
              have hfalse : False := by
                have hv := congrArg Fin.val htime
                simp only [Fin.val_zero, Fin.val_succ] at hv
                omega
              exact hfalse.elim
          | inr xb =>
              have hf : False := by simpa [ghostAddress] using hsameGhost
              exact hf.elim
  | inr ra =>
      cases ra with
      | inl xa =>
          rcases xa with ⟨i, ga', haSlot⟩
          cases b with
          | inl xb =>
              rcases xb with ⟨gb', hbSlot⟩
              have htime := hvisitEq
              change (i.succ : Fin (n + 1)) = 0 at htime
              have hfalse : False := by
                have hv := congrArg Fin.val htime
                simp only [Fin.val_zero, Fin.val_succ] at hv
                omega
              exact hfalse.elim
          | inr rb =>
              cases rb with
              | inl xb =>
                  rcases xb with ⟨j, gb', hbSlot⟩
                  have htime := hvisitEq
                  simp [addressVisit] at htime
                  have hij : i = j := by
                    apply Fin.ext
                    have hv := congrArg Fin.val htime
                    simpa only [Fin.val_succ] using hv
                  have hraw : (Q.target i ga'.val haSlot).val =
                      (Q.target j gb'.val hbSlot).val := by
                    simpa [H, MemoryHistory.addressValue, ResiduePath.reconstructedHistory,
                      ResiduePath.stateBefore, ResiduePath.target, permuteActive,
                      PrimeGroups.act] using hab
                  have hgroup : ga' = gb' := by
                    apply Subtype.ext
                    exact prime_group_eq (Q.target i ga'.val haSlot)
                      (Q.target j gb'.val hbSlot) hraw
                  subst gb'
                  subst j
                  have hlabels : Q.target i ga'.val haSlot = Q.target i ga'.val hbSlot :=
                    Subtype.ext hraw
                  have hslot := Q.target_injective hQ i ga'.val hlabels
                  subst hbSlot
                  rfl
              | inr xb =>
                  have hf : False := by simpa [ghostAddress] using hsameGhost
                  exact hf.elim
      | inr xa =>
          rcases xa with ⟨i, ga', haSlot⟩
          cases b with
          | inl xb =>
              have hf : False := by simpa [ghostAddress] using hsameGhost.symm
              exact hf.elim
          | inr rb =>
              cases rb with
              | inl xb =>
                  have hf : False := by simpa [ghostAddress] using hsameGhost.symm
                  exact hf.elim
              | inr xb =>
                  rcases xb with ⟨j, gb', hbSlot⟩
                  have htime := hvisitEq
                  simp [addressVisit] at htime
                  have hij : i = j := htime
                  have hindexA : haSlot.val < (Q.ghostBirthPrimes S i ga').card := by
                    simpa [H, MemoryHistory.addressPerformed,
                      ResiduePath.reconstructedHistory, ResiduePath.reconstructedGhostChoice]
                      using haPerf
                  have hindexB : hbSlot.val < (Q.ghostBirthPrimes S j gb').card := by
                    simpa [H, MemoryHistory.addressPerformed,
                      ResiduePath.reconstructedHistory, ResiduePath.reconstructedGhostChoice]
                      using hbPerf
                  have hraw :
                      (Q.ghostBatchLabels S i ga' ⟨haSlot.val, hindexA⟩).val =
                        (Q.ghostBatchLabels S j gb' ⟨hbSlot.val, hindexB⟩).val := by
                    simpa [H, MemoryHistory.addressValue, ResiduePath.reconstructedHistory,
                      ResiduePath.reconstructedGhostChoice, hindexA, hindexB,
                      ResiduePath.ghostBatchLabels] using hab
                  have hgroup : ga' = gb' := by
                    apply Subtype.ext
                    exact prime_group_eq
                      (Q.ghostBatchLabels S i ga' ⟨haSlot.val, hindexA⟩)
                      (Q.ghostBatchLabels S j gb' ⟨hbSlot.val, hindexB⟩) hraw
                  subst gb'
                  subst j
                  have hlabels : Q.ghostBatchLabels S i ga' ⟨haSlot.val, hindexA⟩ =
                      Q.ghostBatchLabels S i ga' ⟨hbSlot.val, hindexB⟩ := Subtype.ext hraw
                  have hslots := ghostBatchLabels_injective Q S i ga' hlabels
                  have hslot : haSlot = hbSlot := by
                    apply Fin.ext
                    simpa using congrArg Fin.val hslots
                  subst hbSlot
                  rfl

end Erdos821.P3Birth

namespace Erdos821.S2Core

theorem SpanBirthTask_proof : SpanBirthTask := by
  intro F P J m n A Q S hQ hS hk y
  let H := Q.reconstructedHistory S hS y
  let B := Erdos821.P3Birth.MemoryHistory.birthCutoff H
  have htruncated : H.Truncated B := by
    exact Erdos821.P3Birth.MemoryHistory.birthCutoff_truncated H
  rw [H.distinctBirths_iff_addresses B htruncated]
  exact Erdos821.P3Birth.performed_address_value_injective Q S hQ hS hk y B


end Erdos821.S2Core
