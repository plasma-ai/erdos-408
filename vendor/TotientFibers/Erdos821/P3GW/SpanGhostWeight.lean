import Erdos821.S2.SpanGhostWeightTask

/-! The factorial-normalized local ghost coefficient, factored by prime spans. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Gw

open Erdos821.S2Core
open Erdos821.S2Core.ResiduePath
open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
variable {A : Model F P J m}

namespace ResiduePath

variable {Q : Erdos821.S2Core.ResiduePath A n}

def pendingZeroPrimes (S : LifespanAssignment P n) (i : Fin (n + 1))
    (g : P.BigGroup) : Finset (P.Prime g.val) :=
  Q.pendingBeforePrimes S i g |>.filter
    (fun p => ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val) = 0)

def survivingZeroHitPrimes (S : LifespanAssignment P n) (i : Fin (n + 1))
    (g : P.BigGroup) : Finset (P.Prime g.val) :=
  Finset.univ.filter (fun p =>
    Q.pendingBefore g p (S g p) i ∧ Q.pendingAfter g p (S g p) i ∧
      ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val) = 0)

theorem pendingBefore_stop_or_after (S : LifespanAssignment P n) (i : Fin (n + 1))
    (g : P.BigGroup) (p : P.Prime g.val)
    (h : Q.pendingBefore g p (S g p) i) :
    Q.ghostStopAt g p (S g p) i ∨ Q.pendingAfter g p (S g p) i := by
  rcases he : S g p with _ | ⟨birth, stop⟩
  · rw [he] at h
    have hf : False := by
      simpa only [Erdos821.S2Core.ResiduePath.pendingBefore] using h
    exact hf.elim
  · rw [he] at h
    simp only [Erdos821.S2Core.ResiduePath.pendingBefore] at h
    rcases h with ⟨hb, hs, ha⟩
    by_cases hstop : stop = i
    · left
      exact ⟨hstop, ha⟩
    · right
      refine ⟨le_of_lt hb, ?_, ha⟩
      have : i.val < stop.val := by omega
      exact Fin.lt_def.mpr this

theorem stop_hits_disjoint (S : LifespanAssignment P n) (i : Fin (n + 1))
    (g : P.BigGroup) :
    Disjoint (Q.ghostStopPrimes S i g)
      (survivingZeroHitPrimes (Q := Q) S i g) := by
  apply Finset.disjoint_left.mpr
  intro p hp hh
  have hs := (Finset.mem_filter.mp hp).2
  have hh' := (Finset.mem_filter.mp hh).2
  rcases he : S g p with _ | ⟨birth, stop⟩
  · rw [he] at hs
    have hf : False := by simpa only [ghostStopAt] using hs
    exact hf.elim
  · rw [he] at hs hh'
    simp only [ghostStopAt, pendingAfter] at hs hh'
    obtain ⟨rfl, _⟩ := hs
    omega

theorem pendingZeroPrimes_eq_stop_union_hits
    (S : LifespanAssignment P n) (hS : Q.lifespanValid S)
    (i : Fin (n + 1)) (g : P.BigGroup) :
      pendingZeroPrimes (Q := Q) S i g =
      Q.ghostStopPrimes S i g ∪ survivingZeroHitPrimes (Q := Q) S i g := by
  ext p
  constructor
  · intro hp
    simp only [pendingZeroPrimes, Finset.mem_filter] at hp
    have hbefore := hp.1
    have hzero := hp.2
    have hbefore' : Q.pendingBefore g p (S g p) i := by
      simpa only [pendingBeforePrimes, Finset.mem_filter, Finset.mem_univ, true_and] using hbefore
    rcases pendingBefore_stop_or_after (Q := Q) S i g p hbefore' with hs | ha
    · apply Finset.mem_union.mpr
      left
      change p ∈ Finset.univ.filter
        (fun q : P.Prime g.val => Q.ghostStopAt g q (S g q) i)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hs⟩
    · apply Finset.mem_union.mpr
      right
      change p ∈ Finset.univ.filter
        (fun q : P.Prime g.val =>
          Q.pendingBefore g q (S g q) i ∧ Q.pendingAfter g q (S g q) i ∧
            ((Q.offset i - Q.spanAnchor (S g q) : ℤ) : ZMod q.val) = 0)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, ⟨hbefore', ha, hzero⟩⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hs | hh
    · have hs' : p ∈ Q.ghostStopPrimes S i g := hs
      have hbefore := Q.ghostStopPrimes_subset S hS i g hs'
      have hzero := Q.ghostStop_residue_zero S hS i g p hs'
      simp only [pendingZeroPrimes, Finset.mem_filter]
      exact ⟨hbefore, hzero⟩
    · have hh' := (Finset.mem_filter.mp hh).2
      simp only [pendingZeroPrimes, Finset.mem_filter]
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh'.1⟩, hh'.2.2⟩

theorem zeroMemoryIndices_card_eq_pendingZeroPrimes
    (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) :
    (zeroMemoryIndices (Q.memoryBefore S i g)).card =
      (pendingZeroPrimes (Q := Q) S i g).card := by
  rw [zeroMemoryIndices_card, Q.memoryBefore_eq_map]
  simp only [Multiset.filter_map, Multiset.card_map]
  rfl

theorem ghostBatchLabels_prod (S : LifespanAssignment P n) (i : Fin (n + 1))
    (g : P.BigGroup) (f : P.Prime g.val → ℝ) :
    (∏ h : Fin (Q.ghostBirthPrimes S i g).card, f (Q.ghostBatchLabels S i g h)) =
      ∏ p ∈ Q.ghostBirthPrimes S i g, f p := by
  calc
    _ = ((List.ofFn (Q.ghostBatchLabels S i g)).map f).prod := by
      rw [List.map_ofFn, List.prod_ofFn]
      rfl
    _ = ((Q.ghostBirthPrimes S i g).toList.map f).prod := by
      rw [Q.ghostBatchLabels_enumeration]
    _ = ∏ p ∈ Q.ghostBirthPrimes S i g, f p :=
      Finset.prod_map_toList _ _

end ResiduePath

theorem mul_self_inv_factor (a b : ℝ) (ha : a ≠ 0) :
    a * (a * b)⁻¹ = b⁻¹ := by
  by_cases hb : b = 0
  · simp [hb]
  · field_simp [ha, hb]

theorem value_mul_tiltedMu (F : FixedData) (P : PrimeGroups) (n : ℕ)
    (g : P.Group) (p : P.Prime g) (hV : P.V g ≠ 0) :
    P.V g * tiltedMu F P n g p = (p.val * baselinePrime F n p.val)⁻¹ := by
  unfold tiltedMu
  simpa only [mul_assoc] using
    mul_self_inv_factor (P.V g) (p.val * baselinePrime F n p.val) hV

theorem groupGhostWeight_factor
    (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m)
    (Q : Erdos821.S2Core.ResiduePath A n) (S : LifespanAssignment P n)
    (hV : ∀ g, P.V g ≠ 0) (hS : Q.lifespanValid S)
    (i : Fin (n + 1)) (g : P.BigGroup) :
    (-eta F n i) ^ (Q.ghostTerminationIndices S i g).card *
        visitQ F.q n i ^
          ((zeroMemoryIndices (Q.memoryBefore S i g)).card -
            (Q.ghostTerminationIndices S i g).card) *
        ((Q.ghostBirthPrimes S i g).card.factorial : ℝ)⁻¹ *
        (-eta F n i * P.V g.val) ^ (Q.ghostBirthPrimes S i g).card *
        (∏ h : Fin (Q.ghostBirthPrimes S i g).card,
          tiltedMu F P n g.val (Q.ghostBatchLabels S i g h)) *
        (Q.ghostBirthPrimes S i g).card.factorial =
      ∏ p : P.Prime g.val, Q.spanGhostFactor S i g p := by
  classical
  let B := Q.ghostBirthPrimes S i g
  let T := Q.ghostStopPrimes S i g
  let R := ResiduePath.survivingZeroHitPrimes (Q := Q) S i g
  have hpart := ResiduePath.pendingZeroPrimes_eq_stop_union_hits (Q := Q) S hS i g
  have hdis := ResiduePath.stop_hits_disjoint (Q := Q) S i g
  have hZcard :
      (zeroMemoryIndices (Q.memoryBefore S i g)).card = T.card + R.card := by
    rw [ResiduePath.zeroMemoryIndices_card_eq_pendingZeroPrimes (Q := Q) S i g, hpart]
    exact Finset.card_union_of_disjoint hdis
  have hterm : (Q.ghostTerminationIndices S i g).card = T.card := by
    have hdeleted := congrArg Multiset.card (Q.ghostDeleted_eq_map S i g)
    simp only [deleteMemoryIndices_eq_map, Multiset.card_map] at hdeleted
    change (Finset.univ \ Q.ghostTerminationIndices S i g).card =
      (Q.pendingBeforePrimes S i g \ Q.ghostStopPrimes S i g).card at hdeleted
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_sdiff_of_subset (Q.ghostStopPrimes_subset S hS i g)] at hdeleted
    have hUniv :
        (Finset.univ : Finset (Fin (Q.memoryBefore S i g).card)).card =
          (Q.memoryBefore S i g).card := by simp
    rw [hUniv] at hdeleted
    have hmem := Q.memoryBefore_card S i g
    have htermLE' :=
      Finset.card_le_card (Finset.subset_univ (Q.ghostTerminationIndices S i g))
    have htermLE :
        (Q.ghostTerminationIndices S i g).card ≤ (Q.memoryBefore S i g).card := by
      simpa only [Finset.card_univ, Fintype.card_fin] using htermLE'
    have hstopLE :
        (Q.ghostStopPrimes S i g).card ≤ (Q.pendingBeforePrimes S i g).card :=
      Finset.card_le_card (Q.ghostStopPrimes_subset S hS i g)
    have hsub :
        (Q.pendingBeforePrimes S i g).card -
            (Q.ghostTerminationIndices S i g).card =
          (Q.pendingBeforePrimes S i g).card - T.card := by
      have hmemsub := congrArg
        (fun k : ℕ => k - (Q.ghostTerminationIndices S i g).card) hmem
      exact hmemsub.symm.trans hdeleted
    have htermLEBefore :
        (Q.ghostTerminationIndices S i g).card ≤ (Q.pendingBeforePrimes S i g).card := by
      omega
    let t : ℕ := (Q.ghostTerminationIndices S i g).card
    let s : ℕ := T.card
    have hsub' :
        (Q.pendingBeforePrimes S i g).card - t =
          (Q.pendingBeforePrimes S i g).card - s := by
      simpa [t, s] using hsub
    have ht' : t ≤ (Q.pendingBeforePrimes S i g).card := by
      simpa [t] using htermLEBefore
    have hs' : s ≤ (Q.pendingBeforePrimes S i g).card := by
      simpa [s] using hstopLE
    have hts : t = s := by omega
    simpa [t, s] using hts
  have hexponent :
      (zeroMemoryIndices (Q.memoryBefore S i g)).card -
          (Q.ghostTerminationIndices S i g).card = R.card := by
    rw [hZcard]
    rw [hterm]
    omega
  have hfact : (B.card.factorial : ℝ) ≠ 0 := by
    have hpNat : 0 < Nat.factorial B.card := Nat.factorial_pos _
    exact_mod_cast (Nat.ne_of_gt hpNat)
  have hbirth :
      (-eta F n i * P.V g.val) ^ B.card *
          (∏ h : Fin B.card, tiltedMu F P n g.val (Q.ghostBatchLabels S i g h)) =
        ∏ p ∈ B, (-eta F n i * (p.val * baselinePrime F n p.val)⁻¹) := by
    calc
      _ = ∏ h : Fin B.card,
            (-eta F n i * P.V g.val) *
              tiltedMu F P n g.val (Q.ghostBatchLabels S i g h) := by
        simpa [B] using
          (Finset.pow_card_mul_prod (s := Finset.univ)
            (b := -eta F n i * P.V g.val)
            (f := fun h : Fin B.card =>
              tiltedMu F P n g.val (Q.ghostBatchLabels S i g h)))
      _ = ∏ h : Fin B.card,
            (-eta F n i *
              ((Q.ghostBatchLabels S i g h).val *
                baselinePrime F n (Q.ghostBatchLabels S i g h).val)⁻¹) := by
        apply Finset.prod_congr rfl
        intro h hh
        rw [show (-eta F n i * P.V g.val) *
              tiltedMu F P n g.val (Q.ghostBatchLabels S i g h) =
            (-eta F n i) *
              (P.V g.val * tiltedMu F P n g.val (Q.ghostBatchLabels S i g h)) by ring]
        rw [value_mul_tiltedMu F P n g.val (Q.ghostBatchLabels S i g h) (hV g)]
      _ = ∏ p ∈ B, (-eta F n i * (p.val * baselinePrime F n p.val)⁻¹) := by
        exact ResiduePath.ghostBatchLabels_prod (Q := Q) S i g
          (fun p => -eta F n i * (p.val * baselinePrime F n p.val)⁻¹)
  have hstop : ∏ p ∈ T, (-eta F n i) = (-eta F n i) ^ T.card := by
    rw [Finset.prod_const]
  have hhit : ∏ p ∈ R, visitQ F.q n i = visitQ F.q n i ^ R.card := by
    rw [Finset.prod_const]
  have hfactor :
      (∏ p : P.Prime g.val,
        Q.spanGhostFactor S i g p) =
        (∏ p ∈ B, (-eta F n i * (p.val * baselinePrime F n p.val)⁻¹)) *
          (∏ p ∈ T, (-eta F n i)) *
          (∏ p ∈ R, visitQ F.q n i) := by
    calc
      _ = ∏ p : P.Prime g.val,
          (if p ∈ B then -eta F n i * (p.val * baselinePrime F n p.val)⁻¹ else 1) *
          (if p ∈ T then -eta F n i else 1) *
          (if p ∈ R then visitQ F.q n i else 1) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hB : p ∈ B ↔ Q.ghostBirthAt g p (S g p) i := by
          change p ∈ Finset.univ.filter
            (fun q : P.Prime g.val => Q.ghostBirthAt g q (S g q) i) ↔ _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hT : p ∈ T ↔ Q.ghostStopAt g p (S g p) i := by
          change p ∈ Finset.univ.filter
            (fun q : P.Prime g.val => Q.ghostStopAt g q (S g q) i) ↔ _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hR :
            p ∈ R ↔ Q.pendingBefore g p (S g p) i ∧ Q.pendingAfter g p (S g p) i ∧
              ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val) = 0 := by
          change p ∈ Finset.univ.filter
            (fun q : P.Prime g.val =>
              Q.pendingBefore g q (S g q) i ∧ Q.pendingAfter g q (S g q) i ∧
                ((Q.offset i - Q.spanAnchor (S g q) : ℤ) : ZMod q.val) = 0) ↔ _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp only [Erdos821.S2Core.ResiduePath.spanGhostFactor, ← hB, ← hT, ← hR]
      _ = _ := by
        simp only [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq]
  calc
    _ = ((-eta F n i) ^ T.card * visitQ F.q n i ^ R.card) *
          (∏ p ∈ B, (-eta F n i * (p.val * baselinePrime F n p.val)⁻¹)) := by
      rw [hexponent, hterm]
      calc
        _ = ((-eta F n i) ^ T.card * visitQ F.q n i ^ R.card) *
              (((B.card.factorial : ℝ)⁻¹ * (B.card.factorial : ℝ)) *
                ((-eta F n i * P.V g.val) ^ B.card *
                  (∏ h : Fin B.card,
                    tiltedMu F P n g.val (Q.ghostBatchLabels S i g h)))) := by
          ring
        _ = ((-eta F n i) ^ T.card * visitQ F.q n i ^ R.card) *
              ((-eta F n i * P.V g.val) ^ B.card *
                (∏ h : Fin B.card,
                  tiltedMu F P n g.val (Q.ghostBatchLabels S i g h))) := by
          rw [inv_mul_cancel₀ hfact, one_mul]
        _ = _ := by rw [hbirth]
    _ = ∏ p : P.Prime g.val,
          Q.spanGhostFactor S i g p := by
      rw [← hstop, ← hhit, hfactor]
      ring

theorem SpanGhostWeightTask_proof : Erdos821.S2Core.SpanGhostWeightTask := by
  intro F P J m n A Q S hV hS y i
  classical
  have hweight :
      ghostChoiceWeight F n 1 i (Q.reconstructedGhostChoice S hS y i) =
        ∏ g : P.BigGroup,
          (-eta F n i) ^ (Q.ghostTerminationIndices S i g).card *
            visitQ F.q n i ^
              ((zeroMemoryIndices (Q.memoryBefore S i g)).card -
                (Q.ghostTerminationIndices S i g).card) *
            ((Q.ghostBirthPrimes S i g).card.factorial : ℝ)⁻¹ *
            (-eta F n i * P.V g.val) ^ (Q.ghostBirthPrimes S i g).card *
            (∏ h : Fin (Q.ghostBirthPrimes S i g).card,
              tiltedMu F P n g.val (Q.ghostBatchLabels S i g h)) := by
    unfold ghostChoiceWeight
    apply Finset.prod_congr rfl
    intro g hg
    simp only [Erdos821.S2Core.ResiduePath.reconstructedGhostChoice,
      Erdos821.S2Core.ResiduePath.stateBefore, div_one, one_pow] <;> rfl
  calc
    _ = (∏ g : P.BigGroup,
          (-eta F n i) ^ (Q.ghostTerminationIndices S i g).card *
            visitQ F.q n i ^
              ((zeroMemoryIndices (Q.memoryBefore S i g)).card -
                (Q.ghostTerminationIndices S i g).card) *
            ((Q.ghostBirthPrimes S i g).card.factorial : ℝ)⁻¹ *
            (-eta F n i * P.V g.val) ^ (Q.ghostBirthPrimes S i g).card *
            (∏ h : Fin (Q.ghostBirthPrimes S i g).card,
              tiltedMu F P n g.val (Q.ghostBatchLabels S i g h))) *
          ((∏ g : P.BigGroup,
            (Q.ghostBirthPrimes S i g).card.factorial) : ℝ) := by
      rw [hweight]
    _ = ∏ g : P.BigGroup,
          (((-eta F n i) ^ (Q.ghostTerminationIndices S i g).card *
            visitQ F.q n i ^
              ((zeroMemoryIndices (Q.memoryBefore S i g)).card -
                (Q.ghostTerminationIndices S i g).card) *
            ((Q.ghostBirthPrimes S i g).card.factorial : ℝ)⁻¹ *
            (-eta F n i * P.V g.val) ^ (Q.ghostBirthPrimes S i g).card *
            (∏ h : Fin (Q.ghostBirthPrimes S i g).card,
              tiltedMu F P n g.val (Q.ghostBatchLabels S i g h))) *
            (Q.ghostBirthPrimes S i g).card.factorial) := by
      exact Finset.prod_mul_distrib.symm
    _ = ∏ g : P.BigGroup, ∏ p : P.Prime g.val, Q.spanGhostFactor S i g p := by
      apply Finset.prod_congr rfl
      intro g hg
      exact groupGhostWeight_factor F P J m n A Q S hV hS i g

end Erdos821.P3Gw

