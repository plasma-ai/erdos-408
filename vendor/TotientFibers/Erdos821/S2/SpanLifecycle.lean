import Erdos821.S2.HistoryAnchors

/-! Finite prime lifespans and their before/after ghost occupancy. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

abbrev PrimeSpan (n : ℕ) := Option (Fin (n + 1) × Fin (n + 1))

namespace ResiduePath

variable {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n)

def activeVisits (g : P.BigGroup) (p : P.Prime g.val) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => ∃ j : Fin (J + F.ell), Q.labels i g.val j = p)

def spanValid (g : P.BigGroup) (p : P.Prime g.val) : PrimeSpan n → Prop
  | none => Q.activeVisits g p = ∅
  | some (birth, stop) =>
      birth ≤ stop ∧ (Q.activeVisits g p = ∅ → birth < stop) ∧
      (∀ i ∈ Q.activeVisits g p, birth ≤ i ∧ i ≤ stop) ∧
      ((Q.offset stop - Q.offset birth : ℤ) : ZMod p.val) = 0 ∧
      (∀ i ∈ Q.activeVisits g p, ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0)

def pendingBefore (g : P.BigGroup) (p : P.Prime g.val) (span : PrimeSpan n) (i : Fin (n + 1)) : Prop :=
  match span with
  | none => False
  | some (birth, stop) => birth < i ∧ i ≤ stop ∧ i ∉ Q.activeVisits g p

def pendingAfter (g : P.BigGroup) (p : P.Prime g.val) (span : PrimeSpan n) (i : Fin (n + 1)) : Prop :=
  match span with
  | none => False
  | some (birth, stop) => birth ≤ i ∧ i < stop ∧ i ∉ Q.activeVisits g p

def ghostBirthAt (g : P.BigGroup) (p : P.Prime g.val) (span : PrimeSpan n) (i : Fin (n + 1)) : Prop :=
  match span with
  | none => False
  | some (birth, _) => birth = i ∧ i ∉ Q.activeVisits g p

def ghostStopAt (g : P.BigGroup) (p : P.Prime g.val) (span : PrimeSpan n) (i : Fin (n + 1)) : Prop :=
  match span with
  | none => False
  | some (_, stop) => stop = i ∧ i ∉ Q.activeVisits g p

def spanAnchor : PrimeSpan n → ℤ
  | none => 0
  | some (birth, _) => Q.offset birth

/-- Original marks charge once per maximal consecutive active run. -/
def activeRunStarts (g : P.BigGroup) (p : P.Prime g.val) : Finset (Fin (n + 1)) :=
  (Q.activeVisits g p).filter (fun i => ¬ ∃ j ∈ Q.activeVisits g p, j.val + 1 = i.val)

def spanWeight (g : P.BigGroup) (p : P.Prime g.val) (span : PrimeSpan n) : ℝ :=
  match span with
  | none => if Q.activeVisits g p = ∅ then 1 else 0
  | some (birth, stop) =>
      if Q.spanValid g p span then
        (p.val * baselinePrime F n p.val : ℝ)⁻¹ *
        (if birth ∈ Q.activeVisits g p then 1 else -eta F n birth) *
        (if stop ∈ Q.activeVisits g p then 1 else -eta F n stop) *
        ∏ i ∈ Finset.univ.filter (fun i => birth < i ∧ i < stop ∧ i ∉ Q.activeVisits g p),
          (1 - eta F n i * if ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0 then 1 else 0)
      else 0

end ResiduePath

abbrev LifespanAssignment (P : PrimeGroups) (n : ℕ) := (g : P.BigGroup) → P.Prime g.val → PrimeSpan n

namespace ResiduePath

variable {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n)

def lifespanValid (S : LifespanAssignment P n) : Prop := ∀ g p, Q.spanValid g p (S g p)

def memoryBefore (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) : P.Memory g.val :=
  ∑ p : P.Prime g.val, if Q.pendingBefore g p (S g p) i then
    {(⟨p, ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val)} else 0

def memoryAfter (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) : P.Memory g.val :=
  ∑ p : P.Prime g.val, if Q.pendingAfter g p (S g p) i then
    {(⟨p, ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val)} else 0

def stateBefore (S : LifespanAssignment P n) (y : P.SmallResidues) (i : Fin (n + 1)) :
    P.MemoryState (J + F.ell) :=
  (translateSmallResidues (Q.offset i) y, Q.labels i, Q.memoryBefore S i)

def stateAfter (S : LifespanAssignment P n) (y : P.SmallResidues) (i : Fin (n + 1)) :
    P.MemoryState (J + F.ell) :=
  (translateSmallResidues (Q.offset i) y, Q.labels i, Q.memoryAfter S i)

def pendingBeforePrimes (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) : Finset (P.Prime g.val) :=
  Finset.univ.filter (fun p => Q.pendingBefore g p (S g p) i)

def pendingAfterPrimes (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) : Finset (P.Prime g.val) :=
  Finset.univ.filter (fun p => Q.pendingAfter g p (S g p) i)

def ghostBirthPrimes (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) : Finset (P.Prime g.val) :=
  Finset.univ.filter (fun p => Q.ghostBirthAt g p (S g p) i)

def ghostStopPrimes (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) : Finset (P.Prime g.val) :=
  Finset.univ.filter (fun p => Q.ghostStopAt g p (S g p) i)

theorem memoryBefore_eq_map (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) :
    Q.memoryBefore S i g = (Q.pendingBeforePrimes S i g).val.map
      (fun p => (⟨p, ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val)) := by
  rw [memoryBefore, ← Finset.sum_filter, sum_singletons_eq_map]
  rfl

theorem memoryAfter_eq_map (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) :
    Q.memoryAfter S i g = (Q.pendingAfterPrimes S i g).val.map
      (fun p => (⟨p, ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val)) := by
  rw [memoryAfter, ← Finset.sum_filter, sum_singletons_eq_map]
  rfl

theorem pendingPrimes_memoryBefore (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) :
    pendingPrimes (Q.memoryBefore S i g) = (Q.pendingBeforePrimes S i g).val := by
  rw [memoryBefore_eq_map]
  simp only [pendingPrimes, Multiset.map_map]
  exact Multiset.map_id _

theorem pendingPrimes_memoryAfter (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) :
    pendingPrimes (Q.memoryAfter S i g) = (Q.pendingAfterPrimes S i g).val := by
  rw [memoryAfter_eq_map]
  simp only [pendingPrimes, Multiset.map_map]
  exact Multiset.map_id _

theorem memoryBefore_card (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) :
    (Q.memoryBefore S i g).card = (Q.pendingBeforePrimes S i g).card := by
  rw [memoryBefore_eq_map, Multiset.card_map]
  rfl

theorem memoryAfter_card (S : LifespanAssignment P n) (i : Fin (n + 1)) (g : P.BigGroup) :
    (Q.memoryAfter S i g).card = (Q.pendingAfterPrimes S i g).card := by
  rw [memoryAfter_eq_map, Multiset.card_map]
  rfl


theorem pendingBefore_zero (g : P.BigGroup) (p : P.Prime g.val) (span : PrimeSpan n) :
    ¬ Q.pendingBefore g p span 0 := by
  rcases span with _ | ⟨birth, stop⟩
  · simp [pendingBefore]
  · simp [pendingBefore]

theorem pendingAfter_last (g : P.BigGroup) (p : P.Prime g.val) (span : PrimeSpan n) :
    ¬ Q.pendingAfter g p span (Fin.last n) := by
  rcases span with _ | ⟨birth, stop⟩
  · simp [pendingAfter]
  · intro hs
    have hlt := hs.2.1
    change n < stop.val at hlt
    have hstop := stop.isLt
    omega

theorem memoryBefore_zero (S : LifespanAssignment P n) (g : P.BigGroup) : Q.memoryBefore S 0 g = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  exact ite_eq_right (Q.pendingBefore_zero g p (S g p))

theorem memoryAfter_last (S : LifespanAssignment P n) (g : P.BigGroup) :
    Q.memoryAfter S (Fin.last n) g = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  exact ite_eq_right (Q.pendingAfter_last g p (S g p))

theorem coincident_span_active (g : P.BigGroup) (p : P.Prime g.val) (birth stop : Fin (n + 1))
    (hs : Q.spanValid g p (some (birth, stop))) (he : birth = stop) : birth ∈ Q.activeVisits g p := by
  have hn : Q.activeVisits g p ≠ ∅ := by
    intro hn
    have hlt := hs.2.1 hn
    rw [he] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hn
  have hc := hs.2.2.1 i hi
  have hie : i = birth := le_antisymm (he.symm ▸ hc.2) hc.1
  exact hie ▸ hi

/-- Termination uses old pending particles; a new ghost starts only afterwards. -/
theorem ghost_occupancy_update (g : P.BigGroup) (p : P.Prime g.val) (span : PrimeSpan n)
    (hs : Q.spanValid g p span) (i : Fin (n + 1)) :
    ((Q.pendingBefore g p span i ∧ ¬ Q.ghostStopAt g p span i) ∨ Q.ghostBirthAt g p span i) ↔
      Q.pendingAfter g p span i := by
  rcases span with _ | ⟨birth, stop⟩
  · simp [pendingBefore, pendingAfter, ghostStopAt, ghostBirthAt]
  · by_cases hi : i ∈ Q.activeVisits g p
    · simp [pendingBefore, pendingAfter, ghostStopAt, ghostBirthAt, hi]
    · have hord := hs.1
      have hbad : ¬ (birth = stop ∧ birth = i) := by
        rintro ⟨he, rfl⟩
        exact hi (Q.coincident_span_active g p birth stop hs he)
      simp only [pendingBefore, pendingAfter, ghostStopAt, ghostBirthAt, hi, not_false_eq_true, and_true]
      omega

theorem ghostBirthPrimes_subset (S : LifespanAssignment P n) (hS : Q.lifespanValid S)
    (i : Fin (n + 1)) (g : P.BigGroup) : Q.ghostBirthPrimes S i g ⊆ Q.pendingAfterPrimes S i g := by
  intro p hp
  have hb := (Finset.mem_filter.mp hp).2
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, (Q.ghost_occupancy_update g p (S g p) (hS g p) i).mp (Or.inr hb)⟩

theorem ghostStopPrimes_subset (S : LifespanAssignment P n) (hS : Q.lifespanValid S)
    (i : Fin (n + 1)) (g : P.BigGroup) : Q.ghostStopPrimes S i g ⊆ Q.pendingBeforePrimes S i g := by
  intro p hp
  have hb := (Finset.mem_filter.mp hp).2
  have hs := hS g p
  rcases he : S g p with _ | ⟨birth, stop⟩
  · simp only [he, ghostStopAt] at hb
  · rw [he] at hs hb
    change stop = i ∧ i ∉ Q.activeVisits g p at hb
    obtain ⟨rfl, hnot⟩ := hb
    have hne : birth ≠ stop := by
      intro heq
      exact hnot (heq ▸ Q.coincident_span_active g p birth stop hs heq)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [he]
    exact ⟨lt_of_le_of_ne hs.1 hne, le_refl _, hnot⟩

theorem ghostBirthPrimes_card_le (S : LifespanAssignment P n) (hS : Q.lifespanValid S)
    (i : Fin (n + 1)) (g : P.BigGroup) : (Q.ghostBirthPrimes S i g).card ≤ (Q.memoryAfter S i g).card := by
  rw [memoryAfter_card]
  exact Finset.card_le_card (Q.ghostBirthPrimes_subset S hS i g)


end ResiduePath


end Erdos821.S2Core
