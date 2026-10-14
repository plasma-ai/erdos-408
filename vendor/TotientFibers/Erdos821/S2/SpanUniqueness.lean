import Erdos821.S2.SpanLifecycle

/-! Prime lifespans are determined by their active and pending occupancies. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

namespace ResiduePath

variable {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n)

def spanLiveAt (g : P.BigGroup) (p : P.Prime g.val) (span : PrimeSpan n)
    (i : Fin (n + 1)) : Prop :=
  i ∈ Q.activeVisits g p ∨ Q.pendingBefore g p span i ∨ Q.pendingAfter g p span i

theorem spanLiveAt_none (g : P.BigGroup) (p : P.Prime g.val)
    (hs : Q.spanValid g p none) (i : Fin (n + 1)) :
    ¬ Q.spanLiveAt g p none i := by
  simp only [spanLiveAt, pendingBefore, pendingAfter, or_false]
  change Q.activeVisits g p = ∅ at hs
  rw [hs]
  simp

theorem spanLiveAt_some (g : P.BigGroup) (p : P.Prime g.val) (b e : Fin (n + 1))
    (hs : Q.spanValid g p (some (b, e))) (i : Fin (n + 1)) :
    Q.spanLiveAt g p (some (b, e)) i ↔ b ≤ i ∧ i ≤ e := by
  constructor
  · rintro (ha | hp | hp)
    · exact hs.2.2.1 i ha
    · exact ⟨le_of_lt hp.1, hp.2.1⟩
    · exact ⟨hp.1, le_of_lt hp.2.1⟩
  · intro hi
    by_cases ha : i ∈ Q.activeVisits g p
    · exact Or.inl ha
    · by_cases hb : b < i
      · exact Or.inr (Or.inl ⟨hb, hi.2, ha⟩)
      · have hib : i = b := le_antisymm (le_of_not_gt hb) hi.1
        have hbe : b ≠ e := by
          intro he
          apply ha
          simpa only [hib] using Q.coincident_span_active g p b e hs he
        have he : i < e := by
          subst i
          exact lt_of_le_of_ne hs.1 hbe
        exact Or.inr (Or.inr ⟨hi.1, he, ha⟩)

theorem span_eq_of_live_iff (g : P.BigGroup) (p : P.Prime g.val)
    (s t : PrimeSpan n) (hs : Q.spanValid g p s) (ht : Q.spanValid g p t)
    (he : ∀ i, Q.spanLiveAt g p s i ↔ Q.spanLiveAt g p t i) : s = t := by
  cases s with
  | none =>
    cases t with
    | none => rfl
    | some be =>
      rcases be with ⟨b, e⟩
      have hl := (Q.spanLiveAt_some g p b e ht b).mpr ⟨le_rfl, ht.1⟩
      exact False.elim (Q.spanLiveAt_none g p hs b ((he b).mpr hl))
  | some be =>
    rcases be with ⟨b, e⟩
    cases t with
    | none =>
      have hl := (Q.spanLiveAt_some g p b e hs b).mpr ⟨le_rfl, hs.1⟩
      exact False.elim (Q.spanLiveAt_none g p ht b ((he b).mp hl))
    | some bf =>
      rcases bf with ⟨c, d⟩
      have hb := (Q.spanLiveAt_some g p c d ht b).mp
        ((he b).mp ((Q.spanLiveAt_some g p b e hs b).mpr ⟨le_rfl, hs.1⟩))
      have hc := (Q.spanLiveAt_some g p b e hs c).mp
        ((he c).mpr ((Q.spanLiveAt_some g p c d ht c).mpr ⟨le_rfl, ht.1⟩))
      have he' := (Q.spanLiveAt_some g p c d ht e).mp
        ((he e).mp ((Q.spanLiveAt_some g p b e hs e).mpr ⟨hs.1, le_rfl⟩))
      have hd := (Q.spanLiveAt_some g p b e hs d).mp
        ((he d).mpr ((Q.spanLiveAt_some g p c d ht d).mpr ⟨ht.1, le_rfl⟩))
      have hbc : b = c := le_antisymm hc.1 hb.1
      have hed : e = d := le_antisymm he'.2 hd.2
      simp [hbc, hed]

theorem lifespan_eq_of_memories (S T : LifespanAssignment P n)
    (hS : Q.lifespanValid S) (hT : Q.lifespanValid T)
    (hb : ∀ i g, Q.memoryBefore S i g = Q.memoryBefore T i g)
    (ha : ∀ i g, Q.memoryAfter S i g = Q.memoryAfter T i g) : S = T := by
  funext g p
  apply Q.span_eq_of_live_iff g p (S g p) (T g p) (hS g p) (hT g p)
  intro i
  have hbefore : Q.pendingBefore g p (S g p) i ↔ Q.pendingBefore g p (T g p) i := by
    have he := congrArg (pendingPrimes (P := P)) (hb i g)
    rw [Q.pendingPrimes_memoryBefore, Q.pendingPrimes_memoryBefore] at he
    have hm := congrArg (fun s : Multiset (P.Prime g.val) => p ∈ s) he
    simpa only [pendingBeforePrimes, Finset.mem_val, Finset.mem_filter,
      Finset.mem_univ, true_and] using Iff.of_eq hm
  have hafter : Q.pendingAfter g p (S g p) i ↔ Q.pendingAfter g p (T g p) i := by
    have he := congrArg (pendingPrimes (P := P)) (ha i g)
    rw [Q.pendingPrimes_memoryAfter, Q.pendingPrimes_memoryAfter] at he
    have hm := congrArg (fun s : Multiset (P.Prime g.val) => p ∈ s) he
    simpa only [pendingAfterPrimes, Finset.mem_val, Finset.mem_filter,
      Finset.mem_univ, true_and] using Iff.of_eq hm
  exact or_congr Iff.rfl (or_congr hbefore hafter)


end ResiduePath
end Erdos821.S2Core
