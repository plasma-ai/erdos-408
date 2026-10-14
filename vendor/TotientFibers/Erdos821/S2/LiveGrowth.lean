import Erdos821.S2.LiveValues
import Erdos821.P3Live.Conservation

/-! A chronological multiset bound: stores and promotions do not create births. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem sum_fin_through {R : Type*} [AddCommMonoid R] (n : ℕ) (f : Fin n → R) (i : Fin n) :
    (∑ j : Fin n, if j.val ≤ i.val then f j else 0) =
      (∑ j : Fin n, if j.val < i.val then f j else 0) + f i := by
  calc
    _ = ∑ j : Fin n, ((if j.val < i.val then f j else 0) + (if j = i then f i else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases he : j = i
      · subst j; simp
      · have hv : j.val ≠ i.val := fun hv => he (Fin.ext hv)
        by_cases hl : j.val < i.val
        · simp [he, hl, Nat.le_of_lt hl]
        · have hn : ¬ j.val ≤ i.val := by omega
          simp [he, hl, hn]
    _ = _ := by simp [Finset.sum_add_distrib]

theorem finite_multiset_growth (n : ℕ) (initial : Multiset ℕ)
    (before after ghost : Fin (n + 1) → Multiset ℕ) (fresh : Fin n → Multiset ℕ)
    (hzero : before 0 = initial)
    (hghost : ∀ i, after i ≤ before i + ghost i)
    (hedge : ∀ i : Fin n, before i.succ ≤ after i.castSucc + fresh i) :
    ∀ i, before i ≤ initial + (∑ j, if j.val < i.val then ghost j else 0) +
        (∑ e : Fin n, if e.val < i.val then fresh e else 0) ∧
      after i ≤ initial + (∑ j, if j.val ≤ i.val then ghost j else 0) +
        (∑ e : Fin n, if e.val < i.val then fresh e else 0) := by
  have hG (i : Fin n) : (∑ j : Fin (n + 1), if j.val < i.succ.val then ghost j else 0) =
      ∑ j : Fin (n + 1), if j.val ≤ i.castSucc.val then ghost j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.lt_succ_iff]
  have hE (i : Fin n) : (∑ e : Fin n, if e.val < i.succ.val then fresh e else 0) =
      (∑ e : Fin n, if e.val < i.castSucc.val then fresh e else 0) + fresh i := by
    simpa only [Fin.val_succ, Fin.val_castSucc, Nat.lt_succ_iff] using sum_fin_through n fresh i
  intro i
  induction i using Fin.induction with
  | zero =>
      constructor
      · simp [hzero]
      · rw [sum_fin_through]
        simpa [hzero] using hghost 0
  | succ i ih =>
      have hb : before i.succ ≤ initial + (∑ j : Fin (n + 1), if j.val < i.succ.val then ghost j else 0) +
          (∑ e : Fin n, if e.val < i.succ.val then fresh e else 0) := by
        calc
          _ ≤ after i.castSucc + fresh i := hedge i
          _ ≤ (initial + (∑ j : Fin (n + 1), if j.val ≤ i.castSucc.val then ghost j else 0) +
              (∑ e : Fin n, if e.val < i.castSucc.val then fresh e else 0)) + fresh i :=
            add_le_add ih.2 (le_refl _)
          _ = _ := by rw [hG, hE]; ac_rfl
      constructor
      · exact hb
      · calc
          _ ≤ before i.succ + ghost i.succ := hghost i.succ
          _ ≤ (initial + (∑ j : Fin (n + 1), if j.val < i.succ.val then ghost j else 0) +
              (∑ e : Fin n, if e.val < i.succ.val then fresh e else 0)) + ghost i.succ :=
            add_le_add hb (le_refl _)
          _ = _ := by rw [sum_fin_through]; ac_rfl

theorem groupLivePrimes_nodup {M : ℕ} (s : P.MemoryState M) (hs : (liveValues s).Nodup)
    (g : P.BigGroup) : (groupLivePrimes s g).Nodup := by
  have hg : (groupLivePrimes s g).map Subtype.val ≤ liveValues s := by
    unfold liveValues
    exact Finset.single_le_sum (f := fun h => (groupLivePrimes s h).map Subtype.val)
      (fun _ _ => zero_le) (Finset.mem_univ g)
  exact Multiset.Nodup.of_map Subtype.val (Multiset.nodup_of_le hg hs)

theorem big_live_structure {M : ℕ} (s : P.MemoryState M) (hs : (liveValues s).Nodup) (g : P.BigGroup) :
    Function.Injective (s.2.1 g.val) ∧ (pendingPrimes (s.2.2 g)).Nodup ∧
      Disjoint (activePrimes s.2.1 g.val) (pendingPrimes (s.2.2 g)) := by
  have hg := Multiset.nodup_add.mp (groupLivePrimes_nodup s hs g)
  refine ⟨?_, hg.2⟩
  have ha : ((Finset.univ : Finset (Fin M)).val.map (s.2.1 g.val)).Nodup := by
    rw [← sum_singletons_eq_map]
    exact hg.1
  intro i j he
  exact Multiset.inj_on_of_nodup_map ha i (Finset.mem_univ i) j (Finset.mem_univ j) he

namespace MemoryHistory

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)

theorem initial_liveValues (hH : H.Valid) : liveValues (H.before 0) = H.initialBirthValues := by
  simp only [liveValues, groupLivePrimes, hH.1, pendingPrimes, Multiset.map_zero, add_zero,
    activePrimes, multiset_map_sum, Multiset.map_singleton, initialBirthValues]

theorem liveValues_le_births (hTask : EdgeLiveConservationTask) (hH : H.Valid) (i : Fin (n + 1)) :
    liveValues (H.before i) ≤ H.birthValues ∧ liveValues (H.after i) ≤ H.birthValues := by
  have he := finite_multiset_growth n H.initialBirthValues
    (fun i => liveValues (H.before i)) (fun i => liveValues (H.after i))
    H.ghostBirthValues H.freshBirthValues (H.initial_liveValues hH)
    (H.ghost_liveValues_le hH) (H.edge_liveValues_le hTask hH) i
  have hg₁ : (∑ j : Fin (n + 1), if j.val < i.val then H.ghostBirthValues j else 0) ≤
      ∑ j, H.ghostBirthValues j := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs <;> simp
  have hg₂ : (∑ j : Fin (n + 1), if j.val ≤ i.val then H.ghostBirthValues j else 0) ≤
      ∑ j, H.ghostBirthValues j := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs <;> simp
  have hf : (∑ e : Fin n, if e.val < i.val then H.freshBirthValues e else 0) ≤
      ∑ e, H.freshBirthValues e := by
    apply Finset.sum_le_sum
    intro e _
    split_ifs <;> simp
  exact ⟨he.1.trans (add_le_add (add_le_add (le_refl _) hg₁) hf),
    he.2.trans (add_le_add (add_le_add (le_refl _) hg₂) hf)⟩

theorem liveValues_nodup (hTask : EdgeLiveConservationTask) (hH : H.Valid) (hd : H.DistinctBirths)
    (i : Fin (n + 1)) : (liveValues (H.before i)).Nodup ∧ (liveValues (H.after i)).Nodup :=
  ⟨Multiset.nodup_of_le (H.liveValues_le_births hTask hH i).1 hd,
    Multiset.nodup_of_le (H.liveValues_le_births hTask hH i).2 hd⟩

theorem big_active_injective (hTask : EdgeLiveConservationTask) (hH : H.Valid) (hd : H.DistinctBirths)
    (i : Fin (n + 1)) (g : P.BigGroup) :
    Function.Injective ((H.before i).2.1 g.val) ∧ Function.Injective ((H.after i).2.1 g.val) :=
  ⟨(big_live_structure (H.before i) (H.liveValues_nodup hTask hH hd i).1 g).1,
    (big_live_structure (H.after i) (H.liveValues_nodup hTask hH hd i).2 g).1⟩

theorem liveValues_nodup_of_distinct (hH : H.Valid) (hd : H.DistinctBirths) (i : Fin (n + 1)) :
    (liveValues (H.before i)).Nodup ∧ (liveValues (H.after i)).Nodup :=
  H.liveValues_nodup EdgeLiveConservationTask_proof hH hd i

theorem big_active_injective_of_distinct (hH : H.Valid) (hd : H.DistinctBirths)
    (i : Fin (n + 1)) (g : P.BigGroup) :
    Function.Injective ((H.before i).2.1 g.val) ∧ Function.Injective ((H.after i).2.1 g.val) :=
  H.big_active_injective EdgeLiveConservationTask_proof hH hd i g

end MemoryHistory


end Erdos821.S2Core
