import Erdos821.S2.HistorySizes
import Erdos821.S2.BlueprintBirths

/-! Global distinctness is exactly injectivity on the performed addresses. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem sum_fin_dite {M : Type*} [AddCommMonoid M] (b B : ℕ) (hb : b ≤ B) (f : Fin b → M) :
    (∑ h : Fin B, if hh : h.val < b then f ⟨h.val, hh⟩ else 0) = ∑ h : Fin b, f h := by
  induction B, hb using Nat.le_induction with
  | base =>
      apply Finset.sum_congr rfl
      intro h _
      simp
  | succ B hb ih =>
      rw [Fin.sum_univ_castSucc]
      simpa only [Fin.val_castSucc, Fin.val_last, dif_neg (Nat.not_lt.mpr hb), add_zero] using ih

theorem sum_singletons_eq_map {α β : Type*} (s : Finset α) (f : α → β) :
    (∑ a ∈ s, ({f a} : Multiset β)) = s.val.map f := by
  simpa only [Finset.sum_eq_multiset_sum, Multiset.map_map, Function.comp_def] using Multiset.sum_map_singleton (s.val.map f)

namespace MemoryHistory

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)

theorem birthValues_eq_addresses (B : ℕ) (hH : H.Truncated B) :
    H.birthValues = ∑ a : BirthAddress P (J + F.ell) n B,
      if H.addressPerformed B a then ({H.addressValue B a} : Multiset ℕ) else 0 := by
  simp only [BirthAddress, Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hin (g : P.BigGroup) (h : Fin (J + F.ell)) :
      (if H.addressPerformed B (.inl (g, h)) then
        ({H.addressValue B (.inl (g, h))} : Multiset ℕ) else 0) =
      {((H.before 0).2.1 g.val h).val} := by
    rw [ite_eq_left (show H.addressPerformed B (.inl (g, h)) from True.intro)]
    rfl
  have hf (i : Fin n) (g : P.BigGroup) (h : Fin (J + F.ell)) :
      (if H.addressPerformed B (.inr (.inl (i, g, h))) then
        ({H.addressValue B (.inr (.inl (i, g, h)))} : Multiset ℕ) else 0) =
      if h ∈ H.freshTargetSlots i g then
        {((permuteActive (H.edge i).2.1 (H.before i.succ)).2.1 g.val h).val} else 0 := by
    by_cases hh : h ∈ H.freshTargetSlots i g
    · rw [ite_eq_left (show H.addressPerformed B (.inr (.inl (i, g, h))) from hh), ite_eq_left hh]
      rfl
    · rw [ite_eq_right (show ¬ H.addressPerformed B (.inr (.inl (i, g, h))) from hh), ite_eq_right hh]
  have hg (i : Fin (n + 1)) (g : P.BigGroup) (h : Fin B) :
      (if H.addressPerformed B (.inr (.inr (i, g, h))) then
        ({H.addressValue B (.inr (.inr (i, g, h)))} : Multiset ℕ) else 0) =
      if hh : h.val < ((H.ghost i).2.1 g).val then
        {((H.ghost i).2.2 g ⟨h.val, hh⟩).val} else 0 := by
    by_cases hh : h.val < ((H.ghost i).2.1 g).val
    · rw [ite_eq_left (show H.addressPerformed B (.inr (.inr (i, g, h))) from hh), dite_eq_left hh]
      simp only [addressValue, dite_eq_left hh]
    · rw [ite_eq_right (show ¬ H.addressPerformed B (.inr (.inr (i, g, h))) from hh), dite_eq_right hh]
  have hb (i : Fin (n + 1)) (g : P.BigGroup) :
      (∑ h : Fin B, if hh : h.val < ((H.ghost i).2.1 g).val then
        ({((H.ghost i).2.2 g ⟨h.val, hh⟩).val} : Multiset ℕ) else 0) =
      ∑ h : Fin ((H.ghost i).2.1 g).val, ({((H.ghost i).2.2 g h).val} : Multiset ℕ) :=
    sum_fin_dite ((H.ghost i).2.1 g).val B (H.ghostBatch_le B hH i g)
      (fun h => ({((H.ghost i).2.2 g h).val} : Multiset ℕ))
  simp_rw [hin, hf, hg]
  simp_rw [hb, Finset.sum_ite_mem_eq]
  simp only [birthValues, initialBirthValues, ghostBirthValues, freshBirthValues]
  ac_rfl

theorem birthValues_eq_map (B : ℕ) (hH : H.Truncated B) :
    H.birthValues = (Finset.univ.filter (H.addressPerformed B)).val.map (H.addressValue B) := by
  rw [H.birthValues_eq_addresses B hH, ← Finset.sum_filter, sum_singletons_eq_map]

theorem distinctBirths_iff_addresses (B : ℕ) (hH : H.Truncated B) :
    H.DistinctBirths ↔ Set.InjOn (H.addressValue B)
      (Finset.univ.filter (H.addressPerformed B)) := by
  rw [DistinctBirths, H.birthValues_eq_map B hH]
  exact Multiset.nodup_map_iff_inj_on (Finset.univ.filter (H.addressPerformed B)).nodup

def performedFin (B : ℕ) : Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B))) :=
  Finset.univ.filter (fun i => H.addressPerformed B ((Fintype.equivFin _).symm i))

def valueFin (B : ℕ) : Fin (Fintype.card (BirthAddress P (J + F.ell) n B)) → ℕ :=
  fun i => H.addressValue B ((Fintype.equivFin _).symm i)

theorem distinctBirths_iff_fin (B : ℕ) (hH : H.Truncated B) :
    H.DistinctBirths ↔ Set.InjOn (H.valueFin B) (H.performedFin B) := by
  rw [H.distinctBirths_iff_addresses B hH]
  constructor
  · intro hd x hx y hy he
    apply (Fintype.equivFin (BirthAddress P (J + F.ell) n B)).symm.injective
    apply hd
    · simpa [performedFin] using hx
    · simpa [performedFin] using hy
    · exact he
  · intro hd x hx y hy he
    apply (Fintype.equivFin (BirthAddress P (J + F.ell) n B)).injective
    apply hd
    · simpa [performedFin] using hx
    · simpa [performedFin] using hy
    · simpa [valueFin] using he

/-- The generic equality-rank formula applies to the actual global birth rule. -/
theorem distinct_birth_expansion_history (B : ℕ) (hH : H.Truncated B) :
    (if H.DistinctBirths then (1 : ℤ) else 0) =
      ∑ π ∈ Finset.univ.powerset.powerset.filter BirthCollection,
        if birthEvent (H.performedFin B) (H.valueFin B) π then birthMobius π else 0 := by
  have he := distinct_birth_expansion_proof _ (H.performedFin B) (H.valueFin B)
  by_cases hd : H.DistinctBirths
  · have hf := (H.distinctBirths_iff_fin B hH).mp hd
    simpa only [ite_eq_left hd, ite_eq_left hf] using he
  · have hf : ¬ Set.InjOn (H.valueFin B) (H.performedFin B) :=
      fun hf => hd ((H.distinctBirths_iff_fin B hH).mpr hf)
    simpa only [ite_eq_right hd, ite_eq_right hf] using he

end MemoryHistory


end Erdos821.S2Core
