module

public import Erdos408.Hypotheses

/-!
# Reindexing the groups

`GraphTransference` takes its groups indexed by any `Fintype ι`; upstream
indexes them by `Fin count`. Along an equivalence `e : ι ≃ κ`, the physical
norm (`physicalNormSq_reindex`) and the pattern pairing
(`patternPairing_reindex`) are unchanged when the groups, the free slots, and
the kernel's arguments are transported.
-/

@[expose] public section

namespace Erdos408.Graph

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Lists are physical exactly when their transports are. -/
lemma mem_physicalLists_reindex (e : ι ≃ κ) (P : ι → Finset ℕ) {M n : ℕ}
    (p : κ → Fin M → ℕ) :
    p ∈ physicalLists (fun k => P (e.symm k)) M n ↔
      (fun g => p (e g)) ∈ physicalLists P M n := by
  simp only [physicalLists, Finset.mem_filter, Fintype.mem_piFinset]
  refine and_congr ?_ ?_
  · exact (e.forall_congr_right (q := fun k => ∀ i, p k i ∈ P (e.symm k))).symm.trans
      (by simp only [Equiv.symm_apply_apply])
  · exact (e.forall_congr_right (q := fun k => Function.Injective (p k) ∧ ∀ i, p k i ∣ n)).symm

/-- Auxiliary labels are those of the original groups, transported. -/
lemma mem_auxLabels_reindex (e : ι ≃ κ) (P : ι → Finset ℕ) {J : ℕ} (C : ι → Finset (Fin J))
    (a : κ → Fin J → ℕ) :
    a ∈ auxLabels (fun k => P (e.symm k)) (fun k => C (e.symm k)) ↔
      (fun g => a (e g)) ∈ auxLabels P C := by
  simp only [auxLabels, Fintype.mem_piFinset]
  exact (e.forall_congr_right (q := fun k => ∀ i, a k i ∈
    if i ∈ C (e.symm k) then P (e.symm k) else {1})).symm.trans
      (by simp only [Equiv.symm_apply_apply])

omit [DecidableEq ι] [DecidableEq κ] in
/-- The edge product of transported lists. -/
lemma edgeProduct_reindex (e : ι ≃ κ) {J : ℕ} (C : ι → Finset (Fin J))
    (p : κ → Fin (J + 1) → ℕ) (a : κ → Fin J → ℕ) :
    edgeProduct (fun k => C (e.symm k)) p a =
      edgeProduct C (fun g => p (e g)) fun g => a (e g) := by
  unfold edgeProduct
  rw [← Equiv.prod_comp e]
  simp only [Equiv.symm_apply_apply]

omit [DecidableEq ι] [DecidableEq κ] in
/-- `ω` is unchanged by reindexing. -/
lemma groupPrimeCount_reindex (e : ι ≃ κ) (P : ι → Finset ℕ) (n : ℕ) :
    groupPrimeCount (fun k => P (e.symm k)) n = groupPrimeCount P n := by
  unfold groupPrimeCount
  exact Equiv.sum_comp e.symm fun g => primeCount (P g) n

/-- The physical norm is unchanged by reindexing. -/
lemma physicalNormSq_reindex (e : ι ≃ κ) (P : ι → Finset ℕ) (M : ℕ) (S : Finset ℕ)
    (f : ℕ → ℂ) :
    physicalNormSq (fun k => P (e.symm k)) M S f = physicalNormSq P M S f := by
  unfold physicalNormSq
  refine Finset.sum_congr rfl fun n _ => ?_
  have hcard : (physicalLists (fun k => P (e.symm k)) M n).card = (physicalLists P M n).card :=
    Finset.card_nbij' (fun p g => p (e g)) (fun p k => p (e.symm k))
      (fun p hp => (mem_physicalLists_reindex e P p).mp hp)
      (fun p hp => (mem_physicalLists_reindex e P _).mpr (by simpa using hp))
      (fun p _ => by simp) (fun p _ => by simp)
  rw [hcard, Equiv.prod_comp e.symm (fun g => (harmonicMass (P g))⁻¹ ^ M)]

/-- The pattern pairing is unchanged by reindexing. -/
lemma patternPairing_reindex (e : ι ≃ κ) (P : ι → Finset ℕ) (q₀ : ℝ) {J : ℕ}
    (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ) (ζ : ℝ)
    (S : Finset ℕ) (f g : ℕ → ℂ) :
    patternPairing (fun k => P (e.symm k)) q₀ (fun k => C (e.symm k))
        (fun p p' a => K (fun g => p (e g)) (fun g => p' (e g)) fun g => a (e g)) ζ S f g =
      patternPairing P q₀ C K ζ S f g := by
  unfold patternPairing
  refine Finset.sum_congr rfl fun n _ => ?_
  refine Finset.sum_nbij' (fun p g => p (e g)) (fun p k => p (e.symm k))
    (fun p hp => (mem_physicalLists_reindex e P p).mp hp)
    (fun p hp => (mem_physicalLists_reindex e P _).mpr (by simpa using hp))
    (fun p _ => by simp) (fun p _ => by simp) fun p hp => ?_
  refine Finset.sum_nbij' (fun a g => a (e g)) (fun a k => a (e.symm k))
    (fun a ha => (mem_auxLabels_reindex e P C a).mp ha)
    (fun a ha => (mem_auxLabels_reindex e P C _).mpr (by simpa using ha))
    (fun a _ => by simp) (fun a _ => by simp) fun a ha => ?_
  rw [edgeProduct_reindex]
  refine Finset.sum_nbij' (fun p' g => p' (e g)) (fun p' k => p' (e.symm k))
    (fun p' hp' => ?_) (fun p' hp' => ?_) (fun p' _ => by simp) (fun p' _ => by simp)
    fun p' hp' => ?_
  · rw [Finset.mem_filter] at hp' ⊢
    refine ⟨(mem_physicalLists_reindex e P p').mp hp'.1, fun h => ?_⟩
    simpa using hp'.2 (e h)
  · rw [Finset.mem_filter] at hp' ⊢
    refine ⟨(mem_physicalLists_reindex e P _).mpr (by simpa using hp'.1), fun k => ?_⟩
    simpa using hp'.2 (e.symm k)
  · rw [groupPrimeCount_reindex, groupPrimeCount_reindex, Fintype.card_congr e]
    congr 3
    rw [← Equiv.prod_comp e]
    simp only [Equiv.symm_apply_apply]

end Erdos408.Graph
