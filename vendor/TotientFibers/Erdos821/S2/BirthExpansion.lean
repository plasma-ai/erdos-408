import Erdos821.S2.CycleFibers
import Erdos821.S2.PerformedSigns

/-! The exact distinct-birth inclusion-exclusion expansion by equality rank. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2

lemma birthMobius_eq_sign_mul_factorials {a : ℕ} (π : Finset (Finset (Fin a))) :
    birthMobius π = (-1 : ℤ) ^ birthRank π *
      ∏ B ∈ π, ((B.card - 1).factorial : ℤ) := by
  simp only [birthMobius, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, birthRank]

lemma permutationsWithBlocks_sign_sum {a : ℕ} (π : Finset (Finset (Fin a)))
    (hπ : BirthCollection π) :
    (∑ σ ∈ permutationsWithBlocks π, (Equiv.Perm.sign σ : ℤ)) = birthMobius π := by
  have hs (σ : Equiv.Perm (Fin a)) (hσ : σ ∈ permutationsWithBlocks π) :
      (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ birthRank π := by
    rw [cycleBirthBlocks_sign, (Finset.mem_filter.mp hσ).2]
  calc
    _ = ∑ σ ∈ permutationsWithBlocks π, (-1 : ℤ) ^ birthRank π :=
      Finset.sum_congr rfl hs
    _ = (permutationsWithBlocks π).card * (-1 : ℤ) ^ birthRank π := by simp
    _ = birthMobius π := by
      rw [permutationsWithBlocks_card π hπ, birthMobius_eq_sign_mul_factorials]
      simp only [Nat.cast_prod]
      exact mul_comm _ _

/-- Distinctness is an exact sum over disjoint nonsingleton blocks.
Unperformed addresses contribute no block conditions. -/
theorem distinct_birth_expansion (a : ℕ) (performed : Finset (Fin a)) (value : Fin a → ℕ) :
    (if Set.InjOn value performed then (1 : ℤ) else 0) =
      ∑ π ∈ Finset.univ.powerset.powerset.filter BirthCollection,
        if birthEvent performed value π then birthMobius π else 0 := by
  let C : Finset (Finset (Finset (Fin a))) :=
    Finset.univ.powerset.powerset.filter BirthCollection
  let term (σ : Equiv.Perm (Fin a)) : ℤ :=
    if σ.support ⊆ performed ∧ ∀ i, value (σ i) = value i
      then (Equiv.Perm.sign σ : ℤ) else 0
  have hmap : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin a))), cycleBirthBlocks σ ∈ C := by
    intro σ _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, cycleBirthBlocks_collection σ⟩
    intro B _
    exact Finset.mem_powerset.mpr (Finset.subset_univ _)
  have hterm (π : Finset (Finset (Fin a))) (σ : Equiv.Perm (Fin a))
      (hσ : σ ∈ permutationsWithBlocks π) :
      term σ = if birthEvent performed value π then (Equiv.Perm.sign σ : ℤ) else 0 := by
    have he := cycleBirthBlocks_event σ performed value
    rw [(Finset.mem_filter.mp hσ).2] at he
    simp only [term, ← he]
  have hfiber (π : Finset (Finset (Fin a))) (hπ : π ∈ C) :
      (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin a) => cycleBirthBlocks σ = π), term σ) =
        if birthEvent performed value π then birthMobius π else 0 := by
    change (∑ σ ∈ permutationsWithBlocks π, term σ) = _
    have hp : BirthCollection π := (Finset.mem_filter.mp hπ).2
    calc
      _ = ∑ σ ∈ permutationsWithBlocks π,
          if birthEvent performed value π then (Equiv.Perm.sign σ : ℤ) else 0 :=
        Finset.sum_congr rfl (hterm π)
      _ = _ := by
        by_cases he : birthEvent performed value π
        · simp only [if_pos he]
          exact permutationsWithBlocks_sign_sum π hp
        · simp only [if_neg he, Finset.sum_const_zero]
  calc
    _ = ∑ σ : Equiv.Perm (Fin a), term σ := by
      refine (performed_value_preserving_sign_sum performed value).trans ?_
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : σ.support ⊆ performed ∧ ∀ i, value (σ i) = value i
      · simp only [term, if_pos h]
      · simp only [term, if_neg h]
    _ = ∑ π ∈ C,
        ∑ σ ∈ Finset.univ.filter (fun σ => cycleBirthBlocks σ = π), term σ :=
      (Finset.sum_fiberwise_of_maps_to hmap term).symm
    _ = _ := Finset.sum_congr rfl hfiber


end Erdos821.S2
