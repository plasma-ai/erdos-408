import Erdos821.S2.CycleBlocks

/-! Equality rank and the signs of cycle decompositions. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2

/-- Rank plus the number of nonsingleton blocks is the number of addresses used. -/
theorem birthRank_add_card {a : ℕ} (π : Finset (Finset (Fin a)))
    (hπ : BirthCollection π) :
    birthRank π + π.card = (π.biUnion id).card := by
  classical
  have he : (∑ B ∈ π, B.card) = birthRank π + π.card := by
    calc
      (∑ B ∈ π, B.card) = ∑ B ∈ π, (B.card - 1 + 1) := by
        apply Finset.sum_congr rfl
        intro B hB
        have := hπ.1 B hB
        omega
      _ = birthRank π + π.card := by
        simp [birthRank, Finset.sum_add_distrib]
  exact he.symm.trans (Finset.card_biUnion hπ.2).symm

theorem cycleFactors_support_injective {a : ℕ} (σ : Equiv.Perm (Fin a)) :
    Set.InjOn (fun c : Equiv.Perm (Fin a) => c.support)
      (σ.cycleFactorsFinset : Set (Equiv.Perm (Fin a))) := by
  classical
  intro c hc d hd hsd
  by_contra hcd
  have hdis := (σ.cycleFactorsFinset_pairwise_disjoint hc hd hcd).disjoint_support
  have hempty : c.support = ∅ := by
    have hdis' : Disjoint c.support c.support := by simpa only [← hsd] using hdis
    exact disjoint_self.mp hdis'
  have hcard := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.two_le_card_support
  simp [hempty] at hcard

theorem cycleBirthBlocks_card {a : ℕ} (σ : Equiv.Perm (Fin a)) :
    (cycleBirthBlocks σ).card = σ.cycleFactorsFinset.card := by
  classical
  exact Finset.card_image_of_injOn (cycleFactors_support_injective σ)

theorem cycleBirthBlocks_rank_add_card {a : ℕ} (σ : Equiv.Perm (Fin a)) :
    birthRank (cycleBirthBlocks σ) + σ.cycleFactorsFinset.card = σ.support.card := by
  simpa only [cycleBirthBlocks_card, cycleBirthBlocks_union] using
    birthRank_add_card (cycleBirthBlocks σ) (cycleBirthBlocks_collection σ)

/-- The sign of a permutation is (-1) to its equality rank. -/
theorem cycleBirthBlocks_sign {a : ℕ} (σ : Equiv.Perm (Fin a)) :
    (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ birthRank (cycleBirthBlocks σ) := by
  classical
  have hs : (Equiv.Perm.sign σ : ℤ) =
      (-1 : ℤ) ^ (σ.support.card + σ.cycleFactorsFinset.card) := by
    have hp := congrArg (fun u : ℤˣ => (u : ℤ)) (Equiv.Perm.sign_of_cycleType σ)
    rw [Equiv.Perm.sum_cycleType] at hp
    simpa [Equiv.Perm.cycleType] using hp
  have he : σ.support.card + σ.cycleFactorsFinset.card =
      birthRank (cycleBirthBlocks σ) + 2 * σ.cycleFactorsFinset.card := by
    have := cycleBirthBlocks_rank_add_card σ
    omega
  rw [hs, he, pow_add, pow_mul]
  simp


end Erdos821.S2
