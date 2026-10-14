import Erdos821.S2.Definitions

/-! Cycle supports as disjoint blocks of birth addresses. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2

def cycleBirthBlocks {a : ℕ} (σ : Equiv.Perm (Fin a)) : Finset (Finset (Fin a)) :=
  σ.cycleFactorsFinset.image Equiv.Perm.support

theorem cycleBirthBlocks_collection {a : ℕ} (σ : Equiv.Perm (Fin a)) :
    BirthCollection (cycleBirthBlocks σ) := by
  classical
  constructor
  · intro B hB
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hB
    exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.two_le_card_support
  · intro B hB C hC hBC
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hC
    have hcd : c ≠ d := fun h => hBC (congrArg Equiv.Perm.support h)
    exact (σ.cycleFactorsFinset_pairwise_disjoint hc hd hcd).disjoint_support

theorem cycleBirthBlocks_union {a : ℕ} (σ : Equiv.Perm (Fin a)) :
    (cycleBirthBlocks σ).biUnion id = σ.support := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨B, hB, hi⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hB
    exact (Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset).mpr ⟨c, hc, hi⟩
  · intro hi
    obtain ⟨c, hc, hi⟩ := (Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset).mp hi
    exact Finset.mem_biUnion.mpr ⟨c.support, Finset.mem_image.mpr ⟨c, hc, rfl⟩, hi⟩

/-- A block event records exactly the supported, value-preserving cycles. -/
theorem cycleBirthBlocks_event {a : ℕ} (σ : Equiv.Perm (Fin a))
    (performed : Finset (Fin a)) (value : Fin a → ℕ) :
    birthEvent performed value (cycleBirthBlocks σ) ↔
      σ.support ⊆ performed ∧ ∀ i, value (σ i) = value i := by
  classical
  constructor
  · intro h
    constructor
    · intro i hi
      obtain ⟨c, hc, hi⟩ :=
        Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hi
      exact (h c.support (Finset.mem_image.mpr ⟨c, hc, rfl⟩)).1 hi
    · intro i
      by_cases hi : σ i = i
      · rw [hi]
      · obtain ⟨c, hc, hic⟩ :=
          Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp
            (Equiv.Perm.mem_support.mpr hi)
        have hci := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2 i hic
        rw [← hci]
        exact (h c.support (Finset.mem_image.mpr ⟨c, hc, rfl⟩)).2
          (c i) (Equiv.Perm.apply_mem_support.mpr hic) i hic
  · rintro ⟨hs, hv⟩ B hB
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hB
    constructor
    · exact (Equiv.Perm.mem_cycleFactorsFinset_support_le hc).trans hs
    · intro i hi j hj
      have hcv : ∀ x, value (c x) = value x := by
        intro x
        by_cases hx : x ∈ c.support
        · rw [(Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2 x hx]
          exact hv x
        · rw [Equiv.Perm.notMem_support.mp hx]
      have hp : ∀ n : ℕ, ∀ x, value ((c ^ n) x) = value x := by
        intro n
        induction n with
        | zero => intro x; rfl
        | succ n ih =>
          intro x
          rw [pow_succ, Equiv.Perm.mul_apply, ih, hcv]
      obtain ⟨n, hn⟩ :=
        ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.sameCycle
          (Equiv.Perm.mem_support.mp hi) (Equiv.Perm.mem_support.mp hj)).exists_nat_pow_eq
      rw [← hn]
      exact (hp n i).symm

/-- Every equality of rank r involves at most 2r addresses. -/
theorem birth_support_le {a : ℕ} (π : Finset (Finset (Fin a))) (hπ : BirthCollection π) :
    (π.biUnion id).card ≤ 2 * birthRank π := by
  classical
  calc
    (π.biUnion id).card ≤ ∑ B ∈ π, B.card := Finset.card_biUnion_le
    _ ≤ ∑ B ∈ π, 2 * (B.card - 1) := by
      apply Finset.sum_le_sum
      intro B hB
      have hB' := hπ.1 B hB
      omega
    _ = 2 * birthRank π := by
      unfold birthRank
      exact (Finset.mul_sum π (fun B => B.card - 1) 2).symm


end Erdos821.S2
