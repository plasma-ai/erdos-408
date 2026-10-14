import Erdos821.Prelim.SieveCountingLower

/-!
# Uniform counting bounds for the block sieve

The block avoidance product is the sieve product. The upper and lower
counting bounds, together with the correction expectation estimate, give
`eq:block-sieve`, uniformly in the number of blocks and in even `h`.
The fixed choice `h = 2` gives the paper's upper bound at level `z^10`.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
namespace Erdos821.PrelimLemmas

theorem blocks_eq_primes (α : Type) (S : Blueprint.SieveData α)
    (z η C : ℝ) (hdb : S.densityBounds z η C)
    (N : ℕ) (hN : Zscale z N < 2) :
    (Finset.range N).biUnion (Block α S z) = S.primes := by
  apply Finset.Subset.antisymm
  · exact biUnion_subset_primes α S z N
  · intro p hp
    obtain ⟨j, hj, hpj⟩ := Block_cover α S z hdb.1 N hN p hp
      (hdb.2.2.1 p hp).1
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hpj⟩

theorem block_product_eq (α : Type) (S : Blueprint.SieveData α)
    (z η C : ℝ) (hdb : S.densityBounds z η C)
    (N : ℕ) (hN : Zscale z N < 2) :
    (∏ j ∈ Finset.range N, blockExpA (Block α S z j) S.density) =
      S.product := by
  unfold blockExpA Blueprint.SieveData.product
  rw [← Finset.prod_biUnion
    (fun j₁ _ j₂ _ hne => Block_disjoint α S z hdb.1 hne),
    blocks_eq_primes α S z η C hdb N hN]

theorem block_product_le_upper (N h : ℕ) (B : ℕ → Finset ℕ)
    (g : ℕ → ℝ) (he : Even h)
    (hg : ∀ j ∈ Finset.range N, ∀ p ∈ B j, 0 ≤ g p ∧ g p ≤ 1) :
    (∏ j ∈ Finset.range N, blockExpA (B j) g) ≤
      ∏ j ∈ Finset.range N, blockExpS (B j) g ((j + 1) * h) := by
  apply Finset.prod_le_prod₀
  · intro j hj
    exact Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hg j hj p hp).2)
  · intro j hj
    have hb := blockExp_bounds (B j) g ((j + 1) * h) (he.mul_left _)
      (fun p hp => (hg j hj p hp).1) (fun p hp => (hg j hj p hp).2)
    linarith [hb.1]

/-- The two-sided estimate of `eq:block-sieve`, with remainder constant one. -/
theorem exists_sifted_error_bound (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∃ h₀ : ℕ,
      ∀ (α : Type) (S : Blueprint.SieveData α) (z : ℝ),
        S.densityBounds z η C → ∀ h : ℕ, h₀ ≤ h → Even h →
          |S.sifted - S.X * S.product| ≤
            K * Real.exp (-(h : ℝ)) * S.X * S.product +
              S.remainderSum (z ^ (4 * h + 2)) := by
  obtain ⟨h₀, K, hK, hbound⟩ := exists_corr_error_bound η C hη hC
  refine ⟨K, hK, h₀, ?_⟩
  intro α S z hdb h hh he
  obtain ⟨N, hN⟩ := exists_Zscale_lt_two hdb.1
  have hg : ∀ j ∈ Finset.range N, ∀ p ∈ Block α S z j,
      0 ≤ S.density p ∧ S.density p ≤ 1 - η := by
    intro j _ p hp
    exact (hdb.2.2.1 p (Block_subset α S z j hp)).2
  have hg' : ∀ j ∈ Finset.range N, ∀ p ∈ Block α S z j,
      0 ≤ S.density p ∧ S.density p ≤ 1 := by
    intro j hj p hp
    obtain ⟨hp0, hp1⟩ := hg j hj p hp
    exact ⟨hp0, by linarith⟩
  have hmass : ∀ j ∈ Finset.range N,
      ∑ p ∈ Block α S z j, S.density p ≤ C :=
    fun j _ => Block_mass_le α S z η C hdb j
  have hproduct := block_product_eq α S z η C hdb N hN
  have hcorr := hbound h N hh he (Block α S z) S.density hg hmass
  rw [hproduct] at hcorr
  have hprod := block_product_le_upper N h (Block α S z) S.density he hg'
  rw [hproduct] at hprod
  have hsub := prod_sub_le_corr N (Block α S z) S.density h he hg'
  rw [hproduct] at hsub
  have hupper := sifted_le_main_add_remainder α S z hdb.1 N hN η C hdb h he
  have hlower := sifted_ge_main_sub_remainder α S z hdb.1 N hN η C hdb h he
  rw [weighted_V_eq_corrExp N h (Block α S z) S.density
    (fun j₁ _ j₂ _ hne => Block_disjoint α S z hdb.1 hne) he] at hlower
  have hprodX := mul_le_mul_of_nonneg_left hprod S.X_nonneg
  have hsubX := mul_le_mul_of_nonneg_left hsub S.X_nonneg
  have hcorrX := mul_le_mul_of_nonneg_left hcorr S.X_nonneg
  apply abs_le.mpr
  constructor <;> nlinarith only [hupper, hlower, hprodX, hsubX, hcorrX]

/-- The fixed `h = 2` upper bound in `lem:sieve`, at level `z^10`. -/
theorem exists_sifted_upper_fixed (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : Type) (S : Blueprint.SieveData α) (z : ℝ),
      S.densityBounds z η C →
        S.sifted ≤ K * S.X * S.product + S.remainderSum (z ^ (10 : ℕ)) := by
  obtain ⟨K, hK, hbound⟩ := exists_prod_upper_fixed η C hη hC 2
    (by norm_num) (by decide)
  refine ⟨K, hK, ?_⟩
  intro α S z hdb
  obtain ⟨N, hN⟩ := exists_Zscale_lt_two hdb.1
  have hg : ∀ j ∈ Finset.range N, ∀ p ∈ Block α S z j,
      0 ≤ S.density p ∧ S.density p ≤ 1 - η := by
    intro j _ p hp
    exact (hdb.2.2.1 p (Block_subset α S z j hp)).2
  have hmass : ∀ j ∈ Finset.range N,
      ∑ p ∈ Block α S z j, S.density p ≤ C :=
    fun j _ => Block_mass_le α S z η C hdb j
  have hp := hbound N (Block α S z) S.density hg hmass
  rw [block_product_eq α S z η C hdb N hN] at hp
  have hupper := sifted_le_main_add_remainder α S z hdb.1 N hN η C hdb 2
    (by decide)
  norm_num only at hupper
  have hpX := mul_le_mul_of_nonneg_left hp S.X_nonneg
  nlinarith only [hupper, hpX]

end Erdos821.PrelimLemmas
