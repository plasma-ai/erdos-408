import Erdos821.Prelim.SievePolynomials

/-! The complete block-sieve field of the P2 interface. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
namespace Erdos821.PrelimLemmas

theorem sieve_product_nonneg (α : Type) (S : Blueprint.SieveData α)
    (z η C : ℝ) (hdb : S.densityBounds z η C) : 0 ≤ S.product := by
  apply Finset.prod_nonneg
  intro p hp
  have hη := hdb.2.1
  have hden := (hdb.2.2.1 p hp).2.2
  linarith

theorem sieve_remainderSum_nonneg (α : Type) (S : Blueprint.SieveData α)
    (D : ℝ) : 0 ≤ S.remainderSum D :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- `lem:sieve`, including both counting bounds and all polynomial certificates. -/
theorem blockSieve_proof : Blueprint.BlockSieve := by
  intro η C hη hC
  obtain ⟨K₁, hK₁, hupper⟩ := exists_sifted_upper_fixed η C hη hC.le
  obtain ⟨K₂, hK₂, h₀, herror⟩ := exists_sifted_error_bound η C hη hC.le
  let K := K₁ + K₂ + 1
  have hKpos : 0 < K := by dsimp [K]; linarith
  have hK1 : K₁ ≤ K := by dsimp [K]; linarith
  have hK2 : K₂ ≤ K := by dsimp [K]; linarith
  have hKunit : 1 ≤ K := by dsimp [K]; linarith
  refine ⟨K, hKpos, h₀, ?_⟩
  intro α S z hdb
  have hP := sieve_product_nonneg α S z η C hdb
  have hmain : 0 ≤ S.X * S.product := mul_nonneg S.X_nonneg hP
  constructor
  · have hu := hupper α S z hdb
    have hm := mul_le_mul_of_nonneg_right hK1 hmain
    have hr := mul_le_mul_of_nonneg_right hKunit
      (sieve_remainderSum_nonneg α S (z ^ (10 : ℕ)))
    nlinarith only [hu, hm, hr]
  · intro h hh he
    refine ⟨?_, exists_sieve_polynomials α S z η C hdb h he⟩
    have he₀ := herror α S z hdb h hh he
    have hm := mul_le_mul_of_nonneg_right hK2
      (mul_nonneg (Real.exp_pos (-(h : ℝ))).le hmain)
    have hr := mul_le_mul_of_nonneg_right hKunit
      (sieve_remainderSum_nonneg α S (z ^ (4 * h + 2)))
    nlinarith only [he₀, hm, hr]

example : Blueprint.BlockSieve := blockSieve_proof

end Erdos821.PrelimLemmas
