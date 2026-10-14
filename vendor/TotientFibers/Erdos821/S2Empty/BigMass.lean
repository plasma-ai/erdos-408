import Erdos821.S2Empty.BigTilted

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Empty

open Erdos821.Blueprint.Graph

theorem big_tilted_sum_le_inv (F : FixedData) (P : PrimeGroups) (n : ℕ)
    (g : P.BigGroup) (e : ℝ) (hV : 0 < P.V g.val) (he : e < 1)
    (hfloor : ∀ p : P.Prime g.val, 1 - e ≤ baselinePrime F n p.val) :
    (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ≤ (1 - e)⁻¹ := by
  classical
  have hden : 0 < 1 - e := by linarith
  have hVeq : (∑ p : P.Prime g.val, (p.val : ℝ)⁻¹) = P.V g.val := by
    change (∑ p : P.primes g.val, (p : ℝ)⁻¹) =
      ∑ p ∈ P.primes g.val, (p : ℝ)⁻¹
    exact Finset.sum_coe_sort (P.primes g.val) (fun p : ℕ => (p : ℝ)⁻¹)
  have hmuSum : (∑ p : P.Prime g.val, P.mu g.val p) = 1 := by
    calc
      _ = ∑ p : P.Prime g.val, (P.V g.val)⁻¹ * (p.val : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [PrimeGroups.mu]
        ring
      _ = (P.V g.val)⁻¹ * ∑ p : P.Prime g.val, (p.val : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
      _ = 1 := by rw [hVeq, inv_mul_cancel₀ hV.ne']
  have hterm (p : P.Prime g.val) :
      tiltedMu F P n g.val p ≤ P.mu g.val p * (1 - e)⁻¹ := by
    have hp : (p.val : ℝ) ≠ 0 := by
      exact_mod_cast (P.prime g.val p.val p.property).ne_zero
    have hpPos : 0 < (p.val : ℝ) := by
      exact_mod_cast (P.prime g.val p.val p.property).pos
    have hbasePos : 0 < baselinePrime F n p.val :=
      lt_of_lt_of_le (by linarith) (hfloor p)
    have hratio : (baselinePrime F n p.val)⁻¹ ≤ (1 - e)⁻¹ :=
      (inv_le_inv₀ hbasePos hden).mpr (hfloor p)
    have htilt : tiltedMu F P n g.val p =
        P.mu g.val p * (baselinePrime F n p.val)⁻¹ := by
      unfold tiltedMu PrimeGroups.mu
      field_simp [hV.ne', hp, hbasePos.ne']
    rw [htilt]
    have hmuNonneg : 0 ≤ P.mu g.val p := by
      unfold PrimeGroups.mu
      positivity
    exact mul_le_mul_of_nonneg_left hratio hmuNonneg
  calc
    _ ≤ ∑ p : P.Prime g.val, P.mu g.val p * (1 - e)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact hterm p
    _ = 1 * (1 - e)⁻¹ := by rw [← Finset.sum_mul, hmuSum]
    _ = (1 - e)⁻¹ := by ring


end Erdos821.S2Empty
