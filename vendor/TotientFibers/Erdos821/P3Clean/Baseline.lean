import Erdos821.P3Clean.Laws
import Erdos821.Leaves.Arith

/-! Positivity and a uniform density ratio for the tilted active laws. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem visitQ_pos (F : FixedData) (n : ℕ) (i : Fin (n + 1)) : 0 < visitQ F.q n i := by
  unfold visitQ
  split_ifs
  · exact Real.sqrt_pos.mpr F.q_pos
  · exact F.q_pos

theorem visitQ_lt_one (F : FixedData) (n : ℕ) (i : Fin (n + 1)) : visitQ F.q n i < 1 := by
  unfold visitQ
  split_ifs
  · simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt F.q_pos.le F.q_lt
  · exact F.q_lt

theorem eta_nonneg (F : FixedData) (n : ℕ) (i : Fin (n + 1)) : 0 ≤ eta F n i :=
  sub_nonneg.mpr (visitQ_lt_one F n i).le

theorem eta_le_one (F : FixedData) (n : ℕ) (i : Fin (n + 1)) : eta F n i ≤ 1 :=
  sub_le_self 1 (visitQ_pos F n i).le

theorem eta_sum_bounds (F : FixedData) (n : ℕ) :
    0 ≤ (∑ i : Fin (n + 1), eta F n i) ∧
      (∑ i : Fin (n + 1), eta F n i) ≤ (n + 1 : ℕ) := by
  refine ⟨Finset.sum_nonneg (fun i _ => eta_nonneg F n i), ?_⟩
  calc
    _ ≤ ∑ _ : Fin (n + 1), (1 : ℝ) := Finset.sum_le_sum (fun i _ => eta_le_one F n i)
    _ = _ := by simp

theorem baselinePrime_bounds (F : FixedData) (n p : ℕ) (hp : 0 < p)
    (hn : 2 * (n + 1) ≤ p) :
    0 < baselinePrime F n p ∧ 1 ≤ (baselinePrime F n p)⁻¹ ∧
      (baselinePrime F n p)⁻¹ ≤ 1 + 2 * ((n + 1 : ℕ) : ℝ) / p := by
  obtain ⟨he0, he1⟩ := eta_sum_bounds F n
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have he2 : 2 * (∑ i : Fin (n + 1), eta F n i) ≤ (p : ℝ) := by
    have hnR : 2 * ((n + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hn
    linarith
  have h := tilted_density_bound (p : ℝ) (∑ i : Fin (n + 1), eta F n i) hpR he0 he2
  have heq : baselinePrime F n p = 1 - (∑ i : Fin (n + 1), eta F n i) / (p : ℝ) := by
    unfold baselinePrime
    simp only [div_eq_mul_inv, mul_comm]
  rw [heq]
  refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
  simpa only [add_comm] using add_le_add_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left he1 (by norm_num : (0 : ℝ) ≤ 2)) hpR.le) 1

theorem tiltedMu_eq_mu_mul (F : FixedData) (P : PrimeGroups) (n : ℕ)
    (g : P.Group) (p : P.Prime g) :
    tiltedMu F P n g p = P.mu g p * (baselinePrime F n p.val)⁻¹ := by
  unfold tiltedMu PrimeGroups.mu
  rw [mul_inv_rev]
  ring

theorem tiltedMu_density_bounds (F : FixedData) (P : PrimeGroups) (n : ℕ)
    (g : P.Group) (p : P.Prime g) (hn : 2 * (n + 1) ≤ p.val) :
    P.mu g p ≤ tiltedMu F P n g p ∧
      tiltedMu F P n g p ≤ P.mu g p * (1 + 2 * ((n + 1 : ℕ) : ℝ) / p.val) := by
  obtain ⟨_, h1, h2⟩ := baselinePrime_bounds F n p.val
    (P.prime g p.val p.property).pos hn
  rw [tiltedMu_eq_mu_mul]
  exact ⟨by simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 (mu_pos g p).le,
    mul_le_mul_of_nonneg_left h2 (mu_pos g p).le⟩


end Erdos821.P3Clean
