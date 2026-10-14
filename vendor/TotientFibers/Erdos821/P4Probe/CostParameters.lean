import Erdos821.P4Probe.Parameters

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

lemma kernel_cost_power (L q ξ : ℝ) (hL : 1 ≤ L) (hq : 0 < q) (hξ : 0 < ξ) :
    max 1 ((((⌊L ^ q⌋₊ : ℕ) : ℝ) ^ 2 / (L ^ (-ξ))) ^ 2) ≤
      L ^ (4 * q + 2 * ξ) := by
  have hp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hf : ((⌊L ^ q⌋₊ : ℕ) : ℝ) ≤ L ^ q := Nat.floor_le (Real.rpow_nonneg hp.le _)
  have hb : (((⌊L ^ q⌋₊ : ℕ) : ℝ) ^ 2 / (L ^ (-ξ))) ^ 2 ≤
      ((L ^ q) ^ (2 : ℕ) / L ^ (-ξ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hf 2)
        (Real.rpow_nonneg hp.le _)) 2
  have he : ((L ^ q) ^ (2 : ℕ) / L ^ (-ξ)) ^ (2 : ℕ) =
      L ^ (4 * q + 2 * ξ) := by
    rw [← Real.rpow_natCast (L ^ q) 2, ← Real.rpow_mul hp.le,
      ← Real.rpow_sub hp, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hp.le]
    congr 1
    norm_num
    ring
  apply max_le
  · exact Real.one_le_rpow hL (by positivity)
  · exact hb.trans_eq he

lemma family_cost_power (F : FixedData) (P : PrimeGroups) (J m : ℕ)
    (hj : m ≤ J) (block : P.BigGroup → Bool) (x q h ξ : ℝ)
    (hL : 2 ≤ L x) (hq : 0 < q) (hξ : 0 < ξ)
    (hn : (Fintype.card P.BigGroup : ℝ) ≤ F.C₀ * T x) :
    ((probeFamily F P J m hj block ⌊L x ^ q⌋₊ (L x ^ (-h))
      (L x ^ (-ξ))).model 1 0).patternMass ≤
        L x ^ ((m : ℝ) * F.C₀ * Real.log 2 + 4 * q + 2 * ξ + 1) := by
  have hp : 0 < L x := by linarith
  have hL1 : 1 ≤ L x := by linarith
  have hC₀ : 0 < F.C₀ := F.C₀_pos
  have hcost := probeFamily_patternMass_le F P J m hj block ⌊L x ^ q⌋₊
    (L x ^ (-h)) (L x ^ (-ξ)) (Real.rpow_pos_of_pos hp _)
  have hnum := probe_power_le 2 F.C₀ m (Fintype.card P.BigGroup) (L x)
    (by norm_num) hL1 hn
  have hkernel := kernel_cost_power (L x) q ξ hL1 hq hξ
  calc
    _ ≤ ((2 : ℝ) ^ (m * Fintype.card P.BigGroup) + 1) *
        max 1 ((((⌊L x ^ q⌋₊ : ℕ) : ℝ) ^ 2 / L x ^ (-ξ)) ^ 2) := hcost
    _ ≤ (L x ^ ((m : ℝ) * F.C₀ * Real.log 2) + 1) *
        L x ^ (4 * q + 2 * ξ) :=
      mul_le_mul (add_le_add hnum le_rfl) hkernel
        (le_trans zero_le_one (le_max_left ..))
        (by positivity)
    _ ≤ (2 * L x ^ ((m : ℝ) * F.C₀ * Real.log 2)) *
        L x ^ (4 * q + 2 * ξ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hp.le _)
      have hone : 1 ≤ L x ^ ((m : ℝ) * F.C₀ * Real.log 2) :=
        Real.one_le_rpow hL1 (mul_nonneg (by positivity)
          (Real.log_nonneg (by norm_num)))
      linarith
    _ = 2 * L x ^ ((m : ℝ) * F.C₀ * Real.log 2 + 4 * q + 2 * ξ) := by
      rw [mul_assoc, ← Real.rpow_add hp]
      congr 2
      ring
    _ ≤ L x * L x ^ ((m : ℝ) * F.C₀ * Real.log 2 + 4 * q + 2 * ξ) :=
      mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hp.le _)
    _ = _ := by
      rw [Real.rpow_add hp ((m : ℝ) * F.C₀ * Real.log 2 + 4 * q + 2 * ξ) 1,
        Real.rpow_one]
      ring

end
end Erdos821.P4Probe
