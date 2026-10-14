import Erdos821.S34.PrecisionPowers

set_option autoImplicit false

namespace Erdos821.S34Core
noncomputable section

theorem rpow_quot_product (L K a b c : ℝ) (hL : 0 < L) :
    L ^ a * (K * L ^ b) / L ^ c = K * L ^ (a + b - c) := by
  calc
    _ = K * (L ^ a * L ^ b / L ^ c) := by ring
    _ = _ := by rw [← Real.rpow_add hL, ← Real.rpow_sub hL]

theorem major_power_precision (L K B q d C₄ hExp ξExp DExp ζ NA NB : ℝ) (Q : ℕ)
    (hL : 3 ≤ L) (hK : 0 < K) (hKL : 3 * K ≤ L)
    (hπL : 2 * (1 + 64 * Real.pi) ≤ L)
    (hB : 0 ≤ B) (hq : 0 ≤ q) (hd : 0 ≤ d) (hC₄ : 0 ≤ C₄)
    (hhEq : hExp = comparisonPowerH B q C₄)
    (hξEq : ξExp = comparisonPowerXi B d hExp)
    (hDEq : DExp = comparisonPowerD B q ξExp)
    (hQ : (Q : ℝ) ≤ L ^ q) (hζ : |ζ| ≤ L ^ C₄)
    (hNA : NA ≤ L ^ (d + 1 + hExp)) (hNB : NB ≤ L ^ (d + 1 + hExp)) :
    (Q : ℝ) ^ 2 * (K * L ^ (-DExp)) / L ^ (-ξExp) ≤ 1 ∧
    Real.sqrt ((NA + NB) * L ^ (-ξExp)) +
        (Q : ℝ) ^ 4 * (2 * L ^ (-hExp) * (|ζ| + 64 * Real.pi * L ^ q)) +
        3 * ((Q : ℝ) ^ 2 * (K * L ^ (-DExp)) / L ^ (-ξExp)) * Real.sqrt (Q : ℝ) ≤ L ^ (-B) := by
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hKle : K ≤ L := by linarith
  let ε := (Q : ℝ) ^ 2 * (K * L ^ (-DExp)) / L ^ (-ξExp)
  have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
  have hQ2 : (Q : ℝ) ^ 2 ≤ L ^ (2 * q) := by
    have ht := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 2
    simpa only [rpow_nat_pow L q 2 hLp.le, Nat.cast_ofNat] using ht
  have hQ4 : (Q : ℝ) ^ 4 ≤ L ^ (4 * q) := by
    have ht := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 4
    simpa only [rpow_nat_pow L q 4 hLp.le, Nat.cast_ofNat] using ht
  have hε : ε ≤ K * L ^ (-B - q - 20) := by
    calc
      _ ≤ L ^ (2 * q) * (K * L ^ (-DExp)) / L ^ (-ξExp) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hQ2 (by positivity)) (by positivity)
      _ = _ := by
        rw [rpow_quot_product L K _ _ _ hLp]
        congr 1
        congr 1
        rw [hDEq]
        unfold comparisonPowerD
        ring
  have hε1 : ε ≤ 1 := by
    calc
      _ ≤ K * L ^ (-B - q - 20) := hε
      _ ≤ L ^ (0 : ℝ) := rpow_cost_absorption L K 0 (-B - q - 20) hL1 hKle (by linarith)
      _ = _ := Real.rpow_zero _
  have hdiscard : Real.sqrt ((NA + NB) * L ^ (-ξExp)) ≤ L ^ (-B - 2) := by
    have hm : (NA + NB) * L ^ (-ξExp) ≤ 2 * L ^ (-2 * B - 20) := by
      calc
        _ ≤ (2 * L ^ (d + 1 + hExp)) * L ^ (-ξExp) :=
          mul_le_mul_of_nonneg_right (by linarith [hNA, hNB]) (Real.rpow_nonneg hLp.le _)
        _ = _ := by
          rw [mul_assoc, ← Real.rpow_add hLp]
          congr 1
          congr 1
          rw [hξEq]
          unfold comparisonPowerXi
          ring
    have hs2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    calc
      _ ≤ Real.sqrt (2 * L ^ (-2 * B - 20)) := Real.sqrt_le_sqrt hm
      _ = Real.sqrt 2 * L ^ (-B - 10) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), sqrt_rpow L _ hLp.le]
        congr 1
        congr 1
        ring
      _ ≤ 2 * L ^ (-B - 10) := mul_le_mul_of_nonneg_right hs2 (Real.rpow_nonneg hLp.le _)
      _ ≤ _ := rpow_cost_absorption L 2 (-B - 2) (-B - 10) hL1 (by linarith) (by linarith)
  have hfreeze : (Q : ℝ) ^ 4 * (2 * L ^ (-hExp) * (|ζ| + 64 * Real.pi * L ^ q)) ≤ L ^ (-B - 2) := by
    have hC : |ζ| + 64 * Real.pi * L ^ q ≤ (1 + 64 * Real.pi) * L ^ (q + C₄) := by
      have hz : L ^ C₄ ≤ L ^ (q + C₄) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      have hq' : L ^ q ≤ L ^ (q + C₄) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      have ht := mul_le_mul_of_nonneg_left hq' (by positivity : 0 ≤ 64 * Real.pi)
      nlinarith [hζ.trans hz]
    calc
      _ ≤ L ^ (4 * q) * (2 * L ^ (-hExp) * ((1 + 64 * Real.pi) * L ^ (q + C₄))) :=
        mul_le_mul hQ4 (mul_le_mul_of_nonneg_left hC (by positivity)) (by positivity) (by positivity)
      _ = (2 * (1 + 64 * Real.pi)) * L ^ (-B - 20) := by
        have he : L ^ (4 * q) * L ^ (-hExp) * L ^ (q + C₄) = L ^ (-B - 20) := by
          rw [← Real.rpow_add hLp, ← Real.rpow_add hLp]
          congr 1
          rw [hhEq]
          unfold comparisonPowerH
          ring
        calc
          _ = (2 * (1 + 64 * Real.pi)) * (L ^ (4 * q) * L ^ (-hExp) * L ^ (q + C₄)) := by ring
          _ = _ := by rw [he]
      _ ≤ _ := rpow_cost_absorption L _ (-B - 2) (-B - 20) hL1 hπL (by linarith)
  have hchar : 3 * ε * Real.sqrt (Q : ℝ) ≤ L ^ (-B - 2) := by
    have hrootQ : Real.sqrt (Q : ℝ) ≤ L ^ (q / 2) := by
      calc
        _ ≤ Real.sqrt (L ^ q) := Real.sqrt_le_sqrt hQ
        _ = _ := sqrt_rpow L q hLp.le
    calc
      _ ≤ 3 * (K * L ^ (-B - q - 20)) * L ^ (q / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hε (by norm_num)) hrootQ (Real.sqrt_nonneg _) (by positivity)
      _ = (3 * K) * L ^ (-B - q / 2 - 20) := by
        have he : L ^ (-B - q - 20) * L ^ (q / 2) = L ^ (-B - q / 2 - 20) := by
          rw [← Real.rpow_add hLp]
          congr 1
          ring
        calc
          _ = (3 * K) * (L ^ (-B - q - 20) * L ^ (q / 2)) := by ring
          _ = _ := by rw [he]
      _ ≤ _ := rpow_cost_absorption L (3 * K) (-B - 2) (-B - q / 2 - 20) hL1 hKL (by linarith)
  refine ⟨hε1, ?_⟩
  have hs := add_le_add (add_le_add hdiscard hfreeze) hchar
  have hlast := rpow_cost_absorption L 3 (-B) (-B - 2) hL1 hL (by linarith)
  exact hs.trans (by convert hlast using 1 <;> ring)

end
end Erdos821.S34Core
