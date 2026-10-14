import Erdos821.S34.BilinearDecayArithmetic

set_option autoImplicit false

namespace Erdos821.S34Core
noncomputable section

def comparisonPowerQ (B κ d : ℝ) : ℝ := 2 * (B + κ + 10) + d + 3
def comparisonPowerH (B q C₄ : ℝ) : ℝ := 5 * q + C₄ + B + 20
def comparisonPowerXi (B d h : ℝ) : ℝ := 2 * B + d + 1 + h + 20
def comparisonPowerD (B q ξ : ℝ) : ℝ := B + ξ + 3 * q + 20

theorem rpow_nat_pow (L a : ℝ) (n : ℕ) (hL : 0 ≤ L) :
    (L ^ a) ^ n = L ^ ((n : ℝ) * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
  congr 1
  ring

theorem sqrt_rpow (L a : ℝ) (hL : 0 ≤ L) : Real.sqrt (L ^ a) = L ^ (a / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL]
  congr 1
  ring

theorem rpow_cost_absorption (L C a b : ℝ) (hL : 1 ≤ L) (hC : C ≤ L) (hab : b + 1 ≤ a) :
    C * L ^ b ≤ L ^ a := by
  have hp : 0 < L := by linarith
  calc
    _ ≤ L * L ^ b := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hp.le _)
    _ = L ^ (b + 1) := by
      calc
        _ = L ^ b * L ^ (1 : ℝ) := by rw [Real.rpow_one]; ring
        _ = _ := (Real.rpow_add hp _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL hab

theorem floor_rpow_bounds (L q : ℝ) (hL : 0 < L) (hpow : 2 ≤ L ^ q) :
    0 < (⌊L ^ q⌋₊ : ℝ) ∧ L ^ q / 2 ≤ (⌊L ^ q⌋₊ : ℝ) ∧ (⌊L ^ q⌋₊ : ℝ) ≤ L ^ q := by
  have hfloor := Nat.lt_floor_add_one (L ^ q)
  have hnonneg : (0 : ℝ) ≤ (⌊L ^ q⌋₊ : ℝ) := Nat.cast_nonneg _
  have hlow : L ^ q / 2 ≤ (⌊L ^ q⌋₊ : ℝ) := by linarith
  refine ⟨?_, hlow, Nat.floor_le (Real.rpow_nonneg hL.le _)⟩
  linarith

theorem minor_power_precision (L K B κ d U V r : ℝ)
    (hL : 2 ≤ L) (hK : 0 < K) (hKL : 60 * K ≤ L)
    (hB : 0 ≤ B) (hκ : 0 ≤ κ) (hd : 0 ≤ d)
    (hU : L ^ comparisonPowerQ B κ d ≤ U) (hV : L ^ comparisonPowerQ B κ d ≤ V)
    (hr : 1 ≤ r) (hrQ : (⌊L ^ comparisonPowerQ B κ d⌋₊ : ℝ) < r)
    (hrS : r ≤ U * V / L ^ comparisonPowerQ B κ d)
    (hlog : Real.log (2 * r) ≤ L ^ (d + 1)) :
    20 * K * L ^ κ * Real.sqrt (bilinearDecay U V r) ≤ L ^ (-B - 2) := by
  let q := comparisonPowerQ B κ d
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hq : 1 ≤ q := by dsimp [q, comparisonPowerQ]; linarith
  have hp2 : 2 ≤ L ^ q := hL.trans (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL1 hq)
  have hpowp : 0 < L ^ q := Real.rpow_pos_of_pos hLp _
  obtain ⟨hQp, hQlo, hQhi⟩ := floor_rpow_bounds L q hLp hp2
  have hUp : 0 < U := hpowp.trans_le hU
  have hVp : 0 < V := hpowp.trans_le hV
  have hminor := bilinear_decay_minor_bound U V r ⌊L ^ q⌋₊ (L ^ q) (L ^ (d + 1))
    hUp hVp hr hQp hpowp (Real.rpow_nonneg hLp.le _) hrQ hrS hlog
  have hVinv : 1 / V ≤ L ^ (-q) := by
    calc
      _ ≤ 1 / L ^ q := one_div_le_one_div_of_le hpowp hV
      _ = _ := by rw [Real.rpow_neg hLp.le, one_div]
  have hQinv : 1 / (⌊L ^ q⌋₊ : ℝ) ≤ 2 * L ^ (-q) := by
    calc
      _ ≤ 1 / (L ^ q / 2) := one_div_le_one_div_of_le (by positivity) hQlo
      _ = _ := by rw [Real.rpow_neg hLp.le]; ring
  have hUdiv : L ^ (d + 1) / U ≤ L ^ (d + 1 - q) := by
    rw [Real.rpow_sub hLp]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hLp.le _) hpowp hU
  have hcomp : L ^ (-q) ≤ L ^ (d + 1 - q) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hdec : bilinearDecay U V r ≤ 5 * L ^ (-2 * (B + κ + 11)) := by
    have hqeq : d + 1 - q = -2 * (B + κ + 11) := by dsimp [q, comparisonPowerQ]; ring
    rw [Real.rpow_sub hLp] at hUdiv
    have hsEq : L ^ (d + 1) / L ^ q = L ^ (-2 * (B + κ + 11)) := by rw [← Real.rpow_sub hLp, hqeq]
    rw [hsEq] at hminor hUdiv
    rw [hqeq] at hcomp
    linarith
  have hs5 : Real.sqrt 5 ≤ 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hroot : Real.sqrt (bilinearDecay U V r) ≤ 3 * L ^ (-(B + κ + 11)) := by
    calc
      _ ≤ Real.sqrt (5 * L ^ (-2 * (B + κ + 11))) := Real.sqrt_le_sqrt hdec
      _ = Real.sqrt 5 * L ^ (-(B + κ + 11)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5), sqrt_rpow L _ hLp.le]
        congr 1
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hs5 (Real.rpow_nonneg hLp.le _)
  calc
    _ ≤ 20 * K * L ^ κ * (3 * L ^ (-(B + κ + 11))) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = 60 * K * L ^ (-B - 11) := by
      have he : L ^ κ * L ^ (-(B + κ + 11)) = L ^ (-B - 11) := by
        rw [← Real.rpow_add hLp]
        congr 1
        ring
      calc
        _ = 60 * K * (L ^ κ * L ^ (-(B + κ + 11))) := by ring
        _ = _ := by rw [he]
    _ ≤ _ := rpow_cost_absorption L (60 * K) (-B - 2) (-B - 11) hL1 hKL (by linarith)

end
end Erdos821.S34Core
