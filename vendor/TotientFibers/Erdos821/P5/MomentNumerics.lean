import Erdos821.P5.ExceptionalAsymptotics

noncomputable section
open Filter

namespace Erdos821.P5Core

/-- The factorial moment bound becomes subpower after the floor choice. -/
theorem moment_numerical_bound (L Y P a b A C : ℝ)
    (hL : Real.exp 1 ≤ L) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hA : 0 < A) (hC : 0 < C) (hY : 0 < Y)
    (hYlo : L / 2 ≤ Real.log Y) (hYhi : Real.log Y ≤ 2 * L)
    (hP : 0 < P) (hPlo : Real.exp (L ^ a) / 2 ≤ P)
    (hPhi : P ≤ Real.exp (L ^ b)) (hsub : L ^ b + Real.log 2 ≤ L / 2) :
    let m := ⌊Real.log Y / Real.log (2 * P)⌋₊
    C * Y * (1 + Real.log (2 * Y)) ^ 3 *
      Nat.factorial m * (3 / P) ^ m / (L ^ (-A)) ^ (2 * m) ≤
      Real.exp ((|Real.log C| + 30 + 4 * A) *
        (L ^ b + L ^ (1 - a) * Real.log L)) := by
  dsimp only
  let m := ⌊Real.log Y / Real.log (2 * P)⌋₊
  let B := 1 + Real.log (2 * Y)
  let R := C * Y * B ^ 3 * Nat.factorial m * (3 / P) ^ m / (L ^ (-A)) ^ (2 * m)
  have hL1 : 1 ≤ L := by
    have h : (1 : ℝ) ≤ Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
    exact h.trans hL
  have hLpos : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hL
  have hlogLpos : 0 ≤ Real.log L := by linarith
  obtain ⟨hm1, _, hmlength, hresid, hlogm⟩ :=
    moment_power_choice L Y P a b hL1 ha hab hb hY hYlo hYhi hP hPlo hPhi hsub
  change 1 ≤ m at hm1
  change (m : ℝ) ≤ 2 * L ^ (1 - a) at hmlength
  change Real.log Y - m * Real.log P ≤ Real.log 2 + L ^ b + m * Real.log 2 at hresid
  change Real.log (m : ℝ) ≤ Real.log 2 + Real.log L at hlogm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
  have hfactpos : (0 : ℝ) < Nat.factorial m := by exact_mod_cast Nat.factorial_pos m
  have hlogYpos : 0 < Real.log Y := by linarith
  have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlog3le : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
  have hBpos : 0 < B := by
    dsimp [B]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hY.ne']
    linarith
  have hBup : B ≤ 4 * L := by
    dsimp [B]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hY.ne']
    linarith
  have hlogB : Real.log B ≤ 4 * Real.log L := by
    have h := Real.log_le_log hBpos hBup
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hLpos.ne'] at h
    have hlog4 : Real.log 4 ≤ 3 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
    linarith
  have hfact : Real.log (Nat.factorial m : ℝ) ≤ (m : ℝ) * (Real.log 2 + Real.log L) := by
    have hfac : (Nat.factorial m : ℝ) ≤ (m : ℝ) ^ m := by
      exact_mod_cast Nat.factorial_le_pow m
    have h := Real.log_le_log hfactpos hfac
    rw [Real.log_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_left hlogm hmpos.le)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hlogR : Real.log R = Real.log C + Real.log Y + 3 * Real.log B +
      Real.log (Nat.factorial m : ℝ) + m * (Real.log 3 - Real.log P) +
      2 * A * m * Real.log L := by
    dsimp [R]
    rw [Real.log_div (by positivity) (by positivity)]
    repeat rw [Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow]
    rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) hP.ne', Real.log_rpow hLpos]
    push_cast
    ring
  have hsmall : Real.log 3 + 2 * Real.log 2 ≤ 4 * Real.log L := by linarith
  have hsmallm := mul_le_mul_of_nonneg_left hsmall hmpos.le
  have hpre : Real.log R ≤ |Real.log C| + 1 + L ^ b + 12 * Real.log L +
      (5 + 2 * A) * m * Real.log L := by
    rw [hlogR]
    have hCabs := le_abs_self (Real.log C)
    nlinarith only [hresid, hfact, hlogB, hCabs, hsmallm, hlog2le]
  have hunit : 1 ≤ L ^ (1 - a) := Real.one_le_rpow hL1 (by linarith)
  have hunitb : 1 ≤ L ^ b := Real.one_le_rpow hL1 (by linarith)
  have hunitlog := mul_le_mul_of_nonneg_right hunit hlogLpos
  have hmlog := mul_le_mul_of_nonneg_right hmlength hlogLpos
  have hlarge : (5 + 2 * A) * (m : ℝ) * Real.log L ≤
      (10 + 4 * A) * L ^ (1 - a) * Real.log L := by
    have h := mul_le_mul_of_nonneg_left hmlog (show 0 ≤ 5 + 2 * A by linarith)
    convert h using 1 <;> ring
  have hconstant : |Real.log C| + 1 ≤ (|Real.log C| + 1) * L ^ b := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hunitb
      (show 0 ≤ |Real.log C| + 1 by positivity)
  have hfinal : Real.log R ≤ (|Real.log C| + 30 + 4 * A) *
      (L ^ b + L ^ (1 - a) * Real.log L) := by
    have hpowb : 0 ≤ L ^ b := Real.rpow_nonneg hLpos.le b
    have hpowlog : 0 ≤ L ^ (1 - a) * Real.log L := by positivity
    have hsecond : 12 * Real.log L + (5 + 2 * A) * (m : ℝ) * Real.log L ≤
        (22 + 4 * A) * (L ^ (1 - a) * Real.log L) := by
      nlinarith only [hunitlog, hlarge]
    have hcomb : Real.log R ≤ (|Real.log C| + 2) * L ^ b +
        (22 + 4 * A) * (L ^ (1 - a) * Real.log L) := by
      nlinarith only [hpre, hsecond, hconstant]
    have hcoefb := mul_le_mul_of_nonneg_right
      (show |Real.log C| + 2 ≤ |Real.log C| + 30 + 4 * A by linarith) hpowb
    have hcoeflog := mul_le_mul_of_nonneg_right
      (show 22 + 4 * A ≤ |Real.log C| + 30 + 4 * A by linarith [abs_nonneg (Real.log C)])
      hpowlog
    nlinarith only [hcomb, hcoefb, hcoeflog]
  have h := Real.exp_le_exp.mpr hfinal
  rw [Real.exp_log hRpos] at h
  exact h

end Erdos821.P5Core
