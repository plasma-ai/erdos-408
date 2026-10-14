import Erdos821.P5.ExceptionalCount

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- Floor choice of the growing moment, with all estimates made explicit. -/
theorem moment_power_choice (L Y P a b : ℝ)
    (hL : 1 ≤ L) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hY : 0 < Y) (hYlo : L / 2 ≤ Real.log Y) (hYhi : Real.log Y ≤ 2 * L)
    (hP : 0 < P) (hPlo : Real.exp (L ^ a) / 2 ≤ P)
    (hPhi : P ≤ Real.exp (L ^ b))
    (hsub : L ^ b + Real.log 2 ≤ L / 2) :
    let m := ⌊Real.log Y / Real.log (2 * P)⌋₊
    1 ≤ m ∧ (2 * P) ^ m ≤ Y ∧
      (m : ℝ) ≤ 2 * L ^ (1 - a) ∧
      Real.log Y - m * Real.log P ≤ Real.log 2 + L ^ b + m * Real.log 2 ∧
      Real.log (m : ℝ) ≤ Real.log 2 + Real.log L := by
  dsimp only
  let m := ⌊Real.log Y / Real.log (2 * P)⌋₊
  have hLpos : 0 < L := by linarith
  have hpowpos : 0 < L ^ a := Real.rpow_pos_of_pos hLpos a
  have hdenlo : L ^ a ≤ Real.log (2 * P) := by
    have h := Real.log_le_log (Real.exp_pos (L ^ a))
      (show Real.exp (L ^ a) ≤ 2 * P by linarith)
    simpa only [Real.log_exp] using h
  have hden : 0 < Real.log (2 * P) := hpowpos.trans_le hdenlo
  have hlogP : Real.log P ≤ L ^ b := by
    simpa only [Real.log_exp] using Real.log_le_log hP hPhi
  have hdenhi : Real.log (2 * P) ≤ Real.log 2 + L ^ b := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hP.ne']
    linarith
  have hlogYpos : 0 < Real.log Y := by linarith
  have hquot : 0 ≤ Real.log Y / Real.log (2 * P) := by positivity
  have hdenY : Real.log (2 * P) ≤ Real.log Y := by linarith
  have hm1 : 1 ≤ m := Nat.le_floor ((le_div_iff₀ hden).mpr
    (by simpa only [Nat.cast_one, one_mul] using hdenY))
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
  have hmle := Nat.floor_le hquot
  have hprod : (m : ℝ) * Real.log (2 * P) ≤ Real.log Y :=
    (le_div_iff₀ hden).mp hmle
  have hpowy : (2 * P) ^ m ≤ Y := by
    apply (Real.log_le_log_iff (pow_pos (by positivity) m) hY).mp
    simpa only [Real.log_pow] using hprod
  have hmLa : (m : ℝ) * L ^ a ≤ 2 * L := by
    have h := mul_le_mul_of_nonneg_left hdenlo hmpos.le
    linarith
  have hdiv : 2 * L / L ^ a = 2 * L ^ (1 - a) := by
    rw [Real.rpow_sub hLpos, Real.rpow_one]
    ring
  have hmlength : (m : ℝ) ≤ 2 * L ^ (1 - a) := by
    rw [← hdiv]
    exact (le_div_iff₀ hpowpos).mpr hmLa
  have hfloorlt : Real.log Y / Real.log (2 * P) < (m : ℝ) + 1 :=
    Nat.lt_floor_add_one (Real.log Y / Real.log (2 * P))
  have hresid : Real.log Y - m * Real.log P ≤ Real.log 2 + L ^ b + m * Real.log 2 := by
    have h : Real.log Y < ((m : ℝ) + 1) * Real.log (2 * P) :=
      (div_lt_iff₀ hden).mp hfloorlt
    conv_rhs at h => arg 2; rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hP.ne']
    nlinarith
  have hmL : (m : ℝ) ≤ 2 * L := by
    have hpow : L ^ (1 - a) ≤ L := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hL (show 1 - a ≤ 1 by linarith)
    linarith
  have hlogm : Real.log (m : ℝ) ≤ Real.log 2 + Real.log L := by
    have h := Real.log_le_log hmpos hmL
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hLpos.ne'] at h
  exact ⟨hm1, hpowy, hmlength, hresid, hlogm⟩

end Erdos821.P5Core
