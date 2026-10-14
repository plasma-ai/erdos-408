import Erdos821.P4Probe.Blocks
import Erdos821.P4Probe.Costs

set_option autoImplicit false
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

def probeBeta (ell m : ℕ) : ℝ := 2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell

lemma exists_small_probe_beta (ell : ℕ) (hell : 1 ≤ ell) (c₀ E : ℝ)
    (hc₀ : 0 < c₀) (hE : 0 < E) :
    ∃ m : ℕ, 1 ≤ m ∧ 0 < probeBeta ell m ∧ probeBeta ell m < 1 ∧
      (c₀ / 6) * Real.log (probeBeta ell m) ≤ -(E + 2) := by
  let delta := Real.exp (-6 * (E + 2) / c₀)
  have hd : 0 < delta := Real.exp_pos _
  have hd1 : delta < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by nlinarith) hc₀
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (2 * (ell : ℝ) ^ ell / delta))
  have hm1 : 1 < (m : ℝ) := (le_max_left ..).trans_lt hm
  have hmpos : 0 < (m : ℝ) := by linarith
  have hmn : 1 ≤ m := by exact_mod_cast hm1.le
  have hp : 0 < probeBeta ell m := by
    unfold probeBeta
    have : 0 < (ell : ℝ) := by exact_mod_cast hell
    positivity
  have hbd : probeBeta ell m < delta := by
    have hpow : (m : ℝ) ≤ (m : ℝ) ^ ell := le_self_pow₀ hm1.le (by omega)
    have hfrac : 2 * (ell : ℝ) ^ ell / delta < (m : ℝ) :=
      (le_max_right ..).trans_lt hm
    have hnum : 2 * (ell : ℝ) ^ ell < delta * (m : ℝ) :=
      by simpa only [mul_comm] using (div_lt_iff₀ hd).mp hfrac
    unfold probeBeta
    apply (div_lt_iff₀ (pow_pos hmpos ell)).mpr
    exact hnum.trans_le (mul_le_mul_of_nonneg_left hpow hd.le)
  refine ⟨m, hmn, hp, hbd.trans hd1, ?_⟩
  have hl : Real.log (probeBeta ell m) ≤ -6 * (E + 2) / c₀ := by
    have := Real.log_le_log hp hbd.le
    simpa only [delta, Real.log_exp] using this
  calc
    _ ≤ (c₀ / 6) * (-6 * (E + 2) / c₀) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ = _ := by field_simp

lemma sqrt_beta_power_le (beta c₀ E L : ℝ) (b : ℕ)
    (hb : 0 < beta) (hb1 : beta < 1) (hc : 0 < c₀) (hL : 1 ≤ L)
    (hlog : c₀ / 6 * Real.log beta ≤ -(E + 2))
    (hsize : c₀ * Real.log L / 3 ≤ (b : ℝ)) :
    Real.sqrt (beta ^ b) ≤ L ^ (-(E + 2)) := by
  have hlb : Real.log beta < 0 := Real.log_neg hb hb1
  have hlL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hsq : Real.sqrt (beta ^ b) = Real.exp (Real.log beta * (b : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hb.le,
      Real.rpow_def_of_pos hb]
    congr 1
    ring
  rw [hsq, Real.rpow_def_of_pos hLpos]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ Real.log beta * (c₀ * Real.log L / 3) / 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonpos_left hsize hlb.le) (by norm_num)
    _ = (c₀ / 6 * Real.log beta) * Real.log L := by ring
    _ ≤ -(E + 2) * Real.log L := mul_le_mul_of_nonneg_right hlog hlL
    _ = _ := by ring

lemma probe_power_le (a C : ℝ) (m n : ℕ) (L : ℝ)
    (ha : 1 ≤ a) (hL : 1 ≤ L) (hn : (n : ℝ) ≤ C * Real.log L) :
    a ^ (m * n) ≤ L ^ ((m : ℝ) * C * Real.log a) := by
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hapos, Real.rpow_def_of_pos hLpos]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hn
    (mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg ha))
  simpa only [Nat.cast_mul] using (show Real.log a * ((m : ℝ) * (n : ℝ)) ≤
    Real.log L * ((m : ℝ) * C * Real.log a) by nlinarith [h])

lemma three_errors_le (L E : ℝ) (hL : 2 ≤ L) :
    3 * L ^ (-(E + 2)) ≤ L ^ (-E) := by
  have hp : 0 < L := by linarith
  have hLp : 0 ≤ L := hp.le
  have hpow : (3 : ℝ) ≤ L ^ (2 : ℕ) := by nlinarith
  calc
    _ ≤ L ^ (2 : ℕ) * L ^ (-(E + 2)) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hLp _)
    _ = L ^ (-E) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hp]
      congr 1
      norm_num <;> ring

end
end Erdos821.P4Probe
