import Erdos821.P5.FreeCollisionTheorem

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem two_pow_primeFactors_card_le (n : ℕ) (hn : 0 < n) :
    2 ^ n.primeFactors.card ≤ n := by
  calc
    _ = ∏ p ∈ n.primeFactors, (2 : ℕ) := by simp only [Finset.prod_const]
    _ ≤ ∏ p ∈ n.primeFactors, p :=
      Finset.prod_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

theorem primeFactors_card_log (n : ℕ) (hn : 0 < n) :
    (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
  have hpow : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by
    exact_mod_cast two_pow_primeFactors_card_le n hn
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
  simpa only [Real.log_pow, mul_comm] using hlog

theorem primeFactors_card_le_log_scale (x r : ℝ) (hx : 0 < x)
    (n : ℕ) (hn : 0 < n) (hnx : (n : ℝ) ≤ x ^ r) :
    (n.primeFactors.card : ℝ) ≤ (r / Real.log 2) * L x := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog := Real.log_le_log hnR hnx
  rw [Real.log_rpow hx r] at hlog
  have h := (primeFactors_card_log n hn).trans hlog
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  simpa only [L] using h

end Erdos821.P5Core
