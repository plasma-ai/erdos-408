import Erdos821.P3Clean.DensityBounds

/-! Elementary scale estimates and exponential domination of fixed polynomials. -/

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem N_add_one_le (x : ℝ) (hL : 1 ≤ L x) : (N x : ℝ) + 1 ≤ 5 * L x := by
  have hp : (L x) ^ ((52 : ℝ) / 100) ≤ L x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL
      (show (52 : ℝ) / 100 ≤ 1 by norm_num)
  have hc := (Nat.ceil_lt_add_one (Real.rpow_nonneg (zero_le_one.trans hL) ((52 : ℝ) / 100))).le
  change (⌈(L x) ^ ((52 : ℝ) / 100)⌉₊ : ℝ) ≤ (L x) ^ ((52 : ℝ) / 100) + 1 at hc
  unfold N R
  push_cast
  linarith

theorem bigGroup_card (P : PrimeGroups) : Fintype.card P.BigGroup = P.bigGroups.card := by
  rw [Fintype.card_subtype]
  rfl

theorem bigGroup_card_le (F : FixedData) (x : ℝ) (P : PrimeGroups)
    (hP : P.Admissible F x) (hL : 1 ≤ L x) :
    (Fintype.card P.BigGroup : ℝ) ≤ F.C₀ * L x := by
  rw [bigGroup_card]
  exact hP.2.2.2.1.trans (mul_le_mul_of_nonneg_left (Real.log_le_self (zero_le_one.trans hL)) F.C₀_pos.le)

theorem bigPrime_lower (F : FixedData) (x : ℝ) (P : PrimeGroups) (hP : P.Admissible F x)
    (g : P.BigGroup) (p : P.Prime g.val) : Real.exp ((L x) ^ F.c) ≤ (p.val : ℝ) := by
  have h := hP.2.2.2.2.2 g.val p.val p.property
  have hh : Real.exp ((L x) ^ F.c) ≤ (p.val : ℝ) ∧
      (p.val : ℝ) ≤ Real.exp ((L x) ^ F.d) := by
    simpa [g.property] using h
  exact hh.1

theorem density_power_error (eps : ℝ) (he : 0 ≤ eps) (q : ℕ) (ht : (q : ℝ) * eps ≤ 1) :
    1 ≤ (1 + eps) ^ q ∧ (1 + eps) ^ q - 1 ≤ 2 * q * eps ∧ (1 + eps) ^ q ≤ 3 := by
  have hlo : 1 ≤ (1 + eps) ^ q := one_le_pow₀ (by linarith)
  have hpow : (1 + eps) ^ q ≤ Real.exp ((q : ℝ) * eps) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by simpa only [add_comm] using Real.add_one_le_exp eps) q
  have ht0 : 0 ≤ (q : ℝ) * eps := mul_nonneg (Nat.cast_nonneg _) he
  have herr := Real.abs_exp_sub_one_le (x := (q : ℝ) * eps)
    (by simpa only [abs_of_nonneg ht0] using ht)
  have hexp : 0 ≤ Real.exp ((q : ℝ) * eps) - 1 := by
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht0)
  rw [abs_of_nonneg hexp, abs_of_nonneg ht0] at herr
  refine ⟨hlo, ?_, ?_⟩ <;> nlinarith

theorem eventually_polynomial_exp (c : ℝ) (hc : 0 < c) (K s E : ℝ) :
    ∀ᶠ x : ℝ in atTop, K * (L x) ^ s / Real.exp ((L x) ^ c) ≤ (L x) ^ (-E) := by
  have hlog : Tendsto L atTop atTop := Real.tendsto_log_atTop
  have hpow : Tendsto (fun x => (L x) ^ c) atTop atTop := (tendsto_rpow_atTop hc).comp hlog
  have hlim := (tendsto_exp_div_rpow_atTop ((s + E) / c)).comp hpow
  filter_upwards [hlim.eventually (eventually_ge_atTop K), hlog.eventually (eventually_ge_atTop 1)] with x hx hL
  have hp : 0 < L x := zero_lt_one.trans_le hL
  have hpc : 0 ≤ L x := hp.le
  have heq : ((L x) ^ c) ^ ((s + E) / c) = (L x) ^ (s + E) := by
    rw [← Real.rpow_mul hpc]
    congr 1
    field_simp [hc.ne']
  change K ≤ Real.exp ((L x) ^ c) / ((L x) ^ c) ^ ((s + E) / c) at hx
  rw [heq] at hx
  have h := (le_div_iff₀ (Real.rpow_pos_of_pos hp (s + E))).mp hx
  rw [Real.rpow_add hp] at h
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  rw [Real.rpow_neg hp.le, mul_comm ((L x) ^ E)⁻¹]
  exact (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hp E)).mpr (by simpa only [mul_assoc] using h)


end Erdos821.P3Clean
