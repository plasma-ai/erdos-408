import Erdos821.S2Empty.BigFactor

noncomputable section
open scoped BigOperators
open Filter Topology
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Empty

open Erdos821.Blueprint.Graph

set_option maxHeartbeats 600000 in
theorem tendsto_log_sq_exp_neg_rpow (F : FixedData) :
    Tendsto (fun x : ℝ => (L x) ^ (2 : ℕ) * Real.exp (-((L x) ^ F.c))) atTop (𝓝 0) := by
  have hc : 0 < F.c := lt_trans F.a_pos (lt_trans F.ab F.bc)
  have hpow : Tendsto (fun x : ℝ => (L x) ^ F.c) atTop atTop :=
    (_root_.tendsto_rpow_atTop hc).comp Real.tendsto_log_atTop
  have hbase := _root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (2 / F.c) 1 one_pos
  have hcomp := hbase.comp hpow
  have heq : (fun x : ℝ => (L x) ^ (2 : ℕ) * Real.exp (-((L x) ^ F.c))) =ᶠ[atTop]
      (fun x : ℝ => ((L x) ^ F.c) ^ (2 / F.c) * Real.exp (-((L x) ^ F.c))) := by
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
      with x hx
    have hp : (L x) ^ (2 : ℕ) = ((L x) ^ F.c) ^ (2 / F.c) := by
      calc
        (L x) ^ (2 : ℕ) = (L x) ^ (2 : ℝ) :=
          (Real.rpow_natCast (L x) 2).symm
        _ = (L x) ^ (F.c * (2 / F.c)) := by
          congr 1
          field_simp [hc.ne']
        _ = ((L x) ^ F.c) ^ (2 / F.c) :=
          Real.rpow_mul hx.le F.c (2 / F.c)
    rw [hp]
  have hcomp' : Tendsto
      (fun x : ℝ => ((L x) ^ F.c) ^ (2 / F.c) * Real.exp (-((L x) ^ F.c)))
      atTop (𝓝 0) := by
    change Tendsto
      (fun x : ℝ => ((L x) ^ F.c) ^ (2 / F.c) * Real.exp (-1 * ((L x) ^ F.c)))
      atTop (𝓝 0) at hcomp
    simpa [neg_one_mul] using hcomp
  exact hcomp'.congr' heq.symm

set_option maxHeartbeats 600000 in
theorem eventually_big_deficit_budget (F : FixedData) (M : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ L x ∧ 0 ≤ T x ∧ T x ≤ L x ∧
      (N x : ℝ) + 1 ≤ 5 * L x ∧
      5 * (L x) ^ (2 : ℕ) * Real.exp (-((L x) ^ F.c)) < 1 / 2 ∧
      (M : ℝ) * F.C₀ * T x * ((N x : ℝ) + 1) / Real.exp ((L x) ^ F.c) ≤ 1 / 2 := by
  have hc : 0 < F.c := lt_trans F.a_pos (lt_trans F.ab F.bc)
  have hdecay := tendsto_log_sq_exp_neg_rpow F
  have hscaled := hdecay.const_mul (5 * (M : ℝ) * F.C₀)
  have hsmall : ∀ᶠ x : ℝ in atTop,
      (5 * (M : ℝ) * F.C₀) * ((L x) ^ (2 : ℕ) * Real.exp (-((L x) ^ F.c))) < 1 / 2 :=
    hscaled.eventually (Iio_mem_nhds (by simp))
  have hsmallBase : ∀ᶠ x : ℝ in atTop,
      5 * (L x) ^ (2 : ℕ) * Real.exp (-((L x) ^ F.c)) < 1 / 2 := by
    simpa [mul_assoc] using (hdecay.const_mul 5).eventually
      (Iio_mem_nhds (by norm_num : (5 : ℝ) * 0 < 1 / 2))
  have hLlarge : ∀ᶠ x : ℝ in atTop, 1 ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hsmall, hsmallBase, hLlarge] with x hsmall hsmallBase hL
  have hLpos : 0 < L x := by linarith
  have hTnonneg : 0 ≤ T x := Real.log_nonneg hL
  have hTle : T x ≤ L x := by
    dsimp [T]
    have hh := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hceil : (R x : ℝ) ≤ (L x) ^ ((52 : ℝ) / 100) + 1 := by
    dsimp [R]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hpowle : (L x) ^ ((52 : ℝ) / 100) ≤ L x := by
    calc
      _ ≤ (L x) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ = L x := by rw [Real.rpow_one]
  have hN : (N x : ℝ) + 1 ≤ 5 * L x := by
    rw [N]
    push_cast
    nlinarith [hceil, hpowle]
  have hTN : T x * ((N x : ℝ) + 1) ≤ 5 * (L x) ^ (2 : ℕ) := by
    calc
      _ ≤ L x * ((N x : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hTle (by positivity)
      _ ≤ L x * (5 * L x) :=
        mul_le_mul_of_nonneg_left hN hLpos.le
      _ = 5 * (L x) ^ (2 : ℕ) := by ring
  have hnum : (M : ℝ) * F.C₀ * T x * ((N x : ℝ) + 1) ≤
      (5 * (M : ℝ) * F.C₀) * (L x) ^ (2 : ℕ) := by
    calc
      _ = ((M : ℝ) * F.C₀) * (T x * ((N x : ℝ) + 1)) := by ring
      _ ≤ ((M : ℝ) * F.C₀) * (5 * (L x) ^ 2) :=
        mul_le_mul_of_nonneg_left hTN (mul_nonneg (Nat.cast_nonneg _) F.C₀_pos.le)
      _ = _ := by ring
  refine ⟨hL, hTnonneg, hTle, hN, hsmallBase, ?_⟩
  calc
    _ ≤ ((5 * (M : ℝ) * F.C₀) * (L x) ^ (2 : ℕ)) / Real.exp ((L x) ^ F.c) :=
      div_le_div_of_nonneg_right hnum (Real.exp_pos _).le
    _ = (5 * (M : ℝ) * F.C₀) * ((L x) ^ (2 : ℕ) * Real.exp (-((L x) ^ F.c))) := by
      rw [div_eq_mul_inv, Real.exp_neg]
      push_cast
      ring_nf
    _ ≤ 1 / 2 := le_of_lt hsmall


end Erdos821.S2Empty
