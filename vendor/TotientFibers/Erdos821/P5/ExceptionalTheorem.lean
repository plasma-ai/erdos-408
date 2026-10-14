import Erdos821.P5.MomentNumerics

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- The geometric small-prime scales permit the moment choice uniformly. -/
theorem eventual_moment_scales (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∀ᶠ x : ℝ in atTop, 2 ≤ x ∧ Real.exp 1 ≤ L x ∧
      Real.log 2 ≤ L x ^ a ∧ L x ^ b + Real.log 2 ≤ L x / 2 := by
  have hL := Real.tendsto_log_atTop.eventually_ge_atTop (max 4 (Real.exp 1))
  have hLa := ((tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop).eventually_ge_atTop
    (Real.log 2)
  have hgap := ((tendsto_rpow_atTop (show 0 < 1 - b by linarith)).comp
    Real.tendsto_log_atTop).eventually_ge_atTop 4
  filter_upwards [eventually_ge_atTop (2 : ℝ), hL, hLa, hgap] with x hx hL hLa hgap
  have hL4 : 4 ≤ L x := (le_max_left _ _).trans hL
  have hLexp : Real.exp 1 ≤ L x := (le_max_right _ _).trans hL
  have hLpos : 0 < L x := by linarith
  have hpowpos : 0 < L x ^ b := Real.rpow_pos_of_pos hLpos b
  have hratio : L x ^ (1 - b) = L x / L x ^ b := by
    rw [Real.rpow_sub hLpos, Real.rpow_one]
  change 4 ≤ L x ^ (1 - b) at hgap
  change Real.log 2 ≤ L x ^ a at hLa
  rw [hratio] at hgap
  have hpow : 4 * L x ^ b ≤ L x := (le_div_iff₀ hpowpos).mp hgap
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  exact ⟨hx, hLexp, hLa, by linarith⟩

end Erdos821.P5Core

namespace Erdos821.Blueprint.Analytic
open Erdos821.P5Core

/-- §4 exceptional unit intervals, proved from the growing prime moment. -/
theorem exceptional_times (a b A : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x in atTop, ∀ (Y P Tmax : ℝ)
      (s : Finset ℕ) (coeff : ℕ → ℂ),
      x ^ (1 / 2 : ℝ) ≤ Y → Y ≤ x ^ (2 : ℕ) → 0 ≤ Tmax → Tmax ≤ Y →
      Real.exp (L x ^ a) / 2 ≤ P → P ≤ Real.exp (L x ^ b) →
      (∀ p ∈ s, p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
      (∀ p ∈ s, ‖coeff p‖ ≤ 1) →
      (occupied s coeff (L x ^ (-A)) Tmax).Finite ∧
      ((occupied s coeff (L x ^ (-A)) Tmax).ncard : ℝ) ≤
        Real.exp (K * (L x ^ b + L x ^ (1 - a) * Real.log (L x))) := by
  classical
  obtain ⟨C, hC, hcount⟩ := occupied_count_bound Erdos821.Classical.blueprint_meanSquares
  refine ⟨|Real.log C| + 30 + 4 * A, by positivity, ?_⟩
  filter_upwards [eventual_moment_scales a b ha hb] with x hx
  intro Y P Tmax s coeff hYlo hYhi hT hTY hPlo hPhi hs hcoeff
  have hxpos : 0 < x := by linarith [hx.1]
  have hx1 : 1 ≤ x := by linarith [hx.1]
  have hYpos : 0 < Y := (Real.rpow_pos_of_pos hxpos (1 / 2 : ℝ)).trans_le hYlo
  have hY1 : 1 ≤ Y := (Real.one_le_rpow hx1 (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans hYlo
  have hYloglo : L x / 2 ≤ Real.log Y := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hxpos (1 / 2 : ℝ)) hYlo
    rw [Real.log_rpow hxpos] at h
    change Real.log x / 2 ≤ Real.log Y
    linarith
  have hYloghi : Real.log Y ≤ 2 * L x := by
    have h := Real.log_le_log hYpos hYhi
    rw [Real.log_pow] at h
    exact h
  have hP1 : 1 ≤ P := by
    have h := (Real.log_le_iff_le_exp (show (0 : ℝ) < 2 by norm_num)).mp hx.2.2.1
    linarith
  have hPpos : 0 < P := by linarith
  have hL1 : 1 ≤ L x := by
    have h : (1 : ℝ) ≤ Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
    exact h.trans hx.2.1
  have hLpos : 0 < L x := by linarith
  let m := ⌊Real.log Y / Real.log (2 * P)⌋₊
  have hchoice := moment_power_choice (L x) Y P a b hL1 ha hab hb hYpos hYloglo hYloghi
    hPpos hPlo hPhi hx.2.2.2
  have hsup : ((s.sup id : ℕ) : ℝ) ≤ 2 * P := by
    have hsup' : s.sup id ≤ ⌊2 * P⌋₊ :=
      Finset.sup_le (fun p hp => Nat.le_floor (hs p hp).2.2)
    have hsup'' : ((s.sup id : ℕ) : ℝ) ≤ (⌊2 * P⌋₊ : ℝ) := by exact_mod_cast hsup'
    exact hsup''.trans (Nat.floor_le (by positivity))
  have hlength : (((s.sup id) ^ m : ℕ) : ℝ) ≤ Y := by
    rw [Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hsup m).trans hchoice.2.1
  have hδ : 0 < L x ^ (-A) := Real.rpow_pos_of_pos hLpos (-A)
  refine ⟨occupied_finite _ _ _ _, ?_⟩
  exact (hcount s coeff m P (L x ^ (-A)) Tmax Y hP1 hδ hT hTY hY1 hlength hs hcoeff).trans
    (moment_numerical_bound (L x) Y P a b A C hx.2.1 ha hab hb hA hC hYpos
      hYloglo hYloghi hPpos hPlo hPhi hx.2.2.2)

end Erdos821.Blueprint.Analytic
