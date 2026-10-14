import Mathlib
import Erdos821.Blueprint.Graph
import Erdos821.Blueprint.Analytic

open scoped BigOperators

namespace Erdos821.Blueprint.Graph

/-- §2 ghost-joint-integral normalization: 1/(k+t)! · C(k+t,t) = 1/k! · 1/t!. -/
theorem ghost_factorial (k t : ℕ) :
    (((k + t).factorial : ℝ)⁻¹ * ((k + t).choose t : ℝ)) =
      (k.factorial : ℝ)⁻¹ * (t.factorial : ℝ)⁻¹ := by
  have hle : t ≤ k + t := Nat.le_add_left t k
  have h := Nat.choose_mul_factorial_mul_factorial hle
  have hsub : k + t - t = k := Nat.add_sub_cancel k t
  rw [hsub] at h
  have hR : ((k + t).choose t : ℝ) * (t.factorial : ℝ) * (k.factorial : ℝ)
      = ((k + t).factorial : ℝ) := by
    exact_mod_cast h
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have ht : (t.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero t)
  have hkt : ((k + t).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + t))
  field_simp
  linear_combination hR

example : @Erdos821.Blueprint.Graph.ghost_factorial =
    @Erdos821.Blueprint.Graph.ghost_factorial := rfl

/-- §2 edge-factorial-reversal, both retrieval counts. -/
theorem edge_factorial (j a b : ℕ) (ha : a ≤ j) :
    (j.descFactorial a : ℝ) / (j.factorial : ℝ) = ((j - a).factorial : ℝ)⁻¹ ∧
      (((j - a + b).descFactorial b : ℝ) / ((j - a + b).factorial : ℝ)) =
        ((j - a).factorial : ℝ)⁻¹ := by
  have h1 := Nat.factorial_mul_descFactorial ha
  have h1R : ((j - a).factorial : ℝ) * (j.descFactorial a : ℝ) = (j.factorial : ℝ) := by
    exact_mod_cast h1
  have hj : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hja : ((j - a).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j - a))
  have hb : b ≤ j - a + b := Nat.le_add_left b (j - a)
  have h2 := Nat.factorial_mul_descFactorial hb
  have hsub : j - a + b - b = j - a := Nat.add_sub_cancel (j - a) b
  rw [hsub] at h2
  have h2R : ((j - a).factorial : ℝ) * ((j - a + b).descFactorial b : ℝ)
      = ((j - a + b).factorial : ℝ) := by
    exact_mod_cast h2
  have hjb : ((j - a + b).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j - a + b))
  constructor
  · rw [div_eq_iff hj]
    field_simp
    linear_combination h1R
  · rw [div_eq_iff hjb]
    field_simp
    linear_combination h2R

example : @Erdos821.Blueprint.Graph.edge_factorial =
    @Erdos821.Blueprint.Graph.edge_factorial := rfl

/-- §2 lifespan weights: both birth conventions pay V⁻ʳ/(p·b). -/
theorem lifespan_weight (V p b : ℝ) (r : ℕ) (hr : 0 < r)
    (hV : V ≠ 0) (hp : p ≠ 0) (hb : b ≠ 0) :
    (V * p * b)⁻¹ * (V⁻¹) ^ (r - 1) = V ^ (-(r : ℤ)) / (p * b) ∧
      (p * b)⁻¹ * (V⁻¹) ^ r = V ^ (-(r : ℤ)) / (p * b) := by
  have _hV : V ≠ 0 := hV
  have _hpb : p * b ≠ 0 := mul_ne_zero hp hb
  have hr1 : r - 1 + 1 = r := Nat.sub_add_cancel hr
  have hVinv_r : (V⁻¹) ^ r = V ^ (-(r : ℤ)) := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  have hsplit : (V * p * b)⁻¹ = V⁻¹ * (p * b)⁻¹ := by
    rw [show V * p * b = V * (p * b) from by ring, mul_inv_rev, mul_comm]
  have hcomb : V⁻¹ * (V⁻¹) ^ (r - 1) = (V⁻¹) ^ r := by
    conv_lhs => rw [mul_comm]
    rw [← pow_succ, hr1]
  constructor
  · rw [hsplit, div_eq_mul_inv, ← hVinv_r]
    calc V⁻¹ * (p * b)⁻¹ * (V⁻¹) ^ (r - 1)
        = (V⁻¹ * (V⁻¹) ^ (r - 1)) * (p * b)⁻¹ := by ring
      _ = (V⁻¹) ^ r * (p * b)⁻¹ := by rw [hcomb]
  · rw [div_eq_mul_inv, ← hVinv_r, mul_comm]

example : @Erdos821.Blueprint.Graph.lifespan_weight =
    @Erdos821.Blueprint.Graph.lifespan_weight := rfl

/-- §2 tilted reciprocal-prime law is uniformly close to the original. -/
theorem tilted_density_bound (p e : ℝ) (hp : 0 < p) (he : 0 ≤ e) (he' : 2 * e ≤ p) :
    0 < 1 - e / p ∧ 1 ≤ (1 - e / p)⁻¹ ∧ (1 - e / p)⁻¹ ≤ 1 + 2 * e / p := by
  have hep_nonneg : 0 ≤ e / p := div_nonneg he (le_of_lt hp)
  have hep_le : e / p ≤ 1 / 2 := by
    rw [div_le_iff₀ hp]
    linarith
  have h1 : 0 < 1 - e / p := by linarith
  refine ⟨h1, ?_, ?_⟩
  · rw [one_le_inv_iff₀]
    exact ⟨h1, by linarith⟩
  · rw [inv_le_iff_one_le_mul₀ h1]
    have hexpand : (1 + 2 * e / p) * (1 - e / p) = 1 + (e / p) * (1 - 2 * (e / p)) := by
      ring
    have h2t : 0 ≤ (e / p) * (1 - 2 * (e / p)) := by
      apply mul_nonneg hep_nonneg
      linarith
    rw [hexpand]
    linarith

example : @Erdos821.Blueprint.Graph.tilted_density_bound =
    @Erdos821.Blueprint.Graph.tilted_density_bound := rfl

/-- §2 compatibility of a prime active at both endpoints. -/
theorem active_both_divides_step (p : ℕ) (n k D : ℤ) (hp : Nat.Prime p)
    (hn : (p : ℤ) ∣ n) (hn' : (p : ℤ) ∣ n + k * D) (hk : ¬ (p : ℤ) ∣ k) :
    (p : ℤ) ∣ D := by
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hsub : (p : ℤ) ∣ (n + k * D) - n := dvd_sub hn' hn
  have heq : (n + k * D) - n = k * D := by ring
  rw [heq] at hsub
  rw [Prime.dvd_mul hprime] at hsub
  rcases hsub with h | h
  · exact absurd h hk
  · exact h

example : @Erdos821.Blueprint.Graph.active_both_divides_step =
    @Erdos821.Blueprint.Graph.active_both_divides_step := rfl

end Erdos821.Blueprint.Graph
