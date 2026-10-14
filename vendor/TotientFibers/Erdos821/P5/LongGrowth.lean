import Erdos821.P5.Basic

noncomputable section
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem eventual_log_le_rpow_mul (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, 1 ≤ y ∧ Real.log y ≤ c * y ^ r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), (isLittleO_log_rpow_atTop hr).bound hc]
    with y hy hb
  refine ⟨hy, ?_⟩
  simpa only [Real.norm_of_nonneg (Real.log_nonneg hy),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ y) r)] using hb

/-- Positive powers of x absorb arbitrary powers of log x. -/
theorem eventual_log_power_le_power (a A : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ L x ∧ L x ^ A ≤ x ^ a := by
  have hL := Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)
  have hb := (isLittleO_log_rpow_rpow_atTop A ha).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hL, hb] with x hx hL hb
  refine ⟨hx, hL, ?_⟩
  simpa only [L, one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Real.log x) A),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) a)] using hb

theorem eventual_negative_power_le_log_power (a A : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ L x ∧ x ^ (-a) ≤ L x ^ (-A) := by
  filter_upwards [eventual_log_power_le_power a A ha] with x hx
  refine ⟨hx.1, hx.2.1, ?_⟩
  rw [Real.rpow_neg (by linarith : 0 ≤ x), Real.rpow_neg (by linarith : 0 ≤ L x)]
  exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith : 0 < L x) A) hx.2.2

def roughDepth (h₀ : ℕ) (x : ℝ) : ℕ := 2 * (h₀ + ⌈L x ^ (1 / 4 : ℝ)⌉₊)

theorem roughDepth_ge (h₀ : ℕ) (x : ℝ) : h₀ ≤ roughDepth h₀ x := by
  dsimp [roughDepth]
  omega

theorem roughDepth_even (h₀ : ℕ) (x : ℝ) : Even (roughDepth h₀ x) := by
  refine ⟨h₀ + ⌈L x ^ (1 / 4 : ℝ)⌉₊, ?_⟩
  dsimp [roughDepth]
  omega

theorem roughDepth_lower (h₀ : ℕ) (x : ℝ) :
    2 * L x ^ (1 / 4 : ℝ) ≤ (roughDepth h₀ x : ℝ) := by
  have h := Nat.le_ceil (L x ^ (1 / 4 : ℝ))
  dsimp [roughDepth]
  push_cast
  nlinarith [(Nat.cast_nonneg h₀ : 0 ≤ (h₀ : ℝ))]

theorem roughDepth_upper (h₀ : ℕ) (x : ℝ) (hL : 0 ≤ L x) :
    ((4 * roughDepth h₀ x + 2 : ℕ) : ℝ) ≤
      8 * (h₀ : ℝ) + 10 + 8 * L x ^ (1 / 4 : ℝ) := by
  have hceil : (⌈L x ^ (1 / 4 : ℝ)⌉₊ : ℝ) ≤ L x ^ (1 / 4 : ℝ) + 1 := by
    have h := Nat.ceil_le_floor_add_one (L x ^ (1 / 4 : ℝ))
    have hR : (⌈L x ^ (1 / 4 : ℝ)⌉₊ : ℝ) ≤ (⌊L x ^ (1 / 4 : ℝ)⌋₊ : ℝ) + 1 := by
      exact_mod_cast h
    have hf := Nat.floor_le (Real.rpow_nonneg hL (1 / 4 : ℝ))
    linarith
  dsimp [roughDepth]
  push_cast
  linarith

theorem rough_level_exponent_le (h₀ : ℕ) (x : ℝ) (hL : 1 ≤ L x) :
    Real.sqrt (L x) * ((4 * roughDepth h₀ x + 2 : ℕ) : ℝ) ≤
      (8 * (h₀ : ℝ) + 18) * L x ^ (3 / 4 : ℝ) := by
  have hLpos : 0 < L x := by linarith
  have hsqrt : Real.sqrt (L x) ≤ L x ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hprod : Real.sqrt (L x) * L x ^ (1 / 4 : ℝ) = L x ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hLpos]
    norm_num
  have hbound := mul_le_mul_of_nonneg_left (roughDepth_upper h₀ x hLpos.le) (Real.sqrt_nonneg (L x))
  have hs := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 8 * (h₀ : ℝ) + 10 by positivity)
  nlinarith [hprod]

end Erdos821.P5Core
