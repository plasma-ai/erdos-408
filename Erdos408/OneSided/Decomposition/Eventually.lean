module

public import Erdos408.OneSided.Bands
public import Erdos408.OneSided.Lift

/-!
# Growth facts for the decomposition

With `L = log x`, eventually in `x`:

* `x^γ ≥ 2` for `γ ≥ L^{-1/100}`;
* `5 e^{2K L^{1/5}} ≤ W = exp(L^{0.24})`, so `5Y < W` whenever a label product exceeds `Y`;
* `(17X)^{3/4} e^{2K L^{1/5}} ≤ X` for `X ≥ x/C_X`, so `Y ≤ X^{1/4}` in PD (3.9);
* `e^{2KJ L^{1/5}} < 2^{⌊L⌋ + 1}`, so every pad product lies in a dyad `k ≤ ⌊L⌋`;
* `c L^E e^{-L^{a₋}} ≤ L^{-D'}`.
-/

@[expose] public section

namespace Erdos408.OneSided

open Filter Finset Real

/-- Eventually `L^c ≥ M`, for `c > 0`. -/
theorem eventually_le_rpow_log {c : ℝ} (hc : 0 < c) (M : ℝ) :
    ∀ᶠ x : ℝ in atTop, M ≤ Real.log x ^ c :=
  ((tendsto_rpow_atTop hc).comp Real.tendsto_log_atTop).eventually_ge_atTop M

/-- Eventually `x^γ ≥ 2` for every `γ ≥ L^{-1/100}`. -/
theorem eventually_two_le_rpow :
    ∀ᶠ x : ℝ in atTop, ∀ γ : ℝ, Real.log x ^ (-(1 / 100 : ℝ)) ≤ γ → 2 ≤ x ^ γ := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop 1]
    with x hL hx γ hγ
  -- `L · L^{-1/100} ≥ L · L⁻¹ = 1`
  have h₁ : (Real.log x)⁻¹ ≤ Real.log x ^ (-(1 / 100 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have h₂ : 1 ≤ Real.log x * Real.log x ^ (-(1 / 100 : ℝ)) := by
    calc (1 : ℝ) = Real.log x * (Real.log x)⁻¹ := (mul_inv_cancel₀ (by linarith)).symm
      _ ≤ _ := by gcongr
  calc (2 : ℝ) ≤ Real.log x * Real.log x ^ (-(1 / 100 : ℝ)) + 1 := by linarith
    _ ≤ Real.exp (Real.log x * Real.log x ^ (-(1 / 100 : ℝ))) := Real.add_one_le_exp _
    _ = x ^ Real.log x ^ (-(1 / 100 : ℝ)) := (Real.rpow_def_of_pos (by linarith) _).symm
    _ ≤ x ^ γ := Real.rpow_le_rpow_of_exponent_le hx hγ

/-- Eventually `5 e^{2K L^{1/5}} ≤ W`. -/
theorem eventually_five_mul_exp_le_roughLevel (K : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      5 * Real.exp (2 * K * Real.log x ^ (1 / 5 : ℝ)) ≤ roughLevel x := by
  filter_upwards [eventually_le_rpow_log (by norm_num : (0 : ℝ) < 1 / 25) (2 * K + 2),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hL
  have h5 := Real.one_le_rpow hL (by norm_num : (0 : ℝ) ≤ 1 / 5)
  -- `L^{0.24} = L^{1/5} L^{1/25} ≥ (2K + 2) L^{1/5}`
  have hsplit : Real.log x ^ (0.24 : ℝ) =
      Real.log x ^ (1 / 5 : ℝ) * Real.log x ^ (1 / 25 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have hlog5 : Real.log 5 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have h5e : 5 * Real.exp (2 * K * Real.log x ^ (1 / 5 : ℝ)) =
      Real.exp (Real.log 5 + 2 * K * Real.log x ^ (1 / 5 : ℝ)) := by
    rw [Real.exp_add, Real.exp_log (by norm_num)]
  unfold roughLevel
  rw [h5e, hsplit]
  refine Real.exp_le_exp.2 ?_
  nlinarith

/-- Eventually `(17X)^{3/4} e^{2K L^{1/5}} ≤ X` for every `X ≥ x/C_X`. -/
theorem eventually_rpow_mul_exp_le {CX : ℝ} (hCX : 1 ≤ CX) (K : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ X : ℝ, x / CX ≤ X →
      (17 * X) ^ (3 / 4 : ℝ) * Real.exp (2 * K * Real.log x ^ (1 / 5 : ℝ)) ≤ X := by
  filter_upwards [eventually_le_rpow_log (by norm_num : (0 : ℝ) < 4 / 5) (16 * K + 1),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * (4 * Real.log 17 + Real.log CX) + 1),
    eventually_gt_atTop CX] with x hx hL hxC X hX
  have hL1 : 1 ≤ Real.log x := by
    have := Real.log_nonneg hCX
    have := Real.log_nonneg (show (1 : ℝ) ≤ 17 by norm_num)
    linarith
  have hC0 : 0 < CX := by linarith
  have hxC0 : 0 < x / CX := div_pos (by linarith) hC0
  have hX0 : 0 < X := hxC0.trans_le hX
  have h5 := Real.one_le_rpow hL1 (by norm_num : (0 : ℝ) ≤ 1 / 5)
  -- `L ≥ 16K L^{1/5}`, from `L = L^{1/5} L^{4/5}`
  have hLsplit : Real.log x = Real.log x ^ (1 / 5 : ℝ) * Real.log x ^ (4 / 5 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have hKL : 16 * K * Real.log x ^ (1 / 5 : ℝ) ≤ Real.log x := by
    have h := mul_le_mul_of_nonneg_left hx (zero_le_one.trans h5)
    calc 16 * K * Real.log x ^ (1 / 5 : ℝ)
        ≤ Real.log x ^ (1 / 5 : ℝ) * Real.log x ^ (4 / 5 : ℝ) := by nlinarith
      _ = Real.log x := hLsplit.symm
  -- `17 e^{2K L^{1/5}} ≤ (x/C_X)^{1/4} ≤ X^{1/4}`
  have hquarter : 17 * Real.exp (2 * K * Real.log x ^ (1 / 5 : ℝ)) ≤ X ^ (1 / 4 : ℝ) := by
    calc 17 * Real.exp (2 * K * Real.log x ^ (1 / 5 : ℝ))
        = Real.exp (Real.log 17 + 2 * K * Real.log x ^ (1 / 5 : ℝ)) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ Real.exp (Real.log (x / CX) * (1 / 4)) := by
          refine Real.exp_le_exp.2 ?_
          rw [Real.log_div (by linarith) hC0.ne']
          nlinarith
      _ = (x / CX) ^ (1 / 4 : ℝ) := (Real.rpow_def_of_pos hxC0 _).symm
      _ ≤ X ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hxC0.le hX (by norm_num)
  have h17 : (17 : ℝ) ^ (3 / 4 : ℝ) ≤ 17 := by
    calc (17 : ℝ) ^ (3 / 4 : ℝ) ≤ 17 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 17 := Real.rpow_one 17
  have hXsplit : X = X ^ (3 / 4 : ℝ) * X ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hX0]
    norm_num
  rw [Real.mul_rpow (by norm_num) hX0.le]
  calc 17 ^ (3 / 4 : ℝ) * X ^ (3 / 4 : ℝ) * Real.exp (2 * K * Real.log x ^ (1 / 5 : ℝ))
      = 17 ^ (3 / 4 : ℝ) * (X ^ (3 / 4 : ℝ) * Real.exp (2 * K * Real.log x ^ (1 / 5 : ℝ))) := by
        ring
    _ ≤ 17 * (X ^ (3 / 4 : ℝ) * Real.exp (2 * K * Real.log x ^ (1 / 5 : ℝ))) :=
        mul_le_mul_of_nonneg_right h17 (by positivity)
    _ = X ^ (3 / 4 : ℝ) * (17 * Real.exp (2 * K * Real.log x ^ (1 / 5 : ℝ))) := by ring
    _ ≤ X ^ (3 / 4 : ℝ) * X ^ (1 / 4 : ℝ) := by
        gcongr
    _ = X := hXsplit.symm

/-- Eventually `e^{2KJ L^{1/5}} < 2^{⌊L⌋ + 1}` with `J = ⌊L^{1/100}⌋`. -/
theorem eventually_exp_lt_two_pow (K : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (2 * K * padCount x * Real.log x ^ (1 / 5 : ℝ)) <
        2 ^ (⌊Real.log x⌋₊ + 1) := by
  filter_upwards [eventually_le_rpow_log (by norm_num : (0 : ℝ) < 79 / 100) (4 * K + 1),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hL
  set L := Real.log x
  have hJ : (padCount x : ℝ) ≤ L ^ (1 / 100 : ℝ) := Nat.floor_le (by positivity)
  -- `2KJ L^{1/5} ≤ 2K L^{21/100} ≤ L/2 < L log 2 < (⌊L⌋ + 1) log 2`
  have hsplit : L = L ^ (21 / 100 : ℝ) * L ^ (79 / 100 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have h21 : L ^ (1 / 100 : ℝ) * L ^ (1 / 5 : ℝ) = L ^ (21 / 100 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have h21' := Real.one_le_rpow hL (by norm_num : (0 : ℝ) ≤ 21 / 100)
  have h15 : 0 ≤ L ^ (1 / 5 : ℝ) := by positivity
  have hle : 2 * K * padCount x * L ^ (1 / 5 : ℝ) ≤ L / 2 := by
    calc 2 * K * padCount x * L ^ (1 / 5 : ℝ) ≤ 2 * K * L ^ (1 / 100 : ℝ) * L ^ (1 / 5 : ℝ) := by
          gcongr
      _ = 2 * K * L ^ (21 / 100 : ℝ) := by rw [mul_assoc, h21]
      _ ≤ L ^ (21 / 100 : ℝ) * L ^ (79 / 100 : ℝ) / 2 := by
          have h := mul_le_mul_of_nonneg_left hx (zero_le_one.trans h21')
          nlinarith
      _ = L / 2 := by rw [← hsplit]
  have hlog2 : 1 / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hfl : L < (⌊L⌋₊ + 1 : ℕ) := by
    push_cast
    exact Nat.lt_floor_add_one L
  calc Real.exp (2 * K * padCount x * L ^ (1 / 5 : ℝ))
      < Real.exp ((⌊L⌋₊ + 1 : ℕ) * Real.log 2) := by
        refine Real.exp_lt_exp.2 ?_
        have : L * Real.log 2 < (⌊L⌋₊ + 1 : ℕ) * Real.log 2 :=
          mul_lt_mul_of_pos_right hfl (by linarith)
        nlinarith
    _ = 2 ^ (⌊L⌋₊ + 1) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- Eventually `c L^E e^{-L^{a}} ≤ L^{-D'}`, for `a > 0`. -/
theorem eventually_mul_rpow_mul_exp_le {a : ℝ} (ha : 0 < a) (c E D' : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      c * Real.log x ^ E * Real.exp (-Real.log x ^ a) ≤ Real.log x ^ (-D') := by
  set s := (E + D' + 1) / a
  have hexp := (tendsto_exp_div_rpow_atTop s).comp
    ((tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop)
  filter_upwards [hexp.eventually_gt_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop c] with x hx hL hLc
  set L := Real.log x
  have hx' : 1 < Real.exp (L ^ a) / (L ^ a) ^ s := hx
  -- `e^{L^a} > (L^a)^s = L^{E + D' + 1}`
  rw [← Real.rpow_mul (by linarith), mul_div_cancel₀ _ ha.ne', one_lt_div (by positivity)] at hx'
  have hL0 : 0 < L := by linarith
  have key : c * L ^ E ≤ L ^ (-D') * Real.exp (L ^ a) := by
    calc c * L ^ E ≤ L * L ^ E := mul_le_mul_of_nonneg_right hLc (by positivity)
      _ = L ^ (-D') * L ^ (E + D' + 1) := by
          rw [← Real.rpow_add hL0, show -D' + (E + D' + 1) = E + 1 by ring,
            Real.rpow_add hL0, Real.rpow_one]
          ring
      _ ≤ L ^ (-D') * Real.exp (L ^ a) := by
          gcongr
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact key

end Erdos408.OneSided
