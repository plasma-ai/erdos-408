import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# The final budget

The totals of `blueprint/one_sided_type_ii.md` §5.4, as a statement about real numbers. With
`L = log x`, `T = ⌈L^{0.76}⌉`, the coefficient mass `exp(L^{0.74})`, and the per-configuration
error of `norm_sum_positions_sub_le`:

* **gap**: `60 σ^T / T!` with `σ ≤ K (L^{1/2} + 3)`, at most `exp(-0.25 L^{0.76} log L)`;
* **discrepancy**: `15 n³ (n_P + 1)^T C₀ p_max^{6(a + T)} m^{-1/5}`, at most
  `exp(C_K L^{0.96}) m^{-1/8}`, where `log m ≥ L^{0.99}`;
* **boundary**: `b (4 n⁻³ + C₀ m^{-1/5})` with `b ≤ n² exp(L^{1/2})` bad cubes, at most
  `exp(2 L^{1/2}) m^{-1/40}`;
* **upper faces**: `(16U + 2V + 2)/(UV) ≤ 20/m`.

The total, times `exp(L^{0.74})`, is eventually below `exp(-L^{0.76})`. The gap is the binding
term. The proofs write every power of `L` as a power of `ℓ = L^{1/100}` (`budget_gap`,
`budget_discrepancy`, `budget_boundary`, `budget_faces` bound each term by `exp(-ℓ^76) / 4`), and
all exponent comparisons follow from `ℓ` exceeding a constant depending on `K` and `C₀`.
-/

noncomputable section

namespace Erdos408.OneSided

open Filter Real

/-- A nonnegative multiple of an exponential is at most a quarter of `exp (-τ)` once the
exponent, shifted by `τ` and by `log (4c + 1)`, is nonpositive. -/
theorem mul_exp_le_exp_neg_div_four {c y τ : ℝ} (hc : 0 ≤ c)
    (h : y + τ + Real.log (4 * c + 1) ≤ 0) : c * Real.exp y ≤ Real.exp (-τ) / 4 := by
  have h1 : (4 * c + 1) * Real.exp y ≤ Real.exp (-τ) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 4 * c + 1), ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have h2 : 0 < Real.exp y := Real.exp_pos y
  nlinarith

/-- **Domination by `ℓ^99`**: once `ℓ ≥ 1` exceeds `40 (A + B)`, the quantity `A + B ℓ^96` is at
most `ℓ^99 / 40`. -/
theorem add_mul_pow_le_pow_div {ℓ A B : ℝ} (hA : 0 ≤ A) (hℓ : 1 ≤ ℓ)
    (h : 40 * (A + B) ≤ ℓ) : A + B * ℓ ^ 96 ≤ ℓ ^ 99 / 40 := by
  have h96 : 1 ≤ ℓ ^ 96 := one_le_pow₀ hℓ
  have h3 : ℓ ≤ ℓ ^ 3 := le_self_pow₀ hℓ (by norm_num)
  have h1 : 40 * (A + B) * ℓ ^ 96 ≤ ℓ ^ 3 * ℓ ^ 96 :=
    mul_le_mul_of_nonneg_right (h.trans h3) (by positivity)
  have h2 : A * 1 ≤ A * ℓ ^ 96 := mul_le_mul_of_nonneg_left h96 hA
  have h4 : ℓ ^ 99 = ℓ ^ 3 * ℓ ^ 96 := by ring
  rw [h4]
  linarith

/-- **The gap term**: with `T = ⌈ℓ^76⌉`, `σ ≤ K (ℓ^50 + 3)` and `ℓ ≥ max(241, 4e⁴K)`, the
coefficient mass times `60 σ^T / T!` is at most `exp(-ℓ^76) / 4`. Here `ℓ = L^{1/100}`. -/
theorem budget_gap (K : ℕ) {ℓ σ : ℝ} (hℓK : 4 * Real.exp 4 * K ≤ ℓ) (hℓ241 : 241 ≤ ℓ)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ K * (ℓ ^ 50 + 3)) :
    Real.exp (ℓ ^ 74) * (15 * (4 * σ ^ ⌈ℓ ^ 76⌉₊ / ((⌈ℓ ^ 76⌉₊).factorial : ℝ))) ≤
      Real.exp (-ℓ ^ 76) / 4 := by
  have hℓ : 1 ≤ ℓ := by linarith
  set τ := ℓ ^ 76 with hτ
  set T := ⌈τ⌉₊ with hT
  have hτT : τ ≤ T := Nat.le_ceil τ
  have hℓτ : ℓ ≤ τ := le_self_pow₀ hℓ (by norm_num)
  have h74 : ℓ ^ 74 ≤ τ := pow_le_pow_right₀ hℓ (by norm_num)
  have hT0 : (0 : ℝ) < T := by linarith
  -- step: `T! ≥ (T / e)^T`, so `σ^T / T! ≤ (e σ / T)^T`
  have h1 : σ ^ T / (T.factorial : ℝ) ≤ (Real.exp 1 * σ / T) ^ T := by
    have hf := Real.pow_div_factorial_le_exp (x := (T : ℝ)) hT0.le T
    calc σ ^ T / (T.factorial : ℝ) = (σ / T) ^ T * ((T : ℝ) ^ T / T.factorial) := by
          rw [div_pow]; field_simp
      _ ≤ (σ / T) ^ T * Real.exp T :=
          mul_le_mul_of_nonneg_left hf (pow_nonneg (div_nonneg hσ0 hT0.le) T)
      _ = (Real.exp 1 * σ / T) ^ T := by
          rw [← Real.exp_one_pow, ← mul_pow]; congr 1; ring
  -- step: `e σ / T ≤ e⁻³`
  have h2 : Real.exp 1 * σ / T ≤ Real.exp (-3) := by
    rw [div_le_iff₀ hT0]
    have hσ4 : σ ≤ K * (4 * ℓ ^ 50) := by
      have : (1 : ℝ) ≤ ℓ ^ 50 := one_le_pow₀ hℓ
      calc σ ≤ K * (ℓ ^ 50 + 3) := hσ
        _ ≤ K * (4 * ℓ ^ 50) := by gcongr; linarith
    have h51 : ℓ * ℓ ^ 50 ≤ τ := by
      rw [← pow_succ']; exact pow_le_pow_right₀ hℓ (by norm_num)
    have he : Real.exp 1 = Real.exp (-3) * Real.exp 4 := by
      rw [← Real.exp_add]; norm_num
    calc Real.exp 1 * σ ≤ Real.exp 1 * (K * (4 * ℓ ^ 50)) := by gcongr
      _ = Real.exp (-3) * ((4 * Real.exp 4 * K) * ℓ ^ 50) := by rw [he]; ring
      _ ≤ Real.exp (-3) * (ℓ * ℓ ^ 50) := by gcongr
      _ ≤ Real.exp (-3) * τ := by gcongr
      _ ≤ Real.exp (-3) * T := by gcongr
  -- step: hence `σ^T / T! ≤ e^{-3T}`
  have h3 : σ ^ T / (T.factorial : ℝ) ≤ Real.exp (T * (-3)) := by
    rw [Real.exp_nat_mul]
    exact h1.trans (pow_le_pow_left₀ (by positivity) h2 T)
  have hlog : Real.log (4 * 60 + 1) ≤ 240 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 * 60 + 1)
    linarith
  calc Real.exp (ℓ ^ 74) * (15 * (4 * σ ^ T / (T.factorial : ℝ))) =
        60 * (Real.exp (ℓ ^ 74) * (σ ^ T / (T.factorial : ℝ))) := by ring
    _ ≤ 60 * (Real.exp (ℓ ^ 74) * Real.exp (T * (-3))) := by gcongr
    _ = 60 * Real.exp (ℓ ^ 74 + T * (-3)) := by rw [Real.exp_add]
    _ ≤ Real.exp (-τ) / 4 := mul_exp_le_exp_neg_div_four (by norm_num) (by linarith)

/-- **The upper faces**: for `m ≥ exp(ℓ^99)` and `U, V ≥ m`, the coefficient mass times
`(16U + 2V + 2)/(UV) ≤ 20/m` is at most `exp(-ℓ^76) / 4`. -/
theorem budget_faces {ℓ m U V : ℝ} (hℓ : 1 ≤ ℓ) (hm : Real.exp (ℓ ^ 99) ≤ m) (hU : m ≤ U)
    (hV : m ≤ V) (h : 2 * ℓ ^ 96 + Real.log 81 ≤ ℓ ^ 99) :
    Real.exp (ℓ ^ 74) * ((16 * U + 2 * V + 2) / (U * V)) ≤ Real.exp (-ℓ ^ 76) / 4 := by
  have hm1 : 1 ≤ m := (Real.one_le_exp (by positivity)).trans hm
  have hU1 : 1 ≤ U := hm1.trans hU
  have hV1 : 1 ≤ V := hm1.trans hV
  -- step: the faces are at most `20 / m ≤ 20 exp(-ℓ^99)`
  have hmexp : 1 / m ≤ Real.exp (-ℓ ^ 99) := by
    rw [Real.exp_neg, ← one_div]; exact one_div_le_one_div_of_le (Real.exp_pos _) hm
  have h1 : (16 * U + 2 * V + 2) / (U * V) ≤ 20 * (1 / m) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ U) (by linarith : (0 : ℝ) ≤ V - m),
      mul_nonneg (by linarith : (0 : ℝ) ≤ V) (by linarith : (0 : ℝ) ≤ U - m),
      mul_nonneg (by linarith : (0 : ℝ) ≤ V) (by linarith : (0 : ℝ) ≤ U - 1)]
  have h74 : ℓ ^ 74 ≤ ℓ ^ 96 := pow_le_pow_right₀ hℓ (by norm_num)
  have h76 : ℓ ^ 76 ≤ ℓ ^ 96 := pow_le_pow_right₀ hℓ (by norm_num)
  calc Real.exp (ℓ ^ 74) * ((16 * U + 2 * V + 2) / (U * V)) ≤
        Real.exp (ℓ ^ 74) * (20 * Real.exp (-ℓ ^ 99)) := by gcongr; exact h1.trans (by gcongr)
    _ = 20 * Real.exp (ℓ ^ 74 + -ℓ ^ 99) := by rw [Real.exp_add]; ring
    _ ≤ Real.exp (-ℓ ^ 76) / 4 :=
        mul_exp_le_exp_neg_div_four (by norm_num) (by norm_num; linarith)

/-- **The discrepancy term**: with `s = m^{1/40} ≥ exp(ℓ^99/40)`, `s ≤ n ≤ 2s`, `μ ≤ s⁻⁸`
(standing for `min(U, V)^{-1/5}`), `n_P ≤ K exp(2ℓ^20)`, `p_max ≤ exp(2ℓ^20)`,
`a ≤ (ℓ^50 + 3) K (ℓ + 1)` and `T ≤ ℓ^76 + 1`, the coefficient mass times
`15 n³ (n_P + 1)^T C₀ p_max^{6(a + T)} μ ≤ 120 C₀ exp((98K + 28) ℓ^96) / s` is at most
`exp(-ℓ^76) / 4`. -/
theorem budget_discrepancy (K : ℕ) {ℓ s n μ C₀ nP pmax : ℝ} (a T : ℕ) (hℓ : 1 ≤ ℓ)
    (hC₀ : 0 ≤ C₀) (hs : Real.exp (ℓ ^ 99 / 40) ≤ s) (hns : n ≤ 2 * s) (hn0 : 0 ≤ n)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ 1 / s ^ 8) (hnP0 : 0 ≤ nP) (hnP : nP ≤ K * Real.exp (2 * ℓ ^ 20))
    (hp1 : 1 ≤ pmax) (hp : pmax ≤ Real.exp (2 * ℓ ^ 20))
    (ha : (a : ℝ) ≤ (ℓ ^ 50 + 3) * (K * (ℓ + 1))) (hT : (T : ℝ) ≤ ℓ ^ 76 + 1)
    (h : (98 * K + 30) * ℓ ^ 96 + Real.log (480 * C₀ + 1) ≤ ℓ ^ 99 / 40) :
    Real.exp (ℓ ^ 74) * (15 * (n ^ 3 * (nP + 1) ^ T * C₀ * pmax ^ (6 * (a + T)) * μ)) ≤
      Real.exp (-ℓ ^ 76) / 4 := by
  have hs1 : 1 ≤ s := (Real.one_le_exp (by positivity)).trans hs
  have hs0 : 0 < s := by linarith
  have hsexp : 1 / s ≤ Real.exp (-(ℓ ^ 99 / 40)) := by
    rw [Real.exp_neg, ← one_div]; exact one_div_le_one_div_of_le (Real.exp_pos _) hs
  -- step: `n³ μ ≤ 8 / s⁵ ≤ 8 exp(-ℓ^99/40)`
  have h1 : n ^ 3 * μ ≤ 8 * Real.exp (-(ℓ ^ 99 / 40)) := by
    have e1 : (2 * s) ^ 3 * (1 / s ^ 8) = 8 / s ^ 5 := by field_simp; ring
    calc n ^ 3 * μ ≤ (2 * s) ^ 3 * (1 / s ^ 8) :=
          mul_le_mul (pow_le_pow_left₀ hn0 hns 3) hμ hμ0 (by positivity)
      _ = 8 / s ^ 5 := e1
      _ ≤ 8 / s := div_le_div_of_nonneg_left (by norm_num) hs0 (le_self_pow₀ hs1 (by norm_num))
      _ = 8 * (1 / s) := by ring
      _ ≤ 8 * Real.exp (-(ℓ ^ 99 / 40)) := by gcongr
  -- step: `n_P + 1 ≤ (K + 1) exp(2ℓ^20) ≤ exp(K + 2ℓ^20)`
  have h2 : nP + 1 ≤ Real.exp (K + 2 * ℓ ^ 20) := by
    have : 1 ≤ Real.exp (2 * ℓ ^ 20) := Real.one_le_exp (by positivity)
    calc nP + 1 ≤ (K + 1) * Real.exp (2 * ℓ ^ 20) := by linarith
      _ ≤ Real.exp K * Real.exp (2 * ℓ ^ 20) := by gcongr; exact Real.add_one_le_exp _
      _ = Real.exp (K + 2 * ℓ ^ 20) := (Real.exp_add _ _).symm
  -- step: the term is at most `120 C₀ exp(ℓ^74 - ℓ^99/40 + T (K + 2ℓ^20) + 12 (a + T) ℓ^20)`
  have h3 : Real.exp (ℓ ^ 74) *
        (15 * (n ^ 3 * (nP + 1) ^ T * C₀ * pmax ^ (6 * (a + T)) * μ)) ≤
      120 * C₀ * Real.exp (ℓ ^ 74 + -(ℓ ^ 99 / 40) + T * (K + 2 * ℓ ^ 20) +
        ((6 * (a + T) : ℕ) : ℝ) * (2 * ℓ ^ 20)) := by
    calc Real.exp (ℓ ^ 74) *
          (15 * (n ^ 3 * (nP + 1) ^ T * C₀ * pmax ^ (6 * (a + T)) * μ)) =
          15 * C₀ * Real.exp (ℓ ^ 74) * ((n ^ 3 * μ) * ((nP + 1) ^ T * pmax ^ (6 * (a + T)))) := by
          ring
      _ ≤ 15 * C₀ * Real.exp (ℓ ^ 74) * ((8 * Real.exp (-(ℓ ^ 99 / 40))) *
          (Real.exp (K + 2 * ℓ ^ 20) ^ T * Real.exp (2 * ℓ ^ 20) ^ (6 * (a + T)))) := by
          gcongr
      _ = 120 * C₀ * Real.exp (ℓ ^ 74 + -(ℓ ^ 99 / 40) + T * (K + 2 * ℓ ^ 20) +
          ((6 * (a + T) : ℕ) : ℝ) * (2 * ℓ ^ 20)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, Real.exp_add, Real.exp_add, Real.exp_add]
          ring
  -- step: the exponent is at most `(98K + 28) ℓ^96 + ℓ^74 - ℓ^99/40`
  have h96 : 1 ≤ ℓ ^ 96 := one_le_pow₀ hℓ
  have h74 : ℓ ^ 74 ≤ ℓ ^ 96 := pow_le_pow_right₀ hℓ (by norm_num)
  have h76 : ℓ ^ 76 ≤ ℓ ^ 96 := pow_le_pow_right₀ hℓ (by norm_num)
  have h761 : 1 ≤ ℓ ^ 76 := one_le_pow₀ hℓ
  have hT2 : (T : ℝ) ≤ 2 * ℓ ^ 76 := by linarith
  have ha8 : (a : ℝ) ≤ 8 * K * ℓ ^ 76 := by
    have h50 : 1 ≤ ℓ ^ 50 := one_le_pow₀ hℓ
    have h51 : ℓ ^ 50 * ℓ ≤ ℓ ^ 76 := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hℓ (by norm_num)
    calc (a : ℝ) ≤ (ℓ ^ 50 + 3) * (K * (ℓ + 1)) := ha
      _ ≤ (4 * ℓ ^ 50) * (K * (2 * ℓ)) := by gcongr <;> linarith
      _ = 8 * K * (ℓ ^ 50 * ℓ) := by ring
      _ ≤ 8 * K * ℓ ^ 76 := by gcongr
  have e96 : ℓ ^ 76 * ℓ ^ 20 = ℓ ^ 96 := by ring
  have hTK : (T : ℝ) * K ≤ 2 * K * ℓ ^ 96 := by
    calc (T : ℝ) * K ≤ (2 * ℓ ^ 76) * K := by gcongr
      _ ≤ (2 * ℓ ^ 96) * K := by gcongr
      _ = 2 * K * ℓ ^ 96 := by ring
  have hTl : (T : ℝ) * ℓ ^ 20 ≤ 2 * ℓ ^ 96 := by
    calc (T : ℝ) * ℓ ^ 20 ≤ (2 * ℓ ^ 76) * ℓ ^ 20 := by gcongr
      _ = 2 * ℓ ^ 96 := by rw [mul_assoc, e96]
  have hal : (a : ℝ) * ℓ ^ 20 ≤ 8 * K * ℓ ^ 96 := by
    calc (a : ℝ) * ℓ ^ 20 ≤ (8 * K * ℓ ^ 76) * ℓ ^ 20 := by gcongr
      _ = 8 * K * ℓ ^ 96 := by rw [mul_assoc, e96]
  have hlog : 4 * (120 * C₀) + 1 = 480 * C₀ + 1 := by ring
  refine h3.trans (mul_exp_le_exp_neg_div_four (by positivity) ?_)
  rw [hlog]
  push_cast
  linarith

/-- **The boundary term**: with `s = m^{1/40} ≥ exp(ℓ^99/40)`, `s ≤ n ≤ 2s`,
`μ ≤ s⁻⁸` (standing for `min(U, V)^{-1/5}`) and `b ≤ n² exp(ℓ^50)` bad cubes, the coefficient mass
times `b (4 n⁻³ + C₀ μ) ≤ (4 + 4C₀) exp(ℓ^50) / s` is at most `exp(-ℓ^76) / 4`. -/
theorem budget_boundary {ℓ s n b μ C₀ : ℝ} (hℓ : 1 ≤ ℓ) (hC₀ : 0 ≤ C₀)
    (hs : Real.exp (ℓ ^ 99 / 40) ≤ s) (hsn : s ≤ n) (hns : n ≤ 2 * s) (hμ0 : 0 ≤ μ)
    (hμ : μ ≤ 1 / s ^ 8) (hb : b ≤ n ^ 2 * Real.exp (ℓ ^ 50))
    (h : 3 * ℓ ^ 96 + Real.log (16 * C₀ + 17) ≤ ℓ ^ 99 / 40) :
    Real.exp (ℓ ^ 74) * (b * (4 / n ^ 3 + C₀ * μ)) ≤ Real.exp (-ℓ ^ 76) / 4 := by
  have hs1 : 1 ≤ s := (Real.one_le_exp (by positivity)).trans hs
  have hs0 : 0 < s := by linarith
  have hn0 : 0 < n := by linarith
  have hsexp : 1 / s ≤ Real.exp (-(ℓ ^ 99 / 40)) := by
    rw [Real.exp_neg, ← one_div]; exact one_div_le_one_div_of_le (Real.exp_pos _) hs
  -- step: `n² (4 n⁻³ + C₀ s⁻⁸) ≤ (4 + 4 C₀) / s`
  have h1 : n ^ 2 * (4 / n ^ 3 + C₀ * (1 / s ^ 8)) ≤ (4 + 4 * C₀) * (1 / s) := by
    have e1 : n ^ 2 * (4 / n ^ 3 + C₀ * (1 / s ^ 8)) = 4 / n + C₀ * (n ^ 2 / s ^ 8) := by
      field_simp
    have h4 : 4 / n ≤ 4 / s := div_le_div_of_nonneg_left (by norm_num) hs0 hsn
    have hn2 : n ^ 2 / s ^ 8 ≤ 4 / s := by
      rw [div_le_div_iff₀ (by positivity) hs0]
      have : n ^ 2 ≤ (2 * s) ^ 2 := pow_le_pow_left₀ hn0.le hns 2
      have : s ^ 3 ≤ s ^ 8 := pow_le_pow_right₀ hs1 (by norm_num)
      nlinarith
    rw [e1]
    calc 4 / n + C₀ * (n ^ 2 / s ^ 8) ≤ 4 / s + C₀ * (4 / s) := by gcongr
      _ = (4 + 4 * C₀) * (1 / s) := by ring
  have h2 : b * (4 / n ^ 3 + C₀ * μ) ≤
      Real.exp (ℓ ^ 50) * ((4 + 4 * C₀) * Real.exp (-(ℓ ^ 99 / 40))) := by
    calc b * (4 / n ^ 3 + C₀ * μ) ≤
          (n ^ 2 * Real.exp (ℓ ^ 50)) * (4 / n ^ 3 + C₀ * (1 / s ^ 8)) := by
          apply mul_le_mul hb _ (by positivity) (by positivity)
          gcongr
      _ = Real.exp (ℓ ^ 50) * (n ^ 2 * (4 / n ^ 3 + C₀ * (1 / s ^ 8))) := by ring
      _ ≤ Real.exp (ℓ ^ 50) * ((4 + 4 * C₀) * Real.exp (-(ℓ ^ 99 / 40))) := by
          exact mul_le_mul_of_nonneg_left (h1.trans (by gcongr)) (by positivity)
  have h74 : ℓ ^ 74 ≤ ℓ ^ 96 := pow_le_pow_right₀ hℓ (by norm_num)
  have h76 : ℓ ^ 76 ≤ ℓ ^ 96 := pow_le_pow_right₀ hℓ (by norm_num)
  have h50 : ℓ ^ 50 ≤ ℓ ^ 96 := pow_le_pow_right₀ hℓ (by norm_num)
  have hlog : 4 * (4 + 4 * C₀) + 1 = 16 * C₀ + 17 := by ring
  calc Real.exp (ℓ ^ 74) * (b * (4 / n ^ 3 + C₀ * μ)) ≤
        Real.exp (ℓ ^ 74) * (Real.exp (ℓ ^ 50) * ((4 + 4 * C₀) * Real.exp (-(ℓ ^ 99 / 40)))) := by
        gcongr
    _ = (4 + 4 * C₀) * Real.exp (ℓ ^ 74 + ℓ ^ 50 + -(ℓ ^ 99 / 40)) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ Real.exp (-ℓ ^ 76) / 4 :=
        mul_exp_le_exp_neg_div_four (by positivity) (by rw [hlog]; linarith)

/-- **The budget of root replacement**: eventually in `x`, for all parameters in the ranges
of §5.4, the coefficient mass times the per-configuration error is below `exp(-L^{0.76})`. -/
theorem eventually_budget (K : ℕ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∀ᶠ x : ℝ in atTop, ∀ (n a : ℕ) (m U V σ nP pmax b : ℝ), 1 ≤ n →
      (n : ℝ) ≤ 2 * m ^ (1 / 40 : ℝ) → m ^ (1 / 40 : ℝ) ≤ n →
      Real.exp (Real.log x ^ (99 / 100 : ℝ)) ≤ m → m ≤ U → m ≤ V →
      0 ≤ σ → σ ≤ K * (Real.log x ^ (1 / 2 : ℝ) + 3) →
      0 ≤ nP → nP ≤ K * Real.exp (2 * Real.log x ^ (1 / 5 : ℝ)) →
      1 ≤ pmax → pmax ≤ Real.exp (2 * Real.log x ^ (1 / 5 : ℝ)) →
      (a : ℝ) ≤ (Real.log x ^ (1 / 2 : ℝ) + 3) * (K * (Real.log x ^ (1 / 100 : ℝ) + 1)) →
      0 ≤ b → b ≤ (n : ℝ) ^ 2 * Real.exp (Real.log x ^ (1 / 2 : ℝ)) →
      Real.exp (Real.log x ^ (74 / 100 : ℝ)) *
          (15 * (4 * σ ^ ⌈Real.log x ^ (76 / 100 : ℝ)⌉₊ /
                (⌈Real.log x ^ (76 / 100 : ℝ)⌉₊).factorial +
              (n : ℝ) ^ 3 * (nP + 1) ^ ⌈Real.log x ^ (76 / 100 : ℝ)⌉₊ * C₀ *
                pmax ^ (6 * (a + ⌈Real.log x ^ (76 / 100 : ℝ)⌉₊)) * min U V ^ (-(1 / 5 : ℝ))) +
            b * (4 / (n : ℝ) ^ 3 + C₀ * min U V ^ (-(1 / 5 : ℝ))) +
            (16 * U + 2 * V + 2) / (U * V)) ≤
        Real.exp (-Real.log x ^ (76 / 100 : ℝ)) := by
  -- step: the threshold for `ℓ = L^{1/100}`
  set A : ℝ := Real.log 81 + Real.log (16 * C₀ + 17) + Real.log (480 * C₀ + 1) with hA
  set M : ℝ := 241 + 4 * Real.exp 4 * K + 40 * (A + (98 * K + 30)) with hM
  have hlog81 : 0 ≤ Real.log 81 := Real.log_nonneg (by norm_num)
  have hlog16 : 0 ≤ Real.log (16 * C₀ + 17) := Real.log_nonneg (by linarith)
  have hlog480 : 0 ≤ Real.log (480 * C₀ + 1) := Real.log_nonneg (by linarith)
  have hA0 : 0 ≤ A := by positivity
  have hlim : Tendsto (fun x => Real.log x ^ (1 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  filter_upwards [hlim.eventually_ge_atTop M, eventually_ge_atTop 1] with x hxM hx1
  intro n a m U V σ nP pmax b hn1 hn2 hn3 hm hmU hmV hσ0 hσ hnP0 hnP hp1 hp ha hb0 hb
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  -- step: rewrite every power of `L` as a power of `ℓ = L^{1/100}`
  set ℓ := Real.log x ^ (1 / 100 : ℝ) with hℓ
  have hpow : ∀ k : ℕ, Real.log x ^ ((k : ℝ) / 100) = ℓ ^ k := fun k => by
    rw [hℓ, ← Real.rpow_mul_natCast hL0]; congr 1; ring
  have h20 : Real.log x ^ (1 / 5 : ℝ) = ℓ ^ 20 := by
    rw [show (1 / 5 : ℝ) = ((20 : ℕ) : ℝ) / 100 by norm_num, hpow]
  have h50 : Real.log x ^ (1 / 2 : ℝ) = ℓ ^ 50 := by
    rw [show (1 / 2 : ℝ) = ((50 : ℕ) : ℝ) / 100 by norm_num, hpow]
  have h74 : Real.log x ^ (74 / 100 : ℝ) = ℓ ^ 74 := by
    rw [show (74 / 100 : ℝ) = ((74 : ℕ) : ℝ) / 100 by norm_num, hpow]
  have h76 : Real.log x ^ (76 / 100 : ℝ) = ℓ ^ 76 := by
    rw [show (76 / 100 : ℝ) = ((76 : ℕ) : ℝ) / 100 by norm_num, hpow]
  have h99 : Real.log x ^ (99 / 100 : ℝ) = ℓ ^ 99 := by
    rw [show (99 / 100 : ℝ) = ((99 : ℕ) : ℝ) / 100 by norm_num, hpow]
  rw [h74, h76]
  rw [h99] at hm
  rw [h50] at hσ hb ha
  rw [h20] at hnP hp
  -- step: the consequences of `ℓ ≥ M`
  have hexp4 : 0 ≤ 4 * Real.exp 4 * K := by positivity
  have hℓ241 : 241 ≤ ℓ := by linarith
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓK : 4 * Real.exp 4 * K ≤ ℓ := by linarith
  have hdom := add_mul_pow_le_pow_div (B := 98 * K + 30) hA0 hℓ1 (by linarith)
  have hKℓ : 0 ≤ (K : ℝ) * ℓ ^ 96 := by positivity
  have hℓ96 : 0 ≤ ℓ ^ 96 := by positivity
  have hℓ99 : 0 ≤ ℓ ^ 99 := by positivity
  -- step: `s = m^{1/40}` and `min(U, V)^{-1/5} ≤ s⁻⁸`
  have hm0 : 0 < m := (Real.exp_pos _).trans_le hm
  have hs : Real.exp (ℓ ^ 99 / 40) ≤ m ^ (1 / 40 : ℝ) := by
    rw [div_eq_mul_one_div, Real.exp_mul]
    exact Real.rpow_le_rpow (Real.exp_pos _).le hm (by norm_num)
  have hμ0 : 0 ≤ min U V ^ (-(1 / 5 : ℝ)) :=
    Real.rpow_nonneg (le_min (hm0.le.trans hmU) (hm0.le.trans hmV)) _
  have hμ : min U V ^ (-(1 / 5 : ℝ)) ≤ 1 / (m ^ (1 / 40 : ℝ)) ^ 8 := by
    calc min U V ^ (-(1 / 5 : ℝ)) ≤ m ^ (-(1 / 5 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hm0 (le_min hmU hmV) (by norm_num)
      _ = 1 / (m ^ (1 / 40 : ℝ)) ^ 8 := by
          rw [Real.rpow_neg hm0.le, ← Real.rpow_mul_natCast hm0.le, one_div]; norm_num
  -- step: the four terms
  have hT : ((⌈ℓ ^ 76⌉₊ : ℕ) : ℝ) ≤ ℓ ^ 76 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hgap := budget_gap K hℓK hℓ241 hσ0 hσ
  have hdisc := budget_discrepancy K a ⌈ℓ ^ 76⌉₊ hℓ1 hC₀ hs hn2 (by positivity) hμ0 hμ hnP0
    hnP hp1 hp ha hT (by linarith)
  have hbd := budget_boundary hℓ1 hC₀ hs hn3 hn2 hμ0 hμ hb (by linarith)
  have hfaces := budget_faces hℓ1 hm hmU hmV (by linarith)
  linarith

end Erdos408.OneSided
