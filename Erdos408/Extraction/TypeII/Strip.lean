module

public import Erdos408.Extraction.TypeII.Single

/-!
# Stripping the candidate primes (E5)

Replace the unstripped proxy `a_j^0(m) = [m > x^γ] g(m)/(D log m)` by the stripped proxy
`a_j(m) = [m̄ > x^γ] g(m)/(D log m̄)`. The difference `δ(m) = a_j^0(m) - a_j(m)` vanishes for
`m ≤ x^γ`, is at most `g(m)/(D γ L)` on the threshold strip `x^γ < m ≤ x^γ e^{L^{0.9}}`, and is at
most `(g(m)/D) log(m/m̄) / (γ² L^{1.9})` above it. Summing against `1/m`, the strip costs
`O(L^{-0.1}/γ)` by the rough-count bound on dyadic ranges, and the rest
`O(L^{0.45} log Y / (γ² L^{1.9}))` by the candidate logarithm bound. The other factors of the
telescoping step are counted by `∑_{m ≤ w} g(m)/(DγL) ≤ c w/(γL)`, which supplies the
saving `1/L`.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real

section Pointwise

variable {x γ : ℝ} {j : ℕ}

/-- Both proxies vanish below `x^γ`. -/
theorem proxies_eq_zero (hx : 1 < x) (hγ : 0 ≤ γ) {m : ℕ} (hm : (m : ℝ) ≤ x ^ γ) :
    unstrippedProxy x γ j m = 0 ∧ strippedProxy x γ j m = 0 := by
  constructor
  · unfold unstrippedProxy; rw [ite_eq_right (not_lt.2 hm)]
  · unfold strippedProxy
    rw [ite_eq_right]
    rcases eq_or_ne m 0 with rfl | hm0
    · simp only [candidateStrip, stripPrimes, Nat.primeFactors_zero, filter_empty, prod_empty,
        Nat.cast_one, not_lt]
      exact Real.one_le_rpow hx.le hγ
    · exact not_lt.2 ((show ((candidateStrip x m : ℕ) : ℝ) ≤ m by
        exact_mod_cast stripPrimes_le _ hm0).trans hm)

/-- `|a_j^0 - a_j| ≤ g/(D γ L)`. -/
theorem abs_proxy_sub_le (hx : 1 < x) (hL : 1 ≤ Real.log x) (hγ : 0 < γ) (hj : 1 ≤ j) (m : ℕ) :
    |unstrippedProxy x γ j m - strippedProxy x γ j m| ≤
      dampedWeight x j m / (dampedDensity x j * (γ * Real.log x)) := by
  obtain ⟨h0, h1⟩ := unstrippedProxy_le hx hL hγ hj m
  obtain ⟨h0', h1'⟩ := strippedProxy_le hx hL hγ hj m
  have hD := dampedDensity_pos hL hj
  have hite : (if x ^ γ < m then dampedWeight x j m else 0) ≤ dampedWeight x j m := by
    have := dampedWeight_nonneg x j m; split_ifs <;> linarith
  have hb : (if x ^ γ < m then dampedWeight x j m else 0) /
      (dampedDensity x j * (γ * Real.log x)) ≤
      dampedWeight x j m / (dampedDensity x j * (γ * Real.log x)) :=
    div_le_div_of_nonneg_right hite (by positivity)
  rw [abs_le]
  constructor <;> linarith

/-- Above the threshold strip, `|δ(m)| ≤ (g(m)/D) log(m/m̄) / (γ² L^{1.9})`. -/
theorem abs_proxy_sub_le_log (hx : 1 < x) (hL : 1 ≤ Real.log x) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hj : 1 ≤ j) {m : ℕ} (hm : γ * Real.log x + Real.log x ^ (9 / 10 : ℝ) < Real.log m) :
    |unstrippedProxy x γ j m - strippedProxy x γ j m| ≤
      dampedWeight x j m / dampedDensity x j *
        (Real.log m - Real.log (candidateStrip x m)) /
          (γ ^ 2 * Real.log x ^ (19 / 10 : ℝ)) := by
  have hD := dampedDensity_pos hL hj
  have hg := dampedWeight_nonneg x j m
  have hL0 : 0 < Real.log x := by linarith
  have hγL : 0 < γ * Real.log x := by positivity
  have hL9 : 0 < Real.log x ^ (9 / 10 : ℝ) := by positivity
  have hm0 : m ≠ 0 := by
    intro h; rw [h, Nat.cast_zero, Real.log_zero] at hm; linarith
  have hlogm : γ * Real.log x < Real.log m := by linarith
  have hxm : x ^ γ < m := by
    rw [← Real.exp_log (show (0 : ℝ) < m by positivity), Real.rpow_def_of_pos (by linarith)]
    exact Real.exp_lt_exp.2 (by linarith)
  set mb := candidateStrip x m with hmb
  have hmb1 : (1 : ℝ) ≤ mb := by
    have := stripPrimes_ne_zero (candidatePrimes x) m
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hmbm : (mb : ℝ) ≤ m := by exact_mod_cast stripPrimes_le _ hm0
  have hlogmb : Real.log mb ≤ Real.log m := Real.log_le_log (by linarith) hmbm
  have hlogmb0 : 0 ≤ Real.log mb := Real.log_nonneg hmb1
  have hL19 : Real.log x ^ (19 / 10 : ℝ) ≤ Real.log x ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hden : γ ^ 2 * Real.log x ^ (19 / 10 : ℝ) ≤ (γ * Real.log x) ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hL19 (by positivity)
  have hden0 : 0 < γ ^ 2 * Real.log x ^ (19 / 10 : ℝ) := by positivity
  have hu : unstrippedProxy x γ j m = dampedWeight x j m / (dampedDensity x j * Real.log m) := by
    unfold unstrippedProxy; rw [ite_eq_left hxm]
  rw [hu]
  unfold strippedProxy
  rw [← hmb]
  split_ifs with hs
  · -- both proxies are present: compare `1/log m` and `1/log m̄`
    have hlogmb' : γ * Real.log x < Real.log mb := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_lt_log (by positivity) hs
    have hpos : 0 < Real.log mb := by linarith
    have heq : dampedWeight x j m / (dampedDensity x j * Real.log m) -
        dampedWeight x j m / (dampedDensity x j * Real.log mb) =
        -(dampedWeight x j m / dampedDensity x j * (Real.log m - Real.log mb) /
          (Real.log m * Real.log mb)) := by
      have hlogm0 : Real.log m ≠ 0 := by linarith
      field_simp
      ring
    rw [heq, abs_neg, abs_of_nonneg (by
      have : 0 ≤ Real.log m - Real.log mb := by linarith
      positivity)]
    apply div_le_div_of_nonneg_left (by
      have : 0 ≤ Real.log m - Real.log mb := by linarith
      positivity) hden0
    calc γ ^ 2 * Real.log x ^ (19 / 10 : ℝ) ≤ (γ * Real.log x) ^ 2 := hden
      _ = γ * Real.log x * (γ * Real.log x) := sq _
      _ ≤ Real.log m * Real.log mb := mul_le_mul hlogm.le hlogmb'.le hγL.le (by linarith)
  · -- only the unstripped proxy is present: `log(m/m̄) ≥ L^{0.9}`
    push Not at hs
    have hlogmb' : Real.log mb ≤ γ * Real.log x := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (by linarith) hs
    have hgap : Real.log x ^ (9 / 10 : ℝ) ≤ Real.log m - Real.log mb := by linarith
    rw [sub_zero, abs_of_nonneg (by positivity)]
    have hgD : 0 ≤ dampedWeight x j m / dampedDensity x j := by positivity
    have hlogm0 : 0 < Real.log m := by linarith
    have hL19 : Real.log x ^ (19 / 10 : ℝ) = Real.log x * Real.log x ^ (9 / 10 : ℝ) := by
      rw [← Real.rpow_one_add' hL0.le (by norm_num)]; norm_num
    calc dampedWeight x j m / (dampedDensity x j * Real.log m)
        = dampedWeight x j m / dampedDensity x j / Real.log m := by rw [div_div]
      _ ≤ dampedWeight x j m / dampedDensity x j / (γ * Real.log x) :=
          div_le_div_of_nonneg_left hgD hγL hlogm.le
      _ ≤ dampedWeight x j m / dampedDensity x j * Real.log x ^ (9 / 10 : ℝ) /
            (γ ^ 2 * Real.log x ^ (19 / 10 : ℝ)) := by
          rw [hL19, div_le_div_iff₀ hγL (by positivity)]
          have : γ ^ 2 ≤ γ := by nlinarith
          have h1 : dampedWeight x j m / dampedDensity x j * (γ ^ 2 *
              (Real.log x * Real.log x ^ (9 / 10 : ℝ))) ≤
              dampedWeight x j m / dampedDensity x j * (γ *
              (Real.log x * Real.log x ^ (9 / 10 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (by positivity)) hgD
          nlinarith
      _ ≤ _ := by gcongr

end Pointwise

/-! ### Counting the proxy weights -/

section Count

variable {x γ : ℝ} {j : ℕ}

/-- The envelope `W(m) = [x^γ < m] g(m) / (D γ L)` of both proxies. -/
noncomputable def proxyEnv (x γ : ℝ) (j m : ℕ) : ℝ :=
  (if x ^ γ < m then dampedWeight x j m else 0) / (dampedDensity x j * (γ * Real.log x))

theorem proxyEnv_nonneg (hL : 1 ≤ Real.log x) (hγ : 0 < γ) (hj : 1 ≤ j) (m : ℕ) :
    0 ≤ proxyEnv x γ j m := by
  have := dampedDensity_pos hL hj
  have := dampedWeight_nonneg x j m
  unfold proxyEnv
  split_ifs <;> positivity

theorem proxyEnv_le (hL : 1 ≤ Real.log x) (hγ : 0 < γ) (hj : 1 ≤ j) (m : ℕ) :
    proxyEnv x γ j m ≤ dampedWeight x j m / (dampedDensity x j * (γ * Real.log x)) := by
  have := dampedDensity_pos hL hj
  have := dampedWeight_nonneg x j m
  unfold proxyEnv
  exact div_le_div_of_nonneg_right (by split_ifs <;> linarith) (by positivity)

/-- `∑_{m ≤ N} W(m)/m ≤ ∏_{Y < p ≤ N} (1 - 1/p)⁻¹`. -/
theorem sum_proxyEnv_div_le (hL : 1 ≤ Real.log x) (hγ : 0 < γ) (hj : 1 ≤ j)
    (hY : 1 ≤ (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x))
    (hYP : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x) {N : ℕ}
    (hYN : proxyCutoff x ≤ N) {w : ℕ → ℝ} (hw : ∀ m, w m ≤ proxyEnv x γ j m) :
    ∑ m ∈ Icc 1 N, w m * cmul (fun p => (p : ℝ)⁻¹) m ≤
      ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹ := by
  obtain ⟨hPi, hPiD⟩ := prod_le_dampedDensity hL hj
  have hD := dampedDensity_pos hL hj
  have hγL : 0 < γ * Real.log x := by positivity
  set ν := (dampedDensity x j * (γ * Real.log x))⁻¹ with hν
  have hterm : ∀ m ∈ Icc 1 N, w m * cmul (fun p => (p : ℝ)⁻¹) m ≤
      ν * (dampedWeight x j m / m) := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (mem_Icc.1 hm).1; omega
    rw [cmul_inv hm0]
    calc w m * (m : ℝ)⁻¹ ≤ dampedWeight x j m / (dampedDensity x j * (γ * Real.log x)) *
          (m : ℝ)⁻¹ := by
          gcongr
          exact (hw m).trans (proxyEnv_le hL hγ hj m)
      _ = ν * (dampedWeight x j m / m) := by rw [hν]; ring
  have hsum := sum_dampedWeight_div_le hL hYP hYN hj
  have hPP : 0 ≤ ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹ :=
    prod_nonneg fun p hp => by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesIoc.1 hp).1.two_le
      rw [inv_nonneg, sub_nonneg, div_le_one (by linarith)]; linarith
  have hPc : 0 < ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ := by
    have := hD; unfold dampedDensity at this
    exact pos_of_mul_pos_right this hPi.le
  calc ∑ m ∈ Icc 1 N, w m * cmul (fun p => (p : ℝ)⁻¹) m
      ≤ ∑ m ∈ Icc 1 N, ν * (dampedWeight x j m / m) := sum_le_sum hterm
    _ = ν * ∑ m ∈ Icc 1 N, dampedWeight x j m / m := (mul_sum _ _ _).symm
    _ ≤ ν * ((∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹) *
          ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹) /
          ((∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x)) := by
        have key : ∀ a b c d : ℝ, b ≠ 0 → (a * b * c)⁻¹ * (b * d) = d / (a * c) := by
          intro a b c d hb
          rw [div_eq_mul_inv, mul_inv, mul_inv, mul_inv]
          field_simp
        rw [hν, dampedDensity]
        exact key _ _ _ _ hPc.ne'
    _ ≤ ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹ := div_le_self hPP hY

/-- The count `∑_{m ≤ w} W(m) ≤ c w / (γ L)`, from the rough-count bound for `g_j`. -/
theorem sum_proxyEnv_count_le {A₁ c₃ θ : ℝ} (hL : 1 ≤ Real.log x) (hγ : 0 < γ)
    (hj : 1 ≤ j) (hA₁ : 0 < A₁) (hc₃ : 0 < c₃) (hθ : 0 < θ)
    (hlogY : 0 < Real.log (proxyCutoff x))
    (hPiY : c₃ / Real.log (proxyCutoff x) ≤ ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p))
    (hG : ∀ W : ℕ, ∑ m ∈ Icc 1 W, dampedWeight x j m ≤
      A₁ * W / Real.log (proxyCutoff x) * ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ +
        (W : ℝ) ^ θ * ∏ p ∈ candidatePrimes x, (1 - (p : ℝ) ^ (-θ))⁻¹)
    (hsmall : ∀ w : ℝ, x ^ γ ≤ w → w ^ θ * ∏ p ∈ candidatePrimes x, (1 - (p : ℝ) ^ (-θ))⁻¹ ≤
      c₃ / Real.log (proxyCutoff x) * w)
    (N : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    ∑ m ∈ Icc 1 N, (if (m : ℝ) ≤ w then proxyEnv x γ j m else 0) ≤
      (A₁ / c₃ + 1) / (γ * Real.log x) * w := by
  obtain ⟨hPi, hPiD⟩ := prod_le_dampedDensity hL hj
  have hD := dampedDensity_pos hL hj
  have hγL : 0 < γ * Real.log x := by positivity
  have hEnv0 := proxyEnv_nonneg hL hγ hj
  by_cases hwγ : w < x ^ γ
  · -- below `x^γ` the envelope vanishes
    refine le_trans (le_of_eq (sum_eq_zero fun m _ => ?_)) (by positivity)
    split_ifs with h
    · unfold proxyEnv; rw [ite_eq_right (by linarith), zero_div]
    · rfl
  push Not at hwγ
  set W := ⌊w⌋₊
  have hWw : (W : ℝ) ≤ w := Nat.floor_le hw
  have hsub : ∑ m ∈ Icc 1 N, (if (m : ℝ) ≤ w then proxyEnv x γ j m else 0) ≤
      ∑ m ∈ Icc 1 W, dampedWeight x j m / (dampedDensity x j * (γ * Real.log x)) := by
    rw [← sum_filter]
    refine (sum_le_sum fun m _ => proxyEnv_le hL hγ hj m).trans
      (sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) fun m _ _ => by
        have := dampedWeight_nonneg x j m; positivity)
    obtain ⟨hmI, hmw⟩ := mem_filter.1 hm
    exact mem_Icc.2 ⟨(mem_Icc.1 hmI).1, Nat.le_floor hmw⟩
  refine hsub.trans ?_
  rw [← sum_div, div_le_iff₀ (by positivity)]
  refine (hG W).trans ?_
  have hPc : 0 < ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ := by
    have := hD; unfold dampedDensity at this
    exact pos_of_mul_pos_right this hPi.le
  have hDeq : dampedDensity x j = (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) *
      ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ := rfl
  -- the main term
  have h1 : A₁ * W / Real.log (proxyCutoff x) * ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ ≤
      A₁ / c₃ * w * dampedDensity x j := by
    rw [hDeq]
    have : A₁ * W / Real.log (proxyCutoff x) ≤ A₁ / c₃ * w *
        (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) := by
      calc A₁ * W / Real.log (proxyCutoff x) = A₁ / c₃ * W * (c₃ / Real.log (proxyCutoff x)) := by
            field_simp
        _ ≤ A₁ / c₃ * w * (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) := by
            gcongr
    calc A₁ * W / Real.log (proxyCutoff x) * ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹
        ≤ A₁ / c₃ * w * (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) *
            ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ :=
          mul_le_mul_of_nonneg_right this hPc.le
      _ = _ := by ring
  -- the `P`-numbers
  have h2 : (W : ℝ) ^ θ * ∏ p ∈ candidatePrimes x, (1 - (p : ℝ) ^ (-θ))⁻¹ ≤
      w * dampedDensity x j := by
    have hWθ : (W : ℝ) ^ θ ≤ w ^ θ := Real.rpow_le_rpow (Nat.cast_nonneg _) hWw hθ.le
    have hPiθ : 0 ≤ ∏ p ∈ candidatePrimes x, (1 - (p : ℝ) ^ (-θ))⁻¹ :=
      prod_nonneg fun p hp => by
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_candidatePrimes hL hp).1.two_le
        have : (p : ℝ) ^ (-θ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
        rw [inv_nonneg]; linarith
    calc (W : ℝ) ^ θ * ∏ p ∈ candidatePrimes x, (1 - (p : ℝ) ^ (-θ))⁻¹
        ≤ w ^ θ * ∏ p ∈ candidatePrimes x, (1 - (p : ℝ) ^ (-θ))⁻¹ :=
          mul_le_mul_of_nonneg_right hWθ hPiθ
      _ ≤ c₃ / Real.log (proxyCutoff x) * w := hsmall w hwγ
      _ ≤ (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * w :=
          mul_le_mul_of_nonneg_right hPiY hw
      _ ≤ dampedDensity x j * w := mul_le_mul_of_nonneg_right hPiD hw
      _ = w * dampedDensity x j := mul_comm _ _
  calc _ ≤ A₁ / c₃ * w * dampedDensity x j + w * dampedDensity x j := add_le_add h1 h2
    _ = (A₁ / c₃ + 1) / (γ * Real.log x) * w * (dampedDensity x j * (γ * Real.log x)) := by
        field_simp

end Count

/-! ### The log density of `δ` -/

/-- A dyadic range: if `∑_{m ≤ w} W(m) ≤ c w`, then `∑_{y < m ≤ 2^K y} W(m)/m ≤ 2 c K`. -/
theorem sum_dyadic_le {N K' : ℕ} {y cW : ℝ} (hy : 0 < y) {W : ℕ → ℝ}
    (hW0 : ∀ m, 0 ≤ W m)
    (hcount : ∀ w : ℝ, 0 ≤ w → ∑ m ∈ Icc 1 N, (if (m : ℝ) ≤ w then W m else 0) ≤ cW * w) :
    ∑ m ∈ Icc 1 N, (if y < m ∧ (m : ℝ) ≤ 2 ^ K' * y then W m / m else 0) ≤ 2 * cW * K' := by
  -- each `m` in the range lies in some dyadic cell
  have hpt : ∀ m ∈ Icc 1 N, (if y < m ∧ (m : ℝ) ≤ 2 ^ K' * y then W m / m else 0) ≤
      ∑ k ∈ range K', (if (m : ℝ) ≤ 2 ^ (k + 1) * y then W m else 0) / (2 ^ k * y) := by
    intro m _
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      have hex : ∃ k, (m : ℝ) ≤ 2 ^ (k + 1) * y := ⟨K', by
        calc (m : ℝ) ≤ 2 ^ K' * y := h2
          _ ≤ 2 ^ (K' + 1) * y := by gcongr <;> norm_num⟩
      classical
      set k := Nat.find hex with hk
      have hk1 : (m : ℝ) ≤ 2 ^ (k + 1) * y := Nat.find_spec hex
      have hk2 : 2 ^ k * y < m := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, pow_zero, one_mul]; exact h1
        · have := Nat.find_min hex (show k - 1 < k by omega)
          push Not at this
          rwa [show k - 1 + 1 = k by omega] at this
      have hkK : k < K' := by
        by_contra hK
        push Not at hK
        have : (2 : ℝ) ^ K' * y ≤ 2 ^ k * y := by gcongr; norm_num
        linarith
      have hm0 : (0 : ℝ) < m := by linarith
      calc W m / m ≤ W m / (2 ^ k * y) :=
            div_le_div_of_nonneg_left (hW0 m) (by positivity) hk2.le
        _ = (if (m : ℝ) ≤ 2 ^ (k + 1) * y then W m else 0) / (2 ^ k * y) := by
            rw [ite_eq_left hk1]
        _ ≤ _ := single_le_sum (f := fun k => (if (m : ℝ) ≤ 2 ^ (k + 1) * y then W m else 0) /
              (2 ^ k * y)) (fun k _ => by split_ifs <;> positivity [hW0 m]) (mem_range.2 hkK)
    · exact sum_nonneg fun k _ => by split_ifs <;> positivity [hW0 m]
  refine (sum_le_sum hpt).trans ?_
  rw [sum_comm]
  calc ∑ k ∈ range K', ∑ m ∈ Icc 1 N, (if (m : ℝ) ≤ 2 ^ (k + 1) * y then W m else 0) /
        (2 ^ k * y)
      ≤ ∑ _k ∈ range K', 2 * cW := by
        refine sum_le_sum fun k _ => ?_
        rw [← sum_div, div_le_iff₀ (by positivity)]
        calc ∑ m ∈ Icc 1 N, (if (m : ℝ) ≤ 2 ^ (k + 1) * y then W m else 0)
            ≤ cW * (2 ^ (k + 1) * y) := hcount _ (by positivity)
          _ = 2 * cW * (2 ^ k * y) := by ring
    _ = 2 * cW * K' := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- The log density of `δ = a_j^0 - a_j`. -/
theorem sum_abs_delta_le {x γ : ℝ} {j N K' : ℕ} {c₃ cW SP : ℝ} (hx : 1 < x)
    (hL : 1 ≤ Real.log x) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hj : 1 ≤ j)
    (hYP : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x)
    (hYN : proxyCutoff x ≤ N) (hc₃ : 0 < c₃) (hlogY : 0 < Real.log (proxyCutoff x))
    (hPiY : c₃ / Real.log (proxyCutoff x) ≤ ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p))
    (hcount : ∀ w : ℝ, 0 ≤ w → ∑ m ∈ Icc 1 N, (if (m : ℝ) ≤ w then proxyEnv x γ j m else 0) ≤
      cW * w)
    (hSP : ∑ p ∈ candidatePrimes x, Real.log p / p ≤ SP)
    (hK' : Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ 2 ^ K') :
    ∑ m ∈ Icc 1 N, |unstrippedProxy x γ j m - strippedProxy x γ j m| / m ≤
      2 * cW * K' + 2 * SP * (∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹) *
        (Real.log (proxyCutoff x) / c₃) / (γ ^ 2 * Real.log x ^ (19 / 10 : ℝ)) := by
  have hD := dampedDensity_pos hL hj
  obtain ⟨hPi, hPiD⟩ := prod_le_dampedDensity hL hj
  have hL0 : 0 < Real.log x := by linarith
  have hden : 0 < γ ^ 2 * Real.log x ^ (19 / 10 : ℝ) := by positivity
  have hxγ0 : 0 < x ^ γ := by positivity
  set Q := (dampedDensity x j * (γ ^ 2 * Real.log x ^ (19 / 10 : ℝ)))⁻¹ with hQ
  have hlogdiff : ∀ m : ℕ, 1 ≤ m → 0 ≤ Real.log m - Real.log (candidateStrip x m) := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    have h1 : (1 : ℝ) ≤ candidateStrip x m := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (stripPrimes_ne_zero _ m)
    have h2 : ((candidateStrip x m : ℕ) : ℝ) ≤ m := by exact_mod_cast stripPrimes_le _ hm0
    linarith [Real.log_le_log (by linarith) h2]
  -- pointwise: the strip and the rest
  have hpt : ∀ m ∈ Icc 1 N, |unstrippedProxy x γ j m - strippedProxy x γ j m| / m ≤
      (if x ^ γ < m ∧ (m : ℝ) ≤ 2 ^ K' * x ^ γ then proxyEnv x γ j m / m else 0) +
        Q * (dampedWeight x j m * (Real.log m - Real.log (candidateStrip x m)) / m) := by
    intro m hm
    have hm1 := (mem_Icc.1 hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hsecond : 0 ≤ Q * (dampedWeight x j m * (Real.log m - Real.log (candidateStrip x m)) /
        m) := by
      have := hlogdiff m hm1
      have := dampedWeight_nonneg x j m
      positivity
    by_cases hmγ : (m : ℝ) ≤ x ^ γ
    · obtain ⟨h1, h2⟩ := proxies_eq_zero (j := j) hx hγ.le hmγ
      rw [h1, h2, sub_zero, abs_zero, zero_div]
      have : 0 ≤ (if x ^ γ < m ∧ (m : ℝ) ≤ 2 ^ K' * x ^ γ then proxyEnv x γ j m / m else 0) := by
        split_ifs <;> [exact div_nonneg (proxyEnv_nonneg hL hγ hj m) hm0.le; exact le_rfl]
      linarith
    push Not at hmγ
    by_cases hmZ : Real.log m ≤ γ * Real.log x + Real.log x ^ (9 / 10 : ℝ)
    · -- the threshold strip
      have hmK : (m : ℝ) ≤ 2 ^ K' * x ^ γ := by
        rw [← Real.exp_log hm0, Real.rpow_def_of_pos (by linarith), mul_comm]
        calc Real.exp (Real.log m) ≤ Real.exp (Real.log x * γ + Real.log x ^ (9 / 10 : ℝ)) :=
              Real.exp_le_exp.2 (by linarith)
          _ = Real.exp (Real.log x * γ) * Real.exp (Real.log x ^ (9 / 10 : ℝ)) := Real.exp_add _ _
          _ ≤ Real.exp (Real.log x * γ) * 2 ^ K' := by gcongr
      rw [ite_eq_left ⟨hmγ, hmK⟩]
      have h := abs_proxy_sub_le hx hL hγ hj m
      have henv : proxyEnv x γ j m =
          dampedWeight x j m / (dampedDensity x j * (γ * Real.log x)) := by
        unfold proxyEnv; rw [ite_eq_left hmγ]
      have : |unstrippedProxy x γ j m - strippedProxy x γ j m| / m ≤ proxyEnv x γ j m / m := by
        rw [henv]; exact div_le_div_of_nonneg_right h hm0.le
      linarith
    · -- above the strip
      push Not at hmZ
      have h := abs_proxy_sub_le_log hx hL hγ hγ1 hj hmZ
      have : 0 ≤ (if x ^ γ < m ∧ (m : ℝ) ≤ 2 ^ K' * x ^ γ then proxyEnv x γ j m / m else 0) := by
        split_ifs <;> [exact div_nonneg (proxyEnv_nonneg hL hγ hj m) hm0.le; exact le_rfl]
      have h2 : |unstrippedProxy x γ j m - strippedProxy x γ j m| / m ≤
          Q * (dampedWeight x j m * (Real.log m - Real.log (candidateStrip x m)) / m) := by
        rw [hQ]
        calc |unstrippedProxy x γ j m - strippedProxy x γ j m| / m
            ≤ dampedWeight x j m / dampedDensity x j *
                (Real.log m - Real.log (candidateStrip x m)) /
                  (γ ^ 2 * Real.log x ^ (19 / 10 : ℝ)) / m :=
              div_le_div_of_nonneg_right h hm0.le
          _ = _ := by field_simp
      linarith
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib]
  refine add_le_add (sum_dyadic_le hxγ0 (proxyEnv_nonneg hL hγ hj) hcount) ?_
  -- the candidate logarithm
  rw [← mul_sum]
  have hlog := sum_dampedWeight_log_div_le hL hj N
  have hdens := sum_dampedWeight_div_le hL hYP hYN hj
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ht1 : (j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hj'
  have hSP0 : 0 ≤ SP := le_trans (sum_nonneg fun p hp => by
    have := (mem_candidatePrimes hL hp).1.one_lt.le
    have : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast this)
    positivity) hSP
  have hPi1 : 0 ≤ ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹ :=
    prod_nonneg fun p hp => by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesIoc.1 hp).1.two_le
      rw [inv_nonneg, sub_nonneg, div_le_one (by linarith)]; linarith
  have hPc : 0 < ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ := by
    have := hD; unfold dampedDensity at this
    exact pos_of_mul_pos_right this hPi.le
  have hgsum0 : 0 ≤ ∑ m ∈ Icc 1 N, dampedWeight x j m / m :=
    sum_nonneg fun m _ => div_nonneg (dampedWeight_nonneg x j m) (Nat.cast_nonneg m)
  calc Q * ∑ m ∈ Icc 1 N, dampedWeight x j m * (Real.log m - Real.log (candidateStrip x m)) / m
      ≤ Q * (2 * (j : ℝ)⁻¹ * (∑ p ∈ candidatePrimes x, Real.log p / p) *
          ∑ m ∈ Icc 1 N, dampedWeight x j m / m) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ Q * (2 * 1 * SP * ((∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹) *
          ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹)) := by
        gcongr
    _ = 2 * SP * (∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹) /
          ((∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) *
            (γ ^ 2 * Real.log x ^ (19 / 10 : ℝ))) := by
        have key : ∀ a b c d e : ℝ, b ≠ 0 →
            (a * b * c)⁻¹ * (2 * 1 * e * (b * d)) = 2 * e * d / (a * c) := by
          intro a b c d e hb
          rw [div_eq_mul_inv, mul_inv, mul_inv, mul_inv]
          field_simp
        rw [hQ, dampedDensity]
        exact key _ _ _ _ _ hPc.ne'
    _ ≤ _ := by
        rw [div_le_div_iff₀ (by positivity) hden, mul_assoc (2 * SP * _)]
        have hinv : 1 ≤ (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) *
            (Real.log (proxyCutoff x) / c₃) := by
          have := mul_le_mul_of_nonneg_right hPiY (show 0 ≤ Real.log (proxyCutoff x) / c₃ by
            positivity)
          rwa [div_mul_div_comm, mul_comm c₃, div_self (by positivity)] at this
        have := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 2 * SP *
          (∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹) *
            (γ ^ 2 * Real.log x ^ (19 / 10 : ℝ)) by positivity)
        nlinarith

/-! ### One telescoping step of E5 -/

/-- One step of E5: the companion is counted with its first factor, which gives `1/L`. -/
theorem abs_strip_step_le {x γ : ℝ} {j N r : ℕ} {SΨ cW : ℝ} (hL : 1 ≤ Real.log x)
    (hγ : 0 < γ) (hj : 1 ≤ j)
    (hY : 1 ≤ (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x))
    (hYP : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x) (hYN : proxyCutoff x ≤ N)
    (Ψ : ℕ → ℝ) (hΨ0 : ∀ h, N < h → Ψ h = 0) (hΨ : ∀ h, |Ψ h| ≤ SΨ) (hcW : 0 ≤ cW)
    (hcount : ∀ w : ℝ, 0 ≤ w → ∑ m ∈ Icc 1 N, (if (m : ℝ) ≤ w then proxyEnv x γ j m else 0) ≤
      cW * w)
    (U : Fin (r + 1) → ℕ → ℝ) (hU0 : ∀ k m, 0 ≤ U k m) (hU : ∀ k m, U k m ≤ proxyEnv x γ j m) :
    |∑ m₀ ∈ Icc 1 N, ∑ m' ∈ Fintype.piFinset (fun _ : Fin (r + 1) => Icc 1 N),
        Ψ (m₀ * ∏ k, m' k) * (unstrippedProxy x γ j m₀ - strippedProxy x γ j m₀) *
          ∏ k, U k (m' k)| ≤
      SΨ * cW * N * (∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹) ^ r *
        ∑ m ∈ Icc 1 N, |unstrippedProxy x γ j m - strippedProxy x γ j m| / m := by
  have hS : 0 ≤ SΨ := (abs_nonneg _).trans (hΨ 0)
  set P₁ := ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹ with hP1
  have hcount' : ∀ w : ℝ, 0 ≤ w → ∑ a ∈ Icc 1 N, (if (a : ℝ) ≤ w then U 0 a else 0) ≤ cW * w :=
    fun w hw => (sum_le_sum fun a _ => by split_ifs <;> [exact hU 0 a; exact le_rfl]).trans
      (hcount w hw)
  have hfactor : ∏ k : Fin r, ∑ a ∈ Icc 1 N, U k.succ a / a ≤ P₁ ^ r := by
    rw [show P₁ ^ r = ∏ _k : Fin r, P₁ by rw [prod_const, card_univ, Fintype.card_fin]]
    refine prod_le_prod₀ (fun k _ => sum_nonneg fun a _ => div_nonneg (hU0 _ _)
      (Nat.cast_nonneg a)) fun k _ => ?_
    have h := sum_proxyEnv_div_le hL hγ hj hY hYP hYN (hU k.succ)
    refine le_trans (le_of_eq (sum_congr rfl fun a ha => ?_)) h
    have ha0 : a ≠ 0 := by have := (mem_Icc.1 ha).1; omega
    rw [cmul_inv ha0, div_eq_mul_inv]
  have hinner : ∀ m₀ ∈ Icc 1 N, |∑ m' ∈ Fintype.piFinset (fun _ : Fin (r + 1) => Icc 1 N),
      Ψ (m₀ * ∏ k, m' k) * (unstrippedProxy x γ j m₀ - strippedProxy x γ j m₀) *
        ∏ k, U k (m' k)| ≤
      SΨ * cW * N * P₁ ^ r * (|unstrippedProxy x γ j m₀ - strippedProxy x γ j m₀| / m₀) := by
    intro m₀ hm₀
    have hm₀1 : 1 ≤ m₀ := (mem_Icc.1 hm₀).1
    have hm₀0 : (0 : ℝ) < m₀ := by exact_mod_cast hm₀1
    set d := |unstrippedProxy x γ j m₀ - strippedProxy x γ j m₀|
    have hpt : ∀ m' ∈ Fintype.piFinset (fun _ : Fin (r + 1) => Icc 1 N),
        |Ψ (m₀ * ∏ k, m' k) * (unstrippedProxy x γ j m₀ - strippedProxy x γ j m₀) *
          ∏ k, U k (m' k)| ≤
        SΨ * d * (if ((∏ k, m' k : ℕ) : ℝ) ≤ N / m₀ then ∏ k, U k (m' k) else 0) := by
      intro m' _
      have hU' : 0 ≤ ∏ k, U k (m' k) := prod_nonneg fun k _ => hU0 _ _
      rw [abs_mul, abs_mul, abs_of_nonneg hU']
      split_ifs with h
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hΨ _) (abs_nonneg _)) hU'
      · push Not at h
        have : N < m₀ * ∏ k, m' k := by
          rw [div_lt_iff₀ hm₀0] at h
          push_cast at h
          exact_mod_cast (show (N : ℝ) < m₀ * ∏ k, m' k by push_cast; linarith)
        rw [hΨ0 _ this, abs_zero, zero_mul, zero_mul, mul_zero]
    calc _ ≤ ∑ m' ∈ Fintype.piFinset (fun _ : Fin (r + 1) => Icc 1 N),
          |Ψ (m₀ * ∏ k, m' k) * (unstrippedProxy x γ j m₀ - strippedProxy x γ j m₀) *
            ∏ k, U k (m' k)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ m' ∈ Fintype.piFinset (fun _ : Fin (r + 1) => Icc 1 N),
          SΨ * d * (if ((∏ k, m' k : ℕ) : ℝ) ≤ N / m₀ then ∏ k, U k (m' k) else 0) :=
          sum_le_sum hpt
      _ = SΨ * d * ∑ m' ∈ Fintype.piFinset (fun _ : Fin (r + 1) => Icc 1 N),
          (if ((∏ k, m' k : ℕ) : ℝ) ≤ N / m₀ then ∏ k, U k (m' k) else 0) := by rw [mul_sum]
      _ ≤ SΨ * d * (cW * (N / m₀) * ∏ k : Fin r, ∑ a ∈ Icc 1 N, U k.succ a / a) :=
          mul_le_mul_of_nonneg_left (sum_prod_le_mass_count (fun a ha => (mem_Icc.1 ha).1) U hU0
            hcount' (by positivity)) (by positivity)
      _ ≤ SΨ * d * (cW * (N / m₀) * P₁ ^ r) := by gcongr
      _ = _ := by ring
  calc _ ≤ ∑ m₀ ∈ Icc 1 N, |∑ m' ∈ Fintype.piFinset (fun _ : Fin (r + 1) => Icc 1 N),
        Ψ (m₀ * ∏ k, m' k) * (unstrippedProxy x γ j m₀ - strippedProxy x γ j m₀) *
          ∏ k, U k (m' k)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ m₀ ∈ Icc 1 N, SΨ * cW * N * P₁ ^ r *
          (|unstrippedProxy x γ j m₀ - strippedProxy x γ j m₀| / m₀) := sum_le_sum hinner
    _ = _ := by rw [mul_sum]

end Erdos408.TypeII
