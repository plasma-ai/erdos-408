import Erdos408.Extraction.TypeII.Proxy
import Erdos408.Extraction.TypeII.Asymp
import Erdos408.Extraction.TypeII.PrimeSums

/-!
# One box of the Type II estimate

`OneSidedTypeII` applied to one box `m ∈ (lo, hi] ⊂ [λ, 2λ]`, `n ∈ [μ, 2μ]` with
`λμ ≍ x`, and the coefficient `α_m = [m prime, m > x^γ] - a_j^0(m)`. The hypothesis is
applied at the scale `x' = λμ` (so `C_X = 1`), with the band exponents rescaled by
`log L / log log x'` so that the bands at `x'` are the bands at `x`, and with `γ/2` in place
of `γ`. Its premises come from:

* P1–P3: `α` is supported on `(lo, hi]`, its prime factors are candidate primes or exceed
  `Y`, or `α` is supported on primes `> x^γ`; all of these exceed `W' = exp((log x')^{0.24})`.
  `|α| ≤ 1`, since `0 ≤ a_j^0 ≤ 1`.
* P4: the twisted-cancellation premise `ProxyTwistPremise` (AC1, `eventually_proxyTwist`).
* The kernel premise `KernelPremise` (AC3, `eventually_kernel_premise`).

The two analytic premises are stated here as hypotheses, so that this file does not depend on
their proofs.
-/

namespace Erdos408.TypeII

open Filter Real Finset

/-- The bound of `eventually_proxyTwist` (AC1) at one `x`. -/
def ProxyTwistAt (c Ch Cj A Cm Kan κ x : ℝ) : Prop :=
  ∀ (j : ℕ), 1 ≤ j → (j : ℝ) ≤ Cj * logLogLog x + 1 →
  ∀ H lo hi : ℝ, x ^ presieveExponent c Ch x / 2 ≤ H → H ≤ x ^ Kan → H ≤ lo →
    hi ≤ 2 * H →
  ∀ (k : ℕ), 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm → ∀ (χ : DirichletCharacter ℂ k)
    (t : ℝ), |t| ≤ x ^ Kan →
    ‖(H : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊,
        χ n * (n : ℂ) ^ ((t : ℂ) * Complex.I) *
          (((if n.Prime ∧ x ^ presieveExponent c Ch x < n then 1 else 0 : ℝ) : ℂ) -
            (unstrippedProxy x (presieveExponent c Ch x) j n : ℂ))‖ ≤
      κ * Real.log x ^ (-A)

/-- The statement of `eventually_proxyTwist` (AC1) for fixed `c, C_h, C_j`. -/
def ProxyTwistPremise (c Ch Cj : ℝ) : Prop :=
  ∀ A Cm Kan : ℝ, ∃ κ : ℝ, ∀ᶠ x : ℝ in atTop, ProxyTwistAt c Ch Cj A Cm Kan κ x

/-- The statement of `eventually_kernel_premise` (AC3). -/
def KernelPremise : Prop :=
  ∀ CX B : ℝ, ∃ cG : ℝ, ∀ᶠ x : ℝ in atTop,
    ∀ γ Hm Hn : ℝ, Real.log x ^ (-(1 / 100 : ℝ)) ≤ γ → x ^ γ ≤ Hm → x ^ γ ≤ Hn →
      Hm * Hn ≤ CX * x → ∀ Δ : ℝ, 1 ≤ |Δ| → |Δ| ≤ 4 * (Hm * Hn) * Real.log x ^ B + 2 →
        Hn⁻¹ * ‖∑ n ∈ Finset.Icc ⌈Hn⌉₊ ⌊2 * Hn⌋₊, (n : ℂ) ^ ((Δ : ℂ) * Complex.I)‖ ≤
          cG * (|Δ|⁻¹ + Real.exp (-Real.log x ^ (0.95 : ℝ)))

/-- The prime-minus-proxy coefficient `[m prime, m > x^γ] - a_j^0(m)`. -/
noncomputable def primeProxyDiff (x γ : ℝ) (j m : ℕ) : ℝ :=
  (if m.Prime ∧ x ^ γ < m then 1 else 0) - unstrippedProxy x γ j m

/-- `log x'` is within `log κ` of `log x` when `x / κ ≤ x' ≤ κ x`. -/
theorem abs_log_sub_le {x x' κ : ℝ} (hx : 0 < x) (hκ : 1 < κ) (h1 : x / κ ≤ x')
    (h2 : x' ≤ κ * x) : |Real.log x' - Real.log x| ≤ Real.log κ := by
  have hκ0 : 0 < κ := by linarith
  have hx' : 0 < x' := lt_of_lt_of_le (by positivity) h1
  rw [abs_le]
  constructor
  · have := Real.log_le_log (by positivity) h1
    rw [Real.log_div hx.ne' hκ0.ne'] at this
    linarith
  · have := Real.log_le_log hx' h2
    rw [Real.log_mul hκ0.ne' hx.ne'] at this
    linarith

/-- Rescaling the band exponents by `log L / log log x'` gives the same bands at `x'`. -/
theorem band_rescale {x x' : ℝ} (hL : 0 < Real.log x) (hL' : 0 < Real.log x')
    (hT' : Real.log (Real.log x') ≠ 0) (a : ℝ) :
    band x' (a * (logLog x / Real.log (Real.log x'))) = band x a := by
  have h : Real.log x' ^ (a * (logLog x / Real.log (Real.log x'))) = Real.log x ^ a := by
    rw [Real.rpow_def_of_pos hL', Real.rpow_def_of_pos hL, logLog]
    congr 1
    field_simp
  unfold band
  rw [h]

/-- `0 ≤ a_j^0 ≤ 1` once `∏_{p ≤ Y} (1 - 1/p) · γ L ≥ 1`. -/
theorem unstrippedProxy_le_one {x γ : ℝ} (hx : 1 < x) (hL : 1 ≤ Real.log x) (hγ : 0 < γ)
    {j : ℕ} (hj : 1 ≤ j)
    (hY : 1 ≤ (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x))
    (n : ℕ) : 0 ≤ unstrippedProxy x γ j n ∧ unstrippedProxy x γ j n ≤ 1 := by
  obtain ⟨h0, h1⟩ := unstrippedProxy_le hx hL hγ hj n
  refine ⟨h0, h1.trans ?_⟩
  obtain ⟨-, hPiD⟩ := prod_le_dampedDensity hL hj
  have hD := dampedDensity_pos hL hj
  have hγL : 0 < γ * Real.log x := by positivity
  have hg : (if x ^ γ < n then dampedWeight x j n else 0) ≤ 1 := by
    split_ifs
    · exact dampedWeight_le_one x hj n
    · exact zero_le_one
  rw [div_le_one (by positivity)]
  calc (if x ^ γ < n then dampedWeight x j n else 0) ≤ 1 := hg
    _ ≤ _ := hY
    _ ≤ dampedDensity x j * (γ * Real.log x) := mul_le_mul_of_nonneg_right hPiD hγL.le

/-- The prime factors of a number where `[m prime, m > x^γ] - a_j^0(m) ≠ 0` are at least
`exp(L^{0.28})`. -/
theorem primeFactors_ge_of_primeProxyDiff {x γ : ℝ} (hL : 1 ≤ Real.log x) {j m : ℕ}
    (hγ : Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ x ^ γ)
    (hY : Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ proxyCutoff x)
    (h : primeProxyDiff x γ j m ≠ 0) :
    ∀ p ∈ m.primeFactors, Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p := by
  intro p hp
  unfold primeProxyDiff at h
  by_cases hm : m.Prime ∧ x ^ γ < m
  · rw [Nat.Prime.primeFactors hm.1, mem_singleton] at hp
    subst hp
    exact hγ.trans hm.2.le
  · simp only [hm, ↓reduceIte, zero_sub, neg_ne_zero] at h
    unfold unstrippedProxy at h
    split_ifs at h with hxm
    · have hg : dampedWeight x j m ≠ 0 := fun h0 => h (by rw [h0, zero_div])
      by_cases hpP : p ∈ candidatePrimes x
      · exact (mem_candidatePrimes hL hpP).2.1
      · unfold dampedWeight at hg
        split_ifs at hg with hrough
        · have hpm : p ∈ (candidateStrip x m).primeFactors := by
            rw [candidateStrip, primeFactors_stripPrimes, mem_filter]
            exact ⟨hp, hpP⟩
          exact hY.trans (hrough p hpm).le
        · exact absurd rfl hg
    · exact absurd rfl h

/-- `r^e ≤ 2^{|e|}` for `1/2 ≤ r ≤ 2`. -/
theorem rpow_le_two_rpow_abs {r : ℝ} (h1 : 1 / 2 ≤ r) (h2 : r ≤ 2) (e : ℝ) :
    r ^ e ≤ 2 ^ |e| := by
  have hr : 0 < r := by linarith
  rcases le_or_gt 0 e with he | he
  · rw [abs_of_nonneg he]
    exact Real.rpow_le_rpow hr.le h2 he
  · rw [abs_of_neg he]
    have : r⁻¹ ≤ 2 := by rw [inv_le_comm₀ hr (by norm_num)]; linarith
    calc r ^ e = (r⁻¹) ^ (-e) := by rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, neg_neg]
      _ ≤ 2 ^ (-e) := Real.rpow_le_rpow (by positivity) this (by linarith)

/-- Comparing powers of nearby logarithms: `a^e ≤ 2^{|e|} b^e` for `b/2 ≤ a ≤ 2b`. -/
theorem rpow_le_of_near {a b : ℝ} (hb : 0 < b) (h1 : b / 2 ≤ a) (h2 : a ≤ 2 * b) (e : ℝ) :
    a ^ e ≤ 2 ^ |e| * b ^ e := by
  have ha : 0 < a := by linarith
  have hr1 : 1 / 2 ≤ a / b := by rw [le_div_iff₀ hb]; linarith
  have hr2 : a / b ≤ 2 := by rw [div_le_iff₀ hb]; linarith
  have := rpow_le_two_rpow_abs hr1 hr2 e
  rw [Real.div_rpow ha.le hb.le, div_le_iff₀ (by positivity)] at this
  exact this

/-! ### The scale `x' = λμ` -/

section Scale

variable {x x' κ γ : ℝ}

/-- `L/2 ≤ log x' ≤ 2L` when `x' ∈ [x/κ, κx]` and `2 log κ ≤ L`. -/
theorem log_scale_bounds (hx : 0 < x) (hκ : 1 < κ) (h1 : x / κ ≤ x') (h2 : x' ≤ κ * x)
    (hLκ : 2 * Real.log κ ≤ Real.log x) :
    Real.log x / 2 ≤ Real.log x' ∧ Real.log x' ≤ 2 * Real.log x := by
  have h := abs_log_sub_le hx hκ h1 h2
  rw [abs_le] at h
  have := Real.log_nonneg hκ.le
  constructor <;> linarith

/-- The rescaling ratio `T / log log x'` lies in `[0.96, 1.02]` when `T ≥ 50`. -/
theorem ratio_bounds (hL : 0 < Real.log x) (hp1 : Real.log x / 2 ≤ Real.log x')
    (hp2 : Real.log x' ≤ 2 * Real.log x) (hT : 50 ≤ logLog x) :
    0 < Real.log (Real.log x') ∧ 96 / 100 ≤ logLog x / Real.log (Real.log x') ∧
      logLog x / Real.log (Real.log x') ≤ 102 / 100 := by
  have hLp0 : 0 < Real.log x' := by linarith
  have hTp1 : logLog x - Real.log 2 ≤ Real.log (Real.log x') := by
    have := Real.log_le_log (by positivity) hp1
    rw [Real.log_div hL.ne' (by norm_num)] at this
    unfold logLog; linarith
  have hTp2 : Real.log (Real.log x') ≤ logLog x + Real.log 2 := by
    have := Real.log_le_log hLp0 hp2
    rw [Real.log_mul (by norm_num) hL.ne'] at this
    unfold logLog; linarith
  have hlog2 : Real.log 2 < 7 / 10 := by have := Real.log_two_lt_d9; linarith
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hTp0 : 0 < Real.log (Real.log x') := by linarith
  refine ⟨hTp0, ?_, ?_⟩
  · rw [le_div_iff₀ hTp0]; linarith
  · rw [div_le_iff₀ hTp0]; linarith

/-- The window `[0.11, 0.19]` rescales into `[0.105, 0.195]`. -/
theorem rescale_window {ρ a : ℝ} (hρ1 : 96 / 100 ≤ ρ) (hρ2 : ρ ≤ 102 / 100)
    (ha1 : 11 / 100 ≤ a) (ha2 : a ≤ 19 / 100) :
    21 / 200 ≤ a * ρ ∧ a * ρ ≤ 39 / 200 := by
  constructor
  · have := mul_le_mul ha1 hρ1 (by norm_num) (by linarith); linarith
  · have := mul_le_mul ha2 hρ2 (by linarith) (by norm_num); linarith

/-- The gap `0.04 / K` rescales to at least `0.02 / K`. -/
theorem rescale_gap {ρ a a' K : ℝ} (hK : 0 < K) (hρ1 : 96 / 100 ≤ ρ)
    (h : a + 4 / 100 / K ≤ a') : a * ρ + 2 / 100 / K ≤ a' * ρ := by
  have h4 : 2 / 100 / K ≤ ρ * (4 / 100 / K) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hK.le
  have h5 := mul_le_mul_of_nonneg_right h (show 0 ≤ ρ by linarith)
  rw [add_mul] at h5
  linarith

/-- `(log x')^{-1/100} ≤ γ/2`. -/
theorem log_rpow_le_half (hL : 0 < Real.log x) (hp1 : Real.log x / 2 ≤ Real.log x')
    (hT : 0 < logLog x) (hγ : logLog x ^ (-21 : ℝ) ≤ γ)
    (h1 : logLog x ^ (21 : ℝ) ≤ Real.log x ^ (1 / 200 : ℝ))
    (h2 : Real.log x ^ (1 / 200 : ℝ) ≤ 1 / 4 * Real.log x ^ (1 / 100 : ℝ)) :
    Real.log x' ^ (-(1 / 100 : ℝ)) ≤ γ / 2 := by
  have hLp0 : 0 < Real.log x' := by linarith
  have hT21 : 0 < logLog x ^ (21 : ℝ) := by positivity
  have hγ0 : 0 < γ := lt_of_lt_of_le (by positivity) hγ
  have h3 : Real.log x ^ (1 / 100 : ℝ) / 2 ≤ Real.log x' ^ (1 / 100 : ℝ) := by
    calc Real.log x ^ (1 / 100 : ℝ) / 2
        ≤ Real.log x ^ (1 / 100 : ℝ) / 2 ^ (1 / 100 : ℝ) := by
          gcongr
          calc (2 : ℝ) ^ (1 / 100 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
      _ = (Real.log x / 2) ^ (1 / 100 : ℝ) := by rw [Real.div_rpow hL.le (by norm_num)]
      _ ≤ Real.log x' ^ (1 / 100 : ℝ) := Real.rpow_le_rpow (by positivity) hp1 (by norm_num)
  rw [Real.rpow_neg hLp0.le, inv_le_comm₀ (by positivity) (by positivity)]
  have h4 : (γ / 2)⁻¹ ≤ 2 * logLog x ^ (21 : ℝ) := by
    rw [inv_div, div_le_iff₀ hγ0]
    have := mul_le_mul_of_nonneg_left hγ hT21.le
    rw [Real.rpow_neg hT.le, mul_inv_cancel₀ hT21.ne'] at this
    linarith
  linarith

/-- `x'^{γ/2} ≤ x^γ` for `x' ≤ x²`. -/
theorem rpow_half_le (hx : 0 < x) (hx' : 0 < x') (hxx : x' ≤ x ^ 2) (hγ : 0 ≤ γ) :
    x' ^ (γ / 2) ≤ x ^ γ := by
  calc x' ^ (γ / 2) ≤ (x ^ 2) ^ (γ / 2) := Real.rpow_le_rpow hx'.le hxx (by positivity)
    _ = x ^ γ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; ring_nf

/-- Primes above `exp(L^{0.28})` exceed the roughness level at `x'`. -/
theorem roughLevel_lt (hL : 0 < Real.log x) (hp2 : Real.log x' ≤ 2 * Real.log x)
    (hLp : 0 < Real.log x')
    (h24 : Real.log x ^ (24 / 100 : ℝ) ≤ 1 / 2 * Real.log x ^ (28 / 100 : ℝ)) {p : ℝ}
    (hp : Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p) : roughLevel x' < p := by
  refine lt_of_lt_of_le ?_ hp
  unfold roughLevel
  rw [Real.exp_lt_exp]
  have h1 : Real.log x' ^ (0.24 : ℝ) ≤ (2 * Real.log x) ^ (0.24 : ℝ) :=
    Real.rpow_le_rpow hLp.le hp2 (by norm_num)
  have h2 : (2 * Real.log x) ^ (0.24 : ℝ) = 2 ^ (0.24 : ℝ) * Real.log x ^ (0.24 : ℝ) :=
    Real.mul_rpow (by norm_num) hL.le
  have h3 : (2 : ℝ) ^ (0.24 : ℝ) < 2 := by
    calc (2 : ℝ) ^ (0.24 : ℝ) < 2 ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h4 : 0 < Real.log x ^ (0.24 : ℝ) := by positivity
  have h5 : Real.log x ^ (0.24 : ℝ) = Real.log x ^ (24 / 100 : ℝ) := by norm_num
  calc Real.log x' ^ (0.24 : ℝ) ≤ (2 * Real.log x) ^ (0.24 : ℝ) := h1
    _ = 2 ^ (0.24 : ℝ) * Real.log x ^ (0.24 : ℝ) := h2
    _ < 2 * Real.log x ^ (0.24 : ℝ) := mul_lt_mul_of_pos_right h3 h4
    _ = 2 * Real.log x ^ (24 / 100 : ℝ) := by rw [h5]
    _ ≤ Real.log x ^ (28 / 100 : ℝ) := by linarith

/-- `exp(L^{0.28}) ≤ x^γ` when `γ ≥ T^{-21}` and `T^{21} ≤ L^{0.72}`. -/
theorem exp_le_rpow_gamma (hx : 0 < x) (hL : 0 < Real.log x) (hT : 0 < logLog x)
    (hγ : logLog x ^ (-21 : ℝ) ≤ γ) (h21 : logLog x ^ (21 : ℝ) ≤ Real.log x ^ (72 / 100 : ℝ)) :
    Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ x ^ γ := by
  rw [Real.rpow_def_of_pos hx, Real.exp_le_exp]
  have hT21 : 0 < logLog x ^ (21 : ℝ) := by positivity
  have h1 : Real.log x ^ (28 / 100 : ℝ) * logLog x ^ (21 : ℝ) ≤ Real.log x := by
    calc Real.log x ^ (28 / 100 : ℝ) * logLog x ^ (21 : ℝ)
        ≤ Real.log x ^ (28 / 100 : ℝ) * Real.log x ^ (72 / 100 : ℝ) := by gcongr
      _ = Real.log x := by rw [← Real.rpow_add hL]; norm_num
  have h2 : Real.log x * logLog x ^ (-21 : ℝ) ≤ Real.log x * γ :=
    mul_le_mul_of_nonneg_left hγ hL.le
  rw [Real.rpow_neg hT.le] at h2
  have h1' : Real.log x ^ (28 / 100 : ℝ) ≤ Real.log x * (logLog x ^ (21 : ℝ))⁻¹ := by
    rw [← div_eq_mul_inv]; exact (le_div_iff₀ hT21).2 h1
  linarith

/-- `exp(L^{0.28}) ≤ Y` when `T^{25} ≤ L^{0.72}`. -/
theorem exp_le_proxyCutoff (hL : 0 < Real.log x) (hT : 0 < logLog x)
    (h25 : logLog x ^ (25 : ℝ) ≤ Real.log x ^ (72 / 100 : ℝ)) :
    Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ proxyCutoff x := by
  unfold proxyCutoff
  rw [Real.exp_le_exp]
  have hT25pos : 0 < logLog x ^ (25 : ℕ) := by positivity
  rw [le_div_iff₀ hT25pos]
  rw [show logLog x ^ (25 : ℝ) = logLog x ^ (25 : ℕ) by norm_cast] at h25
  calc Real.log x ^ (28 / 100 : ℝ) * logLog x ^ 25
      ≤ Real.log x ^ (28 / 100 : ℝ) * Real.log x ^ (72 / 100 : ℝ) := by gcongr
    _ = Real.log x := by rw [← Real.rpow_add hL]; norm_num

/-- `1 ≤ ∏_{p ≤ Y} (1 - 1/p) · γ L` once `c₃ T⁴ ≥ 1`, from Mertens. -/
theorem one_le_prod_mul {c₃ : ℝ} (hc₃ : 0 < c₃)
    (hmert : ∀ y : ℝ, 2 ≤ y → c₃ / Real.log y ≤ ∏ p ∈ primesIcc 2 y, (1 - (1 : ℝ) / p))
    (hL : 1 ≤ Real.log x) (hT : 0 < logLog x) (hγ : logLog x ^ (-21 : ℝ) ≤ γ)
    (hY2 : 2 ≤ proxyCutoff x) (hTc : 1 / c₃ ≤ logLog x ^ (4 : ℕ)) :
    1 ≤ (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x) := by
  have hm := hmert (proxyCutoff x) hY2
  have hlogY : Real.log (proxyCutoff x) = Real.log x / logLog x ^ 25 := by
    unfold proxyCutoff; rw [Real.log_exp]
  rw [hlogY] at hm
  have hγT : logLog x ^ (-21 : ℝ) * logLog x ^ (25 : ℕ) = logLog x ^ (4 : ℕ) := by
    rw [show logLog x ^ (25 : ℕ) = logLog x ^ (25 : ℝ) by norm_cast, ← Real.rpow_add hT]
    norm_num
  have hPi0 : 0 ≤ ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) :=
    prod_nonneg fun p hp => by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesIcc.1 hp).1.two_le
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hL0 : 0 < Real.log x := by linarith
  calc (1 : ℝ) ≤ c₃ * logLog x ^ 4 := by rw [div_le_iff₀ hc₃] at hTc; linarith
    _ = c₃ / (Real.log x / logLog x ^ 25) * (logLog x ^ (-21 : ℝ) * Real.log x) := by
        rw [← hγT]; field_simp
    _ ≤ _ := by gcongr

end Scale

/-- P4 for the box coefficient at the scale `x'`, from AC1 at `x`. -/
theorem box_P4 {c Ch Cj A A₀ B κp κ : ℝ} {x x' lam lo hi : ℝ} {j : ℕ}
    (hκpx : ProxyTwistAt c Ch Cj A (|A₀| + 1) 3 κp x) (hκ : 0 < κ) (hx1 : 1 < x)
    (hL : 0 < Real.log x) (hp1 : Real.log x / 2 ≤ Real.log x')
    (hp2 : Real.log x' ≤ 2 * Real.log x) (hLp1 : 1 ≤ Real.log x')
    (hLA₀ : 2 ^ |A₀| ≤ Real.log x) (hBx : 2 * κ * 2 ^ |B| * Real.log x ^ |B| ≤ x)
    (hx2 : x' ≤ κ * x) (hlamx : lam ≤ x ^ (3 : ℝ))
    (hH : x ^ presieveExponent c Ch x / 2 ≤ lam) (hlo : lam ≤ lo) (hhi : hi ≤ 2 * lam)
    (hj1 : 1 ≤ j) (hj2 : (j : ℝ) ≤ Cj * logLogLog x + 1) :
    ∀ (k : ℕ), 1 ≤ k → (k : ℝ) ≤ Real.log x' ^ A₀ → ∀ (χ : DirichletCharacter ℂ k)
      (t : ℝ), |t| ≤ 2 * x' * Real.log x' ^ B →
      ‖(lam : ℂ)⁻¹ * ∑ m ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, χ m * (m : ℂ) ^ ((t : ℂ) * Complex.I) *
          (((if m.Prime ∧ x ^ presieveExponent c Ch x < m then 1 else 0 : ℝ) : ℂ) -
            (unstrippedProxy x (presieveExponent c Ch x) j m : ℂ))‖ ≤
        |κp| * 2 ^ |A| * Real.log x' ^ (-A) := by
  intro k hk1 hk χ t ht
  have hx0 : 0 < x := by linarith
  have hLp0 : 0 < Real.log x' := by linarith
  have hk' : (k : ℝ) ≤ Real.log x ^ (|A₀| + 1) := by
    refine hk.trans ?_
    rcases le_or_gt 0 A₀ with hA | hA
    · calc Real.log x' ^ A₀ ≤ (2 * Real.log x) ^ A₀ := Real.rpow_le_rpow hLp0.le hp2 hA
        _ = 2 ^ A₀ * Real.log x ^ A₀ := Real.mul_rpow (by norm_num) hL.le
        _ ≤ Real.log x * Real.log x ^ A₀ := by
            gcongr
            calc (2 : ℝ) ^ A₀ ≤ 2 ^ |A₀| :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_abs_self _)
              _ ≤ Real.log x := hLA₀
        _ = Real.log x ^ (|A₀| + 1) := by
            rw [abs_of_nonneg hA, Real.rpow_add hL, Real.rpow_one, mul_comm]
    · have : (1 : ℝ) ≤ Real.log x := by
        have := Real.one_le_rpow (show (1 : ℝ) ≤ 2 by norm_num) (abs_nonneg A₀); linarith
      calc Real.log x' ^ A₀ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hLp1 hA.le
        _ ≤ Real.log x ^ (|A₀| + 1) := Real.one_le_rpow this (by positivity)
  have ht' : |t| ≤ x ^ (3 : ℝ) := by
    have h1L : (1 : ℝ) ≤ 2 * Real.log x := by linarith
    have hB' : Real.log x' ^ B ≤ (2 * Real.log x) ^ |B| := by
      rcases le_or_gt 0 B with hB | hB
      · calc Real.log x' ^ B ≤ (2 * Real.log x) ^ B := Real.rpow_le_rpow hLp0.le hp2 hB
          _ ≤ (2 * Real.log x) ^ |B| := Real.rpow_le_rpow_of_exponent_le h1L (le_abs_self _)
      · calc Real.log x' ^ B ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hLp1 hB.le
          _ ≤ (2 * Real.log x) ^ |B| := Real.one_le_rpow h1L (abs_nonneg _)
    have h2L : (2 * Real.log x) ^ |B| = 2 ^ |B| * Real.log x ^ |B| :=
      Real.mul_rpow (by norm_num) hL.le
    have hx3 : x * x ≤ x ^ (3 : ℝ) := by
      rw [show x ^ (3 : ℝ) = x ^ (3 : ℕ) by norm_cast, pow_succ, sq]
      exact le_mul_of_one_le_right (by positivity) hx1.le
    have hBpos : 0 ≤ Real.log x' ^ B := by positivity
    calc |t| ≤ 2 * x' * Real.log x' ^ B := ht
      _ ≤ 2 * (κ * x) * (2 * Real.log x) ^ |B| :=
          mul_le_mul (mul_le_mul_of_nonneg_left hx2 (by norm_num)) hB' hBpos (by positivity)
      _ = x * (2 * κ * 2 ^ |B| * Real.log x ^ |B|) := by rw [h2L]; ring
      _ ≤ x * x := mul_le_mul_of_nonneg_left hBx hx0.le
      _ ≤ x ^ (3 : ℝ) := hx3
  have hbound := hκpx j hj1 hj2 lam lo hi hH hlamx hlo hhi k hk1 hk' χ t ht'
  have hLA : Real.log x ^ (-A) ≤ 2 ^ |-A| * Real.log x' ^ (-A) :=
    rpow_le_of_near hLp0 (by linarith) (by linarith) (-A)
  rw [abs_neg] at hLA
  have hLA0 : 0 ≤ Real.log x ^ (-A) := by positivity
  calc _ ≤ κp * Real.log x ^ (-A) := hbound
    _ ≤ |κp| * Real.log x ^ (-A) := mul_le_mul_of_nonneg_right (le_abs_self _) hLA0
    _ ≤ |κp| * (2 ^ |A| * Real.log x' ^ (-A)) := mul_le_mul_of_nonneg_left hLA (abs_nonneg _)
    _ = _ := by ring

/-- `L³ ≤ (log x')⁴` for `log x' ≥ L/2 ≥ 8`. -/
theorem log_cube_le {x x' : ℝ} (hL16 : 16 ≤ Real.log x) (hp1 : Real.log x / 2 ≤ Real.log x') :
    Real.log x ^ (3 : ℝ) ≤ Real.log x' ^ (4 : ℝ) := by
  have e3 : Real.log x ^ (3 : ℝ) = Real.log x ^ (3 : ℕ) := by
    exact_mod_cast Real.rpow_natCast (Real.log x) 3
  have e4 : Real.log x' ^ (4 : ℝ) = Real.log x' ^ (4 : ℕ) := by
    exact_mod_cast Real.rpow_natCast (Real.log x') 4
  rw [e3, e4]
  have hL0 : 0 ≤ Real.log x := by linarith
  have h16 : Real.log x ^ 3 * 16 ≤ Real.log x ^ 3 * Real.log x :=
    mul_le_mul_of_nonneg_left hL16 (by positivity)
  have hL4 : (Real.log x / 2) ^ 4 = Real.log x ^ 3 * Real.log x / 16 := by ring
  calc Real.log x ^ 3 ≤ (Real.log x / 2) ^ 4 := by
        rw [hL4, le_div_iff₀ (by norm_num)]; linarith only [h16]
    _ ≤ Real.log x' ^ 4 := pow_le_pow_left₀ (by positivity) hp1 4

/-- Restricting a sum over `[⌈λ⌉, ⌊2λ⌋]` to `(lo, hi]`. -/
theorem sum_Icc_ite_Ioc {lam lo hi : ℝ} (hlo : lam ≤ lo) (hhi : hi ≤ 2 * lam) (hlam : 0 ≤ lam)
    (f G : ℕ → ℂ) :
    ∑ m ∈ Icc ⌈lam⌉₊ ⌊2 * lam⌋₊, (if m ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊ then f m else 0) * G m =
      ∑ m ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, f m * G m := by
  have hsub : Ioc ⌊lo⌋₊ ⌊hi⌋₊ ⊆ Icc ⌈lam⌉₊ ⌊2 * lam⌋₊ := by
    intro m hm
    obtain ⟨h1, h2⟩ := mem_Ioc.1 hm
    have : lo < m := (Nat.floor_lt (by linarith)).1 h1
    exact mem_Icc.2 ⟨Nat.ceil_le.2 (by linarith), h2.trans (Nat.floor_le_floor (by linarith))⟩
  rw [← sum_subset hsub fun m _ hm => by simp only [hm, ↓reduceIte, zero_mul]]
  exact sum_congr rfl fun m hm => by simp only [hm, ↓reduceIte]

/-- The conclusion of `typeII_box` at one `x`. -/
def BoxBound (q : ℝ) (K : ℕ) (c Ch Cj κ C₂ x : ℝ) : Prop :=
  ∀ (a : Fin K → ℝ) (F : ℕ → ℂ) (lam mu lo hi : ℝ) (j : ℕ) (β : ℕ → ℂ),
    (∀ i, 11 / 100 ≤ a i ∧ a i ≤ 19 / 100) →
    (∀ i i' : Fin K, i < i' → a i + 4 / 100 / K ≤ a i') →
    (∀ h, ‖F h‖ ≤ 1) → (∀ i h, ∀ p ∈ band x (a i), F (p * h) = F h) →
    x ^ presieveExponent c Ch x ≤ lam → x ^ presieveExponent c Ch x ≤ mu →
    x / κ ≤ lam * mu → lam * mu ≤ κ * x → lam ≤ lo → hi ≤ 2 * lam →
    1 ≤ j → (j : ℝ) ≤ Cj * logLogLog x + 1 →
    (∀ n, β n ≠ 0 → mu < n ∧ (n : ℝ) ≤ 2 * mu ∧
      (∀ p ∈ n.primeFactors, Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p) ∧
      ‖β n‖ ≤ Real.log x ^ (3 : ℝ)) →
    ‖∑ m ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, ∑ n ∈ Icc ⌈mu⌉₊ ⌊2 * mu⌋₊,
        (primeProxyDiff x (presieveExponent c Ch x) j m : ℂ) * β n * F (m * n - 1) *
          markedWeight Finset.univ q (fun i => band x (a i)) (m * n - 1)‖ ≤
      C₂ * (lam * mu) * Real.log x ^ (-12 : ℝ)

/-- `OneSidedTypeII` on one box, with all its premises verified. -/
theorem typeII_box (h₁ : OneSidedTypeII) {q : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (hKer : KernelPremise) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ (c Ch Cj κ : ℝ), 0 < c → 1 < κ →
      ProxyTwistPremise c Ch Cj → ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ᶠ x : ℝ in atTop,
        BoxBound q K c Ch Cj κ C₂ x := by
  obtain ⟨K₀, A₀, B, A, hTII⟩ := h₁ q 4 12 1 (21 / 200) (39 / 200) hq hq₁ (by norm_num)
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₃, hc₃, hmert⟩ := mertens_third_lower
  refine ⟨max K₀ 1, fun K hK c Ch Cj κ hc hκ hPT => ?_⟩
  have hK0 : (0 : ℝ) < K := by
    have : 1 ≤ K := le_of_max_le_right hK
    exact_mod_cast this
  obtain ⟨κp, hκp⟩ := hPT A (|A₀| + 1) 3
  obtain ⟨cG, hcG⟩ := hKer 1 B
  obtain ⟨C₁, hC₁⟩ := hTII K (le_of_max_le_left hK) (2 / 100 / K) (|κp| * 2 ^ |A|) cG
    (by positivity)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 hC₁
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1 hcG
  refine ⟨|C₁| * 2 ^ (12 : ℝ), by positivity, ?_⟩
  have hκ0 : 0 < κ := by linarith
  filter_upwards [hκp, eventually_ge_atTop (κ * max (max X₁ X₂) 1 + κ),
    eventually_le_log 16, eventually_le_log (2 * Real.log κ), eventually_le_logLog 50,
    eventually_presieveExponent_bounds c Ch hc,
    eventually_logLog_rpow_le 21 (72 / 100) (by norm_num),
    eventually_logLog_rpow_le 25 (72 / 100) (by norm_num),
    eventually_log_rpow_le_mul (24 / 100) (28 / 100) (1 / 2) (by norm_num) (by norm_num),
    eventually_le_logLog ((1 / c₃) ^ (1 / 4 : ℝ) + 1),
    eventually_le_log (2 ^ |A₀|),
    eventually_mul_log_rpow_le (2 * κ * 2 ^ |B|) |B| 1 one_pos,
    eventually_logLog_rpow_le 21 (1 / 200) (by norm_num),
    eventually_log_rpow_le_mul (1 / 200) (1 / 100) (1 / 4) (by norm_num) (by norm_num)]
    with x hκpx hxX hL16 hLκ hT50 hγb hT21 hT25 hL24 hTc₃ hLA₀ hBx hT21' hL200
  intro a F lam mu lo hi j β ha hgap hF hFinv hlam hmu hx1 hx2 hlo hhi hj1 hj2 hβ
  obtain ⟨hγlow, hγ1⟩ := hγb
  -- sizes
  have hmax1 : 1 ≤ max (max X₁ X₂) 1 := le_max_right _ _
  have hκmax : κ ≤ κ * max (max X₁ X₂) 1 := by
    have := mul_le_mul_of_nonneg_left hmax1 hκ0.le; linarith
  have hxκ : κ ≤ x := by linarith
  have hx1' : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hT0 : 0 < logLog x := by linarith
  have hγ0 : 0 < presieveExponent c Ch x := lt_of_lt_of_le (by positivity) hγlow
  have hxγ1 : 1 ≤ x ^ presieveExponent c Ch x := Real.one_le_rpow hx1'.le hγ0.le
  have hlam0 : 0 < lam := lt_of_lt_of_le (by linarith) hlam
  have hmu0 : 0 < mu := lt_of_lt_of_le (by linarith) hmu
  have hx'0 : 0 < lam * mu := by positivity
  have hx'X : max X₁ X₂ ≤ lam * mu := by
    have : max (max X₁ X₂) 1 ≤ x / κ := by
      rw [le_div_iff₀ hκ0]; linarith [mul_comm (max (max X₁ X₂) 1) κ]
    exact (le_max_left _ _).trans (this.trans hx1)
  obtain ⟨hp1, hp2⟩ := log_scale_bounds hx0 hκ hx1 hx2 hLκ
  have hLp0 : 0 < Real.log (lam * mu) := by linarith
  have hLp1' : 1 ≤ Real.log (lam * mu) := by linarith
  obtain ⟨hTp0, hρ1, hρ2⟩ := ratio_bounds hL0 hp1 hp2 hT50
  have hxx : lam * mu ≤ x ^ 2 := by
    calc lam * mu ≤ κ * x := hx2
      _ ≤ x * x := mul_le_mul_of_nonneg_right hxκ hx0.le
      _ = x ^ 2 := (sq x).symm
  have hx'γ := rpow_half_le hx0 hx'0 hxx hγ0.le
  have hγ' := log_rpow_le_half hL0 hp1 hT0 hγlow hT21' hL200
  have hexpγ := exp_le_rpow_gamma hx0 hL0 hT0 hγlow hT21
  have hexpY := exp_le_proxyCutoff hL0 hT0 hT25
  have hY2 : 2 ≤ proxyCutoff x := by
    have : (1 : ℝ) ≤ Real.log x ^ (28 / 100 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have := Real.add_one_le_exp (Real.log x ^ (28 / 100 : ℝ))
    linarith
  have hTc : 1 / c₃ ≤ logLog x ^ (4 : ℕ) := by
    have h1 : (1 / c₃) ^ (1 / 4 : ℝ) ≤ logLog x := by linarith
    calc 1 / c₃ = ((1 / c₃) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      _ ≤ logLog x ^ (4 : ℕ) := pow_le_pow_left₀ (by positivity) h1 _
  have hprodY := one_le_prod_mul hc₃ hmert (by linarith) hT0 hγlow hY2 hTc
  have hdiff : ∀ m, |primeProxyDiff x (presieveExponent c Ch x) j m| ≤ 1 := by
    intro m
    obtain ⟨h0, h1⟩ := unstrippedProxy_le_one hx1' (by linarith) hγ0 hj1 hprodY m
    unfold primeProxyDiff
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  -- the rescaled exponents
  set a' : Fin K → ℝ := fun i => a i * (logLog x / Real.log (Real.log (lam * mu))) with ha'def
  have hband : ∀ i, band (lam * mu) (a' i) = band x (a i) := fun i =>
    band_rescale hL0 hLp0 hTp0.ne' (a i)
  have ha' : ∀ i, 21 / 200 ≤ a' i ∧ a' i ≤ 39 / 200 := fun i =>
    rescale_window hρ1 hρ2 (ha i).1 (ha i).2
  have hgap' : ∀ i i' : Fin K, i < i' → a' i + 2 / 100 / K ≤ a' i' := fun i i' h =>
    rescale_gap hK0 hρ1 (hgap i i' h)
  -- the coefficient on `[λ, 2λ]`
  set α : ℕ → ℂ := fun m => if m ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊ then
    (primeProxyDiff x (presieveExponent c Ch x) j m : ℂ) else 0 with hαdef
  have hα : ∀ m, α m ≠ 0 → lam ≤ m ∧ (m : ℝ) ≤ 2 * lam ∧ IsRough (lam * mu) m ∧
      ‖α m‖ ≤ Real.log (lam * mu) ^ (4 : ℝ) := by
    intro m hm
    have hmI : m ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊ := by
      by_contra h
      exact hm (by simp only [hαdef, h, ↓reduceIte])
    have hαm : α m = (primeProxyDiff x (presieveExponent c Ch x) j m : ℂ) := by
      simp only [hαdef, hmI, ↓reduceIte]
    rw [hαm] at hm ⊢
    have hd : primeProxyDiff x (presieveExponent c Ch x) j m ≠ 0 := fun h =>
      hm (by rw [h, Complex.ofReal_zero])
    obtain ⟨h1, h2⟩ := mem_Ioc.1 hmI
    have hlom : lo < m := (Nat.floor_lt (by linarith)).1 h1
    have hmhi : (m : ℝ) ≤ hi := (Nat.le_floor_iff' (by omega)).1 h2
    refine ⟨by linarith, by linarith, fun p hp => roughLevel_lt hL0 hp2 hLp0 hL24
      (primeFactors_ge_of_primeProxyDiff (by linarith) hexpγ hexpY hd p hp), ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hdiff m).trans (Real.one_le_rpow hLp1' (by norm_num))
  have hlamx : lam ≤ x ^ (3 : ℝ) := by
    have hmu1 : 1 ≤ mu := hxγ1.trans hmu
    have : lam ≤ lam * mu := le_mul_of_one_le_right hlam0.le hmu1
    have hx23 : x ^ (2 : ℕ) ≤ x ^ (3 : ℕ) := pow_le_pow_right₀ hx1'.le (by norm_num)
    calc lam ≤ x ^ (2 : ℕ) := this.trans hxx
      _ ≤ x ^ (3 : ℕ) := hx23
      _ = x ^ (3 : ℝ) := by norm_cast
  have hH : x ^ presieveExponent c Ch x / 2 ≤ lam := by
    have : 0 ≤ x ^ presieveExponent c Ch x := by positivity
    linarith
  have hBx' : 2 * κ * 2 ^ |B| * Real.log x ^ |B| ≤ x := by
    have := hBx; rwa [Real.rpow_one] at this
  have hP4' := box_P4 hκpx hκ0 hx1' hL0 hp1 hp2 hLp1' hLA₀ hBx' hx2 hlamx hH hlo hhi hj1 hj2
  have hP4 : ∀ (k : ℕ), 1 ≤ k → (k : ℝ) ≤ Real.log (lam * mu) ^ A₀ →
      ∀ (χ : DirichletCharacter ℂ k) (t : ℝ), |t| ≤ 2 * (lam * mu) * Real.log (lam * mu) ^ B →
      ‖(lam : ℂ)⁻¹ * ∑ m ∈ Icc ⌈lam⌉₊ ⌊2 * lam⌋₊, α m * χ m * (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
        |κp| * 2 ^ |A| * Real.log (lam * mu) ^ (-A) := by
    intro k hk1 hk χ t ht
    have hsum : ∑ m ∈ Icc ⌈lam⌉₊ ⌊2 * lam⌋₊, α m * χ m * (m : ℂ) ^ ((t : ℂ) * Complex.I) =
        ∑ m ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, χ m * (m : ℂ) ^ ((t : ℂ) * Complex.I) *
          (((if m.Prime ∧ x ^ presieveExponent c Ch x < m then 1 else 0 : ℝ) : ℂ) -
            (unstrippedProxy x (presieveExponent c Ch x) j m : ℂ)) := by
      simp only [mul_assoc]
      rw [sum_Icc_ite_Ioc hlo hhi hlam0.le]
      refine sum_congr rfl fun m _ => ?_
      simp only [primeProxyDiff, Complex.ofReal_sub]
      ring
    rw [hsum]
    exact hP4' k hk1 hk χ t ht
  -- the companion and the kernel premise at `x'`
  have hβ' : ∀ n, β n ≠ 0 → mu ≤ n ∧ (n : ℝ) ≤ 2 * mu ∧ IsRough (lam * mu) n ∧
      ‖β n‖ ≤ Real.log (lam * mu) ^ (4 : ℝ) := by
    intro n hn
    obtain ⟨h1, h2, h3, h4⟩ := hβ n hn
    exact ⟨h1.le, h2, fun p hp => roughLevel_lt hL0 hp2 hLp0 hL24 (h3 p hp),
      h4.trans (log_cube_le hL16 hp1)⟩
  have hHm := hx'γ.trans hlam
  have hHn := hx'γ.trans hmu
  have hker := hX₂ (lam * mu) ((le_max_right _ _).trans hx'X) (presieveExponent c Ch x / 2)
    lam mu hγ' hHm hHn (by rw [one_mul])
  have hFinv' : ∀ i h, ∀ p ∈ band (lam * mu) (a' i), F (p * h) = F h := by
    intro i h p hp; rw [hband i] at hp; exact hFinv i h p hp
  have key := hX₁ (lam * mu) ((le_max_left _ _).trans hx'X) a' (presieveExponent c Ch x / 2)
    lam mu F α β ha' hgap' hγ' hHm hHn (by rw [div_one]) (by rw [one_mul]) hF hFinv' hα hP4
    hβ' hker
  have hW : (fun i => band (lam * mu) (a' i)) = fun i => band x (a i) := funext hband
  rw [hW] at key
  have hconv : ∑ m ∈ Icc ⌈lam⌉₊ ⌊2 * lam⌋₊, ∑ n ∈ Icc ⌈mu⌉₊ ⌊2 * mu⌋₊,
      α m * β n * F (m * n - 1) *
        (markedWeight Finset.univ q (fun i => band x (a i)) (m * n - 1) : ℂ) =
      ∑ m ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, ∑ n ∈ Icc ⌈mu⌉₊ ⌊2 * mu⌋₊,
        (primeProxyDiff x (presieveExponent c Ch x) j m : ℂ) * β n * F (m * n - 1) *
          (markedWeight Finset.univ q (fun i => band x (a i)) (m * n - 1) : ℂ) := by
    simp only [mul_assoc]
    simp only [← mul_sum]
    exact sum_Icc_ite_Ioc hlo hhi hlam0.le _ _
  rw [hconv] at key
  have hLp12 : Real.log (lam * mu) ^ (-12 : ℝ) ≤ 2 ^ (12 : ℝ) * Real.log x ^ (-12 : ℝ) := by
    have := rpow_le_of_near hL0 hp1 (by linarith) (-12)
    rwa [show |(-12 : ℝ)| = 12 by norm_num] at this
  have hLp0' : 0 ≤ Real.log (lam * mu) ^ (-12 : ℝ) := by positivity
  calc _ ≤ C₁ * (lam * mu) * Real.log (lam * mu) ^ (-12 : ℝ) := key
    _ ≤ |C₁| * (lam * mu) * Real.log (lam * mu) ^ (-12 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hx'0.le) hLp0'
    _ ≤ |C₁| * (lam * mu) * (2 ^ (12 : ℝ) * Real.log x ^ (-12 : ℝ)) :=
        mul_le_mul_of_nonneg_left hLp12 (by positivity)
    _ = _ := by ring

end Erdos408.TypeII
