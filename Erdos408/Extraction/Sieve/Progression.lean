module

public import Erdos408.Extraction.Sieve.Kubilius
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The progression lemma for the inert polynomial (E1)

PD Lemma 7.2 at the shrinking parameters of `blueprint/rectangle_input.md` §4:
for every function `H` of the band primes dividing `u` with `|H| ≤ 1` (in
particular `H ∈ {P, 1 - P}`), every family of long moduli `ℓ_i` whose prime
factors exceed `x^ε` with `#S ≤ x^{1-ε}` and `∑ 1/ℓ_i ≤ L`, and `|b_i| ≤ 1`,

  `∑_{r ≤ x^{ε/4}} |∑_{r ∣ u+1} Φ(u/x) (∑_{ℓ_i ∣ u} b_i) H(u)
      - (x/r) I (∑ b_i / ℓ_i) M_x(H)| ≪ x / L²`,

with the cutoff mass `I = x⁻¹ ∑_{u ≤ κ x} Φ(u/x)`. The proof applies the
independent divisor model of `Erdos408.Extraction.Sieve.Kubilius` with the
band primes `p ≤ m = exp(2 L^{1/5})`, the depth `h = 2 ⌈L^{1/10}⌉ + O(1)`,
and `Y₀ = x^{ε/4}`:

* `e^{-h}`, `∑_{p ∣ r, p band} 1/p ≤ L exp(-L^{0.11})` and the Rankin tail
  `exp(-c L^{0.8} / (8 T²⁰) + e T)` are all `≤ L⁻⁶`;
* the remainders cost `x^{1-ε/2} m^{O(h)} T^{O(1)} ≤ x / L²`.

The slot statistic is the family of slot tuples with `ℓ = ∏ Q`, and the
constant `1` is the family with the single modulus `ℓ = 1`.

`sum_powerset_rem_le` converts the bound to the sum over sets of sieving
primes that `BlockSieve` requires.
-/

@[expose] public section

namespace Erdos408

open Filter Real Finset

namespace Sieve

noncomputable section

/-- The cutoff mass `I = x⁻¹ ∑_{1 ≤ u ≤ κ x} Φ(u/x)`, a Riemann sum for `∫ Φ`. -/
def cutoffMass (κ x : ℝ) (Φ : ℝ → ℝ) : ℝ :=
  (∑ n ∈ Icc 1 ⌊κ * x⌋₊, Φ (n / x)) / x

/-- A cutoff is bounded by `M₀`. -/
lemma abs_le_of_isCutoff {κ CΦ : ℝ} {M : ℕ → ℝ} {x : ℝ} {Φ : ℝ → ℝ}
    (hΦ : IsCutoff κ CΦ M x Φ) (y : ℝ) : |Φ y| ≤ M 0 := by
  have := hΦ.2.2.2 0 y
  rwa [iteratedDeriv_zero, Nat.cast_zero, mul_zero, rpow_zero, mul_one] at this

/-- The mass of a cutoff is nonnegative. -/
lemma cutoffMass_nonneg {κ CΦ : ℝ} {M : ℕ → ℝ} {x : ℝ} {Φ : ℝ → ℝ} (hx : 0 < x)
    (hΦ : IsCutoff κ CΦ M x Φ) : 0 ≤ cutoffMass κ x Φ :=
  div_nonneg (sum_nonneg fun _ _ => hΦ.2.1 _) hx.le

/-- The mass of a cutoff is at most `κ M₀`. -/
lemma cutoffMass_le {κ CΦ : ℝ} {M : ℕ → ℝ} {x : ℝ} {Φ : ℝ → ℝ} (hκ : 1 < κ) (hx : 0 < x)
    (hΦ : IsCutoff κ CΦ M x Φ) : cutoffMass κ x Φ ≤ κ * M 0 := by
  have hM : 0 ≤ M 0 := (abs_nonneg _).trans (abs_le_of_isCutoff hΦ 0)
  rw [cutoffMass, div_le_iff₀ hx]
  calc ∑ n ∈ Icc 1 ⌊κ * x⌋₊, Φ (n / x) ≤ ∑ _n ∈ Icc 1 ⌊κ * x⌋₊, M 0 :=
        sum_le_sum fun n _ => (le_abs_self _).trans (abs_le_of_isCutoff hΦ _)
    _ = ⌊κ * x⌋₊ * M 0 := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ κ * x * M 0 := mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) hM
    _ = κ * M 0 * x := by ring

/-! ### The parameters of E1 -/

/-- `∑_{r ≤ R} 1/r ≤ 1 + log R`. -/
lemma sum_Icc_inv_le (R : ℕ) : ∑ r ∈ Icc 1 R, (1 : ℝ) / r ≤ 1 + Real.log R := by
  have h := harmonic_le_one_add_log R
  have he : ∀ n : ℕ, ((harmonic n : ℚ) : ℝ) = ∑ r ∈ Icc 1 n, (1 : ℝ) / r := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [harmonic_succ, sum_Icc_succ_top (by omega), ← ih]
      push_cast
      ring
  rw [← he R]
  exact h

/-- A number `r ≤ x` has at most `L` prime factors above `exp(L^{0.11})`, so the band primes
dividing it have reciprocal mass at most `L exp(-L^{0.11})`. -/
lemma sum_inv_dvd_le {𝔅 : Finset ℕ} {x : ℝ} (hx : 1 < x) (hL1 : 1 ≤ Real.log x)
    (h𝔅 : ∀ p ∈ 𝔅, p.Prime ∧ exp (Real.log x ^ (11 / 100 : ℝ)) ≤ p) {r : ℕ} (hr : 0 < r)
    (hrx : (r : ℝ) ≤ x) :
    ∑ p ∈ 𝔅.filter (· ∣ r), (1 : ℝ) / p ≤
      Real.log x * exp (-Real.log x ^ (11 / 100 : ℝ)) := by
  set F := 𝔅.filter (· ∣ r)
  set q := exp (Real.log x ^ (11 / 100 : ℝ))
  have hL : 0 < Real.log x := Real.log_pos hx
  have hq : 0 < q := exp_pos _
  have hFp : ∀ p ∈ F, p.Prime := fun p hp => (h𝔅 p (mem_filter.1 hp).1).1
  -- `q^{#F} ≤ ∏ F ≤ r ≤ x`
  have hdvd : ∏ p ∈ F, p ∣ r := prod_primes_dvd r (fun p hp => (hFp p hp).prime)
    fun p hp => (mem_filter.1 hp).2
  have hle : (∏ p ∈ F, (p : ℝ)) ≤ x := by
    have : ((∏ p ∈ F, p : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.le_of_dvd hr hdvd
    push_cast at this
    linarith
  have hlo : q ^ #F ≤ ∏ p ∈ F, (p : ℝ) := by
    rw [← prod_const]
    exact prod_le_prod₀ (fun _ _ => hq.le) fun p hp => (h𝔅 p (mem_filter.1 hp).1).2
  have hcard : (#F : ℝ) ≤ Real.log x := by
    have h1 : (#F : ℝ) * Real.log x ^ (11 / 100 : ℝ) ≤ Real.log x := by
      have := Real.log_le_log (by positivity) (hlo.trans hle)
      rwa [Real.log_pow, Real.log_exp] at this
    have h2 : 1 ≤ Real.log x ^ (11 / 100 : ℝ) := one_le_rpow hL1 (by norm_num)
    nlinarith [(Nat.cast_nonneg #F : (0 : ℝ) ≤ #F)]
  calc ∑ p ∈ F, (1 : ℝ) / p ≤ ∑ _p ∈ F, 1 / q := sum_le_sum fun p hp => by
        have := (h𝔅 p (mem_filter.1 hp).1).2
        exact one_div_le_one_div_of_le hq this
    _ = #F * (1 / q) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ Real.log x * (1 / q) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [exp_neg, one_div]

/-- A nonnegative sum over a union is at most the sum of the sums. -/
lemma sum_biUnion_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → Finset ℕ)
    (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) : ∑ p ∈ s.biUnion t, g p ≤ ∑ i ∈ s, ∑ p ∈ t i, g p := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [biUnion_insert, sum_insert hi]
    have h := sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := g)
    have h0 : 0 ≤ ∑ p ∈ t i ∩ s.biUnion t, g p := sum_nonneg fun p _ => hg p
    linarith

/-- For large `x`, the inert band primes lie in `[exp(L^{0.11}), exp(2 L^{1/5})]` and have
reciprocal mass at most `T`. -/
lemma eventually_inertBands_bounds {K : ℕ} (hK : 1 ≤ K) (CN : ℝ) : ∀ᶠ x : ℝ in atTop,
    (∀ p ∈ inertBands K CN x, p.Prime ∧ exp (Real.log x ^ (11 / 100 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ exp (2 * Real.log x ^ (1 / 5 : ℝ))) ∧
    ∑ p ∈ inertBands K CN x, (1 : ℝ) / p ≤ logLog x := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  filter_upwards [eventually_inertExponent_mem hK CN, eventually_harmonicMass_inert hK CN,
    tendsto_log_atTop.eventually_ge_atTop 1, eventually_mul_logLogLog_le (|CN| + K),
    tendsto_logLog.eventually_ge_atTop 1]
    with x ha hV hL hT hT1
  have hs0 : 0 ≤ logLogLog x := by
    rw [logLogLog]
    exact log_nonneg hT1
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨ci, hci, hpb⟩ := mem_biUnion.1 hp
    obtain ⟨hc, hi⟩ := mem_product.1 hci
    obtain ⟨ha1, ha2⟩ := ha ci.1 (mem_range.1 hc) ci.2 (mem_range.1 hi)
    obtain ⟨hlo, hhi⟩ := le_of_mem_band hpb
    refine ⟨prime_of_mem_band hpb, le_trans (exp_le_exp.2 ?_) hlo, hhi.trans (exp_le_exp.2 ?_)⟩
    · exact rpow_le_rpow_of_exponent_le hL ha1
    · have := rpow_le_rpow_of_exponent_le hL ha2
      linarith
  · refine (sum_biUnion_le_sum _ _ _ fun p => by positivity).trans ?_
    calc ∑ ci ∈ range K ×ˢ range (inertPerCluster K CN x),
          ∑ p ∈ band x (inertExponent K x ci.1 ci.2), (1 : ℝ) / p
        ≤ ∑ _ci ∈ range K ×ˢ range (inertPerCluster K CN x), (1 : ℝ) := sum_le_sum fun ci hci => by
          obtain ⟨hc, hi⟩ := mem_product.1 hci
          exact (hV ci.1 (mem_range.1 hc) ci.2 (mem_range.1 hi)).2
      _ = K * inertPerCluster K CN x := by
          rw [sum_const, card_product, card_range, card_range, nsmul_one]
          push_cast
          ring
      _ ≤ K * (|CN| / K * logLogLog x + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0.le
          have := Nat.ceil_lt_add_one (show 0 ≤ |CN| * logLogLog x / K by positivity)
          have h1 : (inertPerCluster K CN x : ℝ) ≤ ⌈|CN| * logLogLog x / K⌉₊ := by
            exact_mod_cast Nat.ceil_mono (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_abs_self CN) hs0) hK0.le)
          have h2 : |CN| * logLogLog x / K = |CN| / K * logLogLog x := by ring
          linarith
      _ = |CN| * logLogLog x + K := by field_simp
      _ ≤ (|CN| + K) * (logLogLog x + 1) := by
          have := mul_nonneg (abs_nonneg CN) hs0
          have := mul_nonneg hK0.le hs0
          nlinarith [abs_nonneg CN]
      _ ≤ logLog x := hT

/-- The savings of E1 at large `x`, with `ε = c / T²⁰`, `m = exp(2 L^{1/5})`,
`h = 2 (⌈L^{1/10}⌉ + h₀)` and `Y₀ = x^{ε/4}`: the relative errors are at most `L⁻⁵` and the
remainders at most `x / L²`. -/
lemma eventually_progression_savings {c : ℝ} (hc : 0 < c) (h₀ : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop,
      exp (2 * Real.log x ^ (1 / 5 : ℝ)) < x ^ (c / logLog x ^ 20) ∧
      A * exp (-((2 * (⌈Real.log x ^ (1 / 10 : ℝ)⌉₊ + h₀) : ℕ) : ℝ)) +
          2 * (Real.log x * exp (-Real.log x ^ (11 / 100 : ℝ))) +
          2 * exp (-(Real.log (x ^ (c / logLog x ^ 20 / 4)) /
            Real.log (exp (2 * Real.log x ^ (1 / 5 : ℝ)))) + exp 1 * logLog x) ≤
        (Real.log x ^ 5)⁻¹ ∧
      x ^ (c / logLog x ^ 20 / 4) * x ^ (1 - c / logLog x ^ 20) *
          (x ^ (c / logLog x ^ 20 / 4) *
            (A * (exp (2 * Real.log x ^ (1 / 5 : ℝ)) ^
              (4 * (2 * (⌈Real.log x ^ (1 / 10 : ℝ)⌉₊ + h₀)) + 2) * Real.log x ^ (1 / 10 : ℝ)) +
              A * exp (2 * Real.log x ^ (1 / 5 : ℝ)))) ≤
        x / Real.log x ^ 2 := by
  have hpow : ∀ (y : ℝ) (n : ℕ), y ^ (n : ℝ) = y ^ n := fun y n => rpow_natCast y n
  filter_upwards [eventually_gt_atTop 1, tendsto_log_atTop.eventually_ge_atTop (A + 4),
    tendsto_log_atTop.eventually_ge_atTop 1, tendsto_logLog.eventually_ge_atTop (max c 1),
    eventually_mul_rpow_le_log_rpow (4 / c) 20 (show (0 : ℝ) < 4 / 5 by norm_num),
    eventually_mul_rpow_le_log_rpow 3 1 (show (0 : ℝ) < 1 / 10 by norm_num),
    eventually_mul_rpow_le_log_rpow 7 1 (show (0 : ℝ) < 11 / 100 by norm_num),
    eventually_mul_rpow_le_log_rpow (72 / c) 21 (show (0 : ℝ) < 4 / 5 by norm_num),
    eventually_mul_rpow_le_log_rpow 3 1 (show (0 : ℝ) < 3 / 10 by norm_num),
    eventually_mul_rpow_le_log_rpow (2 * (16 * h₀ + 38) / c) 20 (show (0 : ℝ) < 7 / 10 by norm_num),
    (tendsto_rpow_atTop (show (0 : ℝ) < 3 / 10 by norm_num)).comp tendsto_log_atTop
      |>.eventually_ge_atTop (Real.log (2 * A + 1))]
    with x hx hLA hL1 hT hS1 hS2a hS2b hS2c hS3a hS3b hS3c
  set L := Real.log x
  set T := logLog x
  have hL0 : 0 < L := by linarith
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  have hTc : c ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := by linarith
  rw [rpow_one] at hS2a hS2b hS3a
  have hT20 : 0 < T ^ (20 : ℝ) := by positivity
  set ε := c / T ^ 20
  have hεT : ε = c / T ^ (20 : ℝ) := by rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, hpow]
  have hε0 : 0 < ε := by positivity
  have hexpT : ∀ k : ℝ, exp (-(k * T)) = (L ^ k)⁻¹ := fun k => by
    rw [exp_neg, log_rpow_eq hL0]
  -- `m < x^ε`
  have hL15 : L ^ (1 / 5 : ℝ) * L ^ (4 / 5 : ℝ) = L := by
    rw [← rpow_add hL0]
    norm_num
  have hxε : x ^ ε = exp (ε * L) := by rw [rpow_def_of_pos hx0, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · rw [hxε]
    refine exp_lt_exp.2 ?_
    rw [hεT, div_mul_eq_mul_div, lt_div_iff₀ hT20]
    have h1 : 4 * T ^ (20 : ℝ) ≤ c * L ^ (4 / 5 : ℝ) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hS1
      linarith
    have h2 : 0 < L ^ (1 / 5 : ℝ) := by positivity
    nlinarith
  · -- the relative errors are each at most `L⁻⁶`
    have hh : 2 * L ^ (1 / 10 : ℝ) ≤ ((2 * (⌈L ^ (1 / 10 : ℝ)⌉₊ + h₀) : ℕ) : ℝ) := by
      push_cast
      have := Nat.le_ceil (L ^ (1 / 10 : ℝ))
      have : (0 : ℝ) ≤ h₀ := Nat.cast_nonneg _
      linarith
    have e1 : exp (-((2 * (⌈L ^ (1 / 10 : ℝ)⌉₊ + h₀) : ℕ) : ℝ)) ≤ (L ^ (6 : ℝ))⁻¹ := by
      rw [← hexpT]
      exact exp_le_exp.2 (by linarith)
    have e2 : L * exp (-L ^ (11 / 100 : ℝ)) ≤ (L ^ (6 : ℝ))⁻¹ := by
      have : exp (-L ^ (11 / 100 : ℝ)) ≤ (L ^ (7 : ℝ))⁻¹ := by
        rw [← hexpT]
        exact exp_le_exp.2 (by linarith)
      calc L * exp (-L ^ (11 / 100 : ℝ)) ≤ L * (L ^ (7 : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_left this hL0.le
        _ = (L ^ (6 : ℝ))⁻¹ := by
            rw [show (7 : ℝ) = 6 + 1 by norm_num, rpow_add hL0, rpow_one]
            field_simp
    have e3 : exp (-(Real.log (x ^ (ε / 4)) / Real.log (exp (2 * L ^ (1 / 5 : ℝ)))) +
        exp 1 * T) ≤ (L ^ (6 : ℝ))⁻¹ := by
      rw [← hexpT, Real.log_rpow hx0, Real.log_exp]
      refine exp_le_exp.2 ?_
      have he : exp 1 < 3 := exp_one_lt_three
      have h2 : 0 < L ^ (1 / 5 : ℝ) := by positivity
      have key : c * L ^ (4 / 5 : ℝ) / (8 * T ^ (20 : ℝ)) * (2 * L ^ (1 / 5 : ℝ)) = ε / 4 * L := by
        rw [hεT]
        conv_rhs => rw [← hL15]
        field_simp
        ring
      have h1 : ε / 4 * L / (2 * L ^ (1 / 5 : ℝ)) = c * L ^ (4 / 5 : ℝ) / (8 * T ^ (20 : ℝ)) := by
        rw [← key]
        field_simp
      rw [h1]
      have h2 : 9 * T * (8 * T ^ (20 : ℝ)) ≤ c * L ^ (4 / 5 : ℝ) := by
        have h3 : T * T ^ (20 : ℝ) = T ^ (21 : ℝ) := by
          rw [show (21 : ℝ) = 1 + 20 by norm_num, rpow_add hT0, rpow_one]
        rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hS2c
        have : 9 * T * (8 * T ^ (20 : ℝ)) = 72 * T ^ (21 : ℝ) := by rw [← h3]; ring
        rw [this, mul_comm c]
        exact hS2c
      have h4 : 9 * T ≤ c * L ^ (4 / 5 : ℝ) / (8 * T ^ (20 : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        exact h2
      nlinarith [exp_pos 1]
    have hL6 : (A + 4) * (L ^ (6 : ℝ))⁻¹ ≤ (L ^ 5)⁻¹ := by
      rw [show (6 : ℝ) = ((5 : ℕ) : ℝ) + 1 by norm_num, rpow_add hL0, hpow, rpow_one, mul_inv,
        ← mul_assoc, mul_comm (A + 4), mul_assoc]
      refine mul_le_of_le_one_right (by positivity) ?_
      rw [mul_inv_le_iff₀ hL0, one_mul]
      exact hLA
    have hA' : A * exp (-((2 * (⌈L ^ (1 / 10 : ℝ)⌉₊ + h₀) : ℕ) : ℝ)) ≤ A * (L ^ (6 : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left e1 hA
    nlinarith
  · -- the remainders: `x^{1-ε/2} (2A+1) m^{4h+2} L^{2.1} ≤ x`
    set h := 2 * (⌈L ^ (1 / 10 : ℝ)⌉₊ + h₀)
    set m := exp (2 * L ^ (1 / 5 : ℝ))
    have hL10 : 1 ≤ L ^ (1 / 10 : ℝ) := one_le_rpow hL1 (by norm_num)
    have hm1 : 1 ≤ m := one_le_exp (by positivity)
    have hW : A * (m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ)) + A * m ≤
        (2 * A + 1) * (m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ)) := by
      have h1 : m ≤ m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ) := by
        calc m = m ^ 1 * 1 := by ring
          _ ≤ m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ) :=
            mul_le_mul (pow_le_pow_right₀ hm1 (by omega)) hL10 zero_le_one (by positivity)
      have h2 : 0 ≤ m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ) := by positivity
      nlinarith
    -- the exponent of `m^{4h+2}`
    have hh : (h : ℝ) ≤ 2 * (L ^ (1 / 10 : ℝ) + 1 + h₀) := by
      have := Nat.ceil_lt_add_one (show 0 ≤ L ^ (1 / 10 : ℝ) by positivity)
      simp only [h]
      push_cast
      linarith
    have hL3 : L ^ (1 / 10 : ℝ) * L ^ (1 / 5 : ℝ) = L ^ (3 / 10 : ℝ) := by
      rw [← rpow_add hL0]
      norm_num
    have hL23 : L ^ (1 / 5 : ℝ) ≤ L ^ (3 / 10 : ℝ) := rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hmexp : m ^ (4 * h + 2) = exp (((4 * h + 2 : ℕ) : ℝ) * (2 * L ^ (1 / 5 : ℝ))) := by
      rw [← exp_nat_mul]
    have hexp1 : ((4 * h + 2 : ℕ) : ℝ) * (2 * L ^ (1 / 5 : ℝ)) ≤
        (16 * h₀ + 36) * L ^ (3 / 10 : ℝ) := by
      push_cast
      have h0 : (0 : ℝ) ≤ h₀ := Nat.cast_nonneg _
      have h5 : 0 ≤ L ^ (1 / 5 : ℝ) := by positivity
      nlinarith
    -- `2A + 1 ≤ exp(L^{0.3})` and `L^{2.1} ≤ exp(L^{0.3})`
    have hA1 : 2 * A + 1 ≤ exp (L ^ (3 / 10 : ℝ)) := by
      have : Real.log (2 * A + 1) ≤ L ^ (3 / 10 : ℝ) := hS3c
      calc 2 * A + 1 = exp (Real.log (2 * A + 1)) := (exp_log (by linarith)).symm
        _ ≤ _ := exp_le_exp.2 this
    have hL21 : L ^ (1 / 10 : ℝ) * L ^ 2 ≤ exp (L ^ (3 / 10 : ℝ)) := by
      have e : L ^ (1 / 10 : ℝ) * L ^ 2 = exp ((21 / 10) * T) := by
        rw [← log_rpow_eq hL0, ← rpow_natCast, ← rpow_add hL0]
        norm_num
        rfl
      rw [e]
      exact exp_le_exp.2 (by linarith)
    -- the total exponent is at most `ε L / 2`
    have hfin : (16 * h₀ + 38) * L ^ (3 / 10 : ℝ) ≤ ε * L / 2 := by
      have h1 : L ^ (3 / 10 : ℝ) * L ^ (7 / 10 : ℝ) = L := by
        rw [← rpow_add hL0]
        norm_num
      rw [hεT]
      rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hS3b
      rw [div_mul_eq_mul_div, div_div, le_div_iff₀ (by positivity)]
      have h0 : (0 : ℝ) ≤ h₀ := Nat.cast_nonneg _
      have h3 : 0 ≤ L ^ (3 / 10 : ℝ) := by positivity
      calc (16 * h₀ + 38) * L ^ (3 / 10 : ℝ) * (T ^ (20 : ℝ) * 2) =
            L ^ (3 / 10 : ℝ) * (2 * (16 * h₀ + 38) * T ^ (20 : ℝ)) := by ring
        _ ≤ L ^ (3 / 10 : ℝ) * (L ^ (7 / 10 : ℝ) * c) := mul_le_mul_of_nonneg_left hS3b h3
        _ = c * L := by rw [← mul_assoc, h1]; ring
    -- assemble
    have hx' : x ^ (ε / 4) * x ^ (1 - ε) * x ^ (ε / 4) * exp (ε * L / 2) = x := by
      rw [← rpow_add hx0, ← rpow_add hx0, rpow_def_of_pos hx0, ← exp_add]
      rw [show L * (ε / 4 + (1 - ε) + ε / 4) + ε * L / 2 = L by ring, exp_log hx0]
    have hbig : (2 * A + 1) * (m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ)) * L ^ 2 ≤ exp (ε * L / 2) := by
      calc (2 * A + 1) * (m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ)) * L ^ 2 =
            (2 * A + 1) * m ^ (4 * h + 2) * (L ^ (1 / 10 : ℝ) * L ^ 2) := by ring
        _ ≤ exp (L ^ (3 / 10 : ℝ)) * exp ((16 * h₀ + 36) * L ^ (3 / 10 : ℝ)) *
            exp (L ^ (3 / 10 : ℝ)) := by
          rw [hmexp]
          refine mul_le_mul (mul_le_mul hA1 (exp_le_exp.2 hexp1) (exp_pos _).le (exp_pos _).le)
            hL21 (by positivity) (by positivity)
        _ = exp ((16 * h₀ + 38) * L ^ (3 / 10 : ℝ)) := by
          rw [← exp_add, ← exp_add]
          ring_nf
        _ ≤ exp (ε * L / 2) := exp_le_exp.2 hfin
    have hxe : 0 < exp (ε * L / 2) := exp_pos _
    have hY : 0 ≤ x ^ (ε / 4) * x ^ (1 - ε) * x ^ (ε / 4) := by positivity
    rw [le_div_iff₀ (by positivity)]
    calc x ^ (ε / 4) * x ^ (1 - ε) * (x ^ (ε / 4) * (A * (m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ)) +
          A * m)) * L ^ 2
        ≤ x ^ (ε / 4) * x ^ (1 - ε) * x ^ (ε / 4) *
          ((2 * A + 1) * (m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ)) * L ^ 2) := by
          rw [show x ^ (ε / 4) * x ^ (1 - ε) * (x ^ (ε / 4) * (A * (m ^ (4 * h + 2) *
            L ^ (1 / 10 : ℝ)) + A * m)) * L ^ 2 = x ^ (ε / 4) * x ^ (1 - ε) * x ^ (ε / 4) *
            ((A * (m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ)) + A * m) * L ^ 2) by ring]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hW (by positivity)) hY
      _ ≤ x ^ (ε / 4) * x ^ (1 - ε) * x ^ (ε / 4) * exp (ε * L / 2) :=
          mul_le_mul_of_nonneg_left hbig hY
      _ = x := hx'

/-- E1, the progression lemma for the inert polynomial (PD Lemma 7.2 at the
shrinking parameters). For every `H` determined by the band primes with
`|H| ≤ 1`, every family of moduli `ℓ_i` with prime factors above `x^ε`,
`#S ≤ x^{1-ε}` and `∑ 1/ℓ_i ≤ L`, and `|b_i| ≤ 1`, the progression sums at
levels `r ≤ x^{ε/4}` match the independent divisor model up to `O(x / L²)` in
total. -/
theorem eventually_progression (h₃ : BlockSieve) {K : ℕ} (hK : 1 ≤ K) (CN c κ CΦ : ℝ)
    (M : ℕ → ℝ) (hc : 0 < c) (hκ : 1 < κ) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ (ι : Type) (S : Finset ι) (ℓ : ι → ℕ) (b : ι → ℝ)
      (Φ : ℝ → ℝ) (H : ℕ → ℝ),
      IsCutoff κ CΦ M x Φ →
      (∀ i ∈ S, 0 < ℓ i ∧ ∀ p ∈ (ℓ i).primeFactors, x ^ (c / logLog x ^ 20) < p) →
      (#S : ℝ) ≤ x ^ (1 - c / logLog x ^ 20) →
      ∑ i ∈ S, (1 : ℝ) / ℓ i ≤ Real.log x →
      (∀ i ∈ S, |b i| ≤ 1) →
      (∀ n, |H n| ≤ 1) →
      (∀ n, H n = H (bandPart (inertBands K CN x) n)) →
      ∑ r ∈ Icc 1 ⌊x ^ (c / logLog x ^ 20 / 4)⌋₊,
        |∑ u ∈ (Icc 1 ⌊κ * x⌋₊).filter (r ∣ · + 1),
            Φ (u / x) * (∑ i ∈ S with ℓ i ∣ u, b i) * H u -
          x / r * cutoffMass κ x Φ * (∑ i ∈ S, b i / ℓ i) * divisorModel (inertBands K CN x) H| ≤
        C * x / Real.log x ^ 2 := by
  obtain ⟨h₀, KB, hBS⟩ := exists_dvdSieve h₃
  refine ⟨2 * κ * |M 0| + 1, ?_⟩
  filter_upwards [eventually_inertBands_bounds hK CN,
    eventually_progression_savings hc h₀ (A := |KB| + |M 0|) (by positivity),
    eventually_mul_rpow_le_log_rpow (κ * |M 1|) |CΦ| (show (0 : ℝ) < 1 / 10 by norm_num),
    eventually_ge_atTop 2, tendsto_log_atTop.eventually_ge_atTop 1,
    tendsto_logLog.eventually_ge_atTop (max c 1)]
    with x ⟨h𝔅, hV𝔅⟩ ⟨hmx, hδ, hrem⟩ hVL hx2 hL hT ι S ℓ b Φ H hΦ hℓ hS hΛ hb hH hHb
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hT1 : 1 ≤ logLog x := (le_max_right _ _).trans hT
  set L := Real.log x
  set T := logLog x
  set ε := c / T ^ 20
  set m := exp (2 * L ^ (1 / 5 : ℝ))
  set h := 2 * (⌈L ^ (1 / 10 : ℝ)⌉₊ + h₀)
  set Y₀ := x ^ (ε / 4)
  set R := ⌊Y₀⌋₊
  set N := ⌊κ * x⌋₊
  set 𝔅 := inertBands K CN x
  set f : ℕ → ℝ := fun u => Φ (u / x)
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact (le_max_left _ _).trans (hT.trans (le_self_pow₀ hT1 (by norm_num)))
  have hY₀ : 1 ≤ Y₀ := one_le_rpow hx1.le (by positivity)
  have hY₀ε : Y₀ ≤ x ^ ε := rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hm1 : 1 < m := by
    have : 0 < L ^ (1 / 5 : ℝ) := by positivity
    have := add_one_le_exp (2 * L ^ (1 / 5 : ℝ))
    simp only [m]
    linarith
  have h𝔅m : ∀ p ∈ 𝔅, p.Prime ∧ (p : ℝ) ≤ m := fun p hp => ⟨(h𝔅 p hp).1, (h𝔅 p hp).2.2⟩
  -- the long moduli are coprime to the band primes and to `r ≤ x^{ε/4}`
  have hℓ𝔅 : ∀ i ∈ S, ∀ p ∈ 𝔅, ¬ p ∣ ℓ i := by
    intro i hi p hp hpℓ
    have h1 := (hℓ i hi).2 p (Nat.mem_primeFactors.2 ⟨(h𝔅 p hp).1, hpℓ, (hℓ i hi).1.ne'⟩)
    linarith [(h𝔅 p hp).2.2]
  have hrℓ : ∀ r ∈ Icc 1 R, ∀ i ∈ S, Nat.Coprime r (ℓ i) := by
    intro r hr i hi
    refine Nat.coprime_of_dvd fun p hp hpr hpℓ => ?_
    have h1 := (hℓ i hi).2 p (Nat.mem_primeFactors.2 ⟨hp, hpℓ, (hℓ i hi).1.ne'⟩)
    have h2 : (p : ℝ) ≤ r := by exact_mod_cast Nat.le_of_dvd (mem_Icc.1 hr).1 hpr
    have h3 : (r : ℝ) ≤ Y₀ := (Nat.le_floor_iff (by positivity)).1 (mem_Icc.1 hr).2
    linarith
  -- the weight `f(u) = Φ(u/x)`
  have hf0 : f 0 = 0 := by
    by_contra h0
    have := (hΦ.2.2.1 _ h0).1
    simp only [Nat.cast_zero, zero_div] at this
    linarith [inv_pos.2 (show (0 : ℝ) < κ by linarith)]
  have hf : ∀ u, 0 ≤ f u := fun u => hΦ.2.1 _
  have hfM : ∀ u, f u ≤ |M 0| := fun u =>
    (le_abs_self _).trans ((abs_le_of_isCutoff hΦ _).trans (le_abs_self _))
  have hV : ∑ k ∈ Icc 1 N, |f k - f (k - 1)| ≤ L ^ (1 / 10 : ℝ) := by
    refine (sum_abs_sub_cutoff_le hx0 hΦ N).trans ?_
    have hN : (N : ℝ) ≤ κ * x := Nat.floor_le (by positivity)
    have hTC : T ^ CΦ ≤ T ^ |CΦ| := rpow_le_rpow_of_exponent_le hT1 (le_abs_self _)
    have h1 : M 1 * T ^ CΦ ≤ |M 1| * T ^ |CΦ| :=
      mul_le_mul (le_abs_self _) hTC (by positivity) (abs_nonneg _)
    calc (N : ℝ) * (M 1 * T ^ CΦ / x) ≤ κ * x * (|M 1| * T ^ |CΦ| / x) := by
          rcases le_or_gt 0 (M 1 * T ^ CΦ) with h0 | h0
          · exact mul_le_mul hN (div_le_div_of_nonneg_right h1 hx0.le) (by positivity)
              (by positivity)
          · have : (N : ℝ) * (M 1 * T ^ CΦ / x) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (div_nonpos_of_nonpos_of_nonneg
                h0.le hx0.le)
            exact this.trans (by positivity)
      _ = κ * |M 1| * T ^ |CΦ| := by field_simp
      _ ≤ L ^ (1 / 10 : ℝ) := hVL
  -- the relative errors
  have hδr : ∀ r ∈ Icc 1 R, |KB| * exp (-(h : ℝ)) + 2 * ∑ p ∈ 𝔅.filter (· ∣ r), (1 : ℝ) / p +
      2 * ∑ S ∈ 𝔅.powerset.filter (fun S : Finset ℕ => Y₀ < ∏ p ∈ S, (p : ℝ)),
        1 / ∏ p ∈ S, (p : ℝ) ≤ (L ^ 5)⁻¹ := by
    intro r hr
    have hr0 : 0 < r := (mem_Icc.1 hr).1
    have hrx : (r : ℝ) ≤ x := by
      have h3 : (r : ℝ) ≤ Y₀ := (Nat.le_floor_iff (by positivity)).1 (mem_Icc.1 hr).2
      have : Y₀ ≤ x := by
        calc Y₀ ≤ x ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hx1.le (by linarith)
          _ = x := rpow_one x
      linarith
    have h1 := sum_inv_dvd_le hx1 hL (fun p hp => ⟨(h𝔅 p hp).1, (h𝔅 p hp).2.1⟩) hr0 hrx
    have h2 := sum_inv_prod_gt_le h𝔅m hm1 (show 0 < Y₀ by positivity)
    have h3 : exp (-(Real.log Y₀ / Real.log m) + exp 1 * ∑ p ∈ 𝔅, (1 : ℝ) / p) ≤
        exp (-(Real.log Y₀ / Real.log m) + exp 1 * T) :=
      exp_le_exp.2 (by nlinarith [exp_pos 1])
    have h4 : |KB| * exp (-(h : ℝ)) ≤ (|KB| + |M 0|) * exp (-(h : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (M 0)]) (exp_pos _).le
    linarith
  -- the harmonic sum over `r`
  have hHR : ∑ r ∈ Icc 1 R, (1 : ℝ) / r ≤ 2 * L := by
    refine (sum_Icc_inv_le R).trans ?_
    have : Real.log R ≤ L := by
      rcases Nat.eq_zero_or_pos R with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        linarith
      · have h1 : (R : ℝ) ≤ x := by
          have := Nat.floor_le (show 0 ≤ Y₀ by positivity)
          have : Y₀ ≤ x := by
            calc Y₀ ≤ x ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hx1.le (by linarith)
              _ = x := rpow_one x
          linarith
        exact Real.log_le_log (by exact_mod_cast h0) h1
    linarith
  have hmain := sum_progression_le hBS h𝔅m hm1.le (N := N) (R := R) S ℓ b
    (fun i hi => (hℓ i hi).1) hrℓ hℓ𝔅 hb hf0 hf hfM hV (even_two_mul _) (by omega) hY₀ H hH
    (fun n => hHb n) hδr (by positivity) hHR hΛ
  -- the target is the bound of `sum_progression_le`
  have heq : ∀ r ∈ Icc 1 R, x / r * cutoffMass κ x Φ * (∑ i ∈ S, b i / ℓ i) *
      divisorModel 𝔅 H = ∑ i ∈ S, b i * (progMain N r (ℓ i) f *
        modelMean 𝔅 fun T => H (∏ p ∈ T, p)) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (mem_Icc.1 hr).1
    rw [mul_sum, sum_mul, divisorModel]
    refine sum_congr rfl fun i hi => ?_
    have hℓ0 : (0 : ℝ) < ℓ i := by exact_mod_cast (hℓ i hi).1
    have key : ∀ X B Mm : ℝ, x / r * (X / x) * (B / ℓ i) * Mm =
        B * (1 / ((r : ℝ) * ℓ i) * X * Mm) := fun X B Mm => by
      field_simp
    simp only [progMain, cutoffMass, f]
    push_cast
    exact key _ _ _
  rw [sum_congr rfl fun r hr => by rw [heq r hr]]
  refine hmain.trans ?_
  -- the main part: `N M₀ (2L) L L⁻⁵ ≤ 2 κ M₀ x / L²`
  have hN : (N : ℝ) ≤ κ * x := Nat.floor_le (by positivity)
  have hL0 : 0 < L := by linarith
  have h1 : (N : ℝ) * |M 0| * (2 * L) * L * (L ^ 5)⁻¹ ≤ 2 * κ * |M 0| * x / L ^ 2 := by
    have e : (N : ℝ) * |M 0| * (2 * L) * L * (L ^ 5)⁻¹ = 2 * N * |M 0| / L ^ 2 * (1 / L) := by
      field_simp
    rw [e]
    have h1L : 1 / L ≤ 1 := by rw [div_le_one hL0]; exact hL
    calc 2 * N * |M 0| / L ^ 2 * (1 / L) ≤ 2 * N * |M 0| / L ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h1L (by positivity)
      _ ≤ 2 * (κ * x) * |M 0| / L ^ 2 := by
          rw [mul_one]
          gcongr
      _ = _ := by ring
  -- the remainders
  have hR : (R : ℝ) ≤ Y₀ := Nat.floor_le (by positivity)
  have hE : Y₀ * (|KB| * (m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ))) + |M 0| * (Y₀ * m) ≤
      Y₀ * ((|KB| + |M 0|) * (m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ)) + (|KB| + |M 0|) * m) := by
    have h0 : 0 ≤ m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ) := by positivity
    have : 0 ≤ Y₀ := by positivity
    nlinarith [abs_nonneg KB, abs_nonneg (M 0), mul_nonneg this h0, mul_nonneg this
      (show 0 ≤ m by positivity)]
  have h2 : (R : ℝ) * #S * (Y₀ * (|KB| * (m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ))) +
      |M 0| * (Y₀ * m)) ≤ x / L ^ 2 := by
    refine le_trans ?_ hrem
    have hE0 : 0 ≤ Y₀ * (|KB| * (m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ))) + |M 0| * (Y₀ * m) := by
      positivity
    calc (R : ℝ) * #S * (Y₀ * (|KB| * (m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ))) + |M 0| * (Y₀ * m))
        ≤ Y₀ * x ^ (1 - ε) * (Y₀ * ((|KB| + |M 0|) * (m ^ (4 * h + 2) * L ^ (1 / 10 : ℝ)) +
          (|KB| + |M 0|) * m)) :=
          mul_le_mul (mul_le_mul hR hS (Nat.cast_nonneg _) (by positivity)) hE hE0
            (by positivity)
      _ = _ := rfl
  calc _ ≤ 2 * κ * |M 0| * x / L ^ 2 + x / L ^ 2 := add_le_add h1 h2
    _ = (2 * κ * |M 0| + 1) * x / L ^ 2 := by ring

/-- E1 for the constant weight `1` (the single modulus `ℓ = 1`). -/
theorem eventually_progression_one (h₃ : BlockSieve) {K : ℕ} (hK : 1 ≤ K) (CN c κ CΦ : ℝ)
    (M : ℕ → ℝ)
    (hc : 0 < c) (hκ : 1 < κ) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ (Φ : ℝ → ℝ) (H : ℕ → ℝ), IsCutoff κ CΦ M x Φ →
      (∀ n, |H n| ≤ 1) → (∀ n, H n = H (bandPart (inertBands K CN x) n)) →
      ∑ r ∈ Icc 1 ⌊x ^ (c / logLog x ^ 20 / 4)⌋₊,
        |∑ u ∈ (Icc 1 ⌊κ * x⌋₊).filter (r ∣ · + 1), Φ (u / x) * H u -
          x / r * cutoffMass κ x Φ * divisorModel (inertBands K CN x) H| ≤
        C * x / Real.log x ^ 2 := by
  obtain ⟨C, hC⟩ := eventually_progression h₃ hK CN c κ CΦ M hc hκ
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1, tendsto_log_atTop.eventually_ge_atTop 1,
    tendsto_logLog.eventually_ge_atTop (max c 1)] with x hx hx1 hL hT Φ H hΦ hH hHb
  have hT1 : 1 ≤ logLog x := le_trans (le_max_right _ _) hT
  have hε : c / logLog x ^ 20 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact (le_max_left _ _).trans (hT.trans (le_self_pow₀ hT1 (by norm_num)))
  have h := hx Unit univ (fun _ => 1) (fun _ => 1) Φ H hΦ (by simp)
    (by simpa using one_le_rpow hx1 (by linarith)) (by simpa using hL) (by simp) hH hHb
  simpa using h


/-- The prime factors of a slot tuple's product exceed `x^ε`. -/
lemma lt_of_mem_primeFactors_slot {x ε : ℝ} (hx : 1 ≤ x) {k : ℕ} {u v : Fin k → ℝ}
    (hu : ∀ i, ε ≤ u i) {Q : Fin k → ℕ} (hQ : Q ∈ slotTuples x u v) {p : ℕ}
    (hp : p ∈ (∏ i, Q i).primeFactors) : x ^ ε < p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  obtain ⟨i, -, hpi⟩ := (hpp.prime.dvd_finsetProd_iff _).1 (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨-, hQi, hlt⟩ := (mem_slotTuples.1 hQ).1 i
  rw [(Nat.prime_dvd_prime_iff_eq hpp hQi).1 hpi]
  exact lt_of_le_of_lt (rpow_le_rpow_of_exponent_le hx (hu i)) hlt

/-- E1 for the slot statistic: the moduli are the slot products `ℓ = ∏ Q`. -/
theorem eventually_progression_slot (h₃ : BlockSieve) {K : ℕ} (hK : 1 ≤ K) (CN c κ CΦ : ℝ)
    (M : ℕ → ℝ)
    (hc : 0 < c) (hκ : 1 < κ) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ k ≤ 2, ∀ (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ)
      (Φ : ℝ → ℝ) (H : ℕ → ℝ), AdmissibleSlots c x u v → (∀ Q, |B Q| ≤ 1) →
      IsCutoff κ CΦ M x Φ → (∀ n, |H n| ≤ 1) →
      (∀ n, H n = H (bandPart (inertBands K CN x) n)) →
      ∑ r ∈ Icc 1 ⌊x ^ (c / logLog x ^ 20 / 4)⌋₊,
        |∑ m ∈ (Icc 1 ⌊κ * x⌋₊).filter (r ∣ · + 1), Φ (m / x) * slotCount x u v B m * H m -
          x / r * cutoffMass κ x Φ * slotMean x u v B * divisorModel (inertBands K CN x) H| ≤
        C * x / Real.log x ^ 2 := by
  obtain ⟨C, hC⟩ := eventually_progression h₃ hK CN c κ CΦ M hc hκ
  obtain ⟨E, hE, hmert⟩ := abs_sum_inv_primes_sub_le
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 2, tendsto_logLog.eventually_ge_atTop (max (max c 1) E),
    eventually_mul_rpow_le_log_rpow 8 3 (show (0 : ℝ) < 1 by norm_num)]
    with x hx hx2 hT hL k hk u v B Φ H hslot hB hΦ hH hHb
  rw [rpow_one, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast] at hL
  have hT1 : 1 ≤ logLog x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTc : c ≤ logLog x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTE : E ≤ logLog x := le_trans (le_max_right _ _) hT
  have hx1 : 1 ≤ x := by linarith
  have hε0 : 0 ≤ c / logLog x ^ 20 := by positivity
  obtain ⟨hu, hv⟩ := hslot
  have hv1 : ∑ i, v i ≤ 1 := by linarith
  -- the hypotheses of E1 for the slot tuples
  have hcard : (#(slotTuples x u v) : ℝ) ≤ x ^ (1 - c / logLog x ^ 20) :=
    (card_slotTuples_le (by linarith) u v).trans (rpow_le_rpow_of_exponent_le hx1 hv)
  have hsum : ∑ Q ∈ slotTuples x u v, (1 : ℝ) / ((∏ i, Q i : ℕ) : ℝ) ≤ Real.log x := by
    have h1 := sum_inv_slotTuples_le (x := x) (by linarith) hv1 (u := u)
    have h2 := sum_inv_primes_le_logLog hmert hx2 le_rfl
    have h0 : 0 ≤ ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p := sum_nonneg fun _ _ => by positivity
    have h3 : (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ (k + 1) ≤ (2 * logLog x) ^ 3 := by
      calc (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ (k + 1) ≤ (2 * logLog x) ^ (k + 1) :=
            pow_le_pow_left₀ h0 (by linarith) _
        _ ≤ (2 * logLog x) ^ 3 := pow_le_pow_right₀ (by linarith) (by omega)
    have h4 : (2 * logLog x) ^ 3 = 8 * logLog x ^ 3 := by ring
    push_cast
    linarith
  have h := hx (Fin (k + 1) → ℕ) (slotTuples x u v) (fun Q => ∏ i, Q i) (fun Q => B (Fin.init Q))
    Φ H hΦ (fun Q hQ => ⟨prod_pos fun i _ => ((mem_slotTuples.1 hQ).1 i).2.1.pos,
      fun p hp => lt_of_mem_primeFactors_slot hx1 hu hQ hp⟩) hcard hsum (fun Q _ => hB _) hH hHb
  have hmean :
      slotMean x u v B = ∑ Q ∈ slotTuples x u v, B (Fin.init Q) / ((∏ i, Q i : ℕ) : ℝ) := by
    simp only [slotMean, Nat.cast_prod]
  rw [hmean]
  exact h

/-- The block-sieve remainders over sets `D` of sieving primes with
`∏ D ≤ Y` are at most the progression remainders over `r ≤ Y'`, for `Y ≤ Y'`. -/
lemma sum_powerset_rem_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (objs : Finset ℕ)
    (wt : ℕ → ℝ) (X : ℝ) {Y Y' : ℝ} (hYY : Y ≤ Y') :
    ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Y),
        |∑ u ∈ objs.filter (fun u => ∀ p ∈ D, p ∣ u + 1), wt u - X * ∏ p ∈ D, 1 / (p : ℝ)| ≤
      ∑ r ∈ Icc 1 ⌊Y'⌋₊, |∑ u ∈ objs.filter (r ∣ · + 1), wt u - X / r| := by
  have hconv : ∀ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Y),
      |∑ u ∈ objs.filter (fun u => ∀ p ∈ D, p ∣ u + 1), wt u - X * ∏ p ∈ D, 1 / (p : ℝ)| =
      |∑ u ∈ objs.filter ((∏ p ∈ D, p) ∣ · + 1), wt u - X / ((∏ p ∈ D, p : ℕ) : ℝ)| := by
    intro D hD
    have hDp : ∀ p ∈ D, p.Prime := fun p hp => hP p (mem_powerset.1 (mem_filter.1 hD).1 hp)
    have hfilt : objs.filter (fun u => ∀ p ∈ D, p ∣ u + 1) =
        objs.filter ((∏ p ∈ D, p) ∣ · + 1) :=
      filter_congr fun u _ => ⟨fun h => prod_primes_dvd _ (fun p hp => (hDp p hp).prime) h,
        fun h p hp => (dvd_prod_of_mem _ hp).trans h⟩
    have hX : X * ∏ p ∈ D, 1 / (p : ℝ) = X / ((∏ p ∈ D, p : ℕ) : ℝ) := by
      push_cast
      rw [prod_div_distrib, prod_const_one, mul_one_div]
    rw [hfilt, hX]
  rw [sum_congr rfl hconv]
  refine (sum_powerset_prod_le hP Y
    (fun r => |∑ u ∈ objs.filter (r ∣ · + 1), wt u - X / r|) fun _ => abs_nonneg _).trans ?_
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (Nat.floor_mono hYY))
    fun _ _ _ => abs_nonneg _

end

end Sieve

end Erdos408
