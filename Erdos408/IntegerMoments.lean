module

public import Erdos408.Mertens
public import Mathlib.Data.Nat.Prime.Factorial

/-!
# Integer moments of the additive companion

Complete additivity gives `F n = ∑_{q^e ∣ n, e ≥ 1} F q`. Summing over `n ≤ x`
and replacing `⌊x / d⌋` by `x / d` gives

* `∑_{n ≤ x} F n = x B(x) + O(x)`,
* `∑_{n ≤ x} F(n)² = x (C(x) + D(x)) + O(x log x)`,

which are Erdős, Granville, Pomerance and Spiro (1990), (2.8) and (2.19). The
prime powers `q^e` with `e ≥ 2` contribute `O(x)` to the first sum and, since
`F n ≤ log x / log 2`, `O(x log x)` to the second. The floors cost
`O(θ(x)) = O(x)` in the first sum and
`O(θ(x) log x + ∑_{q r ≤ x} log q log r) = O(x log x)` in the second, and
`F q ≤ log q / log 2` bounds every coefficient.
-/

@[expose] public section

namespace Erdos408

open Finset

/-- `mem_primesIoc_one` with the bound `p ≤ ⌊x⌋₊` in `ℕ`. -/
private lemma mem_primesIoc_one' {x : ℝ} {p : ℕ} :
    p ∈ primesIoc 1 x ↔ p.Prime ∧ p ≤ ⌊x⌋₊ :=
  mem_primesIoc_one.trans (and_congr_right fun hp => (Nat.le_floor_iff' hp.ne_zero).symm)

/-- `∑_{n ≤ N} F n = F (N!)`. -/
private lemma sum_F_Icc (N : ℕ) : ∑ n ∈ Icc 1 N, F n = F N.factorial := by
  induction N with
  | zero => simp [F_one]
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
      F_mul N.succ_ne_zero N.factorial_ne_zero, add_comm]

/-- `F (⌊x⌋!) = ∑_{q ≤ x} v_q(⌊x⌋!) F q`. -/
private lemma F_factorial (x : ℝ) :
    F ⌊x⌋₊.factorial = ∑ q ∈ primesIoc 1 x, ⌊x⌋₊.factorial.factorization q * F q := by
  rw [F_eq_sum_factorization (Nat.factorial_ne_zero _)]
  refine sum_subset (fun q hq => ?_) (fun q _ hq => ?_)
  · have hp := Nat.prime_of_mem_primeFactors hq
    exact mem_primesIoc_one'.2 ⟨hp, hp.dvd_factorial.1 (Nat.dvd_of_mem_primeFactors hq)⟩
  · rw [Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization]), zero_mul]

/-- Legendre's formula gives `N / p ≤ v_p(N!)`. -/
private lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (by omega : Nat.log p N < Nat.log p N + 2)]
  simpa using single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _)
    (show 1 ∈ Ico 1 (Nat.log p N + 2) by simp)

/-- Legendre's formula gives `v_p(⌊x⌋!) ≤ x / (p - 1) = x / p + x / (p (p - 1))`. -/
private lemma factorization_factorial_le {x : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : p.Prime) :
    (⌊x⌋₊.factorial.factorization p : ℝ) ≤ x / p + x / (p * (p - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have h : ((⌊x⌋₊ / (p - 1) : ℕ) : ℝ) ≤ x / (p - 1) := by
    refine Nat.cast_div_le.trans ?_
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    exact div_le_div_of_nonneg_right (Nat.floor_le hx) (by linarith)
  calc _ ≤ x / (p - 1) := (Nat.cast_le.2 (Nat.factorization_factorial_le_div_pred hp _)).trans h
    _ = _ := by field_simp; ring

/-- `⌊x⌋ / d` is within `1` of `x / d`. -/
private lemma abs_floor_div_sub_le {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    |((⌊x⌋₊ / d : ℕ) : ℝ) - x / d| ≤ 1 := by
  rw [← Nat.floor_div_natCast]
  have h0 : 0 ≤ x / d := div_nonneg hx d.cast_nonneg
  rw [abs_le]
  constructor <;> linarith [Nat.floor_le h0, Nat.lt_floor_add_one (x / d)]

/-- `∑_{2 ≤ n ≤ N} log n / (n (n - 1)) ≤ 2 - (log N + 2) / N`, by telescoping. -/
private lemma sum_log_div_mul_pred_le_aux {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 2 N, Real.log n / (n * (n - 1)) ≤ 2 - (Real.log N + 2) / N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    -- `log (N + 1) - log N ≤ 1 / N`
    have hlog : Real.log (N + 1) - Real.log N ≤ 1 / N := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have h := Real.log_le_sub_one_of_pos (x := (N + 1) / N) (by positivity)
      have h' : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
      linarith
    have hmul : ((N : ℝ) + 1) * (Real.log (N + 1) - Real.log N) ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ N + 1)
      have h' : ((N : ℝ) + 1) * (1 / N) ≤ 2 := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
      linarith
    have key : (Real.log N + 2) / N - (Real.log (N + 1) + 2) / (N + 1) -
        Real.log (N + 1) / ((N + 1) * N) =
        (2 - (N + 1) * (Real.log (N + 1) - Real.log N)) / (N * (N + 1)) := by
      field_simp; ring
    have : 0 ≤ (2 - (N + 1) * (Real.log (N + 1) - Real.log N)) / (N * (N + 1)) :=
      div_nonneg (by linarith) (by positivity)
    push_cast
    rw [add_sub_cancel_right]
    linarith

/-- `∑_{2 ≤ n ≤ N} log n / (n (n - 1)) ≤ 2`. -/
private lemma sum_log_div_mul_pred_le (N : ℕ) :
    ∑ n ∈ Icc 2 N, Real.log n / (n * (n - 1)) ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have := div_nonneg (by linarith [Real.log_nonneg h1] : 0 ≤ Real.log N + 2)
    (by linarith : (0 : ℝ) ≤ N)
  linarith [sum_log_div_mul_pred_le_aux hN]

/-- `∑_{q ≤ x} F q / (q (q - 1)) ≤ 2 / log 2`. -/
private lemma sum_F_div_mul_pred_le (x : ℝ) :
    ∑ q ∈ primesIoc 1 x, (F q : ℝ) / (q * (q - 1)) ≤ 2 / Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc _ ≤ ∑ q ∈ primesIoc 1 x, Real.log q / (q * (q - 1)) / Real.log 2 := by
        refine sum_le_sum fun q hq => ?_
        have hp := (mem_primesIoc_one'.1 hq).1
        have : (1 : ℝ) < q := by exact_mod_cast hp.one_lt
        rw [div_right_comm]
        exact div_le_div_of_nonneg_right (F_le_log_div_log_two hp.ne_zero) (by nlinarith)
    _ = (∑ q ∈ primesIoc 1 x, Real.log q / (q * (q - 1))) / Real.log 2 := by rw [sum_div]
    _ ≤ (∑ n ∈ Icc 2 ⌊x⌋₊, Real.log n / (n * (n - 1))) / Real.log 2 := by
        refine div_le_div_of_nonneg_right (sum_le_sum_of_subset_of_nonneg ?_ ?_) h2.le
        · intro q hq
          have := mem_primesIoc_one'.1 hq
          exact mem_Icc.2 ⟨this.1.two_le, this.2⟩
        · intro n hn _
          have : (2 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.1 hn).1
          exact div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith)
    _ ≤ 2 / Real.log 2 := div_le_div_of_nonneg_right (sum_log_div_mul_pred_le _) h2.le

/-- `∑_{q ≤ x} F q ≤ x log 4 / log 2`. -/
private lemma sum_F_primesIoc_le {x : ℝ} (hx : 0 ≤ x) :
    ∑ q ∈ primesIoc 1 x, (F q : ℝ) ≤ Real.log 4 * x / Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc _ ≤ ∑ q ∈ primesIoc 1 x, Real.log q / Real.log 2 :=
        sum_le_sum fun q hq => F_le_log_div_log_two (mem_primesIoc_one'.1 hq).1.ne_zero
    _ = (∑ q ∈ primesIoc 1 x, Real.log q) / Real.log 2 := by rw [sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right (sum_log_primesIoc_le hx) h2.le

/-- `∑_{q ≤ x} F q (x / (q (q - 1)) + 1) ≤ (2 + log 4) / log 2 · x`. -/
private lemma sum_F_error_le {x : ℝ} (hx : 0 ≤ x) :
    ∑ q ∈ primesIoc 1 x, (F q : ℝ) * (x / (q * (q - 1)) + 1) ≤
      (2 + Real.log 4) / Real.log 2 * x := by
  calc _ = x * ∑ q ∈ primesIoc 1 x, (F q : ℝ) / (q * (q - 1)) +
        ∑ q ∈ primesIoc 1 x, (F q : ℝ) := by
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun q _ => by ring
    _ ≤ x * (2 / Real.log 2) + Real.log 4 * x / Real.log 2 :=
        add_le_add (mul_le_mul_of_nonneg_left (sum_F_div_mul_pred_le x) hx)
          (sum_F_primesIoc_le hx)
    _ = _ := by ring

/-- The first integer moment: `∑_{n ≤ x} F n = x B(x) + O(x)`. -/
theorem integer_first_moment : ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (F n : ℝ) - x * harmonicF x| ≤ K * x := by
  refine ⟨(2 + Real.log 4) / Real.log 2, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have h : ∑ n ∈ Icc 1 ⌊x⌋₊, (F n : ℝ) - x * harmonicF x =
      ∑ q ∈ primesIoc 1 x, (F q : ℝ) * (⌊x⌋₊.factorial.factorization q - x / q) := by
    rw [← Nat.cast_sum, sum_F_Icc, F_factorial, harmonicF, mul_sum, Nat.cast_sum,
      ← sum_sub_distrib]
    exact sum_congr rfl fun q _ => by push_cast; ring
  rw [h]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun q hq => ?_).trans (sum_F_error_le hx0))
  have hp := (mem_primesIoc_one'.1 hq).1
  rw [abs_mul, Nat.abs_cast]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have h1 := factorization_factorial_le hx0 hp
  have h2 : ((⌊x⌋₊ / q : ℕ) : ℝ) ≤ ⌊x⌋₊.factorial.factorization q := by
    exact_mod_cast div_le_factorization_factorial hp _
  have h3 := abs_floor_div_sub_le hx0 q
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hp.one_lt
  have h4 : 0 ≤ x / (q * (q - 1)) := div_nonneg hx0 (by nlinarith)
  rw [abs_le] at h3 ⊢
  constructor <;> linarith

/-- `F` summed over the distinct prime factors. -/
private noncomputable def distinctF (n : ℕ) : ℕ :=
  ∑ q ∈ n.primeFactors, F q

/-- `distinctF n ≤ F n`, since every prime factor has multiplicity at least one. -/
private lemma distinctF_le_F {n : ℕ} (hn : n ≠ 0) : distinctF n ≤ F n := by
  rw [distinctF, F_eq_sum_factorization hn]
  refine sum_le_sum fun q hq => Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero ?_)
  exact Finsupp.mem_support_iff.1 (by rwa [Nat.support_factorization])

/-- For `1 ≤ n ≤ x`, the prime factors of `n` are the primes `q ≤ x` dividing `n`. -/
private lemma primeFactors_eq_filter {x : ℝ} {n : ℕ} (hn : n ∈ Icc 1 ⌊x⌋₊) :
    n.primeFactors = {q ∈ primesIoc 1 x | q ∣ n} := by
  obtain ⟨h1, h2⟩ := mem_Icc.1 hn
  ext q
  simp only [Nat.mem_primeFactors, mem_filter, mem_primesIoc_one']
  constructor
  · rintro ⟨hp, hq, -⟩
    exact ⟨⟨hp, (Nat.le_of_dvd h1 hq).trans h2⟩, hq⟩
  · rintro ⟨⟨hp, -⟩, hq⟩
    exact ⟨hp, hq, by omega⟩

/-- `#{n ≤ N : d ∣ n} = N / d`. -/
private lemma card_filter_dvd_Icc (N d : ℕ) : #{n ∈ Icc 1 N | d ∣ n} = N / d := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div N d]
  rfl

/-- `∑_{n ≤ x} distinctF n = ∑_{q ≤ x} F q ⌊x / q⌋`. -/
private lemma sum_distinctF (x : ℝ) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, distinctF n = ∑ q ∈ primesIoc 1 x, F q * (⌊x⌋₊ / q) := by
  rw [sum_congr rfl fun n hn => by rw [distinctF, primeFactors_eq_filter hn, sum_filter],
    sum_comm]
  refine sum_congr rfl fun q _ => ?_
  rw [← sum_filter, sum_const, card_filter_dvd_Icc, smul_eq_mul, mul_comm]

/-- `∑_{n ≤ x} distinctF(n)² = ∑_{q, r ≤ x} F q F r ⌊x / lcm(q, r)⌋`. -/
private lemma sum_distinctF_sq (x : ℝ) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, distinctF n ^ 2 =
      ∑ q ∈ primesIoc 1 x, ∑ r ∈ primesIoc 1 x, F q * F r * (⌊x⌋₊ / Nat.lcm q r) := by
  have h : ∀ n ∈ Icc 1 ⌊x⌋₊, distinctF n ^ 2 = ∑ q ∈ primesIoc 1 x,
      ∑ r ∈ primesIoc 1 x, if Nat.lcm q r ∣ n then F q * F r else 0 := by
    intro n hn
    rw [distinctF, primeFactors_eq_filter hn, sq, sum_mul_sum, sum_filter]
    refine sum_congr rfl fun q _ => ?_
    split_ifs with hq
    · rw [sum_filter]
      exact sum_congr rfl fun r _ => by simp [Nat.lcm_dvd_iff, hq]
    · simp [Nat.lcm_dvd_iff, hq]
  rw [sum_congr rfl h, sum_comm]
  refine sum_congr rfl fun q _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun r _ => ?_
  rw [← sum_filter, sum_const, card_filter_dvd_Icc, smul_eq_mul, mul_comm]

/-- `∑_{n ≤ x} distinctF(n)²` split into the diagonal `q = r` and the pairs `q ≠ r` with
`q r ≤ x`. -/
private lemma sum_distinctF_sq_eq (x : ℝ) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, (distinctF n : ℝ) ^ 2 = ∑ q ∈ primesIoc 1 x,
      ((F q : ℝ) ^ 2 * (⌊x⌋₊ / q : ℕ) +
        ∑ r ∈ primesIoc 1 (x / q) with r ≠ q, (F q : ℝ) * F r * (⌊x⌋₊ / (q * r) : ℕ)) := by
  have h := congrArg (Nat.cast : ℕ → ℝ) (sum_distinctF_sq x)
  push_cast at h
  rw [h]
  refine sum_congr rfl fun q hq => ?_
  have hp := (mem_primesIoc_one'.1 hq).1
  rw [← add_sum_erase _ _ hq, Nat.lcm_self, ← filter_ne', sq]
  congr 1
  rw [sum_congr rfl fun r hr => by
    rw [Nat.Coprime.lcm_eq_mul ((Nat.coprime_primes hp (mem_primesIoc_one'.1
      (mem_filter.1 hr).1).1).2 (mem_filter.1 hr).2.symm)]]
  refine (sum_subset (fun r hr => ?_) fun r hr hr' => ?_).symm
  · obtain ⟨hr, hrq⟩ := mem_filter.1 hr
    obtain ⟨hr, hrx⟩ := mem_primesIoc_one'.1 hr
    rw [Nat.floor_div_natCast] at hrx
    exact mem_filter.2 ⟨mem_primesIoc_one'.2 ⟨hr, hrx.trans (Nat.div_le_self _ _)⟩, hrq⟩
  · obtain ⟨hr, hrq⟩ := mem_filter.1 hr
    have hrx : ⌊x⌋₊ / q < r := by
      by_contra hle
      refine hr' (mem_filter.2 ⟨mem_primesIoc_one'.2 ⟨(mem_primesIoc_one'.1 hr).1, ?_⟩, hrq⟩)
      rw [Nat.floor_div_natCast]
      omega
    rw [← Nat.div_div_eq_div_mul, Nat.div_eq_of_lt hrx, Nat.cast_zero, mul_zero]

/-- The second integer moment: `∑_{n ≤ x} F(n)² = x (C(x) + D(x)) + O(x log x)`. -/
theorem integer_second_moment : ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (F n : ℝ) ^ 2 - x * (harmonicFSq x + harmonicFPair x)| ≤
      K * x * Real.log x := by
  obtain ⟨E, hE0, hE⟩ := mertens_first
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set K₁ := (2 + Real.log 4) / Real.log 2 with hK₁
  refine ⟨(2 * K₁ + 2 * Real.log 4 / Real.log 2 + Real.log 4 * E / Real.log 2 ^ 2) /
    Real.log 2, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  set L := Real.log x / Real.log 2 with hL
  have hL1 : 1 ≤ L := (one_le_div h2).2 hlogx
  -- `F n ≤ L` for `n ≤ x`
  have hFL : ∀ n ∈ Icc 1 ⌊x⌋₊, (F n : ℝ) ≤ L := by
    intro n hn
    obtain ⟨hn1, hnx⟩ := mem_Icc.1 hn
    refine (F_le_log_div_log_two (by omega)).trans (div_le_div_of_nonneg_right ?_ h2.le)
    exact Real.log_le_log (by exact_mod_cast hn1) ((Nat.cast_le.2 hnx).trans (Nat.floor_le hx0))
  -- `∑_{n ≤ x} (F n - distinctF n) ≤ K₁ x`
  have hdiff : ∑ n ∈ Icc 1 ⌊x⌋₊, ((F n : ℝ) - distinctF n) ≤ K₁ * x := by
    rw [sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, sum_F_Icc, F_factorial, sum_distinctF,
      Nat.cast_sum, Nat.cast_sum, ← sum_sub_distrib]
    refine (sum_le_sum fun q hq => ?_).trans (sum_F_error_le hx0)
    have hp := (mem_primesIoc_one'.1 hq).1
    have h1 := factorization_factorial_le hx0 hp
    have h3 := (abs_le.1 (abs_floor_div_sub_le hx0 q)).1
    push_cast
    rw [mul_comm _ (F q : ℝ), ← mul_sub]
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  -- `0 ≤ ∑ F(n)² - ∑ distinctF(n)² ≤ 2 L K₁ x`
  have hsq : |∑ n ∈ Icc 1 ⌊x⌋₊, (F n : ℝ) ^ 2 - ∑ n ∈ Icc 1 ⌊x⌋₊, (distinctF n : ℝ) ^ 2| ≤
      2 * L * (K₁ * x) := by
    have hle : ∀ n ∈ Icc 1 ⌊x⌋₊, (distinctF n : ℝ) ≤ F n := fun n hn =>
      Nat.cast_le.2 (distinctF_le_F (by have := (mem_Icc.1 hn).1; omega))
    have h0 : 0 ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, ((F n : ℝ) ^ 2 - (distinctF n : ℝ) ^ 2) := by
      refine sum_nonneg fun n hn => ?_
      have := hle n hn
      have : (0 : ℝ) ≤ distinctF n := Nat.cast_nonneg _
      nlinarith
    rw [← sum_sub_distrib, abs_of_nonneg h0]
    refine (sum_le_sum fun n hn => ?_).trans
      ((mul_sum ..).symm.le.trans (mul_le_mul_of_nonneg_left hdiff (by linarith)))
    have := hle n hn
    have := hFL n hn
    have : (0 : ℝ) ≤ distinctF n := Nat.cast_nonneg _
    nlinarith
  -- `∑_{q ≤ x} F(q)² ≤ L θ(x) / log 2`
  have hdiag : ∑ q ∈ primesIoc 1 x, (F q : ℝ) ^ 2 ≤ L * (Real.log 4 * x / Real.log 2) := by
    refine (sum_le_sum fun q hq => ?_).trans ((mul_sum ..).symm.le.trans
      (mul_le_mul_of_nonneg_left (sum_F_primesIoc_le hx0) (by linarith)))
    have hq' := mem_primesIoc_one'.1 hq
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hFL q (mem_Icc.2 ⟨hq'.1.one_lt.le, hq'.2⟩))
      (Nat.cast_nonneg _)
  -- `∑_{q r ≤ x} F q F r ≤ (log 4 / log² 2) x ∑_{q ≤ x} log q / q`
  have hcross : ∑ q ∈ primesIoc 1 x, ∑ r ∈ primesIoc 1 (x / q), (F q : ℝ) * F r ≤
      Real.log 4 * x / Real.log 2 ^ 2 * (Real.log x + E) := by
    have hM := (abs_le.1 (hE 1 x le_rfl (by linarith))).2
    rw [div_one] at hM
    calc _ ≤ ∑ q ∈ primesIoc 1 x, Real.log 4 * x / Real.log 2 ^ 2 * (Real.log q / q) := by
          refine sum_le_sum fun q hq => ?_
          have hp := (mem_primesIoc_one'.1 hq).1
          have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.pos
          rw [← mul_sum]
          calc _ ≤ Real.log q / Real.log 2 * (Real.log 4 * (x / q) / Real.log 2) :=
                mul_le_mul (F_le_log_div_log_two hp.ne_zero)
                  (sum_F_primesIoc_le (div_nonneg hx0 hq0.le))
                  (sum_nonneg fun _ _ => Nat.cast_nonneg _)
                  (div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)) h2.le)
            _ = _ := by ring
      _ = Real.log 4 * x / Real.log 2 ^ 2 * ∑ q ∈ primesIoc 1 x, Real.log q / q := by
          rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- replacing the floors costs `∑_{q ≤ x} F(q)² + ∑_{q r ≤ x} F q F r`
  have hfloor : |∑ n ∈ Icc 1 ⌊x⌋₊, (distinctF n : ℝ) ^ 2 -
      x * (harmonicFSq x + harmonicFPair x)| ≤ ∑ q ∈ primesIoc 1 x, (F q : ℝ) ^ 2 +
        ∑ q ∈ primesIoc 1 x, ∑ r ∈ primesIoc 1 (x / q), (F q : ℝ) * F r := by
    rw [sum_distinctF_sq_eq, harmonicFSq, harmonicFPair, ← sum_add_distrib, mul_sum,
      ← sum_sub_distrib, ← sum_add_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q hq => ?_)
    have e : (F q : ℝ) ^ 2 * (⌊x⌋₊ / q : ℕ) +
        ∑ r ∈ primesIoc 1 (x / q) with r ≠ q, (F q : ℝ) * F r * (⌊x⌋₊ / (q * r) : ℕ) -
        x * ((F q : ℝ) ^ 2 / q + ∑ r ∈ primesIoc 1 (x / q) with r ≠ q,
          (F q : ℝ) * F r / (q * r)) =
        (F q : ℝ) ^ 2 * ((⌊x⌋₊ / q : ℕ) - x / q) +
        ∑ r ∈ primesIoc 1 (x / q) with r ≠ q,
          (F q : ℝ) * F r * ((⌊x⌋₊ / (q * r) : ℕ) - x / (q * r : ℕ)) := by
      rw [mul_add, mul_sum, add_sub_add_comm, ← sum_sub_distrib]
      congr 1
      · ring
      · exact sum_congr rfl fun r _ => by push_cast; ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (by positivity) (abs_floor_div_sub_le hx0 q)
    · refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun r _ => ?_).trans
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity))
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (by positivity) (abs_floor_div_sub_le hx0 (q * r))
  calc _ ≤ |∑ n ∈ Icc 1 ⌊x⌋₊, (F n : ℝ) ^ 2 - ∑ n ∈ Icc 1 ⌊x⌋₊, (distinctF n : ℝ) ^ 2| +
        |∑ n ∈ Icc 1 ⌊x⌋₊, (distinctF n : ℝ) ^ 2 - x * (harmonicFSq x + harmonicFPair x)| :=
        abs_sub_le _ _ _
    _ ≤ 2 * L * (K₁ * x) + (L * (Real.log 4 * x / Real.log 2) +
        Real.log 4 * x / Real.log 2 ^ 2 * (Real.log x + E)) :=
        add_le_add hsq (hfloor.trans (add_le_add hdiag hcross))
    _ ≤ _ := by
        have e : (2 * K₁ + 2 * Real.log 4 / Real.log 2 + Real.log 4 * E / Real.log 2 ^ 2) /
            Real.log 2 * x * Real.log x - (2 * L * (K₁ * x) + (L * (Real.log 4 * x /
              Real.log 2) + Real.log 4 * x / Real.log 2 ^ 2 * (Real.log x + E))) =
            Real.log 4 * E * x / Real.log 2 ^ 2 * (L - 1) := by
          rw [hL]
          field_simp
          ring
        have : 0 ≤ Real.log 4 * E * x / Real.log 2 ^ 2 * (L - 1) :=
          mul_nonneg (by positivity) (by linarith)
        linarith

end Erdos408
