module

public import Erdos408.Mertens

/-!
# From dyadic to cumulative prime moments

Cut `(s, t]`, with `s = t / 2^I ∈ [√t, 2√t]`, into the dyads
`(t / 2^{i+1}, t / 2^i]` for `i < I`. On the `i`-th dyad the harmonic sums differ
from their values at `t` by `O(i + 1)` and `O((i + 1) L)` (Mertens' first
theorem), and Chebyshev's bound gives `Π_y ≪ y / log y`. So the weighted
replacement costs sum to `O(t / log t)` and `O(t)`, and the at most `s` primes
up to `s` are negligible. This is the dyadic-to-cumulative passage in the
proof of Proposition 4.1 of *The normal order of the number of iterations of
Euler's function* (Plasma AI, 2026), §4, normalized by `π(t)` with an absolute
error, so that no rate in the prime number theorem is needed.
-/

@[expose] public section

namespace Erdos408

open Filter Real

/-- Cutting `(1, t]` into `(1, t / 2^n]` and the dyads `(t / 2^{i+1}, t / 2^i]`. -/
private lemma sum_primesIoc_dyadic (g : ℕ → ℝ) {t : ℝ} (n : ℕ) (h : 1 ≤ t / 2 ^ n) :
    ∑ p ∈ primesIoc 1 t, g p = ∑ p ∈ primesIoc 1 (t / 2 ^ n), g p +
      ∑ i ∈ Finset.range n, ∑ p ∈ dyadicPrimes (t / 2 ^ (i + 1)), g p := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht : 0 < t := by
      have := lt_of_lt_of_le one_pos h
      rwa [div_pos_iff_of_pos_right (by positivity)] at this
    have h2 : t / 2 ^ (n + 1) ≤ t / 2 ^ n := by gcongr <;> norm_num
    have hd : dyadicPrimes (t / 2 ^ (n + 1)) = primesIoc (t / 2 ^ (n + 1)) (t / 2 ^ n) := by
      rw [dyadicPrimes_eq_primesIoc, pow_succ]
      congr 1
      ring
    rw [ih (h.trans h2), Finset.sum_range_succ, hd, ← sum_primesIoc_add g h h2]
    ring

/-- `∑_{i < n} (i + 2) / 2^{i+1} ≤ 3`. -/
private lemma sum_range_div_two_pow_le (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 2) / 2 ^ (i + 1) ≤ 3 := by
  have key : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i : ℝ) + 2) / 2 ^ (i + 1) +
      ((n : ℝ) + 3) / 2 ^ n = 3 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have : ((n : ℝ) + 2) / 2 ^ (n + 1) + ((n : ℝ) + 1 + 3) / 2 ^ (n + 1) =
          ((n : ℝ) + 3) / 2 ^ n := by
        field_simp
        ring
      rw [Finset.sum_range_succ]
      push_cast
      linarith
  linarith [key n, (by positivity : 0 ≤ ((n : ℝ) + 3) / 2 ^ n)]

/-- At most `s` primes lie in `(1, s]`. -/
private lemma card_primesIoc_one_le {s : ℝ} (hs : 0 ≤ s) : ((primesIoc 1 s).card : ℝ) ≤ s := by
  have h : (primesIoc 1 s).card ≤ ⌊s⌋₊ :=
    (Finset.card_filter_le _ _).trans (by simp)
  exact (Nat.cast_le.mpr h).trans (Nat.floor_le hs)

/-- Mertens' first theorem bounds `∑_{y < q ≤ z} F(q) / q`. -/
private lemma sum_F_div_le {E : ℝ}
    (hE : ∀ y z : ℝ, 1 ≤ y → y ≤ z → |∑ p ∈ primesIoc y z, log p / p - log (z / y)| ≤ E)
    {y z : ℝ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    ∑ q ∈ primesIoc y z, (F q : ℝ) / q ≤ (log (z / y) + E) / log 2 := by
  have hl2 : 0 < log 2 := log_pos one_lt_two
  calc ∑ q ∈ primesIoc y z, (F q : ℝ) / q ≤ ∑ q ∈ primesIoc y z, log q / q / log 2 := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hq0 := (mem_primesIoc.1 hq).1.pos
        rw [div_right_comm]
        exact div_le_div_of_nonneg_right (F_le_log_div_log_two hq0.ne') (by positivity)
    _ = (∑ q ∈ primesIoc y z, log q / q) / log 2 := by rw [Finset.sum_div]
    _ ≤ _ := by
        gcongr
        linarith [(abs_le.mp (hE y z hy hyz)).2]

/-- `B` is increasing, with `B(z) - B(y) ≤ (log (z / y) + E) / log 2`. -/
private lemma harmonicF_sub {E : ℝ}
    (hE : ∀ y z : ℝ, 1 ≤ y → y ≤ z → |∑ p ∈ primesIoc y z, log p / p - log (z / y)| ≤ E)
    {y z : ℝ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    0 ≤ harmonicF z - harmonicF y ∧ harmonicF z - harmonicF y ≤ (log (z / y) + E) / log 2 := by
  have h : harmonicF z - harmonicF y = ∑ q ∈ primesIoc y z, (F q : ℝ) / q := by
    rw [harmonicF, harmonicF, ← sum_primesIoc_add _ hy hyz]
    ring
  rw [h]
  exact ⟨Finset.sum_nonneg fun _ _ => by positivity, sum_F_div_le hE hy hyz⟩

/-- `C` is increasing, with `C(z) - C(y) ≤ log z (log (z / y) + E) / log² 2`. -/
private lemma harmonicFSq_sub {E : ℝ}
    (hE : ∀ y z : ℝ, 1 ≤ y → y ≤ z → |∑ p ∈ primesIoc y z, log p / p - log (z / y)| ≤ E)
    {y z : ℝ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    0 ≤ harmonicFSq z - harmonicFSq y ∧
      harmonicFSq z - harmonicFSq y ≤ log z * (log (z / y) + E) / log 2 ^ 2 := by
  have hl2 : 0 < log 2 := log_pos one_lt_two
  have h : harmonicFSq z - harmonicFSq y = ∑ q ∈ primesIoc y z, (F q : ℝ) ^ 2 / q := by
    rw [harmonicFSq, harmonicFSq, ← sum_primesIoc_add _ hy hyz]
    ring
  rw [h]
  refine ⟨Finset.sum_nonneg fun _ _ => by positivity, ?_⟩
  calc ∑ q ∈ primesIoc y z, (F q : ℝ) ^ 2 / q
      ≤ ∑ q ∈ primesIoc y z, log z / log 2 * ((F q : ℝ) / q) := by
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨hq, -, hqz⟩ := mem_primesIoc.1 hq
        have hlq : log q ≤ log z := log_le_log (by exact_mod_cast hq.pos) hqz
        have : (F q : ℝ) ≤ log z / log 2 :=
          (F_le_log_div_log_two hq.ne_zero).trans (by gcongr)
        rw [sq, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = log z / log 2 * ∑ q ∈ primesIoc y z, (F q : ℝ) / q := by rw [Finset.mul_sum]
    _ ≤ log z / log 2 * ((log (z / y) + E) / log 2) := by
        gcongr
        · exact div_nonneg (log_nonneg (by linarith)) hl2.le
        · exact sum_F_div_le hE hy hyz
    _ = _ := by ring

/-- The inner sum of `D` over `(a, b]` is at most `F(q) / q · (log (b / a) + E) / log 2`. -/
private lemma sum_pair_le {E : ℝ}
    (hE : ∀ y z : ℝ, 1 ≤ y → y ≤ z → |∑ p ∈ primesIoc y z, log p / p - log (z / y)| ≤ E)
    (q : ℕ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ r ∈ primesIoc a b with r ≠ q, (F q : ℝ) * F r / (q * r) ≤
      F q / q * ((log (b / a) + E) / log 2) := by
  calc ∑ r ∈ primesIoc a b with r ≠ q, (F q : ℝ) * F r / (q * r)
      ≤ ∑ r ∈ primesIoc a b, (F q : ℝ) * F r / (q * r) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => by positivity
    _ = F q / q * ∑ r ∈ primesIoc a b, (F r : ℝ) / r := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => mul_div_mul_comm _ _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_F_div_le hE ha hab) (by positivity)

/-- `D` is increasing, with
`D(z) - D(y) ≤ 2 (log z + E) (log (z / y) + E) / log² 2`. -/
private lemma harmonicFPair_sub {E : ℝ}
    (hE : ∀ y z : ℝ, 1 ≤ y → y ≤ z → |∑ p ∈ primesIoc y z, log p / p - log (z / y)| ≤ E)
    (hE0 : 0 ≤ E) {y z : ℝ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    0 ≤ harmonicFPair z - harmonicFPair y ∧
      harmonicFPair z - harmonicFPair y ≤ 2 * (log z + E) * (log (z / y) + E) / log 2 ^ 2 := by
  have hl2 : 0 < log 2 := log_pos one_lt_two
  have hzy : 0 ≤ log (z / y) + E :=
    add_nonneg (log_nonneg ((one_le_div (by linarith)).mpr hyz)) hE0
  have hz : 0 ≤ log z + E := add_nonneg (log_nonneg (by linarith)) hE0
  -- Split the outer range at `y` and, for `q ≤ y`, the inner range at `y / q`.
  have h : harmonicFPair z - harmonicFPair y =
      ∑ q ∈ primesIoc 1 y, ∑ r ∈ primesIoc (y / q) (z / q) with r ≠ q,
          (F q : ℝ) * F r / (q * r) +
        ∑ q ∈ primesIoc y z, ∑ r ∈ primesIoc 1 (z / q) with r ≠ q,
          (F q : ℝ) * F r / (q * r) := by
    rw [harmonicFPair, harmonicFPair, ← sum_primesIoc_add _ hy hyz]
    have hin : ∀ q ∈ primesIoc 1 y,
        ∑ r ∈ primesIoc 1 (z / q) with r ≠ q, (F q : ℝ) * F r / (q * r) =
          ∑ r ∈ primesIoc 1 (y / q) with r ≠ q, (F q : ℝ) * F r / (q * r) +
            ∑ r ∈ primesIoc (y / q) (z / q) with r ≠ q, (F q : ℝ) * F r / (q * r) := by
      intro q hq
      obtain ⟨hq, -, hqy⟩ := mem_primesIoc.1 hq
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
      simp only [Finset.sum_filter]
      rw [sum_primesIoc_add _ ((one_le_div hq0).mpr hqy) (by gcongr)]
    rw [Finset.sum_congr rfl hin, Finset.sum_add_distrib]
    ring
  have hw : ∀ (q : ℕ) (s : Finset ℕ), 0 ≤ ∑ r ∈ s with r ≠ q, (F q : ℝ) * F r / (q * r) :=
    fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  rw [h]
  refine ⟨add_nonneg (Finset.sum_nonneg fun _ _ => hw _ _)
    (Finset.sum_nonneg fun _ _ => hw _ _), ?_⟩
  have h1 : ∑ q ∈ primesIoc 1 y, ∑ r ∈ primesIoc (y / q) (z / q) with r ≠ q,
      (F q : ℝ) * F r / (q * r) ≤ (log z + E) * (log (z / y) + E) / log 2 ^ 2 := by
    calc _ ≤ ∑ q ∈ primesIoc 1 y, (F q : ℝ) / q * ((log (z / y) + E) / log 2) := by
          refine Finset.sum_le_sum fun q hq => ?_
          obtain ⟨hq, -, hqy⟩ := mem_primesIoc.1 hq
          have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
          have := sum_pair_le hE q ((one_le_div hq0).mpr hqy)
            (div_le_div_of_nonneg_right hyz hq0.le)
          rwa [div_div_div_cancel_right₀ hq0.ne'] at this
      _ = (∑ q ∈ primesIoc 1 y, (F q : ℝ) / q) * ((log (z / y) + E) / log 2) := by
          rw [Finset.sum_mul]
      _ ≤ (log (y / 1) + E) / log 2 * ((log (z / y) + E) / log 2) :=
          mul_le_mul_of_nonneg_right (sum_F_div_le hE le_rfl hy) (by positivity)
      _ ≤ (log z + E) / log 2 * ((log (z / y) + E) / log 2) := by
          rw [div_one]
          gcongr
      _ = _ := by ring
  have h2 : ∑ q ∈ primesIoc y z, ∑ r ∈ primesIoc 1 (z / q) with r ≠ q,
      (F q : ℝ) * F r / (q * r) ≤ (log z + E) * (log (z / y) + E) / log 2 ^ 2 := by
    calc _ ≤ ∑ q ∈ primesIoc y z, (F q : ℝ) / q * ((log z + E) / log 2) := by
          refine Finset.sum_le_sum fun q hq => ?_
          obtain ⟨hq, hyq, hqz⟩ := mem_primesIoc.1 hq
          have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
          refine (sum_pair_le hE q le_rfl ((one_le_div hq0).mpr hqz)).trans ?_
          rw [div_one]
          gcongr
          · exact div_pos (by linarith) hq0
          · exact div_le_self (by linarith) (by linarith)
      _ = (∑ q ∈ primesIoc y z, (F q : ℝ) / q) * ((log z + E) / log 2) := by
          rw [Finset.sum_mul]
      _ ≤ (log (z / y) + E) / log 2 * ((log z + E) / log 2) :=
          mul_le_mul_of_nonneg_right (sum_F_div_le hE hy hyz) (by positivity)
      _ = _ := by ring
  have : 2 * (log z + E) * (log (z / y) + E) / log 2 ^ 2 =
      (log z + E) * (log (z / y) + E) / log 2 ^ 2 +
        (log z + E) * (log (z / y) + E) / log 2 ^ 2 := by ring
  linarith

/-- Dyadic moments of `g` against `H` with errors `O(Π_y L^{k+1} T⁻⁶)` give cumulative
moments with error `O(t L^k T⁻⁶)`, provided `|g(p)| ≪ (log p)^{k+1}`, `H(1) = 0` and
`H(t) - H(y) ≪ L^k (log (t / y) + 1)`. -/
private lemma cumulative_of_dyadic (g : ℕ → ℝ) (H : ℝ → ℝ) (k : ℕ) {K M c K₀ : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hc : 0 ≤ c) (hK₀ : 0 ≤ K₀)
    (hπ : ∀ x : ℝ, 2 ≤ x → ((primesIoc 1 x).card : ℝ) ≤ K₀ * x / log x)
    (hg : ∀ p : ℕ, p.Prime → |g p| ≤ c * log p ^ (k + 1)) (hH : H 1 = 0)
    (hvar : ∀ y t : ℝ, 1 ≤ y → y ≤ t → 3 ≤ t →
      |H t - H y| ≤ M * log t ^ k * (log (t / y) + 1))
    (hdy : ∀ᶠ y : ℝ in atTop,
      |∑ p ∈ dyadicPrimes y, g p - (dyadicPrimes y).card * H y| ≤
        K * (dyadicPrimes y).card * log y ^ (k + 1) / log (log y) ^ 6) :
    ∃ K' : ℝ, ∀ᶠ t : ℝ in atTop,
      |∑ p ∈ primesIoc 1 t, g p - (primesIoc 1 t).card * H t| ≤
        K' * t * log t ^ k / log (log t) ^ 6 := by
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.mp hdy
  refine ⟨32 * (c + 2 * M) + 64 * K * K₀ + 12 * K₀ * M, ?_⟩
  have hT6 : ∀ᶠ t : ℝ in atTop, log (log t) ^ 6 ≤ log t := by
    filter_upwards [((isLittleO_pow_log_id_atTop (n := 6)).comp_tendsto
      tendsto_log_atTop).bound one_pos, eventually_ge_atTop 1] with t ht ht1
    simp only [Function.comp, id, one_mul, Real.norm_eq_abs] at ht
    exact (le_abs_self _).trans (ht.trans_eq (abs_of_nonneg (log_nonneg ht1)))
  have hL4 : ∀ᶠ t : ℝ in atTop, log t ^ 4 ≤ 16 * √t := by
    filter_upwards [((isLittleO_pow_log_id_atTop (n := 4)).comp_tendsto
      tendsto_sqrt_atTop).bound one_pos, eventually_ge_atTop 0] with t ht ht0
    simp only [Function.comp, id, one_mul, Real.norm_eq_abs, log_sqrt ht0] at ht
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (sqrt_nonneg _), div_pow] at ht
    linarith
  filter_upwards [hT6, hL4, (tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop 2,
    tendsto_log_atTop.eventually_ge_atTop 1,
    tendsto_sqrt_atTop.eventually_ge_atTop (max y₀ 3)] with t hT6 hL4 hT hL hst
  simp only [Function.comp] at hT
  set L := log t with hLdef
  set T := log L with hTdef
  have hst3 : 3 ≤ √t := (le_max_right _ _).trans hst
  have hsq : √t * √t = t := mul_self_sqrt (by
    by_contra h
    rw [sqrt_eq_zero_of_nonpos (by linarith)] at hst3
    linarith)
  have ht9 : 9 ≤ t := by nlinarith
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T := by linarith
  have hT60 : 0 < T ^ 6 := pow_pos hT0 6
  have hl2 : log 2 < 1 := log_two_lt_d9.trans (by norm_num)
  -- Choose `I` with `s = t / 2^I ∈ [√t, 2√t]`.
  have hfl : ⌊√t⌋₊ ≠ 0 := (Nat.floor_pos.mpr (by linarith)).ne'
  set I := Nat.log 2 ⌊√t⌋₊ with hIdef
  have hI1 : (2 : ℝ) ^ I ≤ √t := by
    calc (2 : ℝ) ^ I = ((2 ^ I : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ⌊√t⌋₊ := Nat.cast_le.mpr (Nat.pow_log_le_self 2 hfl)
      _ ≤ √t := Nat.floor_le (sqrt_nonneg _)
  have hI2 : √t ≤ 2 * 2 ^ I := by
    have h' : ((⌊√t⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (I + 1) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) _)
    push_cast at h'
    linarith [Nat.lt_floor_add_one √t, pow_succ (2 : ℝ) I]
  have hs1 : √t ≤ t / 2 ^ I := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sqrt_nonneg t]
  have hs2 : t / 2 ^ I ≤ 2 * √t := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sqrt_nonneg t]
  have hs : 1 ≤ t / 2 ^ I := by linarith
  -- The dyads `(y_i, 2 y_i]` with `y_i = t / 2^{i+1}` lie in `[s, t]`.
  have hy : ∀ i ∈ Finset.range I, √t ≤ t / 2 ^ (i + 1) ∧ t / 2 ^ (i + 1) ≤ t := by
    intro i hi
    refine ⟨hs1.trans (div_le_div_of_nonneg_left ht0.le (by positivity)
      (pow_le_pow_right₀ one_le_two (Finset.mem_range.mp hi))), ?_⟩
    exact div_le_self ht0.le (one_le_pow₀ one_le_two)
  have hlog : ∀ y : ℝ, √t ≤ y → L / 2 ≤ log y := fun y hy => by
    rw [← log_sqrt ht0.le]
    exact log_le_log (by linarith) hy
  have hA := sum_primesIoc_dyadic g I hs
  have hN : ((primesIoc 1 t).card : ℝ) = (primesIoc 1 (t / 2 ^ I)).card +
      ∑ i ∈ Finset.range I, ((dyadicPrimes (t / 2 ^ (i + 1))).card : ℝ) := by
    simp only [Finset.cast_card]
    exact sum_primesIoc_dyadic (fun _ => 1) I hs
  have hsplit : ∑ p ∈ primesIoc 1 t, g p - (primesIoc 1 t).card * H t =
      (∑ p ∈ primesIoc 1 (t / 2 ^ I), g p - (primesIoc 1 (t / 2 ^ I)).card * H t) +
        ∑ i ∈ Finset.range I, (∑ p ∈ dyadicPrimes (t / 2 ^ (i + 1)), g p -
          (dyadicPrimes (t / 2 ^ (i + 1))).card * H (t / 2 ^ (i + 1))) +
        ∑ i ∈ Finset.range I, (dyadicPrimes (t / 2 ^ (i + 1))).card *
          (H (t / 2 ^ (i + 1)) - H t) := by
    rw [hA, hN]
    simp only [Finset.sum_sub_distrib, mul_sub, add_mul, Finset.sum_mul]
    ring
  -- The primes up to `s`.
  have hhead : |∑ p ∈ primesIoc 1 (t / 2 ^ I), g p - (primesIoc 1 (t / 2 ^ I)).card * H t| ≤
      32 * (c + 2 * M) * (t * L ^ k / T ^ 6) := by
    have hHt : |H t| ≤ 2 * M * L ^ (k + 1) := by
      have := hvar 1 t le_rfl (by linarith) (by linarith)
      rw [hH, sub_zero, div_one] at this
      calc |H t| ≤ M * L ^ k * (L + 1) := this
        _ ≤ M * L ^ k * (2 * L) := by gcongr; linarith
        _ = 2 * M * L ^ (k + 1) := by ring
    have hsum : |∑ p ∈ primesIoc 1 (t / 2 ^ I), g p| ≤
        (primesIoc 1 (t / 2 ^ I)).card * (c * L ^ (k + 1)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_).trans_eq (nsmul_eq_mul _ _))
      obtain ⟨hp, -, hps⟩ := mem_primesIoc.1 hp
      refine (hg p hp).trans ?_
      gcongr
      exact log_le_log (by exact_mod_cast hp.pos)
        (hps.trans (div_le_self ht0.le (one_le_pow₀ one_le_two)))
    have key : 2 * √t * L ≤ 32 * t / T ^ 6 := by
      rw [le_div_iff₀ hT60]
      have hL2 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
      calc 2 * √t * L * T ^ 6 ≤ 2 * √t * L * L := by gcongr
        _ = 2 * √t * L ^ 2 := by ring
        _ ≤ 2 * √t * (16 * √t) := by gcongr; linarith
        _ = 32 * t := by linear_combination 32 * hsq
    calc _ ≤ |∑ p ∈ primesIoc 1 (t / 2 ^ I), g p| +
          |((primesIoc 1 (t / 2 ^ I)).card : ℝ) * H t| := abs_sub _ _
      _ ≤ (primesIoc 1 (t / 2 ^ I)).card * (c * L ^ (k + 1)) +
          (primesIoc 1 (t / 2 ^ I)).card * (2 * M * L ^ (k + 1)) := by
        rw [abs_mul, Nat.abs_cast]
        gcongr
      _ = (primesIoc 1 (t / 2 ^ I)).card * ((c + 2 * M) * L ^ (k + 1)) := by ring
      _ ≤ 2 * √t * ((c + 2 * M) * L ^ (k + 1)) :=
        mul_le_mul_of_nonneg_right ((card_primesIoc_one_le (by positivity)).trans hs2)
          (mul_nonneg (by linarith) (by positivity))
      _ = 2 * √t * L * ((c + 2 * M) * L ^ k) := by ring
      _ ≤ 32 * t / T ^ 6 * ((c + 2 * M) * L ^ k) :=
        mul_le_mul_of_nonneg_right key (mul_nonneg (by linarith) (by positivity))
      _ = _ := by ring
  -- The dyadic errors.
  have hmid : |∑ i ∈ Finset.range I, (∑ p ∈ dyadicPrimes (t / 2 ^ (i + 1)), g p -
      (dyadicPrimes (t / 2 ^ (i + 1))).card * H (t / 2 ^ (i + 1)))| ≤
      64 * K * K₀ * (t * L ^ k / T ^ 6) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hK' : 0 ≤ 64 * K * L ^ (k + 1) / T ^ 6 := by
      have := mul_nonneg hK (pow_nonneg hL0.le (k + 1))
      positivity
    calc _ ≤ ∑ i ∈ Finset.range I, 64 * K * L ^ (k + 1) / T ^ 6 *
          (dyadicPrimes (t / 2 ^ (i + 1))).card := by
          refine Finset.sum_le_sum fun i hi => ?_
          obtain ⟨hy1, hy2⟩ := hy i hi
          set y := t / 2 ^ (i + 1)
          have hly := hlog y hy1
          have hly' : log y ≤ L := log_le_log (by linarith) hy2
          have hTy : T / 2 ≤ log (log y) := by
            have : log (L / 2) ≤ log (log y) := log_le_log (by linarith) hly
            rw [log_div hL0.ne' two_ne_zero] at this
            linarith
          refine (hy₀ y ((le_max_left _ _).trans (hst.trans hy1))).trans ?_
          calc K * (dyadicPrimes y).card * log y ^ (k + 1) / log (log y) ^ 6 =
              K * (dyadicPrimes y).card * (log y ^ (k + 1) / log (log y) ^ 6) := by ring
            _ ≤ K * (dyadicPrimes y).card * (L ^ (k + 1) / (T / 2) ^ 6) := by
              refine mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity)
                (pow_le_pow_left₀ (by linarith) hly' _) (by positivity)
                (pow_le_pow_left₀ (by linarith) hTy _)) (mul_nonneg hK (by positivity))
            _ = _ := by ring
      _ = 64 * K * L ^ (k + 1) / T ^ 6 *
          ∑ i ∈ Finset.range I, ((dyadicPrimes (t / 2 ^ (i + 1))).card : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ 64 * K * L ^ (k + 1) / T ^ 6 * (K₀ * t / L) := by
          refine mul_le_mul_of_nonneg_left ?_ hK'
          refine le_trans ?_ (hπ t (by linarith))
          linarith [hN, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (primesIoc 1 (t / 2 ^ I)).card)]
      _ = _ := by
          field_simp
          ring
  -- The variation of `H` across the dyads.
  have hvar' : |∑ i ∈ Finset.range I, (dyadicPrimes (t / 2 ^ (i + 1))).card *
      (H (t / 2 ^ (i + 1)) - H t)| ≤ 12 * K₀ * M * (t * L ^ k / T ^ 6) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ i ∈ Finset.range I, K₀ * M * (4 * t * L ^ k / L) *
          (((i : ℝ) + 2) / 2 ^ (i + 1)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          obtain ⟨hy1, hy2⟩ := hy i hi
          have hty : t / (t / 2 ^ (i + 1)) = 2 ^ (i + 1) := div_div_cancel₀ ht0.ne'
          set y := t / 2 ^ (i + 1) with hydef
          have hsub : dyadicPrimes y ⊆ primesIoc 1 (2 * y) := by
            rw [dyadicPrimes_eq_primesIoc]
            exact Finset.filter_subset_filter _
              (Finset.Ioc_subset_Ioc_left (Nat.floor_le_floor (by linarith)))
          have hNy : ((dyadicPrimes y).card : ℝ) ≤ K₀ * (2 * y) / (L / 2) := by
            refine (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
              ((hπ _ (by linarith)).trans ?_)
            refine div_le_div_of_nonneg_left (by positivity) (by linarith) ?_
            exact (hlog y hy1).trans (log_le_log (by linarith) (by linarith))
          have hHy : |H t - H y| ≤ M * L ^ k * ((i : ℝ) + 2) := by
            refine (hvar y t (by linarith) hy2 (by linarith)).trans ?_
            rw [hty, log_pow]
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hM (by positivity))
            push_cast
            nlinarith [mul_le_mul_of_nonneg_left hl2.le (by positivity : (0 : ℝ) ≤ i + 1)]
          rw [abs_mul, Nat.abs_cast, abs_sub_comm]
          calc ((dyadicPrimes y).card : ℝ) * |H t - H y| ≤
              K₀ * (2 * y) / (L / 2) * (M * L ^ k * ((i : ℝ) + 2)) :=
                mul_le_mul hNy hHy (abs_nonneg _) (by positivity)
            _ = _ := by
                rw [hydef]
                field_simp
                ring
      _ = K₀ * M * (4 * t * L ^ k / L) *
          ∑ i ∈ Finset.range I, ((i : ℝ) + 2) / 2 ^ (i + 1) := by rw [Finset.mul_sum]
      _ ≤ K₀ * M * (4 * t * L ^ k / L) * 3 :=
          mul_le_mul_of_nonneg_left (sum_range_div_two_pow_le I)
            (mul_nonneg (mul_nonneg hK₀ hM) (by positivity))
      _ = K₀ * M * (12 * (t * L ^ k) / L) := by ring
      _ ≤ K₀ * M * (12 * (t * L ^ k) / T ^ 6) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) hT60 hT6)
            (mul_nonneg hK₀ hM)
      _ = _ := by ring
  rw [hsplit]
  calc _ ≤ _ := abs_add_three _ _ _
    _ ≤ _ := add_le_add_three hhead hmid hvar'
    _ = _ := by ring

/-- Dyadic prime moments with errors `O(Π_y L T⁻⁶)` and `O(Π_y L² T⁻⁶)` give
cumulative moments `A₁(t) = π(t) B(t) + O(t T⁻⁶)` and
`A₂(t) = π(t) (C(t) + D(t)) + O(t L T⁻⁶)`. -/
theorem cumulative_moments {K : ℝ}
    (h : ∀ᶠ y : ℝ in Filter.atTop,
      |∑ p ∈ dyadicPrimes y, (F p : ℝ) - (dyadicPrimes y).card * harmonicF y| ≤
          K * (dyadicPrimes y).card * Real.log y / Real.log (Real.log y) ^ 6 ∧
        |∑ p ∈ dyadicPrimes y, (F p : ℝ) ^ 2 -
            (dyadicPrimes y).card * (harmonicFSq y + harmonicFPair y)| ≤
          K * (dyadicPrimes y).card * Real.log y ^ 2 / Real.log (Real.log y) ^ 6) :
    ∃ K' : ℝ, ∀ᶠ t : ℝ in Filter.atTop,
      |primeF t - (primesIoc 1 t).card * harmonicF t| ≤
          K' * t / Real.log (Real.log t) ^ 6 ∧
        |primeFSq t - (primesIoc 1 t).card * (harmonicFSq t + harmonicFPair t)| ≤
          K' * t * Real.log t / Real.log (Real.log t) ^ 6 := by
  obtain ⟨E, hE0, hE⟩ := mertens_first
  obtain ⟨K₀, hK₀, hπ⟩ := card_primesIoc_le
  have hl2 : 0 < log 2 := log_pos one_lt_two
  have h3 : 1 ≤ log 3 := by
    rw [le_log_iff_exp_le (by norm_num)]
    exact (exp_one_lt_d9.trans (by norm_num)).le
  -- Replacing `K` by `max K 0` in the dyadic bounds.
  have hK : ∀ y : ℝ, 1 ≤ y → ∀ n : ℕ, ∀ N : ℕ,
      K * N * log y ^ n / log (log y) ^ 6 ≤ max K 0 * N * log y ^ n / log (log y) ^ 6 :=
    fun y hy n N => div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
      (pow_nonneg (log_nonneg hy) _)) (by positivity)
  -- The first moment.
  obtain ⟨K₁, hK₁⟩ := cumulative_of_dyadic (fun p => (F p : ℝ)) harmonicF 0
    (K := max K 0) (M := (1 + E) / log 2) (c := 1 / log 2) (le_max_right _ _)
    (by positivity) (by positivity) hK₀ hπ
    (fun p hp => by
      rw [abs_of_nonneg (by positivity), zero_add, pow_one, one_div, ← div_eq_inv_mul]
      exact F_le_log_div_log_two hp.ne_zero)
    (by simp [harmonicF, primesIoc])
    (fun y t hy hyt _ => by
      obtain ⟨h0, h1⟩ := harmonicF_sub hE hy hyt
      have hb : 0 ≤ log (t / y) := log_nonneg ((one_le_div (by linarith)).mpr hyt)
      rw [abs_of_nonneg h0, pow_zero, mul_one, div_mul_eq_mul_div]
      exact h1.trans (div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hE0 hb]) hl2.le))
    (by
      filter_upwards [h, eventually_ge_atTop 1] with y hy hy1
      exact hy.1.trans (by simpa using hK y hy1 1 (dyadicPrimes y).card))
  -- The second moment.
  obtain ⟨K₂, hK₂⟩ := cumulative_of_dyadic (fun p => (F p : ℝ) ^ 2)
    (fun x => harmonicFSq x + harmonicFPair x) 1
    (K := max K 0) (M := 3 * (1 + E) ^ 2 / log 2 ^ 2) (c := 1 / log 2 ^ 2) (le_max_right _ _)
    (by positivity) (by positivity) hK₀ hπ
    (fun p hp => by
      rw [abs_of_nonneg (by positivity), one_div, ← div_eq_inv_mul, ← div_pow]
      exact pow_le_pow_left₀ (by positivity) (F_le_log_div_log_two hp.ne_zero) _)
    (by simp [harmonicFSq, harmonicFPair, primesIoc])
    (fun y t hy hyt ht => by
      obtain ⟨c0, c1⟩ := harmonicFSq_sub hE hy hyt
      obtain ⟨d0, d1⟩ := harmonicFPair_sub hE hE0 hy hyt
      have ha : 1 ≤ log t := h3.trans (log_le_log (by norm_num) ht)
      have hb : 0 ≤ log (t / y) := log_nonneg ((one_le_div (by linarith)).mpr hyt)
      have hsplit : harmonicFSq t + harmonicFPair t - (harmonicFSq y + harmonicFPair y) =
          (harmonicFSq t - harmonicFSq y) + (harmonicFPair t - harmonicFPair y) := by ring
      rw [hsplit, abs_of_nonneg (by linarith), pow_one]
      calc _ ≤ log t * (log (t / y) + E) / log 2 ^ 2 +
            2 * (log t + E) * (log (t / y) + E) / log 2 ^ 2 := add_le_add c1 d1
        _ = (log t * (log (t / y) + E) + 2 * (log t + E) * (log (t / y) + E)) /
            log 2 ^ 2 := by ring
        _ ≤ 3 * (1 + E) ^ 2 * log t * (log (t / y) + 1) / log 2 ^ 2 := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          nlinarith [mul_nonneg (mul_nonneg hE0 hb) (sub_nonneg.mpr ha),
            mul_nonneg (mul_nonneg hE0 hE0) (sub_nonneg.mpr ha), mul_nonneg hE0 hb,
            mul_nonneg (mul_nonneg (mul_nonneg hE0 hE0) hb) (by linarith : (0 : ℝ) ≤ log t),
            mul_nonneg hE0 (by linarith : (0 : ℝ) ≤ log t)]
        _ = _ := by ring)
    (by
      filter_upwards [h, eventually_ge_atTop 1] with y hy hy1
      exact hy.2.trans (hK y hy1 2 (dyadicPrimes y).card))
  refine ⟨max K₁ K₂, ?_⟩
  filter_upwards [hK₁, hK₂, eventually_ge_atTop 1] with t h₁ h₂ ht
  refine ⟨h₁.trans ?_, h₂.trans ?_⟩
  · rw [pow_zero, mul_one]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by linarith)) (by positivity)
  · rw [pow_one]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_max_right _ _) (by linarith)) (log_nonneg ht)) (by positivity)

end Erdos408
