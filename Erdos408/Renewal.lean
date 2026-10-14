module

public import Erdos408.Mertens

/-!
# The dyadic renewal equations

Let `h_k = ∑_{2^k < p ≤ 2^{k+1}} 1 / p` and `P_K = ∏_{j < K} (1 + h_j)`.
Mertens' second theorem gives `∑_{K ≤ j < K'} h_j = log (K' / K) + O(1 / K)`,
and `h_j ≪ 1 / j`, so `P_K = c K (1 + O(1 / K))` for a constant `c > 0`.

A discrete Abel inequality on the dyad `(y, 2y]`, `y = 2^k`, with weight `1 / n`
bounds `∑_{y < q ≤ 2y} (F q - B(y)) / q` by `2 / y` times the largest partial
sum `|A₁(t) - π(t) B(y)|` with `y ≤ t ≤ 2y`. The cumulative first moment
`A₁(t) = π(t) B(t) + O(t T⁻⁶)`, the variation `B(t) - B(y) = O(1)` and
Chebyshev's bound `π(2y) ≪ y / k` then give

  `B_{k+1} = B_k (1 + h_k) + e_k`,   `e_k = O(T_k⁻⁶ + 1 / k)`.

Telescoping, `B_K / P_K = B_0 + ∑_{k < K} e_k / P_{k+1}`. The series converges
with tail `O((log K)⁻⁵)`, so `B(x) = α L + O(L T⁻⁵)`. Pillai's bounds
`log q / log 3 ≤ F q ≤ log q / log 2` and Mertens' first theorem give
`1 / log 3 ≤ α ≤ 1 / log 2`.

The second moment works the same way, using
`C_{k+1} = C_k (1 + h_k) + D_k h_k + e'_k` with `e'_k = O(k / log⁵ k)`. Here
the variation of `C + D` on the dyad is `O(k)` for `C`, since `F q ≤ k + 1`,
and `O(k² / log⁵ k)` for `D`, from the asymptotic
`D(x) = α² L² / 2 + O(L² T⁻⁵)` at both ends. With the cross term
`D_k = α² (k log 2)² / 2 + O(k² T_k⁻⁵)` and `∑_{k < K} k h_k = K + O(log K)`,
the result is `C(x) = α² L² / 2 + O(L² T⁻⁵)`.

This follows *The normal order of the number of iterations of Euler's
function* (Plasma AI, 2026), §5, a discrete version of the renewal argument of
Erdős, Granville, Pomerance and Spiro (1990, Section 2). Only Mertens' theorems
and Chebyshev's bound are used, not a quantitative prime number theorem.
-/

@[expose] public section

namespace Erdos408

open Filter Finset Real

/-! ### Prime sums over intervals -/

/-- With natural endpoints, `primesIoc` is a filtered `Finset.Ioc`. -/
private lemma primesIoc_natCast (m n : ℕ) :
    primesIoc m n = (Ioc m n).filter Nat.Prime := by
  simp [primesIoc]

/-- Mertens' first theorem bounds `∑_{y < q ≤ t} F q / q` for `y ≤ t ≤ 2 y`. -/
private lemma exists_sum_F_div_le : ∃ V : ℝ, 0 ≤ V ∧ ∀ y t : ℝ, 1 ≤ y → y ≤ t → t ≤ 2 * y →
    ∑ q ∈ primesIoc y t, (F q : ℝ) / q ≤ V := by
  obtain ⟨E, hE0, hE⟩ := mertens_first
  have hl2 : 0 < log 2 := log_pos one_lt_two
  refine ⟨(log 2 + E) / log 2, by positivity, fun y t hy hyt ht => ?_⟩
  calc ∑ q ∈ primesIoc y t, (F q : ℝ) / q
      ≤ ∑ q ∈ primesIoc y t, log q / q / log 2 := by
        refine sum_le_sum fun q hq => ?_
        have hq := (mem_primesIoc.1 hq).1
        rw [div_right_comm]
        gcongr
        exact F_le_log_div_log_two hq.ne_zero
    _ = (∑ q ∈ primesIoc y t, log q / q) / log 2 := by rw [sum_div]
    _ ≤ (log 2 + E) / log 2 := by
        gcongr
        have h1 := (abs_le.1 (hE y t hy hyt)).2
        have h2 : log (t / y) ≤ log 2 :=
          log_le_log (div_pos (by linarith) (by linarith)) ((div_le_iff₀ (by linarith)).2 ht)
        linarith

/-- Pillai's bounds and Mertens' first theorem give `B(x) = Θ(log x)`. -/
private lemma exists_harmonicF_bounds : ∃ E : ℝ, ∀ x : ℝ, 1 ≤ x →
    (log x - E) / log 3 ≤ harmonicF x ∧ harmonicF x ≤ (log x + E) / log 2 := by
  obtain ⟨E, hE0, hE⟩ := mertens_first
  refine ⟨E, fun x hx => ?_⟩
  have h := abs_le.1 (hE 1 x le_rfl hx)
  rw [div_one] at h
  have hsum : ∀ c : ℝ, ∑ q ∈ primesIoc 1 x, log q / q / c =
      (∑ q ∈ primesIoc 1 x, log q / q) / c := fun c => by rw [sum_div]
  constructor
  · calc (log x - E) / log 3 ≤ (∑ q ∈ primesIoc 1 x, log q / q) / log 3 := by
          gcongr; linarith
      _ = ∑ q ∈ primesIoc 1 x, log q / q / log 3 := (hsum _).symm
      _ ≤ harmonicF x := by
          refine sum_le_sum fun q hq => ?_
          have hq := (mem_primesIoc.1 hq).1
          rw [div_right_comm]
          gcongr
          exact log_div_log_three_le_F hq.ne_zero
  · calc harmonicF x ≤ ∑ q ∈ primesIoc 1 x, log q / q / log 2 := by
          refine sum_le_sum fun q hq => ?_
          have hq := (mem_primesIoc.1 hq).1
          rw [div_right_comm]
          gcongr
          exact F_le_log_div_log_two hq.ne_zero
      _ = (∑ q ∈ primesIoc 1 x, log q / q) / log 2 := hsum _
      _ ≤ (log x + E) / log 2 := by gcongr; linarith

/-! ### Elementary estimates -/

/-- A sum dominated by the increments of `g` is at most the total increment. -/
private lemma sum_Ico_le_sub {a g : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (h : ∀ k, m ≤ k → k < n → a k ≤ g (k + 1) - g k) : ∑ k ∈ Ico m n, a k ≤ g n - g m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [sum_Ico_succ_top hmn]
    have h1 := ih fun k hk hkn => h k hk (by omega)
    have h2 := h n hmn (by omega)
    linarith

/-- A sequence oscillating by at most `ρ n → 0` after `n` converges, within `ρ n` of the
limit at `n`. -/
private lemma exists_abs_sub_le {u ρ : ℕ → ℝ} {N : ℕ} (hρ : Tendsto ρ atTop (nhds 0))
    (h : ∀ n, N ≤ n → ∀ m, n ≤ m → |u m - u n| ≤ ρ n) :
    ∃ a, ∀ n, N ≤ n → |u n - a| ≤ ρ n := by
  have hu : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨n, hn, hnN⟩ := ((hρ.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop N)).exists
    exact ⟨n, fun m hm => (h n hnN m hm).trans_lt hn⟩
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hu
  refine ⟨a, fun n hn => ?_⟩
  rw [abs_sub_comm]
  exact le_of_tendsto ((ha.sub_const _).abs) (eventually_atTop.2 ⟨n, fun m hm => h n hn m hm⟩)

/-- Eventually `log x ^ n ≤ x`. -/
private lemma eventually_log_pow_le (n : ℕ) : ∀ᶠ x : ℝ in atTop, log x ^ n ≤ x := by
  filter_upwards [isLittleO_pow_log_id_atTop.bound one_pos, eventually_ge_atTop 1] with x hx hx1
  rwa [norm_of_nonneg (pow_nonneg (log_nonneg hx1) _), id, norm_of_nonneg (by linarith),
    one_mul] at hx

/-- Eventually `log k ^ n ≤ k` for naturals. -/
private lemma eventually_log_pow_le_nat (n : ℕ) : ∀ᶠ k : ℕ in atTop, log k ^ n ≤ k :=
  tendsto_natCast_atTop_atTop.eventually (eventually_log_pow_le n)

/-- `log k → ∞` along the naturals. -/
private lemma tendsto_log_nat : Tendsto (fun k : ℕ => log k) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `(log log x)ⁿ → ∞` for `n ≠ 0`. -/
private lemma tendsto_log_log_pow (n : ℕ) (hn : n ≠ 0) :
    Tendsto (fun x : ℝ => log (log x) ^ n) atTop atTop :=
  (tendsto_pow_atTop hn).comp (tendsto_log_atTop.comp tendsto_log_atTop)

/-- `5 x⁴ (y - x) ≤ y⁵ - x⁵ ≤ 5 y⁴ (y - x)` for `0 ≤ x ≤ y`. -/
private lemma pow_five_sub_bounds {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    5 * x ^ 4 * (y - x) ≤ y ^ 5 - x ^ 5 ∧ y ^ 5 - x ^ 5 ≤ 5 * y ^ 4 * (y - x) := by
  have hy : 0 ≤ y := hx.trans hxy
  have e : y ^ 5 - x ^ 5 = (y - x) * (y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 + y * x ^ 3 + x ^ 4) := by
    ring
  have h1 := pow_le_pow_left₀ hx hxy 2
  have h2 := pow_le_pow_left₀ hx hxy 3
  have h3 := pow_le_pow_left₀ hx hxy 4
  have hs1 : 5 * x ^ 4 ≤ y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 + y * x ^ 3 + x ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right h2 hx, mul_le_mul_of_nonneg_right h1 (sq_nonneg x),
      mul_le_mul_of_nonneg_right hxy (pow_nonneg hx 3)]
  have hs2 : y ^ 4 + y ^ 3 * x + y ^ 2 * x ^ 2 + y * x ^ 3 + x ^ 4 ≤ 5 * y ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hxy (pow_nonneg hy 3),
      mul_le_mul_of_nonneg_left h1 (sq_nonneg y), mul_le_mul_of_nonneg_left h2 hy]
  have hyx : 0 ≤ y - x := by linarith
  rw [e]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hs1 hyx]
  · nlinarith [mul_le_mul_of_nonneg_left hs2 hyx]

/-- For `k ≥ 3`, `x = log k` and `y = log (k + 1)` satisfy `1 ≤ x < y ≤ 2 x` and
`1 / (2 k) ≤ y - x ≤ 1 / k`. -/
private lemma log_succ_bounds {k : ℕ} (hk : 3 ≤ k) :
    1 ≤ log k ∧ log k ≤ log (k + 1) ∧ log (k + 1) ≤ 2 * log k ∧
      1 / (2 * k) ≤ log (k + 1) - log k ∧ log (k + 1) - log k ≤ 1 / k := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  refine ⟨?_, log_le_log hk0 (by linarith), ?_, ?_, ?_⟩
  · rw [le_log_iff_exp_le hk0]
    linarith [exp_one_lt_d9]
  · rw [← log_rpow hk0, show ((k : ℝ) ^ (2 : ℝ)) = k * k by rw [rpow_two, sq]]
    exact log_le_log (by linarith) (by nlinarith)
  · rw [← log_div (by linarith) hk0.ne']
    have := one_sub_inv_le_log_of_pos (x := (k + 1) / k) (by positivity)
    have e : 1 - ((k + 1) / k : ℝ)⁻¹ = 1 / (k + 1) := by field_simp; ring
    rw [e] at this
    exact (one_div_le_one_div_of_le (by positivity) (by linarith)).trans this
  · rw [← log_div (by linarith) hk0.ne']
    have := log_le_sub_one_of_pos (x := (k + 1) / k) (by positivity)
    rw [add_div, div_self hk0.ne'] at this ⊢
    linarith

/-- The increments of `-13 / log⁵ k` dominate `1 / (k log⁶ k)`. -/
private lemma one_div_mul_log_pow_six_le {k : ℕ} (hk : 3 ≤ k) :
    1 / (k * log k ^ 6) ≤ 13 / log k ^ 5 - 13 / log (k + 1) ^ 5 := by
  obtain ⟨hx1, hxy, hy2, hd1, -⟩ := log_succ_bounds hk
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  set x := log k
  set y := log (k + 1)
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have h5 := (pow_five_sub_bounds hx0.le hxy).1
  have hy5 : y ^ 5 ≤ 32 * x ^ 5 := by
    calc y ^ 5 ≤ (2 * x) ^ 5 := pow_le_pow_left₀ hy0.le hy2 5
      _ = 32 * x ^ 5 := by ring
  have hkd : 1 ≤ (y - x) * (2 * k) := (div_le_iff₀ (by positivity)).1 hd1
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h5 (by positivity : (0 : ℝ) ≤ k * x ^ 6),
    mul_le_mul_of_nonneg_left hy5 (by positivity : (0 : ℝ) ≤ x ^ 5),
    mul_le_mul_of_nonneg_left hkd (by positivity : (0 : ℝ) ≤ x ^ 10),
    mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ x ^ 10) (by linarith : 0 ≤ y - x))
      hk0.le]

/-- For `log k ≥ 160`, the increments of `64 k / log⁵ k` dominate `1 / log⁵ k`. -/
private lemma one_div_log_pow_five_le {k : ℕ} (hk : 3 ≤ k) (hlog : 160 ≤ log k) :
    1 / log k ^ 5 ≤ 64 * (k + 1) / log (k + 1) ^ 5 - 64 * k / log k ^ 5 := by
  obtain ⟨hx1, hxy, hy2, -, hd2⟩ := log_succ_bounds hk
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  set x := log k
  set y := log (k + 1)
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have h5 := (pow_five_sub_bounds hx0.le hxy).2
  have hy4 : y ^ 4 ≤ 16 * x ^ 4 := by
    calc y ^ 4 ≤ (2 * x) ^ 4 := pow_le_pow_left₀ hy0.le hy2 4
      _ = 16 * x ^ 4 := by ring
  have hy5 : y ^ 5 ≤ 32 * x ^ 5 := by
    calc y ^ 5 ≤ (2 * x) ^ 5 := pow_le_pow_left₀ hy0.le hy2 5
      _ = 32 * x ^ 5 := by ring
  have hkd : (y - x) * k ≤ 1 := (le_div_iff₀ hk0).1 (by simpa using hd2)
  have hA : k * (y ^ 5 - x ^ 5) ≤ 80 * x ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left h5 hk0.le,
      mul_le_mul_of_nonneg_left hkd (by positivity : (0 : ℝ) ≤ 5 * y ^ 4)]
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ x ^ 5),
    mul_le_mul_of_nonneg_left hy5 (by positivity : (0 : ℝ) ≤ x ^ 5),
    mul_nonneg (by positivity : (0 : ℝ) ≤ x ^ 9) (by linarith : (0 : ℝ) ≤ x - 160)]

/-- On the dyad `[2^k, 2^{k+1}]` with `k ≥ 3`, `log t ≍ k` and `log log t ≥ log k / 2`. -/
private lemma dyad_log_bounds {k : ℕ} (hk : 3 ≤ k) {t : ℝ} (ht : 2 ^ k ≤ t)
    (ht' : t ≤ 2 ^ (k + 1)) :
    k * log 2 ≤ log t ∧ log t ≤ (k + 1) * log 2 ∧ log k / 2 ≤ log (log t) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hl2 := log_two_gt_d9
  have hk0 : (0 : ℝ) < k := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hkl : 0 < k * log 2 := mul_pos hk0 (log_pos one_lt_two)
  have h1 : k * log 2 ≤ log t := by
    rw [← log_pow]
    exact log_le_log (by positivity) ht
  refine ⟨h1, ?_, ?_⟩
  · rw [← Nat.cast_succ, ← log_pow]
    exact log_le_log ht0 ht'
  · have h22 : (1 : ℝ) / 3 ≤ log 2 ^ 2 := by nlinarith
    have h2 : log k ≤ log ((k * log 2) ^ 2) := by
      refine log_le_log hk0 ?_
      calc (k : ℝ) = k * (3 * (1 / 3)) := by ring
        _ ≤ k * (k * log 2 ^ 2) := by gcongr
        _ = (k * log 2) ^ 2 := by ring
    rw [log_pow, Nat.cast_ofNat] at h2
    have h3 : log (k * log 2) ≤ log (log t) := log_le_log hkl h1
    linarith

/-! ### The renewal product -/

/-- The dyadic prime harmonic sum `h_k = ∑_{2^k < p ≤ 2^{k+1}} 1 / p`. -/
noncomputable def dyadH (k : ℕ) : ℝ :=
  ∑ p ∈ primesIoc (2 ^ k) (2 ^ (k + 1)), (1 : ℝ) / p

/-- The renewal product `P_K = ∏_{j < K} (1 + h_j)`. -/
noncomputable def dyadP (K : ℕ) : ℝ :=
  ∏ j ∈ range K, (1 + dyadH j)

/-- `h_k ≥ 0`. -/
private lemma dyadH_nonneg (k : ℕ) : 0 ≤ dyadH k :=
  sum_nonneg fun _ _ => by positivity

/-- `P_K > 0`. -/
private lemma dyadP_pos (K : ℕ) : 0 < dyadP K :=
  prod_pos fun j _ => by linarith [dyadH_nonneg j]

/-- `P_{K+1} = P_K (1 + h_K)`. -/
private lemma dyadP_succ (K : ℕ) : dyadP (K + 1) = dyadP K * (1 + dyadH K) :=
  prod_range_succ _ _

/-- Dyadic blocks of a prime sum add up to the sum over `(2^K, 2^{K'}]`. -/
private lemma sum_Ico_dyad (g : ℕ → ℝ) {K K' : ℕ} (hKK' : K ≤ K') :
    ∑ j ∈ Ico K K', ∑ p ∈ primesIoc (2 ^ j) (2 ^ (j + 1)), g p =
      ∑ p ∈ primesIoc (2 ^ K) (2 ^ K'), g p := by
  induction K', hKK' using Nat.le_induction with
  | base => simp [primesIoc]
  | succ K' hKK' ih =>
    rw [sum_Ico_succ_top hKK', ih, sum_primesIoc_add _ (pow_le_pow_right₀ one_le_two hKK')
      (pow_le_pow_right₀ one_le_two K'.le_succ)]

/-- Mertens' second theorem on `(2^K, 2^{K'}]`. -/
private lemma exists_abs_sum_Ico_dyadH_sub_le : ∃ E : ℝ, 0 ≤ E ∧ ∀ K K' : ℕ, 1 ≤ K → K ≤ K' →
    |∑ j ∈ Ico K K', dyadH j - (log K' - log K)| ≤ E / K := by
  obtain ⟨E, hE0, hE⟩ := mertens_second
  have hl2 : 0 < log 2 := log_pos one_lt_two
  refine ⟨E / log 2, by positivity, fun K K' hK hKK' => ?_⟩
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hK'0 : (0 : ℝ) < K' := Nat.cast_pos.2 (by omega)
  have h := hE (2 ^ K) (2 ^ K') (by simpa using pow_le_pow_right₀ one_le_two hK)
    (pow_le_pow_right₀ one_le_two hKK')
  rw [log_pow, log_pow, mul_div_mul_right _ _ hl2.ne', log_div hK'0.ne' hK0.ne'] at h
  unfold dyadH
  rw [sum_Ico_dyad _ hKK', div_div, mul_comm]
  exact h

/-- `h_k ≤ c / k` for `k ≥ 1`. -/
private lemma exists_dyadH_le : ∃ c : ℝ, 0 ≤ c ∧ ∀ k : ℕ, 1 ≤ k → dyadH k ≤ c / k := by
  obtain ⟨E, hE0, hE⟩ := exists_abs_sum_Ico_dyadH_sub_le
  refine ⟨1 + E, by positivity, fun k hk => ?_⟩
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have h := (abs_le.1 (hE k (k + 1) hk k.le_succ)).2
  rw [Nat.Ico_succ_singleton, sum_singleton, Nat.cast_succ, ← log_div (by positivity) hk0.ne']
    at h
  rw [add_div, div_self hk0.ne'] at h
  have hlog := log_le_sub_one_of_pos (x := (k + 1) / k) (by positivity)
  rw [add_div, div_self hk0.ne', add_sub_cancel_left] at hlog
  rw [add_div]
  linarith

/-- The renewal product is `c K + O(1)` for some `c > 0`. -/
private lemma exists_dyadP_sub : ∃ c E : ℝ, 0 < c ∧ 0 ≤ E ∧
    ∀ᶠ K : ℕ in atTop, |dyadP K - c * K| ≤ E ∧ c * K / 2 ≤ dyadP K := by
  obtain ⟨E, hE0, hE⟩ := exists_abs_sum_Ico_dyadH_sub_le
  obtain ⟨ch, hch0, hch⟩ := exists_dyadH_le
  set Ev := E + 2 * ch ^ 2
  have hlogP (K : ℕ) : log (dyadP K) = ∑ j ∈ range K, log (1 + dyadH j) :=
    log_prod fun j _ => by linarith [dyadH_nonneg j]
  -- `v_K = log P_K - log K` oscillates by `O(1 / K)`
  set v : ℕ → ℝ := fun K => log (dyadP K) - log K
  have hv : ∀ K, 1 ≤ K → ∀ K', K ≤ K' → |v K' - v K| ≤ Ev / K := by
    intro K hK K' hKK'
    have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
    have hsplit : v K' - v K = (∑ j ∈ Ico K K', dyadH j - (log K' - log K)) -
        ∑ j ∈ Ico K K', (dyadH j - log (1 + dyadH j)) := by
      simp only [v, hlogP, sum_sub_distrib, sum_Ico_eq_sub _ hKK']
      ring
    -- `0 ≤ h - log (1 + h) ≤ h²` and `h_j² ≤ c² / j² ≤ 2 c² (1 / j - 1 / (j + 1))`
    have h2 : ∑ j ∈ Ico K K', (dyadH j - log (1 + dyadH j)) ≤ 2 * ch ^ 2 / K := by
      have := sum_Ico_le_sub (a := fun j => dyadH j - log (1 + dyadH j))
          (g := fun j : ℕ => -(2 * ch ^ 2 / j)) hKK' fun j hj _ => by
        have hj0 : (0 : ℝ) < j := Nat.cast_pos.2 (by omega)
        have hh0 := dyadH_nonneg j
        have hhj := hch j (by omega)
        have hlog := one_sub_inv_le_log_of_pos (x := 1 + dyadH j) (by linarith)
        have e : 1 - (1 + dyadH j)⁻¹ = dyadH j - dyadH j ^ 2 / (1 + dyadH j) := by
          field_simp; ring
        have h1 : dyadH j ^ 2 / (1 + dyadH j) ≤ dyadH j ^ 2 :=
          div_le_self (sq_nonneg _) (by linarith)
        have h3 : dyadH j ^ 2 ≤ (ch / j) ^ 2 := pow_le_pow_left₀ hh0 hhj 2
        have h4 : (ch / j) ^ 2 ≤ 2 * ch ^ 2 / j - 2 * ch ^ 2 / (j + 1) := by
          rw [div_pow, div_sub_div _ _ (by positivity) (by positivity),
            div_le_div_iff₀ (by positivity) (by positivity)]
          have hj1 : (1 : ℝ) ≤ j := Nat.one_le_cast.2 (by omega)
          nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ch) hj0.le) (by linarith : (0 : ℝ) ≤ j - 1)]
        push_cast
        linarith
      have hK'0 : (0 : ℝ) ≤ 2 * ch ^ 2 / K' := by positivity
      linarith
    have h3 : 0 ≤ ∑ j ∈ Ico K K', (dyadH j - log (1 + dyadH j)) :=
      sum_nonneg fun j _ => by
        have := log_le_sub_one_of_pos (x := 1 + dyadH j) (by linarith [dyadH_nonneg j])
        linarith
    have h1 := hE K K' hK hKK'
    rw [hsplit, show Ev / K = E / K + 2 * ch ^ 2 / K by rw [add_div]]
    exact (abs_sub _ _).trans (add_le_add h1 (by rw [abs_of_nonneg h3]; exact h2))
  obtain ⟨c₀, hc₀⟩ := exists_abs_sub_le (tendsto_const_div_atTop_nhds_zero_nat Ev) hv
  have hEv : 0 ≤ Ev := by positivity
  refine ⟨exp c₀, 2 * exp c₀ * Ev, exp_pos _, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (4 * Ev)] with K hK hKE
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hδ := hc₀ K hK
  have hδ1 : |v K - c₀| ≤ 1 := hδ.trans ((div_le_one hK0).2 (by linarith))
  have hPK : dyadP K - exp c₀ * K = K * exp c₀ * (exp (v K - c₀) - 1) := by
    simp only [v]
    rw [exp_sub, exp_sub, exp_log (dyadP_pos K), exp_log hK0]
    field_simp
  have hbound : |dyadP K - exp c₀ * K| ≤ 2 * exp c₀ * Ev := by
    rw [hPK, abs_mul, abs_of_pos (by positivity)]
    calc K * exp c₀ * |exp (v K - c₀) - 1| ≤ K * exp c₀ * (2 * (Ev / K)) := by
          gcongr
          exact (abs_exp_sub_one_le hδ1).trans (by linarith)
      _ = 2 * exp c₀ * Ev := by field_simp
  refine ⟨hbound, ?_⟩
  have := (abs_le.1 hbound).1
  nlinarith [exp_pos c₀]

/-- `∑_{k < K} h_k = O(log K)` and `∑_{k < K} k h_k = K + O(log K)`. -/
private lemma exists_sum_dyadH_le : ∃ E : ℝ, 0 ≤ E ∧ ∀ K : ℕ, 1 ≤ K →
    ∑ k ∈ range K, dyadH k ≤ log K + E ∧ |∑ k ∈ range K, k * dyadH k - K| ≤ log K + E := by
  obtain ⟨E₁, hE₁0, hE₁⟩ := mertens_first
  obtain ⟨E₂, hE₂0, hE₂⟩ := exists_abs_sum_Ico_dyadH_sub_le
  have hl2 : 0 < log 2 := log_pos one_lt_two
  refine ⟨dyadH 0 + E₂ + E₁ / log 2, by linarith [dyadH_nonneg 0, div_nonneg hE₁0 hl2.le],
    fun K hK => ?_⟩
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hlogK : 0 ≤ log K := log_nonneg (Nat.one_le_cast.2 hK)
  -- `∑_{k < K} h_k = h_0 + ∑_{1 ≤ k < K} h_k`
  have hS : ∑ k ∈ range K, dyadH k ≤ log K + (dyadH 0 + E₂) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hK]
    have := (abs_le.1 (hE₂ 1 K le_rfl hK)).2
    simp only [Nat.cast_one, log_one, sub_zero, div_one] at this
    linarith
  -- `k h_k ≤ L_k / log 2 ≤ (k + 1) h_k` with `L_k = ∑_{2^k < p ≤ 2^{k+1}} log p / p`
  set L : ℕ → ℝ := fun k => ∑ p ∈ primesIoc (2 ^ k) (2 ^ (k + 1)), log p / p
  have hL (k : ℕ) : k * dyadH k ≤ L k / log 2 ∧ L k / log 2 ≤ k * dyadH k + dyadH k := by
    simp only [L, dyadH, mul_sum, sum_div, ← sum_add_distrib]
    constructor <;> refine sum_le_sum fun p hp => ?_ <;>
      obtain ⟨hp, hlo, hhi⟩ := mem_primesIoc.1 hp <;>
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    · have : k * log 2 ≤ log p := by rw [← log_pow]; exact log_le_log (by positivity) hlo.le
      rw [mul_one_div, div_right_comm]
      gcongr
      rwa [le_div_iff₀ hl2]
    · have : log p ≤ (k + 1) * log 2 := by
        rw [← Nat.cast_succ, ← log_pow]; exact log_le_log hp0 hhi
      rw [mul_one_div, div_right_comm, ← add_div]
      gcongr
      rwa [div_le_iff₀ hl2]
  have hsumL : |∑ k ∈ range K, L k / log 2 - K| ≤ E₁ / log 2 := by
    have h := hE₁ 1 (2 ^ K) le_rfl (one_le_pow₀ one_le_two)
    rw [div_one, log_pow] at h
    rw [← sum_div, range_eq_Ico]
    simp only [L]
    rw [sum_Ico_dyad _ (Nat.zero_le K), pow_zero, show (K : ℝ) = K * log 2 / log 2 by
      field_simp, ← sub_div, abs_div, abs_of_pos hl2]
    gcongr
  have h1 := sum_le_sum fun k (_ : k ∈ range K) => (hL k).1
  have h2 := sum_le_sum fun k (_ : k ∈ range K) => (hL k).2
  rw [sum_add_distrib] at h2
  have h3 := abs_le.1 hsumL
  refine ⟨by linarith, abs_le.2 ⟨by linarith, by linarith [dyadH_nonneg 0]⟩⟩

/-- Telescoping: if `X_{k+1} = X_k (1 + h_k) + f_k` for `k ≥ k₀`, then
`X_K / P_K = X_{k₀} / P_{k₀} + ∑_{k₀ ≤ k < K} f_k / P_{k+1}`. -/
private lemma div_dyadP_eq {X f : ℕ → ℝ} {k₀ : ℕ}
    (hX : ∀ k, k₀ ≤ k → X (k + 1) = X k * (1 + dyadH k) + f k) {K : ℕ} (hK : k₀ ≤ K) :
    X K / dyadP K = X k₀ / dyadP k₀ + ∑ k ∈ Ico k₀ K, f k / dyadP (k + 1) := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    have h1 : 0 < 1 + dyadH K := by linarith [dyadH_nonneg K]
    have h2 := dyadP_pos K
    rw [sum_Ico_succ_top hK, ← add_assoc, ← ih, hX K hK, dyadP_succ]
    field_simp

/-! ### Abel summation on a dyad -/

/-- Abel's inequality: if the partial sums of `a` over `(m, j]` are at most `M` and `w`
decreases to `w (n + 1) ≥ 0`, then `|∑_{m < i ≤ n} a i w i| ≤ M w (m + 1)`. -/
private lemma abs_sum_Ioc_mul_le {a w : ℕ → ℝ} {m n : ℕ} {M : ℝ} (hmn : m ≤ n)
    (hw : ∀ i, m < i → w (i + 1) ≤ w i) (hw0 : 0 ≤ w (n + 1))
    (hS : ∀ j, m ≤ j → j ≤ n → |∑ i ∈ Ioc m j, a i| ≤ M) :
    |∑ i ∈ Ioc m n, a i * w i| ≤ M * w (m + 1) := by
  -- `∑_{m < i ≤ j} a i w i = S_j w (j + 1) + ∑_{m < i ≤ j} S_i (w i - w (i + 1))`
  have key : ∀ j, m ≤ j → j ≤ n →
      |∑ i ∈ Ioc m j, a i * w i - (∑ i ∈ Ioc m j, a i) * w (j + 1)| ≤
        M * (w (m + 1) - w (j + 1)) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; simp
    | succ j hj ih =>
      intro hjn
      have e : ∑ i ∈ Ioc m (j + 1), a i * w i - (∑ i ∈ Ioc m (j + 1), a i) * w (j + 1 + 1) =
          (∑ i ∈ Ioc m j, a i * w i - (∑ i ∈ Ioc m j, a i) * w (j + 1)) +
            (∑ i ∈ Ioc m (j + 1), a i) * (w (j + 1) - w (j + 1 + 1)) := by
        rw [sum_Ioc_succ_top hj, sum_Ioc_succ_top hj]
        ring
      have hwj : 0 ≤ w (j + 1) - w (j + 1 + 1) := by linarith [hw (j + 1) (by omega)]
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hwj]
      have := mul_le_mul_of_nonneg_right (hS (j + 1) (by omega) hjn) hwj
      linarith [ih (by omega)]
  have h1 := key n hmn le_rfl
  have h2 := mul_le_mul_of_nonneg_right (hS n hmn le_rfl) hw0
  rw [← abs_of_nonneg hw0, ← abs_mul] at h2
  calc |∑ i ∈ Ioc m n, a i * w i|
      ≤ |∑ i ∈ Ioc m n, a i * w i - (∑ i ∈ Ioc m n, a i) * w (n + 1)| +
        |(∑ i ∈ Ioc m n, a i) * w (n + 1)| := by
          have := abs_add_le (∑ i ∈ Ioc m n, a i * w i - (∑ i ∈ Ioc m n, a i) * w (n + 1))
            ((∑ i ∈ Ioc m n, a i) * w (n + 1))
          rwa [sub_add_cancel] at this
    _ ≤ M * w (m + 1) := by rw [abs_of_nonneg hw0] at h2; linarith

/-- The dyad step: if `A(t) = π(t) Φ(t) + O(2^k ε)` and `Φ` varies by at most `V` on
`[2^k, 2^{k+1}]`, then `∑_{2^k < p ≤ 2^{k+1}} (g p - Φ(2^k)) / p = O(ε + V / k)`. -/
private lemma abs_sum_dyad_sub_le {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (hπ : ∀ x : ℝ, 2 ≤ x → ((primesIoc 1 x).card : ℝ) ≤ K₀ * x / log x)
    {g : ℕ → ℝ} {Φ : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ}
    (hA : ∀ t : ℝ, 2 ^ k ≤ t → t ≤ 2 ^ (k + 1) →
      |∑ p ∈ primesIoc 1 t, g p - (primesIoc 1 t).card * Φ t| ≤ 2 ^ k * ε)
    (hV : ∀ t : ℝ, 2 ^ k ≤ t → t ≤ 2 ^ (k + 1) → |Φ t - Φ (2 ^ k)| ≤ V) :
    |∑ p ∈ primesIoc (2 ^ k) (2 ^ (k + 1)), (g p - Φ (2 ^ k)) / p| ≤
      2 * ε + 4 * K₀ * V / (k * log 2) := by
  have hl2 : 0 < log 2 := log_pos one_lt_two
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hV0 : 0 ≤ V := by
    have := hV (2 ^ k) le_rfl (by rw [pow_succ]; linarith)
    rwa [sub_self, abs_zero] at this
  set φ := Φ (2 ^ k)
  set M := 2 ^ k * ε + K₀ * 2 ^ (k + 1) * V / (k * log 2)
  -- `|A(t) - π(t) Φ(2^k)| ≤ M` on the dyad
  have hM : ∀ t : ℝ, 2 ^ k ≤ t → t ≤ 2 ^ (k + 1) →
      |∑ p ∈ primesIoc 1 t, (g p - φ)| ≤ M := by
    intro t ht ht'
    have hlog : k * log 2 ≤ log t := by
      rw [← log_pow]; exact log_le_log h2k ht
    have hπt : ((primesIoc 1 t).card : ℝ) ≤ K₀ * 2 ^ (k + 1) / (k * log 2) :=
      (hπ t (le_trans (by simpa using pow_le_pow_right₀ one_le_two hk) ht)).trans
        (div_le_div₀ (by positivity) (by gcongr) (by positivity) hlog)
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul,
      show ∑ p ∈ primesIoc 1 t, g p - (primesIoc 1 t).card * φ =
        (∑ p ∈ primesIoc 1 t, g p - (primesIoc 1 t).card * Φ t) +
          (primesIoc 1 t).card * (Φ t - φ) by ring]
    refine (abs_add_le _ _).trans (add_le_add (hA t ht ht') ?_)
    rw [abs_mul, Nat.abs_cast, mul_div_right_comm]
    exact mul_le_mul hπt (hV t ht ht') (abs_nonneg _) (by positivity)
  -- Abel summation over `n ∈ (2^k, 2^{k+1}]` with weight `1 / n`
  set N := 2 ^ k
  have hN : ((2 : ℝ) ^ k) = (N : ℝ) := by simp [N]
  have hN' : ((2 : ℝ) ^ (k + 1)) = ((2 * N : ℕ) : ℝ) := by simp [N, pow_succ, mul_comm]
  set a : ℕ → ℝ := fun i => if i.Prime then g i - φ else 0
  have hsum : ∑ p ∈ primesIoc (2 ^ k) (2 ^ (k + 1)), (g p - φ) / p =
      ∑ i ∈ Ioc N (2 * N), a i * (1 / (i : ℝ)) := by
    rw [hN, hN', primesIoc_natCast, sum_filter]
    refine sum_congr rfl fun i _ => ?_
    simp only [a]
    split_ifs <;> simp [div_eq_mul_inv]
  have hpartial : ∀ j, N ≤ j → j ≤ 2 * N → |∑ i ∈ Ioc N j, a i| ≤ 2 * M := by
    intro j hj hj'
    have hjr : (2 : ℝ) ^ k ≤ j := by rw [hN]; exact_mod_cast hj
    have hjr' : (j : ℝ) ≤ 2 ^ (k + 1) := by rw [hN']; exact_mod_cast hj'
    have e : ∑ i ∈ Ioc N j, a i =
        ∑ p ∈ primesIoc 1 (j : ℝ), (g p - φ) - ∑ p ∈ primesIoc 1 (2 ^ k), (g p - φ) := by
      rw [← sum_primesIoc_add _ (one_le_pow₀ one_le_two) hjr, add_sub_cancel_left, hN,
        primesIoc_natCast, sum_filter]
    rw [e]
    refine (abs_sub _ _).trans ?_
    linarith [hM j hjr hjr', hM (2 ^ k) le_rfl (by rw [pow_succ]; linarith)]
  rw [hsum]
  have hNpos : (0 : ℝ) < N := by rw [← hN]; exact h2k
  have hN2 : N ≤ 2 * N := by rw [two_mul]; exact Nat.le_add_left N N
  refine (abs_sum_Ioc_mul_le hN2 (fun i hi => ?_) (by positivity) hpartial).trans ?_
  · have : (0 : ℝ) < i := Nat.cast_pos.2 (Nat.zero_lt_of_lt hi)
    push_cast
    gcongr
    linarith
  · have hM0 : 0 ≤ 2 * M := (abs_nonneg _).trans (hpartial N le_rfl hN2)
    calc 2 * M * (1 / ((N + 1 : ℕ) : ℝ)) ≤ 2 * M * (1 / N) := by
          gcongr; linarith
      _ = 2 * ε + 4 * K₀ * V / (k * log 2) := by
          rw [← hN]; simp only [M, pow_succ]; field_simp; ring

/-! ### From dyads to reals -/

/-- A property eventually true of reals holds on `[2^k, ∞)` for large `k`. -/
private lemma eventually_dyad {P : ℝ → Prop} (h : ∀ᶠ t : ℝ in atTop, P t) :
    ∀ᶠ k : ℕ in atTop, ∀ t : ℝ, 2 ^ k ≤ t → P t := by
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 h
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_ge_atTop t₀]
    with k hk t ht using ht₀ t (hk.trans ht)

/-- Bounds `C K^n / log⁵ K` on the dyads `[2^K, 2^{K+1})` give bounds
`K' L^n / T⁵` for large `x`. -/
private lemma exists_of_dyadic {G : ℝ → ℝ} {n : ℕ} {C : ℝ}
    (h : ∀ᶠ K : ℕ in atTop, ∀ x : ℝ, 2 ^ K ≤ x → x < 2 ^ (K + 1) →
      |G x| ≤ C * K ^ n / log K ^ 5) :
    ∃ K' : ℝ, ∀ᶠ x : ℝ in atTop, |G x| ≤ K' * log x ^ n / log (log x) ^ 5 := by
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.1 h
  have hl2 := log_two_gt_d9
  have hl2' := log_two_lt_d9
  refine ⟨32 * |C| / log 2 ^ n, ?_⟩
  filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ max K₁ 3)] with x hx
  have hx8 : (2 : ℝ) ^ 3 ≤ x := le_trans (pow_le_pow_right₀ one_le_two (le_max_right _ _)) hx
  have hfl0 : ⌊x⌋₊ ≠ 0 := (Nat.floor_pos.2 (by linarith)).ne'
  set K := Nat.log 2 ⌊x⌋₊
  have hKK : max K₁ 3 ≤ K :=
    Nat.le_log_of_pow_le one_lt_two (Nat.le_floor (by exact_mod_cast hx))
  have hlo : (2 : ℝ) ^ K ≤ x :=
    le_trans (by exact_mod_cast Nat.pow_log_le_self 2 hfl0) (Nat.floor_le (by linarith))
  have hhi : x < 2 ^ (K + 1) := by
    have h' : (⌊x⌋₊ : ℝ) + 1 ≤ 2 ^ (K + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two ⌊x⌋₊
    linarith [Nat.lt_floor_add_one x]
  have hK3 : 3 ≤ K := le_of_max_le_right hKK
  have hK3' : (3 : ℝ) ≤ K := by exact_mod_cast hK3
  have hG := hK₁ K (le_of_max_le_left hKK) x hlo hhi
  obtain ⟨hlx, hlx', hT⟩ := dyad_log_bounds hK3 hlo hhi.le
  have hlogK := (log_succ_bounds hK3).1
  have hT0 : 0 < log (log x) := by linarith
  -- `T(x) ≤ log ((K + 1) log 2) ≤ log (K²) = 2 log K`
  have hT2 : log (log x) / 2 ≤ log K := by
    have : log (log x) ≤ log ((K : ℝ) ^ 2) :=
      log_le_log (by nlinarith) (by nlinarith)
    rw [log_pow] at this
    push_cast at this
    linarith
  have hKx : (K : ℝ) ≤ log x / log 2 := (le_div_iff₀ (by linarith)).2 hlx
  have hlx0 : 0 < log x := by nlinarith
  calc |G x| ≤ C * K ^ n / log K ^ 5 := hG
    _ ≤ |C| * K ^ n / log K ^ 5 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
          (pow_pos (by linarith) 5).le
    _ ≤ |C| * (log x / log 2) ^ n / (log (log x) / 2) ^ 5 :=
        div_le_div₀ (mul_nonneg (abs_nonneg C) (pow_nonneg (div_nonneg hlx0.le (by linarith)) n))
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg K) hKx n) (abs_nonneg C))
          (pow_pos (by linarith) 5) (pow_le_pow_left₀ (by linarith) hT2 5)
    _ = 32 * |C| / log 2 ^ n * log x ^ n / log (log x) ^ 5 := by
        rw [div_pow, div_pow]
        field_simp
        ring

/-! ### The first renewal -/

/-- The variation of `B` on a dyad is `O(1)`. -/
private lemma abs_harmonicF_sub_le {V : ℝ}
    (hV : ∀ y t : ℝ, 1 ≤ y → y ≤ t → t ≤ 2 * y → ∑ q ∈ primesIoc y t, (F q : ℝ) / q ≤ V)
    {k : ℕ} {t : ℝ} (ht : 2 ^ k ≤ t) (ht' : t ≤ 2 ^ (k + 1)) :
    |harmonicF t - harmonicF (2 ^ k)| ≤ V := by
  have hsplit := sum_primesIoc_add (fun q => (F q : ℝ) / q) (one_le_pow₀ one_le_two) ht
  have hpos : 0 ≤ ∑ q ∈ primesIoc (2 ^ k) t, (F q : ℝ) / q := sum_nonneg fun _ _ => by
    positivity
  simp only [harmonicF] at hsplit ⊢
  rw [← hsplit, add_sub_cancel_left, abs_of_nonneg hpos]
  exact hV _ t (one_le_pow₀ one_le_two) ht (by rw [← pow_succ']; exact ht')

/-- The first renewal step: `B_{k+1} = B_k (1 + h_k) + O(log⁻⁶ k)`. -/
private lemma exists_harmonicF_step {K : ℝ}
    (h : ∀ᶠ t : ℝ in atTop,
      |primeF t - (primesIoc 1 t).card * harmonicF t| ≤ K * t / log (log t) ^ 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
      |harmonicF (2 ^ (k + 1)) - harmonicF (2 ^ k) * (1 + dyadH k)| ≤ C / log k ^ 6 := by
  obtain ⟨V, hV0, hV⟩ := exists_sum_F_div_le
  obtain ⟨K₀, hK₀, hπ⟩ := card_primesIoc_le
  have hl2 : 0 < log 2 := log_pos one_lt_two
  refine ⟨256 * |K| + 4 * K₀ * V / log 2, by positivity, ?_⟩
  filter_upwards [eventually_dyad h, eventually_ge_atTop 3, eventually_log_pow_le_nat 6]
    with k hk hk3 hlog6
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  have hlogk := (log_succ_bounds hk3).1
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
  have h2k' : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := pow_le_pow_right₀ one_le_two k.le_succ
  -- `e_k = ∑_{2^k < q ≤ 2^{k+1}} (F q - B_k) / q`
  have e : harmonicF (2 ^ (k + 1)) - harmonicF (2 ^ k) * (1 + dyadH k) =
      ∑ q ∈ primesIoc (2 ^ k) (2 ^ (k + 1)), ((F q : ℝ) - harmonicF (2 ^ k)) / q := by
    have hsplit : harmonicF (2 ^ (k + 1)) = harmonicF (2 ^ k) +
        ∑ q ∈ primesIoc (2 ^ k) (2 ^ (k + 1)), (F q : ℝ) / q :=
      (sum_primesIoc_add _ h2k h2k').symm
    rw [hsplit, dyadH, mul_add, mul_one, mul_sum, add_sub_add_left_eq_sub, ← sum_sub_distrib]
    exact sum_congr rfl fun q _ => by ring
  rw [e]
  refine (abs_sum_dyad_sub_le hK₀ hπ (g := fun q => (F q : ℝ)) (by omega)
    (ε := 128 * |K| / log k ^ 6) (V := V) (fun t ht ht' => ?_) (fun t ht ht' => ?_)).trans ?_
  · obtain ⟨-, -, hT⟩ := dyad_log_bounds hk3 ht ht'
    calc _ ≤ K * t / log (log t) ^ 6 := hk t ht
      _ ≤ |K| * 2 ^ (k + 1) / (log k / 2) ^ 6 :=
          div_le_div₀ (by positivity) (mul_le_mul (le_abs_self K) ht' (by linarith)
            (abs_nonneg K)) (by positivity) (pow_le_pow_left₀ (by positivity) hT 6)
      _ = 2 ^ k * (128 * |K| / log k ^ 6) := by
          rw [pow_succ, div_pow]
          field_simp
          ring
  · exact abs_harmonicF_sub_le hV ht ht'
  · have h1 : 1 / (k : ℝ) ≤ 1 / log k ^ 6 :=
      one_div_le_one_div_of_le (by positivity) hlog6
    have h2 : 4 * K₀ * V / (k * log 2) = 4 * K₀ * V / log 2 * (1 / k) := by
      field_simp
    have h3 : 0 ≤ 4 * K₀ * V / log 2 := by positivity
    have h4 := mul_le_mul_of_nonneg_left h1 h3
    rw [h2, add_div]
    simp only [mul_one_div] at h4 ⊢
    linarith [show 2 * (128 * |K| / log k ^ 6) = 256 * |K| / log k ^ 6 by ring]

/-- The first renewal: if `A₁(t) = π(t) B(t) + O(t T⁻⁶)`, then there is
`1 / log 3 ≤ α ≤ 1 / log 2` with `B(x) = α L + O(L T⁻⁵)`. -/
theorem first_renewal {K : ℝ}
    (h : ∀ᶠ t : ℝ in Filter.atTop,
      |primeF t - (primesIoc 1 t).card * harmonicF t| ≤ K * t / Real.log (Real.log t) ^ 6) :
    ∃ α K' : ℝ, 1 / Real.log 3 ≤ α ∧ α ≤ 1 / Real.log 2 ∧ ∀ᶠ x : ℝ in Filter.atTop,
      |harmonicF x - α * Real.log x| ≤ K' * Real.log x / Real.log (Real.log x) ^ 5 := by
  obtain ⟨c, EP, hc, hEP, hP⟩ := exists_dyadP_sub
  obtain ⟨C, hC0, hC⟩ := exists_harmonicF_step h
  obtain ⟨V, hV0, hV⟩ := exists_sum_F_div_le
  have hl2 : 0 < log 2 := log_pos one_lt_two
  set B : ℕ → ℝ := fun k => harmonicF (2 ^ k)
  set e : ℕ → ℝ := fun k => B (k + 1) - B k * (1 + dyadH k)
  set C₃ := 2 * C / c
  have hC₃ : 0 ≤ C₃ := by positivity
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 ((eventually_ge_atTop 3).and
    (hC.and ((tendsto_add_atTop_nat 1).eventually hP)))
  -- `|e_k| / P_{k+1} ≤ C₃ / (k log⁶ k)`, which telescopes against `-13 C₃ / log⁵ k`
  have hterm : ∀ k, k₁ ≤ k →
      |e k| / dyadP (k + 1) ≤ C₃ * (13 / log k ^ 5 - 13 / log (k + 1) ^ 5) := by
    intro k hk
    obtain ⟨hk3, hek, -, hPk⟩ := hk₁ k hk
    have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
    have hlk : 0 < log k := by linarith [(log_succ_bounds hk3).1]
    push_cast at hPk
    calc |e k| / dyadP (k + 1) ≤ C / log k ^ 6 / (c * k / 2) :=
          div_le_div₀ (by positivity) hek (by positivity) (by nlinarith)
      _ = C₃ * (1 / (k * log k ^ 6)) := by simp only [C₃]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (one_div_mul_log_pow_six_le hk3) hC₃
  -- `w_N = B_N / P_N` converges to some `β` at rate `13 C₃ / log⁵ N`
  have hw : ∀ N, k₁ ≤ N → ∀ N', N ≤ N' →
      |B N' / dyadP N' - B N / dyadP N| ≤ 13 * C₃ / log N ^ 5 := by
    intro N hN N' hNN'
    rw [div_dyadP_eq (f := e) (fun k _ => by simp only [e]; ring) hNN', add_sub_cancel_left]
    have hsum := sum_Ico_le_sub (a := fun k => |e k| / dyadP (k + 1))
      (g := fun k : ℕ => -(13 * C₃ / log k ^ 5)) hNN' fun k hk _ => by
        have := hterm k (hN.trans hk)
        push_cast
        linarith [show C₃ * (13 / log k ^ 5 - 13 / log (k + 1) ^ 5) =
          13 * C₃ / log k ^ 5 - 13 * C₃ / log (k + 1) ^ 5 by ring]
    have hN'0 : 0 ≤ 13 * C₃ / log N' ^ 5 := by
      have := log_nonneg (Nat.one_le_cast.2 (show 1 ≤ N' by have := (hk₁ N hN).1; omega))
      positivity
    calc |∑ k ∈ Ico N N', e k / dyadP (k + 1)| ≤ ∑ k ∈ Ico N N', |e k| / dyadP (k + 1) := by
          refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun k _ => ?_))
          rw [abs_div, abs_of_pos (dyadP_pos _)]
      _ ≤ 13 * C₃ / log N ^ 5 := by linarith
  have hρ : Tendsto (fun N : ℕ => 13 * C₃ / log N ^ 5) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num)).comp tendsto_log_nat)
  obtain ⟨β, hβ⟩ := exists_abs_sub_le hρ hw
  set α := c * β / log 2
  -- on the dyad `[2^N, 2^{N+1})`, `B(x) = α log x + O(N / log⁵ N)`
  set C₅ := V + 13 * C₃ * (c + EP) + |β| * EP + |α| * log 2
  have hdy : ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, 2 ^ N ≤ x → x < 2 ^ (N + 1) →
      |harmonicF x - α * log x| ≤ C₅ * N ^ 1 / log N ^ 5 := by
    filter_upwards [eventually_ge_atTop k₁, hP, eventually_log_pow_le_nat 6] with N hN hPN hlog6
    intro x hx hx'
    have hN3 := (hk₁ N hN).1
    have hlN := (log_succ_bounds hN3).1
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
    set u := (N : ℝ) / log N ^ 5
    have hl5 : 1 ≤ log N ^ 5 := one_le_pow₀ hlN
    have hu : log N ≤ u := by
      rw [le_div_iff₀ (by positivity), ← pow_succ']
      exact hlog6
    have hu1 : 1 ≤ u := hlN.trans hu
    have hinv : 1 / log N ^ 5 ≤ u := ((div_le_one (by positivity)).2 hl5).trans hu1
    obtain ⟨hlx, hlx', -⟩ := dyad_log_bounds hN3 hx hx'.le
    have h1 := abs_harmonicF_sub_le hV hx hx'.le
    -- `B_N - c β N = P_N (w_N - β) + β (P_N - c N)`
    have h2 : |B N - c * β * N| ≤ (c * N + EP) * (13 * C₃ / log N ^ 5) + |β| * EP := by
      have hPpos := dyadP_pos N
      have e2 : B N - c * β * N = dyadP N * (B N / dyadP N - β) + β * (dyadP N - c * N) := by
        field_simp
        ring
      rw [e2]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_pos hPpos]
        exact mul_le_mul (by linarith [(abs_le.1 hPN.1).2]) (hβ N hN) (abs_nonneg _)
          (by positivity)
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hPN.1 (abs_nonneg _)
    have h3 : |c * β * N - α * log x| ≤ |α| * log 2 := by
      rw [show c * β * N - α * log x = α * (N * log 2 - log x) by simp only [α]; field_simp,
        abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _)
    have e3 : (c * N + EP) * (13 * C₃ / log N ^ 5) =
        13 * C₃ * c * u + 13 * C₃ * EP * (1 / log N ^ 5) := by
      simp only [u]; ring
    have h4 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 13 * C₃ * EP)
    have h5 := le_mul_of_one_le_right hV0 hu1
    have h6 := le_mul_of_one_le_right (by positivity : 0 ≤ |β| * EP) hu1
    have h7 := le_mul_of_one_le_right (by positivity : 0 ≤ |α| * log 2) hu1
    have e4 : C₅ * N ^ 1 / log N ^ 5 = C₅ * u := by simp only [u]; ring
    rw [e4]
    calc |harmonicF x - α * log x|
        ≤ |harmonicF x - B N| + |B N - c * β * N| + |c * β * N - α * log x| := by
          have := abs_add_three (harmonicF x - B N) (B N - c * β * N) (c * β * N - α * log x)
          ring_nf at this ⊢
          linarith
      _ ≤ C₅ * u := by simp only [C₅]; nlinarith
  obtain ⟨K', hK'⟩ := exists_of_dyadic hdy
  obtain ⟨E, hE⟩ := exists_harmonicF_bounds
  have hK'' : ∀ᶠ x : ℝ in atTop,
      |harmonicF x - α * log x| ≤ K' * log x / log (log x) ^ 5 := by
    simpa only [pow_one] using hK'
  -- `B(x) / log x → α` and Pillai's bounds give `1 / log 3 ≤ α ≤ 1 / log 2`
  have hf (a : ℝ) : Tendsto (fun x => a / log x + K' / log (log x) ^ 5) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_log_atTop).add
      (tendsto_const_nhds.div_atTop (tendsto_log_log_pow 5 (by norm_num)))
  refine ⟨α, K', ?_, ?_, hK''⟩
  · have := ge_of_tendsto (hf (E / log 3)) (b := 1 / log 3 - α) ?_
    · linarith
    filter_upwards [hK'', eventually_ge_atTop (exp 1)] with x hx hx1
    have hlx : 1 ≤ log x := (le_log_iff_exp_le (by linarith [exp_pos 1])).2 hx1
    have hb := (hE x (by linarith [add_one_le_exp 1])).1
    have hx' := (abs_le.1 hx).2
    refine le_of_mul_le_mul_right ?_ (by linarith : 0 < log x)
    rw [add_mul, div_mul_cancel₀ _ (by linarith), div_mul_eq_mul_div]
    have : (log x - E) / log 3 = log x / log 3 - E / log 3 := sub_div _ _ _
    rw [sub_mul, one_div_mul_eq_div]
    linarith
  · have := ge_of_tendsto (hf (E / log 2)) (b := α - 1 / log 2) ?_
    · linarith
    filter_upwards [hK'', eventually_ge_atTop (exp 1)] with x hx hx1
    have hlx : 1 ≤ log x := (le_log_iff_exp_le (by linarith [exp_pos 1])).2 hx1
    have hb := (hE x (by linarith [add_one_le_exp 1])).2
    have hx' := (abs_le.1 hx).1
    refine le_of_mul_le_mul_right ?_ (by linarith : 0 < log x)
    rw [add_mul, div_mul_cancel₀ _ (by linarith), div_mul_eq_mul_div]
    have : (log x + E) / log 2 = log x / log 2 + E / log 2 := add_div _ _ _
    rw [sub_mul, one_div_mul_eq_div]
    linarith

/-! ### The second renewal -/

/-- The variation of `C` on a dyad is `O(k)`. -/
private lemma abs_harmonicFSq_sub_le {V : ℝ}
    (hV : ∀ y t : ℝ, 1 ≤ y → y ≤ t → t ≤ 2 * y → ∑ q ∈ primesIoc y t, (F q : ℝ) / q ≤ V)
    {k : ℕ} {t : ℝ} (ht : 2 ^ k ≤ t) (ht' : t ≤ 2 ^ (k + 1)) :
    |harmonicFSq t - harmonicFSq (2 ^ k)| ≤ (k + 1) * V := by
  have hl2 : 0 < log 2 := log_pos one_lt_two
  have hsplit := sum_primesIoc_add (fun q => (F q : ℝ) ^ 2 / q) (one_le_pow₀ one_le_two) ht
  have hpos : 0 ≤ ∑ q ∈ primesIoc (2 ^ k) t, (F q : ℝ) ^ 2 / q := sum_nonneg fun _ _ => by
    positivity
  simp only [harmonicFSq] at hsplit ⊢
  rw [← hsplit, add_sub_cancel_left, abs_of_nonneg hpos]
  calc ∑ q ∈ primesIoc (2 ^ k) t, (F q : ℝ) ^ 2 / q
      ≤ ∑ q ∈ primesIoc (2 ^ k) t, (k + 1) * ((F q : ℝ) / q) := sum_le_sum fun q hq => by
        obtain ⟨hq, -, hqt⟩ := mem_primesIoc.1 hq
        -- `F q ≤ log q / log 2 ≤ k + 1`
        have hlq : log q ≤ (k + 1) * log 2 := by
          rw [← Nat.cast_succ, ← log_pow]
          exact log_le_log (by exact_mod_cast hq.pos) (hqt.trans ht')
        have hF : (F q : ℝ) ≤ k + 1 :=
          (F_le_log_div_log_two hq.ne_zero).trans ((div_le_iff₀ hl2).2 hlq)
        rw [sq, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hF (by positivity)
    _ = (k + 1) * ∑ q ∈ primesIoc (2 ^ k) t, (F q : ℝ) / q := (mul_sum _ _ _).symm
    _ ≤ (k + 1) * V :=
        mul_le_mul_of_nonneg_left (hV _ t (one_le_pow₀ one_le_two) ht
          (by rw [← pow_succ']; exact ht')) (by positivity)

/-- The second renewal step: `C_{k+1} = C_k (1 + h_k) + D_k h_k + O(k / log⁵ k)`. -/
private lemma exists_harmonicFSq_step {α K : ℝ}
    (h : ∀ᶠ t : ℝ in atTop,
      |primeFSq t - (primesIoc 1 t).card * (harmonicFSq t + harmonicFPair t)| ≤
        K * t * log t / log (log t) ^ 6)
    (hD : ∀ᶠ x : ℝ in atTop,
      |harmonicFPair x - α ^ 2 / 2 * log x ^ 2| ≤ K * log x ^ 2 / log (log x) ^ 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
      |harmonicFSq (2 ^ (k + 1)) - harmonicFSq (2 ^ k) * (1 + dyadH k) -
        harmonicFPair (2 ^ k) * dyadH k| ≤ C * k / log k ^ 5 := by
  obtain ⟨V, hV0, hV⟩ := exists_sum_F_div_le
  obtain ⟨K₀, hK₀, hπ⟩ := card_primesIoc_le
  have hl2 : 0 < log 2 := log_pos one_lt_two
  set a := α ^ 2 / 2
  have ha : 0 ≤ a := by positivity
  set W := 2 * V + 256 * |K| * log 2 ^ 2 + 3 * a * log 2 ^ 2
  refine ⟨512 * |K| * log 2 + 4 * K₀ * W / log 2, by positivity, ?_⟩
  filter_upwards [eventually_dyad h, eventually_dyad hD, eventually_ge_atTop 3,
    eventually_log_pow_le_nat 6] with k hk hDk hk3 hlog6
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  have hlogk := (log_succ_bounds hk3).1
  have hL0 : 0 < log k := by linarith
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
  have h2k' : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := pow_le_pow_right₀ one_le_two k.le_succ
  set u := (k : ℝ) / log k ^ 5
  have hu : log k ≤ u := by
    rw [le_div_iff₀ (by positivity), ← pow_succ']
    exact hlog6
  have hu1 : 1 ≤ u := hlogk.trans hu
  -- `e'_k = ∑_{2^k < q ≤ 2^{k+1}} (F q² - (C_k + D_k)) / q`
  have e : harmonicFSq (2 ^ (k + 1)) - harmonicFSq (2 ^ k) * (1 + dyadH k) -
        harmonicFPair (2 ^ k) * dyadH k =
      ∑ q ∈ primesIoc (2 ^ k) (2 ^ (k + 1)),
        ((F q : ℝ) ^ 2 - (harmonicFSq (2 ^ k) + harmonicFPair (2 ^ k))) / q := by
    have hsplit : harmonicFSq (2 ^ (k + 1)) = harmonicFSq (2 ^ k) +
        ∑ q ∈ primesIoc (2 ^ k) (2 ^ (k + 1)), (F q : ℝ) ^ 2 / q :=
      (sum_primesIoc_add _ h2k h2k').symm
    rw [hsplit, dyadH, mul_add, mul_one, mul_sum, mul_sum, add_sub_add_left_eq_sub,
      ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun q _ => by ring
  -- `D(s) = a log² s + O(k u)` on the dyad
  have hDb : ∀ s : ℝ, 2 ^ k ≤ s → s ≤ 2 ^ (k + 1) →
      |harmonicFPair s - a * log s ^ 2| ≤ 128 * |K| * log 2 ^ 2 * k * u := by
    intro s hs hs'
    obtain ⟨hls, hls', hT⟩ := dyad_log_bounds hk3 hs hs'
    have hk1 : ((k : ℝ) + 1) ^ 2 ≤ 4 * k ^ 2 := by nlinarith
    calc _ ≤ K * log s ^ 2 / log (log s) ^ 5 := hDk s hs
      _ ≤ |K| * ((k + 1) * log 2) ^ 2 / (log k / 2) ^ 5 :=
          div_le_div₀ (by positivity) (mul_le_mul (le_abs_self K)
            (pow_le_pow_left₀ (le_trans (by positivity) hls) hls' 2) (sq_nonneg _)
            (abs_nonneg K))
            (by positivity) (pow_le_pow_left₀ (by positivity) hT 5)
      _ = 32 * |K| * log 2 ^ 2 * ((k + 1) ^ 2 / log k ^ 5) := by
          rw [div_pow]; field_simp; ring
      _ ≤ 32 * |K| * log 2 ^ 2 * (4 * k ^ 2 / log k ^ 5) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hk1 (by positivity))
            (by positivity)
      _ = 128 * |K| * log 2 ^ 2 * k * u := by simp only [u]; ring
  have hkL : ((k : ℝ) + 1) / log k ^ 6 ≤ 2 * u :=
    calc ((k : ℝ) + 1) / log k ^ 6 ≤ 2 * k / log k ^ 6 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ 2 * k / log k ^ 5 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_right₀ hlogk (by norm_num))
      _ = 2 * u := by simp only [u]; ring
  rw [e]
  refine (abs_sum_dyad_sub_le hK₀ hπ (g := fun q => (F q : ℝ) ^ 2)
    (Φ := fun t => harmonicFSq t + harmonicFPair t) (by omega)
    (ε := 256 * |K| * log 2 * u) (V := W * k * u) (fun t ht ht' => ?_)
    (fun t ht ht' => ?_)).trans ?_
  · obtain ⟨hlt, hlt', hT⟩ := dyad_log_bounds hk3 ht ht'
    calc _ ≤ K * t * log t / log (log t) ^ 6 := hk t ht
      _ ≤ |K| * 2 ^ (k + 1) * ((k + 1) * log 2) / (log k / 2) ^ 6 :=
          div_le_div₀ (by positivity) (mul_le_mul (mul_le_mul (le_abs_self K) ht'
            (by linarith) (abs_nonneg K)) hlt' (le_trans (by positivity) hlt) (by positivity))
            (by positivity) (pow_le_pow_left₀ (by positivity) hT 6)
      _ = 2 ^ k * (128 * |K| * log 2) * (((k : ℝ) + 1) / log k ^ 6) := by
          rw [div_pow, pow_succ]; field_simp; ring
      _ ≤ 2 ^ k * (128 * |K| * log 2) * (2 * u) :=
          mul_le_mul_of_nonneg_left hkL (by positivity)
      _ = 2 ^ k * (256 * |K| * log 2 * u) := by ring
  · obtain ⟨hlt, hlt', -⟩ := dyad_log_bounds hk3 ht ht'
    have hC := abs_harmonicFSq_sub_le hV ht ht'
    have hD1 := hDb t ht ht'
    have hD2 := hDb (2 ^ k) le_rfl h2k'
    rw [log_pow] at hD2
    -- `a (log² t - (k log 2)²) ≤ a (2 k + 1) log² 2 ≤ 3 a log² 2 k`
    have hlt0 : 0 ≤ log t := le_trans (by positivity) hlt
    have hsq : a * log t ^ 2 - a * (k * log 2) ^ 2 ≤ 3 * a * log 2 ^ 2 * k := by
      have h1 := pow_le_pow_left₀ hlt0 hlt' 2
      have h2 := mul_le_mul_of_nonneg_right (by linarith : 2 * (k : ℝ) + 1 ≤ 3 * k)
        (sq_nonneg (log 2))
      have : log t ^ 2 - (k * log 2) ^ 2 ≤ 3 * log 2 ^ 2 * k := by nlinarith
      calc a * log t ^ 2 - a * (k * log 2) ^ 2 = a * (log t ^ 2 - (k * log 2) ^ 2) := by ring
        _ ≤ a * (3 * log 2 ^ 2 * k) := mul_le_mul_of_nonneg_left this ha
        _ = 3 * a * log 2 ^ 2 * k := by ring
    have hsq0 : 0 ≤ a * log t ^ 2 - a * (k * log 2) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hlt 2
      rw [← mul_sub]
      exact mul_nonneg ha (by linarith)
    have hCu : ((k : ℝ) + 1) * V ≤ 2 * V * k * u := by
      have h1 := mul_le_mul_of_nonneg_right (by linarith : (k : ℝ) + 1 ≤ 2 * k) hV0
      have h2 := le_mul_of_one_le_right (by positivity : 0 ≤ 2 * V * k) hu1
      linarith
    have h3u : 3 * a * log 2 ^ 2 * k ≤ 3 * a * log 2 ^ 2 * k * u :=
      le_mul_of_one_le_right (by positivity) hu1
    show |harmonicFSq t + harmonicFPair t - (harmonicFSq (2 ^ k) + harmonicFPair (2 ^ k))| ≤
      W * k * u
    rw [show harmonicFSq t + harmonicFPair t - (harmonicFSq (2 ^ k) + harmonicFPair (2 ^ k)) =
      (harmonicFSq t - harmonicFSq (2 ^ k)) + ((harmonicFPair t - a * log t ^ 2) -
        (harmonicFPair (2 ^ k) - a * (k * log 2) ^ 2) +
          (a * log t ^ 2 - a * (k * log 2) ^ 2)) by ring]
    have t1 := abs_add_le (harmonicFSq t - harmonicFSq (2 ^ k))
      ((harmonicFPair t - a * log t ^ 2) - (harmonicFPair (2 ^ k) - a * (k * log 2) ^ 2) +
        (a * log t ^ 2 - a * (k * log 2) ^ 2))
    have t2 := abs_add_le ((harmonicFPair t - a * log t ^ 2) -
      (harmonicFPair (2 ^ k) - a * (k * log 2) ^ 2)) (a * log t ^ 2 - a * (k * log 2) ^ 2)
    have t3 := abs_sub (harmonicFPair t - a * log t ^ 2)
      (harmonicFPair (2 ^ k) - a * (k * log 2) ^ 2)
    rw [abs_of_nonneg hsq0] at t2
    simp only [W]
    linarith
  · have e2 : 4 * K₀ * (W * k * u) / (k * log 2) = 4 * K₀ * W / log 2 * u := by
      field_simp
    rw [e2, show (512 * |K| * log 2 + 4 * K₀ * W / log 2) * k / log k ^ 5 =
      (512 * |K| * log 2 + 4 * K₀ * W / log 2) * u by simp only [u]; ring]
    linarith

/-- The cross term on dyads: `D_k = a k² + O(k² / log⁵ k)` with `a = α² log² 2 / 2`. -/
private lemma eventually_abs_harmonicFPair_sub_le {α K : ℝ}
    (hD : ∀ᶠ x : ℝ in atTop,
      |harmonicFPair x - α ^ 2 / 2 * log x ^ 2| ≤ K * log x ^ 2 / log (log x) ^ 5) :
    ∀ᶠ k : ℕ in atTop, |harmonicFPair (2 ^ k) - α ^ 2 / 2 * log 2 ^ 2 * k ^ 2| ≤
      32 * |K| * log 2 ^ 2 * (k ^ 2 / log k ^ 5) := by
  filter_upwards [eventually_dyad hD, eventually_ge_atTop 3] with k hk hk3
  obtain ⟨-, -, hT⟩ := dyad_log_bounds hk3 le_rfl (pow_le_pow_right₀ one_le_two k.le_succ)
  have hL0 : 0 < log k := by linarith [(log_succ_bounds hk3).1]
  have hl2k : log ((2 : ℝ) ^ k) = k * log 2 := log_pow _ _
  rw [show α ^ 2 / 2 * log 2 ^ 2 * k ^ 2 = α ^ 2 / 2 * log ((2 : ℝ) ^ k) ^ 2 by
    rw [hl2k]; ring]
  calc _ ≤ K * log ((2 : ℝ) ^ k) ^ 2 / log (log ((2 : ℝ) ^ k)) ^ 5 := hk _ le_rfl
    _ ≤ |K| * log ((2 : ℝ) ^ k) ^ 2 / (log k / 2) ^ 5 :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (le_abs_self K)
          (sq_nonneg _)) (by positivity) (pow_le_pow_left₀ (by positivity) hT 5)
    _ = 32 * |K| * log 2 ^ 2 * (k ^ 2 / log k ^ 5) := by
        rw [hl2k, div_pow]; field_simp; norm_num

/-- One term of the second renewal sum:
`(D h_k + e) / P_{k+1} = (a / c) k h_k + O(log⁻⁵ k + h_k)` when `D = a k² + O(k² / log⁵ k)`
and `e = O(k / log⁵ k)`. -/
private lemma abs_renewal_term_le {a c EP ch C₂ K₃ D e : ℝ} {k : ℕ} (ha : 0 ≤ a) (hc : 0 < c)
    (hEP : 0 ≤ EP) (hch0 : 0 ≤ ch) (hC₂0 : 0 ≤ C₂) (hK₃ : 0 ≤ K₃) (hk : 1 ≤ k)
    (hL0 : 0 < log k) (hhk : dyadH k ≤ ch / k) (hek : |e| ≤ C₂ * k / log k ^ 5)
    (hDkk : |D - a * k ^ 2| ≤ K₃ * (k ^ 2 / log k ^ 5))
    (hPk : |dyadP (k + 1) - c * (k + 1)| ≤ EP) (hPk' : c * (k + 1) / 2 ≤ dyadP (k + 1)) :
    |(D * dyadH k + e) / dyadP (k + 1) - a / c * (k * dyadH k)| ≤
      (2 * ch * K₃ / c + 2 * C₂ / c) / log k ^ 5 + 2 * a * (c + EP) / c ^ 2 * dyadH k := by
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  have hP0 := dyadP_pos (k + 1)
  have hPk'' : c * k / 2 ≤ dyadP (k + 1) := by nlinarith
  have hh0 := dyadH_nonneg k
  have e1 : (D * dyadH k + e) / dyadP (k + 1) - a / c * (k * dyadH k) =
      dyadH k * ((D - a * k ^ 2) / dyadP (k + 1)) +
        a / c * dyadH k * (k * (c * k - dyadP (k + 1)) / dyadP (k + 1)) +
          e / dyadP (k + 1) := by
    field_simp
    ring
  have b1 : |dyadH k * ((D - a * k ^ 2) / dyadP (k + 1))| ≤ 2 * ch * K₃ / c / log k ^ 5 := by
    rw [abs_mul, abs_div, abs_of_nonneg hh0, abs_of_pos hP0]
    calc dyadH k * (|D - a * k ^ 2| / dyadP (k + 1))
        ≤ ch / k * (K₃ * (k ^ 2 / log k ^ 5) / (c * k / 2)) :=
          mul_le_mul hhk (div_le_div₀ (by positivity) hDkk (by positivity) hPk'')
            (by positivity) (by positivity)
      _ = 2 * ch * K₃ / c / log k ^ 5 := by field_simp
  have b2 : |a / c * dyadH k * (k * (c * k - dyadP (k + 1)) / dyadP (k + 1))| ≤
      2 * a * (c + EP) / c ^ 2 * dyadH k := by
    have hck : |c * k - dyadP (k + 1)| ≤ c + EP := by
      have := abs_le.1 hPk
      exact abs_le.2 ⟨by linarith, by linarith⟩
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a / c), abs_of_nonneg hh0,
      abs_div, abs_mul, abs_of_pos hP0, abs_of_pos hk0]
    calc a / c * dyadH k * (k * |c * k - dyadP (k + 1)| / dyadP (k + 1))
        ≤ a / c * dyadH k * (k * (c + EP) / (c * k / 2)) :=
          mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity)
            (mul_le_mul_of_nonneg_left hck hk0.le) (by positivity) hPk'') (by positivity)
      _ = 2 * a * (c + EP) / c ^ 2 * dyadH k := by field_simp
  have b3 : |e / dyadP (k + 1)| ≤ 2 * C₂ / c / log k ^ 5 := by
    rw [abs_div, abs_of_pos hP0]
    calc |e| / dyadP (k + 1) ≤ C₂ * k / log k ^ 5 / (c * k / 2) :=
          div_le_div₀ (by positivity) hek (by positivity) hPk''
      _ = 2 * C₂ / c / log k ^ 5 := by field_simp
  rw [e1, add_div]
  have t1 := abs_add_le (dyadH k * ((D - a * k ^ 2) / dyadP (k + 1)) +
    a / c * dyadH k * (k * (c * k - dyadP (k + 1)) / dyadP (k + 1))) (e / dyadP (k + 1))
  have t2 := abs_add_le (dyadH k * ((D - a * k ^ 2) / dyadP (k + 1)))
    (a / c * dyadH k * (k * (c * k - dyadP (k + 1)) / dyadP (k + 1)))
  linarith

/-- The second renewal on dyads: `C_N = a N² + O(N² / log⁵ N)` with `a = α² log² 2 / 2`. -/
private lemma exists_harmonicFSq_dyad {α K : ℝ}
    (h : ∀ᶠ t : ℝ in atTop,
      |primeFSq t - (primesIoc 1 t).card * (harmonicFSq t + harmonicFPair t)| ≤
        K * t * log t / log (log t) ^ 6)
    (hD : ∀ᶠ x : ℝ in atTop,
      |harmonicFPair x - α ^ 2 / 2 * log x ^ 2| ≤ K * log x ^ 2 / log (log x) ^ 5) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      |harmonicFSq (2 ^ N) - α ^ 2 / 2 * log 2 ^ 2 * N ^ 2| ≤ C * (N * (N / log N ^ 5)) := by
  obtain ⟨c, EP, hc, hEP, hP⟩ := exists_dyadP_sub
  obtain ⟨ch, hch0, hch⟩ := exists_dyadH_le
  obtain ⟨Es, hEs0, hEs⟩ := exists_sum_dyadH_le
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_harmonicFSq_step h hD
  have hl2 : 0 < log 2 := log_pos one_lt_two
  set a := α ^ 2 / 2 * log 2 ^ 2
  have ha : 0 ≤ a := by positivity
  set X : ℕ → ℝ := fun k => harmonicFSq (2 ^ k)
  set Dk : ℕ → ℝ := fun k => harmonicFPair (2 ^ k)
  set e : ℕ → ℝ := fun k => X (k + 1) - X k * (1 + dyadH k) - Dk k * dyadH k
  set K₃ := 32 * |K| * log 2 ^ 2
  have hDk : ∀ᶠ k : ℕ in atTop, |Dk k - a * k ^ 2| ≤ K₃ * (k ^ 2 / log k ^ 5) :=
    eventually_abs_harmonicFPair_sub_le hD
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 ((eventually_ge_atTop 3).and
    ((tendsto_log_nat.eventually_ge_atTop 160).and (hC₂.and (hDk.and
      ((tendsto_add_atTop_nat 1).eventually hP)))))
  set C₅ := 2 * ch * K₃ / c + 2 * C₂ / c
  set C₆ := 2 * a * (c + EP) / c ^ 2
  -- `(D_k h_k + e_k) / P_{k+1} = (a / c) k h_k + O(log⁻⁵ k + h_k)`
  have hr : ∀ k, k₁ ≤ k →
      |(Dk k * dyadH k + e k) / dyadP (k + 1) - a / c * (k * dyadH k)| ≤
        C₅ / log k ^ 5 + C₆ * dyadH k := by
    intro k hk
    obtain ⟨hk3, hlk, hek, hDkk, hPk, hPk'⟩ := hk₁ k hk
    push_cast at hPk hPk'
    exact abs_renewal_term_le ha hc hEP hch0 hC₂0 (by positivity) (by omega) (by linarith)
      (hch k (by omega)) hek hDkk hPk hPk'
  set S₀ := ∑ k ∈ range k₁, k * dyadH k
  set R₀ := |X k₁ / dyadP k₁ - a / c * S₀|
  set C₇ := R₀ + a / c * (1 + Es) + 64 * C₅ + C₆ * (1 + Es)
  refine ⟨(c + EP) * C₇ + a / c * EP, ?_⟩
  filter_upwards [eventually_ge_atTop k₁, hP, eventually_log_pow_le_nat 6] with N hN hPN hlog6
  have hN3 := (hk₁ N hN).1
  have hlN := (log_succ_bounds hN3).1
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 (by omega)
  set u := (N : ℝ) / log N ^ 5
  have hu : log N ≤ u := by
    rw [le_div_iff₀ (by positivity), ← pow_succ']
    exact hlog6
  have hu1 : 1 ≤ u := hlN.trans hu
  -- `∑_{k₁ ≤ k < N} 1 / log⁵ k ≤ 64 N / log⁵ N`
  have hsum5 : ∑ k ∈ Ico k₁ N, 1 / log k ^ 5 ≤ 64 * u := by
    have := sum_Ico_le_sub (a := fun k => 1 / log k ^ 5) (g := fun k : ℕ => 64 * k / log k ^ 5)
      hN fun k hk _ => by
        obtain ⟨hk3, hlk, -⟩ := hk₁ k hk
        push_cast
        exact one_div_log_pow_five_le hk3 hlk
    have h0 : 0 ≤ 64 * (k₁ : ℝ) / log k₁ ^ 5 := by
      have := (log_succ_bounds (hk₁ k₁ le_rfl).1).1
      positivity
    have e2 : 64 * (N : ℝ) / log N ^ 5 = 64 * u := by simp only [u]; ring
    linarith
  have hsumh : ∑ k ∈ Ico k₁ N, dyadH k ≤ log N + Es := by
    have := sum_range_add_sum_Ico dyadH hN
    have := sum_nonneg fun k (_ : k ∈ range k₁) => dyadH_nonneg k
    linarith [(hEs N (by omega)).1]
  -- `X_N / P_N = (a / c) N + O(u)`
  have hmain : |X N / dyadP N - a / c * N| ≤ C₇ * u := by
    rw [div_dyadP_eq (f := fun k => Dk k * dyadH k + e k) (fun k _ => by simp only [e]; ring) hN]
    have e2 : X k₁ / dyadP k₁ + ∑ k ∈ Ico k₁ N, (Dk k * dyadH k + e k) / dyadP (k + 1) -
        a / c * N = (X k₁ / dyadP k₁ - a / c * S₀) +
          a / c * (∑ k ∈ range N, k * dyadH k - N) +
            ∑ k ∈ Ico k₁ N, ((Dk k * dyadH k + e k) / dyadP (k + 1) -
              a / c * (k * dyadH k)) := by
      have hS : ∑ k ∈ Ico k₁ N, (k : ℝ) * dyadH k = ∑ k ∈ range N, k * dyadH k - S₀ :=
        sum_Ico_eq_sub _ hN
      rw [sum_sub_distrib, ← mul_sum, hS]
      ring
    rw [e2]
    have hR := abs_sum_le_sum_abs (fun k => (Dk k * dyadH k + e k) / dyadP (k + 1) -
      a / c * (k * dyadH k)) (Ico k₁ N)
    have hR' := sum_le_sum fun k (hk : k ∈ Ico k₁ N) => hr k (mem_Ico.1 hk).1
    have e5 : ∑ k ∈ Ico k₁ N, C₅ / log k ^ 5 = C₅ * ∑ k ∈ Ico k₁ N, 1 / log k ^ 5 := by
      rw [mul_sum]
      exact sum_congr rfl fun k _ => by ring
    rw [sum_add_distrib, e5, ← mul_sum] at hR'
    have h5 := mul_le_mul_of_nonneg_left hsum5 (by positivity : 0 ≤ C₅)
    have h6 := mul_le_mul_of_nonneg_left hsumh (by positivity : 0 ≤ C₆)
    have hK := hEs N (by omega)
    have h7 : |a / c * (∑ k ∈ range N, k * dyadH k - N)| ≤ a / c * (log N + Es) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hK.2 (by positivity)
    have t1 := abs_add_le (X k₁ / dyadP k₁ - a / c * S₀ +
      a / c * (∑ k ∈ range N, k * dyadH k - N))
      (∑ k ∈ Ico k₁ N, ((Dk k * dyadH k + e k) / dyadP (k + 1) - a / c * (k * dyadH k)))
    have t2 := abs_add_le (X k₁ / dyadP k₁ - a / c * S₀)
      (a / c * (∑ k ∈ range N, k * dyadH k - N))
    have h8 : a / c * (log N + Es) ≤ a / c * (1 + Es) * u := by
      have := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ a / c)
      have := mul_le_mul_of_nonneg_left hu1 (by positivity : 0 ≤ a / c * Es)
      linarith
    have h9 : C₆ * (log N + Es) ≤ C₆ * (1 + Es) * u := by
      have := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ C₆)
      have := mul_le_mul_of_nonneg_left hu1 (by positivity : 0 ≤ C₆ * Es)
      linarith
    have h10 : R₀ ≤ R₀ * u := le_mul_of_one_le_right (abs_nonneg _) hu1
    simp only [C₇]
    linarith
  -- `X_N - a N² = P_N (X_N / P_N - (a / c) N) + (a / c) N (P_N - c N)`
  have hPpos := dyadP_pos N
  have e3 : X N - a * N ^ 2 = dyadP N * (X N / dyadP N - a / c * N) +
      a / c * N * (dyadP N - c * N) := by
    field_simp
    ring
  show |X N - a * N ^ 2| ≤ _
  rw [e3]
  have t1 := abs_add_le (dyadP N * (X N / dyadP N - a / c * N)) (a / c * N * (dyadP N - c * N))
  have hC₇ : 0 ≤ C₇ * u := (abs_nonneg _).trans hmain
  have b1 : |dyadP N * (X N / dyadP N - a / c * N)| ≤ (c + EP) * C₇ * (N * u) := by
    rw [abs_mul, abs_of_pos hPpos]
    have hPN' : dyadP N ≤ (c + EP) * N := by
      have := le_mul_of_one_le_right hEP hN1
      linarith [(abs_le.1 hPN.1).2]
    calc dyadP N * |X N / dyadP N - a / c * N| ≤ ((c + EP) * N) * (C₇ * u) :=
          mul_le_mul hPN' hmain (abs_nonneg _) (by positivity)
      _ = (c + EP) * C₇ * (N * u) := by ring
  have b2 : |a / c * N * (dyadP N - c * N)| ≤ a / c * EP * (N * u) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc a / c * N * |dyadP N - c * N| ≤ a / c * N * EP :=
          mul_le_mul_of_nonneg_left hPN.1 (by positivity)
      _ ≤ a / c * N * EP * u := le_mul_of_one_le_right (by positivity) hu1
      _ = a / c * EP * (N * u) := by ring
  linarith

/-- The second renewal: if `A₂(t) = π(t) (C(t) + D(t)) + O(t L T⁻⁶)` and
`D(x) = α² L² / 2 + O(L² T⁻⁵)`, then `C(x) = α² L² / 2 + O(L² T⁻⁵)`. -/
theorem second_renewal {α K : ℝ}
    (h : ∀ᶠ t : ℝ in Filter.atTop,
      |primeFSq t - (primesIoc 1 t).card * (harmonicFSq t + harmonicFPair t)| ≤
        K * t * Real.log t / Real.log (Real.log t) ^ 6)
    (hD : ∀ᶠ x : ℝ in Filter.atTop,
      |harmonicFPair x - α ^ 2 / 2 * Real.log x ^ 2| ≤
        K * Real.log x ^ 2 / Real.log (Real.log x) ^ 5) :
    ∃ K' : ℝ, ∀ᶠ x : ℝ in Filter.atTop,
      |harmonicFSq x - α ^ 2 / 2 * Real.log x ^ 2| ≤
        K' * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 := by
  obtain ⟨C, hC⟩ := exists_harmonicFSq_dyad h hD
  obtain ⟨V, hV0, hV⟩ := exists_sum_F_div_le
  have hl2 : 0 < log 2 := log_pos one_lt_two
  set a := α ^ 2 / 2 * log 2 ^ 2
  have ha : 0 ≤ a := by positivity
  refine exists_of_dyadic (C := C + 2 * V + 3 * a) ?_
  filter_upwards [hC, eventually_ge_atTop 3, eventually_log_pow_le_nat 6] with N hN hN3 hlog6
  intro x hx hx'
  have hlN := (log_succ_bounds hN3).1
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hN3' : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  set u := (N : ℝ) / log N ^ 5
  have hu : log N ≤ u := by
    rw [le_div_iff₀ (by positivity), ← pow_succ']
    exact hlog6
  have hu1 : 1 ≤ u := hlN.trans hu
  obtain ⟨hlx, hlx', -⟩ := dyad_log_bounds hN3 hx hx'.le
  have h1 := abs_harmonicFSq_sub_le hV hx hx'.le
  -- `α² / 2 (log² x - (N log 2)²) ≤ a (2 N + 1) ≤ 3 a N`
  have h3 : |a * N ^ 2 - α ^ 2 / 2 * log x ^ 2| ≤ 3 * a * N := by
    have hlx0 : 0 ≤ N * log 2 := by positivity
    have hsq := pow_le_pow_left₀ hlx0 hlx 2
    have hsq' := pow_le_pow_left₀ (hlx0.trans hlx) hlx' 2
    have e1 : a * N ^ 2 - α ^ 2 / 2 * log x ^ 2 =
        -(α ^ 2 / 2 * (log x ^ 2 - (N * log 2) ^ 2)) := by simp only [a]; ring
    rw [e1, abs_neg, abs_of_nonneg (by have := sq_nonneg α; nlinarith)]
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 2 * (N : ℝ) + 1 ≤ 3 * N)
      (sq_nonneg (log 2))
    calc α ^ 2 / 2 * (log x ^ 2 - (N * log 2) ^ 2) ≤
          α ^ 2 / 2 * (((N + 1) * log 2) ^ 2 - (N * log 2) ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = α ^ 2 / 2 * ((2 * N + 1) * log 2 ^ 2) := by ring
      _ ≤ α ^ 2 / 2 * (3 * N * log 2 ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 3 * a * N := by simp only [a]; ring
  have t1 := abs_add_three (harmonicFSq x - harmonicFSq (2 ^ N))
    (harmonicFSq (2 ^ N) - a * N ^ 2) (a * N ^ 2 - α ^ 2 / 2 * log x ^ 2)
  have h4 : ((N : ℝ) + 1) * V ≤ 2 * V * (N * u) := by
    have := mul_le_mul_of_nonneg_right (by linarith : (N : ℝ) + 1 ≤ 2 * N) hV0
    have := le_mul_of_one_le_right (by positivity : 0 ≤ 2 * V * N) hu1
    nlinarith
  have h5 : 3 * a * N ≤ 3 * a * (N * u) := by
    have := le_mul_of_one_le_right (by positivity : 0 ≤ 3 * a * N) hu1
    linarith
  rw [show (C + 2 * V + 3 * a) * N ^ 2 / log N ^ 5 =
    C * (N * u) + 2 * V * (N * u) + 3 * a * (N * u) by simp only [u]; ring]
  have e4 : harmonicFSq x - α ^ 2 / 2 * log x ^ 2 = harmonicFSq x - harmonicFSq (2 ^ N) +
      (harmonicFSq (2 ^ N) - a * N ^ 2) + (a * N ^ 2 - α ^ 2 / 2 * log x ^ 2) := by ring
  rw [e4]
  linarith

end Erdos408
