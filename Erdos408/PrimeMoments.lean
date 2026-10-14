module

public import Erdos408.SpareSlot

/-!
# The dyadic prime moments

For primes `x < p ≤ 2x`, `F p = F (p - 1)`. Put `n = p - 1 < 2x` and
`ℓ = log 2x`. Since `log n = ∑_{q ∣ n} v_q(n) log q` and `F q ≤ 2 log q`, two
deterministic inequalities hold, with `q` over the primes of `region₁` and
`(q, r)` over the pairs of `region₂` dividing `n`:

* `0 ≤ F n - ∑ F q ≤ 2 (ℓ - ∑ log q)`;
* `0 ≤ F(n)² - ∑ F(q)² - ∑ F q F r ≤ 4 (2 ℓ (ℓ - ∑ log q) + ℓ² - ∑ (log q)² - ∑ log q log r)`.

The spare-slot statistics with coefficients `log q`, `(log q)²` and
`log q log r`, together with Mertens' first theorem on `region₁` and the model
lower bounds of `Erdos408.Grid`, show that the right sides sum over `p` to
`O(Π_x L T⁻⁶)` and `O(Π_x L² T⁻⁶)`. This is the positivity argument of
*The normal order of the number of iterations of Euler's function* (Plasma AI,
2026), §4, which needs no sieve bound for the omitted primes, prime powers and
products. The spare-slot statistics with coefficients `F q`, `F(q)²` and
`F q F r` then give the dyadic moments, and Mertens' first theorem bounds the
harmonic tails outside the regions.
-/

@[expose] public section

namespace Erdos408

open Filter Real

/-- `F q ≤ 2 log q`, since `F q ≤ log q / log 2` and `log 2 > 1 / 2`. -/
private lemma F_le_two_mul_log {q : ℕ} (hq : q ≠ 0) : (F q : ℝ) ≤ 2 * log q := by
  have h2 : (1 / 2 : ℝ) < log 2 := lt_trans (by norm_num) log_two_gt_d9
  have hlog := log_natCast_nonneg q
  calc (F q : ℝ) ≤ log q / log 2 := F_le_log_div_log_two hq
    _ ≤ 2 * log q := by rw [div_le_iff₀ (by linarith)]; nlinarith

/-- If `A` consists of prime divisors of `n ≠ 0` and `log n ≤ ℓ`, then
`0 ≤ F n - ∑_A F q ≤ 2 (ℓ - ∑_A log q)`. -/
private lemma F_sub_sum_le {n : ℕ} (hn : n ≠ 0) {A : Finset ℕ}
    (hA : ∀ q ∈ A, q.Prime ∧ q ∣ n) {ℓ : ℝ} (hℓ : log n ≤ ℓ) :
    0 ≤ (F n : ℝ) - ∑ q ∈ A, (F q : ℝ) ∧
      (F n : ℝ) - ∑ q ∈ A, (F q : ℝ) ≤ 2 * (ℓ - ∑ q ∈ A, log (q : ℝ)) := by
  have hsub : A ⊆ n.primeFactors := fun q hq =>
    Nat.mem_primeFactors.2 ⟨(hA q hq).1, (hA q hq).2, hn⟩
  -- the multiplicity of `q` in `n`, less one for `q ∈ A`
  set u : ℕ → ℝ := fun q => (n.factorization q : ℝ) - if q ∈ A then 1 else 0 with hu
  have hu0 : ∀ q ∈ n.primeFactors, 0 ≤ u q := by
    intro q hq
    by_cases hqA : q ∈ A
    · have : (1 : ℝ) ≤ n.factorization q := by
        exact_mod_cast (hA q hqA).1.factorization_pos_of_dvd hn (hA q hqA).2
      simp only [u, hqA, ite_true]
      linarith
    · simp [u, hqA]
  have hsum : ∀ g : ℕ → ℝ, ∑ q ∈ n.primeFactors, n.factorization q * g q - ∑ q ∈ A, g q =
      ∑ q ∈ n.primeFactors, u q * g q := by
    intro g
    rw [← Finset.inter_eq_right.2 hsub, ← Finset.sum_ite_mem, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [u]
    split_ifs <;> ring
  have hF : (F n : ℝ) = ∑ q ∈ n.primeFactors, n.factorization q * (F q : ℝ) := by
    rw [F_eq_sum_factorization hn]
    push_cast
    rfl
  have hlog : log (n : ℝ) = ∑ q ∈ n.primeFactors, n.factorization q * log (q : ℝ) := by
    rw [log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  have hl : log (n : ℝ) - ∑ q ∈ A, log (q : ℝ) = ∑ q ∈ n.primeFactors, u q * log (q : ℝ) := by
    rw [hlog, hsum]
  rw [hF, hsum fun q => (F q : ℝ)]
  refine ⟨Finset.sum_nonneg fun q hq => mul_nonneg (hu0 q hq) (Nat.cast_nonneg _), ?_⟩
  have h1 : ∑ q ∈ n.primeFactors, u q * (F q : ℝ) ≤
      ∑ q ∈ n.primeFactors, u q * (2 * log (q : ℝ)) :=
    Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left
      (F_le_two_mul_log (Nat.prime_of_mem_primeFactors hq).ne_zero) (hu0 q hq)
  have h2 : ∑ q ∈ n.primeFactors, u q * (2 * log (q : ℝ)) =
      2 * (log n - ∑ q ∈ A, log (q : ℝ)) := by
    rw [hl, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  linarith

/-- `(∑_A g)² = ∑_A g² + ∑_{q ≠ r ∈ A} g q g r`. -/
private lemma sq_sum_eq (A : Finset ℕ) (g : ℕ → ℝ) :
    (∑ q ∈ A, g q) ^ 2 = ∑ q ∈ A, g q ^ 2 + ∑ Q ∈ A.offDiag, g Q.1 * g Q.2 := by
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.diag, Finset.sum_map]
  simp [sq]

/-- If `A` consists of prime divisors of `n ≠ 0`, `R` of pairs of distinct elements of `A`,
and `log n ≤ ℓ`, then `F(n)² - ∑_A F(q)² - ∑_R F q F r` lies between `0` and
`4 (2 ℓ (ℓ - ∑_A log q) + ℓ² - ∑_A (log q)² - ∑_R log q log r)`. -/
private lemma sq_sub_sum_le {n : ℕ} (hn : n ≠ 0) {A : Finset ℕ}
    (hA : ∀ q ∈ A, q.Prime ∧ q ∣ n) {R : Finset (ℕ × ℕ)} (hRA : R ⊆ A.offDiag) {ℓ : ℝ}
    (hℓ : log n ≤ ℓ) :
    0 ≤ (F n : ℝ) ^ 2 - ∑ q ∈ A, (F q : ℝ) ^ 2 - ∑ Q ∈ R, (F Q.1 : ℝ) * F Q.2 ∧
      (F n : ℝ) ^ 2 - ∑ q ∈ A, (F q : ℝ) ^ 2 - ∑ Q ∈ R, (F Q.1 : ℝ) * F Q.2 ≤
        4 * (2 * ℓ * (ℓ - ∑ q ∈ A, log (q : ℝ)) +
          (ℓ ^ 2 - ∑ q ∈ A, log (q : ℝ) ^ 2 - ∑ Q ∈ R, log (Q.1 : ℝ) * log Q.2)) := by
  obtain ⟨h0, h1⟩ := F_sub_sum_le hn hA hℓ
  obtain ⟨-, h1'⟩ := F_sub_sum_le hn hA le_rfl
  -- the pairs of distinct primes of `A` outside `R`
  have hsplit : ∀ g : ℕ → ℝ, (∑ q ∈ A, g q) ^ 2 - ∑ q ∈ A, g q ^ 2 - ∑ Q ∈ R, g Q.1 * g Q.2 =
      ∑ Q ∈ A.offDiag \ R, g Q.1 * g Q.2 := by
    intro g
    rw [sq_sum_eq, ← Finset.sum_sdiff hRA]
    ring
  have hW0 : 0 ≤ ∑ Q ∈ A.offDiag \ R, (F Q.1 : ℝ) * F Q.2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hW : ∑ Q ∈ A.offDiag \ R, (F Q.1 : ℝ) * F Q.2 ≤
      4 * ∑ Q ∈ A.offDiag \ R, log (Q.1 : ℝ) * log Q.2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun Q hQ => ?_
    obtain ⟨hQ1, hQ2, -⟩ := Finset.mem_offDiag.1 (Finset.mem_sdiff.1 hQ).1
    have h1 := F_le_two_mul_log (hA _ hQ1).1.ne_zero
    have h2 := F_le_two_mul_log (hA _ hQ2).1.ne_zero
    have := mul_le_mul h1 h2 (Nat.cast_nonneg _) (by linarith [Nat.cast_nonneg (α := ℝ) (F Q.1)])
    linarith
  have hsF := hsplit fun q => (F q : ℝ)
  have hsl := hsplit fun q => log (q : ℝ)
  set S := ∑ q ∈ A, (F q : ℝ)
  set Sl := ∑ q ∈ A, log (q : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hSl : 0 ≤ Sl := Finset.sum_nonneg fun _ _ => log_natCast_nonneg _
  have hFn : (F n : ℝ) ≤ 2 * log n := F_le_two_mul_log hn
  have hSln : Sl ≤ log n := by linarith
  have hSlℓ : Sl ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ hSl (by linarith) 2
  constructor
  · nlinarith
  · nlinarith

/-- Eventually `c T⁶ ≤ L`, where `L = log y` and `T = log L`. -/
private lemma eventually_mul_loglog_pow_le (c : ℝ) :
    ∀ᶠ y : ℝ in atTop, c * log (log y) ^ 6 ≤ log y := by
  have hε : (0 : ℝ) < 1 / (|c| + 1) := by positivity
  filter_upwards [tendsto_log_atTop.eventually ((isLittleO_pow_log_id_atTop (n := 6)).bound hε),
    tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with y hy hL
  have hT : 0 ≤ log (log y) ^ 6 := Even.pow_nonneg (by decide) _
  rw [norm_of_nonneg hT, id, norm_of_nonneg (by linarith)] at hy
  have h1 : (|c| + 1) * log (log y) ^ 6 ≤ log y := by
    calc _ ≤ (|c| + 1) * (1 / (|c| + 1) * log y) := by gcongr
      _ = log y := by field_simp
  nlinarith [le_abs_self c]

/-- Eventually `T = log log y ≥ 2`. -/
private lemma eventually_two_le_loglog : ∀ᶠ y : ℝ in atTop, 2 ≤ log (log y) :=
  (tendsto_log_atTop.comp tendsto_log_atTop).eventually (eventually_ge_atTop 2)

/-- Eventually `region₁ y` consists of primes `q ≤ y`. -/
private lemma eventually_region₁_le :
    ∀ᶠ y : ℝ in atTop, ∀ q ∈ region₁ y, q.Prime ∧ (q : ℝ) ≤ y := by
  filter_upwards [exists_region₁_eq, eventually_ge_atTop 1] with y hex hy q hq
  obtain ⟨U, -, hU, hreg⟩ := hex
  have ha : 0 ≤ margin y := by unfold margin; positivity
  rw [hreg] at hq
  have hq' := Finset.mem_filter.1 hq
  refine ⟨hq'.2, ?_⟩
  calc (q : ℝ) ≤ ⌊y ^ U⌋₊ := by exact_mod_cast (Finset.mem_Ioc.1 hq'.1).2
    _ ≤ y ^ U := Nat.floor_le (by positivity)
    _ ≤ y ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hy (by linarith)
    _ = y := rpow_one y

/-- `spare_slot_one` for a coefficient bounded by `M` on `region₁`. -/
private lemma spare_slot_one_le (hR : RectangleInput) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop,
    ∀ G : ℕ → ℝ, ∀ M : ℝ, 0 < M → (∀ q ∈ region₁ x, |G q| ≤ M) →
      |∑ p ∈ dyadicPrimes x, ∑ q ∈ region₁ x with q ∣ p - 1, G q -
          (dyadicPrimes x).card * ∑ q ∈ region₁ x, G q / q| ≤
        K * M * (dyadicPrimes x).card / log (log x) ^ 7 := by
  obtain ⟨K, hK⟩ := spare_slot_one hR
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  filter_upwards [hK, eventually_two_le_loglog] with x hx hT G M hM hG
  set B : ℕ → ℝ := fun q => if q ∈ region₁ x then G q / M else 0
  have hB : ∀ q, |B q| ≤ 1 := by
    intro q
    by_cases hq : q ∈ region₁ x
    · simp only [B, hq, ite_true, abs_div, abs_of_pos hM]
      exact (div_le_one hM).2 (hG q hq)
    · simp [B, hq]
  have h := hx B hB
  have e1 : ∑ p ∈ dyadicPrimes x, ∑ q ∈ region₁ x with q ∣ p - 1, B q =
      (∑ p ∈ dyadicPrimes x, ∑ q ∈ region₁ x with q ∣ p - 1, G q) / M := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun q hq => by simp [B, (Finset.mem_filter.1 hq).1]
  have e2 : ∑ q ∈ region₁ x, B q / q = (∑ q ∈ region₁ x, G q / q) / M := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun q hq => by simp only [B, hq, ite_true]; ring
  rw [e1, e2, ← mul_div_assoc, ← sub_div, abs_div, abs_of_pos hM, div_le_iff₀ hM] at h
  have hT7 : 0 < log (log x) ^ 7 := by positivity
  have h1 : K * (dyadicPrimes x).card / log (log x) ^ 7 ≤
      max K 0 * (dyadicPrimes x).card / log (log x) ^ 7 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)) hT7.le
  calc _ ≤ K * (dyadicPrimes x).card / log (log x) ^ 7 * M := h
    _ ≤ max K 0 * (dyadicPrimes x).card / log (log x) ^ 7 * M :=
      mul_le_mul_of_nonneg_right h1 hM.le
    _ = _ := by ring

/-- `spare_slot_two` for a coefficient bounded by `M` on `region₂`. -/
private lemma spare_slot_two_le (hR : RectangleInput) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop,
    ∀ G : ℕ → ℕ → ℝ, ∀ M : ℝ, 0 < M → (∀ Q ∈ region₂ x, |G Q.1 Q.2| ≤ M) →
      |∑ p ∈ dyadicPrimes x, ∑ Q ∈ region₂ x with Q.1 * Q.2 ∣ p - 1, G Q.1 Q.2 -
          (dyadicPrimes x).card * ∑ Q ∈ region₂ x, G Q.1 Q.2 / (Q.1 * Q.2)| ≤
        K * M * (dyadicPrimes x).card / log (log x) ^ 7 := by
  obtain ⟨K, hK⟩ := spare_slot_two hR
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  filter_upwards [hK, eventually_two_le_loglog] with x hx hT G M hM hG
  set B : ℕ → ℕ → ℝ := fun q r => if (q, r) ∈ region₂ x then G q r / M else 0
  have hB : ∀ q r, |B q r| ≤ 1 := by
    intro q r
    by_cases hq : (q, r) ∈ region₂ x
    · simp only [B, hq, ite_true, abs_div, abs_of_pos hM]
      exact (div_le_one hM).2 (hG _ hq)
    · simp [B, hq]
  have h := hx B hB
  have e1 : ∑ p ∈ dyadicPrimes x, ∑ Q ∈ region₂ x with Q.1 * Q.2 ∣ p - 1, B Q.1 Q.2 =
      (∑ p ∈ dyadicPrimes x, ∑ Q ∈ region₂ x with Q.1 * Q.2 ∣ p - 1, G Q.1 Q.2) / M := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun Q hQ => by simp [B, (Finset.mem_filter.1 hQ).1]
  have e2 : ∑ Q ∈ region₂ x, B Q.1 Q.2 / (Q.1 * Q.2) =
      (∑ Q ∈ region₂ x, G Q.1 Q.2 / (Q.1 * Q.2)) / M := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun Q hQ => by simp only [B, hQ, ite_true]; ring
  rw [e1, e2, ← mul_div_assoc, ← sub_div, abs_div, abs_of_pos hM, div_le_iff₀ hM] at h
  have hT7 : 0 < log (log x) ^ 7 := by positivity
  have h1 : K * (dyadicPrimes x).card / log (log x) ^ 7 ≤
      max K 0 * (dyadicPrimes x).card / log (log x) ^ 7 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)) hT7.le
  calc _ ≤ K * (dyadicPrimes x).card / log (log x) ^ 7 * M := h
    _ ≤ max K 0 * (dyadicPrimes x).card / log (log x) ^ 7 * M :=
      mul_le_mul_of_nonneg_right h1 hM.le
    _ = _ := by ring

/-- The scales used below: eventually `y ≥ 3`, `T⁶ ≥ 1`, `c ≤ L T⁻⁶`, `1 ≤ L T⁻⁶`,
`0 ≤ m ≤ a ≤ 1 / 64` and `T⁻⁷ ≤ T⁻⁶`. -/
private lemma eventually_scales (c : ℝ) : ∀ᶠ y : ℝ in atTop, 3 ≤ y ∧
    1 ≤ log (log y) ^ 6 ∧ c ≤ log y / log (log y) ^ 6 ∧ 1 ≤ log y / log (log y) ^ 6 ∧
      0 ≤ mesh y ∧ mesh y ≤ margin y ∧ margin y ≤ 1 / 64 ∧
        1 / log (log y) ^ 7 ≤ 1 / log (log y) ^ 6 := by
  filter_upwards [eventually_mul_loglog_pow_le (max c 1), eventually_two_le_loglog,
    mesh_le_margin_pow, eventually_ge_atTop 3] with y h1 hT hm hy
  have hT6 : (64 : ℝ) ≤ log (log y) ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT 6
    norm_num at this
    exact this
  have hT6' : (0 : ℝ) < log (log y) ^ 6 := by linarith
  have hX : max c 1 ≤ log y / log (log y) ^ 6 := (le_div_iff₀ hT6').2 h1
  refine ⟨hy, by linarith, (le_max_left _ _).trans hX, (le_max_right _ _).trans hX,
    by unfold mesh; positivity, hm.1.trans ?_, ?_, ?_⟩
  · exact one_div_le_one_div_of_le hT6' (pow_le_pow_right₀ (by linarith) (by norm_num))
  · exact one_div_le_one_div_of_le (by norm_num) hT6
  · exact one_div_le_one_div_of_le hT6' (pow_le_pow_right₀ (by linarith) (by norm_num))

/-- Positivity for one prime: `Π log 2y - ∑_p ∑_{q ∈ region₁, q ∣ p - 1} log q ≪ Π L T⁻⁶`,
since `∑_{q ∣ n} log q ≤ log n < log 2y` while the spare-slot statistic and Mertens' first
theorem give `∑_{region₁} log q / q ≥ (1 - 2a - m) L - O(1)`. -/
private lemma first_positivity (hR : RectangleInput) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ y : ℝ in atTop,
    (dyadicPrimes y).card * log (2 * y) -
        ∑ p ∈ dyadicPrimes y, ∑ q ∈ region₁ y with q ∣ p - 1, log (q : ℝ) ≤
      K * (dyadicPrimes y).card * log y / log (log y) ^ 6 := by
  obtain ⟨K₁, hK₁, hS⟩ := spare_slot_one_le hR
  obtain ⟨E, hE0, hE⟩ := mertens_first
  refine ⟨K₁ + 4, by linarith, ?_⟩
  filter_upwards [hS, exists_region₁_eq, eventually_region₁_le, eventually_scales (E + 1)]
    with y hy hex hreg₁ hsc
  obtain ⟨U, hU1, hU2, hreg⟩ := hex
  obtain ⟨hy3, hT6, hEX, hX, hm0, hma, ha, hT7⟩ := hsc
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hL : 1 ≤ log y := hX.trans (div_le_self (log_nonneg (by linarith)) hT6)
  have ha0 : 0 ≤ margin y := by unfold margin; positivity
  -- the spare-slot statistic with `B q = log q / L`
  have h1 := hy (fun q => log (q : ℝ)) (log y) (by linarith) fun q hq => by
    have hq' := hreg₁ q hq
    rw [abs_of_nonneg (log_natCast_nonneg q)]
    exact log_le_log (by exact_mod_cast hq'.1.pos) hq'.2
  -- Mertens' first theorem on `region₁ = (y^a, y^U]`
  have h2 := hE (y ^ margin y) (y ^ U) (one_le_rpow hy1 ha0)
    (rpow_le_rpow_of_exponent_le hy1 (by linarith))
  rw [← hreg, log_div (by positivity) (by positivity), log_rpow (by linarith),
    log_rpow (by linarith)] at h2
  have h3 := (abs_le.1 h1).1
  have h4 := mul_le_mul_of_nonneg_left (abs_le.1 h2).1
    (Nat.cast_nonneg (α := ℝ) (dyadicPrimes y).card)
  have h5 := mul_le_mul_of_nonneg_left hT7
    (mul_nonneg (mul_nonneg hK₁ (by linarith : (0 : ℝ) ≤ log y))
      (Nat.cast_nonneg (α := ℝ) (dyadicPrimes y).card))
  have haL : margin y * log y = log y / log (log y) ^ 6 := by unfold margin; ring
  have hmL : mesh y * log y ≤ margin y * log y :=
    mul_le_mul_of_nonneg_right hma (by linarith)
  have hUL : (1 - U) * log y ≤ (margin y + mesh y) * log y :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hl2 : log (2 * y) = log 2 + log y := log_mul (by norm_num) (by linarith)
  have hl2' : log 2 < 1 := lt_trans log_two_lt_d9 (by norm_num)
  have key : log 2 + log y - (U * log y - margin y * log y - E) ≤
      4 * (log y / log (log y) ^ 6) := by
    linarith
  have h6 := mul_le_mul_of_nonneg_left key (Nat.cast_nonneg (α := ℝ) (dyadicPrimes y).card)
  rw [hl2]
  calc _ ≤ ((dyadicPrimes y).card : ℝ) *
        (log 2 + log y - (U * log y - margin y * log y - E)) +
          K₁ * log y * (dyadicPrimes y).card / log (log y) ^ 7 := by linarith
    _ ≤ ((dyadicPrimes y).card : ℝ) * (4 * (log y / log (log y) ^ 6)) +
          K₁ * log y * (dyadicPrimes y).card * (1 / log (log y) ^ 6) := by
      have : K₁ * log y * (dyadicPrimes y).card / log (log y) ^ 7 =
          K₁ * log y * (dyadicPrimes y).card * (1 / log (log y) ^ 7) := by ring
      linarith
    _ = _ := by ring

/-- Positivity for pairs: `Π (log 2y)² - ∑_p ∑_{region₁} (log q)² - ∑_p ∑_{region₂} log q log r
≪ Π L² T⁻⁶`, from the model lower bounds `region₁_square_model` and `region₂_model`. -/
private lemma second_positivity (hR : RectangleInput) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ y : ℝ in atTop,
    (dyadicPrimes y).card * log (2 * y) ^ 2 -
        ∑ p ∈ dyadicPrimes y, ∑ q ∈ region₁ y with q ∣ p - 1, log (q : ℝ) ^ 2 -
        ∑ p ∈ dyadicPrimes y, ∑ Q ∈ region₂ y with Q.1 * Q.2 ∣ p - 1,
          log (Q.1 : ℝ) * log (Q.2 : ℝ) ≤
      K * (dyadicPrimes y).card * log y ^ 2 / log (log y) ^ 6 := by
  obtain ⟨K₁, hK₁, hS₁⟩ := spare_slot_one_le hR
  obtain ⟨K₂, hK₂, hS₂⟩ := spare_slot_two_le hR
  obtain ⟨C₁, hC₁⟩ := region₁_square_model
  obtain ⟨C₂, hC₂⟩ := region₂_model
  refine ⟨K₁ + K₂ + |C₁| + |C₂| + 7, by positivity, ?_⟩
  filter_upwards [hS₁, hS₂, hC₁, hC₂, eventually_region₁_le, mem_region₂, eventually_scales 0]
    with y h₁ h₂ hm₁ hm₂ hreg₁ hreg₂ hsc
  obtain ⟨hy3, hT6, -, hX, hm0, hma, ha, hT7⟩ := hsc
  have hL : 1 ≤ log y := hX.trans (div_le_self (log_nonneg (by linarith)) hT6)
  have hlog : ∀ q ∈ region₁ y, 0 ≤ log (q : ℝ) ∧ log (q : ℝ) ≤ log y := fun q hq =>
    ⟨log_natCast_nonneg q, log_le_log (by exact_mod_cast (hreg₁ q hq).1.pos) (hreg₁ q hq).2⟩
  -- the spare-slot statistics with `B q = (log q / L)²` and `B q r = log q log r / L²`
  have h₁' := h₁ (fun q => log (q : ℝ) ^ 2) (log y ^ 2) (by positivity) fun q hq => by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (hlog q hq).1 (hlog q hq).2 2
  have h₂' := h₂ (fun q r => log (q : ℝ) * log (r : ℝ)) (log y ^ 2) (by positivity) fun Q hQ => by
    obtain ⟨hQ1, hQ2, -⟩ := hreg₂ Q hQ
    rw [abs_of_nonneg (mul_nonneg (hlog _ hQ1).1 (hlog _ hQ2).1), sq]
    exact mul_le_mul (hlog _ hQ1).2 (hlog _ hQ2).2 (hlog _ hQ2).1 (by linarith)
  have e₁ : ∑ q ∈ region₁ y, log (q : ℝ) ^ 2 / q =
      log y ^ 2 * ∑ q ∈ region₁ y, (log (q : ℝ) / log y) ^ 2 / q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by field_simp
  have e₂ : ∑ Q ∈ region₂ y, log (Q.1 : ℝ) * log (Q.2 : ℝ) / (Q.1 * Q.2) =
      log y ^ 2 * ∑ Q ∈ region₂ y, log (Q.1 : ℝ) / log y * (log (Q.2 : ℝ) / log y) /
        (Q.1 * Q.2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun Q _ => by field_simp
  -- the two models add up to at least `1 - 4a - O(m)`
  have hmod : 1 - 4 * margin y - (|C₁| + |C₂|) * mesh y ≤
      ∑ q ∈ region₁ y, (log (q : ℝ) / log y) ^ 2 / q +
        ∑ Q ∈ region₂ y, log (Q.1 : ℝ) / log y * (log (Q.2 : ℝ) / log y) / (Q.1 * Q.2) := by
    have := add_le_add hm₁ hm₂
    nlinarith [le_abs_self C₁, le_abs_self C₂, sq_nonneg (margin y)]
  have hmod' := mul_le_mul_of_nonneg_left hmod (sq_nonneg (log y))
  rw [mul_add, ← e₁, ← e₂] at hmod'
  have haL : margin y * log y ^ 2 = log y ^ 2 / log (log y) ^ 6 := by unfold margin; ring
  have hmL : (|C₁| + |C₂|) * (mesh y * log y ^ 2) ≤
      (|C₁| + |C₂|) * (log y ^ 2 / log (log y) ^ 6) :=
    mul_le_mul_of_nonneg_left (haL ▸ mul_le_mul_of_nonneg_right hma (sq_nonneg _))
      (by positivity)
  have hLX : log y ≤ log y ^ 2 / log (log y) ^ 6 := by
    have := mul_le_mul_of_nonneg_left hX (by linarith : (0 : ℝ) ≤ log y)
    rw [mul_one] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  have hl2 : log (2 * y) = log 2 + log y := log_mul (by norm_num) (by linarith)
  have hl2' : log 2 < 1 := lt_trans log_two_lt_d9 (by norm_num)
  have hl2'' : 0 < log 2 := log_pos (by norm_num)
  have hsq : log (2 * y) ^ 2 ≤ log y ^ 2 + 3 * log y := by rw [hl2]; nlinarith
  have key : log (2 * y) ^ 2 -
      (∑ q ∈ region₁ y, log (q : ℝ) ^ 2 / q +
        ∑ Q ∈ region₂ y, log (Q.1 : ℝ) * log (Q.2 : ℝ) / (Q.1 * Q.2)) ≤
      (|C₁| + |C₂| + 7) * (log y ^ 2 / log (log y) ^ 6) := by
    nlinarith
  have h6 := mul_le_mul_of_nonneg_left key (Nat.cast_nonneg (α := ℝ) (dyadicPrimes y).card)
  have h7 := mul_le_mul_of_nonneg_left hT7
    (mul_nonneg (mul_nonneg (add_nonneg hK₁ hK₂) (sq_nonneg (log y)))
      (Nat.cast_nonneg (α := ℝ) (dyadicPrimes y).card))
  have e₃ : (K₁ + K₂) * log y ^ 2 * (dyadicPrimes y).card * (1 / log (log y) ^ 7) =
      K₁ * log y ^ 2 * (dyadicPrimes y).card / log (log y) ^ 7 +
        K₂ * log y ^ 2 * (dyadicPrimes y).card / log (log y) ^ 7 := by ring
  have e₄ : (K₁ + K₂ + |C₁| + |C₂| + 7) * (dyadicPrimes y).card * log y ^ 2 /
        log (log y) ^ 6 =
      (dyadicPrimes y).card * ((|C₁| + |C₂| + 7) * (log y ^ 2 / log (log y) ^ 6)) +
        (K₁ + K₂) * log y ^ 2 * (dyadicPrimes y).card * (1 / log (log y) ^ 6) := by ring
  rw [e₄]
  linarith [(abs_le.1 h₁').1, (abs_le.1 h₂').1]

/-- The harmonic tail outside `region₁`: if `0 ≤ g q ≤ c log q / q` for primes `q ≤ y`, then
`0 ≤ ∑_{q ≤ y} g q - ∑_{region₁} g q ≪ c L T⁻⁶`, by Mertens' first theorem on `(1, y^a]`
and `(y^U, y]`. -/
private lemma tail_region₁ : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ y : ℝ in atTop, ∀ g : ℕ → ℝ, ∀ c : ℝ,
    0 ≤ c → (∀ q : ℕ, q.Prime → (q : ℝ) ≤ y → 0 ≤ g q ∧ g q ≤ c * (log q / q)) →
      0 ≤ ∑ q ∈ primesIoc 1 y, g q - ∑ q ∈ region₁ y, g q ∧
        ∑ q ∈ primesIoc 1 y, g q - ∑ q ∈ region₁ y, g q ≤
          c * (K * log y / log (log y) ^ 6) := by
  obtain ⟨E, hE0, hE⟩ := mertens_first
  refine ⟨5, by norm_num, ?_⟩
  filter_upwards [exists_region₁_eq, eventually_scales E] with y hex hsc g c hc hg
  obtain ⟨U, hU1, hU2, hreg⟩ := hex
  obtain ⟨hy3, hT6, hEX, hX, hm0, hma, ha, -⟩ := hsc
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hL : 0 ≤ log y := log_nonneg hy1
  have ha0 : 0 ≤ margin y := by unfold margin; positivity
  have h1 : (1 : ℝ) ≤ y ^ margin y := one_le_rpow hy1 ha0
  have h2 : y ^ margin y ≤ y ^ U := rpow_le_rpow_of_exponent_le hy1 (by linarith)
  have h3 : y ^ U ≤ y := by
    simpa using rpow_le_rpow_of_exponent_le hy1 (show U ≤ 1 by linarith)
  rw [← sum_primesIoc_add _ h1 (h2.trans h3), ← sum_primesIoc_add _ h2 h3, ← hreg]
  -- each piece is a Mertens sum
  have hpiece : ∀ z w : ℝ, 1 ≤ z → z ≤ w → w ≤ y → 0 ≤ ∑ q ∈ primesIoc z w, g q ∧
      ∑ q ∈ primesIoc z w, g q ≤ c * (log (w / z) + E) := by
    intro z w hz hzw hw
    have hmem : ∀ q ∈ primesIoc z w, q.Prime ∧ (q : ℝ) ≤ y := fun q hq => by
      obtain ⟨hp, -, hq⟩ := mem_primesIoc.1 hq
      exact ⟨hp, hq.trans hw⟩
    refine ⟨Finset.sum_nonneg fun q hq => (hg q (hmem q hq).1 (hmem q hq).2).1, ?_⟩
    calc ∑ q ∈ primesIoc z w, g q ≤ ∑ q ∈ primesIoc z w, c * (log (q : ℝ) / q) :=
          Finset.sum_le_sum fun q hq => (hg q (hmem q hq).1 (hmem q hq).2).2
      _ = c * ∑ q ∈ primesIoc z w, log (q : ℝ) / q := (Finset.mul_sum _ _ _).symm
      _ ≤ c * (log (w / z) + E) :=
        mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 (hE z w hz hzw)).2]) hc
  obtain ⟨hA0, hA⟩ := hpiece 1 (y ^ margin y) le_rfl h1 (h2.trans h3)
  obtain ⟨hB0, hB⟩ := hpiece (y ^ U) y (h1.trans h2) h3 le_rfl
  rw [div_one, log_rpow (by linarith)] at hA
  rw [log_div (by positivity) (by positivity), log_rpow (by linarith)] at hB
  have haL : margin y * log y = log y / log (log y) ^ 6 := by unfold margin; ring
  have hmL : mesh y * log y ≤ margin y * log y := mul_le_mul_of_nonneg_right hma hL
  have hUL : (1 - U) * log y ≤ (margin y + mesh y) * log y :=
    mul_le_mul_of_nonneg_right (by linarith) hL
  have key : margin y * log y + E + (log y - U * log y + E) ≤
      5 * log y / log (log y) ^ 6 := by
    have : 5 * log y / log (log y) ^ 6 = 5 * (log y / log (log y) ^ 6) := by ring
    linarith
  refine ⟨by linarith, ?_⟩
  calc _ = ∑ q ∈ primesIoc 1 (y ^ margin y), g q + ∑ q ∈ primesIoc (y ^ U) y, g q := by ring
    _ ≤ c * (margin y * log y + E) + c * (log y - U * log y + E) := add_le_add hA hB
    _ = c * (margin y * log y + E + (log y - U * log y + E)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key hc

/-- `D(y)` as a sum over the ordered pairs of distinct primes `q, r ≤ y` with `q r ≤ y`. -/
private lemma harmonicFPair_eq_sum_pairs (y : ℝ) : harmonicFPair y =
    ∑ Q ∈ (primesIoc 1 y ×ˢ primesIoc 1 y).filter
        (fun Q => Q.1 ≠ Q.2 ∧ ((Q.1 * Q.2 : ℕ) : ℝ) ≤ y),
      (F Q.1 : ℝ) * F Q.2 / (Q.1 * Q.2) := by
  unfold harmonicFPair
  refine (Finset.sum_finset_product' _ _ _ fun Q => ?_).symm
  obtain ⟨q, r⟩ := Q
  simp only [Finset.mem_filter, Finset.mem_product, mem_primesIoc (y := 1) (z := y)]
  constructor
  · rintro ⟨⟨⟨hq, hq1, hqy⟩, hr, hr1, hry⟩, hne, hqr⟩
    have hq0 : (0 : ℝ) < q := by linarith
    refine ⟨⟨hq, hq1, hqy⟩, mem_primesIoc.2 ⟨hr, hr1, ?_⟩, Ne.symm hne⟩
    rw [le_div_iff₀ hq0]
    push_cast at hqr
    linarith
  · rintro ⟨⟨hq, hq1, hqy⟩, hr', hne⟩
    have hq0 : (0 : ℝ) < q := by linarith
    obtain ⟨hr, hr1, hry⟩ := mem_primesIoc.1 hr'
    rw [le_div_iff₀ hq0] at hry
    refine ⟨⟨⟨hq, hq1, hqy⟩, hr, hr1, by nlinarith⟩, Ne.symm hne, ?_⟩
    push_cast
    linarith

/-- The harmonic tail outside `region₂`: `0 ≤ D(y) - ∑_{region₂} F q F r / (q r) ≪ L² T⁻⁶`.
A pair of distinct primes with `q r ≤ y` outside `region₂` has `q ≤ y^a`, `r ≤ y^a` or
`q r > y^{1 - a - 3m}`, and Mertens' first theorem bounds each part. -/
private lemma tail_region₂ : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ y : ℝ in atTop,
    0 ≤ harmonicFPair y - ∑ Q ∈ region₂ y, (F Q.1 : ℝ) * F Q.2 / (Q.1 * Q.2) ∧
      harmonicFPair y - ∑ Q ∈ region₂ y, (F Q.1 : ℝ) * F Q.2 / (Q.1 * Q.2) ≤
        K * log y ^ 2 / log (log y) ^ 6 := by
  obtain ⟨E, hE0, hE⟩ := mertens_first
  refine ⟨72, by norm_num, ?_⟩
  filter_upwards [mem_region₂, mem_region₂_of_mul_le, eventually_region₁_le,
    eventually_scales E] with y hreg₂ hmul hreg₁ hsc
  obtain ⟨hy3, hT6, hEX, hX, hm0, hma, ha, -⟩ := hsc
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hL : 0 ≤ log y := log_nonneg hy1
  have ha0 : 0 ≤ margin y := by unfold margin; positivity
  set a := margin y with ha_def
  set m := mesh y
  set c := 1 - a - 3 * m with hc_def
  have hya : (1 : ℝ) ≤ y ^ a := one_le_rpow hy1 ha0
  have hyay : y ^ a ≤ y := by
    simpa using rpow_le_rpow_of_exponent_le hy1 (show a ≤ 1 by linarith)
  have hyc : y ^ c ≤ y := by
    simpa using rpow_le_rpow_of_exponent_le hy1 (show c ≤ 1 by linarith)
  have hyc0 : 0 < y ^ c := by positivity
  set P := primesIoc 1 y
  have hP : ∀ q, q ∈ P ↔ q.Prime ∧ 1 < (q : ℝ) ∧ (q : ℝ) ≤ y := fun q => mem_primesIoc
  have hPa : ∀ q, q ∈ primesIoc 1 (y ^ a) ↔ q.Prime ∧ 1 < (q : ℝ) ∧ (q : ℝ) ≤ y ^ a :=
    fun q => mem_primesIoc
  set PP := (P ×ˢ P).filter fun Q => Q.1 ≠ Q.2 ∧ ((Q.1 * Q.2 : ℕ) : ℝ) ≤ y
  have hPP : ∀ Q, Q ∈ PP ↔ Q.1 ∈ P ∧ Q.2 ∈ P ∧ Q.1 ≠ Q.2 ∧ ((Q.1 * Q.2 : ℕ) : ℝ) ≤ y :=
    fun Q => by simp only [PP, Finset.mem_filter, Finset.mem_product, and_assoc]
  have hsub : region₂ y ⊆ PP := by
    intro Q hQ
    obtain ⟨hQ1, hQ2, hne, -, -, hQ⟩ := hreg₂ Q hQ
    have hya' : y ^ (1 - a) ≤ y := by
      simpa using rpow_le_rpow_of_exponent_le hy1 (show 1 - a ≤ 1 by linarith)
    refine (hPP Q).2 ⟨(hP _).2 ⟨(hreg₁ _ hQ1).1, ?_, (hreg₁ _ hQ1).2⟩,
      (hP _).2 ⟨(hreg₁ _ hQ2).1, ?_, (hreg₁ _ hQ2).2⟩, hne, hQ.trans hya'⟩
    · exact_mod_cast (hreg₁ _ hQ1).1.one_lt
    · exact_mod_cast (hreg₁ _ hQ2).1.one_lt
  rw [harmonicFPair_eq_sum_pairs, ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  -- the majorant `4 (log q / q) (log r / r)`
  set h : ℕ × ℕ → ℝ := fun Q => 4 * (log (Q.1 : ℝ) / Q.1 * (log (Q.2 : ℝ) / Q.2)) with hh
  have hh0 : ∀ Q, 0 ≤ h Q := fun Q => by
    simp only [h]
    have := log_natCast_nonneg Q.1
    have := log_natCast_nonneg Q.2
    positivity
  have hgh : ∀ Q ∈ PP \ region₂ y, (F Q.1 : ℝ) * F Q.2 / (Q.1 * Q.2) ≤ h Q := by
    intro Q hQ
    obtain ⟨hQ1, hQ2, -⟩ := (hPP Q).1 (Finset.mem_sdiff.1 hQ).1
    have h1 := F_le_two_mul_log ((hP _).1 hQ1).1.ne_zero
    have h2 := F_le_two_mul_log ((hP _).1 hQ2).1.ne_zero
    have h1' : (F Q.1 : ℝ) / Q.1 ≤ 2 * log (Q.1 : ℝ) / Q.1 :=
      div_le_div_of_nonneg_right h1 (Nat.cast_nonneg _)
    have h2' : (F Q.2 : ℝ) / Q.2 ≤ 2 * log (Q.2 : ℝ) / Q.2 :=
      div_le_div_of_nonneg_right h2 (Nat.cast_nonneg _)
    have := mul_le_mul h1' h2' (by positivity)
      (div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (F Q.1)]) (Nat.cast_nonneg _))
    calc (F Q.1 : ℝ) * F Q.2 / (Q.1 * Q.2) = (F Q.1 : ℝ) / Q.1 * (F Q.2 / Q.2) := by
          rw [mul_div_mul_comm]
      _ ≤ 2 * log (Q.1 : ℝ) / Q.1 * (2 * log (Q.2 : ℝ) / Q.2) := this
      _ = h Q := by simp only [h]; ring
  -- the three parts
  set Sa := primesIoc 1 (y ^ a) ×ˢ P
  set Sb := P ×ˢ primesIoc 1 (y ^ a)
  set Sc := (P ×ˢ P).filter fun Q => y ^ c < ((Q.1 * Q.2 : ℕ) : ℝ) ∧ ((Q.1 * Q.2 : ℕ) : ℝ) ≤ y
  have hcover : PP \ region₂ y ⊆ Sa ∪ Sb ∪ Sc := by
    intro Q hQ
    obtain ⟨hQP, hQ2⟩ := Finset.mem_sdiff.1 hQ
    obtain ⟨hq, hr, hne, hqr⟩ := (hPP Q).1 hQP
    simp only [Finset.mem_union, Sa, Sb, Sc, Finset.mem_product, Finset.mem_filter]
    by_cases hqa : (Q.1 : ℝ) ≤ y ^ a
    · exact Or.inl (Or.inl ⟨(hPa _).2 ⟨((hP _).1 hq).1, ((hP _).1 hq).2.1, hqa⟩, hr⟩)
    by_cases hra : (Q.2 : ℝ) ≤ y ^ a
    · exact Or.inl (Or.inr ⟨hq, (hPa _).2 ⟨((hP _).1 hr).1, ((hP _).1 hr).2.1, hra⟩⟩)
    by_cases hc : ((Q.1 * Q.2 : ℕ) : ℝ) ≤ y ^ c
    · exact absurd (hmul Q.1 Q.2 ((hP _).1 hq).1 ((hP _).1 hr).1 hne (not_le.1 hqa)
        (not_le.1 hra) hc) hQ2
    · exact Or.inr ⟨⟨hq, hr⟩, not_le.1 hc, hqr⟩
  -- Mertens' bounds
  have hMP : 0 ≤ ∑ q ∈ P, log (q : ℝ) / q ∧ ∑ q ∈ P, log (q : ℝ) / q ≤ log y + E := by
    refine ⟨Finset.sum_nonneg fun q _ => by have := log_natCast_nonneg q; positivity, ?_⟩
    have := (abs_le.1 (hE 1 y le_rfl hy1)).2
    rw [div_one] at this
    linarith
  have hMa : 0 ≤ ∑ q ∈ primesIoc 1 (y ^ a), log (q : ℝ) / q ∧
      ∑ q ∈ primesIoc 1 (y ^ a), log (q : ℝ) / q ≤ a * log y + E := by
    refine ⟨Finset.sum_nonneg fun q _ => by have := log_natCast_nonneg q; positivity, ?_⟩
    have := (abs_le.1 (hE 1 (y ^ a) le_rfl hya)).2
    rw [div_one, log_rpow (by linarith)] at this
    linarith
  have hSa : ∑ Q ∈ Sa, h Q = 4 * ((∑ q ∈ primesIoc 1 (y ^ a), log (q : ℝ) / q) *
      ∑ r ∈ P, log (r : ℝ) / r) := by
    rw [Finset.sum_product, Finset.sum_mul_sum, Finset.mul_sum]
    simp_rw [Finset.mul_sum, h]
  have hSb : ∑ Q ∈ Sb, h Q = 4 * ((∑ q ∈ P, log (q : ℝ) / q) *
      ∑ r ∈ primesIoc 1 (y ^ a), log (r : ℝ) / r) := by
    rw [Finset.sum_product, Finset.sum_mul_sum, Finset.mul_sum]
    simp_rw [Finset.mul_sum, h]
  -- the strip `y^c < q r ≤ y`: for fixed `q`, `r ∈ (max 1 (y^c / q), y / q]`
  have hinner : ∀ q ∈ P, ∑ r ∈ P with y ^ c < ((q * r : ℕ) : ℝ) ∧ ((q * r : ℕ) : ℝ) ≤ y,
      log (r : ℝ) / r ≤ (1 - c) * log y + E := by
    intro q hq
    obtain ⟨-, hq1, hqy⟩ := (hP q).1 hq
    have hq0 : (0 : ℝ) < q := by linarith
    have hzw : max 1 (y ^ c / q) ≤ y / q :=
      max_le ((le_div_iff₀ hq0).2 (by linarith)) (div_le_div_of_nonneg_right hyc hq0.le)
    have hsub' : (P.filter fun r => y ^ c < ((q * r : ℕ) : ℝ) ∧ ((q * r : ℕ) : ℝ) ≤ y) ⊆
        primesIoc (max 1 (y ^ c / q)) (y / q) := by
      intro r hr
      obtain ⟨hr, hcr, hry⟩ := Finset.mem_filter.1 hr
      obtain ⟨hrp, hr1, -⟩ := (hP r).1 hr
      push_cast at hcr hry
      refine mem_primesIoc.2 ⟨hrp, max_lt hr1 ?_, ?_⟩
      · rw [div_lt_iff₀ hq0]; linarith
      · rw [le_div_iff₀ hq0]; linarith
    have hM := (abs_le.1 (hE _ _ (le_max_left _ _) hzw)).2
    have hlog : log (y / q / max 1 (y ^ c / q)) ≤ (1 - c) * log y := by
      have h1 : y / q / max 1 (y ^ c / q) ≤ y / q / (y ^ c / q) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (le_max_right _ _)
      have h2 : y / q / (y ^ c / q) = y / y ^ c := by field_simp
      calc _ ≤ log (y / q / (y ^ c / q)) :=
            log_le_log (div_pos (by positivity) (lt_of_lt_of_le one_pos (le_max_left _ _))) h1
        _ = (1 - c) * log y := by
          rw [h2, log_div (by positivity) hyc0.ne', log_rpow (by linarith)]
          ring
    calc _ ≤ ∑ r ∈ primesIoc (max 1 (y ^ c / q)) (y / q), log (r : ℝ) / r :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub' fun r _ _ => by
            have := log_natCast_nonneg r; positivity
      _ ≤ _ := by linarith
  have hSc : ∑ Q ∈ Sc, h Q ≤ 4 * ((∑ q ∈ P, log (q : ℝ) / q) * ((1 - c) * log y + E)) := by
    rw [Finset.sum_finset_product Sc P
      (fun q => P.filter fun r => y ^ c < ((q * r : ℕ) : ℝ) ∧ ((q * r : ℕ) : ℝ) ≤ y)
      (fun Q => by simp only [Sc, Finset.mem_filter, Finset.mem_product]; tauto),
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    simp only [h]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have := log_natCast_nonneg q
    have := mul_le_mul_of_nonneg_left (hinner q hq)
      (by positivity : (0 : ℝ) ≤ log (q : ℝ) / q)
    linarith
  -- the union bound
  have hunion : ∀ s t : Finset (ℕ × ℕ), ∑ Q ∈ s ∪ t, h Q ≤ ∑ Q ∈ s, h Q + ∑ Q ∈ t, h Q :=
    fun s t => by
      rw [← Finset.sum_union_inter]
      linarith [Finset.sum_nonneg fun Q (_ : Q ∈ s ∩ t) => hh0 Q]
  have htot : ∑ Q ∈ PP \ region₂ y, (F Q.1 : ℝ) * F Q.2 / (Q.1 * Q.2) ≤
      ∑ Q ∈ Sa, h Q + ∑ Q ∈ Sb, h Q + ∑ Q ∈ Sc, h Q :=
    calc _ ≤ ∑ Q ∈ PP \ region₂ y, h Q := Finset.sum_le_sum hgh
      _ ≤ ∑ Q ∈ Sa ∪ Sb ∪ Sc, h Q :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun Q _ _ => hh0 Q
      _ ≤ _ := by linarith [hunion (Sa ∪ Sb) Sc, hunion Sa Sb]
  refine ⟨Finset.sum_nonneg fun Q _ => by positivity, htot.trans ?_⟩
  -- with `X = L T⁻⁶`: `a L = X`, `m L ≤ X`, `E ≤ X ≤ L`
  set X := log y / log (log y) ^ 6 with hX_def
  have haL : a * log y = X := by rw [ha_def]; unfold margin; ring
  have hmL : m * log y ≤ X := haL ▸ mul_le_mul_of_nonneg_right hma hL
  have hXL : X ≤ log y := div_le_self hL hT6
  have hE1 : a * log y + E ≤ 2 * X := by linarith
  have hE2 : log y + E ≤ 2 * log y := by linarith
  have hE3 : (1 - c) * log y + E ≤ 5 * X := by
    have : (1 - c) * log y = a * log y + 3 * (m * log y) := by rw [hc_def]; ring
    linarith
  obtain ⟨hMP0, hMP1⟩ := hMP
  obtain ⟨hMa0, hMa1⟩ := hMa
  have hX0 : 0 ≤ X := by positivity
  have p1 := mul_le_mul hMa1 hMP1 hMP0 (by linarith)
  have p2 := mul_le_mul hMP1 hMa1 hMa0 (by linarith)
  have p3 := mul_le_mul_of_nonneg_left hE3 hMP0
  have p4 := mul_le_mul_of_nonneg_left hE1 (by linarith : (0 : ℝ) ≤ log y + E)
  have p5 := mul_le_mul_of_nonneg_right hE2 hX0
  have p6 := mul_le_mul_of_nonneg_right hMP1 (by linarith : (0 : ℝ) ≤ 5 * X)
  have e : 72 * log y ^ 2 / log (log y) ^ 6 = 72 * (log y * X) := by rw [hX_def]; ring
  rw [hSa, hSb, e]
  nlinarith

/-- Eventually, for every prime `p` of the dyad, `F p = F n` with `n = p - 1 ≠ 0`,
`log n ≤ log 2y`, the primes of `region₁` dividing `n` are prime divisors of `n`, and the pairs
of `region₂` dividing `n` are pairs of distinct such primes. -/
private lemma eventually_dyadicPrimes : ∀ᶠ y : ℝ in atTop, ∀ p ∈ dyadicPrimes y,
    (F p : ℝ) = F (p - 1) ∧ p - 1 ≠ 0 ∧ log ((p - 1 : ℕ) : ℝ) ≤ log (2 * y) ∧
      (∀ q ∈ (region₁ y).filter (· ∣ p - 1), q.Prime ∧ q ∣ p - 1) ∧
        (region₂ y).filter (fun Q => Q.1 * Q.2 ∣ p - 1) ⊆
          ((region₁ y).filter (· ∣ p - 1)).offDiag := by
  filter_upwards [eventually_region₁_le, mem_region₂, eventually_ge_atTop 3]
    with y hreg₁ hreg₂ hy3 p hp
  rw [dyadicPrimes_eq_primesIoc] at hp
  obtain ⟨hpp, hyp, hp2y⟩ := mem_primesIoc.1 hp
  have hp3 : 3 < p := by exact_mod_cast hy3.trans_lt hyp
  refine ⟨by exact_mod_cast F_prime_of_ne_two hpp (by omega), by omega, ?_, fun q hq => ?_,
    fun Q hQ => ?_⟩
  · have : (3 : ℝ) < p := by exact_mod_cast hp3
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    exact log_le_log (by linarith) (by linarith)
  · obtain ⟨hq, hqd⟩ := Finset.mem_filter.1 hq
    exact ⟨(hreg₁ q hq).1, hqd⟩
  · obtain ⟨hQ, hd⟩ := Finset.mem_filter.1 hQ
    obtain ⟨hQ1, hQ2, hne, -⟩ := hreg₂ Q hQ
    exact Finset.mem_offDiag.2 ⟨Finset.mem_filter.2 ⟨hQ1, (dvd_mul_right _ _).trans hd⟩,
      Finset.mem_filter.2 ⟨hQ2, (dvd_mul_left _ _).trans hd⟩, hne⟩

/-- The first dyadic moment: `|∑_p F p - Π B(y)| ≪ Π L T⁻⁶`. -/
private lemma first_moment (hR : RectangleInput) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ y : ℝ in atTop,
    |∑ p ∈ dyadicPrimes y, (F p : ℝ) - (dyadicPrimes y).card * harmonicF y| ≤
      K * (dyadicPrimes y).card * log y / log (log y) ^ 6 := by
  obtain ⟨K₁, hK₁, hS₁⟩ := spare_slot_one_le hR
  obtain ⟨KP, hKP, hP₁⟩ := first_positivity hR
  obtain ⟨KT, hKT, hT₁⟩ := tail_region₁
  refine ⟨2 * KP + 2 * K₁ + 2 * KT, by positivity, ?_⟩
  filter_upwards [hS₁, hP₁, hT₁, eventually_region₁_le, eventually_dyadicPrimes,
    eventually_scales 0] with y h₁ hp₁ ht₁ hreg₁ hp hsc
  obtain ⟨hy3, hT6, -, hX, -, -, -, hT7⟩ := hsc
  have hL : 1 ≤ log y := hX.trans (div_le_self (log_nonneg (by linarith)) hT6)
  have hF2 : ∀ q ∈ region₁ y, 0 ≤ (F q : ℝ) ∧ (F q : ℝ) ≤ 2 * log y := fun q hq =>
    ⟨Nat.cast_nonneg _, (F_le_two_mul_log (hreg₁ q hq).1.ne_zero).trans
      (by linarith [log_le_log (by exact_mod_cast (hreg₁ q hq).1.pos) (hreg₁ q hq).2])⟩
  have hN0 : 0 ≤ ((dyadicPrimes y).card : ℝ) := Nat.cast_nonneg _
  -- the per-prime inequality `0 ≤ F n - ∑_{region₁, q ∣ n} F q ≤ 2 (log 2y - ∑ log q)`
  have hpF : ∀ p ∈ dyadicPrimes y,
      0 ≤ (F p : ℝ) - ∑ q ∈ region₁ y with q ∣ p - 1, (F q : ℝ) ∧
        (F p : ℝ) - ∑ q ∈ region₁ y with q ∣ p - 1, (F q : ℝ) ≤
          2 * (log (2 * y) - ∑ q ∈ region₁ y with q ∣ p - 1, log (q : ℝ)) := by
    intro p hp'
    obtain ⟨hFp, hn, hℓp, hA, -⟩ := hp p hp'
    rw [hFp]
    exact F_sub_sum_le hn hA hℓp
  have hsF := Finset.sum_le_sum fun p hp' => (hpF p hp').2
  have hsF0 := Finset.sum_nonneg fun p hp' => (hpF p hp').1
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsF hsF0
  -- the spare-slot statistic with `B q = F q / 2L` and the tail of `B(y)`
  have s₁ := h₁ (fun q => (F q : ℝ)) (2 * log y) (by linarith) fun q hq => by
    rw [abs_of_nonneg (hF2 q hq).1]; exact (hF2 q hq).2
  have t₁ := ht₁ (fun q => (F q : ℝ) / q) 2 (by norm_num) fun q hq _ =>
    ⟨by positivity, by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (F_le_two_mul_log hq.ne_zero) (Nat.cast_nonneg _)⟩
  beta_reduce at s₁ t₁
  have e₁ : K₁ * (2 * log y) * (dyadicPrimes y).card / log (log y) ^ 7 ≤
      2 * K₁ * ((dyadicPrimes y).card * log y / log (log y) ^ 6) := by
    have := mul_le_mul_of_nonneg_left hT7
      (by positivity : 0 ≤ 2 * K₁ * ((dyadicPrimes y).card * log y))
    calc _ = 2 * K₁ * ((dyadicPrimes y).card * log y) * (1 / log (log y) ^ 7) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have e₂ : KP * (dyadicPrimes y).card * log y / log (log y) ^ 6 =
      KP * ((dyadicPrimes y).card * log y / log (log y) ^ 6) := by ring
  have e₃ := mul_le_mul_of_nonneg_left t₁.2 hN0
  have e₃' : ((dyadicPrimes y).card : ℝ) * (2 * (KT * log y / log (log y) ^ 6)) =
      2 * KT * ((dyadicPrimes y).card * log y / log (log y) ^ 6) := by ring
  have e₄ := mul_nonneg hN0 t₁.1
  have e₅ : (2 * KP + 2 * K₁ + 2 * KT) * (dyadicPrimes y).card * log y / log (log y) ^ 6 =
      (2 * KP + 2 * K₁ + 2 * KT) * ((dyadicPrimes y).card * log y / log (log y) ^ 6) := by
    ring
  have e₆ := mul_nonneg hKP (by positivity : (0 : ℝ) ≤
    (dyadicPrimes y).card * log y / log (log y) ^ 6)
  have e₇ := mul_nonneg hKT (by positivity : (0 : ℝ) ≤
    (dyadicPrimes y).card * log y / log (log y) ^ 6)
  rw [e₂] at hp₁
  unfold harmonicF
  rw [e₅, abs_le]
  constructor
  · linarith only [hsF0, (abs_le.1 s₁).1, e₁, e₃, e₃', e₆]
  · linarith only [hsF, hp₁, (abs_le.1 s₁).2, e₁, e₄, e₇]

/-- The second dyadic moment: `|∑_p F(p)² - Π (C(y) + D(y))| ≪ Π L² T⁻⁶`. -/
private lemma second_moment (hR : RectangleInput) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ y : ℝ in atTop,
    |∑ p ∈ dyadicPrimes y, (F p : ℝ) ^ 2 -
        (dyadicPrimes y).card * (harmonicFSq y + harmonicFPair y)| ≤
      K * (dyadicPrimes y).card * log y ^ 2 / log (log y) ^ 6 := by
  obtain ⟨K₁, hK₁, hS₁⟩ := spare_slot_one_le hR
  obtain ⟨K₂, hK₂, hS₂⟩ := spare_slot_two_le hR
  obtain ⟨KP, hKP, hP₁⟩ := first_positivity hR
  obtain ⟨KQ, hKQ, hP₂⟩ := second_positivity hR
  obtain ⟨KT, hKT, hT₁⟩ := tail_region₁
  obtain ⟨KD, hKD, hT₂⟩ := tail_region₂
  refine ⟨16 * KP + 4 * KQ + 4 * K₁ + 4 * K₂ + 4 * KT + KD, by positivity, ?_⟩
  filter_upwards [hS₁, hS₂, hP₁, hP₂, hT₁, hT₂, eventually_region₁_le, mem_region₂,
    eventually_dyadicPrimes, eventually_scales 0]
    with y h₁ h₂ hp₁ hp₂ ht₁ ht₂ hreg₁ hreg₂ hp hsc
  obtain ⟨hy3, hT6, -, hX, -, -, -, hT7⟩ := hsc
  have hL : 1 ≤ log y := hX.trans (div_le_self (log_nonneg (by linarith)) hT6)
  have hF2 : ∀ q ∈ region₁ y, 0 ≤ (F q : ℝ) ∧ (F q : ℝ) ≤ 2 * log y := fun q hq =>
    ⟨Nat.cast_nonneg _, (F_le_two_mul_log (hreg₁ q hq).1.ne_zero).trans
      (by linarith [log_le_log (by exact_mod_cast (hreg₁ q hq).1.pos) (hreg₁ q hq).2])⟩
  have hN0 : 0 ≤ ((dyadicPrimes y).card : ℝ) := Nat.cast_nonneg _
  have hZ₁ : 0 ≤ ((dyadicPrimes y).card : ℝ) * log y / log (log y) ^ 6 := by positivity
  have hZ₂ : 0 ≤ ((dyadicPrimes y).card : ℝ) * log y ^ 2 / log (log y) ^ 6 := by positivity
  have hl2 : log (2 * y) = log 2 + log y := log_mul (by norm_num) (by linarith)
  have hl2' : log 2 < 1 := lt_trans log_two_lt_d9 (by norm_num)
  have hℓ : log (2 * y) ≤ 2 * log y := by linarith
  -- the per-prime inequalities
  have hpF : ∀ p ∈ dyadicPrimes y,
      0 ≤ log (2 * y) - ∑ q ∈ region₁ y with q ∣ p - 1, log (q : ℝ) := by
    intro p hp'
    obtain ⟨hFp, hn, hℓp, hA, -⟩ := hp p hp'
    have := F_sub_sum_le hn hA hℓp
    linarith
  have hpF2 : ∀ p ∈ dyadicPrimes y,
      0 ≤ (F p : ℝ) ^ 2 - ∑ q ∈ region₁ y with q ∣ p - 1, (F q : ℝ) ^ 2 -
          ∑ Q ∈ region₂ y with Q.1 * Q.2 ∣ p - 1, (F Q.1 : ℝ) * F Q.2 ∧
        (F p : ℝ) ^ 2 - ∑ q ∈ region₁ y with q ∣ p - 1, (F q : ℝ) ^ 2 -
            ∑ Q ∈ region₂ y with Q.1 * Q.2 ∣ p - 1, (F Q.1 : ℝ) * F Q.2 ≤
          4 * (2 * log (2 * y) * (log (2 * y) - ∑ q ∈ region₁ y with q ∣ p - 1, log (q : ℝ)) +
            (log (2 * y) ^ 2 - ∑ q ∈ region₁ y with q ∣ p - 1, log (q : ℝ) ^ 2 -
              ∑ Q ∈ region₂ y with Q.1 * Q.2 ∣ p - 1, log (Q.1 : ℝ) * log (Q.2 : ℝ))) := by
    intro p hp'
    obtain ⟨hFp, hn, hℓp, hA, hRA⟩ := hp p hp'
    rw [hFp]
    exact sq_sub_sum_le hn hA hRA hℓp
  have hsW := Finset.sum_nonneg hpF
  have hsF2 := Finset.sum_le_sum fun p hp' => (hpF2 p hp').2
  have hsF20 := Finset.sum_nonneg fun p hp' => (hpF2 p hp').1
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul] at hsW hsF2 hsF20
  -- `ℓ (Π ℓ - ∑∑ log q) ≤ 2 L · KP Z₁`
  have hW := mul_le_mul hℓ hp₁ hsW (by linarith)
  -- the spare-slot statistics and the tails of `C(y)` and `D(y)`
  have s₂ := h₁ (fun q => (F q : ℝ) ^ 2) (4 * log y ^ 2) (by positivity) fun q hq => by
    rw [abs_of_nonneg (by positivity)]
    calc (F q : ℝ) ^ 2 ≤ (2 * log y) ^ 2 := pow_le_pow_left₀ (hF2 q hq).1 (hF2 q hq).2 2
      _ = 4 * log y ^ 2 := by ring
  have s₃ := h₂ (fun q r => (F q : ℝ) * F r) (4 * log y ^ 2) (by positivity) fun Q hQ => by
    obtain ⟨hQ1, hQ2, -⟩ := hreg₂ Q hQ
    rw [abs_of_nonneg (mul_nonneg (hF2 _ hQ1).1 (hF2 _ hQ2).1)]
    calc (F Q.1 : ℝ) * F Q.2 ≤ (2 * log y) * (2 * log y) :=
          mul_le_mul (hF2 _ hQ1).2 (hF2 _ hQ2).2 (hF2 _ hQ2).1 (by linarith)
      _ = 4 * log y ^ 2 := by ring
  have t₂ := ht₁ (fun q => (F q : ℝ) ^ 2 / q) (4 * log y) (by linarith) fun q hq hqy =>
    ⟨by positivity, by
      have h1 := F_le_two_mul_log hq.ne_zero
      have h2 : log (q : ℝ) ≤ log y := log_le_log (by exact_mod_cast hq.pos) hqy
      have h3 := log_natCast_nonneg q
      rw [mul_div_assoc', div_le_div_iff_of_pos_right (by exact_mod_cast hq.pos)]
      calc (F q : ℝ) ^ 2 ≤ (2 * log q) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
        _ = 4 * log q * log q := by ring
        _ ≤ 4 * log y * log q := mul_le_mul_of_nonneg_right (by linarith) h3⟩
  beta_reduce at s₂ s₃ t₂
  have f₁ : K₁ * (4 * log y ^ 2) * (dyadicPrimes y).card / log (log y) ^ 7 ≤
      4 * K₁ * ((dyadicPrimes y).card * log y ^ 2 / log (log y) ^ 6) := by
    have := mul_le_mul_of_nonneg_left hT7
      (by positivity : 0 ≤ 4 * K₁ * ((dyadicPrimes y).card * log y ^ 2))
    calc _ = 4 * K₁ * ((dyadicPrimes y).card * log y ^ 2) * (1 / log (log y) ^ 7) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have f₂ : K₂ * (4 * log y ^ 2) * (dyadicPrimes y).card / log (log y) ^ 7 ≤
      4 * K₂ * ((dyadicPrimes y).card * log y ^ 2 / log (log y) ^ 6) := by
    have := mul_le_mul_of_nonneg_left hT7
      (by positivity : 0 ≤ 4 * K₂ * ((dyadicPrimes y).card * log y ^ 2))
    calc _ = 4 * K₂ * ((dyadicPrimes y).card * log y ^ 2) * (1 / log (log y) ^ 7) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have f₃ : 2 * log y * (KP * (dyadicPrimes y).card * log y / log (log y) ^ 6) =
      2 * KP * ((dyadicPrimes y).card * log y ^ 2 / log (log y) ^ 6) := by ring
  have f₄ : KQ * (dyadicPrimes y).card * log y ^ 2 / log (log y) ^ 6 =
      KQ * ((dyadicPrimes y).card * log y ^ 2 / log (log y) ^ 6) := by ring
  have f₅ := mul_le_mul_of_nonneg_left t₂.2 hN0
  have f₅' : ((dyadicPrimes y).card : ℝ) * (4 * log y * (KT * log y / log (log y) ^ 6)) =
      4 * KT * ((dyadicPrimes y).card * log y ^ 2 / log (log y) ^ 6) := by ring
  have f₆ := mul_le_mul_of_nonneg_left ht₂.2 hN0
  have f₆' : ((dyadicPrimes y).card : ℝ) * (KD * log y ^ 2 / log (log y) ^ 6) =
      KD * ((dyadicPrimes y).card * log y ^ 2 / log (log y) ^ 6) := by ring
  have f₇ := mul_nonneg hN0 t₂.1
  have f₈ := mul_nonneg hN0 ht₂.1
  have f₉ : (16 * KP + 4 * KQ + 4 * K₁ + 4 * K₂ + 4 * KT + KD) * (dyadicPrimes y).card *
      log y ^ 2 / log (log y) ^ 6 = (16 * KP + 4 * KQ + 4 * K₁ + 4 * K₂ + 4 * KT + KD) *
        ((dyadicPrimes y).card * log y ^ 2 / log (log y) ^ 6) := by ring
  have g₁ := mul_nonneg hKP hZ₂
  have g₂ := mul_nonneg hKQ hZ₂
  have g₃ := mul_nonneg hKT hZ₂
  have g₄ := mul_nonneg hKD hZ₂
  rw [f₄] at hp₂
  unfold harmonicFSq
  rw [f₉, abs_le]
  constructor
  · linarith only [hsF20, (abs_le.1 s₂).1, (abs_le.1 s₃).1, f₁, f₂, f₅, f₅', f₆, f₆',
      g₁, g₂, g₃, g₄]
  · linarith only [hsF2, hW, f₃, hp₂, (abs_le.1 s₂).2, (abs_le.1 s₃).2, f₁, f₂, f₇, f₈,
      g₁, g₂, g₃, g₄]

/-- Under `RectangleInput`, the dyadic prime moments of `F` match the harmonic
sums: `∑_{x < p ≤ 2x} F p = Π_x (B(x) + O(L T⁻⁶))` and
`∑_{x < p ≤ 2x} F(p)² = Π_x (C(x) + D(x) + O(L² T⁻⁶))`. -/
theorem dyadic_moments (hR : RectangleInput) : ∃ K : ℝ, ∀ᶠ y : ℝ in Filter.atTop,
    |∑ p ∈ dyadicPrimes y, (F p : ℝ) - (dyadicPrimes y).card * harmonicF y| ≤
        K * (dyadicPrimes y).card * Real.log y / Real.log (Real.log y) ^ 6 ∧
      |∑ p ∈ dyadicPrimes y, (F p : ℝ) ^ 2 -
          (dyadicPrimes y).card * (harmonicFSq y + harmonicFPair y)| ≤
        K * (dyadicPrimes y).card * Real.log y ^ 2 / Real.log (Real.log y) ^ 6 := by
  obtain ⟨K₁, hK₁, h₁⟩ := first_moment hR
  obtain ⟨K₂, hK₂, h₂⟩ := second_moment hR
  refine ⟨K₁ + K₂, ?_⟩
  filter_upwards [h₁, h₂, eventually_scales 0] with y h₁ h₂ hsc
  obtain ⟨hy3, hT6, -⟩ := hsc
  have hL : 0 ≤ log y := log_nonneg (by linarith)
  have hZ₁ : 0 ≤ ((dyadicPrimes y).card : ℝ) * log y / log (log y) ^ 6 := by positivity
  have hZ₂ : 0 ≤ ((dyadicPrimes y).card : ℝ) * log y ^ 2 / log (log y) ^ 6 := by positivity
  constructor
  · calc _ ≤ _ := h₁
      _ ≤ (K₁ + K₂) * (dyadicPrimes y).card * log y / log (log y) ^ 6 := by
        have := mul_nonneg hK₂ hZ₁
        have e : (K₁ + K₂) * (dyadicPrimes y).card * log y / log (log y) ^ 6 =
            K₁ * (dyadicPrimes y).card * log y / log (log y) ^ 6 +
              K₂ * ((dyadicPrimes y).card * log y / log (log y) ^ 6) := by ring
        linarith
  · calc _ ≤ _ := h₂
      _ ≤ (K₁ + K₂) * (dyadicPrimes y).card * log y ^ 2 / log (log y) ^ 6 := by
        have := mul_nonneg hK₁ hZ₂
        have e : (K₁ + K₂) * (dyadicPrimes y).card * log y ^ 2 / log (log y) ^ 6 =
            K₁ * ((dyadicPrimes y).card * log y ^ 2 / log (log y) ^ 6) +
              K₂ * (dyadicPrimes y).card * log y ^ 2 / log (log y) ^ 6 := by ring
        linarith

end Erdos408
