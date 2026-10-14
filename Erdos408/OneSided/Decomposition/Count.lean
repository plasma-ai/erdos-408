import Erdos408.OneSided.Analysis.Divisor
import Erdos408.OneSided.Setup

/-!
# Counting the solutions of the two equations

The absolute sizes of the two squares at fixed label products `a, b ≍ Y`
(PD Lemma 1.2 and `mem:unshared-collisions`).

* The raw equations `mn - 1 = ah`, `rs - 1 = bh` have at most
  `∑_{h ≤ 4X/Y} τ(1 + ah) τ(1 + bh)` solutions, which PD (3.9) bounds.
* The near-solutions `|bmn - ars| ≤ 5Y` number at most `11 ∑_{k ≤ M} τ(k)²`: grouping by
  `k = mn` and `l = rs`, each `k` has at most `10Y/a + 1` partners `l`, and conversely.
-/

namespace Erdos408.OneSided

open Finset

/-- The pairs `(m, n)` with `mn = N ≠ 0` number at most `τ(N)`. -/
theorem sum_sum_ite_mul_eq_le (A B : Finset ℕ) {N : ℕ} (hN : N ≠ 0) :
    ∑ m ∈ A, ∑ n ∈ B, (if m * n = N then (1 : ℝ) else 0) ≤ N.divisors.card := by
  -- for each `m`, at most one `n`, and only if `m ∣ N`
  have hm : ∀ m, ∑ n ∈ B, (if m * n = N then (1 : ℝ) else 0) ≤ if m ∣ N then 1 else 0 := by
    intro m
    rw [sum_boole]
    split_ifs with hdvd
    · have hcard : #{n ∈ B | m * n = N} ≤ 1 := by
        refine card_le_one.2 fun n hn n' hn' => ?_
        rw [mem_filter] at hn hn'
        have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => hN (by rw [← hn.2, h0, zero_mul])
        exact Nat.eq_of_mul_eq_mul_left hm0 (hn.2.trans hn'.2.symm)
      exact_mod_cast hcard
    · rw [Nat.cast_nonpos, card_eq_zero, filter_eq_empty_iff]
      exact fun n _ hmn => hdvd ⟨n, hmn.symm⟩
  calc ∑ m ∈ A, ∑ n ∈ B, (if m * n = N then (1 : ℝ) else 0)
      ≤ ∑ m ∈ A, (if m ∣ N then (1 : ℝ) else 0) := sum_le_sum fun m _ => hm m
    _ = #{m ∈ A | m ∣ N} := by rw [sum_boole]
    _ ≤ N.divisors.card := by
        refine Nat.cast_le.2 (card_le_card fun m hm => ?_)
        rw [mem_filter] at hm
        exact Nat.mem_divisors.2 ⟨hm.2, hN⟩

/-- Grouping by the product: `∑_{m, n} G(mn) ≤ ∑_{k ≤ M} τ(k) G(k)` for `G ≥ 0`, when every
product lies in `[1, M]`. -/
theorem sum_sum_mul_le (A B : Finset ℕ) {M : ℕ}
    (hAB : ∀ m ∈ A, ∀ n ∈ B, 1 ≤ m * n ∧ m * n ≤ M) {G : ℕ → ℝ} (hG : ∀ k, 0 ≤ G k) :
    ∑ m ∈ A, ∑ n ∈ B, G (m * n) ≤ ∑ k ∈ Icc 1 M, (k.divisors.card : ℝ) * G k := by
  have hsplit : ∀ m ∈ A, ∀ n ∈ B,
      G (m * n) = ∑ k ∈ Icc 1 M, (if m * n = k then (1 : ℝ) else 0) * G k := by
    intro m hm n hn
    simp_rw [ite_mul, one_mul, zero_mul]
    rw [sum_ite_eq, ite_eq_left (mem_Icc.2 (hAB m hm n hn))]
  calc ∑ m ∈ A, ∑ n ∈ B, G (m * n)
      = ∑ k ∈ Icc 1 M, (∑ m ∈ A, ∑ n ∈ B, (if m * n = k then (1 : ℝ) else 0)) * G k := by
        rw [sum_congr rfl fun m hm => sum_congr rfl fun n hn => hsplit m hm n hn]
        simp_rw [Finset.sum_mul]
        exact (sum_congr rfl fun m _ => sum_comm).trans sum_comm
    _ ≤ ∑ k ∈ Icc 1 M, (k.divisors.card : ℝ) * G k := by
        refine sum_le_sum fun k hk => mul_le_mul_of_nonneg_right ?_ (hG k)
        exact sum_sum_ite_mul_eq_le A B (by linarith [(mem_Icc.1 hk).1])

/-- The `l` with `|c - a l| ≤ w` number at most `2w/a + 1`. -/
theorem card_filter_abs_sub_le (s : Finset ℕ) (c : ℝ) {a w : ℝ} (ha : 0 < a) (hw : 0 ≤ w) :
    (#{l ∈ s | |c - a * ((l : ℕ) : ℝ)| ≤ w} : ℝ) ≤ 2 * w / a + 1 := by
  set T := {l ∈ s | |c - a * ((l : ℕ) : ℝ)| ≤ w}
  rcases T.eq_empty_or_nonempty with hT | hT
  · rw [hT, card_empty, Nat.cast_zero]
    positivity
  -- every element lies within `2w/a` of the least one
  set l₀ := T.min' hT
  have hl₀ : |c - a * l₀| ≤ w := (mem_filter.1 (T.min'_mem hT)).2
  have hsub : T ⊆ Icc l₀ (l₀ + ⌊2 * w / a⌋₊) := by
    intro l hl
    have hle : l₀ ≤ l := T.min'_le l hl
    have hlw : |c - a * l| ≤ w := (mem_filter.1 hl).2
    refine mem_Icc.2 ⟨hle, ?_⟩
    have hdiff : ((l - l₀ : ℕ) : ℝ) ≤ 2 * w / a := by
      rw [Nat.cast_sub hle, le_div_iff₀ ha]
      have h₁ := (abs_le.1 hl₀).2
      have h₂ := (abs_le.1 hlw).1
      nlinarith
    have := Nat.le_floor hdiff
    omega
  calc (#T : ℝ) ≤ #(Icc l₀ (l₀ + ⌊2 * w / a⌋₊)) := by exact_mod_cast card_le_card hsub
    _ = ⌊2 * w / a⌋₊ + 1 := by
        rw [Nat.card_Icc, show l₀ + ⌊2 * w / a⌋₊ + 1 - l₀ = ⌊2 * w / a⌋₊ + 1 by omega]
        push_cast
        ring
    _ ≤ 2 * w / a + 1 := by
        gcongr
        exact Nat.floor_le (by positivity)

/-- Moving an innermost sum out past two sums. -/
theorem sum_sum_sum_comm {α β γ M : Type*} [AddCommMonoid M] (A : Finset α) (B : Finset β)
    (C : Finset γ) (f : α → β → γ → M) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, f a b c :=
  (sum_congr rfl fun _ _ => sum_comm).trans sum_comm

open scoped Classical in
/-- The raw equations: the quadruples with `mn - 1 = ah`, `rs - 1 = bh` for some `h ≥ 1`
number at most `∑_{h ≤ Z} τ(1 + ah) τ(1 + bh)`, when every such `h` is at most `Z`. -/
theorem sum_ite_exists_le (A B : Finset ℕ) {a b Z : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hZ : ∀ m ∈ A, ∀ n ∈ B, ∀ h, 1 ≤ h → m * n - 1 = a * h → h ≤ Z) :
    ∑ m ∈ A, ∑ n ∈ B, ∑ r ∈ A, ∑ s ∈ B,
        (if ∃ h, 1 ≤ h ∧ m * n - 1 = a * h ∧ r * s - 1 = b * h then (1 : ℝ) else 0) ≤
      ∑ h ∈ Icc 1 Z, ((1 + a * h).divisors.card : ℝ) * (1 + b * h).divisors.card := by
  -- the indicator is at most the sum over `h ≤ Z` of the two indicators
  have hind : ∀ m ∈ A, ∀ n ∈ B, ∀ r s : ℕ,
      (if ∃ h, 1 ≤ h ∧ m * n - 1 = a * h ∧ r * s - 1 = b * h then (1 : ℝ) else 0) ≤
        ∑ h ∈ Icc 1 Z, (if m * n = 1 + a * h then (1 : ℝ) else 0) *
          (if r * s = 1 + b * h then 1 else 0) := by
    intro m hm n hn r s
    split_ifs with hex
    · obtain ⟨h, h1, hmn, hrs⟩ := hex
      have hah : 1 ≤ a * h := Nat.mul_pos ha h1
      have hbh : 1 ≤ b * h := Nat.mul_pos hb h1
      refine le_trans ?_ (single_le_sum (f := fun h => (if m * n = 1 + a * h then (1 : ℝ)
        else 0) * (if r * s = 1 + b * h then 1 else 0)) (fun h _ => by positivity)
        (mem_Icc.2 ⟨h1, hZ m hm n hn h h1 hmn⟩))
      rw [ite_eq_left (by omega), ite_eq_left (by omega), one_mul]
    · exact sum_nonneg fun h _ => by positivity
  calc ∑ m ∈ A, ∑ n ∈ B, ∑ r ∈ A, ∑ s ∈ B,
        (if ∃ h, 1 ≤ h ∧ m * n - 1 = a * h ∧ r * s - 1 = b * h then (1 : ℝ) else 0)
      ≤ ∑ m ∈ A, ∑ n ∈ B, ∑ r ∈ A, ∑ s ∈ B, ∑ h ∈ Icc 1 Z,
          (if m * n = 1 + a * h then (1 : ℝ) else 0) * (if r * s = 1 + b * h then 1 else 0) :=
        sum_le_sum fun m hm => sum_le_sum fun n hn => sum_le_sum fun r _ =>
          sum_le_sum fun s _ => hind m hm n hn r s
    _ = ∑ h ∈ Icc 1 Z, (∑ m ∈ A, ∑ n ∈ B, if m * n = 1 + a * h then (1 : ℝ) else 0) *
          ∑ r ∈ A, ∑ s ∈ B, if r * s = 1 + b * h then (1 : ℝ) else 0 := by
        rw [sum_congr rfl fun m _ => sum_congr rfl fun n _ => sum_sum_sum_comm _ _ _ _,
          sum_sum_sum_comm]
        refine sum_congr rfl fun h _ => ?_
        simp only [Finset.sum_mul]
        simp only [Finset.mul_sum]
    _ ≤ ∑ h ∈ Icc 1 Z, ((1 + a * h).divisors.card : ℝ) * (1 + b * h).divisors.card := by
        refine sum_le_sum fun h _ => mul_le_mul (sum_sum_ite_mul_eq_le A B (by omega))
          (sum_sum_ite_mul_eq_le A B (by omega)) ?_ (Nat.cast_nonneg _)
        exact sum_nonneg fun r _ => sum_nonneg fun s _ => by positivity

/-- The near-solutions: the quadruples with `|b mn - a rs| ≤ 5Y` number at most
`11 ∑_{k ≤ M} τ(k)²`, when `a, b > Y` and every product lies in `[1, M]`. -/
theorem sum_ite_abs_le (A B : Finset ℕ) {M : ℕ}
    (hAB : ∀ m ∈ A, ∀ n ∈ B, 1 ≤ m * n ∧ m * n ≤ M) {a b Y : ℝ} (hY : 0 < Y) (ha : Y < a)
    (hb : Y < b) :
    ∑ m ∈ A, ∑ n ∈ B, ∑ r ∈ A, ∑ s ∈ B,
        (if |b * ((m * n : ℕ) : ℝ) - a * ((r * s : ℕ) : ℝ)| ≤ 5 * Y then (1 : ℝ) else 0) ≤
      11 * ∑ k ∈ Icc 1 M, (k.divisors.card : ℝ) ^ 2 := by
  set g : ℕ → ℕ → ℝ := fun k l => if |b * (k : ℝ) - a * (l : ℝ)| ≤ 5 * Y then 1 else 0
  set τ : ℕ → ℝ := fun k => (k.divisors.card : ℝ)
  have hg : ∀ k l, 0 ≤ g k l := fun k l => by simp only [g]; split_ifs <;> norm_num
  -- each `k` has at most `11` partners `l`, and conversely
  have hrow : ∀ k, ∑ l ∈ Icc 1 M, g k l ≤ 11 := by
    intro k
    simp only [g]
    rw [sum_boole]
    refine (card_filter_abs_sub_le _ _ (hY.trans ha) (by linarith)).trans ?_
    rw [div_add_one (by linarith), div_le_iff₀ (by linarith)]
    linarith
  have hcol : ∀ l, ∑ k ∈ Icc 1 M, g k l ≤ 11 := by
    intro l
    simp only [g]
    simp_rw [abs_sub_comm (b * _)]
    rw [sum_boole]
    refine (card_filter_abs_sub_le _ _ (hY.trans hb) (by linarith)).trans ?_
    rw [div_add_one (by linarith), div_le_iff₀ (by linarith)]
    linarith
  calc ∑ m ∈ A, ∑ n ∈ B, ∑ r ∈ A, ∑ s ∈ B, g (m * n) (r * s)
      ≤ ∑ k ∈ Icc 1 M, τ k * ∑ r ∈ A, ∑ s ∈ B, g k (r * s) :=
        sum_sum_mul_le A B hAB (G := fun k => ∑ r ∈ A, ∑ s ∈ B, g k (r * s))
          fun k => sum_nonneg fun r _ => sum_nonneg fun s _ => hg _ _
    _ ≤ ∑ k ∈ Icc 1 M, τ k * ∑ l ∈ Icc 1 M, τ l * g k l :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (sum_sum_mul_le A B hAB (hg k))
          (Nat.cast_nonneg _)
    _ ≤ ∑ k ∈ Icc 1 M, ∑ l ∈ Icc 1 M, (τ k ^ 2 / 2 * g k l + τ l ^ 2 / 2 * g k l) := by
        refine sum_le_sum fun k _ => ?_
        rw [mul_sum]
        refine sum_le_sum fun l _ => ?_
        have := hg k l
        nlinarith [sq_nonneg (τ k - τ l)]
    _ = ∑ k ∈ Icc 1 M, τ k ^ 2 / 2 * ∑ l ∈ Icc 1 M, g k l +
          ∑ l ∈ Icc 1 M, τ l ^ 2 / 2 * ∑ k ∈ Icc 1 M, g k l := by
        simp only [sum_add_distrib]
        congr 1
        · simp only [mul_sum]
        · rw [sum_comm]
          simp only [mul_sum]
    _ ≤ ∑ k ∈ Icc 1 M, τ k ^ 2 / 2 * 11 + ∑ l ∈ Icc 1 M, τ l ^ 2 / 2 * 11 := by
        gcongr with k _ l _
        · exact hrow k
        · exact hcol l
    _ = 11 * ∑ k ∈ Icc 1 M, τ k ^ 2 := by
        rw [← sum_add_distrib, mul_sum]
        exact sum_congr rfl fun k _ => by ring

end Erdos408.OneSided
