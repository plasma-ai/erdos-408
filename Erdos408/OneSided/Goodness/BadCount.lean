module

public import Erdos408.OneSided.Goodness
public import Erdos408.OneSided.Goodness.RootBox

/-!
# Counting bad positions

The counting analogue of PD Lemma 3.2 (`Goodness.lean`), for `eventually_badMass_le`
(`blueprint/one_sided_type_ii.md` §14). Instead of measuring the bad ratios, count the
positions whose root ratio is bad, given an *interval bound*: at most `A (β - α) + E` of the
counted positions have their ratio in any `[α, β] ⊆ [0, 1]` (`RootBox.lean`).

* `card_circleDist_le`: the ratios with `‖n r‖ ≤ δ` lie in `2|n| + 1` intervals of length
  `2δ/|n|`, so there are at most `6Aδ + (2|n| + 1) E` of them.
* `card_lt_sum_ite_le`: Markov's inequality over a weighted family of conditions, with counts
  in place of measures.
* `eventually_card_not_isGood_le`: the positions failing goodness number at most
  `A e^{-L^{a₋}/4} + E N`, where `N = badIntervals` bounds the number of intervals. The main
  term repeats the bookkeeping of `eventually_volume_not_good`.
-/

@[expose] public section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

/-- The interval bound: at most `A (β - α) + E` of the positions of `T` satisfying `Φ` have
their root ratio in `[α, β]`, for every `[α, β] ⊆ [0, 1]`. -/
def IntervalBound (T : Finset (ℕ × ℕ)) (Φ : ℕ × ℕ → Prop) [DecidablePred Φ] (A E : ℝ) :
    Prop :=
  ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 1 →
    (#{P ∈ T | Φ P ∧ α ≤ rootRatio P ∧ rootRatio P ≤ β} : ℝ) ≤ A * (β - α) + E

/-- For a nonzero integer `n`, the positions with `‖n r‖ ≤ δ` number at most
`6Aδ + (2|n| + 1) E`: their ratios lie within `δ/|n|` of one of the `2|n| + 1` points `k/n`,
`|k| ≤ |n|`. -/
theorem card_circleDist_le {T : Finset (ℕ × ℕ)} (hT : ∀ P ∈ T, 0 < P.1)
    {Φ : ℕ × ℕ → Prop} [DecidablePred Φ] {A E : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hI : IntervalBound T Φ A E) {n : ℤ} (hn : n ≠ 0) {δ : ℝ} (hδ : 0 ≤ δ) :
    (#{P ∈ T | Φ P ∧ circleDist (n * rootRatio P) ≤ δ} : ℝ) ≤
      6 * A * δ + (2 * |(n : ℝ)| + 1) * E := by
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn
  have hn0 : (n : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn
  set w := δ / |(n : ℝ)|
  have hw : 0 ≤ w := by positivity
  set lo : ℤ → ℝ := fun k => max 0 ((k : ℝ) / n - w)
  set hi : ℤ → ℝ := fun k => min 1 ((k : ℝ) / n + w)
  -- each such ratio lies within `δ/|n|` of `k/n` with `k = round (n r)`
  have hsub : {P ∈ T | Φ P ∧ circleDist (n * rootRatio P) ≤ δ} ⊆
      (Icc (-|n|) |n|).biUnion fun k => {P ∈ T | Φ P ∧ lo k ≤ rootRatio P ∧
        rootRatio P ≤ hi k} := by
    intro P hP
    rw [mem_filter] at hP
    obtain ⟨hPT, hΦ, hr⟩ := hP
    set r := rootRatio P
    have hr0 : 0 ≤ r := rootRatio_nonneg P
    have hr1 : r < 1 := rootRatio_lt_one (hT P hPT)
    unfold circleDist at hr
    have hk := abs_sub_round ((n : ℝ) * r)
    have hnr : |(n : ℝ) * r| ≤ |(n : ℝ)| := by
      rw [abs_mul, abs_of_nonneg hr0]
      exact mul_le_of_le_one_right (abs_nonneg _) hr1.le
    -- `|k| ≤ |n r| + 1/2 < |n| + 1`
    have hkn : |round ((n : ℝ) * r)| ≤ |n| := by
      have : ((|round ((n : ℝ) * r)| : ℤ) : ℝ) < |n| + 1 := by
        push_cast
        have := abs_sub_abs_le_abs_sub ((round ((n : ℝ) * r) : ℤ) : ℝ) ((n : ℝ) * r)
        rw [abs_sub_comm ((round ((n : ℝ) * r) : ℤ) : ℝ)] at this
        linarith
      exact Int.lt_add_one_iff.1 (by exact_mod_cast this)
    refine mem_biUnion.2 ⟨round ((n : ℝ) * r), mem_Icc.2 (abs_le.1 hkn), ?_⟩
    -- `|r - k/n| = |n r - k| / |n|`
    have hdist : |r - (round ((n : ℝ) * r) : ℝ) / n| ≤ w := by
      rw [show r - (round ((n : ℝ) * r) : ℝ) / n = ((n : ℝ) * r - round ((n : ℝ) * r)) / n by
        field_simp, abs_div]
      exact div_le_div_of_nonneg_right hr (abs_nonneg _)
    rw [abs_le] at hdist
    exact mem_filter.2 ⟨hPT, hΦ, max_le hr0 (by linarith), le_min hr1.le (by linarith)⟩
  -- each interval has length at most `2δ/|n|`
  have hk : ∀ k, (#{P ∈ T | Φ P ∧ lo k ≤ rootRatio P ∧ rootRatio P ≤ hi k} : ℝ) ≤
      A * (2 * w) + E := by
    intro k
    by_cases hlh : lo k ≤ hi k
    · refine (hI (lo k) (hi k) (le_max_left _ _) hlh (min_le_left _ _)).trans ?_
      have : hi k - lo k ≤ 2 * w := by
        have := min_le_right 1 ((k : ℝ) / n + w)
        have := le_max_right 0 ((k : ℝ) / n - w)
        linarith
      gcongr
    · have hempty : {P ∈ T | Φ P ∧ lo k ≤ rootRatio P ∧ rootRatio P ≤ hi k} = ∅ :=
        filter_false_of_mem fun P _ h => hlh (h.2.1.trans h.2.2)
      rw [hempty, card_empty, Nat.cast_zero]
      positivity
  have hcard : ((Icc (-|n|) |n|).card : ℝ) = 2 * |(n : ℝ)| + 1 := by
    have h : ((Icc (-|n|) |n|).card : ℤ) = 2 * |n| + 1 := by
      rw [Int.card_Icc, Int.toNat_of_nonneg (by linarith [abs_nonneg n])]
      ring
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this
    exact this
  calc (#{P ∈ T | Φ P ∧ circleDist (n * rootRatio P) ≤ δ} : ℝ)
      ≤ ∑ k ∈ Icc (-|n|) |n|,
          (#{P ∈ T | Φ P ∧ lo k ≤ rootRatio P ∧ rootRatio P ≤ hi k} : ℝ) := by
        exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _k ∈ Icc (-|n|) |n|, (A * (2 * w) + E) := sum_le_sum fun k _ => hk k
    _ = (2 * |(n : ℝ)| + 1) * (A * (2 * w)) + (2 * |(n : ℝ)| + 1) * E := by
        rw [sum_const, nsmul_eq_mul, hcard]
        ring
    _ ≤ 6 * A * δ + (2 * |(n : ℝ)| + 1) * E := by
        have h3 : (2 * |(n : ℝ)| + 1) * (2 * w) ≤ 6 * δ := by
          simp only [w]
          rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith)]
          nlinarith
        nlinarith

/-- Markov's inequality for counts: the positions at which the conditions `B · t` holding
carry weight more than `θ` number at most `θ⁻¹ ∑_t w_t #{B · t}`. -/
theorem card_lt_sum_ite_le {ι : Type*} (T : Finset (ℕ × ℕ)) (Φ : ℕ × ℕ → Prop)
    [DecidablePred Φ] (s : Finset ι) {w : ι → ℝ} (hw : ∀ t ∈ s, 0 ≤ w t)
    (B : ℕ × ℕ → ι → Prop) [∀ P t, Decidable (B P t)] {θ : ℝ} (hθ : 0 < θ) :
    (#{P ∈ T | Φ P ∧ θ < ∑ t ∈ s, if B P t then w t else 0} : ℝ) ≤
      θ⁻¹ * ∑ t ∈ s, w t * #{P ∈ T | Φ P ∧ B P t} := by
  rw [le_inv_mul_iff₀ hθ]
  have hnn : ∀ P, 0 ≤ ∑ t ∈ s, if B P t then w t else 0 := fun P =>
    sum_nonneg fun t ht => by split_ifs; exacts [hw t ht, le_rfl]
  calc θ * (#{P ∈ T | Φ P ∧ θ < ∑ t ∈ s, if B P t then w t else 0} : ℝ)
      = ∑ _P ∈ {P ∈ T | Φ P ∧ θ < ∑ t ∈ s, if B P t then w t else 0}, θ := by
        rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ P ∈ {P ∈ T | Φ P ∧ θ < ∑ t ∈ s, if B P t then w t else 0},
          ∑ t ∈ s, if B P t then w t else 0 := sum_le_sum fun P hP => (mem_filter.1 hP).2.2.le
    _ ≤ ∑ P ∈ {P ∈ T | Φ P}, ∑ t ∈ s, if B P t then w t else 0 := by
        refine sum_le_sum_of_subset_of_nonneg (fun P hP => ?_) fun P _ _ => hnn P
        rw [mem_filter] at hP ⊢
        exact ⟨hP.1, hP.2.1⟩
    _ = ∑ t ∈ s, w t * #{P ∈ T | Φ P ∧ B P t} := by
        rw [sum_comm]
        refine sum_congr rfl fun t _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul, filter_filter, mul_comm]

/-! ### Bounds on the trial integers -/

/-- `B = exp(2 ∑_i L^{a_i})`, which bounds every product of at most one band prime per group. -/
noncomputable def labelBound (x : ℝ) (d : Data K) : ℝ :=
  Real.exp (2 * ∑ i, Real.log x ^ d.a i)

/-- `B ≥ 1`. -/
theorem one_le_labelBound {x : ℝ} (hL : 0 ≤ Real.log x) (d : Data K) : 1 ≤ labelBound x d :=
  Real.one_le_exp (mul_nonneg zero_le_two (sum_nonneg fun _ _ => Real.rpow_nonneg hL _))

/-- A product of at most one band prime per group is at most `B`. -/
theorem prod_le_labelBound {x : ℝ} (hL : 0 ≤ Real.log x) {d : Data K} {Z : Fin K → ℕ}
    (hZ : ∀ j, Z j = 1 ∨ Z j ∈ band x (d.a j)) : ((∏ j, Z j : ℕ) : ℝ) ≤ labelBound x d := by
  rw [labelBound, mul_sum, Real.exp_sum, Nat.cast_prod]
  refine prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) fun j _ => ?_
  rcases hZ j with h | h
  · rw [h, Nat.cast_one]
    exact Real.one_le_exp (mul_nonneg zero_le_two (Real.rpow_nonneg hL _))
  · exact le_exp_of_mem_band h

/-- The selections number at most `B`. -/
theorem card_selections_le_labelBound {x : ℝ} (hL : 0 ≤ Real.log x) (d : Data K)
    (I : Finset (Fin K)) (i : Fin K) : ((selections x d I i).card : ℝ) ≤ labelBound x d := by
  unfold selections
  rw [Fintype.card_piFinset, Nat.cast_prod, labelBound, mul_sum, Real.exp_sum]
  refine prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) fun j _ => ?_
  split_ifs
  · exact card_band_le _ _
  · rw [card_singleton, Nat.cast_one]
    exact Real.one_le_exp (mul_nonneg zero_le_two (Real.rpow_nonneg hL _))

/-- The inverse threshold `exp(L^{a_i}/4)` is at most `B`. -/
theorem exp_div_four_le_labelBound {x : ℝ} (hL : 0 ≤ Real.log x) (d : Data K) (i : Fin K) :
    (Real.exp (-Real.log x ^ d.a i / 4))⁻¹ ≤ labelBound x d := by
  rw [← Real.exp_neg, labelBound]
  refine Real.exp_le_exp.2 ?_
  have h₁ : Real.log x ^ d.a i ≤ ∑ j, Real.log x ^ d.a j :=
    single_le_sum (fun j _ => Real.rpow_nonneg hL _) (mem_univ i)
  have h₂ : 0 ≤ Real.log x ^ d.a i := Real.rpow_nonneg hL _
  linarith

/-- An omission product is at most the list product. -/
theorem omitProd_le_listProd {J : ℕ} {p : Lists K J} (hp : ∀ i h, p i h ≠ 0)
    (o : Fin K → Fin (J + 1)) : omitProd p o ≤ listProd p := by
  unfold omitProd listProd
  refine prod_le_prod fun i _ => ?_
  exact prod_le_prod_of_subset_of_one_le (erase_subset _ _) fun h _ _ =>
    Nat.one_le_iff_ne_zero.2 (hp i h)

/-- The number of intervals of bad ratios: `M^K n (2 n G + 1)` for test (i), with
`n = ⌊Y^{1/5}⌋`, and `2^K B (M^K B)² (2 G B² + 1)` for test (ii), with `G` the list product. -/
noncomputable def badIntervals (x : ℝ) (d : Data K) (Y : ℝ) {J : ℕ} (p : Lists K J) : ℝ :=
  ((J : ℝ) + 1) ^ K * ⌊Y ^ (1 / 5 : ℝ)⌋₊ * (2 * ⌊Y ^ (1 / 5 : ℝ)⌋₊ * listProd p + 1) +
    2 ^ K * labelBound x d * (((J : ℝ) + 1) ^ K * labelBound x d) ^ 2 *
      (2 * listProd p * labelBound x d ^ 2 + 1)

/-- `L^{a₋} ≥ 8 (K + 2K L^{0.01} + 600)` eventually, since `a₋ > 0.01`. -/
private theorem eventually_rpow_ge_affine' {alo : ℝ} (halo : 1 / 10 < alo) (K : ℕ) :
    ∀ᶠ x : ℝ in atTop, 8 * (K + 2 * K * Real.log x ^ (1 / 100 : ℝ) + 600) ≤
      Real.log x ^ alo := by
  have hu := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp
    Real.tendsto_log_atTop
  filter_upwards [hu.eventually_ge_atTop (8 * (3 * K + 600) + 1),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hL
  set u := Real.log x ^ (1 / 100 : ℝ) with hu_def
  have hx' : 8 * (3 * K + 600) + 1 ≤ u := hx
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  -- `L^{a₋} ≥ L^{0.1} = u^{10} ≥ u^2`
  have h10 : u ^ (10 : ℕ) ≤ Real.log x ^ alo := by
    rw [hu_def, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num; linarith)
  have h2 : u ^ 2 ≤ u ^ (10 : ℕ) := pow_le_pow_right₀ (by linarith) (by norm_num)
  nlinarith

/-! ### The count of bad positions -/

open scoped Classical in
/-- Test (i): the positions failing test (i) number at most `M^K n (6 A Y^{-0.7} + (2nG + 1) E)`:
there are `M^K` omission products `D ≤ G` and `n = ⌊Y^{0.2}⌋` integers `l`. -/
theorem card_not_goodFirst_le {T : Finset (ℕ × ℕ)} (hT : ∀ P ∈ T, 0 < P.1)
    {Φ : ℕ × ℕ → Prop} [DecidablePred Φ] {A E : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hI : IntervalBound T Φ A E) {Y : ℝ} (hY : 0 < Y) (d₀ : ℝ) {J : ℕ} {p : Lists K J}
    (hp : ∀ i h, p i h ≠ 0) :
    (#{P ∈ T | Φ P ∧ ¬ GoodFirst Y d₀ (rootRatio P) p} : ℝ) ≤
      ((J : ℝ) + 1) ^ K * ⌊Y ^ (1 / 5 : ℝ)⌋₊ *
        (6 * A * Y ^ (-(7 / 10 : ℝ)) + (2 * ⌊Y ^ (1 / 5 : ℝ)⌋₊ * listProd p + 1) * E) := by
  set n := ⌊Y ^ (1 / 5 : ℝ)⌋₊
  set δ := Y ^ (-(7 / 10 : ℝ))
  have hD : ∀ o, omitProd p o ≠ 0 := fun o =>
    prod_ne_zero_iff.2 fun i _ => prod_ne_zero_iff.2 fun h _ => hp i h
  -- a failure is a pair `(D, l)` with `‖l D r‖ ≤ Y^{-0.7}`
  have hsub : {P ∈ T | Φ P ∧ ¬ GoodFirst Y d₀ (rootRatio P) p} ⊆
      (univ : Finset (Fin K → Fin (J + 1))).biUnion fun o => (Icc 1 n).biUnion fun l =>
        {P ∈ T | Φ P ∧ circleDist ((((l * omitProd p o : ℕ) : ℤ) : ℝ) * rootRatio P) ≤ δ} := by
    intro P hP
    rw [mem_filter] at hP
    obtain ⟨hPT, hΦ, hbad⟩ := hP
    unfold GoodFirst at hbad
    push Not at hbad
    obtain ⟨o, -, -, l, hl1, hlY, hl⟩ := hbad
    refine mem_biUnion.2 ⟨o, mem_univ o, mem_biUnion.2 ⟨l, mem_Icc.2 ⟨hl1, Nat.le_floor hlY⟩,
      mem_filter.2 ⟨hPT, hΦ, ?_⟩⟩⟩
    push_cast
    exact hl
  have hδ : 0 ≤ δ := Real.rpow_nonneg hY.le _
  have hn : (n : ℝ) ≤ Y ^ (1 / 5 : ℝ) := Nat.floor_le (by positivity)
  -- each pair costs `6 A δ + (2 l D + 1) E ≤ 6 A δ + (2 n G + 1) E`
  have hpair : ∀ o, ∀ l ∈ Icc 1 n,
      (#{P ∈ T | Φ P ∧ circleDist ((((l * omitProd p o : ℕ) : ℤ) : ℝ) * rootRatio P) ≤ δ} : ℝ) ≤
        6 * A * δ + (2 * n * listProd p + 1) * E := by
    intro o l hl
    have hl' := mem_Icc.1 hl
    have hN : ((l * omitProd p o : ℕ) : ℤ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.mul_ne_zero (by omega) (hD o))
    refine (card_circleDist_le hT hA hE hI hN hδ).trans ?_
    have habs : |((((l * omitProd p o : ℕ) : ℤ)) : ℝ)| ≤ n * listProd p := by
      rw [Int.cast_natCast, Nat.abs_cast, Nat.cast_mul]
      have h₁ : (l : ℝ) ≤ n := by exact_mod_cast hl'.2
      have h₂ : (omitProd p o : ℝ) ≤ listProd p := by exact_mod_cast omitProd_le_listProd hp o
      gcongr
    have h2 : (2 * |((((l * omitProd p o : ℕ) : ℤ)) : ℝ)| + 1) * E ≤
        (2 * n * listProd p + 1) * E := mul_le_mul_of_nonneg_right (by linarith) hE
    linarith
  calc (#{P ∈ T | Φ P ∧ ¬ GoodFirst Y d₀ (rootRatio P) p} : ℝ)
      ≤ ∑ o : Fin K → Fin (J + 1), ∑ l ∈ Icc 1 n,
          (#{P ∈ T | Φ P ∧ circleDist ((((l * omitProd p o : ℕ) : ℤ) : ℝ) * rootRatio P) ≤
            δ} : ℝ) := by
        refine (Nat.cast_le.2 ((card_le_card hsub).trans card_biUnion_le)).trans ?_
        push_cast
        exact sum_le_sum fun o _ => by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _o : Fin K → Fin (J + 1), ∑ _l ∈ Icc 1 n,
          (6 * A * δ + (2 * n * listProd p + 1) * E) :=
        sum_le_sum fun o _ => sum_le_sum fun l hl => hpair o l hl
    _ = _ := by
        rw [sum_const, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        ring

open scoped Classical in
/-- Test (ii) at one nonempty `I`, with `i_* = max I`: by Markov's inequality over the fresh
draws at the threshold `θ = exp(-L^{a_{i_*}}/4)`, the failing positions number at most
`θ⁻¹ #pairs (6 A δ + (2 G B² + 1) E)` with `δ = 100 e^{-L^{a_{i_*}}}`: the trial integers
`N = (D Z - D' Z') ∏ T` satisfy `|N| ≤ G B²`. -/
theorem card_not_goodSecond_at_le {T : Finset (ℕ × ℕ)} (hT : ∀ P ∈ T, 0 < P.1)
    {Φ : ℕ × ℕ → Prop} [DecidablePred Φ] {A E : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hI : IntervalBound T Φ A E) {x : ℝ} (hL : 0 ≤ Real.log x) {d : Data K}
    (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) (d₀ : ℝ) {J : ℕ} {p : Lists K J}
    (hp : ∀ i h, p i h ≠ 0) {I : Finset (Fin K)} (hIne : I.Nonempty) :
    (#{P ∈ T | Φ P ∧ ¬ ∑ t ∈ (freshDraws x d I).filter
          (fun t => ¬ Separated x d d₀ I (I.max' hIne) (rootRatio P) p t), freshWeight x d I t ≤
        Real.exp (-Real.log x ^ d.a (I.max' hIne) / 4)} : ℝ) ≤
      (Real.exp (-Real.log x ^ d.a (I.max' hIne) / 4))⁻¹ *
        ((((J : ℝ) + 1) ^ K * (selections x d I (I.max' hIne)).card) ^ 2 *
          (6 * A * (100 * Real.exp (-Real.log x ^ d.a (I.max' hIne))) +
            (2 * listProd p * labelBound x d ^ 2 + 1) * E)) := by
  set i := I.max' hIne
  set θ := Real.exp (-Real.log x ^ d.a i / 4)
  set δ := 100 * Real.exp (-Real.log x ^ d.a i)
  set S := selections x d I i
  set Bd := labelBound x d
  set G := listProd p
  set N : (Fin K → Fin (J + 1)) × (Fin K → ℕ) → ℕ := fun q => omitProd p q.1 * ∏ j, q.2 j
  set Q := ((univ ×ˢ S) ×ˢ (univ ×ˢ S)).filter fun q => N q.1 ≠ N q.2
  set X := (Q.card : ℝ) * (6 * A * δ + (2 * G * Bd ^ 2 + 1) * E)
  have hδ : 0 ≤ δ := by positivity
  have hB1 := one_le_labelBound hL d
  -- the fresh draws consist of `1`s and band primes
  have hfresh : ∀ t ∈ freshDraws x d I, ∀ j, t j = 1 ∨ t j ∈ band x (d.a j) := by
    intro t ht j
    have htj := Fintype.mem_piFinset.1 ht j
    split_ifs at htj
    · exact Or.inl (mem_singleton.1 htj)
    · exact Or.inr htj
  have hsel : ∀ Z ∈ S, ∀ j, Z j = 1 ∨ Z j ∈ band x (d.a j) := by
    intro Z hZ j
    have hZj := Fintype.mem_piFinset.1 hZ j
    split_ifs at hZj
    · exact Or.inr hZj
    · exact Or.inl (mem_singleton.1 hZj)
  -- for one fresh draw, a failure is a pair of distinct trial integers at distance `< δ`
  have hsep : ∀ t ∈ freshDraws x d I,
      (#{P ∈ T | Φ P ∧ ¬ Separated x d d₀ I i (rootRatio P) p t} : ℝ) ≤ X := by
    intro t ht
    have hTt : ∏ j, t j ≠ 0 := prod_ne_zero_iff.2 fun j _ => by
      rcases hfresh t ht j with h | h
      · rw [h]; exact one_ne_zero
      · exact (TypeII.band_prime h).ne_zero
    set n : (Fin K → Fin (J + 1)) × (Fin K → ℕ) → (Fin K → Fin (J + 1)) × (Fin K → ℕ) → ℤ :=
      fun q q' => ((N q : ℤ) - N q') * ∏ j, (t j : ℤ)
    have hsub : {P ∈ T | Φ P ∧ ¬ Separated x d d₀ I i (rootRatio P) p t} ⊆
        Q.biUnion fun q => {P ∈ T | Φ P ∧ circleDist ((n q.1 q.2 : ℝ) * rootRatio P) ≤ δ} := by
      intro P hP
      rw [mem_filter] at hP
      obtain ⟨hPT, hΦ, hbad⟩ := hP
      unfold Separated at hbad
      push Not at hbad
      obtain ⟨o, o', Z, hZ, Z', hZ', -, -, -, -, hne, hlt⟩ := hbad
      refine mem_biUnion.2 ⟨((o, Z), (o', Z')),
        mem_filter.2 ⟨mem_product.2 ⟨mem_product.2 ⟨mem_univ _, hZ⟩,
          mem_product.2 ⟨mem_univ _, hZ'⟩⟩, hne⟩, mem_filter.2 ⟨hPT, hΦ, ?_⟩⟩
      simp only [n, N]
      push_cast at hlt ⊢
      exact hlt.le
    have hq : ∀ q ∈ Q, (#{P ∈ T | Φ P ∧ circleDist ((n q.1 q.2 : ℝ) * rootRatio P) ≤ δ} : ℝ) ≤
        6 * A * δ + (2 * G * Bd ^ 2 + 1) * E := by
      intro q hq
      obtain ⟨hmem, hne⟩ := mem_filter.1 hq
      rw [mem_product, mem_product, mem_product] at hmem
      have hn0 : n q.1 q.2 ≠ 0 :=
        mul_ne_zero (sub_ne_zero.2 (by exact_mod_cast hne)) (by exact_mod_cast hTt)
      refine (card_circleDist_le hT hA hE hI hn0 hδ).trans ?_
      -- `|N| ≤ max (D Z, D' Z') ∏ T ≤ G B · B`
      have hNle : ∀ q' : (Fin K → Fin (J + 1)) × (Fin K → ℕ), q'.2 ∈ S →
          (N q' : ℝ) ≤ G * Bd := by
        intro q' hq'
        simp only [N]
        push_cast
        have h₁ : (omitProd p q'.1 : ℝ) ≤ G := by exact_mod_cast omitProd_le_listProd hp q'.1
        have h₂ := prod_le_labelBound hL (hsel q'.2 hq')
        push_cast at h₂
        exact mul_le_mul h₁ h₂ (by positivity) (by positivity)
      have hT' := prod_le_labelBound hL (hfresh t ht)
      push_cast at hT'
      have habs : |(n q.1 q.2 : ℝ)| ≤ G * Bd ^ 2 := by
        simp only [n]
        push_cast
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ∏ j, (t j : ℝ))]
        have h₁ := hNle q.1 hmem.1.2
        have h₂ := hNle q.2 hmem.2.2
        have h₃ : |(N q.1 : ℝ) - N q.2| ≤ G * Bd := by
          rw [abs_le]
          constructor <;> linarith [(Nat.cast_nonneg (N q.1) : (0 : ℝ) ≤ _),
            (Nat.cast_nonneg (N q.2) : (0 : ℝ) ≤ _)]
        calc |(N q.1 : ℝ) - N q.2| * ∏ j, (t j : ℝ) ≤ G * Bd * Bd :=
              mul_le_mul h₃ hT' (by positivity) (by positivity)
          _ = G * Bd ^ 2 := by ring
      have h2 : (2 * |(n q.1 q.2 : ℝ)| + 1) * E ≤ (2 * G * Bd ^ 2 + 1) * E :=
        mul_le_mul_of_nonneg_right (by linarith) hE
      linarith
    calc (#{P ∈ T | Φ P ∧ ¬ Separated x d d₀ I i (rootRatio P) p t} : ℝ)
        ≤ ∑ q ∈ Q, (#{P ∈ T | Φ P ∧ circleDist ((n q.1 q.2 : ℝ) * rootRatio P) ≤ δ} : ℝ) := by
          exact_mod_cast (card_le_card hsub).trans card_biUnion_le
      _ ≤ ∑ _q ∈ Q, (6 * A * δ + (2 * G * Bd ^ 2 + 1) * E) := sum_le_sum hq
      _ = X := by rw [sum_const, nsmul_eq_mul]
  -- Markov over the fresh draws, of total weight one
  have hsub : {P ∈ T | Φ P ∧ ¬ ∑ t ∈ (freshDraws x d I).filter
        (fun t => ¬ Separated x d d₀ I i (rootRatio P) p t), freshWeight x d I t ≤ θ} ⊆
      {P ∈ T | Φ P ∧ θ < ∑ t ∈ freshDraws x d I,
        if ¬ Separated x d d₀ I i (rootRatio P) p t then freshWeight x d I t else 0} := by
    intro P hP
    rw [mem_filter] at hP ⊢
    rw [sum_filter, not_le] at hP
    exact hP
  have hX : 0 ≤ X := by positivity
  have hQ : (Q.card : ℝ) ≤ (((J : ℝ) + 1) ^ K * S.card) ^ 2 := by
    have := card_filter_le ((univ ×ˢ S) ×ˢ (univ ×ˢ S)) fun q => N q.1 ≠ N q.2
    rw [card_product, card_product, card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin] at this
    calc (Q.card : ℝ) ≤ (((J + 1) ^ K * S.card * ((J + 1) ^ K * S.card) : ℕ) : ℝ) := by
          exact_mod_cast this
      _ = (((J : ℝ) + 1) ^ K * S.card) ^ 2 := by push_cast; ring
  calc _ ≤ (#{P ∈ T | Φ P ∧ θ < ∑ t ∈ freshDraws x d I,
        if ¬ Separated x d d₀ I i (rootRatio P) p t then freshWeight x d I t else 0} : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ θ⁻¹ * ∑ t ∈ freshDraws x d I, freshWeight x d I t *
          #{P ∈ T | Φ P ∧ ¬ Separated x d d₀ I i (rootRatio P) p t} :=
        card_lt_sum_ite_le T Φ _ (fun t _ => freshWeight_nonneg I hV t) _ (Real.exp_pos _)
    _ ≤ θ⁻¹ * ∑ t ∈ freshDraws x d I, freshWeight x d I t * X := by
        gcongr with t ht
        · exact freshWeight_nonneg I hV t
        · exact hsep t ht
    _ = θ⁻¹ * X := by rw [← sum_mul, sum_freshWeight I hV, one_mul]
    _ ≤ θ⁻¹ * ((((J : ℝ) + 1) ^ K * S.card) ^ 2 * (6 * A * δ + (2 * G * Bd ^ 2 + 1) * E)) := by
        gcongr
        exact mul_le_mul_of_nonneg_right hQ (by positivity)

open scoped Classical in
/-- **Counting PD Lemma 3.2.** Eventually, under an interval bound `A (β - α) + E`, the
positions failing goodness number at most `A e^{-L^{a₋}/4} + E N`, with `N = badIntervals`,
uniformly in the lists, the varying data and the label dyads `Y ≥ exp(L^{a₋})/4`. The main
term is the measure bound of `eventually_volume_not_good`. -/
theorem eventually_card_not_isGood_le {C CX alo ahi g : ℝ} (halo : 1 / 10 < alo)
    (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ∀ Y d₀ : ℝ, Real.exp (Real.log x ^ alo) ≤ 4 * Y →
      ∀ p ∈ lists x d (padCount x), ∀ T : Finset (ℕ × ℕ), (∀ P ∈ T, 0 < P.1) →
      ∀ (Φ : ℕ × ℕ → Prop) [DecidablePred Φ] (A E : ℝ), 0 ≤ A → 0 ≤ E →
        IntervalBound T Φ A E →
        (#{P ∈ T | Φ P ∧ ¬ IsGood x d Y d₀ P p} : ℝ) ≤
          A * Real.exp (-Real.log x ^ alo / 4) + E * badIntervals x d Y p := by
  have hLg := (tendsto_rpow_atTop hg).comp Real.tendsto_log_atTop
  filter_upwards [eventually_harmonicMass_band halo.le, eventually_rpow_ge_affine' halo K,
    hLg.eventually_ge_atTop (32 * K), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with x hVx hlo hgK hL d hd Y d₀ hY4 p hp T hT Φ _ A E hA hE hI
  set u := Real.log x ^ (1 / 100 : ℝ)
  set ε := Real.exp (-Real.log x ^ alo / 4)
  set Bd := labelBound x d
  set G := listProd p
  set n := ⌊Y ^ (1 / 5 : ℝ)⌋₊
  have hL0 : 0 ≤ Real.log x := by linarith
  have hgK' : 32 * (K : ℝ) ≤ Real.log x ^ g := hgK
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hu : 0 ≤ u := by positivity
  have hY : 0 < Y := by linarith [Real.exp_pos (Real.log x ^ alo)]
  have hV : ∀ i, 0 < harmonicMass (band x (d.a i)) := fun i =>
    lt_of_lt_of_le (by norm_num) (hVx _ (hd.window i).1).1
  have hp' : ∀ i h, p i h ≠ 0 := fun i h =>
    (TypeII.band_prime (Fintype.mem_piFinset.1
      (Fintype.mem_piFinset.1 (mem_filter.1 hp).1 i) h)).ne_zero
  have hB1 := one_le_labelBound hL0 d
  -- `M = J + 1 ≤ exp(L^{0.01})`
  have hM : ((padCount x : ℝ) + 1) ^ K ≤ Real.exp (K * u) := by
    rw [Real.exp_nat_mul]
    gcongr
    exact (Real.add_one_le_exp _).trans (Real.exp_le_exp.2 (Nat.floor_le (by positivity)))
  -- split the failures into the two tests, and test (ii) by the set `I`
  have hsub : {P ∈ T | Φ P ∧ ¬ IsGood x d Y d₀ P p} ⊆
      {P ∈ T | Φ P ∧ ¬ GoodFirst Y d₀ (rootRatio P) p} ∪
        univ.biUnion fun I : Finset (Fin K) => {P ∈ T | Φ P ∧ ∃ hI : I.Nonempty,
          ¬ ∑ t ∈ (freshDraws x d I).filter
              (fun t => ¬ Separated x d d₀ I (I.max' hI) (rootRatio P) p t),
            freshWeight x d I t ≤ Real.exp (-Real.log x ^ d.a (I.max' hI) / 4)} := by
    intro P hP
    rw [mem_filter] at hP
    obtain ⟨hPT, hΦ, hbad⟩ := hP
    by_cases h1 : GoodFirst Y d₀ (rootRatio P) p
    · have h2 : ¬ GoodSecond x d d₀ (rootRatio P) p := fun h2 => hbad ⟨h1, h2⟩
      unfold GoodSecond at h2
      push Not at h2
      obtain ⟨I, hI', h⟩ := h2
      exact mem_union_right _ (mem_biUnion.2 ⟨I, mem_univ _,
        mem_filter.2 ⟨hPT, hΦ, hI', not_le.2 h⟩⟩)
    · exact mem_union_left _ (mem_filter.2 ⟨hPT, hΦ, h1⟩)
  -- test (i): the main term is `6 M^K Y^{-1/2} A ≤ ε/2 A`
  have hfirst : (#{P ∈ T | Φ P ∧ ¬ GoodFirst Y d₀ (rootRatio P) p} : ℝ) ≤
      A * (ε / 2) + E * (((padCount x : ℝ) + 1) ^ K * n * (2 * n * G + 1)) := by
    refine (card_not_goodFirst_le hT hA hE hI hY d₀ hp').trans ?_
    have hn : (n : ℝ) ≤ Y ^ (1 / 5 : ℝ) := Nat.floor_le (by positivity)
    have hδY : Y ^ (1 / 5 : ℝ) * Y ^ (-(7 / 10 : ℝ)) = Y ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hY]
      norm_num
    -- `log Y ≥ L^{a₋} - log 4 ≥ L^{a₋} - 3`
    have hlogY : Real.log x ^ alo ≤ 3 + Real.log Y := by
      have h := Real.log_le_log (Real.exp_pos _) hY4
      rw [Real.log_exp, Real.log_mul (by norm_num) hY.ne'] at h
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hYr : Y ^ (-(1 / 2 : ℝ)) ≤ Real.exp ((3 - Real.log x ^ alo) / 2) := by
      rw [Real.rpow_def_of_pos hY]
      exact Real.exp_le_exp.2 (by linarith)
    have h12 : (12 : ℝ) ≤ Real.exp 11 := by linarith [Real.add_one_le_exp (11 : ℝ)]
    have hmain : 6 * ((padCount x : ℝ) + 1) ^ K * Y ^ (-(1 / 2 : ℝ)) ≤ ε / 2 := by
      calc 6 * ((padCount x : ℝ) + 1) ^ K * Y ^ (-(1 / 2 : ℝ))
          ≤ 6 * Real.exp (K * u) * Real.exp ((3 - Real.log x ^ alo) / 2) := by gcongr
        _ ≤ Real.exp 11 * Real.exp (K * u) * Real.exp ((3 - Real.log x ^ alo) / 2) / 2 := by
            rw [le_div_iff₀ two_pos]
            nlinarith [mul_pos (Real.exp_pos (K * u))
              (Real.exp_pos ((3 - Real.log x ^ alo) / 2))]
        _ = Real.exp (11 + K * u + (3 - Real.log x ^ alo) / 2) / 2 := by
            rw [Real.exp_add, Real.exp_add]
        _ ≤ ε / 2 :=
            div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith [mul_nonneg hK hu]))
              zero_le_two
    have hA6 : ((padCount x : ℝ) + 1) ^ K * n * (6 * A * Y ^ (-(7 / 10 : ℝ))) ≤ A * (ε / 2) := by
      calc ((padCount x : ℝ) + 1) ^ K * n * (6 * A * Y ^ (-(7 / 10 : ℝ)))
          ≤ ((padCount x : ℝ) + 1) ^ K * Y ^ (1 / 5 : ℝ) * (6 * A * Y ^ (-(7 / 10 : ℝ))) := by
            gcongr
        _ = A * (6 * ((padCount x : ℝ) + 1) ^ K * Y ^ (-(1 / 2 : ℝ))) := by rw [← hδY]; ring
        _ ≤ A * (ε / 2) := mul_le_mul_of_nonneg_left hmain hA
    nlinarith
  -- test (ii): each nonempty `I` has main term at most `ε / 2^{K+1} A`
  have hsecond : ∀ I : Finset (Fin K), (#{P ∈ T | Φ P ∧ ∃ hI : I.Nonempty,
      ¬ ∑ t ∈ (freshDraws x d I).filter
          (fun t => ¬ Separated x d d₀ I (I.max' hI) (rootRatio P) p t), freshWeight x d I t ≤
        Real.exp (-Real.log x ^ d.a (I.max' hI) / 4)} : ℝ) ≤
      A * (ε / 2 / 2 ^ K) +
        E * (Bd * (((padCount x : ℝ) + 1) ^ K * Bd) ^ 2 * (2 * G * Bd ^ 2 + 1)) := by
    intro I
    by_cases hI' : I.Nonempty
    swap
    · have hempty : {P ∈ T | Φ P ∧ ∃ hI : I.Nonempty,
          ¬ ∑ t ∈ (freshDraws x d I).filter
              (fun t => ¬ Separated x d d₀ I (I.max' hI) (rootRatio P) p t),
            freshWeight x d I t ≤ Real.exp (-Real.log x ^ d.a (I.max' hI) / 4)} = ∅ :=
        filter_false_of_mem fun P _ h => hI' h.2.1
      rw [hempty, card_empty, Nat.cast_zero]
      positivity
    have hsub' : {P ∈ T | Φ P ∧ ∃ hI : I.Nonempty,
        ¬ ∑ t ∈ (freshDraws x d I).filter
            (fun t => ¬ Separated x d d₀ I (I.max' hI) (rootRatio P) p t),
          freshWeight x d I t ≤ Real.exp (-Real.log x ^ d.a (I.max' hI) / 4)} ⊆
        {P ∈ T | Φ P ∧ ¬ ∑ t ∈ (freshDraws x d I).filter
            (fun t => ¬ Separated x d d₀ I (I.max' hI') (rootRatio P) p t),
          freshWeight x d I t ≤ Real.exp (-Real.log x ^ d.a (I.max' hI') / 4)} := by
      intro P hP
      rw [mem_filter] at hP ⊢
      obtain ⟨hPT, hΦ, _, h⟩ := hP
      exact ⟨hPT, hΦ, h⟩
    refine (Nat.cast_le.2 (card_le_card hsub')).trans
      ((card_not_goodSecond_at_le hT hA hE hI hL0 hV d₀ hp' hI').trans ?_)
    set a := d.a (I.max' hI')
    set S := ((selections x d I (I.max' hI')).card : ℝ)
    set θ := Real.exp (-Real.log x ^ a / 4)
    have ha : alo ≤ a := (hd.window _).1
    have hLa : Real.log x ^ alo ≤ Real.log x ^ a := Real.rpow_le_rpow_of_exponent_le hL ha
    have hS := card_selections_le hd hL hI'
    have hSB : S ≤ Bd := card_selections_le_labelBound hL0 d I _
    have hθB : θ⁻¹ ≤ Bd := exp_div_four_le_labelBound hL0 d _
    -- `4K L^{a - g} ≤ L^a / 8`, since `L^g ≥ 32K`
    have hgap : 4 * K * Real.log x ^ (a - g) ≤ Real.log x ^ a / 8 := by
      have h := Real.rpow_add (by linarith : (0 : ℝ) < Real.log x) (a - g) g
      rw [sub_add_cancel] at h
      have : 0 ≤ Real.log x ^ (a - g) := by positivity
      nlinarith
    have hMS : ((padCount x : ℝ) + 1) ^ K * S ≤
        Real.exp (K * u + 2 * K * Real.log x ^ (a - g)) := by
      calc ((padCount x : ℝ) + 1) ^ K * S
          ≤ Real.exp (K * u) * Real.exp (2 * Real.log x ^ (a - g)) ^ K :=
            mul_le_mul hM hS (Nat.cast_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (K * u + 2 * K * Real.log x ^ (a - g)) := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]
            ring_nf
    have h600 : (600 : ℝ) ≤ Real.exp 599 := by linarith [Real.add_one_le_exp (599 : ℝ)]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hmain : (((padCount x : ℝ) + 1) ^ K * S) ^ 2 * (600 * Real.exp (-Real.log x ^ a)) / θ ≤
        ε / 2 / 2 ^ K := by
      calc (((padCount x : ℝ) + 1) ^ K * S) ^ 2 * (600 * Real.exp (-Real.log x ^ a)) / θ
          = (((padCount x : ℝ) + 1) ^ K * S) ^ 2 * 600 *
              Real.exp (-Real.log x ^ a - -Real.log x ^ a / 4) := by
            rw [Real.exp_sub]
            ring
        _ ≤ Real.exp (K * u + 2 * K * Real.log x ^ (a - g)) ^ 2 * Real.exp 599 *
              Real.exp (-Real.log x ^ a - -Real.log x ^ a / 4) := by
            gcongr
        _ = Real.exp (2 * (K * u + 2 * K * Real.log x ^ (a - g)) + 599 +
              (-Real.log x ^ a - -Real.log x ^ a / 4)) := by
            rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
        _ ≤ Real.exp (-Real.log x ^ alo / 4 - (K + 1)) := by
            refine Real.exp_le_exp.2 ?_
            nlinarith
        _ ≤ ε / 2 / 2 ^ K := by
            rw [le_div_iff₀ (by positivity), le_div_iff₀ two_pos, Real.exp_sub]
            calc Real.exp (-Real.log x ^ alo / 4) / Real.exp (K + 1) * 2 ^ K * 2
                ≤ Real.exp (-Real.log x ^ alo / 4) / Real.exp (K + 1) * Real.exp 1 ^ K *
                    Real.exp 1 := by gcongr
              _ = ε := by
                  rw [← Real.exp_nat_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, ← Real.exp_add,
                    ← Real.exp_add, ← Real.exp_sub,
                    show ε = Real.exp (-Real.log x ^ alo / 4) from rfl]
                  congr 1
                  ring
    have hθ0 : 0 < θ⁻¹ := inv_pos.2 (Real.exp_pos _)
    have hA' : θ⁻¹ * ((((padCount x : ℝ) + 1) ^ K * S) ^ 2 *
        (6 * A * (100 * Real.exp (-Real.log x ^ a))))
        ≤ A * (ε / 2 / 2 ^ K) := by
      calc θ⁻¹ * ((((padCount x : ℝ) + 1) ^ K * S) ^ 2 *
            (6 * A * (100 * Real.exp (-Real.log x ^ a))))
          = A * ((((padCount x : ℝ) + 1) ^ K * S) ^ 2 * (600 * Real.exp (-Real.log x ^ a)) /
              θ) := by
            rw [div_eq_mul_inv]
            ring
        _ ≤ A * (ε / 2 / 2 ^ K) := mul_le_mul_of_nonneg_left hmain hA
    have hE' : θ⁻¹ * ((((padCount x : ℝ) + 1) ^ K * S) ^ 2 * ((2 * G * Bd ^ 2 + 1) * E)) ≤
        E * (Bd * (((padCount x : ℝ) + 1) ^ K * Bd) ^ 2 * (2 * G * Bd ^ 2 + 1)) := by
      have hS0 : 0 ≤ S := Nat.cast_nonneg _
      have hc : 0 ≤ (2 * (G : ℝ) * Bd ^ 2 + 1) * E := by positivity
      calc θ⁻¹ * ((((padCount x : ℝ) + 1) ^ K * S) ^ 2 * ((2 * G * Bd ^ 2 + 1) * E))
          ≤ Bd * ((((padCount x : ℝ) + 1) ^ K * Bd) ^ 2 * ((2 * G * Bd ^ 2 + 1) * E)) := by
            gcongr
        _ = _ := by ring
    rw [mul_add, mul_add]
    linarith
  -- sum the two tests and the `2^K` sets `I`
  calc (#{P ∈ T | Φ P ∧ ¬ IsGood x d Y d₀ P p} : ℝ)
      ≤ (#{P ∈ T | Φ P ∧ ¬ GoodFirst Y d₀ (rootRatio P) p} : ℝ) +
          ∑ I : Finset (Fin K), (#{P ∈ T | Φ P ∧ ∃ hI : I.Nonempty,
            ¬ ∑ t ∈ (freshDraws x d I).filter
                (fun t => ¬ Separated x d d₀ I (I.max' hI) (rootRatio P) p t),
              freshWeight x d I t ≤ Real.exp (-Real.log x ^ d.a (I.max' hI) / 4)} : ℝ) := by
        refine (Nat.cast_le.2 ((card_le_card hsub).trans (card_union_le _ _))).trans ?_
        push_cast
        gcongr
        exact_mod_cast card_biUnion_le
    _ ≤ (A * (ε / 2) + E * (((padCount x : ℝ) + 1) ^ K * n * (2 * n * G + 1))) +
          ∑ _I : Finset (Fin K), (A * (ε / 2 / 2 ^ K) +
            E * (Bd * (((padCount x : ℝ) + 1) ^ K * Bd) ^ 2 * (2 * G * Bd ^ 2 + 1))) :=
        add_le_add hfirst (sum_le_sum fun I _ => hsecond I)
    _ = A * ε + E * badIntervals x d Y p := by
        rw [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul,
          badIntervals]
        push_cast
        field_simp
        ring

end Erdos408.OneSided
