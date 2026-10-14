module

public import Erdos408.TwoSided.Setup

/-!
# Truncating a list expansion

The combinatorial core of Lemma E1 (`blueprint/two_sided_correlation.md` §6.1, steps 1–2 and
5–6), for a finite set `Q` of primes. A function in *list form*
`H(n) = ∑_j [R_j ⊆ D(n)] c_j ∏_{p ∈ D(n) \ R_j} w_p`, with `D(n)` the primes of `Q` dividing
`n`, expands as `∑_j [R_j ⊆ D(n)] c_j ∑_{U ⊆ D(n) \ R_j} ∏_{p ∈ U} (w_p - 1)`. Keeping the
subsets `|U| ≤ h₀` gives the divisor model `∑_{d ∣ n} A_d` with
`A_d = ∑_j ∑_{U ⊆ Q \ R_j, |U| ≤ h₀, ∏(R_j ∪ U) = d} c_j ∏_{p ∈ U} (w_p - 1)`.

* `DivModel.listForm`, `DivModel.truncModel`: the list form and its truncated model.
* `DivModel.norm_listForm_sub_le`: for `|w_p - 1| ≤ 1`, the pointwise error is at most
  `(∑_j [R_j ⊆ D(n)] |c_j|) 4^{|D(n)|} 2^{-h₀}`.
* `DivModel.sum_norm_truncModel_div_le`: `∑_d |A_d|/d ≤ (∑_j |c_j|/∏ R_j) ∏_{p ∈ Q} (1 + 1/p)`.
* `DivModel.listForm_mul`: list forms on disjoint prime sets multiply.
* `DivModel.sum_pow_card_divs_le`: `∑_{n ≤ N} z^{|D(n)|} ≤ N ∏_{p ∈ Q} (1 + (z - 1)/p)`, the
  bound (6.27).
-/

@[expose] public section

namespace Erdos408.TwoSided.DivModel

open Finset

variable {κ κ' : Type*}

/-- The primes of `Q` dividing `n`. -/
def divs (Q : Finset ℕ) (n : ℕ) : Finset ℕ :=
  Q.filter (· ∣ n)

/-- The list form `∑_j [R_j ⊆ D(n)] c_j ∏_{p ∈ D(n) \ R_j} w_p`. -/
noncomputable def listForm (Q : Finset ℕ) (J : Finset κ) (R : κ → Finset ℕ) (c : κ → ℂ)
    (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ J, if R j ⊆ divs Q n then c j * ∏ p ∈ divs Q n \ R j, w p else 0

/-- The truncated model `A_d` of a list form, keeping the subsets `|U| ≤ h₀`. -/
noncomputable def truncModel (Q : Finset ℕ) (J : Finset κ) (R : κ → Finset ℕ) (c : κ → ℂ)
    (w : ℕ → ℂ) (h₀ : ℕ) (d : ℕ) : ℂ :=
  ∑ j ∈ J, ∑ U ∈ (Q \ R j).powerset with #U ≤ h₀,
    if ∏ p ∈ R j ∪ U, p = d then c j * ∏ p ∈ U, (w p - 1) else 0

/-- For a set `S ⊆ Q` of primes and `n ≠ 0`, `∏ S ∣ n` iff `S ⊆ D(n)`. -/
theorem prod_dvd_iff {Q S : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) (hS : S ⊆ Q) (n : ℕ) :
    ∏ p ∈ S, p ∣ n ↔ S ⊆ divs Q n := by
  constructor
  · intro h p hp
    exact mem_filter.2 ⟨hS hp, (dvd_prod_of_mem _ hp).trans h⟩
  · intro h
    exact prod_primes_dvd n (fun p hp => (hQ p (hS hp)).prime)
      fun p hp => (mem_filter.1 (h hp)).2

/-- `D(n) ⊆ Q`. -/
theorem divs_subset (Q : Finset ℕ) (n : ℕ) : divs Q n ⊆ Q :=
  filter_subset _ _

/-- The divisor sum of the truncated model: the list expansion with `|U| ≤ h₀`. -/
theorem sum_divisors_truncModel {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) {J : Finset κ}
    {R : κ → Finset ℕ} (hR : ∀ j ∈ J, R j ⊆ Q) (c : κ → ℂ) (w : ℕ → ℂ) (h₀ : ℕ) {n : ℕ}
    (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, truncModel Q J R c w h₀ d =
      ∑ j ∈ J, if R j ⊆ divs Q n then
        c j * ∑ U ∈ (divs Q n \ R j).powerset with #U ≤ h₀, ∏ p ∈ U, (w p - 1) else 0 := by
  unfold truncModel
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [sum_comm]
  have hterm : ∀ U ∈ (Q \ R j).powerset.filter (#· ≤ h₀),
      ∑ d ∈ n.divisors, (if ∏ p ∈ R j ∪ U, p = d then c j * ∏ p ∈ U, (w p - 1) else 0) =
        if R j ∪ U ⊆ divs Q n then c j * ∏ p ∈ U, (w p - 1) else 0 := by
    intro U hU
    have hUQ : U ⊆ Q \ R j := mem_powerset.1 (mem_filter.1 hU).1
    have hsub : R j ∪ U ⊆ Q := union_subset (hR j hj) (hUQ.trans sdiff_subset)
    rw [sum_ite_eq]
    by_cases h : R j ∪ U ⊆ divs Q n
    · rw [ite_eq_left h, ite_eq_left (Nat.mem_divisors.2 ⟨(prod_dvd_iff hQ hsub n).2 h, hn⟩)]
    · rw [ite_eq_right h,
        ite_eq_right fun h' => h ((prod_dvd_iff hQ hsub n).1 (Nat.mem_divisors.1 h').1)]
  rw [sum_congr rfl hterm]
  split_ifs with hRj
  · rw [mul_sum, ← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext U
    simp only [mem_filter, mem_powerset, union_subset_iff, subset_sdiff]
    constructor
    · rintro ⟨⟨⟨hUQ, hUR⟩, hU⟩, -, hUD⟩
      exact ⟨⟨hUD, hUR⟩, hU⟩
    · rintro ⟨⟨hUD, hUR⟩, hU⟩
      exact ⟨⟨⟨hUD.trans (divs_subset Q n), hUR⟩, hU⟩, hRj, hUD⟩
  · refine sum_eq_zero fun U _ => ?_
    rw [ite_eq_right fun h => hRj (subset_union_left.trans h)]

/-- The list form, with every damping factor expanded. -/
theorem listForm_eq_sum (Q : Finset ℕ) (J : Finset κ) (R : κ → Finset ℕ) (c : κ → ℂ)
    (w : ℕ → ℂ) (n : ℕ) :
    listForm Q J R c w n =
      ∑ j ∈ J, if R j ⊆ divs Q n then
        c j * ∑ U ∈ (divs Q n \ R j).powerset, ∏ p ∈ U, (w p - 1) else 0 := by
  unfold listForm
  refine sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [← prod_one_add]
    simp
  · rfl

/-- The truncation error: the subsets with `|U| > h₀`. -/
theorem listForm_sub_sum_divisors {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) {J : Finset κ}
    {R : κ → Finset ℕ} (hR : ∀ j ∈ J, R j ⊆ Q) (c : κ → ℂ) (w : ℕ → ℂ) (h₀ : ℕ) {n : ℕ}
    (hn : n ≠ 0) :
    listForm Q J R c w n - ∑ d ∈ n.divisors, truncModel Q J R c w h₀ d =
      ∑ j ∈ J, if R j ⊆ divs Q n then
        c j * ∑ U ∈ (divs Q n \ R j).powerset with ¬#U ≤ h₀, ∏ p ∈ U, (w p - 1) else 0 := by
  rw [listForm_eq_sum, sum_divisors_truncModel hQ hR c w h₀ hn, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [← mul_sub, ← sum_filter_add_sum_filter_not _ (fun U : Finset ℕ => #U ≤ h₀)]
    ring
  · ring

/-- The number of subsets of `D \ R` with more than `h₀` elements is at most
`4^{|D|} / 2^{h₀}`. -/
theorem card_filter_powerset_le (D R : Finset ℕ) (h₀ : ℕ) :
    (#((D \ R).powerset.filter fun U => ¬#U ≤ h₀) : ℝ) ≤ 4 ^ #D / 2 ^ h₀ := by
  rcases le_or_gt #D h₀ with hD | hD
  · have : (D \ R).powerset.filter (fun U => ¬#U ≤ h₀) = ∅ := by
      refine filter_eq_empty_iff.2 fun U hU => ?_
      have := card_le_card ((mem_powerset.1 hU).trans sdiff_subset)
      omega
    rw [this, card_empty, Nat.cast_zero]
    positivity
  · have h1 : #((D \ R).powerset.filter fun U => ¬#U ≤ h₀) ≤ 2 ^ #D := by
      calc _ ≤ #(D \ R).powerset := card_filter_le _ _
        _ = 2 ^ #(D \ R) := card_powerset _
        _ ≤ 2 ^ #D := Nat.pow_le_pow_right (by norm_num) (card_le_card sdiff_subset)
    have h2 : (2 : ℝ) ^ h₀ ≤ 2 ^ #D := pow_le_pow_right₀ (by norm_num) hD.le
    rw [le_div_iff₀ (by positivity)]
    calc (#((D \ R).powerset.filter fun U => ¬#U ≤ h₀) : ℝ) * 2 ^ h₀
        ≤ 2 ^ #D * 2 ^ #D := by
          gcongr
          exact_mod_cast h1
      _ = 4 ^ #D := by rw [← mul_pow]; norm_num

/-- The pointwise truncation error: for `|w_p - 1| ≤ 1` on `Q`, it is at most
`(∑_j [R_j ⊆ D(n)] |c_j|) 4^{|D(n)|} / 2^{h₀}`. -/
theorem norm_listForm_sub_le {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) {J : Finset κ}
    {R : κ → Finset ℕ} (hR : ∀ j ∈ J, R j ⊆ Q) (c : κ → ℂ) {w : ℕ → ℂ}
    (hw : ∀ p ∈ Q, ‖w p - 1‖ ≤ 1) (h₀ : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ‖listForm Q J R c w n - ∑ d ∈ n.divisors, truncModel Q J R c w h₀ d‖ ≤
      (∑ j ∈ J, if R j ⊆ divs Q n then ‖c j‖ else 0) * (4 ^ #(divs Q n) / 2 ^ h₀) := by
  rw [listForm_sub_sum_divisors hQ hR c w h₀ hn, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
  split_ifs
  · rw [norm_mul]
    gcongr
    refine (norm_sum_le _ _).trans ?_
    refine le_trans ?_ (card_filter_powerset_le _ (R j) h₀)
    have : ∀ U ∈ (divs Q n \ R j).powerset.filter (fun U => ¬#U ≤ h₀),
        ‖∏ p ∈ U, (w p - 1)‖ ≤ 1 := by
      intro U hU
      rw [norm_prod]
      refine prod_le_one₀ (fun _ _ => norm_nonneg _) fun p hp => hw p ?_
      exact divs_subset Q n (sdiff_subset (mem_powerset.1 (mem_filter.1 hU).1 hp))
    calc _ ≤ ∑ _U ∈ (divs Q n \ R j).powerset.filter (fun U => ¬#U ≤ h₀), (1 : ℝ) :=
          sum_le_sum this
      _ = _ := by rw [sum_const, nsmul_eq_mul, mul_one]
  · simp

/-- The truncated model vanishes off the products `∏(R_j ∪ U)` with `U ⊆ Q \ R_j` and
`|U| ≤ h₀`. -/
theorem exists_of_truncModel_ne_zero {Q : Finset ℕ} {J : Finset κ} {R : κ → Finset ℕ}
    {c : κ → ℂ} {w : ℕ → ℂ} {h₀ d : ℕ} (hd : truncModel Q J R c w h₀ d ≠ 0) :
    ∃ j ∈ J, ∃ U ⊆ Q \ R j, #U ≤ h₀ ∧ ∏ p ∈ R j ∪ U, p = d := by
  obtain ⟨j, hj, hj'⟩ := exists_ne_zero_of_sum_ne_zero hd
  obtain ⟨U, hU, hU'⟩ := exists_ne_zero_of_sum_ne_zero hj'
  obtain ⟨hU₁, hU₂⟩ := mem_filter.1 hU
  refine ⟨j, hj, U, mem_powerset.1 hU₁, hU₂, ?_⟩
  by_contra h
  exact hU' (ite_eq_right h)

/-- The mass of the truncated model:
`∑_d |A_d|/d ≤ (∑_j |c_j| / ∏ R_j) ∏_{p ∈ Q} (1 + 1/p)`. -/
theorem sum_norm_truncModel_div_le {Q : Finset ℕ} (J : Finset κ) (R : κ → Finset ℕ)
    (c : κ → ℂ) {w : ℕ → ℂ} (hw : ∀ p ∈ Q, ‖w p - 1‖ ≤ 1) (h₀ : ℕ) (s : Finset ℕ) :
    ∑ d ∈ s, ‖truncModel Q J R c w h₀ d‖ / d ≤
      (∑ j ∈ J, ‖c j‖ / ∏ p ∈ R j, (p : ℝ)) * ∏ p ∈ Q, (1 + 1 / (p : ℝ)) := by
  -- bound each coefficient by the sum of the norms of its terms
  have h1 : ∀ d ∈ s, ‖truncModel Q J R c w h₀ d‖ / d ≤
      ∑ j ∈ J, ∑ U ∈ (Q \ R j).powerset with #U ≤ h₀,
        if ∏ p ∈ R j ∪ U, p = d then ‖c j‖ / (∏ p ∈ R j ∪ U, p : ℕ) else 0 := by
    intro d _
    have hn : ‖truncModel Q J R c w h₀ d‖ ≤ ∑ j ∈ J, ∑ U ∈ (Q \ R j).powerset with #U ≤ h₀,
        ‖if ∏ p ∈ R j ∪ U, p = d then c j * ∏ p ∈ U, (w p - 1) else 0‖ :=
      (norm_sum_le _ _).trans (sum_le_sum fun j _ => norm_sum_le _ _)
    refine (div_le_div_of_nonneg_right hn (Nat.cast_nonneg d)).trans ?_
    rw [sum_div]
    refine sum_le_sum fun j hj => ?_
    rw [sum_div]
    refine sum_le_sum fun U hU => ?_
    split_ifs with h
    · rw [← h, norm_mul, norm_prod]
      have : ∏ p ∈ U, ‖w p - 1‖ ≤ 1 := by
        refine prod_le_one₀ (fun _ _ => norm_nonneg _) fun p hp => hw p ?_
        exact sdiff_subset ((mem_powerset.1 (mem_filter.1 hU).1) hp)
      have hc := norm_nonneg (c j)
      gcongr
      calc ‖c j‖ * ∏ p ∈ U, ‖w p - 1‖ ≤ ‖c j‖ * 1 := by gcongr
        _ = ‖c j‖ := mul_one _
    · simp
  refine (sum_le_sum h1).trans ?_
  rw [sum_comm]
  rw [sum_mul]
  refine sum_le_sum fun j hj => ?_
  rw [sum_comm]
  -- the inner sum over `d` picks out `d = ∏ (R_j ∪ U)`
  have h2 : ∀ U ∈ (Q \ R j).powerset.filter (#· ≤ h₀),
      ∑ d ∈ s, (if ∏ p ∈ R j ∪ U, p = d then ‖c j‖ / (∏ p ∈ R j ∪ U, p : ℕ) else 0) ≤
        ‖c j‖ / (∏ p ∈ R j, (p : ℝ)) * ∏ p ∈ U, (1 / (p : ℝ)) := by
    intro U hU
    have hUQ : U ⊆ Q \ R j := mem_powerset.1 (mem_filter.1 hU).1
    have hdisj : Disjoint (R j) U := disjoint_of_subset_right hUQ disjoint_sdiff
    rw [sum_ite_eq]
    have heq : ‖c j‖ / ((∏ p ∈ R j ∪ U, p : ℕ) : ℝ) =
        ‖c j‖ / (∏ p ∈ R j, (p : ℝ)) * ∏ p ∈ U, (1 / (p : ℝ)) := by
      simp only [one_div, prod_inv_distrib]
      rw [Nat.cast_prod, prod_union hdisj, div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_assoc]
    split_ifs
    · exact heq.le
    · rw [← heq]
      positivity
  refine (sum_le_sum h2).trans ?_
  rw [← mul_sum]
  have hR0 : 0 ≤ ‖c j‖ / ∏ p ∈ R j, (p : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hR0
  rw [prod_one_add]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
  intro U hU
  exact mem_powerset.2 ((mem_powerset.1 (mem_filter.1 hU).1).trans sdiff_subset)

/-- `D(n)` of a disjoint union. -/
theorem divs_union (Q₁ Q₂ : Finset ℕ) (n : ℕ) : divs (Q₁ ∪ Q₂) n = divs Q₁ n ∪ divs Q₂ n :=
  filter_union _ _ _

/-- The represented sets of a pair split along a disjoint union `Q₁ ∪ Q₂`. -/
theorem union_subset_divs_iff {Q₁ Q₂ R₁ R₂ : Finset ℕ} (hQ : Disjoint Q₁ Q₂) (hR₁ : R₁ ⊆ Q₁)
    (hR₂ : R₂ ⊆ Q₂) (n : ℕ) :
    R₁ ∪ R₂ ⊆ divs (Q₁ ∪ Q₂) n ↔ R₁ ⊆ divs Q₁ n ∧ R₂ ⊆ divs Q₂ n := by
  rw [divs_union]
  constructor
  · intro h
    constructor
    · intro p hp
      rcases mem_union.1 (h (mem_union_left _ hp)) with h' | h'
      · exact h'
      · exact absurd (divs_subset Q₂ n h') (disjoint_left.1 hQ (hR₁ hp))
    · intro p hp
      rcases mem_union.1 (h (mem_union_right _ hp)) with h' | h'
      · exact absurd (divs_subset Q₁ n h') (disjoint_right.1 hQ (hR₂ hp))
      · exact h'
  · rintro ⟨h₁, h₂⟩
    exact union_subset_union h₁ h₂

/-- List forms on disjoint prime sets multiply: the lists are pairs, the represented sets
are unions. -/
theorem listForm_mul {Q₁ Q₂ : Finset ℕ} (hQ : Disjoint Q₁ Q₂) {J₁ : Finset κ}
    {J₂ : Finset κ'} {R₁ : κ → Finset ℕ} {R₂ : κ' → Finset ℕ} (hR₁ : ∀ j ∈ J₁, R₁ j ⊆ Q₁)
    (hR₂ : ∀ j ∈ J₂, R₂ j ⊆ Q₂) (c₁ : κ → ℂ) (c₂ : κ' → ℂ) (w : ℕ → ℂ) (n : ℕ) :
    listForm Q₁ J₁ R₁ c₁ w n * listForm Q₂ J₂ R₂ c₂ w n =
      listForm (Q₁ ∪ Q₂) (J₁ ×ˢ J₂) (fun j => R₁ j.1 ∪ R₂ j.2) (fun j => c₁ j.1 * c₂ j.2)
        w n := by
  unfold listForm
  rw [sum_mul_sum, sum_product]
  refine sum_congr rfl fun j₁ hj₁ => sum_congr rfl fun j₂ hj₂ => ?_
  have hD₁ := divs_subset Q₁ n
  have hD₂ := divs_subset Q₂ n
  have hiff := union_subset_divs_iff hQ (hR₁ j₁ hj₁) (hR₂ j₂ hj₂) n
  by_cases h₁ : R₁ j₁ ⊆ divs Q₁ n
  · by_cases h₂ : R₂ j₂ ⊆ divs Q₂ n
    · rw [ite_eq_left h₁, ite_eq_left h₂, ite_eq_left (hiff.2 ⟨h₁, h₂⟩), divs_union]
      have hsd : (divs Q₁ n ∪ divs Q₂ n) \ (R₁ j₁ ∪ R₂ j₂) =
          (divs Q₁ n \ R₁ j₁) ∪ (divs Q₂ n \ R₂ j₂) := by
        ext p
        simp only [mem_sdiff, mem_union]
        constructor
        · rintro ⟨hp | hp, hp'⟩
          · exact Or.inl ⟨hp, fun h => hp' (Or.inl h)⟩
          · exact Or.inr ⟨hp, fun h => hp' (Or.inr h)⟩
        · rintro (⟨hp, hp'⟩ | ⟨hp, hp'⟩)
          · refine ⟨Or.inl hp, ?_⟩
            rintro (h | h)
            · exact hp' h
            · exact disjoint_left.1 hQ (hD₁ hp) (hR₂ j₂ hj₂ h)
          · refine ⟨Or.inr hp, ?_⟩
            rintro (h | h)
            · exact disjoint_left.1 hQ (hR₁ j₁ hj₁ h) (hD₂ hp)
            · exact hp' h
      rw [hsd, prod_union (disjoint_of_subset_left (sdiff_subset.trans hD₁)
        (disjoint_of_subset_right (sdiff_subset.trans hD₂) hQ))]
      ring
    · rw [ite_eq_right h₂, ite_eq_right fun h => h₂ (hiff.1 h).2, mul_zero]
  · rw [ite_eq_right h₁, ite_eq_right fun h => h₁ (hiff.1 h).1, zero_mul]

/-- The weight sum `∑_j [R_j ⊆ D(n)] |c_j|` of a product of list forms on disjoint sets. -/
theorem sum_norm_mul {Q₁ Q₂ : Finset ℕ} (hQ : Disjoint Q₁ Q₂) {J₁ : Finset κ}
    {J₂ : Finset κ'} {R₁ : κ → Finset ℕ} {R₂ : κ' → Finset ℕ} (hR₁ : ∀ j ∈ J₁, R₁ j ⊆ Q₁)
    (hR₂ : ∀ j ∈ J₂, R₂ j ⊆ Q₂) (c₁ : κ → ℂ) (c₂ : κ' → ℂ) (n : ℕ) :
    (∑ j ∈ J₁ ×ˢ J₂, if R₁ j.1 ∪ R₂ j.2 ⊆ divs (Q₁ ∪ Q₂) n then ‖c₁ j.1 * c₂ j.2‖ else 0) =
      (∑ j ∈ J₁, if R₁ j ⊆ divs Q₁ n then ‖c₁ j‖ else 0) *
        ∑ j ∈ J₂, if R₂ j ⊆ divs Q₂ n then ‖c₂ j‖ else 0 := by
  rw [sum_mul_sum, sum_product]
  refine sum_congr rfl fun j₁ hj₁ => sum_congr rfl fun j₂ hj₂ => ?_
  have hiff := union_subset_divs_iff hQ (hR₁ j₁ hj₁) (hR₂ j₂ hj₂) n
  by_cases h₁ : R₁ j₁ ⊆ divs Q₁ n
  · by_cases h₂ : R₂ j₂ ⊆ divs Q₂ n
    · rw [ite_eq_left h₁, ite_eq_left h₂, ite_eq_left (hiff.2 ⟨h₁, h₂⟩), norm_mul]
    · rw [ite_eq_right h₂, ite_eq_right fun h => h₂ (hiff.1 h).2, mul_zero]
  · rw [ite_eq_right h₁, ite_eq_right fun h => h₁ (hiff.1 h).1, zero_mul]

/-- The mass `∑_j |c_j| / ∏ R_j` of a product of list forms on disjoint sets. -/
theorem sum_norm_div_mul {Q₁ Q₂ : Finset ℕ} (hQ : Disjoint Q₁ Q₂) {J₁ : Finset κ}
    {J₂ : Finset κ'} {R₁ : κ → Finset ℕ} {R₂ : κ' → Finset ℕ} (hR₁ : ∀ j ∈ J₁, R₁ j ⊆ Q₁)
    (hR₂ : ∀ j ∈ J₂, R₂ j ⊆ Q₂) (c₁ : κ → ℂ) (c₂ : κ' → ℂ) :
    ∑ j ∈ J₁ ×ˢ J₂, ‖c₁ j.1 * c₂ j.2‖ / ∏ p ∈ R₁ j.1 ∪ R₂ j.2, (p : ℝ) =
      (∑ j ∈ J₁, ‖c₁ j‖ / ∏ p ∈ R₁ j, (p : ℝ)) * ∑ j ∈ J₂, ‖c₂ j‖ / ∏ p ∈ R₂ j, (p : ℝ) := by
  rw [sum_mul_sum, sum_product]
  refine sum_congr rfl fun j₁ hj₁ => sum_congr rfl fun j₂ hj₂ => ?_
  rw [prod_union (disjoint_of_subset_left (hR₁ j₁ hj₁) (disjoint_of_subset_right
    (hR₂ j₂ hj₂) hQ)), norm_mul]
  ring

/-- (6.27): `∑_{n ≤ N} z^{|D(n)|} ≤ N ∏_{p ∈ Q} (1 + (z - 1)/p)` for `z ≥ 1`. -/
theorem sum_pow_card_divs_le {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) {z : ℝ} (hz : 1 ≤ z)
    (N : ℕ) :
    ∑ n ∈ Ioc 0 N, z ^ #(divs Q n) ≤ N * ∏ p ∈ Q, (1 + (z - 1) / p) := by
  -- `z^{|D|} = ∑_{U ⊆ D} (z - 1)^{|U|}`
  have h1 : ∀ n ∈ Ioc 0 N, z ^ #(divs Q n) =
      ∑ U ∈ Q.powerset, if ∏ p ∈ U, p ∣ n then (z - 1) ^ #U else 0 := by
    intro n _
    have : z ^ #(divs Q n) = ∑ U ∈ (divs Q n).powerset, (z - 1) ^ #U := by
      rw [← prod_const, show z = 1 + (z - 1) by ring, prod_one_add]
      simp
    rw [this, ← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext U
    simp only [mem_powerset, mem_filter]
    constructor
    · intro h
      exact ⟨h.trans (divs_subset Q n), (prod_dvd_iff hQ (h.trans (divs_subset Q n)) n).2 h⟩
    · rintro ⟨h, h'⟩
      exact (prod_dvd_iff hQ h n).1 h'
  rw [sum_congr rfl h1, sum_comm]
  have h2 : ∀ U ∈ Q.powerset,
      ∑ n ∈ Ioc 0 N, (if ∏ p ∈ U, p ∣ n then (z - 1) ^ #U else 0) ≤
        N * ∏ p ∈ U, ((z - 1) / p) := by
    intro U hU
    rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div, prod_div_distrib,
      prod_const]
    have hpos : (0 : ℝ) < ∏ p ∈ U, (p : ℝ) :=
      prod_pos fun p hp => by exact_mod_cast (hQ p (mem_powerset.1 hU hp)).pos
    have hdiv : ((N / ∏ p ∈ U, p : ℕ) : ℝ) ≤ N / ∏ p ∈ U, (p : ℝ) := by
      rw [← Nat.cast_prod]
      exact Nat.cast_div_le
    have hz1 : 0 ≤ (z - 1) ^ #U := pow_nonneg (by linarith) _
    calc ((N / ∏ p ∈ U, p : ℕ) : ℝ) * (z - 1) ^ #U ≤ N / (∏ p ∈ U, (p : ℝ)) * (z - 1) ^ #U :=
          mul_le_mul_of_nonneg_right hdiv hz1
      _ = N * ((z - 1) ^ #U / ∏ p ∈ U, (p : ℝ)) := by ring
  refine (sum_le_sum h2).trans ?_
  rw [← mul_sum, ← prod_one_add]

/-- `∏_{p ∈ Q} (1 + a/p) ≤ exp(a ∑_{p ∈ Q} 1/p)` for `a ≥ 0`. -/
theorem prod_one_add_div_le_exp (Q : Finset ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ∏ p ∈ Q, (1 + a / p) ≤ Real.exp (a * ∑ p ∈ Q, (1 : ℝ) / p) := by
  rw [mul_sum, Real.exp_sum]
  refine prod_le_prod₀ (fun p _ => by positivity) fun p _ => ?_
  rw [mul_one_div]
  linarith [Real.add_one_le_exp (a / p)]

end Erdos408.TwoSided.DivModel
