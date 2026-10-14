module

public import Erdos408.Extraction.Defs

/-!
# Bonferroni inequalities

The truncated inclusion–exclusion used by the sieve of E6.

* Pointwise: `|[s = ∅] - ∑_{u ⊆ s, |u| ≤ R} (-1)^{|u|}| ≤ #{u ⊆ s : |u| = R + 1}`, from
  `∑_{k ≤ R} (-1)^k C(n, k) = (-1)^R C(n - 1, R)`.
* For products, averaged over the product measure
  `w(T) = ∏_{i ∈ T} x_i ∏_{i ∈ S ∖ T} (1 - x_i)` on the subsets of `S`:
  `|∏_{i ∈ S} (1 - x_i) - ∑_{u ⊆ S, |u| ≤ R} (-1)^{|u|} x^u| ≤ ∑_{|u| = R + 1} x^u`.
* Rankin's bound `∑_{|u| = k} x^u ≤ z^{-k} ∏ (1 + z x_i)`, the bound
  `∑_{|u| = 2} x^u ≤ (∑ x_i)² / 2`, and the count `#{u ⊆ S : |u| ≤ m} ≤ (|S| + 1)^m`.
-/

@[expose] public section

namespace Erdos408

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### Pointwise -/

/-- The alternating sum of a row of binomials, truncated at `R`, written over all of the row. -/
private lemma sum_range_choose_ite_eq (n R : ℕ) :
    ∑ m ∈ range (n + 1), (n.choose m : ℝ) * (if m ≤ R then (-1 : ℝ) ^ m else 0) =
      ∑ m ∈ range (R + 1), (-1 : ℝ) ^ m * n.choose m := by
  have h1 : ∑ m ∈ range (n + 1), (n.choose m : ℝ) * (if m ≤ R then (-1 : ℝ) ^ m else 0) =
      ∑ m ∈ range (n + R + 2), (n.choose m : ℝ) * (if m ≤ R then (-1 : ℝ) ^ m else 0) := by
    refine sum_subset (range_subset_range.2 (by omega)) fun m hm hm' => ?_
    rw [mem_range] at hm hm'
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  have h2 : ∑ m ∈ range (R + 1), (-1 : ℝ) ^ m * n.choose m =
      ∑ m ∈ range (n + R + 2), (n.choose m : ℝ) * (if m ≤ R then (-1 : ℝ) ^ m else 0) := by
    refine (sum_congr rfl fun m hm => ?_).trans
      (sum_subset (range_subset_range.2 (by omega)) fun m hm hm' => ?_)
    · rw [mem_range] at hm
      rw [ite_eq_left (by omega)]
      ring
    · rw [mem_range] at hm'
      rw [ite_eq_right (by omega), mul_zero]
  rw [h1, h2]

/-- Pointwise Bonferroni: `|[s = ∅] - ∑_{u ⊆ s, |u| ≤ R} (-1)^{|u|}| ≤ #{u ⊆ s : |u| = R + 1}`. -/
lemma abs_ite_sub_sum_powerset_le (s : Finset α) (R : ℕ) :
    |(if s = ∅ then (1 : ℝ) else 0) - ∑ u ∈ s.powerset with u.card ≤ R, (-1 : ℝ) ^ u.card| ≤
      (s.powersetCard (R + 1)).card := by
  rw [sum_filter, sum_powerset_apply_card (fun m => if m ≤ R then (-1 : ℝ) ^ m else 0)]
  simp only [nsmul_eq_mul]
  rw [sum_range_choose_ite_eq, card_powersetCard]
  rcases Nat.eq_zero_or_pos s.card with h | h
  · rw [card_eq_zero.1 h, ite_eq_left rfl, card_empty, sum_range_succ']
    simp [Nat.choose_zero_succ]
  · obtain ⟨n, hn⟩ : ∃ n, s.card = n + 1 := ⟨s.card - 1, by omega⟩
    rw [ite_eq_right (by rw [← card_eq_zero]; omega), hn]
    have h := Int.alternating_sum_range_choose_eq_choose (n := n) (m := R)
    have h' : ∑ m ∈ range (R + 1), (-1 : ℝ) ^ m * ((n + 1).choose m : ℝ) =
        (-1 : ℝ) ^ R * n.choose R := by exact_mod_cast h
    rw [h', zero_sub, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      Nat.abs_cast, Nat.choose_succ_succ]
    push_cast
    linarith [(Nat.cast_nonneg (n.choose (R + 1)) : (0 : ℝ) ≤ _)]

/-! ### Averaging over the product measure -/

/-- The product measure of the subsets containing `u` is `∏_{i ∈ u} x_i`. -/
lemma sum_powerset_prod_mul_ite_subset (S u : Finset α) (hu : u ⊆ S) (x : α → ℝ) :
    ∑ T ∈ S.powerset, (∏ i ∈ T, x i) * (∏ i ∈ S \ T, (1 - x i)) * (if u ⊆ T then 1 else 0) =
      ∏ i ∈ u, x i := by
  have h := prod_add (fun i => x i) (fun i => (1 - x i) * (if i ∈ u then 0 else 1)) S
  have hl : ∏ i ∈ S, (x i + (1 - x i) * (if i ∈ u then 0 else 1)) =
      ∏ i ∈ S, (if i ∈ u then x i else 1) :=
    prod_congr rfl fun i _ => by split_ifs <;> ring
  rw [hl, prod_ite_mem, inter_eq_right.2 hu] at h
  rw [h]
  refine sum_congr rfl fun T hT => ?_
  rw [prod_mul_distrib, mul_assoc]
  congr 2
  rw [show (∏ i ∈ S \ T, if i ∈ u then (0 : ℝ) else 1) =
      ∏ i ∈ S \ T, if i ∉ u then (1 : ℝ) else 0 from prod_congr rfl fun i _ => by
        split_ifs <;> simp_all, prod_ite_zero, prod_const_one]
  congr 1
  apply propext
  constructor
  · intro h' i hi hiu
    exact (mem_sdiff.1 hi).2 (h' hiu)
  · intro h' i hi
    by_contra hiT
    exact h' i (mem_sdiff.2 ⟨hu hi, hiT⟩) hi

/-- Bonferroni for products: with `0 ≤ x_i ≤ 1`,
`|∏ (1 - x_i) - ∑_{u ⊆ S, |u| ≤ R} (-1)^{|u|} x^u| ≤ ∑_{|u| = R + 1} x^u`. -/
lemma abs_prod_one_sub_sub_sum_le (S : Finset α) (R : ℕ) (x : α → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i ∧ x i ≤ 1) :
    |∏ i ∈ S, (1 - x i) - ∑ u ∈ S.powerset with u.card ≤ R, (-1 : ℝ) ^ u.card * ∏ i ∈ u, x i| ≤
      ∑ u ∈ S.powersetCard (R + 1), ∏ i ∈ u, x i := by
  set w : Finset α → ℝ := fun T => (∏ i ∈ T, x i) * ∏ i ∈ S \ T, (1 - x i) with hw
  have hw0 : ∀ T ∈ S.powerset, 0 ≤ w T := fun T hT =>
    mul_nonneg (prod_nonneg fun i hi => (hx i (mem_powerset.1 hT hi)).1)
      (prod_nonneg fun i hi => sub_nonneg.2 (hx i (mem_sdiff.1 hi).1).2)
  -- each sum is an average against `w`
  have hav : ∀ u ∈ S.powerset, ∏ i ∈ u, x i =
      ∑ T ∈ S.powerset, w T * (if u ⊆ T then 1 else 0) := fun u hu =>
    (sum_powerset_prod_mul_ite_subset S u (mem_powerset.1 hu) x).symm
  have h1 : ∏ i ∈ S, (1 - x i) = ∑ T ∈ S.powerset, w T * (if T = ∅ then 1 else 0) := by
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_powerset, empty_subset, ite_true, hw,
      prod_empty, one_mul, sdiff_empty]
  have hswap : ∀ (P : Finset α → Prop) [DecidablePred P] (f : Finset α → ℝ),
      ∑ u ∈ S.powerset with P u, f u * ∏ i ∈ u, x i =
        ∑ T ∈ S.powerset, w T * ∑ u ∈ T.powerset with P u, f u := by
    intro P _ f
    calc ∑ u ∈ S.powerset with P u, f u * ∏ i ∈ u, x i
        = ∑ u ∈ S.powerset with P u, ∑ T ∈ S.powerset,
            f u * (w T * (if u ⊆ T then 1 else 0)) :=
          sum_congr rfl fun u hu => by rw [hav u (mem_filter.1 hu).1, mul_sum]
      _ = ∑ T ∈ S.powerset, ∑ u ∈ S.powerset with P u,
            f u * (w T * (if u ⊆ T then 1 else 0)) := sum_comm
      _ = _ := sum_congr rfl fun T hT => by
          have hTS := mem_powerset.1 hT
          have hfilt : (S.powerset.filter P).filter (· ⊆ T) = T.powerset.filter P := by
            ext u
            simp only [mem_filter, mem_powerset]
            exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hTS, h.2⟩, h.1⟩⟩
          rw [← hfilt, Finset.sum_filter (fun u : Finset α => u ⊆ T), mul_sum]
          refine sum_congr rfl fun u _ => ?_
          split_ifs <;> ring
  have h2 := hswap (fun u => u.card ≤ R) fun u => (-1 : ℝ) ^ u.card
  have h3 := hswap (fun u => u.card = R + 1) fun _ => (1 : ℝ)
  simp only [one_mul, sum_const] at h3
  rw [powersetCard_eq_filter, h3, h1, h2, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun T hT => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (hw0 T hT), nsmul_eq_mul, mul_one]
  refine mul_le_mul_of_nonneg_left ?_ (hw0 T hT)
  have := abs_ite_sub_sum_powerset_le T R
  rwa [powersetCard_eq_filter] at this

/-! ### Rankin's bound and small cases -/

omit [DecidableEq α] in
/-- Rankin's bound: `∑_{|u| = k} x^u ≤ z^{-k} ∏ (1 + z x_i)` for `x ≥ 0`, `z > 0`. -/
lemma sum_powersetCard_prod_le (S : Finset α) (k : ℕ) {x : α → ℝ} (hx : ∀ i ∈ S, 0 ≤ x i)
    {z : ℝ} (hz : 0 < z) :
    ∑ u ∈ S.powersetCard k, ∏ i ∈ u, x i ≤ (∏ i ∈ S, (1 + z * x i)) / z ^ k := by
  rw [le_div_iff₀ (pow_pos hz k), prod_one_add, sum_mul]
  calc ∑ u ∈ S.powersetCard k, (∏ i ∈ u, x i) * z ^ k
      = ∑ u ∈ S.powersetCard k, ∏ i ∈ u, z * x i := by
        refine sum_congr rfl fun u hu => ?_
        rw [prod_mul_distrib, prod_const, (mem_powersetCard.1 hu).2, mul_comm]
    _ ≤ ∑ u ∈ S.powerset, ∏ i ∈ u, z * x i :=
        sum_le_sum_of_subset_of_nonneg (fun u hu => mem_powerset.2 (mem_powersetCard.1 hu).1)
          fun u hu _ =>
          prod_nonneg fun i hi => mul_nonneg hz.le (hx i (mem_powerset.1 hu hi))

/-- `∑_{|u| = 2} x^u ≤ (∑ x_i)² / 2` for `x ≥ 0`. -/
lemma sum_powersetCard_two_prod_le (S : Finset α) {x : α → ℝ} (hx : ∀ i ∈ S, 0 ≤ x i) :
    ∑ u ∈ S.powersetCard 2, ∏ i ∈ u, x i ≤ (∑ i ∈ S, x i) ^ 2 / 2 := by
  induction S using Finset.induction_on with
  | empty =>
    rw [powersetCard_eq_empty.2 (by simp)]
    simp
  | insert a S ha ih =>
    have hxS : ∀ i ∈ S, 0 ≤ x i := fun i hi => hx i (mem_insert_of_mem hi)
    have hxa : 0 ≤ x a := hx a (mem_insert_self a S)
    have hS0 : 0 ≤ ∑ i ∈ S, x i := sum_nonneg hxS
    rw [powersetCard_succ_insert ha, sum_insert ha]
    have hu := sum_union_inter (s₁ := S.powersetCard 2)
      (s₂ := (S.powersetCard 1).image (insert a)) (f := fun u => ∏ i ∈ u, x i)
    have hnn : ∀ u ∈ (insert a S).powerset, 0 ≤ ∏ i ∈ u, x i := fun u hu =>
      prod_nonneg fun i hi => hx i (mem_powerset.1 hu hi)
    have hinter : 0 ≤ ∑ u ∈ S.powersetCard 2 ∩ (S.powersetCard 1).image (insert a),
        ∏ i ∈ u, x i := sum_nonneg fun u hu => by
      obtain ⟨-, hu⟩ := mem_inter.1 hu
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hu
      exact hnn _ (mem_powerset.2 (insert_subset_insert a
        (mem_powersetCard.1 hv).1))
    have himg : ∑ u ∈ (S.powersetCard 1).image (insert a), ∏ i ∈ u, x i ≤
        x a * ∑ i ∈ S, x i := by
      refine (sum_image_le_of_nonneg fun u hu => ?_).trans (le_of_eq ?_)
      · obtain ⟨v, hv, rfl⟩ := mem_image.1 hu
        exact hnn _ (mem_powerset.2 (insert_subset_insert a
          (mem_powersetCard.1 hv).1))
      · rw [powersetCard_one, sum_map, mul_sum]
        refine sum_congr rfl fun i hi => ?_
        simp only [Function.Embedding.coeFn_mk]
        rw [prod_insert fun h => ha (by rwa [← mem_singleton.1 h] at hi), prod_singleton]
    nlinarith [ih hxS]

/-- `#{u ⊆ S : |u| ≤ m} ≤ (|S| + 1)^m`. -/
lemma card_filter_powerset_card_le (S : Finset α) (m : ℕ) :
    (S.powerset.filter (·.card ≤ m)).card ≤ (S.card + 1) ^ m := by
  have hsub : S.powerset.filter (·.card ≤ m) ⊆ (range (m + 1)).biUnion (S.powersetCard ·) := by
    intro u hu
    obtain ⟨hu, hm⟩ := mem_filter.1 hu
    exact mem_biUnion.2 ⟨u.card, mem_range.2 (by omega),
      mem_powersetCard.2 ⟨mem_powerset.1 hu, rfl⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [add_pow]
  refine sum_le_sum fun k hk => ?_
  rw [card_powersetCard, one_pow, mul_one]
  have h1 : 1 ≤ m.choose k := Nat.choose_pos (by have := mem_range.1 hk; omega)
  calc S.card.choose k ≤ S.card ^ k := Nat.choose_le_pow _ _
    _ ≤ S.card ^ k * m.choose k := Nat.le_mul_of_pos_right _ h1

end Erdos408
