import Erdos408.Extraction.Allocation.Groups

/-!
# Sharper facts about the candidate groups

E6 needs two facts beyond `GroupFacts`:

* every candidate group has reciprocal mass at most `4/5` (by Mertens it is
  `log 2 + O(1/y)` at scale `y`), so the `u`-side model mass of a group stays
  below `1` and the depth-two Bonferroni bound has positive expectation;
* each family has at least `T/15` groups: the scales `2^i L^a` run over
  `⌊(b - a) T / log 2⌋` values of `i`, and distinct scales give disjoint
  nonempty groups.
-/

namespace Erdos408

open Finset Filter Real

/-- The reciprocal mass of a dyadic group at a large scale is at most `4/5`. -/
lemma harmonicMass_dyadicGroup_le : ∃ Y₀ : ℝ, ∀ y : ℝ, Y₀ ≤ y →
    harmonicMass (dyadicGroup y) ≤ 4 / 5 := by
  obtain ⟨E, hE, hM⟩ := mertens_second
  refine ⟨10 * (E + 1) + 4, fun y hy => ?_⟩
  have hy4 : 4 ≤ y := by linarith
  have hey : 2 ≤ Real.exp y - 1 := by
    have := add_one_le_exp y
    linarith
  have hlog1 : y - 1 ≤ Real.log (Real.exp y - 1) := by
    rw [← log_exp (y - 1)]
    refine log_le_log (exp_pos _) ?_
    rw [exp_sub]
    have he : 2 ≤ Real.exp 1 := by linarith [exp_one_gt_d9]
    rw [div_le_iff₀ (exp_pos 1)]
    nlinarith [exp_pos y]
  have hsub : dyadicGroup y ⊆ primesIoc (Real.exp y - 1) (Real.exp (2 * y)) := by
    intro q hq
    obtain ⟨hp, h1, h2⟩ := mem_dyadicGroup.1 hq
    exact mem_primesIoc.2 ⟨hp, by linarith, h2.le⟩
  have hS := sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => (1 : ℝ) / q) hsub
    fun q _ _ => by positivity
  have hexp : Real.exp y - 1 ≤ Real.exp (2 * y) := by
    have := exp_le_exp.2 (show y ≤ 2 * y by linarith)
    linarith
  have hm := (abs_le.1 (hM (Real.exp y - 1) (Real.exp (2 * y)) hey hexp)).2
  rw [log_exp] at hm
  have hl0 : 0 < y - 1 := by linarith
  -- `log (2y / log(e^y - 1)) ≤ log 2 + 1/(y - 1)`
  have hl : Real.log (2 * y / Real.log (Real.exp y - 1)) ≤ Real.log 2 + 1 / (y - 1) := by
    have h1 : 2 * y / Real.log (Real.exp y - 1) ≤ 2 * (1 + 1 / (y - 1)) := by
      rw [div_le_iff₀ (by linarith)]
      have : 2 * (1 + 1 / (y - 1)) * (y - 1) = 2 * y := by field_simp; ring
      nlinarith
    calc Real.log (2 * y / Real.log (Real.exp y - 1)) ≤ Real.log (2 * (1 + 1 / (y - 1))) :=
          log_le_log (div_pos (by linarith) (by linarith)) h1
      _ = Real.log 2 + Real.log (1 + 1 / (y - 1)) := log_mul (by norm_num) (by positivity)
      _ ≤ Real.log 2 + 1 / (y - 1) := by
          have := log_le_sub_one_of_pos (show 0 < 1 + 1 / (y - 1) by positivity)
          linarith
  have hE' : E / Real.log (Real.exp y - 1) ≤ E / (y - 1) :=
    div_le_div_of_nonneg_left hE hl0 hlog1
  have hsmall : 1 / (y - 1) + E / (y - 1) ≤ 1 / 10 := by
    rw [← add_div, div_le_iff₀ hl0]
    linarith
  have := log_two_lt_d9
  unfold harmonicMass
  linarith

/-- For large `x`, every candidate group has reciprocal mass at most `4/5`. -/
lemma eventually_harmonicMass_le : ∀ᶠ x : ℝ in atTop,
    ∀ g ∈ candidateGroups x, harmonicMass g ≤ 4 / 5 := by
  obtain ⟨Y₀, hY₀⟩ := harmonicMass_dyadicGroup_le
  have hL : Tendsto (fun x : ℝ => Real.log x ^ (28 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  filter_upwards [hL.eventually_ge_atTop Y₀, eventually_le_log 1] with x hY hx g hg
  obtain ⟨y, rfl, h1, -⟩ := exists_scale_of_mem_candidateGroups hx hg
  exact hY₀ y (hY.trans h1)

/-- A doubling family has at least `(b - a) T / log 2 - 1` groups, given that all its groups
are nonempty. -/
lemma card_doublingGroups_ge {x : ℝ} (hx : 1 ≤ Real.log x) {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ i : ℕ, 2 ^ (i + 1) * Real.log x ^ a ≤ Real.log x ^ b →
      (dyadicGroup (2 ^ i * Real.log x ^ a)).Nonempty) :
    (b - a) * logLog x / Real.log 2 - 1 ≤ ((doublingGroups x a b).card : ℝ) := by
  set z := Real.logb 2 (Real.log x ^ (b - a)) with hz
  have hL0 : 0 < Real.log x := by linarith
  have hlog : z = (b - a) * logLog x / Real.log 2 := by
    rw [hz, Real.logb, Real.log_rpow hL0, logLog]
  have hz0 : 0 ≤ z := Real.logb_nonneg (by norm_num) (Real.one_le_rpow hx (by linarith))
  -- every `i < ⌊z⌋` passes the filter
  have hfilt : (range ⌊z⌋₊).filter (fun i => 2 ^ (i + 1) * Real.log x ^ a ≤ Real.log x ^ b) =
      range ⌊z⌋₊ := by
    refine filter_true_of_mem fun i hi => ?_
    have hi' : ((i + 1 : ℕ) : ℝ) ≤ z := by
      have := mem_range.1 hi
      have h1 : ((i + 1 : ℕ) : ℝ) ≤ (⌊z⌋₊ : ℝ) := by exact_mod_cast this
      exact h1.trans (Nat.floor_le hz0)
    have h2 : (2 : ℝ) ^ (i + 1) ≤ Real.log x ^ (b - a) := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hi'
      rw [Real.rpow_natCast, hz, Real.rpow_logb (by norm_num) (by norm_num)
        (Real.rpow_pos_of_pos hL0 _)] at this
      exact this
    have h3 : Real.log x ^ b = Real.log x ^ (b - a) * Real.log x ^ a := by
      rw [← Real.rpow_add hL0]
      ring_nf
    rw [h3]
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_pos_of_pos hL0 a).le
  have hinj : Set.InjOn (fun i : ℕ => dyadicGroup (2 ^ i * Real.log x ^ a))
      ((range ⌊z⌋₊).filter (fun i => 2 ^ (i + 1) * Real.log x ^ a ≤ Real.log x ^ b)) := by
    intro i hi i' hi' h
    by_contra hii'
    have hLa : 0 < Real.log x ^ a := Real.rpow_pos_of_pos hL0 a
    have key : ∀ i i' : ℕ, i < i' → 2 * (2 ^ i * Real.log x ^ a) ≤ 2 ^ i' * Real.log x ^ a := by
      intro i i' hlt
      rw [← mul_assoc, ← pow_succ']
      gcongr
      · norm_num
      · exact hlt
    have hdisj : Disjoint (dyadicGroup (2 ^ i * Real.log x ^ a))
        (dyadicGroup (2 ^ i' * Real.log x ^ a)) := by
      rcases lt_or_gt_of_ne hii' with hlt | hlt
      · exact disjoint_dyadicGroup (key i i' hlt)
      · exact (disjoint_dyadicGroup (key i' i hlt)).symm
    simp only at h
    rw [h, disjoint_self, bot_eq_empty] at hdisj
    have := hne i' (mem_filter.1 hi').2
    rw [hdisj] at this
    exact not_nonempty_empty this
  have hcard : (doublingGroups x a b).card = ⌊z⌋₊ := by
    rw [doublingGroups, card_image_of_injOn hinj, hfilt, card_range]
  rw [hcard, ← hlog]
  have := Nat.lt_floor_add_one z
  linarith

/-- For large `x`, each family has at least `T/15` groups. -/
lemma eventually_card_families_ge : ∀ᶠ x : ℝ in atTop,
    logLog x / 15 ≤ ((smallGroups x).card : ℝ) ∧ logLog x / 15 ≤ ((bigGroups x).card : ℝ) := by
  obtain ⟨Y₀, hY₀⟩ := harmonicMass_dyadicGroup
  have hL : Tendsto (fun x : ℝ => Real.log x ^ (28 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  filter_upwards [hL.eventually_ge_atTop Y₀, eventually_le_log 1, eventually_le_logLog 200]
    with x hY hx hT
  have hL0 : 0 < Real.log x := by linarith
  -- groups at scales `≥ L^{0.28}` are nonempty
  have hne : ∀ a : ℝ, 28 / 100 ≤ a → ∀ i : ℕ, (dyadicGroup (2 ^ i * Real.log x ^ a)).Nonempty := by
    intro a ha i
    have h1 : Real.log x ^ (28 / 100 : ℝ) ≤ 2 ^ i * Real.log x ^ a := by
      have : Real.log x ^ (28 / 100 : ℝ) ≤ Real.log x ^ a := Real.rpow_le_rpow_of_exponent_le hx ha
      have h2 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      nlinarith [Real.rpow_pos_of_pos hL0 a]
    have hm := (hY₀ _ (hY.trans h1)).1
    rw [nonempty_iff_ne_empty]
    intro h
    rw [h, harmonicMass, sum_empty] at hm
    linarith
  have hlog2 := log_two_lt_d9
  have hlog2' := log_two_gt_d9
  have hT0 : 0 ≤ logLog x := by linarith
  constructor
  · have h := card_doublingGroups_ge hx (show (28 / 100 : ℝ) ≤ 35 / 100 by norm_num)
      fun i _ => hne _ (by norm_num) i
    refine le_trans ?_ h
    rw [le_sub_iff_add_le, le_div_iff₀ (by linarith)]
    nlinarith
  · have h := card_doublingGroups_ge hx (show (40 / 100 : ℝ) ≤ 45 / 100 by norm_num)
      fun i _ => hne _ (by norm_num) i
    refine le_trans ?_ h
    rw [le_sub_iff_add_le, le_div_iff₀ (by linarith)]
    nlinarith

end Erdos408
