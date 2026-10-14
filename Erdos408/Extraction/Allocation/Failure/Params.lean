import Erdos408.Extraction.Allocation.Failure.Bound

/-!
# The parameters of E6 at large `x`

Bounds for the quantities of the free-factor bound in terms of `L = log x`,
`T = log L` and `s = log T`:

* `∑_{p ≤ Y} 1/p ≤ log log Y + C` (Mertens), so the omitted Bonferroni
  envelope at depth `R + 1 ≥ 6 T` is `ε ≤ e^{8 (T + C)} / 8^{R+1}`;
* the roundings: `#{u ⊆ 𝒫 : |u| ≤ R + 1} ≤ (Y + 1)^{R+1}` and
  `#{K ⊆ g : |K| ≤ 2} ≤ (|g| + 1)²`;
* `1/γ ≤ C_γ T^{21}` with `C_γ = 4 (8 |C_h| + 11) / c`, and `D_j γ L ≥ 1`.
-/

namespace Erdos408

open Finset Filter Real

noncomputable section

/-- Mertens: `∑_{p ≤ Y} 1/p ≤ log log Y + C`. -/
lemma exists_sum_one_div_primesIcc_le : ∃ C : ℝ, ∀ Y : ℝ, 2 ≤ Y →
    ∑ p ∈ primesIcc 2 Y, (1 : ℝ) / p ≤ Real.log (Real.log Y) + C := by
  obtain ⟨E, hE, hM⟩ := mertens_second
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨3 / 2 + E / Real.log 2, fun Y hY => ?_⟩
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hsplit : primesIcc 2 Y ⊆ insert 2 (primesIoc 2 Y) := by
    intro p hp
    obtain ⟨hpr, h1, h2⟩ := mem_primesIcc.1 hp
    rcases eq_or_lt_of_le (show (2 : ℝ) ≤ p from h1) with h | h
    · rw [show p = 2 by exact_mod_cast h.symm]
      exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_primesIoc.2 ⟨hpr, h, h2⟩)
  have hlog2 : -Real.log (Real.log 2) ≤ 1 := by
    have := Real.add_one_le_exp (-Real.log (Real.log 2))
    rw [Real.exp_neg, Real.exp_log hl2] at this
    have := Real.log_two_gt_d9
    have : (Real.log 2)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hl2 (by norm_num)]
      linarith
    linarith
  calc ∑ p ∈ primesIcc 2 Y, (1 : ℝ) / p ≤ ∑ p ∈ insert 2 (primesIoc 2 Y), (1 : ℝ) / p :=
        sum_le_sum_of_subset_of_nonneg hsplit fun _ _ _ => by positivity
    _ = 1 / 2 + ∑ p ∈ primesIoc 2 Y, (1 : ℝ) / p := by
        rw [sum_insert (by simp [mem_primesIoc])]
        norm_num
    _ ≤ 1 / 2 + (Real.log (Real.log Y / Real.log 2) + E / Real.log 2) := by
        have := (abs_le.1 (hM 2 Y le_rfl hY)).2
        linarith
    _ ≤ _ := by
        rw [Real.log_div hlY.ne' hl2.ne']
        linarith

/-- Rankin at `z = 8`: `ε ≤ exp(8 ∑_{p ∈ S} 1/p) / 8^{R+1}`. -/
lemma sum_powersetCard_le_exp (S : Finset ℕ) (R : ℕ) :
    ∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p ≤
      Real.exp (8 * ∑ p ∈ S, (1 : ℝ) / p) / 8 ^ (R + 1) := by
  refine (sum_powersetCard_prod_le S (R + 1) (fun p _ => by positivity) (by norm_num :
    (0 : ℝ) < 8)).trans ?_
  gcongr
  rw [mul_sum, exp_sum]
  exact prod_le_prod₀ (fun p _ => by positivity) fun p _ => by
    rw [add_comm]
    exact add_one_le_exp _

/-- At most `Y` primes up to `Y`. -/
lemma card_primesIcc_le {Y : ℝ} (hY : 0 ≤ Y) : ((primesIcc 2 Y).card : ℝ) ≤ Y := by
  have h1 : (primesIcc 2 Y).card ≤ ⌊Y⌋₊ := by
    refine (card_filter_le _ _).trans ?_
    rw [Nat.card_Icc]
    have : ⌈(2 : ℝ)⌉₊ = 2 := by norm_num
    omega
  exact (Nat.cast_le.2 h1).trans (Nat.floor_le hY)

/-- `#{u ⊆ S : |u| ≤ m} ≤ (Y + 1)^m` for the primes up to `Y`. -/
lemma card_filter_powerset_primesIcc_le {Y : ℝ} (hY : 0 ≤ Y) (m : ℕ) :
    (((primesIcc 2 Y).powerset.filter (·.card ≤ m)).card : ℝ) ≤ (Y + 1) ^ m := by
  have := card_filter_powerset_card_le (primesIcc 2 Y) m
  calc (((primesIcc 2 Y).powerset.filter (·.card ≤ m)).card : ℝ)
      ≤ (((primesIcc 2 Y).card + 1) ^ m : ℕ) := by exact_mod_cast this
    _ ≤ (Y + 1) ^ m := by
        push_cast
        gcongr
        exact card_primesIcc_le hY

/-- `#{K ⊆ g : |K| ≤ 2} ≤ (|g| + 1)²`. -/
lemma card_lowSubsets_le (g : Finset ℕ) : ((lowSubsets g).card : ℝ) ≤ ((g.card : ℝ) + 1) ^ 2 := by
  have := card_filter_powerset_card_le g 2
  exact_mod_cast this

/-- `4 h + 3 ≤ (8 |C_h| + 11) T`. -/
lemma sieveDepth_le {Ch x : ℝ} (hT : 1 ≤ logLog x) :
    4 * (sieveDepth Ch x : ℝ) + 3 ≤ (8 * |Ch| + 11) * logLog x := by
  have hs : logLogLog x ≤ logLog x := by
    have := Real.log_le_sub_one_of_pos (show 0 < logLog x by linarith)
    rw [logLogLog]
    linarith
  have hs0 : 0 ≤ logLogLog x := by rw [logLogLog]; exact Real.log_nonneg hT
  have hh : (sieveDepth Ch x : ℝ) ≤ 2 * (|Ch| * logLog x + 1) := by
    rw [sieveDepth]
    push_cast
    have h1 : (⌈Ch * logLogLog x⌉₊ : ℝ) ≤ |Ch| * logLogLog x + 1 := by
      refine (Nat.cast_le.2 (Nat.ceil_mono (show Ch * logLogLog x ≤ |Ch| * logLogLog x from
        mul_le_mul_of_nonneg_right (le_abs_self _) hs0))).trans ?_
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have h2 : |Ch| * logLogLog x ≤ |Ch| * logLog x := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    linarith
  nlinarith [abs_nonneg Ch]

/-- `γ > 0` and `1/γ ≤ C_γ T^{21}`, with `C_γ = 4 (8 |C_h| + 11) / c`. -/
lemma presieveExponent_facts {c Ch x : ℝ} (hc : 0 < c) (hT : 1 ≤ logLog x) :
    0 < presieveExponent c Ch x ∧
      1 / presieveExponent c Ch x ≤ 4 * (8 * |Ch| + 11) / c * logLog x ^ 21 := by
  have hT0 : 0 < logLog x := by linarith
  have hden : 0 < 4 * (sieveDepth Ch x : ℝ) + 3 := by positivity
  have hγ : presieveExponent c Ch x =
      c / (4 * logLog x ^ 20 * (4 * (sieveDepth Ch x : ℝ) + 3)) := by
    rw [presieveExponent]
    field_simp
  refine ⟨by rw [hγ]; positivity, ?_⟩
  rw [hγ, one_div_div, div_le_iff₀ hc]
  have := sieveDepth_le (Ch := Ch) hT
  have h20 : 0 < logLog x ^ 20 := by positivity
  calc 4 * logLog x ^ 20 * (4 * (sieveDepth Ch x : ℝ) + 3)
      ≤ 4 * logLog x ^ 20 * ((8 * |Ch| + 11) * logLog x) := by gcongr
    _ = 4 * (8 * |Ch| + 11) / c * logLog x ^ 21 * c := by field_simp

end

end Erdos408
