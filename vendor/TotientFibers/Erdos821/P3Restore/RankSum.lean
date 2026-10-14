import Erdos821.S2.RankCount
import Erdos821.Blueprint.Graph

/-! Finite equality-rank summation: low ranks by a polynomial bound, high ranks by a
geometric tail. Purely finite; no analytic input. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Restore

open Erdos821.Blueprint.Graph

/-- The rank-r absolute Möbius count, in the blueprint names and as a real bound. -/
theorem rank_coefficient_real (a r : ℕ) :
    (∑ π ∈ (Finset.univ.powerset.powerset.filter
        (fun π : Finset (Finset (Fin a)) => BirthCollection π)).filter
          (fun π => birthRank π = r),
      ((birthMobius π).natAbs : ℝ)) ≤ (a : ℝ) ^ (2 * r) := by
  rw [Finset.filter_filter]
  have h := Erdos821.S2.rank_coefficient_count a r
  have h' : (∑ π ∈ Finset.univ.powerset.powerset.filter
      (fun π : Finset (Finset (Fin a)) => BirthCollection π ∧ birthRank π = r),
        (birthMobius π).natAbs) ≤ a ^ (2 * r) := h
  exact_mod_cast h'

theorem norm_birthMobius {a : ℕ} (π : Finset (Finset (Fin a))) :
    ‖(birthMobius π : ℂ)‖ = ((birthMobius π).natAbs : ℝ) := by
  rw [Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]

/-- Split the Möbius-weighted rank expansion at rank `r0`. -/
theorem rank_sum_bound {a : ℕ} (low : Finset (Finset (Fin a)) → ℂ) (X Y Z q : ℝ) (r0 : ℕ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hq : 0 ≤ q) (hV : (a : ℝ) ^ 2 * q < 1)
    (hlow : ∀ π : Finset (Finset (Fin a)), BirthCollection π → birthRank π < r0 →
      ‖low π‖ ≤ X * Y ^ birthRank π)
    (hhigh : ∀ π : Finset (Finset (Fin a)), BirthCollection π →
      ‖low π‖ ≤ Z * q ^ birthRank π) :
    ‖∑ π ∈ Finset.univ.powerset.powerset.filter BirthCollection,
        (birthMobius π : ℂ) * low π‖ ≤
      r0 * X * (max 1 ((a : ℝ) ^ 2 * Y)) ^ r0 +
        Z * ((a : ℝ) ^ 2 * q) ^ r0 / (1 - (a : ℝ) ^ 2 * q) := by
  set 𝒞 := Finset.univ.powerset.powerset.filter
    (fun π : Finset (Finset (Fin a)) => BirthCollection π) with h𝒞
  set M := max 1 ((a : ℝ) ^ 2 * Y) with hM
  set V := (a : ℝ) ^ 2 * q with hVdef
  let f : ℕ → ℝ := fun r => if r < r0 then X * Y ^ r else Z * q ^ r
  have hf0 : ∀ r, 0 ≤ f r := by
    intro r
    simp only [f]
    split_ifs
    · exact mul_nonneg hX (pow_nonneg hY _)
    · exact mul_nonneg hZ (pow_nonneg hq _)
  have hterm : ∀ π ∈ 𝒞, ‖(birthMobius π : ℂ) * low π‖ ≤
      ((birthMobius π).natAbs : ℝ) * f (birthRank π) := by
    intro π hπ
    have hbc : BirthCollection π := (Finset.mem_filter.mp hπ).2
    rw [norm_mul, norm_birthMobius]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    simp only [f]
    split_ifs with h
    · exact hlow π hbc h
    · exact hhigh π hbc
  set t := 𝒞.image birthRank with ht
  have hfib : ∑ π ∈ 𝒞, ((birthMobius π).natAbs : ℝ) * f (birthRank π) =
      ∑ r ∈ t, (∑ π ∈ 𝒞.filter (fun π => birthRank π = r),
        ((birthMobius π).natAbs : ℝ)) * f r := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := 𝒞) (t := t) (g := birthRank)
      (fun π hπ => Finset.mem_image_of_mem _ hπ)]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro π hπ
    rw [(Finset.mem_filter.mp hπ).2]
  have hcount : ∀ r, ∑ π ∈ 𝒞.filter (fun π => birthRank π = r),
      ((birthMobius π).natAbs : ℝ) ≤ (a : ℝ) ^ (2 * r) := fun r => rank_coefficient_real a r
  have hM1 : 1 ≤ M := le_max_left _ _
  have hlowsum : ∑ r ∈ t.filter (· < r0), (a : ℝ) ^ (2 * r) * f r ≤ r0 * X * M ^ r0 := by
    have hle : ∀ r ∈ t.filter (· < r0), (a : ℝ) ^ (2 * r) * f r ≤ X * M ^ r0 := by
      intro r hr
      have hr0 : r < r0 := (Finset.mem_filter.mp hr).2
      have hfr : f r = X * Y ^ r := if_pos hr0
      rw [hfr]
      calc (a : ℝ) ^ (2 * r) * (X * Y ^ r) = X * ((a : ℝ) ^ 2 * Y) ^ r := by
            rw [pow_mul, mul_pow]; ring
        _ ≤ X * M ^ r := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hY)
              (le_max_right _ _) r) hX
        _ ≤ X * M ^ r0 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 hr0.le) hX
    have hcard : (t.filter (· < r0)).card ≤ r0 := by
      calc (t.filter (· < r0)).card ≤ (Finset.range r0).card := by
            apply Finset.card_le_card
            intro r hr
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2
        _ = r0 := Finset.card_range r0
    calc ∑ r ∈ t.filter (· < r0), (a : ℝ) ^ (2 * r) * f r
        ≤ (t.filter (· < r0)).card • (X * M ^ r0) := Finset.sum_le_card_nsmul _ _ _ hle
      _ = ((t.filter (· < r0)).card : ℝ) * (X * M ^ r0) := nsmul_eq_mul _ _
      _ ≤ (r0 : ℝ) * (X * M ^ r0) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
          (mul_nonneg hX (pow_nonneg (by linarith) _))
      _ = r0 * X * M ^ r0 := by ring
  have hV0 : 0 ≤ V := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hq
  have hhighsum : ∑ r ∈ t.filter (fun r => ¬ r < r0), (a : ℝ) ^ (2 * r) * f r ≤
      Z * V ^ r0 / (1 - V) := by
    have heq : ∀ r ∈ t.filter (fun r => ¬ r < r0), (a : ℝ) ^ (2 * r) * f r = Z * V ^ r := by
      intro r hr
      have hr0 : ¬ r < r0 := (Finset.mem_filter.mp hr).2
      have hfr : f r = Z * q ^ r := if_neg hr0
      rw [hfr, hVdef, pow_mul, mul_pow]
      ring
    rw [Finset.sum_congr rfl heq, ← Finset.mul_sum, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hZ
    calc ∑ r ∈ t.filter (fun r => ¬ r < r0), V ^ r
        ≤ ∑ r ∈ Finset.Ico r0 (t.sup id + 1), V ^ r := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro r hr
            have hr' := Finset.mem_filter.mp hr
            apply Finset.mem_Ico.mpr
            refine ⟨Nat.le_of_not_lt hr'.2, Nat.lt_succ_of_le ?_⟩
            exact Finset.le_sup (f := id) hr'.1
          · intro r _ _
            exact pow_nonneg hV0 r
      _ ≤ V ^ r0 / (1 - V) := geom_sum_Ico_le_of_lt_one hV0 hV
  calc ‖∑ π ∈ 𝒞, (birthMobius π : ℂ) * low π‖
      ≤ ∑ π ∈ 𝒞, ‖(birthMobius π : ℂ) * low π‖ := norm_sum_le _ _
    _ ≤ ∑ π ∈ 𝒞, ((birthMobius π).natAbs : ℝ) * f (birthRank π) := Finset.sum_le_sum hterm
    _ = _ := hfib
    _ ≤ ∑ r ∈ t, (a : ℝ) ^ (2 * r) * f r :=
        Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_right (hcount r) (hf0 r))
    _ = ∑ r ∈ t.filter (· < r0), (a : ℝ) ^ (2 * r) * f r +
          ∑ r ∈ t.filter (fun r => ¬ r < r0), (a : ℝ) ^ (2 * r) * f r :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ _ := add_le_add hlowsum hhighsum


end Erdos821.P3Restore
