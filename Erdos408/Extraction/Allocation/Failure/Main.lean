import Erdos408.Extraction.Allocation.Failure.Eventually

/-!
# E6: the failure mass

With `c₁ = 1/4`, `θ = 1 - e⁻¹` and `a = θ / 4500`: for large `x` and
`2 ≤ j ≤ J_c`, each family's free-factor sum is at most
`X/L (2 e^{aT/4} (e^{-aT} + e^{-T}) + e^{-T})`, the Chernoff factor is
`e^{(a/4) T}`, and the failure mass is at most `20 κ (x/L) L^{-a/2}`.
-/

namespace Erdos408

open Finset Filter Real

noncomputable section

/-- The decay exponent `a = θ / 4500` of E6. -/
def failureDecay : ℝ := chernoffTheta / 4500

/-- `a > 0`. -/
lemma failureDecay_pos : 0 < failureDecay := by
  unfold failureDecay
  have := chernoffTheta_pos
  positivity

/-- `a ≤ 1`. -/
lemma failureDecay_le_one : failureDecay ≤ 1 := by
  unfold failureDecay
  have := chernoffTheta_le_one
  linarith

/-- A family with at least `T/15` groups fails with model probability at most `e^{-aT}`. -/
lemma one_sub_pow_le_exp {n : ℕ} {T : ℝ} (hn : T / 15 ≤ n) :
    (1 - chernoffTheta * (1 / 4) / 75) ^ n ≤ Real.exp (-(failureDecay * T)) := by
  have hθ := chernoffTheta_pos
  have hθ1 := chernoffTheta_le_one
  have h0 : 0 ≤ 1 - chernoffTheta * (1 / 4) / 75 := by linarith
  calc (1 - chernoffTheta * (1 / 4) / 75) ^ n ≤ Real.exp (-(chernoffTheta * (1 / 4) / 75)) ^ n :=
        pow_le_pow_left₀ h0 (one_sub_le_exp_neg _) n
    _ = Real.exp (-(chernoffTheta * (1 / 4) / 75 * n)) := by
        rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-(failureDecay * T)) := by
        refine exp_le_exp.2 ?_
        unfold failureDecay
        have : chernoffTheta / 4500 * T ≤ chernoffTheta * (1 / 4) / 75 * n := by
          have := mul_le_mul_of_nonneg_left hn (show 0 ≤ chernoffTheta / 300 by positivity)
          linarith
        linarith

/-- For large `x`, each family's free-factor sum is small, uniformly in `2 ≤ j ≤ J_c`. -/
theorem eventually_freeFactorSum_le {c : ℝ} (hc : 0 < c) (Ch Cj κ : ℝ) (hκ : 1 < κ) :
    ∀ᶠ x : ℝ in atTop, ∀ j' : ℕ, j' + 1 ≤ compositeCutoff Cj x →
      ∀ F ∈ ({smallGroups x, bigGroups x} : Finset (Finset (Finset ℕ))),
        freeFactorSum x (presieveExponent c Ch x) (1 / 4) j' (⌊κ * x⌋₊ + 1) F ≤
          (⌊κ * x⌋₊ + 1 : ℕ) / Real.log x *
            (2 * Real.exp (failureDecay * logLog x / 4) *
              (Real.exp (-(failureDecay * logLog x)) + Real.exp (-logLog x)) +
                Real.exp (-logLog x)) := by
  filter_upwards [eventually_candidateGroups, eventually_sideGroup, eventually_card_families_ge,
    eventually_groups_small κ hκ, eventually_presieveExponent hc Ch,
    eventually_one_le_dampedDensity_mul hc Ch, eventually_candKappa_pow_mul_le,
    eventually_delta_le hc Ch κ hκ, eventually_free_factors_le hc Ch Cj κ hκ failureDecay_pos,
    eventually_err_le hc Ch Cj κ hκ, eventually_gt_atTop 1, eventually_le_log 1]
    with x hgroups hside hcard hsmall hγ hDγL hκE hδ hH herr hx hlogx j' hj' F hF
  obtain ⟨hγ0, hγ1, -⟩ := hγ
  obtain ⟨hgS, hPX, hxX, -, -⟩ := hsmall
  have hFC : F ⊆ candidateGroups x := by
    rcases mem_insert.1 hF with h | h
    · rw [h]; exact subset_union_left
    · rw [mem_singleton.1 h]; exact subset_union_right
  have hFT : (F.card : ℝ) ≤ logLog x ∧ logLog x / 15 ≤ F.card := by
    rcases mem_insert.1 hF with h | h
    · rw [h]; exact ⟨hgroups.2.2.2.2.1, hcard.1⟩
    · rw [mem_singleton.1 h]; exact ⟨hgroups.2.2.2.2.2.1, hcard.2⟩
  exact freeFactorSum_le_of_facts (⌈6 * logLog x⌉₊) failureDecay hx hlogx hγ0 hγ1 hside hFC
    (fun g hg => (hgS g (hFC hg)).1) hxX hPX (hDγL (j' + 1) (by omega)) (hκE (j' + 1) (by omega))
    (one_sub_pow_le_exp hFT.2) (hδ F.card hFT.1) (hH j' hj')
    (herr j' hj' F hFT.1 fun g hg => (hgS g (hFC hg)).2)

/-- The final arithmetic: `e^{aT/4} (S₁ + S₂) ≤ 20 κ (x/L) L^{-a/2}`. -/
lemma final_le {a T L X x κ S₁ S₂ : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hT : 0 ≤ T)
    (hLT : Real.exp T = L) (hX0 : 0 ≤ X) (hX : X ≤ 2 * κ * x)
    (hS₁ : S₁ ≤ X / L * (2 * Real.exp (a * T / 4) * (Real.exp (-(a * T)) + Real.exp (-T)) +
      Real.exp (-T)))
    (hS₂ : S₂ ≤ X / L * (2 * Real.exp (a * T / 4) * (Real.exp (-(a * T)) + Real.exp (-T)) +
      Real.exp (-T))) :
    Real.exp (a / 4 * T) * (S₁ + S₂) ≤ 20 * κ * (x / L) * L ^ (-(a / 2)) := by
  have hL0 : 0 < L := by rw [← hLT]; exact exp_pos T
  have hxκ : 0 ≤ 2 * κ * x := hX0.trans hX
  -- `e^{-T} ≤ e^{-aT}` and the bracket is at most `5 e^{-3aT/4}`
  have h1 : Real.exp (-T) ≤ Real.exp (-(a * T)) := exp_le_exp.2 (by nlinarith)
  have h2 : Real.exp (-(a * T)) ≤ Real.exp (-(3 * a * T / 4)) := exp_le_exp.2 (by nlinarith)
  have hB : 2 * Real.exp (a * T / 4) * (Real.exp (-(a * T)) + Real.exp (-T)) + Real.exp (-T) ≤
      5 * Real.exp (-(3 * a * T / 4)) := by
    have h3 : Real.exp (a * T / 4) * Real.exp (-(a * T)) = Real.exp (-(3 * a * T / 4)) := by
      rw [← exp_add]; ring_nf
    have h4 : 0 ≤ Real.exp (a * T / 4) := (exp_pos _).le
    have h5 : Real.exp (a * T / 4) * Real.exp (-T) ≤ Real.exp (a * T / 4) * Real.exp (-(a * T)) :=
      mul_le_mul_of_nonneg_left h1 h4
    nlinarith
  have hXL : 0 ≤ X / L := div_nonneg hX0 hL0.le
  have hsum : S₁ + S₂ ≤ X / L * (10 * Real.exp (-(3 * a * T / 4))) := by
    have := mul_le_mul_of_nonneg_left hB hXL
    linarith
  have hrpow : L ^ (-(a / 2)) = Real.exp (-(a / 2 * T)) := by
    rw [rpow_def_of_pos hL0, ← hLT, log_exp]
    ring_nf
  rw [hrpow]
  calc Real.exp (a / 4 * T) * (S₁ + S₂)
      ≤ Real.exp (a / 4 * T) * (X / L * (10 * Real.exp (-(3 * a * T / 4)))) :=
        mul_le_mul_of_nonneg_left hsum (exp_pos _).le
    _ = 10 * (X / L) * Real.exp (-(a / 2 * T)) := by
        rw [show Real.exp (-(a / 2 * T)) = Real.exp (a / 4 * T) * Real.exp (-(3 * a * T / 4)) by
          rw [← exp_add]; ring_nf]
        ring
    _ ≤ 10 * (2 * κ * x / L) * Real.exp (-(a / 2 * T)) := by
        gcongr
    _ = 20 * κ * (x / L) * Real.exp (-(a / 2 * T)) := by ring

end

end Erdos408
