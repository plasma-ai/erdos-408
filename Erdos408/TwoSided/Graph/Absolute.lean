import Erdos408.TwoSided.Graph.BoundsDamping
import Erdos408.TwoSided.Graph.Endpoint

/-!
# The absolute pattern bound

Lemma G2a of `blueprint/two_sided_correlation.md` §4.2: bounding every factor of a pattern
pairing absolutely, `|⟨f, 𝒜 g_X⟩| ≤ sup|K| · X L^{C_abs}`, with an exponent that may depend
on `J`. It is used only for the Mellin tail of S2, whose precision is chosen after `J`, so it
replaces WD Lemma 3.4. The generic bound is `GraphBounds.norm_patternPairing_le`
(`Graph/BoundsDamping.lean`).
-/

namespace Erdos408.TwoSided

open Filter

/-- **Lemma G2a (absolute pattern bound).** For every `J` there is `C_abs` such that,
eventually, for groups as in (6.1), every pattern `C` with any kernel `|K| ≤ κ_K`, every
frequency `ζ`, every dyad `X = 2^m`, every `|f| ≤ 1` and every clipped core,
`|patternPairing P q₀ C K ζ S_X f g_X| ≤ κ_K X L^{C_abs}`. By
`GraphBounds.norm_patternPairing_le`, the pairing is at most
`|S_X| κ_K L^{B₀} (max(1, 1/v₋)^{2M} c²)^{s_P}` with `z^M q₀^{z/2} ≤ c q₀^{M/2}` for all
`z`, and `|S_X| ≤ L X`, `s_P ≤ 2C₀T`. -/
theorem exists_norm_patternPairing_le (q₀ c₀ C₀ vlo vhi B₀ : ℝ) (hq₀ : 0 < q₀)
    (hq₀₁ : q₀ < 1) (hvlo : 0 < vlo) (J : ℕ) :
    ∃ Cabs : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (C : ι → Finset (Fin J))
          (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
          (κK : ℝ), (∀ p p' a, ‖K p p' a‖ ≤ κK) →
        ∀ (G : ℕ → ℝ), CoreAdmissible B₀ x P G →
        ∀ m ∈ dyads x, ∀ (ζ : ℝ) (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
          ‖patternPairing P q₀ C K ζ (dyadSource (2 ^ m)) f
              (targetEndpoint q₀ P J G (2 ^ m))‖ ≤
            κK * 2 ^ m * Real.log x ^ Cabs := by
  obtain ⟨c, hc1, hc⟩ := GraphBounds.exists_pow_mul_sqrt_pow_le hq₀ hq₀₁ (J + 1)
  set K₁ := (max 1 vlo⁻¹) ^ (2 * (J + 1)) * c ^ 2
  have hK₁ : 1 ≤ K₁ :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_left _ _)) (one_le_pow₀ hc1)
  refine ⟨B₀ + 1 + 2 * C₀ * Real.log K₁, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 2, eventually_gt_atTop 1]
    with x hL2 hx1 ι _ _ P big hP C K κK hK G hG m _ ζ f hf
  set X : ℝ := 2 ^ m
  set L := Real.log x
  set T := Real.log L
  have hX1 : 1 ≤ X := one_le_pow₀ (by norm_num)
  have hL0 : 0 < L := by linarith
  have hT0 : 0 ≤ T := Real.log_nonneg (by linarith)
  have hκ : 0 ≤ κK := (norm_nonneg _).trans (hK 0 0 0)
  have h := GraphBounds.norm_patternPairing_le P hvlo (fun g => (hP.2.2.2.2.2.1 g).1) hq₀ hq₀₁
    hc hc1 C K hK ζ (dyadSource X) hf (norm_targetEndpoint_le hx1 hq₀₁ hG J X)
  -- `|S_X| ≤ X + 1 ≤ L X`
  have hS : (Finset.card (dyadSource X) : ℝ) ≤ L * X := by
    unfold dyadSource
    rw [Nat.card_Ico, Nat.cast_sub (Nat.ceil_mono (by linarith))]
    have h₁ := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * X by linarith)
    have h₂ := Nat.le_ceil X
    nlinarith
  -- `s_P ≤ 2 C₀ T`, so `K₁^{s_P} ≤ L^{2 C₀ log K₁}`
  have hs : (Fintype.card ι : ℝ) ≤ 2 * C₀ * T := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ big)
    rw [Finset.card_univ] at h
    have h₁ := hP.2.2.1
    have h₂ := hP.2.2.2.2.1
    rw [← h]
    push_cast
    linarith
  have hKs : K₁ ^ Fintype.card ι ≤ L ^ (2 * C₀ * Real.log K₁) := by
    rw [← Real.rpow_natCast]
    calc K₁ ^ (Fintype.card ι : ℝ) ≤ K₁ ^ (2 * C₀ * T) :=
          Real.rpow_le_rpow_of_exponent_le hK₁ hs
      _ = L ^ (2 * C₀ * Real.log K₁) := by
          rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hL0]
          congr 1
          ring
  refine h.trans ?_
  have hLB : 0 ≤ L ^ B₀ := Real.rpow_nonneg hL0.le _
  calc (Finset.card (dyadSource X) : ℝ) * κK * L ^ B₀ * K₁ ^ Fintype.card ι
      ≤ (L * X) * κK * L ^ B₀ * L ^ (2 * C₀ * Real.log K₁) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS hκ) hLB)
          hKs (pow_nonneg (by linarith) _) ?_
        have : 0 ≤ L * X := by positivity
        positivity
    _ = κK * X * L ^ (B₀ + 1 + 2 * C₀ * Real.log K₁) := by
        rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one]
        ring

end Erdos408.TwoSided
