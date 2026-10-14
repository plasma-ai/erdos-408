import Erdos408.TwoSided.Comparison.ArcsFourier

/-!
# One shifted bilinear form from the mean square

S8–S10 of `blueprint/two_sided_correlation.md` §§5.3–5.4 for abstract data: a shifted sum
`𝔅 = ∑_l c_l ∑_{Y ≤ n ≤ 2Y} f_n g_{n + D_l}` is `∫₀¹ star(F) G M` with
`M(θ) = ∑_l c_l e(-θ D_l)` (the shift identity); Parseval and the arc split (upstream
`FourierArcTask_proof`) bound it by the minor-arc bound `ε` of `M` and the arc energies of
`F`, which the local Mellin energy bounds by the mean square (6.24) of `f` at the centres
`u/r`, `1 ≤ r ≤ R`, `-R ≤ u ≤ 2R`.
-/

namespace Erdos408.TwoSided.Arcs

open MeasureTheory
open Erdos821.Blueprint.Analytic (e)
open Erdos821.P5Core (localAdditivePolynomial)

/-- The rational centres `u/r`, `1 ≤ r ≤ R`, `-R ≤ u ≤ 2R`. -/
private noncomputable def arcCentres (R : ℕ) : Finset ℝ :=
  ((Finset.Icc 1 R) ×ˢ (Finset.Icc (-(R : ℤ)) (2 * R))).image fun p => (p.2 : ℝ) / p.1

/-- There are at most `4R²` centres. -/
private theorem card_arcCentres_le (R : ℕ) : ((arcCentres R).card : ℝ) ≤ 4 * (R : ℝ) ^ 2 := by
  have h : (arcCentres R).card ≤ R * (3 * R + 1) := by
    unfold arcCentres
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Nat.card_Icc, Int.card_Icc,
      show (2 * (R : ℤ) + 1 - -(R : ℤ)).toNat = 3 * R + 1 by omega, Nat.add_sub_cancel]
  calc ((arcCentres R).card : ℝ) ≤ ((R * (3 * R + 1) : ℕ) : ℝ) := by exact_mod_cast h
    _ ≤ 4 * (R : ℝ) ^ 2 := by
        push_cast
        nlinarith [show (R : ℝ) ≤ (R : ℝ) ^ 2 by
          rcases Nat.eq_zero_or_pos R with h0 | h0
          · simp [h0]
          · nlinarith [show (1 : ℝ) ≤ R by exact_mod_cast h0]]

/-- **One shifted bilinear form (S8–S10).** For `j ≥ 4` there is `K > 0` such that: for
`10 ≤ Y`, `1 ≤ H ≤ Y/10`, `2Y ≤ T₀H`, shifts `n + D_l ∈ s'` (when `c_l ≠ 0`), energies
`∑_s |f|² ≤ A`, `∑_{s'} |g|² ≤ B`, a multiplier `M = ∑_l c_l e(-θ D_l)` with `|M| ≤ 1` on
`[0, 1]` and `|M| ≤ ε` at distance `> 1/H` from every centre, and the mean square of `f` at
most `Ξ₀ ≥ 0` at every centre,
`|∑_l c_l ∑_s f_n g_{n + D_l}| ≤ ε √A √B + 4R² √E √B` with
`E = K (Y Ξ₀ + (1 + T₀H/(2Y))^{4-j} (1/H + 2 log 4Y) A + (H/Y)² A)`. -/
theorem exists_norm_sum_shift_le (j : ℕ) (hj : 4 ≤ j) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y H T₀ ε A B Ξ₀ : ℝ) (R : ℕ) {Λ : Type} (Ls : Finset Λ) (c : Λ → ℂ)
      (D : Λ → ℕ) (s' : Finset ℕ) (f g : ℕ → ℂ),
      10 ≤ Y → 1 ≤ H → H ≤ Y / 10 → 2 * Y ≤ T₀ * H → 0 ≤ ε → 0 ≤ Ξ₀ →
      (∀ l ∈ Ls, c l ≠ 0 → ∀ n ∈ Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊, n + D l ∈ s') →
      ∑ n ∈ Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊, ‖f n‖ ^ 2 ≤ A → ∑ n ∈ s', ‖g n‖ ^ 2 ≤ B →
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖∑ l ∈ Ls, c l * e (-θ * D l)‖ ≤ 1) →
      (∀ θ ∈ Set.Icc (0 : ℝ) 1,
        (∀ (r : ℕ) (u : ℤ), 1 ≤ r → r ≤ R → -(R : ℤ) ≤ u → u ≤ 2 * R →
          1 / H < |θ - u / r|) →
        ‖∑ l ∈ Ls, c l * e (-θ * D l)‖ ≤ ε) →
      (∀ (r : ℕ) (u : ℤ), 1 ≤ r → r ≤ R →
        ∫ t in (-T₀)..T₀, ‖twistedPoly Y f (-u) r t‖ ^ 2 ≤ Ξ₀) →
      ‖∑ l ∈ Ls, c l * ∑ n ∈ Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊, f n * g (n + D l)‖ ≤
        ε * Real.sqrt A * Real.sqrt B +
          4 * (R : ℝ) ^ 2 * Real.sqrt (K * (Y * Ξ₀ +
            ((1 + T₀ * H / (2 * Y)) ^ (j - 4))⁻¹ * (1 / H + 2 * Real.log (4 * Y)) * A +
            (H / Y) ^ 2 * A)) * Real.sqrt B := by
  obtain ⟨K, hK, harc⟩ := exists_integral_norm_localAdditivePolynomial_le j hj
  refine ⟨K, hK, ?_⟩
  intro Y H T₀ ε A B Ξ₀ R Λ Ls c D s' f g hY hH hHY hT₀ hε hΞ hD hfA hgB hM₁ hMε hΞ₀
  set s := Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊ with hs
  have hY0 : 0 < Y := by linarith
  have hH0 : 0 < H := by linarith
  have hsupp : ∀ n ∈ s, Y ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Y := fun n hn =>
    ⟨Nat.ceil_le.1 (Finset.mem_Icc.1 hn).1,
      (Nat.le_floor_iff (by positivity)).1 (Finset.mem_Icc.1 hn).2⟩
  set F := localAdditivePolynomial s (fun n => star (f n)) with hF
  set G := localAdditivePolynomial s' g with hG
  set M : ℝ → ℂ := fun θ => ∑ l ∈ Ls, c l * e (-θ * D l) with hM
  have hA0 : 0 ≤ A := (Finset.sum_nonneg fun n _ => by positivity).trans hfA
  have hB0 : 0 ≤ B := (Finset.sum_nonneg fun n _ => by positivity).trans hgB
  set Z : ℝ := ((1 + T₀ * H / (2 * Y)) ^ (j - 4))⁻¹ with hZ
  have hZ0 : 0 ≤ Z := by
    have : 0 ≤ T₀ * H / (2 * Y) := div_nonneg (by linarith) (by positivity)
    positivity
  have hlog : 0 ≤ Real.log (4 * Y) := Real.log_nonneg (by linarith)
  set E : ℝ := K * (Y * Ξ₀ + Z * (1 / H + 2 * Real.log (4 * Y)) * A + (H / Y) ^ 2 * A)
    with hE
  have hE0 : 0 ≤ E := by positivity
  -- the arc energies
  have hFE : ∀ c ∈ arcCentres R, ∫ θ in (c - 1 / H)..(c + 1 / H), ‖F θ‖ ^ 2 ≤ E := by
    intro c hc
    obtain ⟨⟨r, u⟩, hru, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨hr, -⟩ := Finset.mem_product.1 hru
    obtain ⟨hr₁, hr₂⟩ := Finset.mem_Icc.1 hr
    have h := harc Y H T₀ ((u : ℝ) / r) s (fun n => star (f n)) hY hH hHY hsupp hT₀
    simp only [norm_star] at h
    have hmain : ∫ t in (-T₀)..T₀,
        ‖∑ n ∈ s, star (f n) * e ((u : ℝ) / r * n) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
          Y ^ 2 * Ξ₀ := by
      simp_rw [hs, norm_sum_star_mul_cpow hY0, mul_pow]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_neg (fun t => ‖twistedPoly Y f (-u) r t‖ ^ 2), neg_neg]
      exact mul_le_mul_of_nonneg_left (hΞ₀ r u hr₁ hr₂) (by positivity)
    refine h.trans ?_
    have hsA : ∑ n ∈ s, ‖f n‖ ^ 2 ≤ A := hfA
    calc K / Y * (∫ t in (-T₀)..T₀,
          ‖∑ n ∈ s, star (f n) * e ((u : ℝ) / r * n) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2) +
          K * Z * (1 / H + 2 * Real.log (4 * Y)) * ∑ n ∈ s, ‖f n‖ ^ 2 +
          K * (H / Y) ^ 2 * ∑ n ∈ s, ‖f n‖ ^ 2
        ≤ K / Y * (Y ^ 2 * Ξ₀) + K * Z * (1 / H + 2 * Real.log (4 * Y)) * A +
          K * (H / Y) ^ 2 * A := by gcongr
      _ = E := by
          rw [hE]
          field_simp
  -- the arc split
  have hFA : ∫ θ in (0 : ℝ)..1, ‖F θ‖ ^ 2 ≤ A := by
    rw [hF, integral_norm_localAdditivePolynomial_sq]
    simpa only [norm_star] using hfA
  have hGB : ∫ θ in (0 : ℝ)..1, ‖G θ‖ ^ 2 ≤ B := by
    rw [hG, integral_norm_localAdditivePolynomial_sq]
    exact hgB
  have hMε' : ∀ θ ∈ Set.Icc (0 : ℝ) 1, (∀ c ∈ arcCentres R, 1 / H < |θ - c|) → ‖M θ‖ ≤ ε := by
    intro θ hθ hc
    refine hMε θ hθ fun r u hr₁ hr₂ hu₁ hu₂ => hc _ (Finset.mem_image.2 ⟨(r, u), ?_, rfl⟩)
    exact Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hr₁, hr₂⟩, Finset.mem_Icc.2 ⟨hu₁, hu₂⟩⟩
  have hMcont : Continuous M := by
    simp only [hM]
    fun_prop
  have hsplit := Erdos821.P5Core.FourierArcTask_proof.2.2 F G M (arcCentres R) (1 / H) A B E ε
    (continuous_localAdditivePolynomial _ _) (continuous_localAdditivePolynomial _ _) hMcont
    (by positivity) hA0 hB0 hE0 hε hFA hGB hM₁ hMε' hFE
  rw [hF, hG, hM, integral_star_mul_mul_sum Ls c D s s' f g hD] at hsplit
  refine hsplit.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (card_arcCentres_le R)
    (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end Erdos408.TwoSided.Arcs
