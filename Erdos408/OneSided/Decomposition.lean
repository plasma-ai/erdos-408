module

public import Erdos408.OneSided.Decomposition.Bound
public import Erdos408.OneSided.Decomposition.Eventually

/-!
# The lift identity and the collisions

PD §4.9 and Lemma 4.1 (`blueprint/one_sided_type_ii.md` §4, §5.6, Lemmas 1.1–1.2). Up to
errors smaller than any power of `L` times `XY`, the difference `Q_Y - Q_Y^maj` of the
Cauchy square and the major sum is `∑_{d₀ = 2^k, k ≤ L} d₀⁻¹ ⟨f, 𝒯 f⟩`.

* Shared labels. The pairs of label products sharing a prime contribute
  `O(XY L^{4C + 3 + 3A₀} e^{-L^{a₋}})` to both `Q_Y` (Lemma 1.2, through PD (3.9)) and
  `Q_Y^maj` (`mem:unshared-collisions`).
* For coprime label products the equation is `t = bmn - ars = b - a` (Lemma 1.3).
  Weight by independent ordered harmonic pads `∏ μ_i(p_{i,h})`, which have total mass one.
  Pads that are distinct and disjoint from `a, b` give exactly `∑_{d₀} d₀⁻¹ ⟨f, 𝒯 f⟩`
  (Lemma 4.1). The change of variables is `P = (Dbm, s)`, `Q = (Dar, n)`, using the
  measure identity `D⁻¹ ∏ V_i^{-(J+2)} = ∏ μ_i(pads) ∏ V_i^{-2}`, roughness, and automatic
  primitivity.
* Pad collisions have probability `≤ C_K M² e^{-L^{a₋}}`, against the absolute raw and
  comparison squares `O(XY L^{4C + 3 + 3A₀})`.

The pieces are in `Decomposition/`: `Count` and `Pair` bound the pair error `E(a, b)`,
`Lists` and `LiftSum` prove the lift identity, `Measure` and `Collision` bound the
collision probabilities, `Bound` assembles them at one `x`, and `Eventually` supplies the
growth facts.
-/

@[expose] public section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

/-- Lemma 4.1 with the shared-label and pad-collision bounds: `Q_Y - Q_Y^maj` is the sum
of `d₀⁻¹ ⟨f, 𝒯 f⟩` over the pad dyads, up to `O(X Y L^{-D'})` for every `D'`. -/
theorem eventually_square_decomposition {C CX alo ahi g : ℝ} (hCX : 1 ≤ CX)
    (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5) (hg : 0 < g) (q A₀ D' : ℝ) :
    ∃ C₀ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j : ℕ,
      ‖cauchySquare x d (2 ^ j) - majorSquare A₀ x d (2 ^ j) -
          ∑ k ∈ range (⌊Real.log x⌋₊ + 1),
            ((2 : ℂ) ^ k)⁻¹ * rowPairing q A₀ x d (2 ^ j) (2 ^ k)‖ ≤
        C₀ * d.X * 2 ^ j * Real.log x ^ (-D') := by
  -- the constant of the final decay: `L^{4C + 3} · 1568 L^{3|A₀|} · 4(K + 1)² L² · 2`
  set E : ℝ := 4 * C + 3 * |A₀| + 5
  set c₁ : ℝ := 200704 * ((K : ℝ) + 1) ^ 2
  refine ⟨1, ?_⟩
  filter_upwards [eventually_band_disjoint hg, eventually_not_dvd_of_isRough hahi,
    eventually_harmonicMass_band halo.le, eventually_two_le_rpow,
    eventually_five_mul_exp_le_roughLevel K, eventually_rpow_mul_exp_le hCX K,
    eventually_exp_lt_two_pow K,
    eventually_mul_rpow_mul_exp_le (show 0 < alo by linarith) c₁ E D',
    Real.tendsto_log_atTop.eventually_ge_atTop (1 + Real.log (17 * CX)),
    eventually_ge_atTop CX] with x hdisj hrough hmass h2 h5W h34 hpad hdecay hL hxC d hd j
  set L := Real.log x
  set J := padCount x
  set Y : ℝ := 2 ^ j
  have hCX0 : 0 < CX := by linarith
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ L := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 17 * CX by linarith)
    linarith
  have hL0 : 0 < L := by linarith
  have hY : 1 ≤ Y := one_le_pow₀ (by norm_num)
  have hY0 : 0 < Y := by linarith
  -- the band facts at `x`
  have hdisj' : ∀ i i', i ≠ i' → Disjoint (band x (d.a i)) (band x (d.a i')) := by
    intro i i' hii
    rcases lt_or_gt_of_ne hii with h | h
    · exact hdisj _ _ (hd.gap i i' h)
    · exact (hdisj _ _ (hd.gap i' i h)).symm
  have hrough' : ∀ i, ∀ r ∈ band x (d.a i), ∀ m : ℕ, m ≠ 0 → IsRough x m → ¬ r ∣ m :=
    fun i => hrough _ (hd.window i).2
  have hV : ∀ i, 0 < harmonicMass (band x (d.a i)) := fun i => by
    linarith [(hmass _ (hd.window i).1).1]
  have hle15 : ∀ i, L ^ d.a i ≤ L ^ (1 / 5 : ℝ) := fun i =>
    Real.rpow_le_rpow_of_exponent_le hL1 ((hd.window i).2.trans hahi.le)
  -- the scales
  have hHm : 2 ≤ d.Hm := (h2 _ hd.γ_ge).trans hd.Hm_ge
  have hHn : 1 ≤ d.Hn := by linarith [(h2 _ hd.γ_ge).trans hd.Hn_ge]
  have hXge : x / CX ≤ d.X := hd.X_ge
  have hX : 1 ≤ d.X := le_trans (by rw [le_div_iff₀ hCX0]; linarith) hXge
  have hlog : 1 + Real.log (17 * d.X) ≤ 2 * L := by
    have : Real.log (17 * d.X) ≤ Real.log (17 * CX) + L := by
      rw [← Real.log_mul (by positivity) hx0.ne', mul_assoc]
      exact Real.log_le_log (by positivity) (by unfold Data.X; linarith [hd.X_le])
    linarith
  -- label products are at most `e^{2K L^{1/5}}`, so `5Y ≤ W` and `Y ≤ X^{1/4}` when relevant
  have hlab : ∀ p ∈ d.labels x,
      ((∏ i, p i : ℕ) : ℝ) ≤ Real.exp (2 * K * L ^ (1 / 5 : ℝ)) := by
    intro p hp
    rw [Nat.cast_prod]
    refine (labelProduct_bounds (mem_band_of_mem_labels hp)).2.trans (Real.exp_le_exp.2 ?_)
    have : ∑ i, L ^ d.a i ≤ ∑ _i : Fin K, L ^ (1 / 5 : ℝ) := sum_le_sum fun i _ => hle15 i
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have hYW : ∀ p ∈ d.labels x, Y < (∏ i, p i : ℕ) → 5 * Y ≤ roughLevel x := fun p hp hpY =>
    by linarith [hlab p hp]
  -- pad products are below `2^{⌊L⌋ + 1}`
  have hN : ∀ z ∈ padSet x d J, ∏ c, z c < 2 ^ (⌊L⌋₊ + 1) := by
    intro z hz
    have hzle : ((∏ c, z c : ℕ) : ℝ) ≤ Real.exp (2 * K * J * L ^ (1 / 5 : ℝ)) := by
      calc ((∏ c, z c : ℕ) : ℝ) = ∏ c, (z c : ℝ) := Nat.cast_prod _ _
        _ ≤ ∏ _c : Fin K × Fin J, Real.exp (2 * L ^ (1 / 5 : ℝ)) :=
            prod_le_prod₀ (fun c _ => Nat.cast_nonneg _) fun c _ =>
              (le_exp_of_mem_band (mem_band_of_mem_padSet hz c)).trans
                (Real.exp_le_exp.2 (by linarith [hle15 c.1]))
        _ = Real.exp (2 * K * J * L ^ (1 / 5 : ℝ)) := by
            rw [prod_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
              ← Real.exp_nat_mul]
            push_cast
            ring_nf
    exact_mod_cast hzle.trans_lt hpad
  -- every atom `μ_i(p)` is at most `ε = 2 e^{-L^{a₋}}`
  set ε := 2 * Real.exp (-L ^ alo)
  have hε0 : 0 ≤ ε := by positivity
  have hε : ∀ i, ∀ y ∈ band x (d.a i), 1 / ((y : ℝ) * harmonicMass (band x (d.a i))) ≤ ε := by
    intro i y hy
    have hy₁ : Real.exp (L ^ alo) ≤ y := (Real.exp_le_exp.2
      (Real.rpow_le_rpow_of_exponent_le hL1 (hd.window i).1)).trans (exp_le_of_mem_band hy)
    have hVi := (hmass _ (hd.window i).1).1
    have hyV : Real.exp (L ^ alo) / 2 ≤ y * harmonicMass (band x (d.a i)) := by
      have := Real.exp_pos (L ^ alo)
      nlinarith
    rw [div_le_iff₀ (by linarith [Real.exp_pos (L ^ alo)])]
    calc (1 : ℝ) = ε * (Real.exp (L ^ alo) / 2) := by
          simp only [ε, Real.exp_neg]
          field_simp
      _ ≤ ε * (y * harmonicMass (band x (d.a i))) := by gcongr
  -- the pair error
  have hα : ∀ m, ‖d.α m‖ ≤ L ^ C := fun m => by
    by_cases h : d.α m = 0
    · rw [h, norm_zero]; positivity
    · exact (hd.α_supp m h).2.2.2
  have hβ : ∀ n, ‖d.β n‖ ≤ L ^ C := fun n => by
    by_cases h : d.β n = 0
    · rw [h, norm_zero]; positivity
    · exact (hd.β_supp n h).2.2.2
  set B := d.X / Y * L ^ (4 * C) * L ^ 3 * (160 + 1408 * L ^ (3 * A₀))
  have hB0 : 0 ≤ B := by positivity
  have hB : ∀ p ∈ d.labels x, ∀ p' ∈ d.labels x, Y < (∏ i, p i : ℕ) →
      Y < (∏ i, p' i : ℕ) → ((∏ i, p i : ℕ) : ℝ) < 4 * Y → ((∏ i, p' i : ℕ) : ℝ) < 4 * Y →
      ‖pairError A₀ x d Y (∏ i, p i) (∏ i, p' i)‖ ≤ B := by
    intro p hp p' _ hpY hp'Y hpY4 hp'Y4
    -- `(17X)^{3/4} Y ≤ (17X)^{3/4} e^{2K L^{1/5}} ≤ X`
    have h34' : (17 * d.X) ^ (3 / 4 : ℝ) ≤ d.X / Y := by
      rw [le_div_iff₀ hY0]
      have := h34 d.X hXge
      have := Real.rpow_nonneg (show (0 : ℝ) ≤ 17 * d.X by linarith) (3 / 4 : ℝ)
      nlinarith [hlab p hp]
    exact norm_pairError_le_of A₀ hL1 hα hβ (by linarith) hHn hX hlog hY0 h34' hpY hp'Y hpY4
      hp'Y4
  refine (norm_square_decomposition_le q A₀ hd hdisj' hrough' hHm hHn hV hY hYW hN hε0 hε hB0
    hB).trans ?_
  -- the decay: `16 Y² B (K² + (KJ)² + 2KJ) ε ≤ X Y c₁ L^E e^{-L^{a₋}} ≤ X Y L^{-D'}`
  have hJ : (J : ℝ) ≤ L := by
    refine (Nat.floor_le (by positivity)).trans ?_
    calc L ^ (1 / 100 : ℝ) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := Real.rpow_one L
  have hA : 160 + 1408 * L ^ (3 * A₀) ≤ 1568 * L ^ (3 * |A₀|) := by
    have h₁ : L ^ (3 * A₀) ≤ L ^ (3 * |A₀|) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [le_abs_self A₀])
    have h₂ : 1 ≤ L ^ (3 * |A₀|) := Real.one_le_rpow hL1 (by positivity)
    linarith
  have hKJ : (K : ℝ) ^ 2 + (((K * J : ℕ) : ℝ) ^ 2 + 2 * (K * J : ℕ)) ≤
      4 * ((K : ℝ) + 1) ^ 2 * L ^ 2 := by
    push_cast
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    have hKL : (K : ℝ) * J ≤ (K + 1) * L := mul_le_mul (by linarith) hJ hJ0 (by linarith)
    have hKL' : (K : ℝ) ≤ (K + 1) * L := by nlinarith
    have hKJ0 : (0 : ℝ) ≤ K * J := mul_nonneg hK0 hJ0
    nlinarith [mul_le_mul hKL hKL hKJ0 (by positivity), mul_le_mul hKL' hKL' hK0 (by positivity),
      mul_le_mul hKL' (le_refl ((K + 1 : ℝ) * L)) (by positivity) (by positivity)]
  have hLE : L ^ E = L ^ (4 * C) * L ^ 3 * L ^ (3 * |A₀|) * L ^ 2 := by
    rw [show E = 4 * C + 3 + 3 * |A₀| + 2 by ring, Real.rpow_add hL0, Real.rpow_add hL0,
      Real.rpow_add hL0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
  have hbr : 16 * (L ^ (4 * C) * L ^ 3 * (160 + 1408 * L ^ (3 * A₀))) *
      ((K : ℝ) ^ 2 + (((K * J : ℕ) : ℝ) ^ 2 + 2 * (K * J : ℕ))) * ε ≤ L ^ (-D') := by
    refine le_trans ?_ hdecay
    rw [hLE]
    have hL4 : 0 ≤ L ^ (4 * C) * L ^ 3 := by positivity
    have hexp : 0 ≤ Real.exp (-L ^ alo) := (Real.exp_pos _).le
    calc 16 * (L ^ (4 * C) * L ^ 3 * (160 + 1408 * L ^ (3 * A₀))) *
          ((K : ℝ) ^ 2 + (((K * J : ℕ) : ℝ) ^ 2 + 2 * (K * J : ℕ))) * ε
        ≤ 16 * (L ^ (4 * C) * L ^ 3 * (1568 * L ^ (3 * |A₀|))) *
          (4 * ((K : ℝ) + 1) ^ 2 * L ^ 2) * ε := by
          gcongr
      _ = c₁ * (L ^ (4 * C) * L ^ 3 * L ^ (3 * |A₀|) * L ^ 2) * Real.exp (-L ^ alo) := by
          simp only [c₁, ε]
          ring
  calc 16 * Y ^ 2 * B * ((K : ℝ) ^ 2 + (((K * J : ℕ) : ℝ) ^ 2 + 2 * (K * J : ℕ))) * ε
      = d.X * Y * (16 * (L ^ (4 * C) * L ^ 3 * (160 + 1408 * L ^ (3 * A₀))) *
          ((K : ℝ) ^ 2 + (((K * J : ℕ) : ℝ) ^ 2 + 2 * (K * J : ℕ))) * ε) := by
        simp only [B]
        field_simp
    _ ≤ d.X * Y * L ^ (-D') := by
        gcongr
    _ = 1 * d.X * 2 ^ j * L ^ (-D') := by ring

end Erdos408.OneSided
