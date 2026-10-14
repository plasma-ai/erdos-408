import Erdos408.OneSided.Decomposition
import Erdos408.OneSided.Goodness.Removal
import Erdos408.OneSided.Moment.Memory
import Erdos408.OneSided.Moment.Statements
import Erdos408.OneSided.Pairing

/-!
# The replacement of the determinant equation

Interface 2 of `blueprint/one_sided_type_ii.md` (§5, PD Proposition 4.1): the Cauchy
square and the major sum differ by `O(X Y L^{-D₁ - 1})`. It follows from four estimates.

* `eventually_square_decomposition` (§5.6, Lemma 4.1, in `Decomposition.lean`): up to the
  shared-label parts and the pad collisions, `Q_Y - Q_Y^maj` is `∑_{d₀} d₀⁻¹ ⟨f, 𝒯 f⟩` over the
  pad dyads `d₀ = 2^k`, `k ≤ L`.
* `eventually_goodness_removal` (§5.6): the good-state projections change `⟨f, 𝒯 f⟩` by
  less than any power of `L` times `UV`.
* `eventually_detMoment` (§§5.4–5.5): the determinant moment is at most `UV L^{-E₀ N}`.
  This is the root replacement (PD Lemma 3.4) and the signed-memory bound (PD §4).
* `eventually_pairing_of_moment` (§5.1, in `Pairing.lean`): a moment bound with precision `E` gives
  `⟨f, 𝒜 f⟩ ≪ UV L^{4C - E}`.

The damping exponent of the lift is a free parameter; the replacement uses `q = 1/2`.
-/

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

/-- Removing the good-state projections changes `⟨f, 𝒯 f⟩` by `O(UV L^{-D'})` for every
`D'`, where `UV = d₀ Y X`. -/
theorem eventually_goodness_removal {q C CX alo ahi g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (hCX : 1 ≤ CX) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5) (hg : 0 < g) (A₀ D' : ℝ) :
    ∃ C₀ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ‖rowPairing q A₀ x d (2 ^ j) (2 ^ k) - pairing q A₀ x d (2 ^ j) (2 ^ k)‖ ≤
        C₀ * (2 ^ k * 2 ^ j * d.X) * Real.log x ^ (-D') := by
  obtain ⟨C₀, hC₀⟩ := eventually_badMass_le (K := K) (C := C) hq hq₁ hCX halo hahi hg A₀
  set E := 4 * C + 3 * A₀ + D'
  -- `L^E ≤ exp(L^{α₋}/8)` eventually: `exp(z) / z^{E/α₋} → ∞` at `z = L^{α₋}/8`
  have halo₀ : 0 < alo := by linarith
  have hexp := (tendsto_exp_div_rpow_atTop (E / alo)).comp
    (((tendsto_rpow_atTop halo₀).comp Real.tendsto_log_atTop).atTop_div_const
      (by norm_num : (0 : ℝ) < 8))
  refine ⟨max C₀ 0, ?_⟩
  filter_upwards [hC₀, hexp.eventually_gt_atTop ((8 : ℝ) ^ (E / alo)),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop 0]
    with x hx hxE hL hx0 d hd j k
  have hL0 : 0 < Real.log x := by linarith
  have hX : 0 < d.X := lt_of_lt_of_le (div_pos hx0 (by linarith)) hd.X_ge
  have hx1 : 1 ≤ x := by
    by_contra h
    have := Real.log_lt_log hx0 (not_le.1 h)
    rw [Real.log_one] at this
    linarith
  have hz : 0 < Real.log x ^ alo / 8 := by positivity
  -- `L^E = 8^{E/α₋} (L^{α₋}/8)^{E/α₋} < exp(L^{α₋}/8)`
  have hLE : Real.log x ^ E ≤ Real.exp (Real.log x ^ alo / 8) := by
    have h₁ : (8 : ℝ) ^ (E / alo) * (Real.log x ^ alo / 8) ^ (E / alo) = Real.log x ^ E := by
      rw [← Real.mul_rpow (by norm_num) hz.le, mul_div_cancel₀ _ (by norm_num : (8 : ℝ) ≠ 0),
        ← Real.rpow_mul hL0.le, mul_div_cancel₀ _ halo₀.ne']
    have h₂ := (lt_div_iff₀ (Real.rpow_pos_of_pos hz _)).1 hxE
    rw [← h₁]
    exact h₂.le
  calc ‖rowPairing q A₀ x d (2 ^ j) (2 ^ k) - pairing q A₀ x d (2 ^ j) (2 ^ k)‖
      ≤ stateMass x d * Real.log x ^ (4 * C) * badMass q A₀ x d (2 ^ j) (2 ^ k) :=
        norm_rowPairing_sub_pairing_le hd hx1 A₀ _ _
    _ = Real.log x ^ (4 * C) * (stateMass x d * badMass q A₀ x d (2 ^ j) (2 ^ k)) := by ring
    _ ≤ Real.log x ^ (4 * C) * (max C₀ 0 * (2 ^ k * 2 ^ j * d.X) * Real.log x ^ (3 * A₀) *
          Real.exp (-Real.log x ^ alo / 8)) := by
        refine mul_le_mul_of_nonneg_left ((hx d hd j k).trans ?_) (by positivity)
        gcongr
        exact le_max_left _ _
    _ = max C₀ 0 * (2 ^ k * 2 ^ j * d.X) * Real.log x ^ (-D') *
          (Real.log x ^ E * Real.exp (-(Real.log x ^ alo / 8))) := by
        rw [show E = 4 * C + 3 * A₀ + D' from rfl, Real.rpow_add hL0, Real.rpow_add hL0,
          Real.rpow_neg hL0.le, neg_div]
        field_simp
    _ ≤ max C₀ 0 * (2 ^ k * 2 ^ j * d.X) * Real.log x ^ (-D') * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
        exact hLE
    _ = _ := mul_one _

/-- The final comparison: for `L ≥ 8`, `8E + 1 ≤ L^{1/100}` and `2 ≤ n ≤ L^{1/2} + 2`,
`exp(-L^{0.76}) + 30 L^{-(E + 1) n} ≤ L^{-E n}`. -/
private theorem exp_add_thirty_mul_rpow_le {E L n : ℝ} (hE : 0 < E) (hL : 8 ≤ L)
    (hLE : 8 * E + 1 ≤ L ^ (1 / 100 : ℝ)) (hn₂ : 2 ≤ n) (hn : n ≤ L ^ (1 / 2 : ℝ) + 2) :
    Real.exp (-L ^ (76 / 100 : ℝ)) + 30 * L ^ (-((E + 1) * n)) ≤ L ^ (-(E * n)) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  obtain ⟨hs2, -⟩ := two_le_rpow_half_of_four_le (show 4 ≤ L by linarith)
  set a := L ^ (-(E * n)) with ha
  -- the first term: `L^{-(E + 1) n} = a L^{-n} ≤ a / 64`
  have hLn : L ^ (-n) ≤ 1 / 64 :=
    calc L ^ (-n) ≤ L ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = 1 / (L * L) := by
          rw [Real.rpow_neg hL0.le, show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
          ring
      _ ≤ 1 / 64 := by
          gcongr
          calc (64 : ℝ) = 8 * 8 := by norm_num
            _ ≤ L * L := mul_le_mul hL hL (by norm_num) hL0.le
  have h₁ : 30 * L ^ (-((E + 1) * n)) ≤ a / 2 := by
    have hsplit : L ^ (-((E + 1) * n)) = a * L ^ (-n) := by
      rw [ha, ← Real.rpow_add hL0]
      ring_nf
    rw [hsplit]
    have ha0 : 0 ≤ a := by positivity
    calc 30 * (a * L ^ (-n)) ≤ 30 * (a * (1 / 64)) := by gcongr
      _ ≤ a / 2 := by linarith
  -- the second term: `E n log L + log 2 ≤ 8E L^{3/4} + 1 ≤ L^{3/4} L^{1/100} = L^{0.76}`
  have hlog : Real.log L ≤ 4 * L ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div hL0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    linarith
  have hn' : n ≤ 2 * L ^ (1 / 2 : ℝ) := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hprod : E * n * Real.log L ≤ 8 * E * L ^ (3 / 4 : ℝ) :=
    calc E * n * Real.log L ≤ E * (2 * L ^ (1 / 2 : ℝ)) * (4 * L ^ (1 / 4 : ℝ)) := by
          gcongr
      _ = 8 * E * (L ^ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ)) := by ring
      _ = 8 * E * L ^ (3 / 4 : ℝ) := by
          rw [← Real.rpow_add hL0]
          norm_num
  have hbig : 8 * E * L ^ (3 / 4 : ℝ) + 1 ≤ L ^ (76 / 100 : ℝ) := by
    have h34 : 1 ≤ L ^ (3 / 4 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    calc 8 * E * L ^ (3 / 4 : ℝ) + 1 ≤ L ^ (3 / 4 : ℝ) * (8 * E + 1) := by linarith
      _ ≤ L ^ (3 / 4 : ℝ) * L ^ (1 / 100 : ℝ) := by gcongr
      _ = L ^ (76 / 100 : ℝ) := by
          rw [← Real.rpow_add hL0]
          norm_num
  have h₂ : Real.exp (-L ^ (76 / 100 : ℝ)) ≤ a / 2 := by
    have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have : a / 2 = Real.exp (Real.log L * (-(E * n)) - Real.log 2) := by
      rw [ha, Real.rpow_def_of_pos hL0, Real.exp_sub, Real.exp_log two_pos]
    rw [this]
    exact Real.exp_le_exp.2 (by linarith)
  linarith

/-- The determinant moment (PD (4.1)): for `K ≥ K₀`, it is at most `UV L^{-E₀ N}`. -/
theorem eventually_detMoment {q C CX alo ahi Dstar g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (hC : 0 < C) (hD : 0 < Dstar) (hCX : 1 ≤ CX) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5)
    (hK : bandThreshold Dstar C ≤ K) (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ‖detMoment q (arcExp Dstar C) x d (2 ^ j) (2 ^ k)‖ ≤
        2 ^ k * 2 ^ j * d.X *
          Real.log x ^ (-(momentPrec Dstar C * (2 * momentPower x : ℕ))) := by
  have hE : 0 < momentPrec Dstar C := by
    unfold momentPrec squarePrec
    linarith
  filter_upwards [eventually_root_replacement (C := C) (CX := CX) hq hq₁ halo hahi hg
      (arcExp Dstar C),
    eventually_norm_lineAverage_le hq hq₁ hC hD hCX halo hahi hK hg,
    Real.tendsto_log_atTop.eventually_ge_atTop 8,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop (8 * momentPrec Dstar C + 1),
    eventually_gt_atTop 0] with x hroot hline hL hLE hx0 d hd j k
  set L := Real.log x
  have hLE' : 8 * momentPrec Dstar C + 1 ≤ L ^ (1 / 100 : ℝ) := hLE
  have hHm : 0 < d.Hm := (Real.rpow_pos_of_pos hx0 _).trans_le hd.Hm_ge
  have hHn : 0 < d.Hn := (Real.rpow_pos_of_pos hx0 _).trans_le hd.Hn_ge
  have hX : 0 < d.X := mul_pos hHm hHn
  obtain ⟨hn₂, hn⟩ := two_mul_momentPower_bounds (show 0 < L by linarith)
  set B := L ^ (-((momentPrec Dstar C + 1) * ((2 * momentPower x : ℕ) : ℝ)))
  have hB : 0 ≤ B := Real.rpow_nonneg (by linarith) _
  -- the Riemann sum is an average of `15 n³ / n³` line averages at corners in the root box
  have hRS : ‖rootRiemannSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k)‖ ≤ 15 * B := by
    unfold rootRiemannSum
    set n := gridSteps d
    have hU : 0 ≤ (2 : ℝ) ^ k * 2 ^ j * d.Hm := by positivity
    have hterm : ∀ i₁ ∈ range (15 * n), ∀ i₂ ∈ range n, ∀ i₃ ∈ range n,
        ‖lineAverage x d fun ℓ => rootMoment q (arcExp Dstar C) x d (2 ^ j) (2 ^ k)
          (2 ^ k * 2 ^ j * d.Hm * (1 + i₁ / n)) (d.Hn * (1 + i₂ / n)) (i₃ / n) ℓ‖ ≤ B := by
      intro i₁ hi₁ i₂ hi₂ i₃ hi₃
      rw [mem_range] at hi₁ hi₂ hi₃
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have h₁ : (i₁ : ℝ) / n ≤ 15 := by
        rw [div_le_iff₀ hn0]
        exact_mod_cast hi₁.le
      have h₂ : (i₂ : ℝ) / n ≤ 1 := by
        rw [div_le_iff₀ hn0, one_mul]
        exact_mod_cast hi₂.le
      have h₃ : (i₃ : ℝ) / n ≤ 1 := by
        rw [div_le_iff₀ hn0, one_mul]
        exact_mod_cast hi₃.le
      refine hline d hd j k _ _ _ ?_ ?_ ?_ ?_ (by positivity) h₃
      · exact le_mul_of_one_le_right hU (le_add_of_nonneg_right (by positivity))
      · calc (2 : ℝ) ^ k * 2 ^ j * d.Hm * (1 + i₁ / n) ≤ (2 : ℝ) ^ k * 2 ^ j * d.Hm * 16 :=
              mul_le_mul_of_nonneg_left (by linarith) hU
          _ = 16 * ((2 : ℝ) ^ k * 2 ^ j * d.Hm) := by ring
      · exact le_mul_of_one_le_right hHn.le (le_add_of_nonneg_right (by positivity))
      · calc d.Hn * (1 + i₂ / n) ≤ d.Hn * 2 := mul_le_mul_of_nonneg_left (by linarith) hHn.le
          _ = 2 * d.Hn := mul_comm _ _
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    calc ((n : ℝ) ^ 3)⁻¹ * ‖∑ i₁ ∈ range (15 * n), ∑ i₂ ∈ range n, ∑ i₃ ∈ range n,
          lineAverage x d fun ℓ => rootMoment q (arcExp Dstar C) x d (2 ^ j) (2 ^ k)
            (2 ^ k * 2 ^ j * d.Hm * (1 + i₁ / n)) (d.Hn * (1 + i₂ / n)) (i₃ / n) ℓ‖
        ≤ ((n : ℝ) ^ 3)⁻¹ * ∑ _i₁ ∈ range (15 * n), ∑ _i₂ ∈ range n, ∑ _i₃ ∈ range n, B := by
          gcongr
          exact norm_sum_le_of_le _ fun i₁ hi₁ => norm_sum_le_of_le _ fun i₂ hi₂ =>
            norm_sum_le_of_le _ fun i₃ hi₃ => hterm i₁ hi₁ i₂ hi₂ i₃ hi₃
      _ = ((n : ℝ) ^ 3)⁻¹ * (15 * n ^ 3) * B := by
          simp only [sum_const, card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 15 * B := by
          by_cases hn0 : n = 0
          · simp [hn0, hB]
          · have : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
            field_simp
            rfl
  -- split off the root replacement and absorb both terms
  set UV := (2 : ℝ) ^ k * 2 ^ j * d.X
  have hUV : 0 < UV := by positivity
  set RS := rootRiemannSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k)
  set M := detMoment q (arcExp Dstar C) x d (2 ^ j) (2 ^ k)
  have hR := hroot d hd j k
  have hfin := exp_add_thirty_mul_rpow_le hE hL hLE' hn₂ hn
  calc ‖M‖ = UV * ‖(UV : ℂ)⁻¹ * M‖ := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hUV.le,
          mul_inv_cancel_left₀ hUV.ne']
    _ ≤ UV * (‖(UV : ℂ)⁻¹ * M - (primitiveDensity : ℂ) * RS‖ +
          ‖(primitiveDensity : ℂ) * RS‖) := by
        gcongr
        have := norm_sub_norm_le ((UV : ℂ)⁻¹ * M) ((primitiveDensity : ℂ) * RS)
        linarith
    _ ≤ UV * (Real.exp (-L ^ (76 / 100 : ℝ)) + 2 * (15 * B)) := by
        gcongr
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul RootResidue.abs_primitiveDensity_le hRS (norm_nonneg _) (by norm_num)
    _ = UV * (Real.exp (-L ^ (76 / 100 : ℝ)) + 30 * B) := by ring
    _ ≤ UV * L ^ (-(momentPrec Dstar C * ((2 * momentPower x : ℕ) : ℝ))) := by gcongr

/-- Interface 2: for `K ≥ K₀`, the Cauchy square and the major sum differ by
`O(X Y L^{-D₁ - 1})` for every dyadic `Y`. -/
theorem eventually_replacement {C CX alo ahi Dstar g : ℝ} (hC : 0 < C) (hD : 0 < Dstar)
    (hCX : 1 ≤ CX) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5) (hK : bandThreshold Dstar C ≤ K)
    (hg : 0 < g) :
    ∃ C₂ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j : ℕ,
      ‖cauchySquare x d (2 ^ j) - majorSquare (arcExp Dstar C) x d (2 ^ j)‖ ≤
        C₂ * d.X * 2 ^ j * Real.log x ^ (-(squarePrec Dstar + 1)) := by
  have hq : (0 : ℝ) < 1 / 2 := by norm_num
  have hq₁ : (1 / 2 : ℝ) < 1 := by norm_num
  set A₀ := arcExp Dstar C
  set D₁ := squarePrec Dstar
  obtain ⟨CA, hA⟩ :=
    eventually_square_decomposition (K := K) hCX halo hahi hg (1 / 2) A₀ (D₁ + 2)
  obtain ⟨CB, hB⟩ :=
    eventually_goodness_removal (K := K) (C := C) hq hq₁ hCX halo hahi hg A₀ (D₁ + 2)
  have hM := eventually_detMoment hq hq₁ hC hD hCX halo hahi hK hg
  obtain ⟨CD, hD⟩ :=
    eventually_pairing_of_moment (K := K) (C := C) (CX := CX) (alo := alo) hq hq₁ hahi hg A₀
      (momentPrec Dstar C)
  refine ⟨|CA| + 2 * (|CB| + |CD|), ?_⟩
  filter_upwards [hA, hB, hM, hD, eventually_ge_atTop (Real.exp 1)] with x hA hB hM hD hx
  intro d hd j
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hL : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hL0 : 0 < Real.log x := by linarith
  have hX : 0 < d.X := lt_of_lt_of_le (div_pos hx0 (by linarith)) hd.X_ge
  set L := Real.log x
  -- `4C - E₀ = -(D₁ + 2)`
  have hexp : 4 * C - momentPrec Dstar C = -(D₁ + 2) := by
    simp only [momentPrec, D₁]; ring
  have hP : 0 ≤ L ^ (-(D₁ + 2)) := (rpow_pos_of_pos hL0 _).le
  -- each pad dyad contributes `O(X Y L^{-D₁ - 2})`
  have hterm : ∀ k : ℕ, ‖((2 : ℂ) ^ k)⁻¹ * rowPairing (1 / 2) A₀ x d (2 ^ j) (2 ^ k)‖ ≤
      (|CB| + |CD|) * (d.X * 2 ^ j) * L ^ (-(D₁ + 2)) := by
    intro k
    have h₁ := hB d hd j k
    have h₂ := hD d hd j k (hM d hd j k)
    rw [hexp] at h₂
    have hUV : 0 ≤ (2 : ℝ) ^ k * 2 ^ j * d.X := by positivity
    have hrow : ‖rowPairing (1 / 2) A₀ x d (2 ^ j) (2 ^ k)‖ ≤
        (|CB| + |CD|) * ((2 : ℝ) ^ k * 2 ^ j * d.X) * L ^ (-(D₁ + 2)) := by
      calc ‖rowPairing (1 / 2) A₀ x d (2 ^ j) (2 ^ k)‖
          = ‖(rowPairing (1 / 2) A₀ x d (2 ^ j) (2 ^ k) - pairing (1 / 2) A₀ x d (2 ^ j) (2 ^ k)) +
              pairing (1 / 2) A₀ x d (2 ^ j) (2 ^ k)‖ := by rw [sub_add_cancel]
        _ ≤ ‖rowPairing (1 / 2) A₀ x d (2 ^ j) (2 ^ k) - pairing (1 / 2) A₀ x d (2 ^ j) (2 ^ k)‖ +
              ‖pairing (1 / 2) A₀ x d (2 ^ j) (2 ^ k)‖ := norm_add_le _ _
        _ ≤ CB * ((2 : ℝ) ^ k * 2 ^ j * d.X) * L ^ (-(D₁ + 2)) +
              CD * ((2 : ℝ) ^ k * 2 ^ j * d.X) * L ^ (-(D₁ + 2)) := add_le_add h₁ h₂
        _ ≤ |CB| * ((2 : ℝ) ^ k * 2 ^ j * d.X) * L ^ (-(D₁ + 2)) +
              |CD| * ((2 : ℝ) ^ k * 2 ^ j * d.X) * L ^ (-(D₁ + 2)) := by
          gcongr <;> exact le_abs_self _
        _ = (|CB| + |CD|) * ((2 : ℝ) ^ k * 2 ^ j * d.X) * L ^ (-(D₁ + 2)) := by ring
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_two]
    calc ((2 : ℝ) ^ k)⁻¹ * ‖rowPairing (1 / 2) A₀ x d (2 ^ j) (2 ^ k)‖
        ≤ ((2 : ℝ) ^ k)⁻¹ * ((|CB| + |CD|) * ((2 : ℝ) ^ k * 2 ^ j * d.X) * L ^ (-(D₁ + 2))) := by
          gcongr
      _ = (|CB| + |CD|) * (d.X * 2 ^ j) * L ^ (-(D₁ + 2)) := by
          field_simp
  -- the sum over the `⌊L⌋ + 1 ≤ 2L` pad dyads
  have hS : ‖∑ k ∈ range (⌊L⌋₊ + 1), ((2 : ℂ) ^ k)⁻¹ * rowPairing (1 / 2) A₀ x d (2 ^ j) (2 ^ k)‖ ≤
      2 * L * ((|CB| + |CD|) * (d.X * 2 ^ j) * L ^ (-(D₁ + 2))) := by
    have hfloor : (⌊L⌋₊ : ℝ) + 1 ≤ 2 * L := by
      have := Nat.floor_le hL0.le
      linarith
    calc _ ≤ ∑ k ∈ range (⌊L⌋₊ + 1),
          ‖((2 : ℂ) ^ k)⁻¹ * rowPairing (1 / 2) A₀ x d (2 ^ j) (2 ^ k)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ range (⌊L⌋₊ + 1), (|CB| + |CD|) * (d.X * 2 ^ j) * L ^ (-(D₁ + 2)) :=
          sum_le_sum fun k _ => hterm k
      _ = ((⌊L⌋₊ : ℝ) + 1) * ((|CB| + |CD|) * (d.X * 2 ^ j) * L ^ (-(D₁ + 2))) := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ 2 * L * ((|CB| + |CD|) * (d.X * 2 ^ j) * L ^ (-(D₁ + 2))) := by
          gcongr
  -- `L · L^{-D₁ - 2} = L^{-D₁ - 1}` and `L^{-D₁ - 2} ≤ L^{-D₁ - 1}`
  have hLpow : L * L ^ (-(D₁ + 2)) = L ^ (-(D₁ + 1)) := by
    rw [show -(D₁ + 1) = 1 + -(D₁ + 2) by ring, rpow_add hL0, rpow_one]
  have hmono : L ^ (-(D₁ + 2)) ≤ L ^ (-(D₁ + 1)) :=
    rpow_le_rpow_of_exponent_le hL (by linarith)
  set S := ∑ k ∈ range (⌊L⌋₊ + 1), ((2 : ℂ) ^ k)⁻¹ * rowPairing (1 / 2) A₀ x d (2 ^ j) (2 ^ k)
  calc ‖cauchySquare x d (2 ^ j) - majorSquare A₀ x d (2 ^ j)‖
      = ‖(cauchySquare x d (2 ^ j) - majorSquare A₀ x d (2 ^ j) - S) + S‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖cauchySquare x d (2 ^ j) - majorSquare A₀ x d (2 ^ j) - S‖ + ‖S‖ := norm_add_le _ _
    _ ≤ CA * d.X * 2 ^ j * L ^ (-(D₁ + 2)) +
          2 * L * ((|CB| + |CD|) * (d.X * 2 ^ j) * L ^ (-(D₁ + 2))) := add_le_add (hA d hd j) hS
    _ ≤ |CA| * d.X * 2 ^ j * L ^ (-(D₁ + 1)) +
          2 * (|CB| + |CD|) * (d.X * 2 ^ j) * (L * L ^ (-(D₁ + 2))) := by
        have : CA * d.X * 2 ^ j * L ^ (-(D₁ + 2)) ≤ |CA| * d.X * 2 ^ j * L ^ (-(D₁ + 1)) := by
          gcongr
          exact le_abs_self _
        exact add_le_add this (le_of_eq (by ring))
    _ = (|CA| + 2 * (|CB| + |CD|)) * d.X * 2 ^ j * L ^ (-(D₁ + 1)) := by
        rw [hLpow]; ring

end Erdos408.OneSided
