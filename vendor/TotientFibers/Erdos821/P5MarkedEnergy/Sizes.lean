import Erdos821.P5MarkedEnergy.Numerics

/-! The scale conditions of the final assembly, uniform over the admissible
`Y`, `H` and smooth pieces. -/

noncomputable section
open Filter Real

namespace Erdos821.P5Marked
open Blueprint.Analytic

/-- `c * x^s ≤ x^t` eventually when `s < t`. -/
theorem ev_const_xpow_le (c s t : ℝ) (hst : s < t) :
    ∀ᶠ x : ℝ in atTop, c * x ^ s ≤ x ^ t := by
  have h := (tendsto_rpow_atTop (show 0 < t - s by linarith)).eventually_ge_atTop c
  filter_upwards [h, ev_x_ge 1] with x hx hx1
  have hxpos : 0 < x := by linarith
  have : x ^ t = x ^ (t - s) * x ^ s := by rw [← Real.rpow_add hxpos]; congr 1; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hxpos.le _)

/-- `c * exp(L^b) * x^s ≤ x^t` eventually when `b < 1`, `s < t`. -/
theorem ev_exp_xpow_le (c b s t : ℝ) (hb : b < 1) (hst : s < t) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, c * Real.exp (L x ^ b) * x ^ s ≤ x ^ t := by
  filter_upwards [ev_rpow_small b (t - s) (Real.log c) hb (by linarith), ev_x_ge 1] with x hx hx1
  have hxpos : 0 < x := by linarith
  rw [rpow_x_eq hxpos, rpow_x_eq hxpos, ← Real.exp_log hc, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- `exp(L^b) * c ≤ exp(L^c'/2)` eventually when `b < c'`, with a polylog factor. -/
theorem ev_exp_small_le (c b c' : ℝ) (hb : 0 ≤ b) (hbc : b < c') (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, c * L x * Real.exp (L x ^ b) ≤ Real.exp (L x ^ c' / 2) := by
  -- L^b + log c + log L ≤ L^c'/2
  have hc'pos : 0 < c' := by linarith
  have h1 : ∀ᶠ x : ℝ in atTop, Real.log c + L x ^ b + Real.log (L x) ≤ L x ^ c' / 2 := by
    have hlog := (isLittleO_log_rpow_atTop hc'pos).comp_tendsto tendsto_L
    have hev := hlog.def (show (0 : ℝ) < 1 / 6 by norm_num)
    have hA := ev_const_le_rpow 6 (c' - b) (by linarith)
    have hB := ev_const_le_rpow (6 * Real.log c) c' hc'pos
    filter_upwards [hev, hA, hB, ev_L_ge 1] with x hx hxA hxB hL1
    have hLpos : 0 < L x := by linarith
    simp only [Function.comp, Real.norm_eq_abs] at hx
    rw [abs_of_nonneg (Real.log_nonneg hL1), abs_of_nonneg (Real.rpow_nonneg hLpos.le _)] at hx
    have hsplit : L x ^ c' = L x ^ b * L x ^ (c' - b) := by
      rw [← Real.rpow_add hLpos]; congr 1; ring
    have hbpos : 0 ≤ L x ^ b := Real.rpow_nonneg hLpos.le _
    have h6 : 6 * L x ^ b ≤ L x ^ c' := by
      rw [hsplit]; nlinarith
    linarith
  filter_upwards [h1, ev_L_ge 1] with x hx hL1
  have hLpos : 0 < L x := by linarith
  have e : c * L x * Real.exp (L x ^ b) = Real.exp (Real.log c + Real.log (L x) + L x ^ b) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hc, Real.exp_log hLpos]
  rw [e]
  exact Real.exp_le_exp.mpr (by linarith)

theorem xpow_mono {x : ℝ} (hx : 1 ≤ x) {s t : ℝ} (hst : s ≤ t) : x ^ s ≤ x ^ t :=
  Real.rpow_le_rpow_of_exponent_le hx hst

/-- `Y`-range consequences. -/
theorem sz_Y (Y0 hi : ℝ) (hhi : 0 < hi) :
    ∀ᶠ x : ℝ in atTop, ∀ Y : ℝ, x ^ (0.99 : ℝ) ≤ Y → Y ≤ x ^ (1.01 : ℝ) →
      1 ≤ hi * Y ∧ Y0 ≤ Y ∧ 2 ≤ Y ∧ x ^ (1 / 2 : ℝ) ≤ Y ∧ Y ≤ x ^ (2 : ℕ) ∧
        2 * Y ≤ x ^ (2 : ℕ) := by
  filter_upwards [ev_const_xpow_le (max (1 / hi) (max Y0 2)) 0 0.99 (by norm_num),
    ev_const_xpow_le 2 1.01 2 (by norm_num), ev_x_ge 1] with x h1 h2 hx1
  intro Y hY1 hY2
  have hxpos : 0 < x := by linarith
  rw [Real.rpow_zero, mul_one] at h1
  have hm1 : 1 / hi ≤ Y := (le_max_left _ _).trans (h1.trans hY1)
  have hm2 : Y0 ≤ Y := ((le_max_left _ _).trans (le_max_right _ _)).trans (h1.trans hY1)
  have hm3 : (2 : ℝ) ≤ Y := ((le_max_right _ _).trans (le_max_right _ _)).trans (h1.trans hY1)
  have hx2 : x ^ (2 : ℕ) = x ^ (2 : ℝ) := by norm_cast
  refine ⟨?_, hm2, hm3, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hhi] at hm1; linarith
  · exact (xpow_mono hx1 (by norm_num)).trans hY1
  · rw [hx2]; exact hY2.trans (xpow_mono hx1 (by norm_num))
  · rw [hx2]
    have : 2 * x ^ (1.01 : ℝ) ≤ x ^ (2 : ℝ) := h2
    linarith

/-- Piece-size consequences. -/
theorem sz_alpha (αmin αmax : ℝ) (hmin : 0 < αmin) :
    ∀ᶠ x : ℝ in atTop, ∀ Y α : ℝ, x ^ (0.99 : ℝ) ≤ Y → Y ≤ x ^ (1.01 : ℝ) → αmin ≤ α → α ≤ αmax →
      10 ≤ α * Y ∧ x ^ (0.01 : ℝ) ≤ α * Y / 10 ∧ 64 * α * Y ≤ x ^ (2 : ℕ) := by
  filter_upwards [ev_const_xpow_le (10 / αmin) 0 0.99 (by norm_num),
    ev_const_xpow_le (10 / αmin) 0.01 0.99 (by norm_num),
    ev_const_xpow_le (64 * |αmax|) 1.01 2 (by norm_num), ev_x_ge 1] with x h1 h2 h3 hx1
  intro Y α hY1 hY2 hα1 hα2
  have hxpos : 0 < x := by linarith
  have hα : 0 < α := by linarith
  have hY0 : 0 < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) hY1
  rw [Real.rpow_zero, mul_one] at h1
  refine ⟨?_, ?_, ?_⟩
  · have : 10 / αmin ≤ Y := h1.trans hY1
    rw [div_le_iff₀ hmin] at this
    nlinarith
  · have : 10 / αmin * x ^ (0.01 : ℝ) ≤ Y := h2.trans hY1
    rw [div_mul_eq_mul_div, div_le_iff₀ hmin] at this
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
    have hx01 : 0 ≤ x ^ (0.01 : ℝ) := Real.rpow_nonneg hxpos.le _
    nlinarith
  · have hx2 : x ^ (2 : ℕ) = x ^ (2 : ℝ) := by norm_cast
    rw [hx2]
    have : α ≤ |αmax| := hα2.trans (le_abs_self _)
    calc 64 * α * Y ≤ 64 * |αmax| * x ^ (1.01 : ℝ) := by
          apply mul_le_mul (by linarith) hY2 hY0.le (by positivity)
      _ ≤ _ := h3

/-- Medium time range consequences. -/
theorem sz_T1 (C b c αmax : ℝ) (hb : 0 ≤ b) (hbc : b < c) :
    ∀ᶠ x : ℝ in atTop, ∀ Y H α : ℝ, x ^ (0.99 : ℝ) ≤ Y → Y ≤ x ^ (1.01 : ℝ) →
      Real.exp (L x ^ c / 2) ≤ H → 0 < α → α ≤ αmax → 2 ≤ Y →
      2 * L x / (H / (α * Y)) + 1 ≤ Y ∧ 2 * L x / (H / (α * Y)) + L x ^ C ≤ x ^ (2 : ℕ) ∧
        2 * (2 * L x / (H / (α * Y))) * (16 * Real.exp (L x ^ b)) ≤ α * Y := by
  have hc : 0 < c := by linarith
  filter_upwards [ev_exp_small_le 64 b c hb hbc (by norm_num),
    ev_exp_small_le (4 * (|αmax| + 1)) 0 c (le_refl 0) hc (by positivity),
    ev_poly_mul_exp_neg 1 C 1 (by norm_num) 0, ev_const_xpow_le 2 1.01 2 (by norm_num),
    ev_x_ge 2, ev_L_ge 1] with x h64 h4 hLC hx2 hx1 hL1
  intro Y H α hY1 hY2 hH hα hαm hY2'
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L x := by linarith
  have hHpos : 0 < H := lt_of_lt_of_le (Real.exp_pos _) hH
  have hYpos : 0 < Y := by linarith
  have hT : 2 * L x / (H / (α * Y)) = 2 * L x * α * Y / H := by field_simp
  rw [hT]
  have hexp1 : (1 : ℝ) ≤ Real.exp (L x ^ (0 : ℝ)) := by rw [Real.rpow_zero]; exact Real.one_le_exp zero_le_one
  have hTY : 2 * L x * α * Y / H ≤ Y / 2 := by
    rw [div_le_iff₀ hHpos]
    have h4' : 4 * (|αmax| + 1) * L x ≤ H := by
      calc 4 * (|αmax| + 1) * L x ≤ 4 * (|αmax| + 1) * L x * Real.exp (L x ^ (0 : ℝ)) :=
            le_mul_of_one_le_right (by positivity) hexp1
        _ ≤ _ := h4
        _ ≤ H := hH
    have : α ≤ |αmax| + 1 := by linarith [le_abs_self αmax]
    calc 2 * L x * α * Y ≤ 2 * L x * (|αmax| + 1) * Y := by gcongr
      _ = Y / 2 * (4 * (|αmax| + 1) * L x) := by ring
      _ ≤ Y / 2 * H := mul_le_mul_of_nonneg_left h4' (by positivity)
  refine ⟨by linarith, ?_, ?_⟩
  · have hLC' : L x ^ C ≤ x := by
      rw [neg_zero, Real.rpow_zero] at hLC
      have := hLC
      rw [one_mul] at this
      have hexp : Real.exp (-(1 * L x)) = 1 / x := by
        rw [one_mul, Real.exp_neg]; unfold L; rw [Real.exp_log hxpos]; ring
      rw [hexp] at this
      rwa [mul_one_div, div_le_iff₀ hxpos, one_mul] at this
    have hxx : x ^ (2 : ℕ) = x ^ (2 : ℝ) := by norm_cast
    have h101 : x ≤ x ^ (1.01 : ℝ) := by
      have := xpow_mono (show 1 ≤ x by linarith) (show (1 : ℝ) ≤ 1.01 by norm_num)
      rwa [Real.rpow_one] at this
    rw [hxx]
    have h0 : 0 ≤ x ^ (1.01 : ℝ) := Real.rpow_nonneg hxpos.le _
    linarith [hx2]
  · have := mul_le_mul_of_nonneg_left (h64.trans hH) (show (0 : ℝ) ≤ α * Y by positivity)
    have e : 2 * (2 * L x * α * Y / H) * (16 * Real.exp (L x ^ b)) =
        α * Y * (64 * L x * Real.exp (L x ^ b)) / H := by field_simp; ring
    rw [e, div_le_iff₀ hHpos]
    exact this

/-- The box-scale condition of the three-range estimate. -/
theorem sz_hz1 (a b τ η αmin αmax : ℝ) (hb : b < 1) (hτ : 0 < τ) (hη : η < 1 / 4)
    (hmin : 0 < αmin) :
    ∀ᶠ x : ℝ in atTop, ∀ Y α P1 P2 : ℝ, x ^ (0.99 : ℝ) ≤ Y → αmin ≤ α → α ≤ αmax →
      Real.exp (L x ^ a) / 2 ≤ P1 → P1 ≤ Real.exp (L x ^ b) → x ^ τ / 2 ≤ P2 → P2 ≤ x ^ η →
      Y ^ (0.6 : ℝ) * (16 * P1 * P2) ≤ α * Y ∧ 4 * α * Y ≤ Y * (P1 * P2) := by
  filter_upwards [ev_exp_xpow_le (16 / αmin) b η 0.396 hb (by linarith) (by positivity),
    ev_const_xpow_le (16 * (|αmax| + 1)) 0 τ hτ, ev_x_ge 1] with x h1 h2 hx1
  intro Y α P1 P2 hY hα1 hα2 hP1a hP1b hP2a hP2b
  have hxpos : 0 < x := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) hY
  have hα : 0 < α := by linarith
  have hP1pos : 0 < P1 := lt_of_lt_of_le (by positivity) hP1a
  have hP2pos : 0 < P2 := lt_of_lt_of_le (by positivity) hP2a
  constructor
  · have hY04 : x ^ (0.396 : ℝ) ≤ Y ^ (0.4 : ℝ) := by
      have : x ^ (0.396 : ℝ) = (x ^ (0.99 : ℝ)) ^ (0.4 : ℝ) := by
        rw [← Real.rpow_mul hxpos.le]; norm_num
      rw [this]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hxpos.le _) hY (by norm_num)
    have hsplit : Y = Y ^ (0.6 : ℝ) * Y ^ (0.4 : ℝ) := by
      rw [← Real.rpow_add hYpos]; norm_num
    have hPP : 16 * P1 * P2 ≤ αmin * Y ^ (0.4 : ℝ) := by
      have hb1 : 16 * P1 * P2 ≤ 16 * Real.exp (L x ^ b) * x ^ η := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hP1b (by norm_num)) hP2b hP2pos.le
          (by positivity)
      have : 16 / αmin * Real.exp (L x ^ b) * x ^ η * αmin = 16 * Real.exp (L x ^ b) * x ^ η := by
        field_simp
      calc 16 * P1 * P2 ≤ 16 * Real.exp (L x ^ b) * x ^ η := hb1
        _ = 16 / αmin * Real.exp (L x ^ b) * x ^ η * αmin := this.symm
        _ ≤ x ^ (0.396 : ℝ) * αmin := mul_le_mul_of_nonneg_right h1 hmin.le
        _ ≤ Y ^ (0.4 : ℝ) * αmin := mul_le_mul_of_nonneg_right hY04 hmin.le
        _ = αmin * Y ^ (0.4 : ℝ) := by ring
    have hY06 : 0 ≤ Y ^ (0.6 : ℝ) := Real.rpow_nonneg hYpos.le _
    calc Y ^ (0.6 : ℝ) * (16 * P1 * P2) ≤ Y ^ (0.6 : ℝ) * (αmin * Y ^ (0.4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hPP hY06
      _ = αmin * (Y ^ (0.6 : ℝ) * Y ^ (0.4 : ℝ)) := by ring
      _ = αmin * Y := by rw [← hsplit]
      _ ≤ α * Y := mul_le_mul_of_nonneg_right hα1 hYpos.le
  · rw [Real.rpow_zero, mul_one] at h2
    have hexp : 1 ≤ Real.exp (L x ^ a) := Real.one_le_exp (Real.rpow_nonneg (by
      unfold L; exact Real.log_nonneg hx1) _)
    have hPP : 4 * α ≤ P1 * P2 := by
      calc 4 * α ≤ 4 * (|αmax| + 1) := by linarith [le_abs_self αmax]
        _ = 16 * (|αmax| + 1) * 1 / 4 := by ring
        _ ≤ x ^ τ * Real.exp (L x ^ a) / 4 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul h2 hexp (by norm_num) (Real.rpow_nonneg hxpos.le _)
        _ = (Real.exp (L x ^ a) / 2) * (x ^ τ / 2) := by ring
        _ ≤ P1 * P2 := mul_le_mul hP1a hP2a (by positivity) hP1pos.le
    nlinarith

/-- The count of exceptional intervals is a small power of `Y`. -/
theorem sz_count (a b K : ℝ) (ha : 0 < a) (hb : b < 1) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop, ∀ Y : ℝ, x ^ (0.99 : ℝ) ≤ Y →
      Real.exp (K * (L x ^ b + L x ^ (1 - a) * Real.log (L x))) ≤ Y ^ (0.05 : ℝ) := by
  filter_upwards [ev_rpow_small b (0.0495 / (2 * K)) 0 hb (by positivity),
    ev_rpow_log_small a (0.0495 / (2 * K)) ha (by positivity), ev_x_ge 1] with x h1 h2 hx1
  intro Y hY
  have hxpos : 0 < x := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) hY
  have hstep : K * (L x ^ b + L x ^ (1 - a) * Real.log (L x)) ≤ 0.0495 * L x := by
    have e : K * (0.0495 / (2 * K) * L x + 0.0495 / (2 * K) * L x) = 0.0495 * L x := by
      field_simp; ring
    rw [← e]
    apply mul_le_mul_of_nonneg_left _ hK.le
    linarith
  calc Real.exp (K * (L x ^ b + L x ^ (1 - a) * Real.log (L x))) ≤ Real.exp (0.0495 * L x) :=
        Real.exp_le_exp.mpr hstep
    _ = (x ^ (0.99 : ℝ)) ^ (0.05 : ℝ) := by
        rw [← Real.rpow_mul hxpos.le, rpow_x_eq hxpos]; norm_num
    _ ≤ Y ^ (0.05 : ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hxpos.le _) hY (by norm_num)

/-- A power of `L` against a positive power of `x`. -/
theorem ev_rpow_le_xpow (c e s : ℝ) (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, L x ^ e ≤ c * x ^ s := by
  filter_upwards [ev_poly_mul_exp_neg (1 / c) e s hs 0, ev_x_ge 1] with x h hx1
  have hxpos : 0 < x := by linarith
  rw [neg_zero, Real.rpow_zero] at h
  rw [rpow_x_eq hxpos]
  have hE : 0 < Real.exp (s * L x) := Real.exp_pos _
  have e1 : Real.exp (-(s * L x)) = (Real.exp (s * L x))⁻¹ := Real.exp_neg _
  rw [e1] at h
  have : 1 / c * L x ^ e ≤ Real.exp (s * L x) := by
    have := mul_le_mul_of_nonneg_right h hE.le
    rwa [mul_assoc, inv_mul_cancel₀ hE.ne', mul_one, one_mul] at this
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hc] at this
  linarith

/-- The Mellin frequency condition. -/
theorem sz_freq (C Cf αmin : ℝ) (hmin : 0 < αmin) :
    ∀ᶠ x : ℝ in atTop, ∀ Y H α : ℝ, x ^ (0.99 : ℝ) ≤ Y → 0 < H → H ≤ x ^ (0.01 : ℝ) →
      αmin ≤ α → L x ^ C + 2 * Real.pi * L x ^ Cf ≤ L x / (H / (α * Y)) := by
  filter_upwards [ev_rpow_le_xpow (αmin / 2) C 0.98 (by norm_num) (by positivity),
    ev_rpow_le_xpow (αmin / (4 * Real.pi)) Cf 0.98 (by norm_num) (by positivity),
    ev_x_ge 1, ev_L_ge 1] with x h1 h2 hx1 hL1
  intro Y H α hY hH0 hH hα
  have hxpos : 0 < x := by linarith
  have hα0 : 0 < α := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) hY
  have hx98 : x ^ (0.98 : ℝ) * x ^ (0.01 : ℝ) = x ^ (0.99 : ℝ) := by
    rw [← Real.rpow_add hxpos]; norm_num
  have hlow : αmin * x ^ (0.98 : ℝ) ≤ L x / (H / (α * Y)) := by
    rw [div_div_eq_mul_div, le_div_iff₀ hH0]
    have hx01 : 0 ≤ x ^ (0.01 : ℝ) := Real.rpow_nonneg hxpos.le _
    calc αmin * x ^ (0.98 : ℝ) * H ≤ αmin * x ^ (0.98 : ℝ) * x ^ (0.01 : ℝ) :=
          mul_le_mul_of_nonneg_left hH (by positivity)
      _ = αmin * x ^ (0.99 : ℝ) := by rw [mul_assoc, hx98]
      _ ≤ α * Y := mul_le_mul hα hY (Real.rpow_nonneg hxpos.le _) hα0.le
      _ ≤ L x * (α * Y) := le_mul_of_one_le_left (by positivity) hL1
  have e2 : 2 * Real.pi * (αmin / (4 * Real.pi) * x ^ (0.98 : ℝ)) = αmin / 2 * x ^ (0.98 : ℝ) := by
    field_simp; ring
  have h2' : 2 * Real.pi * L x ^ Cf ≤ αmin / 2 * x ^ (0.98 : ℝ) := by
    rw [← e2]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

/-- The removed primes are far below the size scale. -/
theorem sz_err (b lo : ℝ) (hb : b < 1) (hlo : 0 < lo) :
    ∀ᶠ x : ℝ in atTop, ∀ Y : ℝ, x ^ (0.99 : ℝ) ≤ Y → ∀ p : ℕ, (p : ℝ) ≤ Real.exp (L x ^ b) →
      ((p ^ 2 : ℕ) : ℝ) ≤ lo * Y := by
  filter_upwards [ev_rpow_small b (0.99 / 2) (-(Real.log lo) / 2) hb (by norm_num), ev_x_ge 1]
    with x h hx1
  intro Y hY p hp
  have hxpos : 0 < x := by linarith
  push_cast
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  calc (p : ℝ) ^ 2 ≤ Real.exp (L x ^ b) ^ 2 := pow_le_pow_left₀ hp0 hp 2
    _ = Real.exp (2 * L x ^ b) := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ Real.exp (Real.log lo + 0.99 * L x) := Real.exp_le_exp.mpr (by linarith)
    _ = lo * x ^ (0.99 : ℝ) := by rw [Real.exp_add, Real.exp_log hlo, rpow_x_eq hxpos]
    _ ≤ lo * Y := mul_le_mul_of_nonneg_left hY hlo.le

/-- `W x` exceeds the group primes and polylogarithmic moduli. -/
theorem sz_W (C d : ℝ) (hd : d < 1 / 2) :
    ∀ᶠ x : ℝ in atTop, L x ^ (2 * C) < W x ∧ Real.exp (L x ^ d) < W x := by
  have hlog := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).comp_tendsto tendsto_L
  have hev := hlog.def (show (0 : ℝ) < 1 / (4 * |C| + 1) by positivity)
  filter_upwards [hev, ev_L_ge 2] with x hx hL2
  have hLpos : 0 < L x := by linarith
  have hL1 : 1 < L x := by linarith
  simp only [Function.comp, Real.norm_eq_abs] at hx
  rw [abs_of_nonneg (Real.log_nonneg hL1.le), abs_of_nonneg (Real.rpow_nonneg hLpos.le _)] at hx
  have hsqrt : Real.sqrt (L x) = L x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (L x)
  unfold W
  rw [hsqrt]
  have hpos : 0 < L x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hLpos _
  constructor
  · rw [← Real.exp_log (Real.rpow_pos_of_pos hLpos (2 * C)), Real.log_rpow hLpos]
    apply Real.exp_lt_exp.mpr
    have h1 : 2 * C * Real.log (L x) ≤ 2 * |C| * Real.log (L x) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (Real.log_nonneg hL1.le)
    have h2 : 2 * |C| * Real.log (L x) ≤ 2 * |C| * (1 / (4 * |C| + 1) * L x ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    have h3 : 2 * |C| * (1 / (4 * |C| + 1) * L x ^ (1 / 2 : ℝ)) < L x ^ (1 / 2 : ℝ) := by
      rw [← mul_assoc, mul_one_div]
      have : 2 * |C| / (4 * |C| + 1) < 1 := by
        rw [div_lt_one (by positivity)]; linarith [abs_nonneg C]
      nlinarith
    linarith
  · exact Real.exp_lt_exp.mpr (Real.rpow_lt_rpow_of_exponent_lt hL1 hd)

theorem sz_B {Lx C B B0 : ℝ} (hL : 2 ≤ Lx) (h1 : 2 * C ≤ B) (h2 : B0 + 1 ≤ B) (h3 : C + 1 ≤ B) :
    Lx ^ (2 * C) ≤ Lx ^ B ∧ Lx ^ B0 + Lx ^ C ≤ Lx ^ B := by
  have hLpos : 0 < Lx := by linarith
  have hL1 : 1 ≤ Lx := by linarith
  refine ⟨Real.rpow_le_rpow_of_exponent_le hL1 h1, ?_⟩
  have hB : Lx ^ B = Lx ^ (B - 1) * Lx := by
    rw [← Real.rpow_add_one hLpos.ne']; congr 1; ring
  have e1 : Lx ^ B0 ≤ Lx ^ (B - 1) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have e2 : Lx ^ C ≤ Lx ^ (B - 1) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have e3 : 0 ≤ Lx ^ (B - 1) := Real.rpow_nonneg hLpos.le _
  rw [hB]; nlinarith

/-- Polylogarithmic quantities are below the smallest group prime. -/
theorem sz_expa (C a : ℝ) (ha : 0 < a) : ∀ᶠ x : ℝ in atTop, L x ^ C < Real.exp (L x ^ a) := by
  have hlog := (isLittleO_log_rpow_atTop ha).comp_tendsto tendsto_L
  have hev := hlog.def (show (0 : ℝ) < 1 / (2 * |C| + 1) by positivity)
  filter_upwards [hev, ev_L_ge 2] with x hx hL2
  have hLpos : 0 < L x := by linarith
  have hL1 : 1 < L x := by linarith
  simp only [Function.comp, Real.norm_eq_abs] at hx
  rw [abs_of_nonneg (Real.log_nonneg hL1.le), abs_of_nonneg (Real.rpow_nonneg hLpos.le _)] at hx
  rw [← Real.exp_log (Real.rpow_pos_of_pos hLpos C), Real.log_rpow hLpos]
  apply Real.exp_lt_exp.mpr
  have hpos : 0 < L x ^ a := Real.rpow_pos_of_pos hLpos _
  have h1 : C * Real.log (L x) ≤ |C| * Real.log (L x) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (Real.log_nonneg hL1.le)
  have h2 : |C| * Real.log (L x) ≤ |C| * (1 / (2 * |C| + 1) * L x ^ a) :=
    mul_le_mul_of_nonneg_left hx (abs_nonneg C)
  have h3 : |C| * (1 / (2 * |C| + 1) * L x ^ a) < L x ^ a := by
    rw [← mul_assoc, mul_one_div]
    have : |C| / (2 * |C| + 1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [abs_nonneg C]
    nlinarith
  linarith

end Erdos821.P5Marked
