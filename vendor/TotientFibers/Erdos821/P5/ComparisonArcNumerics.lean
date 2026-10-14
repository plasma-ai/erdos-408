import Erdos821.P5.ComparisonFourierArcBound

noncomputable section

namespace Erdos821.P5Core

theorem comparison_arc_cross_sqrt (Y L D C₂ Carc Ks Ke : ℝ)
    (hY : 0 < Y) (hL : 0 < L) (hKs : 0 ≤ Ks) (hKe : 0 ≤ Ke) :
    Real.sqrt (Ke * Y * L ^ (-(2 * D + 4 * Carc + C₂))) *
      Real.sqrt (Ks * Y * L ^ C₂) =
      Real.sqrt (Ke * Ks) * Y * L ^ (-D - 2 * Carc) := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ Ke * Y * L ^ (-(2 * D + 4 * Carc + C₂)))]
  have he : (Ke * Y * L ^ (-(2 * D + 4 * Carc + C₂))) * (Ks * Y * L ^ C₂) =
      (Ke * Ks) * (Y * L ^ (-D - 2 * Carc)) ^ 2 := by
    calc
      _ = (Ke * Ks) * Y ^ 2 *
          (L ^ (-(2 * D + 4 * Carc + C₂)) * L ^ C₂) := by ring
      _ = (Ke * Ks) * Y ^ 2 * L ^ (-(2 * D + 4 * Carc + C₂) + C₂) := by
        rw [← Real.rpow_add hL]
      _ = _ := by
        rw [show -(2 * D + 4 * Carc + C₂) + C₂ =
          (-D - 2 * Carc) + (-D - 2 * Carc) by ring, Real.rpow_add hL]
        ring
  rw [he, Real.sqrt_mul (mul_nonneg hKe hKs), Real.sqrt_sq (by positivity)]
  ring

/-- The outside 1/Y cancels both square-norm factors. The chosen energy
exponent pays the full 4 L^(2 Carc) arc count. -/
theorem comparison_arc_log_bound (Y L D C₂ Carc Ks Ke Km N : ℝ)
    (hY : 0 < Y) (hL : 0 < L) (hKs : 0 ≤ Ks) (hKe : 0 ≤ Ke)
    (hN : N ≤ 4 * L ^ (2 * Carc)) :
    Y⁻¹ * ((Km * L ^ (-(D + C₂))) * Real.sqrt (Ks * Y * L ^ C₂) *
        Real.sqrt (Ks * Y * L ^ C₂) +
      N * Real.sqrt (Ke * Y * L ^ (-(2 * D + 4 * Carc + C₂))) *
        Real.sqrt (Ks * Y * L ^ C₂)) ≤
      (Km * Ks + 4 * Real.sqrt (Ke * Ks)) * L ^ (-D) := by
  have hminor : (Km * L ^ (-(D + C₂))) * Real.sqrt (Ks * Y * L ^ C₂) *
      Real.sqrt (Ks * Y * L ^ C₂) = Km * Ks * Y * L ^ (-D) := by
    calc
      _ = Km * L ^ (-(D + C₂)) *
          (Real.sqrt (Ks * Y * L ^ C₂) * Real.sqrt (Ks * Y * L ^ C₂)) := by ring
      _ = Km * L ^ (-(D + C₂)) * (Ks * Y * L ^ C₂) := by
        rw [Real.mul_self_sqrt (by positivity : 0 ≤ Ks * Y * L ^ C₂)]
      _ = Km * Ks * Y * (L ^ (-(D + C₂)) * L ^ C₂) := by ring
      _ = _ := by rw [← Real.rpow_add hL, show -(D + C₂) + C₂ = -D by ring]
  have hcross := comparison_arc_cross_sqrt Y L D C₂ Carc Ks Ke hY hL hKs hKe
  calc
    _ ≤ Y⁻¹ * ((Km * L ^ (-(D + C₂))) * Real.sqrt (Ks * Y * L ^ C₂) *
        Real.sqrt (Ks * Y * L ^ C₂) +
      (4 * L ^ (2 * Carc)) * Real.sqrt (Ke * Y * L ^ (-(2 * D + 4 * Carc + C₂))) *
        Real.sqrt (Ks * Y * L ^ C₂)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hY.le)
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hN (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [hminor]
      have hmajor : (4 * L ^ (2 * Carc)) *
          Real.sqrt (Ke * Y * L ^ (-(2 * D + 4 * Carc + C₂))) *
          Real.sqrt (Ks * Y * L ^ C₂) =
          4 * Real.sqrt (Ke * Ks) * Y * L ^ (-D) := by
        calc
          _ = (4 * L ^ (2 * Carc)) *
              (Real.sqrt (Ke * Y * L ^ (-(2 * D + 4 * Carc + C₂))) *
                Real.sqrt (Ks * Y * L ^ C₂)) := by ring
          _ = _ := by
            rw [hcross]
            calc
              _ = 4 * Real.sqrt (Ke * Ks) * Y *
                  (L ^ (2 * Carc) * L ^ (-D - 2 * Carc)) := by ring
              _ = _ := by rw [← Real.rpow_add hL, show 2 * Carc + (-D - 2 * Carc) = -D by ring]
      rw [hmajor]
      field_simp [hY.ne']

end Erdos821.P5Core
