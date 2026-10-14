import Erdos821.P5.Basic

noncomputable section

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem shared_shift_factor (DR DC : ℕ) (w k : ℤ) :
    (DR : ℤ) * w + k * ((DR * DC : ℕ) : ℤ) =
      (DR : ℤ) * (w + k * (DC : ℤ)) := by
  push_cast
  ring

theorem shared_shift_positive (DR DC : ℕ) (hD : 0 < DR) (w k : ℤ) :
    0 < (DR : ℤ) * w + k * ((DR * DC : ℕ) : ℤ) ↔ 0 < w + k * (DC : ℤ) := by
  rw [shared_shift_factor]
  have hDZ : (0 : ℤ) < DR := by exact_mod_cast hD
  exact mul_pos_iff_of_pos_left hDZ

/-- Removing the shared product leaves only the free-product Mellin ratios. -/
theorem shared_mellin_cancellation (DR DC w w' a₁ a₂ : ℝ)
    (hDR : 0 < DR) (hDC : 0 < DC) (hw : 0 < w) (hw' : 0 < w') :
    mellin (DR * w) a₁ * mellin (DR * w') a₂ * mellin (DR * DC) (-a₁ - a₂) =
      mellin (w / DC) a₁ * mellin (w' / DC) a₂ := by
  unfold Blueprint.Analytic.mellin
  simp only [Real.log_mul hDR.ne' hw.ne', Real.log_mul hDR.ne' hw'.ne',
    Real.log_mul hDR.ne' hDC.ne', Real.log_div hw.ne' hDC.ne',
    Real.log_div hw'.ne' hDC.ne']
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Both the cutoff argument and its harmonic weight reindex exactly.
Only the removed shared factor must be nonzero; the field identities also
cover a vanishing remaining denominator. -/
theorem shared_cutoff_reindex (Ψ : ℝ → ℂ) (DR DC Z w : ℝ) (hDR : DR ≠ 0) :
    Ψ ((DR * w) / (Z * (DR * DC))) / ((DR * w : ℝ) : ℂ) =
      (DR : ℂ)⁻¹ * (Ψ (w / (Z * DC)) / (w : ℂ)) := by
  have harg : (DR * w) / (Z * (DR * DC)) = w / (Z * DC) := by
    calc
      _ = (DR * w) / (DR * (Z * DC)) := by congr 1; ring
      _ = (DR * DR⁻¹) * (w / (Z * DC)) := by simp only [div_eq_mul_inv, mul_inv]; ring
      _ = _ := by rw [mul_inv_cancel₀ hDR, one_mul]
  rw [harg]
  simp only [Complex.ofReal_mul, div_eq_mul_inv, mul_inv]
  ring

end Erdos821.P5Core
