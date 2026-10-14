import Erdos821.P5MarkedEnergy.FinalAux

/-! Uniform simplifications of the piece bound. -/

noncomputable section
open scoped BigOperators
open Classical

namespace Erdos821.P5Marked
open Blueprint.Analytic

/-- The uniform three-range bound. -/
def PhiJ (ℓ K3r c3r As Al Kl B0 B C Cmk vmax : ℝ) : ℝ :=
  K3r * ((ℓ ^ (-As)) ^ 2 * (1 + 16 * ℓ) * (ℓ ^ C * ℓ ^ C * ℓ ^ Cmk) ^ 2 * (2 * ℓ) ^ c3r +
    (Kl * ℓ ^ (-Al)) ^ 2 * (ℓ ^ C * ℓ ^ C * (vmax * ℓ ^ Cmk)) ^ 2 * (2 * ℓ) ^ c3r * (2 * ℓ)) +
  2 * ℓ ^ B0 * ((ℓ ^ (-B)) ^ 2 * (ℓ ^ C * (vmax * ℓ ^ Cmk)) ^ 2)

/-- The uniform weighted mean value. -/
def PhiW (ℓ KW cW C Cmk : ℝ) : ℝ :=
  KW * (16 * (1 + 2 * ℓ)) * ((ℓ ^ C * ℓ ^ C * ℓ ^ Cmk) ^ 2 * (2 * ℓ) ^ cW)

theorem J3_le_PhiJ {ℓ K3r c3r As Al Kl B0 B C Cmk vmax m : ℝ} (hℓ : 0 < ℓ) (hK : 0 ≤ K3r)
    (hm : 0 < m) (hmv : m ≤ vmax) :
    K3r * (((m⁻¹ * ℓ ^ (-As)) ^ 2 * (1 + 16 * ℓ) *
        (ℓ ^ C * (ℓ ^ C * (m * ℓ ^ Cmk))) ^ 2 * (2 * ℓ) ^ c3r) +
      (Kl * ℓ ^ (-Al)) ^ 2 * (ℓ ^ C * (ℓ ^ C * (m * ℓ ^ Cmk))) ^ 2 * (2 * ℓ) ^ c3r * (2 * ℓ)) +
      2 * ℓ ^ B0 * ((ℓ ^ (-B)) ^ 2 * (ℓ ^ C * (m * ℓ ^ Cmk)) ^ 2) ≤
    PhiJ ℓ K3r c3r As Al Kl B0 B C Cmk vmax := by
  unfold PhiJ
  have e1 : (m⁻¹ * ℓ ^ (-As)) ^ 2 * (1 + 16 * ℓ) * (ℓ ^ C * (ℓ ^ C * (m * ℓ ^ Cmk))) ^ 2 *
      (2 * ℓ) ^ c3r = (ℓ ^ (-As)) ^ 2 * (1 + 16 * ℓ) * (ℓ ^ C * ℓ ^ C * ℓ ^ Cmk) ^ 2 *
      (2 * ℓ) ^ c3r := by
    field_simp
  rw [e1]
  have hC : 0 ≤ ℓ ^ C := Real.rpow_nonneg hℓ.le _
  have hCm : 0 ≤ ℓ ^ Cmk := Real.rpow_nonneg hℓ.le _
  have hc3 : 0 ≤ (2 * ℓ) ^ c3r := Real.rpow_nonneg (by positivity) _
  have hB0 : 0 ≤ ℓ ^ B0 := Real.rpow_nonneg hℓ.le _
  have hmm : m * ℓ ^ Cmk ≤ vmax * ℓ ^ Cmk := mul_le_mul_of_nonneg_right hmv hCm
  have h2 : (ℓ ^ C * (ℓ ^ C * (m * ℓ ^ Cmk))) ^ 2 ≤ (ℓ ^ C * ℓ ^ C * (vmax * ℓ ^ Cmk)) ^ 2 := by
    rw [← mul_assoc]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left hmm (by positivity)
  have h3 : (ℓ ^ C * (m * ℓ ^ Cmk)) ^ 2 ≤ (ℓ ^ C * (vmax * ℓ ^ Cmk)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hmm hC) 2
  gcongr

theorem WM_eq_PhiW {ℓ KW cW C Cmk m : ℝ} (hm : 0 < m) :
    KW * (16 * (1 + 2 * ℓ)) *
        ((ℓ ^ C * m⁻¹ * 1 * (ℓ ^ C * (m * ℓ ^ Cmk))) ^ 2 * (2 * ℓ) ^ cW) =
      PhiW ℓ KW cW C Cmk := by
  unfold PhiW
  field_simp

/-- The piece bound with uniform atoms. -/
theorem piece_rhs_le {KLM α αmin Y cR cRb A1 A1b J3 J3b w WM WMb εt εb SqT : ℝ}
    (hKLM : 0 ≤ KLM) (hα : αmin ≤ α) (hαmin : 0 < αmin) (hY : 0 < Y) (hcR0 : 0 ≤ cR)
    (hcR : cR ≤ cRb) (hA1 : 0 ≤ A1) (hA1b : A1 ≤ A1b) (hJ0 : 0 ≤ J3) (hJ : J3 ≤ J3b) (hw : 0 ≤ w)
    (hWM0 : 0 ≤ WM) (hWM : WM ≤ WMb) (hεt0 : 0 ≤ εt) (hεt : εt ≤ εb) :
    KLM / (α * Y) * (Y ^ 2 * (cR * A1 * (cR * (A1 * (J3 + w * WM) + εt * WM)))) + SqT ≤
      Y * (KLM / αmin * (cRb * A1b * (cRb * (A1b * (J3b + w * WMb) + εb * WMb)))) + SqT := by
  have hα0 : 0 < α := lt_of_lt_of_le hαmin hα
  have e : KLM / (α * Y) * (Y ^ 2 * (cR * A1 * (cR * (A1 * (J3 + w * WM) + εt * WM)))) =
      Y * (KLM / α * (cR * A1 * (cR * (A1 * (J3 + w * WM) + εt * WM)))) := by
    field_simp
  rw [e]
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ hY.le
  have h1 : KLM / α ≤ KLM / αmin := div_le_div_of_nonneg_left hKLM hαmin hα
  have hcRb : 0 ≤ cRb := hcR0.trans hcR
  have hJb : 0 ≤ J3b := hJ0.trans hJ
  have hWb : 0 ≤ WMb := hWM0.trans hWM
  have hεb : 0 ≤ εb := hεt0.trans hεt
  have hA1b0 : 0 ≤ A1b := hA1.trans hA1b
  gcongr

theorem card_relBoxes_le (K : ℕ) (αY : ℝ) : ((relBoxes K αY).card : ℝ) ≤ ((K : ℝ) + 1) ^ 4 := by
  have h : (relBoxes K αY).card ≤ (allBoxes K).card := Finset.card_filter_le _ _
  have h2 : (allBoxes K).card = (K + 1) ^ 4 := by
    simp [allBoxes, Finset.card_product]; ring
  have : ((relBoxes K αY).card : ℝ) ≤ (((K + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast h.trans h2.le
  push_cast at this
  exact this

theorem log2_floor_le {x z : ℝ} (hx : 1 ≤ x) (hz : 1 ≤ z) (hzx : z ≤ x ^ (2 : ℕ)) :
    ((Nat.log 2 ⌊z⌋₊ : ℕ) : ℝ) ≤ 3 * L x := by
  set N := ⌊z⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hz)
  have hpow : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hNz : (N : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hpowR : (2 : ℝ) ^ Nat.log 2 N ≤ x ^ (2 : ℕ) := by
    have : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpow
    push_cast at this
    linarith
  have hlog := Real.log_le_log (by positivity) hpowR
  rw [Real.log_pow, Real.log_pow] at hlog
  have hl2 : (2 : ℝ) / 3 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hLx : 0 ≤ Real.log x := Real.log_nonneg hx
  unfold L
  push_cast at hlog
  nlinarith

end Erdos821.P5Marked
