import Erdos821.P5MarkedEnergy.MellinBox
import Erdos821.P5MarkedEnergy.Weights
import Erdos821.P5MarkedEnergy.Decomposition

/-! The energy of one smooth piece: local Mellin energy, Mellin-separated box
sum, and the split of each box integral into the medium range and the tail. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos821.P5Marked
open Blueprint.Analytic P5Core

theorem piece_energy_core {ι : Type*} (Rel : Finset ι) (Pb : ι → ℝ → ℂ)
    (hPc : ∀ β, Continuous (Pb β)) (Mb : ι → ℝ) (hPb : ∀ β t, ‖Pb β t‖ ≤ Mb β)
    (s : Finset ℕ) (bco : ℕ → ℂ) (Y Yi H Lx v R A1 εt J3 WM KLM : ℝ) (j : ℕ)
    (b : (Fin 1 → ℝ) → ℂ) (hb : Integrable b)
    (hj : 4 ≤ j) (hL : 1 ≤ Lx) (hYi : 0 < Yi) (hH : 0 < H) (hKLM : 0 ≤ KLM)
    (hJ30 : 0 ≤ J3) (hWM0 : 0 ≤ WM) (hR : 0 ≤ R)
    (hLM : ∫ θ in (-1 / H)..(1 / H), ‖localAdditivePolynomial s bco θ‖ ^ 2 ≤
      KLM / Yi * (∫ t : ℝ, (1 + |H / Yi * t|) ^ (-(j : ℤ)) * ‖dp s bco t‖ ^ 2) +
        KLM * (H / Yi) ^ 2 * sqNorm s bco)
    (hD : ∀ t, dp s bco t = (Y : ℂ) * ∑ β ∈ Rel, ∫ ξ, b ξ * Pb β (t + v + 2 * Real.pi * ξ 0))
    (hA1 : ∫ ξ, ‖b ξ‖ ≤ A1) (htail : ∫ ξ in {ξ : Fin 1 → ℝ | R < ‖ξ‖}, ‖b ξ‖ ≤ εt)
    (hJ3 : ∀ β ∈ Rel, ∫ t in (-(2 * Lx / (H / Yi)))..(2 * Lx / (H / Yi)), ‖Pb β t‖ ^ 2 ≤ J3)
    (hWM : ∀ β ∈ Rel, ∀ c : ℝ, Integrable (fun t => wt (H / Yi) t * ‖Pb β (t + c)‖ ^ 2) ∧
      ∫ t, wt (H / Yi) t * ‖Pb β (t + c)‖ ^ 2 ≤ WM)
    (hfreq : |v| + 2 * Real.pi * R ≤ Lx / (H / Yi)) :
    ∫ θ in (-1 / H)..(1 / H), ‖localAdditivePolynomial s bco θ‖ ^ 2 ≤
      KLM / Yi * (Y ^ 2 * (Rel.card * A1 * ∑ β ∈ Rel,
          (A1 * (J3 + ((1 + Lx) ^ (j - 4))⁻¹ * WM) + εt * WM))) +
        KLM * (H / Yi) ^ 2 * sqNorm s bco := by
  set h' := H / Yi with hh'
  have hh'pos : 0 < h' := by positivity
  refine hLM.trans ?_
  refine add_le_add ?_ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  -- the weight is `wj`
  have hwj : ∀ t, (1 + |h' * t|) ^ (-(j : ℤ)) = wj j h' t := fun t => rfl
  simp_rw [hwj]
  set D' : ℝ → ℂ := fun t => ∑ β ∈ Rel, ∫ ξ, b ξ * Pb β (t + v + 2 * Real.pi * ξ 0) with hD'
  have hdp : ∀ t, ‖dp s bco t‖ ^ 2 = Y ^ 2 * ‖D' t‖ ^ 2 := by
    intro t
    rw [hD t, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  simp_rw [hdp]
  have heq : ∫ t, wj j h' t * (Y ^ 2 * ‖D' t‖ ^ 2) = Y ^ 2 * ∫ t, wj j h' t * ‖D' t‖ ^ 2 := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg Y)
  have hj2 : 2 ≤ j := by omega
  have hJm : ∀ β ∈ Rel, ∀ ξ : Fin 1 → ℝ, ‖ξ‖ ≤ R →
      ∫ t, wj j h' t * ‖Pb β (t + v + 2 * Real.pi * ξ 0)‖ ^ 2 ≤
        J3 + ((1 + Lx) ^ (j - 4))⁻¹ * WM := by
    intro β hβ ξ hξ
    have hc : |v + 2 * Real.pi * ξ 0| ≤ Lx / h' := by
      have hξ0 : |ξ 0| ≤ R := (norm_le_pi_norm ξ 0).trans hξ
      calc |v + 2 * Real.pi * ξ 0| ≤ |v| + |2 * Real.pi * ξ 0| := abs_add_le _ _
        _ = |v| + 2 * Real.pi * |ξ 0| := by
            rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        _ ≤ |v| + 2 * Real.pi * R := by gcongr
        _ ≤ _ := hfreq
    have hint0 := (hWM β hβ 0).1
    simp only [add_zero] at hint0
    have hsplit := wj_integral_split hj hh'pos hL hc (Pb β) (hPc β) hint0
    have hfun : (fun t => wj j h' t * ‖Pb β (t + v + 2 * Real.pi * ξ 0)‖ ^ 2) =
        fun t => wj j h' t * ‖Pb β (t + (v + 2 * Real.pi * ξ 0))‖ ^ 2 := by
      funext t; rw [add_assoc]
    rw [hfun]
    refine hsplit.trans (add_le_add (hJ3 β hβ) ?_)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := (hWM β hβ 0).2
    simp only [add_zero] at this
    exact this
  have hJa : ∀ β ∈ Rel, ∀ ξ : Fin 1 → ℝ,
      ∫ t, wj j h' t * ‖Pb β (t + v + 2 * Real.pi * ξ 0)‖ ^ 2 ≤ WM := by
    intro β hβ ξ
    obtain ⟨hint, hle⟩ := hWM β hβ (v + 2 * Real.pi * ξ 0)
    have hfun : (fun t => wj j h' t * ‖Pb β (t + v + 2 * Real.pi * ξ 0)‖ ^ 2) =
        fun t => wj j h' t * ‖Pb β (t + (v + 2 * Real.pi * ξ 0))‖ ^ 2 := by
      funext t; rw [add_assoc]
    rw [hfun]
    refine le_trans ?_ hle
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun t =>
      mul_nonneg (wj_nonneg j h' t) (by positivity)) hint
    exact Filter.Eventually.of_forall fun t =>
      mul_le_mul_of_nonneg_right (wj_le_wt hj2 h' t) (by positivity)
  exact mellin_box_energy Rel b hb Pb hPc Mb hPb (wj j h') (integrable_wj hj2 hh'pos.ne')
    (continuous_wj j h') (wj_nonneg j h') v R A1 εt
    (fun _ => J3 + ((1 + Lx) ^ (j - 4))⁻¹ * WM) (fun _ => WM)
    (fun _ => by positivity) (fun _ => hWM0) hA1 htail hJm hJa D' (fun t => rfl)

end Erdos821.P5Marked
