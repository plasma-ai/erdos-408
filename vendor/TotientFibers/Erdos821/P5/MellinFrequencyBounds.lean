import Erdos821.P5.DyadicTransference

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem graph_intervalBigGroups (P : Geometry) (x : ℝ) (G : PrimeGroups)
    (hG : Admissible P x G) : intervalBigGroups G.graph := by
  intro g
  apply hG.2.2.2.2 g.val
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, of_decide_eq_true g.property⟩

theorem eventual_mellin_shift_frequency_bound (C Cf : ℝ) (hC : 0 < C) :
    0 ≤ max C Cf + 1 ∧ ∀ᶠ x : ℝ in atTop, ∀ (a₁ a₂ ζ : ℝ) (ξ : Fin 1 → ℝ),
      |a₁| ≤ L x ^ C → |a₂| ≤ L x ^ C → ζ = -a₁ - a₂ → ‖ξ‖ ≤ L x ^ Cf →
      |ζ - mellinFrequency ξ| ≤ L x ^ (max C Cf + 1) := by
  refine ⟨by linarith [le_max_left C Cf], ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 + 2 * Real.pi)] with x hL hlarge
  change 1 ≤ L x at hL
  change 2 + 2 * Real.pi ≤ L x at hlarge
  intro a₁ a₂ ζ ξ ha₁ ha₂ hζ hξ
  have hz : |ζ| ≤ 2 * L x ^ C := by
    rw [hζ, show -a₁ - a₂ = -(a₁ + a₂) by ring, abs_neg]
    exact (abs_add_le a₁ a₂).trans (by linarith)
  have hcoordinate : |ξ 0| ≤ L x ^ Cf := by
    have hcoord : |ξ 0| ≤ ‖ξ‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm ξ 0
    exact hcoord.trans hξ
  have hv : |mellinFrequency ξ| ≤ 2 * Real.pi * L x ^ Cf := by
    unfold mellinFrequency
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact mul_le_mul_of_nonneg_left hcoordinate (by positivity)
  have hCgrow := Real.rpow_le_rpow_of_exponent_le hL (le_max_left C Cf)
  have hFgrow := Real.rpow_le_rpow_of_exponent_le hL (le_max_right C Cf)
  have hs : |ζ - mellinFrequency ξ| ≤ (2 + 2 * Real.pi) * L x ^ (max C Cf) := by
    have htri : |ζ - mellinFrequency ξ| ≤ |ζ| + |mellinFrequency ξ| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le ζ 0 (mellinFrequency ξ)
    nlinarith [Real.pi_pos]
  calc
    _ ≤ (2 + 2 * Real.pi) * L x ^ (max C Cf) := hs
    _ ≤ L x * L x ^ (max C Cf) :=
      mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg (by linarith : 0 ≤ L x) _)
    _ = _ := by rw [Real.rpow_add (by linarith : 0 < L x), Real.rpow_one]; ring

end Erdos821.P5Core
