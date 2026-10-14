import Erdos821.P5.ComparisonEnergyTransport

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- Increasing the fixed logarithmic exponent preserves all endpoint data. -/
theorem comparison_endpoint_bound_enlarge (x C C' τ η : ℝ) (E : Endpoint)
    (hL : 1 ≤ L x) (hC : C ≤ C') (hE : EndpointBound x C τ η E) :
    EndpointBound x C' τ η E := by
  obtain ⟨hτ, hτη, hη, hc, hr, hmod, hσ₀, hσ₁, hlo, hI, hhi⟩ := hE
  have hp := Real.rpow_le_rpow_of_exponent_le hL hC
  exact ⟨hτ, hτη, hη, fun n => ⟨(hc n).1.trans hp, (hc n).2.trans hp⟩,
    hr, hmod.trans hp, hσ₀.trans hp, hσ₁.trans hp, hlo, hI, hhi⟩

theorem comparison_energy_frequency_bound (x C Cv a v : ℝ) (hL : 2 ≤ L x)
    (ha : |a| ≤ L x ^ C) (hv : |v| ≤ L x ^ Cv) :
    |-a - v| ≤ L x ^ (max C Cv + 1) := by
  have hL1 : 1 ≤ L x := by linarith
  have hLp : 0 < L x := by linarith
  have ha' := ha.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left C Cv))
  have hv' := hv.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right C Cv))
  calc
    _ = |a + v| := by rw [show -a - v = -(a + v) by ring, abs_neg]
    _ ≤ |a| + |v| := abs_add_le _ _
    _ ≤ 2 * L x ^ (max C Cv) := by linarith
    _ ≤ L x * L x ^ (max C Cv) :=
      mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hLp.le _)
    _ = _ := by rw [Real.rpow_add hLp, Real.rpow_one]; ring

end Erdos821.P5Core
