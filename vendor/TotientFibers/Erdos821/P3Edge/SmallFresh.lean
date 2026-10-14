import Erdos821.P3Edge.PowRho
import Erdos821.Leaves.Damped

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

/-- Small fresh-label counts against `q` damping, uniformly in the
remaining-zero count. This is the small-group analogue of
`eq:promotion-count`, with fixed `ell` in place of `a ≤ ell+m`. -/
lemma small_count_damp (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (ell : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ, ell ≤ Y →
      (Y : ℝ) ^ ell * q ^ ((((Y - ell : ℕ)) : ℝ) / 2) ≤ C := by
  classical
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hsq1 : Real.sqrt q < 1 := by
    have h := Real.sqrt_lt_sqrt hq0.le hq1
    simpa using h
  obtain ⟨C₀, hC₀pos, hC₀⟩ := pow_mul_rho_bound (Real.sqrt q) hsq0 hsq1 ell
  refine ⟨C₀ / (Real.sqrt q) ^ ell, div_pos hC₀pos (pow_pos hsq0 _), fun Y hY => ?_⟩
  have hsq : q ^ ((((Y - ell : ℕ)) : ℝ) / 2) = (Real.sqrt q) ^ (Y - ell) :=
    Erdos821.GraphLemmas.sqrt_pow_eq q hq0 (Y - ell)
  have hnum : (Y : ℝ) ^ ell * (Real.sqrt q) ^ Y ≤ C₀ := hC₀ ell (le_refl _) Y
  have hpow : (Real.sqrt q) ^ (Y - ell) * (Real.sqrt q) ^ ell
      = (Real.sqrt q) ^ Y := by
    have hY2 : Y - ell + ell = Y := Nat.sub_add_cancel hY
    calc (Real.sqrt q) ^ (Y - ell) * (Real.sqrt q) ^ ell
        = (Real.sqrt q) ^ ((Y - ell) + ell) := by rw [pow_add]
      _ = (Real.sqrt q) ^ Y := by rw [hY2]
  have hfin : (Y : ℝ) ^ ell * (Real.sqrt q) ^ (Y - ell) ≤ C₀ / (Real.sqrt q) ^ ell := by
    rw [le_div_iff₀ (pow_pos hsq0 _)]
    have heq : (Y : ℝ) ^ ell * (Real.sqrt q) ^ (Y - ell) * (Real.sqrt q) ^ ell
        = (Y : ℝ) ^ ell * (Real.sqrt q) ^ Y := by
      calc _ = (Y : ℝ) ^ ell * ((Real.sqrt q) ^ (Y - ell) * (Real.sqrt q) ^ ell) := by
              ring
        _ = _ := by rw [hpow]
    rw [heq]
    exact hnum
  calc (Y : ℝ) ^ ell * q ^ ((((Y - ell : ℕ)) : ℝ) / 2)
      = (Y : ℝ) ^ ell * (Real.sqrt q) ^ (Y - ell) := by rw [hsq]
    _ ≤ C₀ / (Real.sqrt q) ^ ell := hfin

end Erdos821.P3Edge
