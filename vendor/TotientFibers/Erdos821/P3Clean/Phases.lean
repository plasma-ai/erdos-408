import Erdos821.P3Clean.FiniteFourier

/-! Unit character factors can be absorbed into the ideal frequency. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem phase_nat_mul (theta : ℝ) (n : ℕ) :
    phase (theta * n) = phase theta ^ n := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem exists_phase_of_norm_one (z : ℂ) (h : ‖z‖ = 1) :
    ∃ theta : ℝ, phase theta = z := by
  refine ⟨z.arg / (2 * Real.pi), ?_⟩
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (mul_pos two_pos Real.pi_pos)
  have he : (2 : ℝ) * Real.pi * (z.arg / (2 * Real.pi)) = z.arg :=
    mul_div_cancel₀ _ hpi
  unfold phase
  have hc : (2 : ℂ) * (Real.pi : ℂ) * ((z.arg / (2 * Real.pi) : ℝ) : ℂ) = (z.arg : ℂ) := by
    exact_mod_cast he
  rw [hc]
  simpa only [h, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I z

theorem character_nsmul_phase {G : Type*} [AddCommGroup G] [Finite G]
    (ψ : AddChar G ℂ) (d : G) :
    ∃ theta : ℝ, ∀ n : ℕ, ψ (n • d) = phase (theta * n) := by
  obtain ⟨theta, ht⟩ := exists_phase_of_norm_one (ψ d) (ψ.norm_apply d)
  refine ⟨theta, ?_⟩
  intro n
  rw [AddChar.map_nsmul_eq_pow, ← ht, phase_nat_mul]

theorem imaginaryPower_mul (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (zeta : ℝ) :
    imaginaryPower (a * b) zeta = imaginaryPower a zeta * imaginaryPower b zeta := by
  unfold imaginaryPower
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (ne_of_gt ha))
    (by exact_mod_cast (ne_of_gt hb)), ← Complex.exp_add]
  congr 1
  push_cast
  ring


end Erdos821.P3Clean
