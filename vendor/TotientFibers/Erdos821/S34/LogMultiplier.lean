import Erdos821.S34.CellCosts

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

def unitPhase (t : ℝ) : ℂ := Complex.exp (Complex.I * t)

theorem norm_unitPhase (t : ℝ) : ‖unitPhase t‖ = 1 := by
  simp [unitPhase, Complex.norm_exp]

theorem unitPhase_add (s t : ℝ) : unitPhase (s + t) = unitPhase s * unitPhase t := by
  simp only [unitPhase, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem norm_unitPhase_sub (s t : ℝ) : ‖unitPhase s - unitPhase t‖ ≤ |s - t| := by
  have he : unitPhase s - unitPhase t = unitPhase t * (unitPhase (s - t) - 1) := by
    rw [mul_sub, ← unitPhase_add]
    congr 1
    · congr 1
      ring
    · ring
  rw [he, norm_mul, norm_unitPhase, one_mul]
  simpa only [unitPhase, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := s - t))

def logMultiplier (ζ β v : ℝ) : ℂ := unitPhase (ζ * v + 2 * Real.pi * β * Real.exp v)

theorem norm_logMultiplier (ζ β v : ℝ) : ‖logMultiplier ζ β v‖ = 1 := norm_unitPhase _

theorem exp_difference_bound (u v H : ℝ) (hu : u ≤ H) (hv : v ≤ H) :
    |Real.exp v - Real.exp u| ≤ Real.exp H * |v - u| := by
  have hb : ∀ t ∈ Set.Iic H, ‖deriv Real.exp t‖ ≤ Real.exp H := by
    intro t ht
    rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
    exact Real.exp_le_exp.mpr ht
  simpa only [Real.norm_eq_abs] using
    (Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t (_ht : t ∈ Set.Iic H) => Real.differentiableAt_exp) hb
      (convex_Iic H) hu hv)

theorem logMultiplier_difference (ζ β u v H : ℝ) (hu : u ≤ H) (hv : v ≤ H) :
    ‖logMultiplier ζ β v - logMultiplier ζ β u‖ ≤
      (|ζ| + 2 * Real.pi * |β| * Real.exp H) * |v - u| := by
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have hβ : 0 ≤ 2 * Real.pi * |β| := by positivity
  calc
    _ ≤ |(ζ * v + 2 * Real.pi * β * Real.exp v) -
          (ζ * u + 2 * Real.pi * β * Real.exp u)| := norm_unitPhase_sub _ _
    _ = |ζ * (v - u) + (2 * Real.pi * β) * (Real.exp v - Real.exp u)| := by congr 1; ring
    _ ≤ |ζ * (v - u)| + |(2 * Real.pi * β) * (Real.exp v - Real.exp u)| := abs_add_le _ _
    _ = |ζ| * |v - u| + (2 * Real.pi * |β|) * |Real.exp v - Real.exp u| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hπ]
    _ ≤ |ζ| * |v - u| + (2 * Real.pi * |β|) * (Real.exp H * |v - u|) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (exp_difference_bound u v H hu hv) hβ)
    _ = _ := by ring

end
end Erdos821.S34Core
