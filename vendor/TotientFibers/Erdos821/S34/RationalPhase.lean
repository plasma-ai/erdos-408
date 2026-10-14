import Erdos821.S34.LogMultiplier
import Erdos821.P5.Basic

set_option autoImplicit false

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by simp [e, Complex.norm_exp]

theorem rational_phase_split (n θ β ζ : ℝ) (u : ℤ) (r : ℕ)
    (hn : 0 < n) (hθ : θ = (u : ℝ) / r + β) :
    mellin n ζ * e (θ * n) = logMultiplier ζ β (Real.log n) * e ((u : ℝ) * n / r) := by
  unfold Blueprint.Analytic.mellin e logMultiplier unitPhase
  rw [Real.exp_log hn, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [hθ]
  push_cast
  ring

end
end Erdos821.S34Core
