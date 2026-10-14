import Erdos821.P4Probe.RawKernel
import Erdos821.P4Probe.CancellationTasks

set_option autoImplicit false

namespace Erdos821.P4Probe
open Blueprint.Graph

lemma imaginaryPower_eq_mellin (n : ℕ) (ζ : ℝ) :
    imaginaryPower n ζ = Blueprint.Analytic.mellin n ζ := by
  unfold imaginaryPower Blueprint.Analytic.mellin
  congr 1
  ring

lemma imaginaryPower_mul (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (ζ : ℝ) :
    imaginaryPower (n * k) ζ = imaginaryPower n ζ * imaginaryPower k ζ := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold imaginaryPower
  rw [← Complex.exp_add]
  congr 1
  simp only [Nat.cast_mul, Real.log_mul hn' hk', Complex.ofReal_add]
  ring

lemma phase_mul_shift (θ C D : ℝ) :
    phase (θ * (C * D)) = Blueprint.Analytic.e ((θ * C) * D) := by
  unfold phase Blueprint.Analytic.e
  congr 1
  ring

end Erdos821.P4Probe
