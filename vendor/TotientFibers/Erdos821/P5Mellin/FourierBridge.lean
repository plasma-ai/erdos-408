import Erdos821.P5Mellin.DerivativeTransfer

namespace Erdos821.P5Mellin

open Erdos821.Blueprint.Analytic

theorem mellinCharacter_eq_fourier (ξ : Fin 1 → ℝ) (t : ℝ) :
    e (∑ i, ξ i * Real.log t) = mellin t (2 * Real.pi * ξ 0) := by
  rw [Erdos821.Blueprint.Analytic.e, Erdos821.Blueprint.Analytic.mellin]
  congr 1
  simp
  ring

end Erdos821.P5Mellin
