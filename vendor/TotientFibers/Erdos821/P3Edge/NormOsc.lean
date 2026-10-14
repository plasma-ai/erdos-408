import Erdos821.S2.MemoryEdge
import Mathlib

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

lemma norm_imaginaryPower (n : ℕ) (ζ : ℝ) : ‖imaginaryPower n ζ‖ = 1 := by
  unfold imaginaryPower
  rw [Complex.norm_exp]
  have h0 : (ζ * Real.log (↑n : ℝ) * Complex.I).re = 0 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [h0, Real.exp_zero]

lemma norm_phase (t : ℝ) : ‖phase t‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  have h0 : (2 * Real.pi * t * Complex.I).re = 0 := by
    simp
  rw [h0, Real.exp_zero]

end Erdos821.P3Edge
