import Erdos821.S34.FrameBridge
import Erdos821.S34.CellCosts

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

theorem cellKernel_star (G : PrimeGroups) (k : Fin G.size → ℕ) (Q : ℕ)
    (h ξ : ℝ) (D X : ℕ) :
    star (cellKernel G k Q h ξ D X) = cellKernel G k Q h ξ X D := by
  by_cases hc : cell h D = cell h X
  · unfold cellKernel
    rw [hc]
    simp only [true_and]
    split_ifs
    · simp [map_sum, mul_comm]
    · simp
  · simp [cellKernel, hc, Ne.symm hc]

def cellTransposeApply (G : PrimeGroups) (k : Fin G.size → ℕ) (Q : ℕ)
    (h ξ : ℝ) (f : Tuple G k → ℂ) (D : Tuple G k) : ℂ :=
  expect G k (fun X => cellKernel G k Q h ξ (product G k D) (product G k X) * f X)

theorem cellTransposeApply_eq (G : PrimeGroups) (k : Fin G.size → ℕ) (Q : ℕ)
    (h ξ : ℝ) (f : Tuple G k → ℂ) :
    cellTransposeApply G k Q h ξ f = fun D => star (cellApply G k Q h ξ (fun X => star (f X)) D) := by
  funext D
  simp only [cellTransposeApply, cellApply, expect, star_sum, star_mul, star_star,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  apply Finset.sum_congr rfl
  intro X _
  have hs := cellKernel_star G k Q h ξ (product G k X) (product G k D)
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    congrArg (fun z : ℂ => (tupleWeight G k X : ℂ) * z * f X) hs.symm

theorem tupleNorm_star (G : PrimeGroups) (k : Fin G.size → ℕ) (f : Tuple G k → ℂ) :
    tupleNorm G k (fun X => star (f X)) = tupleNorm G k f := by
  simp only [tupleNorm, norm_star]

theorem cell_transpose_operator_norm (G : PrimeGroups) (k : Fin G.size → ℕ) (Q : ℕ)
    (h ξ δ : ℝ) (hξ : 0 < ξ) (hδ : 0 ≤ δ)
    (hgram : ∀ j : ℤ, ξ ≤ cellMass G k h j →
      ∀ χ ∈ primitiveCharacters Q, ∀ ψ ∈ primitiveCharacters Q, χ ≠ ψ →
      ‖expect G k (fun z => if cell h (product G k z) = j then
        star (charValue χ (product G k z)) * charValue ψ (product G k z) else 0)‖ ≤ δ)
    (f : Tuple G k → ℂ) :
    tupleNorm G k (cellTransposeApply G k Q h ξ f) ≤
      (1 + (Q : ℝ) ^ 2 * δ / ξ) * tupleNorm G k f := by
  rw [cellTransposeApply_eq, tupleNorm_star]
  simpa only [tupleNorm_star] using cell_operator_norm G k Q h ξ δ hξ hδ hgram (fun X => star (f X))

end
end Erdos821.S34Core
