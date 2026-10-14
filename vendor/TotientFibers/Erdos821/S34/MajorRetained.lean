import Erdos821.S34.MajorCharacter
import Erdos821.S34.DyadicMultiplier
import Erdos821.S34.TupleBilinear

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

def comparisonScalar (G : PrimeGroups) (a b : Fin G.size → ℕ)
    (Q : ℕ) (h ξ θ ζ : ℝ) (X : Tuple G a) (Y : Tuple G b) : ℂ :=
  expect G a (fun D => expect G b (fun E =>
    cellKernel G a Q h ξ (product G a D) (product G a X) *
    cellKernel G b Q h ξ (product G b E) (product G b Y) * tuplePhase G a b θ ζ D E))

theorem major_retained_comparison (hfourier : RationalFourierTask) (hind : PrimitiveInductionTask)
    (G : PrimeGroups) (a b : Fin G.size → ℕ) (Q r : ℕ) (u : ℤ)
    (h ξ U V S θ β ζ ε : ℝ) (hr : 1 ≤ r) (hrQ : r ≤ Q)
    (hh : 0 < h) (hh2 : h ≤ Real.log 2) (hξ : 0 < ξ)
    (hU : 0 < U) (hV : 0 < V) (hS : 0 ≤ S)
    (hθ : θ = (u : ℝ) / r + β) (hβ : |β| * (U * V) ≤ 2 * S)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (X : Tuple G a) (Y : Tuple G b)
    (hX : U ≤ (product G a X : ℝ) ∧ (product G a X : ℝ) ≤ 2 * U)
    (hY : V ≤ (product G b Y : ℝ) ∧ (product G b Y : ℝ) ≤ 2 * V)
    (hcopA : ∀ D : Tuple G a, Nat.Coprime (product G a D) r)
    (hcopB : ∀ E : Tuple G b, Nat.Coprime (product G b E) r)
    (hrepA : ∀ χ ∈ primitiveCharacters Q,
      ‖cellApply G a Q h ξ (fun D => charValue χ (product G a D)) X - charValue χ (product G a X)‖ ≤ ε)
    (hrepB : ∀ χ ∈ primitiveCharacters Q,
      ‖cellApply G b Q h ξ (fun E => charValue χ (product G b E)) Y - charValue χ (product G b Y)‖ ≤ ε) :
    ‖tuplePhase G a b θ ζ X Y - comparisonScalar G a b Q h ξ θ ζ X Y‖ ≤
      (Q : ℝ) ^ 4 * (2 * h * (|ζ| + 64 * Real.pi * S)) + 3 * ε * Real.sqrt (r.totient : ℝ) := by
  let rational := fun D : Tuple G a => fun E : Tuple G b =>
    e ((u : ℝ) * (product G a D * product G b E) / r)
  let M := fun D : Tuple G a => fun E : Tuple G b =>
    logMultiplier ζ β (Real.log (product G a D * product G b E))
  let I := expect G a (fun D => expect G b (fun E =>
    cellKernel G a Q h ξ (product G a D) (product G a X) *
    cellKernel G b Q h ξ (product G b E) (product G b Y) * rational D E))
  have hsplit (D : Tuple G a) (E : Tuple G b) : tuplePhase G a b θ ζ D E = M D E * rational D E := by
    have hD : (0 : ℝ) < product G a D := by exact_mod_cast tuple_product_pos G a D
    have hE : (0 : ℝ) < product G b E := by exact_mod_cast tuple_product_pos G b E
    simpa only [tuplePhase, M, rational, mul_assoc] using
      rational_phase_split ((product G a D : ℝ) * product G b E) θ β ζ u r (mul_pos hD hE) hθ
  have hfreeze_eq : comparisonScalar G a b Q h ξ θ ζ X Y - M X Y * I =
      expect G a (fun D => expect G b (fun E =>
        cellKernel G a Q h ξ (product G a D) (product G a X) *
        cellKernel G b Q h ξ (product G b E) (product G b Y) *
        (M D E - M X Y) * rational D E)) := by
    simp only [comparisonScalar, I, expect, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro D _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro E _
    rw [hsplit]
    ring
  have hfreeze : ‖comparisonScalar G a b Q h ξ θ ζ X Y - M X Y * I‖ ≤
      (Q : ℝ) ^ 4 * (2 * h * (|ζ| + 64 * Real.pi * S)) := by
    rw [hfreeze_eq]
    exact dyadic_multiplier_freeze G a b Q h ξ U V S β ζ u r hh hh2 hξ hU hV hS hβ X Y hX hY
  have hrepro : ‖I - rational X Y‖ ≤ 3 * ε * Real.sqrt (r.totient : ℝ) :=
    rational_kernel_reproduction hfourier hind G a b Q r u h ξ ε hr hrQ hε hε1 X Y hcopA hcopB hrepA hrepB
  have heq : tuplePhase G a b θ ζ X Y - comparisonScalar G a b Q h ξ θ ζ X Y =
      M X Y * (rational X Y - I) - (comparisonScalar G a b Q h ξ θ ζ X Y - M X Y * I) := by
    rw [hsplit]
    ring
  rw [heq]
  have hnM : ‖M X Y‖ = 1 := norm_logMultiplier _ _ _
  calc
    _ ≤ ‖M X Y * (rational X Y - I)‖ + ‖comparisonScalar G a b Q h ξ θ ζ X Y - M X Y * I‖ := norm_sub_le _ _
    _ = ‖I - rational X Y‖ + ‖comparisonScalar G a b Q h ξ θ ζ X Y - M X Y * I‖ := by
      rw [norm_mul, hnM, one_mul, norm_sub_rev]
    _ ≤ _ := by linarith [hrepro, hfreeze]

end
end Erdos821.S34Core
