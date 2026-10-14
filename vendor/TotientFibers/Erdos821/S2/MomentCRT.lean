import Erdos821.S2.ClosedPaths
import Erdos821.Blueprint.Transference

/-! The physical expansion and relative CRT error give a root-moment comparison. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ} (A : Model F P J m)

theorem averagedMoment_eq_closed (hPath : PhysicalPathExpansionTask)
    (r : ℕ) (hr : 0 < r) (X : ℝ) :
    A.averagedMoment r X =
      (Complex.ofReal (((dyad X).card : ℝ)⁻¹) *
        ∑ z ∈ dyad X, closedPhysicalExpression A (2 * r) z).re := by
  unfold Model.averagedMoment
  simp_rw [hPath F P J m r A hr]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp [dyad, div_eq_mul_inv, mul_comm]

theorem averagedMoment_replacement_bound (hPath : PhysicalPathExpansionTask)
    (r : ℕ) (hr : 0 < r) (X epsilon : ℝ)
    (hreplace : ∀ Q : ResiduePath A (2 * r), Q.Valid →
      |((dyad X).card : ℝ)⁻¹ * ∑ z ∈ dyad X,
          P.pathFactor (2 * r) (visitQ F.q (2 * r)) Q.offset Q.active z -
        P.residueExpectation (2 * r) (visitQ F.q (2 * r)) Q.offset Q.active| ≤
      epsilon * P.residueExpectation (2 * r) (visitQ F.q (2 * r)) Q.offset Q.active) :
    |A.averagedMoment r X - (closedResidueExpression A (2 * r)).re| ≤
      epsilon * closedAbsoluteResidueExpression A (2 * r) := by
  rw [averagedMoment_eq_closed A hPath r hr X]
  have hn := closed_replacement_bound A (2 * r) X epsilon hreplace
  have hreal := Complex.abs_re_le_norm
    (Complex.ofReal (((dyad X).card : ℝ)⁻¹) *
      (∑ z ∈ dyad X, closedPhysicalExpression A (2 * r) z) -
      closedResidueExpression A (2 * r))
  simpa only [Complex.sub_re] using hreal.trans hn


end Erdos821.S2Core
