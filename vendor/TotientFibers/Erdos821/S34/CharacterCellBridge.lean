import Erdos821.P4Cell.CharacterCellTask
import Erdos821.P1.ClassicalInputs
import Erdos821.S34.EventualFrame

set_option autoImplicit false
open Filter

namespace Erdos821.S34Core

theorem characterCellTask_proof : CharacterCellTask :=
  Erdos821.P4Cell.CharacterCellTask_proof

open Blueprint.Analytic

/-- The uniform frame norm estimate with the harmonic input discharged. -/
theorem cell_operator_norm_eventual (P : Geometry) (m : ℕ) (qexp ξexp : ℝ)
    (hq : 0 < qexp) (hξexp : 0 < ξexp) :
    ∀ᶠ x in atTop, ∀ G : PrimeGroups, Admissible P x G →
      ∀ k, bigSlots G k m → ∀ (Q : ℕ) (h : ℝ), (Q : ℝ) ≤ L x ^ qexp → 0 < h →
      ∀ f : Tuple G k → ℂ,
        tupleNorm G k (cellApply G k Q h (L x ^ (-ξexp)) f) ≤ 2 * tupleNorm G k f ∧
        tupleNorm G k (cellTransposeApply G k Q h (L x ^ (-ξexp)) f) ≤ 2 * tupleNorm G k f :=
  eventually_cell_operator_norm characterCellTask_proof Blueprint.classical_inputs.harmonic
    P m qexp ξexp hq hξexp

end Erdos821.S34Core
