import Erdos821.S2.ResiduePaths

/-! The finite physical path expansion before CRT replaces the root residue. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

def closedPhysicalExpression {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n : ℕ) (z : ℤ) : ℂ :=
  ∑ Q : ResiduePath A n,
    if Q.Valid ∧ Q.offset (Fin.last n) = 0 then
      (P.markMass (J + F.ell) : ℂ) * (∏ i : Fin n, Q.edgeCoefficient 0 i) *
        (P.pathFactor n (visitQ F.q n) Q.offset Q.active z : ℂ)
    else 0

def PhysicalPathExpansionTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J m r : ℕ) (A : Model F P J m),
    0 < r → ∀ z : ℤ,
      A.rootMoment r z = (closedPhysicalExpression A (2 * r) z).re


end Erdos821.S2Core
