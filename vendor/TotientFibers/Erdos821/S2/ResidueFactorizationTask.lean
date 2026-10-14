import Erdos821.S2.SpanEdgeValidity
import Erdos821.S2.PrimeLifespans

/-! Separate small conditional damping from independent big-prime expectations. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

namespace ResiduePath

variable {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
  (Q : ResiduePath A n)

def smallResidueExpression : ℝ :=
  (Fintype.card P.SmallResidues : ℝ)⁻¹ * ∑ y : P.SmallResidues,
    if Q.SmallCompatible y then
      ∏ i : Fin n, smallDamping (P := P) F J
          (translateSmallResidues (Q.offset i.castSucc) y) *
        smallDamping (P := P) F J (translateSmallResidues (Q.offset i.succ) y)
    else 0

end ResiduePath

def ResidueFactorizationTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m)
    (Q : ResiduePath A n), 0 < n → Q.Valid →
      P.residueExpectation n (visitQ F.q n) Q.offset Q.active =
        Q.smallResidueExpression *
          ∏ g : P.BigGroup, ∏ p : P.Prime g.val,
            onePrimeExpectation p.val (n + 1) (eta F n)
              (fun i => (Q.offset i : ZMod p.val)) (Q.activeVisits g p)


end Erdos821.S2Core
