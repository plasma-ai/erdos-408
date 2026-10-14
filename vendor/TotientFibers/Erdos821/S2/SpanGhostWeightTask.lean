import Erdos821.S2.SpanGhost

/-! Factorial-normalized ghost coefficients factor over distinct prime lifespans. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

namespace ResiduePath

variable {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
  {A : Model F P J m} (Q : ResiduePath A n)

def spanGhostFactor (S : LifespanAssignment P n) (i : Fin (n + 1))
    (g : P.BigGroup) (p : P.Prime g.val) : ℝ :=
  (if Q.ghostBirthAt g p (S g p) i then
    -eta F n i * (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) *
  (if Q.ghostStopAt g p (S g p) i then -eta F n i else 1) *
  (if Q.pendingBefore g p (S g p) i ∧ Q.pendingAfter g p (S g p) i ∧
      ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val) = 0 then
    visitQ F.q n i else 1)

end ResiduePath

def SpanGhostWeightTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m)
    (Q : ResiduePath A n) (S : LifespanAssignment P n),
    (∀ g, P.V g ≠ 0) → ∀ hS : Q.lifespanValid S,
    ∀ (y : P.SmallResidues) (i : Fin (n + 1)),
      ghostChoiceWeight F n 1 i (Q.reconstructedGhostChoice S hS y i) *
          (∏ g : P.BigGroup, ((Q.ghostBirthPrimes S i g).card.factorial : ℝ)) =
        ∏ g : P.BigGroup, ∏ p : P.Prime g.val, Q.spanGhostFactor S i g p


end Erdos821.S2Core
