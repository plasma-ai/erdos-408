import Erdos821.S2.SpanGhostWeightTask
import Erdos821.S2.SpanEdge

/-! Original active-mark costs and one reciprocal charge per prime lifespan. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

def SpanMarkWeightTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m)
    (Q : ResiduePath A n) (S : LifespanAssignment P n),
    Q.Valid → Q.lifespanValid S →
    (∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k) →
    ∀ g : P.BigGroup, P.V g.val ≠ 0 →
      (∏ j : Fin (J + F.ell), tiltedMu F P n g.val (Q.labels 0 g.val j)) *
        (∏ i : Fin n,
          (∏ j : Fin (J + F.ell),
            if (A.pattern (Q.pattern i)).shared g.val j ∨ j ∈ Q.promotionSlots S i g then 1
            else tiltedMu F P n g.val (Q.target i g.val j)) *
          (P.V g.val) ^ (-((Q.promotionSlots S i g).card : ℤ))) *
        (∏ i : Fin (n + 1), ∏ p : P.Prime g.val, Q.spanGhostFactor S i g p) =
      (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ) *
        (∏ i : Fin n, (P.V g.val) ^ (-((A.pattern (Q.pattern i)).t g.val : ℤ))) *
        (∏ p : P.Prime g.val, Q.spanWeight g p (S g p))


end Erdos821.S2Core
