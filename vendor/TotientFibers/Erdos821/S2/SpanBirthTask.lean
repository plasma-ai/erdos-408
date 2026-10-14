import Erdos821.S2.SpanHistory

/-! A prime lifespan creates exactly one original birth in the inverse history. -/

noncomputable section
namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

def SpanBirthTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m)
    (Q : ResiduePath A n) (S : LifespanAssignment P n),
    Q.Valid → ∀ hS : Q.lifespanValid S,
    (∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k) →
    ∀ y : P.SmallResidues, (Q.reconstructedHistory S hS y).DistinctBirths


end Erdos821.S2Core
