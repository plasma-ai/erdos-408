import Erdos821.S2.SpanLifecycle
import Erdos821.S2.LifespanEnds
import Erdos821.S2.OrphanResidues

/-! The finite one-prime lifespan sum, including the absent and orphan cases. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

def SpanSumTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m)
    (Q : ResiduePath A n) (g : P.BigGroup) (p : P.Prime g.val),
    baselinePrime F n p.val ≠ 0 →
    (∑ span : PrimeSpan n, Q.spanWeight g p span) =
      (baselinePrime F n p.val)⁻¹ *
        onePrimeExpectation p.val (n + 1) (eta F n)
          (fun i => (Q.offset i : ZMod p.val)) (Q.activeVisits g p)


end Erdos821.S2Core
