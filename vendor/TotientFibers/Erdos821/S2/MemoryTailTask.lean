import Erdos821.S2.HistoryFinite

/-! The memory tail from doubled original ghost births and absolute rows. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

/-- The finite mass at the initial empty-memory boundary. Absolute values
allow the structural tail estimate to use only its explicit row hypotheses. -/
def initialMemoryBoundaryMass {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (_A : Model F P J m) (n : ℕ) : ℝ :=
  ∑ y : P.SmallResidues, ∑ a : P.Labels (J + F.ell),
    |P.memoryMass F J n (y, a, fun _ => 0)|

/-- No signed edge norm, CRT statement or lifespan identity is an input.
The integer exponent retains the store capacity when B is larger than it. -/
def MemoryTailTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m)
    (rho v theta CG CE : ℝ),
    1 ≤ v → 0 ≤ CG → 0 ≤ CE →
    (∀ (i : Fin (n + 1)) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteScaledMemoryGhostKernel F J n rho 2 i s t *
        P.memoryWeight v t) ∧
      (∑' t, absoluteScaledMemoryGhostKernel F J n rho 2 i s t *
        P.memoryWeight v t) ≤ CG * P.memoryWeight v s) →
    (∀ (i : Fin n) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteMemoryEdgeKernel A n rho theta i .all s t *
        P.memoryWeight v t) ∧
      (∑' t, absoluteMemoryEdgeKernel A n rho theta i .all s t *
        P.memoryWeight v t) ≤ CE * P.memoryWeight v s) →
    ∀ B : ℕ,
      (∑' H : MemoryHistory A n,
        if H.Valid ∧ H.DistinctBirths ∧ ¬ H.Truncated B then ‖H.Weight rho theta‖ else 0) ≤
        (2 : ℝ) ^ (((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) - (B : ℤ)) *
          CG ^ (n + 1) * CE ^ n * initialMemoryBoundaryMass A n


end Erdos821.S2Core
