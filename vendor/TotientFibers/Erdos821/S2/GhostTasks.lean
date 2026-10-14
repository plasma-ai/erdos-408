import Erdos821.S2.MemoryGhost
import Erdos821.Blueprint.Transference

/-! Frozen independently verifiable P3 helper tasks. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

/-- Source §2 ghost joint-integral / adjoint identity, with numerical multiplicities.
The scale is one normally and two in the memory-tail majorant. -/
def GhostAdjointTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J n : ℕ) (r : MemoryParameters F),
    (∀ g, 0 < P.V g) →
    (∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val) →
    ∀ (d : ℝ), (d = 1 ∨ d = 2) → ∀ i : Fin (n + 1),
    ∀ s t : P.MemoryState (J + F.ell),
      P.memoryMass F J n s * absoluteScaledMemoryGhostKernel F J n r.rho d i s t =
        P.memoryMass F J n t * ghostReversalFactor d t s *
          absoluteScaledMemoryGhostKernel F J n r.rho d i t s

/-- Absolute ghost row bounds for both factorial adjoint directions.
Convergence is part of the task; divergent real tsums must not supply a bound. -/
def GhostRowsTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J n : ℕ) (r : MemoryParameters F),
    (∀ g, 0 < P.V g ∧ P.V g ≤ F.vMax) →
    (∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val) →
    (∀ g : P.BigGroup, (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ≤ 2) →
    ∀ (d : ℝ), (d = 1 ∨ d = 2) → ∀ i : Fin (n + 1),
    ∀ s : P.MemoryState (J + F.ell),
      Summable (fun t => absoluteScaledMemoryGhostKernel F J n r.rho d i s t *
        P.memoryWeight r.v t) ∧
      (∑' t, absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) ≤
        (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card * P.memoryWeight r.v s ∧
      Summable (fun t => ghostReversalFactor d s t *
        absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) ∧
      (∑' t, ghostReversalFactor d s t * absoluteScaledMemoryGhostKernel F J n r.rho d i s t *
        P.memoryWeight r.v t) ≤
        (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card * P.memoryWeight r.v s

/-- Source §2 endpoint consequence on the literal physical kernels.
Both premises are arguments, not uses of their unproved blueprint declarations. -/
def PairingFromMomentTask : Prop :=
  AbsolutePhysicalBounds → TransferenceEstimate → TransferencePairing

end Erdos821.S2Core

