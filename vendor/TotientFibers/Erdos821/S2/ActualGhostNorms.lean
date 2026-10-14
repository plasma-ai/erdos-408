import Erdos821.S2.MemoryMassBounds
import Erdos821.S2.NormProjection
import Erdos821.P3Adj.Adjoint
import Erdos821.P3Rows.GhostRows

/-! Concrete absolute ghost norm bounds, including local birth phases and cutoffs. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups}

theorem actual_scaled_ghost_norm (F : FixedData) (J n : ℕ) (r : MemoryParameters F)
    (hV : ∀ g, 0 < P.V g ∧ P.V g ≤ F.vMax)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hmu : ∀ g : P.BigGroup, ∑ p : P.Prime g.val, tiltedMu F P n g.val p ≤ 2)
    (i : Fin (n + 1)) (d : ℝ) (hd : d = 1 ∨ d = 2)
    (K : P.MemoryState (J + F.ell) → P.MemoryState (J + F.ell) → ℂ)
    (hbound : ∀ s t, ‖K s t‖ ≤ absoluteScaledMemoryGhostKernel F J n r.rho d i s t) :
    NormBound (P.memoryMass F J n) K
      ((Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card) :=
  scaled_ghost_domination_of_tasks GhostAdjointTask_proof GhostRowsTask_proof
    F J n r hV hb hmu i d hd K hbound

theorem actual_projected_ghost_norm (F : FixedData) (J n B : ℕ) (r : MemoryParameters F)
    (hV : ∀ g, 0 < P.V g ∧ P.V g ≤ F.vMax)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hmu : ∀ g : P.BigGroup, ∑ p : P.Prime g.val, tiltedMu F P n g.val p ≤ 2)
    (i : Fin (n + 1))
    (phi : (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℂ)
    (hphi : ∀ s t c, ‖phi s t c‖ ≤ 1) :
    NormBound (P.memoryMass F J n)
      (projectKernel (fun s => P.memorySize s ≤ B) (memoryGhostKernel F J n r.rho i phi))
      ((Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card) := by
  apply normBound_project
  · exact (pow_pos (Real.exp_pos _) _).le
  · exact memoryMass_nonneg F J n (fun g => (hV g).1) hb
  · exact ghost_norm_of_tasks GhostAdjointTask_proof GhostRowsTask_proof F J n r hV hb hmu i phi hphi


end Erdos821.S2Core
