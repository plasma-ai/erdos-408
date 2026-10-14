import Erdos821.S2.SpanHistory

/-! Signed coefficients and phases are unchanged by the lifespan construction. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

namespace ResiduePath

variable {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n)

def edgeOscillation (theta : ℝ) (i : Fin n) : ℂ :=
  let ν := A.pattern (Q.pattern i)
  let D := ν.D (Q.source i) (Q.free i)
  let uBig : P.BigAux J := fun g => Q.free i g.val
  let z := ν.coefficient (P.restrictBig (Q.source i)) (P.restrictBig (Q.target i)) uBig *
    imaginaryPower D A.zeta
  let zr := star (ν.coefficient (P.restrictBig (Q.target i)) (P.restrictBig (Q.source i)) uBig *
    imaginaryPower D A.zeta)
  (if edgeForward i then z else zr) * phase (theta * (Q.step i : ℝ))

theorem edgeCoefficient_split (theta : ℝ) (i : Fin n) :
    Q.edgeCoefficient theta i =
      (edgeSymmetryFactor P (J + F.ell) *
        (A.pattern (Q.pattern i)).auxMass (Q.free i) *
        (A.pattern (Q.pattern i)).physicalTargetMass : ℝ) * Q.edgeOscillation theta i := by
  dsimp only [edgeCoefficient, edgeOscillation]
  rw [mul_assoc]

def reconstructedRawWeight (S : LifespanAssignment P n) (y : P.SmallResidues)
    (rho : ℝ) (i : Fin n) : ℝ :=
  rawEdgeWeight A n rho (A.pattern (Q.pattern i)) (Q.free i)
    (permuteActive (Q.sourcePerm i) (Q.stateAfter S y i.castSucc))
    (permuteActive (Q.targetPerm i) (Q.stateBefore S y i.succ))
    (Q.reconstructedTransferChoice S y i)

theorem reconstructed_edge_coefficient (S : LifespanAssignment P n)
    (hS : Q.lifespanValid S) (y : P.SmallResidues) (rho theta : ℝ) (i : Fin n) :
    edgeChoiceCoefficient A n rho theta i
        ((Q.reconstructedHistory S hS y).after i.castSucc)
        ((Q.reconstructedHistory S hS y).before i.succ)
        ((Q.reconstructedHistory S hS y).edge i) =
      (Q.reconstructedRawWeight S y rho i : ℂ) * Q.edgeOscillation theta i := by
  dsimp only [reconstructedHistory, edgeChoiceCoefficient, reconstructedRawWeight,
    edgeOscillation, stateAfter, stateBefore, permuteActive, source, target, step]
  rw [mul_assoc]

def reconstructedScalarWeight (S : LifespanAssignment P n) (hS : Q.lifespanValid S)
    (y : P.SmallResidues) (rho : ℝ) : ℝ :=
  P.memoryMass F J n (Q.stateBefore S y 0) *
    (∏ i : Fin (n + 1), ghostChoiceWeight F n rho i (Q.reconstructedGhostChoice S hS y i)) *
    (∏ i : Fin n, edgeSymmetryFactor P (J + F.ell) * Q.reconstructedRawWeight S y rho i)

theorem reconstructed_weight_split (S : LifespanAssignment P n)
    (hS : Q.lifespanValid S) (y : P.SmallResidues) (rho theta : ℝ) :
    (Q.reconstructedHistory S hS y).Weight rho theta =
      (Q.reconstructedScalarWeight S hS y rho : ℂ) * ∏ i : Fin n, Q.edgeOscillation theta i := by
  unfold MemoryHistory.Weight
  simp_rw [Q.reconstructed_edge_coefficient S hS y rho theta]
  simp only [reconstructedHistory, reconstructedScalarWeight, Complex.ofReal_mul,
    Complex.ofReal_prod, Finset.prod_mul_distrib]
  ac_rfl


end ResiduePath
end Erdos821.S2Core
