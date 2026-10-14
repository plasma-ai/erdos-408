import Erdos821.P4Probe.RawModel
import Erdos821.P4Probe.CancellationTasks

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

def bigCoordinateAverage (P : PrimeGroups) (M : ℕ)
    (S : P.BigGroup → Finset (Fin M)) (f : P.BigLabels M → ℂ) (a : P.BigLabels M) : ℂ :=
  ∑ y, (P.idealMass y : ℂ) * f (fun g i => if i ∈ S g then y g i else a g i)

def patternSideCoordinates {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (g : P.BigGroup) : Finset (Fin (J + ell)) :=
  if block g = side then (ν.changed g.val).image ν.slot else ∅

def onePatternFamily (F : FixedData) (P : PrimeGroups) (J m : ℕ)
    (ν : Pattern P J F.ell m) : Family F P J m where
  count := 1
  pattern := fun _ => ν

def idealFullPair {P : PrimeGroups} {M : ℕ} (K : P.BigLabels M → P.BigLabels M → ℂ)
    (f g : P.BigLabels M → ℂ) : ℂ :=
  ∑ a, ∑ b, (P.idealMass a : ℂ) * star (f a) * K a b * g b

def idealVectorNorm (P : PrimeGroups) (M : ℕ) (f : P.BigLabels M → ℂ) : ℝ :=
  Real.sqrt (∑ a, P.idealMass a * ‖f a‖ ^ 2)

/-- Exact one-pattern conditional comparison bridge, before permutations.
The signed comparison has coefficient -sigma KA KB. Average the unused
source A coordinates and target B coordinates. Condition on all shared
first-J coordinates, whose positive product C changes frequency to theta*C
and contributes a unit Mellin factor. Identify selectedCellMass with the
analytic free-tuple cellMass by unused-coordinate integration; all required
side counts are positive and <=m. Apply LocalComparison, then weighted
Cauchy--Schwarz over shared labels. Generic marginal/CS helpers are already
proved in P4Probe; no projection/cardinality/symmetry proof is needed. -/
def PatternComparisonBridgeTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J m : ℕ) (hj : m ≤ J)
    (block : P.BigGroup → Bool) (Q : ℕ) (h ξ θ ζ ε : ℝ)
    (c : ProbeChoice P m block),
    (∀ g, 0 < P.V g) → 0 ≤ ε → LocalComparison P m Q h ξ ζ ε →
    ∀ f g : P.BigLabels (J + F.ell) → ℂ,
    let ν : Pattern P J F.ell m := signedPattern hj block Q h ξ c
    let sigma := (-1 : ℂ) ^ (∑ j, (ν.changed j).card)
    let fA := bigCoordinateAverage P (J + F.ell) (patternSideCoordinates ν block false) f
    let gB := bigCoordinateAverage P (J + F.ell) (patternSideCoordinates ν block true) g
    ‖idealFullPair (((onePatternFamily F P J m ν).model 1 ζ).idealRaw θ) f g +
      sigma * idealFullPair (((rawFamily F P J m).model 1 ζ).idealRaw θ) fA gB‖ ≤
      ε * idealVectorNorm P (J + F.ell) f * idealVectorNorm P (J + F.ell) g

end
end Erdos821.P4Probe
