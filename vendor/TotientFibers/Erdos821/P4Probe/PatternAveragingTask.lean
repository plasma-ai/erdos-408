import Erdos821.P4Probe.PatternBridgeTasks

set_option autoImplicit false

namespace Erdos821.P4Probe
open Blueprint.Graph

/-- The signed one-pattern pairing ignores its unused source-false and
target-true changed slots. Use freshMass = idealMass / sharedLabelMass on
compatible pairs, then source/target average duality for the relative
kernel. This is the finite marginal identity in the comparison bridge;
it assumes no analytic comparison estimate. -/
def PatternAveragingTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J m : ℕ) (hj : m ≤ J)
    (block : P.BigGroup → Bool) (Q : ℕ) (h ξ θ ζ : ℝ)
    (c : ProbeChoice P m block),
    (∀ g, 0 < P.V g) → ∀ f g : P.BigLabels (J + F.ell) → ℂ,
    let ν : Pattern P J F.ell m := signedPattern hj block Q h ξ c
    let K := ((onePatternFamily F P J m ν).model 1 ζ).idealRaw θ
    let fA := bigCoordinateAverage P (J + F.ell) (patternSideCoordinates ν block false) f
    let gB := bigCoordinateAverage P (J + F.ell) (patternSideCoordinates ν block true) g
    idealFullPair K f g = idealFullPair K fA gB

end Erdos821.P4Probe
