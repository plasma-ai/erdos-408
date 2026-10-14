import Erdos821.P4Probe.Family
import Erdos821.P4Probe.ProjectionTasks

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

def analyticGroups (P : PrimeGroups) : Blueprint.Analytic.PrimeGroups where
  size := P.count
  primes := P.primes
  small := P.smallGroups
  prime := P.prime
  disjoint := P.disjoint

/-- Uniform finite comparison hypothesis. No limiting or admissibility
assumption enters the finite cancellation lemma. -/
def LocalComparison (P : PrimeGroups) (m Q : ℕ) (h ξ ζ ε : ℝ) : Prop :=
  let G := analyticGroups P
  ∀ a b, Blueprint.Analytic.bigSlots G a m → Blueprint.Analytic.bigSlots G b m →
    ∀ (α : ℝ) (f : Blueprint.Analytic.Tuple G b → ℂ)
      (g : Blueprint.Analytic.Tuple G a → ℂ),
      ‖Blueprint.Analytic.comparisonError G a b Q h ξ α ζ f g‖ ≤
        ε * Blueprint.Analytic.tupleNorm G b f * Blueprint.Analytic.tupleNorm G a g

/-- Pure finite all-pattern cancellation, conditional on the independent
symmetric projection task. Use asymmetric freed coordinates, condition on
all shared labels, and apply LocalComparison with α=θ*C. Sum the two full
exceptions before norms; their costs are sqrt(theta^block-size), with no
subset count. At most 3^(m*#big-groups) triples pay the comparison error.
The target is the literal Graph idealKernel, including both permutation
averages; all unselected auxiliary labels integrate to one. -/
def FiniteProbeCancellationTask : Prop :=
  SymmetricFullComponentTask →
  ∀ (F : FixedData) (P : PrimeGroups) (J m : ℕ) (hj : m ≤ J)
    (block : P.BigGroup → Bool) (Q : ℕ) (h ξ θ ζ ε : ℝ),
    (∀ g, 0 < P.V g) → 1 ≤ m →
    (m + F.ell) * (m + F.ell - 1) ≤ J + F.ell →
    0 ≤ ε → LocalComparison P m Q h ξ ζ ε →
    let beta := 2 * (F.ell : ℝ) ^ F.ell / (m : ℝ) ^ F.ell
    let b₁ := (Finset.univ.filter (fun g : P.BigGroup => block g = false)).card
    let b₂ := (Finset.univ.filter (fun g : P.BigGroup => block g = true)).card
    NormBound (P.idealMass (M := J + F.ell))
      (((probeFamily F P J m hj block Q h ξ).model 1 ζ).idealKernel θ)
      (Real.sqrt (beta ^ b₁) + Real.sqrt (beta ^ b₂) +
        (3 : ℝ) ^ (m * Fintype.card P.BigGroup) * ε)

end
end Erdos821.P4Probe
