import Erdos821.Blueprint.Graph
import Erdos821.Blueprint.MemoryHistory
import Erdos821.Blueprint.Sieve

/-! P3 boundary on the literal finite row kernels of Graph.lean. -/
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
namespace Erdos821.Blueprint.Graph

namespace Model
variable {F : FixedData} {P : PrimeGroups} {J m : ℕ} (A : Model F P J m)
def stepBound : ℕ := A.k.natAbs * (P.allPrimes.sup id) ^ (J * P.count)
def neighbors (n : ℤ) : Finset A.State :=
  (Finset.Icc (n - A.stepBound) (n + A.stepBound)).product Finset.univ
def averagedMoment (R : ℕ) (X : ℝ) : ℝ :=
  let I := Finset.Ico ⌈X⌉ ⌈2 * X⌉
  (∑ n ∈ I, A.rootMoment R n) / I.card

def normOn (s : Finset A.State) (f : A.State → ℂ) : ℝ :=
  Real.sqrt (∑ z ∈ s, A.stateMass z * ‖f z‖ ^ 2)
def pairing (X : ℝ) (t : Finset A.State) (f : ℤ → ℂ) (g : A.State → ℂ) : ℂ :=
  ∑ n ∈ Finset.Ico ⌈X⌉ ⌈2 * X⌉, ∑ a : A.Labels, ∑ z ∈ t,
    (A.stateMass (n, a) : ℂ) * star (f n) * A.physicalKernel false (n, a) z * g z
end Model

def AbsolutePhysicalBounds : Prop :=
  ∀ F : FixedData, ∀ m : ℕ, ∀ C₁ : ℝ, ∃ Cabs : ℝ,
    ∀ J : ℕ, ∀ᶠ x : ℝ in atTop, ∀ (P : PrimeGroups) (A : Model F P J m),
      P.Admissible F x → A.patternMass ≤ L x ^ C₁ →
      (∀ z, (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z z'‖) ≤ L x ^ Cabs) ∧
      (∀ z, (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z' z‖) ≤ L x ^ Cabs)

/-- E_id precedes m,C₁,J. The threshold for x follows every fixed choice. -/
def TransferenceEstimate : Prop :=
  ∀ F : FixedData, ∀ E : ℝ, 0 < E → ∃ Eid : ℝ, 0 < Eid ∧
    ∀ (m : ℕ) (C₁ : ℝ), ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      ∀ γ C₂ : ℝ, 0 < γ → 0 < C₂ →
        ∀ᶠ x : ℝ in atTop, ∀ (P : PrimeGroups) (A : Model F P J m),
          P.Admissible F x → A.patternMass ≤ L x ^ C₁ →
          A.k ≠ 0 → |(A.k : ℝ)| ≤ L x ^ C₂ →
          (∀ θ : ℝ, NormBound (P.idealMass (M := J + F.ell))
            (A.idealKernel θ) (L x ^ (-Eid))) →
          ∀ X : ℝ, x ^ γ ≤ X → X ≤ x ^ γ⁻¹ →
            A.averagedMoment ⌈L x ^ (0.52 : ℝ)⌉₊ X ≤
              L x ^ (-E * (2 * (⌈L x ^ (0.52 : ℝ)⌉₊ : ℝ)))

/-- The only mark-independent endpoint is f. No equal root norms are assumed. -/
def TransferencePairing : Prop :=
  ∀ F : FixedData, ∀ E : ℝ, 0 < E → ∃ Eid : ℝ, 0 < Eid ∧
    ∀ (m : ℕ) (C₁ : ℝ), ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      ∀ γ C₂ C₃ Cf : ℝ, 0 < γ → 0 < C₂ →
        ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
          ∀ (P : PrimeGroups) (A : Model F P J m) (X : ℝ)
            (t : Finset A.State) (f : ℤ → ℂ) (g : A.State → ℂ),
            P.Admissible F x → A.patternMass ≤ L x ^ C₁ →
            A.k ≠ 0 → |(A.k : ℝ)| ≤ L x ^ C₂ →
            (∀ θ : ℝ, NormBound (P.idealMass (M := J + F.ell))
              (A.idealKernel θ) (L x ^ (-Eid))) →
            x ^ γ ≤ X → X ≤ x ^ γ⁻¹ →
            (∀ n ∈ Finset.Ico ⌈X⌉ ⌈2 * X⌉, ‖f n‖ ≤ Real.exp (Cf * Real.sqrt (L x))) →
            A.normOn ((Finset.Ico ⌈X⌉ ⌈2 * X⌉).product Finset.univ)
              (fun z => f z.1) ≤ Real.sqrt X * L x ^ C₃ →
            A.normOn t g ≤ Real.sqrt X * L x ^ C₃ →
            ‖A.pairing X t f g‖ ≤ K * X * L x ^ (-E + 2 * C₃)

end Erdos821.Blueprint.Graph
namespace Erdos821.Blueprint

structure TransferenceInputs : Prop where
  absolute : Graph.AbsolutePhysicalBounds
  moment : Graph.TransferenceEstimate
  pairing : Graph.TransferencePairing

/-- P3 boundary: CRT, exact memory identity, truncation, rare/clean edges and rank restoration. -/
abbrev transference_inputs_statement : Prop :=
  ∀ (_hc : ClassicalInputs),
    TransferenceInputs
end Erdos821.Blueprint
