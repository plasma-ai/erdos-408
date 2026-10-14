import Mathlib

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.P4Probe

noncomputable section

abbrev ProbeSample {s : ℕ} (α : Fin s → Type) (M : ℕ) :=
  ∀ g, Fin M → α g

def sampleWeight {s M : ℕ} {α : Fin s → Type}
    (w : ∀ g, α g → ℝ) (x : ProbeSample α M) : ℝ :=
  ∏ g, ∏ i, w g (x g i)

def sampleSqNorm {s M : ℕ} {α : Fin s → Type} [∀ g, Fintype (α g)]
    (w : ∀ g, α g → ℝ) (f : ProbeSample α M → ℂ) : ℝ :=
  ∑ x, sampleWeight w x * ‖f x‖ ^ 2

def replaceCoords {s M : ℕ} {α : Fin s → Type}
    (I : Finset (Fin s × Fin M)) (x y : ProbeSample α M) : ProbeSample α M :=
  fun g i => if (g, i) ∈ I then y g i else x g i

def averageCoords {s M : ℕ} {α : Fin s → Type} [∀ g, Fintype (α g)]
    (w : ∀ g, α g → ℝ) (I : Finset (Fin s × Fin M))
    (f : ProbeSample α M → ℂ) (x : ProbeSample α M) : ℂ :=
  ∑ y, (sampleWeight w y : ℂ) * f (replaceCoords I x y)

/-- Projection onto components involving every coordinate in I, after
averaging the disjoint tail. This is ∏(1-E_i) E_tail, expressed finitely. -/
def fullProbeComponent {s M : ℕ} {α : Fin s → Type} [∀ g, Fintype (α g)]
    (w : ∀ g, α g → ℝ) (tail I : Finset (Fin s × Fin M))
    (f : ProbeSample α M → ℂ) (x : ProbeSample α M) : ℂ :=
  ∑ U ∈ I.powerset, (-1 : ℂ) ^ U.card * averageCoords w (tail ∪ U) f x

/-- Pure finite weighted symmetry estimate used at eq:ideal-full-component.
All labels in a row have the same probability law. The source vector may
couple every row; resolve joint cardinality tuples rather than assuming it
is a tensor product. Genuine scalar Hoeffding bounds are in S34/Hoeffding. -/
def SymmetricFullComponentTask : Prop :=
  ∀ (s J ell m : ℕ) (α : Fin s → Type) [∀ g, Fintype (α g)]
    (w : ∀ g, α g → ℝ) (block : Finset (Fin s))
    (f : ProbeSample α (J + ell) → ℂ),
    (∀ g x, 0 ≤ w g x) → (∀ g, ∑ x, w g x = 1) →
    1 ≤ m → 1 ≤ ell → m ≤ J →
    (m + ell) * (m + ell - 1) ≤ J + ell →
    (∀ (π : Fin s → Equiv.Perm (Fin (J + ell))) x,
      f (fun g i => x g (π g i)) = f x) →
    let tail := Finset.univ.filter (fun z : Fin s × Fin (J + ell) => J ≤ z.2.val)
    let I := Finset.univ.filter
      (fun z : Fin s × Fin (J + ell) => z.1 ∈ block ∧ z.2.val < m)
    sampleSqNorm w (fullProbeComponent w tail I f) ≤
      (2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ block.card * sampleSqNorm w f

end
end Erdos821.P4Probe
