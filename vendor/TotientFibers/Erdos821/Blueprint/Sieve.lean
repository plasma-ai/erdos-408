import Erdos821.Blueprint.Classical

/-! P2: the block sieve, including its coefficient and level certificates. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos821.Blueprint

structure SieveData (α : Type) where
  objects : Finset α
  weight : α → ℝ
  primes : Finset ℕ
  bad : ℕ → α → Prop
  X : ℝ
  density : ℕ → ℝ
  nonneg : ∀ a ∈ objects, 0 ≤ weight a
  prime : ∀ p ∈ primes, p.Prime
  X_nonneg : 0 ≤ X

namespace SieveData
variable {α : Type} (S : SieveData α)
def monomial (d : ℕ) (a : α) : ℝ := if ∀ p ∈ d.primeFactors, S.bad p a then 1 else 0
def g (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors, S.density p
def remainder (d : ℕ) : ℝ :=
  (∑ a ∈ S.objects, S.weight a * S.monomial d a) - S.X * S.g d
def sifted : ℝ := ∑ a ∈ S.objects,
  if ∀ p ∈ S.primes, ¬ S.bad p a then S.weight a else 0
def product : ℝ := ∏ p ∈ S.primes, (1 - S.density p)
def products (D : ℝ) : Finset ℕ := (Finset.Icc 1 ⌊D⌋₊).filter
  (fun d => Squarefree d ∧ d.primeFactors ⊆ S.primes)
def remainderSum (D : ℝ) : ℝ := ∑ d ∈ S.products D, |S.remainder d|
def polynomial (D : ℝ) (lam : ℕ → ℝ) (a : α) : ℝ :=
  ∑ d ∈ S.products D, lam d * S.monomial d a
def densityBounds (z η C : ℝ) : Prop :=
  1 < z ∧ 0 < η ∧ (∀ p ∈ S.primes, (p : ℝ) ≤ z ∧
    0 ≤ S.density p ∧ S.density p ≤ 1 - η) ∧
  ∀ w : ℝ, 1 < w →
    (∑ p ∈ S.primes.filter (fun p : ℕ => w < (p : ℝ) ∧ (p : ℝ) ≤ w ^ (2 : ℕ)),
      S.density p) ≤ C
end SieveData

/-- Includes h=2 upper-only bound and coefficient-one upper/lower polynomials. -/
def BlockSieve : Prop :=
  ∀ η C : ℝ, 0 < η → 0 < C → ∃ K : ℝ, 0 < K ∧ ∃ h₀ : ℕ,
    ∀ (α : Type) (S : SieveData α) (z : ℝ), S.densityBounds z η C →
      (S.sifted ≤ K * S.X * S.product + K * S.remainderSum (z ^ (10 : ℕ))) ∧
      ∀ h : ℕ, h₀ ≤ h → Even h →
        |S.sifted - S.X * S.product| ≤
          K * Real.exp (-(h : ℝ)) * S.X * S.product +
            K * S.remainderSum (z ^ (4 * h + 2)) ∧
        ∃ u v : ℕ → ℝ,
          (∀ d, |u d| ≤ 1 ∧ |v d| ≤ 1 ∧ |u d - v d| ≤ 1) ∧
          (∀ d, d ∉ S.products (z ^ (4 * h + 2)) → u d = 0 ∧ v d = 0) ∧
          ∀ a ∈ S.objects,
            let D := z ^ (4 * h + 2)
            let I : ℝ := if ∀ p ∈ S.primes, ¬ S.bad p a then 1 else 0
            S.polynomial D v a ≤ I ∧ I ≤ S.polynomial D u a ∧
              0 ≤ S.polynomial D u a ∧
              S.polynomial D u a - I ≤ S.polynomial D (fun d => u d - v d) a

/-- The polynomial is chosen before its counting interval. -/
def RoughPolynomial : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → Even h →
    ∀ z : ℝ, 2 ≤ z → ∃ lam : ℕ → ℝ,
      (∀ d, |lam d| ≤ 1) ∧
      (∀ d, lam d ≠ 0 → Squarefree d ∧ (d : ℝ) ≤ z ^ (4 * h + 2) ∧
        d.primeFactors ⊆ primesUpTo z) ∧
      (∀ n : ℕ, 0 < n →
        (if Analytic.rough z n then 1 else 0 : ℝ) ≤ ∑ d ∈ n.divisors, lam d) ∧
      (∑ d ∈ Finset.Icc 1 ⌊z ^ (4 * h + 2)⌋₊, |lam d| / d) ≤
        K * Real.log (2 * z) ∧
      ∀ lo hi : ℝ, 1 ≤ lo → lo ≤ hi →
        (∑ n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊,
          ((∑ d ∈ n.divisors, lam d) - (if Analytic.rough z n then 1 else 0))) ≤
          K * ((hi - lo) * Real.exp (-(h : ℝ)) + z ^ (4 * h + 2))

structure SieveInputs : Prop where
  block : BlockSieve
  roughPolynomial : RoughPolynomial

/-- P2 boundary. -/
abbrev sieve_inputs_statement : Prop :=
  ∀ (_hc : ClassicalInputs),
    SieveInputs
end Erdos821.Blueprint
