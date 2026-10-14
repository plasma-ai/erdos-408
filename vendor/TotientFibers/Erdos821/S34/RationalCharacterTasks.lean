import Erdos821.Blueprint.Analytic

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
open Blueprint.Analytic

/-- §3 rational Fourier expansion, on the group of reduced residue classes.
Suggested proof: coefficient = normalized character transform of the unit
phase; reconstruct by DirichletCharacter.sum_char_inv_mul_char_eq, and use
OAI.LargePrimeGaps.character_transform_bound for the L1 estimate. -/
def RationalFourierTask : Prop :=
  ∀ (r : ℕ) (u : ℤ), 1 ≤ r →
    ∃ c : DirichletCharacter ℂ r → ℂ,
      (∑ ψ, ‖c ψ‖) ≤ Real.sqrt (r.totient : ℝ) ∧
      ∀ n : ℕ, Nat.Coprime n r →
        e ((u : ℝ) * n / r) = ∑ ψ, c ψ * ψ (n : ZMod r)

/-- Every character mod r is represented by its primitive inducing character
in the packet of conductors at most Q, at all integers coprime to r. -/
def PrimitiveInductionTask : Prop :=
  ∀ (Q r : ℕ), 1 ≤ r → r ≤ Q → ∀ ψ : DirichletCharacter ℂ r,
    ∃ χ ∈ primitiveCharacters Q, ∀ n : ℕ, Nat.Coprime n r →
      charValue χ n = ψ (n : ZMod r)

end Erdos821.S34Core
