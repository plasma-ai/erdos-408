import Erdos821.P5.Basic

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- §4 pointwise rough-divisor count for the physical endpoint sup bound.
A rough divisor chooses exponents only at prime factors of N exceeding y.
Its count is the product of (e_p+1) over those primes, at most 2^(sum e_p).
Their prime-power product is at most N, while each prime is greater than y,
so sum e_p ≤ log(N)/log(y). All logs and divisions are real.
This is an elementary finite-factorization task and needs no P1 interface. -/
def RoughDivisorCountTask : Prop :=
  ∀ (y : ℝ) (N : ℕ), 1 < y → 0 < N →
    (((N.divisors.filter (rough y)).card : ℕ) : ℝ) ≤
      Real.exp (Real.log 2 * Real.log (N : ℝ) / Real.log y)

end Erdos821.P5Core
