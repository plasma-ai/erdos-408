import Erdos408.Extraction.Unsmooth
import Erdos408.FinalAssembly
import Erdos408.Graph
import Erdos408.OneSided
import Erdos408.TwoSided

/-!
# Proof of Erdős Problem 408: distribution of iterated totient heights

Comparator checks the three theorems in this module against the Mathlib-only
statements in `Challenge.lean`.
-/

open Filter
open scoped Topology

namespace Erdos408

/-- The rectangle statistic, from the one-sided Type II estimate and from the
two-sided correlation, which the graph transference input gives. -/
theorem rectangleInput : RectangleInput :=
  rectangleInput_of_hypotheses oneSidedTypeII
    (twoSidedCorrelation_of_graphTransference graphTransference)

/-- `f n` has normal order `α log n` for a constant `1 / log 3 ≤ α ≤ 1 / log 2`,
with variance `O(x (log x)² / (log log x)⁵)` up to `x`, and
`|f n - α log n| ≤ log n / log log n` outside a set with counting function
`O(x / (log log x)³ + √x)`. -/
theorem normal_order_rate :
    ∃ α : ℝ, 1 / Real.log 3 ≤ α ∧ α ≤ 1 / Real.log 2 ∧ ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((f n : ℝ) - α * Real.log n) ^ 2 ≤
          C * x * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 ∧
        (((Finset.Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
            Real.log n / Real.log (Real.log n) < |(f n : ℝ) - α * Real.log n|).card : ℝ) ≤
          C * (x / Real.log (Real.log x) ^ 3 + √x) :=
  normal_order_rate_proved rectangleInput

/--
$f(n)/\log n$ has a distribution function: the point mass at the constant of
`normal_order_rate`.
-/
theorem erdos_408.parts.i :
    ∃ F : ℝ → ℝ, Monotone F ∧ Tendsto F atBot (𝓝 0) ∧ Tendsto F atTop (𝓝 1) ∧
      ∀ c : ℝ, ContinuousAt F c →
        HasDensity {n : ℕ | (f n : ℝ) / Real.log n ≤ c} (F c) :=
  parts_i_proved rectangleInput

/--
$f(n)/\log n$ is almost always constant: for every $\epsilon > 0$, the set of $n$
with $|f(n)/\log n - \alpha| < \epsilon$ has natural density $1$.
-/
theorem erdos_408.parts.ii :
    ∃ α : ℝ, ∀ ε > (0 : ℝ),
      HasDensity {n : ℕ | |(f n : ℝ) / Real.log n - α| < ε} 1 :=
  parts_ii_proved rectangleInput

end Erdos408
