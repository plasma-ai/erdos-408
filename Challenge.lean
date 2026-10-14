module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Erdős Problem 408: distribution of iterated totient heights

Let `φ_k` be the `k`-th iterate of Euler's totient function, and let `f(n)` be
the least `k ≥ 1` with `φ_k(n) = 1`. Erdős asked whether `f(n) / log n` has a
distribution function, and whether it is almost always constant.

**Claim.** There is a constant `α` with `1 / log 3 ≤ α ≤ 1 / log 2` such that

  `∑_{n ≤ x} (f(n) - α log n)² ≪ x (log x)² / (log log x)⁵`.

Hence `|f(n) - α log n| ≤ log n / log log n` outside a set with counting
function `O(x / (log log x)³ + √x)`. Then `f(n) / log n` tends to `α` on a set
of natural density one, and its distribution function is the point mass at
`α`. This answers the first two questions of Erdős Problem 408.

The proof follows Erdős, Granville, Pomerance and Spiro, with the prime factors
of `p - 1` controlled by OpenAI's *The Poisson-Dirichlet law for prime
predecessors* (PD) and *Weighted dilation graphs, smooth shifted primes and
totient fibers* (WD) (24 September 2026), and the zero-free half-plane
`re s > 7/8` of OpenAI's *The Quasi-Riemann Hypothesis* (30 September 2026).
Extensions of PD Theorems 3.1 and 6.1 are proved in the development behind
`Solution.lean`, using vendored Lean proofs of the half-plane (openai/math) and
of the WD results (Yao Xu's totient-fibers-lean4).

`f` is copied verbatim from `formal-conjectures`
(`FormalConjectures/ErdosProblems/408.lean`, commit `7db2ea3b91`), and
`erdos_408.parts.i` and `erdos_408.parts.ii` are its statements of the same
names verbatim, with its `Set.HasDensity` written as `HasDensity`, which
inlines it relative to all of `ℕ`.
Thomas F. Bloom catalogs the questions as
[Erdős Problem 408](https://www.erdosproblems.com/408).

The three theorems below have deliberate proof holes. `Solution.lean` supplies
their proofs, and Comparator checks them against these statements.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Erdos408

/--
`f n` is $f(n) = \min\{k \geq 1 : \phi_k(n) = 1\}$, where $\phi_1 = \phi$ is Euler's totient
function and $\phi_k(n) = \phi(\phi_{k-1}(n))$. As in the source, $k$ starts at $1$, so
$f(1) = 1$. Every iterate of $\phi$ at $0$ is $0$, so `sInf ∅ = 0` gives the junk value
$f(0) = 0$.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ Nat.totient^[k] n = 1}

/-- A set `S` of natural numbers has natural density `α` if the proportion of
`n < b` that lie in `S` tends to `α`. -/
def HasDensity (S : Set ℕ) (α : ℝ) : Prop :=
  Tendsto (fun b : ℕ => ((S ∩ Set.Iio b).ncard : ℝ) / (Set.Iio b).ncard) atTop (𝓝 α)

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
          C * (x / Real.log (Real.log x) ^ 3 + √x) := by
  sorry

/--
$f(n)/\log n$ has a distribution function: the point mass at the constant of
`normal_order_rate`.
-/
theorem erdos_408.parts.i :
    ∃ F : ℝ → ℝ, Monotone F ∧ Tendsto F atBot (𝓝 0) ∧ Tendsto F atTop (𝓝 1) ∧
      ∀ c : ℝ, ContinuousAt F c →
        HasDensity {n : ℕ | (f n : ℝ) / Real.log n ≤ c} (F c) := by
  sorry

/--
$f(n)/\log n$ is almost always constant: for every $\epsilon > 0$, the set of $n$
with $|f(n)/\log n - \alpha| < \epsilon$ has natural density $1$.
-/
theorem erdos_408.parts.ii :
    ∃ α : ℝ, ∀ ε > (0 : ℝ),
      HasDensity {n : ℕ | |(f n : ℝ) / Real.log n - α| < ε} 1 := by
  sorry

end Erdos408
