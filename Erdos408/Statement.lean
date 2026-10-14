module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Statement of Erdős Problem 408: distribution of iterated totient heights

`f` and `HasDensity` repeat the definitions of `Challenge.lean` for the proof
development; Comparator requires them to agree exactly. `RectangleInput` is the
intermediate statistic: `Erdos408.Extraction.Unsmooth` derives it from the
graph-paper results of `Erdos408.Hypotheses`, and `Erdos408.FinalAssembly`
derives the normal order from it.
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

/-- The primes `p` with `x < p ≤ 2 x`. -/
noncomputable def dyadicPrimes (x : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter Nat.Prime

/-- The tuples `Q` of distinct primes with `x ^ u i < Q i ≤ x ^ v i` for every
slot `i`. -/
noncomputable def slotTuples (x : ℝ) {k : ℕ} (u v : Fin k → ℝ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun i =>
    (Finset.Iic ⌊x ^ v i⌋₊).filter fun q : ℕ => q.Prime ∧ x ^ u i < q).filter
    Function.Injective

/-- The rectangle statistic: for `k + 1 ≤ 3` prime slots whose lower log
coordinates are at least `c / T²⁰` and whose upper log coordinates sum to at
most `1 - c / T²⁰`, with `T = log log x`, the average over primes
`x < p ≤ 2 x` of the tuples dividing `p - 1`, weighted by any coefficient of
modulus at most one in all slots but the last, agrees with its harmonic model
up to `C / T³⁰⁰`. -/
def RectangleInput : Prop :=
  ∃ c > (0 : ℝ), ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ k ≤ 2, ∀ u v : Fin (k + 1) → ℝ,
    (∀ i, c / Real.log (Real.log x) ^ 20 ≤ u i) →
    ∑ i, v i ≤ 1 - c / Real.log (Real.log x) ^ 20 →
    ∀ B : (Fin k → ℕ) → ℝ, (∀ Q, |B Q| ≤ 1) →
      |(∑ p ∈ dyadicPrimes x, ∑ Q ∈ slotTuples x u v with ∏ i, Q i ∣ p - 1,
            B (Fin.init Q)) / (dyadicPrimes x).card -
          ∑ Q ∈ slotTuples x u v, B (Fin.init Q) / ∏ i, (Q i : ℝ)| ≤
        C / Real.log (Real.log x) ^ 300

end Erdos408
