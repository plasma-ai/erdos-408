import Erdos408.Basic
import Erdos408.Hypotheses
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Definitions for the extraction of the rectangle statistic

The objects of the quantitative rewrite of PD Section 7, with the parameters at
scale `x`: `L = log x`, `T = log L`, `s = log T`, margin `ε = c T⁻²⁰`.

* The slot statistic `f_𝔟(n) = ∑_{Q ∣ n} 𝔟(Q)` and its harmonic mean
  `C_𝔟 = ∑ 𝔟(Q) / Q`, over the slot tuples of `RectangleInput`.
* Presieve parameters: depth `h = 2 ⌈C_h s⌉`, level exponent
  `γ = (ε / 4) / (4h + 3)` (so `z = x^γ`), and composite cutoff
  `J_c = ⌈C_j s⌉`.
* The clustered inert polynomial
  `P(n) = ∏_{c < K} (1 - ∏_{i < N/K} (1 - c_w w_{c,i}(n)))`, where `w_{c,i}`
  is the single-band weight `q^{ω - 1} ω / V` of the band with exponent
  `0.11 + c · 0.08/K + i · 2/T`.
* The candidate groups (PD 7.3): small groups `[e^y, e^{2y})` for
  `y = 2^i L^{0.28}` up to `L^{0.35}`, and big groups from `L^{0.40}` up to
  `L^{0.45}`.
* The damped proxy with cutoff `Y = exp(L / T²⁵)` and `t = 1/j`:
  `g_j(n) = [n̄ Y-rough] t^{Ω_P(n)}`,
  `D_j = ∏_{p ≤ Y} (1 - 1/p) ∏_{p ∈ P} (1 - t/p)⁻¹`, the unstripped proxy
  `[n > x^γ] g_j(n) / (D_j log n)`, and the stripped proxy
  `[n̄ > x^γ] g_j(n) / (D_j log n̄)`. Here `n̄` removes every candidate prime.
* The composite sum `Comp_j` over `j`-tuples of primes above `z`, and the
  proxy sum `Prox_j` with every prime replaced by the stripped proxy. Each
  carries the endpoint `P · (f_𝔟 - C_𝔟)` and the cutoff `Φ((∏ - 1) / x)`.

See `blueprint/rectangle_input.md` §4 and *The normal order of the number of
iterations of Euler's function* (Plasma AI, 2026), §6.
-/

namespace Erdos408

open Real

noncomputable section

/-- `T = log log x`. -/
def logLog (x : ℝ) : ℝ :=
  Real.log (Real.log x)

/-- `s = log log log x`. -/
def logLogLog (x : ℝ) : ℝ :=
  Real.log (logLog x)

/-! ### The slot statistic -/

/-- The weighted slot count `f_𝔟(n) = ∑_{Q ∣ n} 𝔟(Q)` over the tuples of
distinct slot primes, with a coefficient ignoring the last slot. -/
def slotCount (x : ℝ) {k : ℕ} (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) (n : ℕ) : ℝ :=
  ∑ Q ∈ slotTuples x u v with ∏ i, Q i ∣ n, B (Fin.init Q)

/-- The harmonic model `C_𝔟 = ∑ 𝔟(Q) / Q` of the slot count. -/
def slotMean (x : ℝ) {k : ℕ} (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ Q ∈ slotTuples x u v, B (Fin.init Q) / ∏ i, (Q i : ℝ)

/-! ### Presieve parameters -/

/-- The sieve depth `h = 2 ⌈C_h s⌉`, an even integer. -/
def sieveDepth (Ch x : ℝ) : ℕ :=
  2 * ⌈Ch * logLogLog x⌉₊

/-- The presieve exponent `γ = (ε / 4) / (4h + 3)` with `ε = c T⁻²⁰`, so that
the sieve level `z^{4h+2}` is below `x^{ε/4}`. -/
def presieveExponent (c Ch x : ℝ) : ℝ :=
  c / logLog x ^ 20 / 4 / (4 * sieveDepth Ch x + 3)

/-- The composite cutoff `J_c = ⌈C_j s⌉`. -/
def compositeCutoff (Cj x : ℝ) : ℕ :=
  ⌈Cj * logLogLog x⌉₊

/-! ### The clustered inert polynomial -/

/-- The exponent of the `i`-th band of cluster `c`:
`0.11 + c · 0.08 / K + i · 2 / T`. -/
def inertExponent (K : ℕ) (x : ℝ) (c i : ℕ) : ℝ :=
  11 / 100 + c * (8 / 100 / K) + i * (2 / logLog x)

/-- The number of bands per cluster, `⌈C_N s / K⌉`. -/
def inertPerCluster (K : ℕ) (CN x : ℝ) : ℕ :=
  ⌈CN * logLogLog x / K⌉₊

/-- The single-band weight `q^{ω(n) - 1} ω(n) / V` of the band with exponent
`a`. -/
def bandWeight (q x a : ℝ) (n : ℕ) : ℝ :=
  markedWeight (Finset.univ : Finset Unit) q (fun _ => band x a) n

/-- The clustered inert polynomial
`P(n) = ∏_{c < K} (1 - ∏_{i} (1 - c_w w_{c,i}(n)))`. -/
def inertPoly (q cw : ℝ) (K : ℕ) (CN x : ℝ) (n : ℕ) : ℝ :=
  ∏ c ∈ Finset.range K,
    (1 - ∏ i ∈ Finset.range (inertPerCluster K CN x),
      (1 - cw * bandWeight q x (inertExponent K x c i) n))

/-- The endpoint `P(n) (f_𝔟(n) - C_𝔟)`. -/
def endpoint (q cw : ℝ) (K : ℕ) (CN x : ℝ) {k : ℕ} (u v : Fin (k + 1) → ℝ)
    (B : (Fin k → ℕ) → ℝ) (n : ℕ) : ℝ :=
  inertPoly q cw K CN x n * (slotCount x u v B n - slotMean x u v B)

/-! ### Candidate groups -/

/-- The primes `p` with `e^y ≤ p < e^{2y}`. -/
def dyadicGroup (y : ℝ) : Finset ℕ :=
  primesIcc (Real.exp y) (⌈Real.exp (2 * y)⌉₊ - 1 : ℕ)

/-- The groups `[e^y, e^{2y})` for `y = 2^i L^a` with `2y ≤ L^b`. -/
def doublingGroups (x a b : ℝ) : Finset (Finset ℕ) :=
  ((Finset.range (⌊Real.logb 2 (Real.log x ^ (b - a))⌋₊)).filter
      fun i => 2 ^ (i + 1) * Real.log x ^ a ≤ Real.log x ^ b).image
    fun i => dyadicGroup (2 ^ i * Real.log x ^ a)

/-- The small candidate groups, from `L^{0.28}` to `L^{0.35}`. -/
def smallGroups (x : ℝ) : Finset (Finset ℕ) :=
  doublingGroups x (28 / 100) (35 / 100)

/-- The big candidate groups, from `L^{0.40}` to `L^{0.45}`. -/
def bigGroups (x : ℝ) : Finset (Finset ℕ) :=
  doublingGroups x (40 / 100) (45 / 100)

/-- All candidate primes. -/
def candidatePrimes (x : ℝ) : Finset ℕ :=
  (smallGroups x ∪ bigGroups x).biUnion id

/-! ### The damped proxy -/

/-- The proxy cutoff `Y = exp(L / T²⁵)`. -/
def proxyCutoff (x : ℝ) : ℝ :=
  Real.exp (Real.log x / logLog x ^ 25)

/-- `Ω_P(n)`: the number of candidate prime factors of `n`, with
multiplicity. -/
def candidateOmega (x : ℝ) (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors with p ∈ candidatePrimes x, n.factorization p

/-- `n̄`: `n` with every candidate prime removed. -/
def candidateStrip (x : ℝ) (n : ℕ) : ℕ :=
  stripPrimes (candidatePrimes x) n

/-- The damped weight `g_j(n) = [n̄ is Y-rough] j^{-Ω_P(n)}`. -/
def dampedWeight (x : ℝ) (j : ℕ) (n : ℕ) : ℝ :=
  if ∀ p ∈ (candidateStrip x n).primeFactors, proxyCutoff x < p then
    ((j : ℝ)⁻¹) ^ candidateOmega x n
  else 0

/-- The density `D_j = ∏_{p ≤ Y} (1 - 1/p) ∏_{p ∈ P} (1 - 1/(j p))⁻¹` of the
damped weight. -/
def dampedDensity (x : ℝ) (j : ℕ) : ℝ :=
  (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) *
    ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹

/-- The unstripped proxy `[n > x^γ] g_j(n) / (D_j log n)`. -/
def unstrippedProxy (x γ : ℝ) (j : ℕ) (n : ℕ) : ℝ :=
  if x ^ γ < n then dampedWeight x j n / (dampedDensity x j * Real.log n) else 0

/-- The stripped proxy `[n̄ > x^γ] g_j(n) / (D_j log n̄)`. -/
def strippedProxy (x γ : ℝ) (j : ℕ) (n : ℕ) : ℝ :=
  if x ^ γ < candidateStrip x n then
    dampedWeight x j n / (dampedDensity x j * Real.log (candidateStrip x n))
  else 0

/-! ### The composite and proxy sums -/

/-- The composite sum `Comp_j`: over ordered `j`-tuples of primes
`x^γ < p_i ≤ κ x + 1`, the weight `Φ((∏ p - 1) / x) P (f_𝔟 - C_𝔟)` at
`∏ p - 1`. -/
def compositeSum (q cw : ℝ) (K : ℕ) (CN x γ κ : ℝ) (j : ℕ) (Φ : ℝ → ℝ) {k : ℕ}
    (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ p ∈ Fintype.piFinset fun _ : Fin j => primesIcc (x ^ γ) (κ * x + 1),
    if (∀ i, x ^ γ < p i) then
      Φ (((∏ i, p i : ℕ) - 1 : ℝ) / x) * endpoint q cw K CN x u v B ((∏ i, p i) - 1)
    else 0

/-- The proxy sum `Prox_j`: as `Comp_j`, over all `j`-tuples of integers in
`[1, κ x + 1]`, weighted by `∏ a_j(m_i)` with the stripped proxy. -/
def proxySum (q cw : ℝ) (K : ℕ) (CN x γ κ : ℝ) (j : ℕ) (Φ : ℝ → ℝ) {k : ℕ}
    (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ m ∈ Fintype.piFinset fun _ : Fin j => Finset.Icc 1 ⌊κ * x + 1⌋₊,
    Φ (((∏ i, m i : ℕ) - 1 : ℝ) / x) * endpoint q cw K CN x u v B ((∏ i, m i) - 1) *
      ∏ i, strippedProxy x γ j (m i)

/-! ### The cutoff class -/

/-- `Φ` is a nonnegative smooth cutoff supported in `[κ⁻¹, κ]` whose `r`-th
derivative is at most `M_r T^{C_Φ r}`. -/
def IsCutoff (κ CΦ : ℝ) (M : ℕ → ℝ) (x : ℝ) (Φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧ (∀ y, 0 ≤ Φ y) ∧
    (∀ y, Φ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) ∧
    ∀ (r : ℕ) (y : ℝ), |iteratedDeriv r Φ y| ≤ M r * logLog x ^ (CΦ * r)

/-- The slots `(x^{u_i}, x^{v_i}]` have lower log coordinates at least
`c / T²⁰` and upper log coordinates summing to at most `1 - c / T²⁰`. -/
def AdmissibleSlots (c x : ℝ) {k : ℕ} (u v : Fin (k + 1) → ℝ) : Prop :=
  (∀ i, c / logLog x ^ 20 ≤ u i) ∧ ∑ i, v i ≤ 1 - c / logLog x ^ 20

end

end Erdos408
