import Erdos821.Blueprint.Classical

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- §4 sparse-gram-kernel: the full containing interval, never an arbitrary subset.
For |z|<1 use the number of terms. For 1≤|z|≤cU apply the first derivative
test to z log(v)/(2π), whose derivative stays below 1/2 in absolute value.
For cU<|z|≤Y apply the second derivative test, obtaining
O(sqrt(|z|)+U/sqrt(|z|))=O(sqrt(Y)). Handle both signs by conjugation.
The conversion between natural-index dp and integer-index e must retain
the ceiling/floor endpoints. Only the two P1 derivative fields are inputs. -/
def SparseGramKernelTask : Prop :=
  Blueprint.DerivativeTests → ∃ K : ℝ, 0 < K ∧ ∀ (Y U z : ℝ),
    1 ≤ U → U ≤ Y → |z| ≤ Y →
    ‖dp (Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊) (fun _ => 1) z‖ ≤
      K * (U / (1 + |z|) + Real.sqrt Y)

/-- §4 log-phase-sum on arbitrary subintervals. For |u|≤cN use the first
derivative test. Otherwise select 2≤k≤ceil(4/τ)+3 with
N^(k−2+1/10)≤|u|≤N^(k−1/10). For k=2 use the second derivative test.
For k>2 use k−2 van der Corput differences with integer shifts at most
floor(N^(1/(20k))). Their second derivatives are iterated integrals of the
kth log derivative and have constant sign and size between
c_k N^(−2+1/10) and C_k N^(−1/20). The second derivative bound is then
O(N^(1−1/40)). Zero-extend inside a containing interval of length O(N);
every correlation support is an interval. Iterate B_j²≤C(H⁻¹+B_(j+1)).
The final δ may be any smaller fixed positive exponent. All constants
must be uniform in q,a; a<q makes qy+a comparable to qN. -/
def LogPhaseSumTask : Prop :=
  Blueprint.DerivativeTests → ∀ τ : ℝ, 0 < τ →
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ (N lo hi u : ℝ) (q a : ℕ),
      x ^ (τ / 2) ≤ N → N ≤ lo → lo ≤ hi → hi ≤ 2 * N →
      1 ≤ q → a < q → 1 ≤ |u| → |u| ≤ x ^ (2 : ℕ) →
      ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
        mellin (q * (y : ℝ) + a) u‖ ≤ K * N * (|u|⁻¹ + N ^ (-δ))

end Erdos821.P5Core
