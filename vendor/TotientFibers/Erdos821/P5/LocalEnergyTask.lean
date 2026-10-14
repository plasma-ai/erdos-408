import Erdos821.Blueprint.Analytic

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic

def localAdditivePolynomial (s : Finset ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ s, a n * e (θ * n)

/-- §4 local Fourier to Mellin energy, source eq. local-mellin-energy.
Proof outline: choose a compact smooth bump K of integral one with
|Fourier(K)|≥1/2 on [-1,1]. Plancherel gives the local additive energy
bounded by H⁻² times the squared convolution norm. Only centers v in a
fixed positive multiple of [Y,2Y] contribute. On that range replace
K((n-v)/H) by K(v*log(n/v)/H). Taylor and Cauchy–Schwarz over O(H) integers
give squared normalized error O((H/Y)²)*sqNorm; never use this kernel near
v=0. Put h=H/Y and v=Y*exp(u). Insert a compact cutoff in u, Fourier-expand
its u-dependent amplitude, and integrate by parts twice in u to obtain
(1+|s|)⁻²*(1+|h*t|)⁻ʲ decay (use a larger decay index first).
Minkowski and Plancherel in u leave H⁻²*Y*h²=Y⁻¹, proving this contract.
No arithmetic or unproved blueprint interface is required. -/
def LocalMellinEnergyTask : Prop :=
  ∀ j : ℕ, 2 ≤ j → ∃ K : ℝ, 0 < K ∧
    ∀ (Y H : ℝ) (s : Finset ℕ) (a : ℕ → ℂ),
      10 ≤ Y → 1 ≤ H → H ≤ Y / 10 →
      (∀ n ∈ s, Y ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Y) →
      (∫ θ in (-1 / H)..(1 / H), ‖localAdditivePolynomial s a θ‖ ^ 2) ≤
        K / Y * (∫ t : ℝ, (1 + |H / Y * t|) ^ (-(j : ℤ)) * ‖dp s a t‖ ^ 2) +
        K * (H / Y) ^ 2 * sqNorm s a

end Erdos821.P5Core
