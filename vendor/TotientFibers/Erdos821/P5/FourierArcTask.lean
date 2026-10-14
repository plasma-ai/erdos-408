import Erdos821.P5.Basic

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic

def integerAdditivePolynomial (s : Finset ℤ) (a : ℤ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ s, a n * e (θ * n)

/-- Pure finite Fourier identities and the abstract major/minor arc bound.
No arithmetic, P5 energy, free-product law or other unfinished task is an
input. First prove integral_0^1 e(theta*n)=if n=0 then 1 else 0 from
intervalIntegral.integral_exp_mul_complex and exp_int_mul_two_pi_mul_I,
or from AddCircle Fourier orthogonality. Expand the finite sums to prove
the two identities. For the last bound split [0,1] into the finite union
of the arcs and its complement. On the complement use the pointwise
minor bound and integral Cauchy--Schwarz. On the union use norm M<=1,
nonnegative finite-union domination, and Cauchy--Schwarz on each arc;
the restricted G square integral is at most its global B bound.
Arcs crossing 0 or 1 are allowed because only their intersection with
[0,1] is used. Delta=0 and empty finite supports/arc sets are included.
Export exactly this proposition and audit all three components. -/
def FourierArcTask : Prop :=
  (∀ (s t : Finset ℤ) (a b : ℤ → ℂ) (d : ℤ),
    (∑ n ∈ s, ∑ m ∈ t, if m = n + d then star (a n) * b m else 0) =
      ∫ θ in (0 : ℝ)..1,
        star (integerAdditivePolynomial s a θ) * integerAdditivePolynomial t b θ *
          e (-θ * d)) ∧
  (∀ (s : Finset ℤ) (a : ℤ → ℂ),
    (∫ θ in (0 : ℝ)..1, ‖integerAdditivePolynomial s a θ‖ ^ 2) =
      ∑ n ∈ s, ‖a n‖ ^ 2) ∧
  (∀ (F G M : ℝ → ℂ) (centers : Finset ℝ) (Δ A B E ε : ℝ),
    Continuous F → Continuous G → Continuous M →
    0 ≤ Δ → 0 ≤ A → 0 ≤ B → 0 ≤ E → 0 ≤ ε →
    (∫ θ in (0 : ℝ)..1, ‖F θ‖ ^ 2) ≤ A →
    (∫ θ in (0 : ℝ)..1, ‖G θ‖ ^ 2) ≤ B →
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖M θ‖ ≤ 1) →
    (∀ θ ∈ Set.Icc (0 : ℝ) 1,
      (∀ c ∈ centers, Δ < |θ - c|) → ‖M θ‖ ≤ ε) →
    (∀ c ∈ centers, (∫ θ in (c - Δ)..(c + Δ), ‖F θ‖ ^ 2) ≤ E) →
    ‖∫ θ in (0 : ℝ)..1, star (F θ) * G θ * M θ‖ ≤
      ε * Real.sqrt A * Real.sqrt B +
        (centers.card : ℝ) * Real.sqrt E * Real.sqrt B)

end Erdos821.P5Core
