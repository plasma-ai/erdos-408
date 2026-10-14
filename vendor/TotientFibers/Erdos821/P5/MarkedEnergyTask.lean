import Erdos821.P5.LocalEnergyTask

noncomputable section
open scoped BigOperators Classical ContDiff
open Filter MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- An invariant endpoint with arbitrary bounded big-label mark weights,
a smooth size cutoff and a fixed Mellin twist. -/
def markedEnergyCoefficient (P : Geometry) (G : PrimeGroups) (x Y v : ℝ)
    (E : Endpoint) (t : Fin G.size → ℕ) (b : Tuple G t → ℂ)
    (Ψ : ℝ → ℂ) (n : ℕ) : ℂ :=
  Ψ ((n : ℝ) / Y) * mellin n v * endpoint G x E n * weightedMarks G P.q t b n

/-- The actual endpoint major-arc energy, source local-energy-target.
This is independent of comparison free draws and their cell costs.
Remove one designated small mark. Outside square multiples the ordered
list bijection gives the exact removal identity; endpoint_square_sum_multiples
and mark_sup make the square-multiple error negligible by Parseval.
Recombine the group part with the residual factor into w=m*p_s*p*r.
Expand the rational phase over gcd classes and all characters of each
quotient (principal and imprimitive included). Apply the accepted
LocalMellinEnergyTask to positive dyads; separate the size cutoff with
the accepted MellinCutoffTask. Fixed divisor moments bound each collapsed
subproduct. Split times into ordinary/exceptional and low/high ranges:
exceptional_times bounds occupied intervals, sparse_residual bounds the
residual maxima, long_rough_polynomial handles high times, and one final
discrepancy exponent handles the low times. Mean squares bound the tail.
The 0.01 scale slack is fixed and is supplied by the lead's comparison
scale asymptotics. No other unfinished P5 task is needed.
Export precisely this proposition; report a defect rather than changing it. -/
def MarkedEndpointEnergyTask : Prop :=
  ∀ (P : Geometry) (R : ℕ) (C A τ η lo hi : ℝ) (bounds : ℕ → ℝ),
    0 < C → 0 < A → 0 < lo → lo < hi → (∀ j, 0 ≤ bounds j) →
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ (G : PrimeGroups) (E : Endpoint) (Y H v : ℝ)
          (t : Fin G.size → ℕ) (b : Tuple G t → ℂ) (Ψ : ℝ → ℂ)
          (r : ℕ) (u : ℤ),
          Admissible P x G → EndpointBound x C τ η E →
          x ^ (0.99 : ℝ) ≤ Y → Y ≤ x ^ (1.01 : ℝ) →
          Real.exp (L x ^ P.c / 2) ≤ H → H ≤ x ^ (0.01 : ℝ) →
          |v| ≤ L x ^ C →
          (∀ g, t g ≤ R) → (∃ g ∈ G.small, 1 ≤ t g) →
          (∀ z, ‖b z‖ ≤ 1) →
          (∀ z z' : Tuple G t, (∀ g, g ∈ G.big → z g = z' g) → b z = b z') →
          CutoffBound x C lo hi Ψ bounds →
          1 ≤ r → (r : ℝ) ≤ L x ^ C → discrepancy x B E.alpha →
          (∫ β in (-1 / H)..(1 / H),
            ‖localAdditivePolynomial (Finset.Icc ⌈lo * Y⌉₊ ⌊hi * Y⌋₊)
              (markedEnergyCoefficient P G x Y v E t b Ψ) ((u : ℝ) / r + β)‖ ^ 2) ≤
            K * Y * L x ^ (-A)

end Erdos821.P5Core
