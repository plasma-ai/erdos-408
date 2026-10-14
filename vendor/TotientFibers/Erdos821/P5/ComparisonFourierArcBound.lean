import Erdos821.P5.SmoothComparisonFourier
import Erdos821.P5.RationalArcCenters

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem natural_fourier_arc_bound (hfourier : FourierArcTask)
    (s t : Finset ℕ) (a b : ℕ → ℂ) (M : ℝ → ℂ) (centers : Finset ℝ)
    (Δ A B E ε : ℝ) (hM : Continuous M) (hΔ : 0 ≤ Δ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hε : 0 ≤ ε)
    (ha : sqNorm s a ≤ A) (hb : sqNorm t b ≤ B)
    (hunit : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖M θ‖ ≤ 1)
    (hminor : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      (∀ c ∈ centers, Δ < |θ - c|) → ‖M θ‖ ≤ ε)
    (hmajor : ∀ c ∈ centers,
      (∫ θ in (c - Δ)..(c + Δ), ‖localAdditivePolynomial s a θ‖ ^ 2) ≤ E) :
    ‖∫ θ in (0 : ℝ)..1,
      star (localAdditivePolynomial s a θ) * localAdditivePolynomial t b θ * M θ‖ ≤
      ε * Real.sqrt A * Real.sqrt B + (centers.card : ℝ) * Real.sqrt E * Real.sqrt B := by
  apply hfourier.2.2 (localAdditivePolynomial s a) (localAdditivePolynomial t b)
    M centers Δ A B E ε (localAdditivePolynomial_continuous s a)
    (localAdditivePolynomial_continuous t b) hM hΔ hA hB hE hε
  · rw [natural_fourier_parseval hfourier]
    exact ha
  · rw [natural_fourier_parseval hfourier]
    exact hb
  · exact hunit
  · exact hminor
  · exact hmajor

/-- Applies the finite arc estimate to the actual smoothed cell law.
The only arithmetic estimates still needed are its minor bound, source
arc energy and the two square sums. -/
theorem smoothComparisonCellCorrelation_arc_bound
    (hfourier : FourierArcTask) {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool)
    (h : ℝ) (hh : 0 < h) (hwidth : Real.exp (2 * h) ≤ 2)
    (j : ℤ × ℤ) (χA χB : CharacterIndex Q) (z : SharedDraw ν)
    (x Z a₁ a₂ v lo hi : ℝ) (E H : Endpoint) (k : ℤ)
    (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z)
    (hk : |(k : ℝ)| ≤ lo * Z / 8) (hG : Admissible P x G)
    (centers : Finset ℝ) (Δ A B Earc ε : ℝ)
    (hΔ : 0 ≤ Δ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hEarc : 0 ≤ Earc) (hε : 0 ≤ ε) :
    let Y := Z * comparisonJointScale h j
    let a := comparisonSmoothSource G x Y a₁ v lo hi hlo hhi E
      (comparisonMarkedEndpoint ν block true h j.2 χB)
    let b := comparisonSmoothTarget G x Y a₂ lo hi hlo hhi H
      (comparisonMarkedEndpoint ν block false h j.1 χA)
    let M := comparisonMultiplier ν block h j
      (comparisonFourierTest χA (comparisonCellScale h j.1) a₁ a₂ v)
      (comparisonFourierTest χB (comparisonCellScale h j.2) a₁ a₂ v) k
    sqNorm (comparisonCommonRoots lo hi Y) a ≤ A →
    sqNorm (comparisonTargetRoots lo hi Y) b ≤ B →
    (∀ θ ∈ Set.Icc (0 : ℝ) 1,
      (∀ c ∈ centers, Δ < |θ - c|) → ‖M θ‖ ≤ ε) →
    (∀ c ∈ centers, (∫ θ in (c - Δ)..(c + Δ),
      ‖localAdditivePolynomial (comparisonCommonRoots lo hi Y) a θ‖ ^ 2) ≤ Earc) →
    ‖smoothComparisonCellCorrelation ν block h j χA χB x Y a₁ a₂ v lo hi hlo hhi E H k‖ ≤
      Y⁻¹ * (ε * Real.sqrt A * Real.sqrt B +
        (centers.card : ℝ) * Real.sqrt Earc * Real.sqrt B) := by
  dsimp only
  intro ha hb hminor hmajor
  have hY : 0 < Z * comparisonJointScale h j := mul_pos hZ (comparisonJointScale_pos h j)
  have hV (g : Fin G.size) : 0 < G.graph.V g := by
    rw [graph_mass]
    exact P.positive.2.2.1.trans_le (hG.2.2.1 g).1
  have hbound := natural_fourier_arc_bound hfourier
    (comparisonCommonRoots lo hi (Z * comparisonJointScale h j))
    (comparisonTargetRoots lo hi (Z * comparisonJointScale h j)) _ _
    (comparisonMultiplier ν block h j
      (comparisonFourierTest χA (comparisonCellScale h j.1) a₁ a₂ v)
      (comparisonFourierTest χB (comparisonCellScale h j.2) a₁ a₂ v) k)
    centers Δ A B Earc ε (comparisonMultiplier_continuous _ _ _ _ _ _ _)
    hΔ hA hB hEarc hε ha hb
    (fun θ hθ => comparisonMultiplier_norm_le_one _ _ _ _ _ _ _ θ hV
      (fun n => ⟨comparisonFourierTest_norm_le _ _ _ _ _ n,
        comparisonFourierTest_norm_le _ _ _ _ _ n⟩)) hminor hmajor
  rw [smoothComparisonCellCorrelation_eq_fourier hfourier ν block h hh hwidth j χA χB z
    x Z a₁ a₂ v lo hi E H k hlo hhi hZ hk]
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  exact mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hY.le)

end Erdos821.P5Core
