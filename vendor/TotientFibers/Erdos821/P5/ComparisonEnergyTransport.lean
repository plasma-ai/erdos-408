import Erdos821.P5.IntegerComparisonSupport

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem comparisonCommonRoots_pos (lo hi Y : ℝ) (hlo : 0 < lo) (hY : 0 < Y)
    (n : ℕ) (hn : n ∈ comparisonCommonRoots lo hi Y) : 0 < n := by
  have hnlo : lo / 2 * Y ≤ (n : ℝ) :=
    Nat.le_of_ceil_le (Finset.mem_Icc.mp hn).1
  have hp : (0 : ℝ) < n := (by positivity : 0 < lo / 2 * Y).trans_le hnlo
  exact_mod_cast hp

/-- The source Fourier polynomial differs from the exact energy polynomial
by a unit scalar, independent of the additive frequency. -/
theorem comparison_source_polynomial_eq_markedEnergy
    {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool) (side : Bool)
    (h : ℝ) (j : ℤ) (χ : CharacterIndex Q) (x Y a v lo hi : ℝ)
    (hlo : 0 < lo) (hhi : lo < hi) (hY : 0 < Y) (E : Endpoint) (θ : ℝ) :
    localAdditivePolynomial (comparisonCommonRoots lo hi Y)
      (comparisonSmoothSource G x Y a v lo hi hlo hhi E
        (comparisonMarkedEndpoint ν block side h j χ)) θ =
      mellin Y v * localAdditivePolynomial (comparisonCommonRoots lo hi Y)
        (markedEnergyCoefficient P G x Y (-a - v) E ν.t
          (comparisonEnergyMark ν block side h j χ)
          (comparisonHarmonicSizeCutoff lo hi hlo hhi)) θ := by
  unfold localAdditivePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [comparisonSmoothSource_eq_markedEnergy ν block side h j χ x Y a v lo hi
    hlo hhi hY E n (comparisonCommonRoots_pos lo hi Y hlo hY n hn)]
  ring

theorem comparison_source_polynomial_norm_eq_markedEnergy
    {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool) (side : Bool)
    (h : ℝ) (j : ℤ) (χ : CharacterIndex Q) (x Y a v lo hi : ℝ)
    (hlo : 0 < lo) (hhi : lo < hi) (hY : 0 < Y) (E : Endpoint) (θ : ℝ) :
    ‖localAdditivePolynomial (comparisonCommonRoots lo hi Y)
      (comparisonSmoothSource G x Y a v lo hi hlo hhi E
        (comparisonMarkedEndpoint ν block side h j χ)) θ‖ =
      ‖localAdditivePolynomial (comparisonCommonRoots lo hi Y)
        (markedEnergyCoefficient P G x Y (-a - v) E ν.t
          (comparisonEnergyMark ν block side h j χ)
          (comparisonHarmonicSizeCutoff lo hi hlo hhi)) θ‖ := by
  rw [comparison_source_polynomial_eq_markedEnergy ν block side h j χ x Y a v lo hi
    hlo hhi hY E θ, norm_mul, norm_mellin, one_mul]

theorem interval_energy_translate (F : ℝ → ℂ) (c Δ : ℝ) :
    (∫ θ in (c - Δ)..(c + Δ), ‖F θ‖ ^ 2) =
      ∫ β in (-Δ)..Δ, ‖F (c + β)‖ ^ 2 := by
  simpa only [sub_eq_add_neg] using
    (intervalIntegral.integral_comp_add_left (fun θ => ‖F θ‖ ^ 2)
      (a := -Δ) (b := Δ) c).symm

theorem comparison_source_arc_energy_eq_markedEnergy
    {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool) (side : Bool)
    (h : ℝ) (j : ℤ) (χ : CharacterIndex Q) (x Y a v lo hi c Δ : ℝ)
    (hlo : 0 < lo) (hhi : lo < hi) (hY : 0 < Y) (E : Endpoint) :
    (∫ θ in (c - Δ)..(c + Δ),
      ‖localAdditivePolynomial (comparisonCommonRoots lo hi Y)
        (comparisonSmoothSource G x Y a v lo hi hlo hhi E
          (comparisonMarkedEndpoint ν block side h j χ)) θ‖ ^ 2) =
      ∫ β in (-Δ)..Δ,
        ‖localAdditivePolynomial (comparisonCommonRoots lo hi Y)
          (markedEnergyCoefficient P G x Y (-a - v) E ν.t
            (comparisonEnergyMark ν block side h j χ)
            (comparisonHarmonicSizeCutoff lo hi hlo hhi)) (c + β)‖ ^ 2 := by
  simp_rw [comparison_source_polynomial_norm_eq_markedEnergy ν block side h j χ
    x Y a v lo hi hlo hhi hY E]
  exact interval_energy_translate _ c Δ

end Erdos821.P5Core
