import Erdos821.P5.IntegerComparisonSupport
import Erdos821.P5.ComparisonFourierMultiplier

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- Exact additive Fourier representation at one occupied comparison cell.
The endpoint polynomials are independent of the free draw; all its
dependence is in the actual comparison multiplier. -/
theorem smoothComparisonCellCorrelation_eq_fourier
    (hfourier : FourierArcTask) {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool)
    (h : ℝ) (hh : 0 < h) (hwidth : Real.exp (2 * h) ≤ 2)
    (j : ℤ × ℤ) (χA χB : CharacterIndex Q) (z : SharedDraw ν)
    (x Z a₁ a₂ v lo hi : ℝ) (E H : Endpoint) (k : ℤ)
    (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z)
    (hk : |(k : ℝ)| ≤ lo * Z / 8) :
    let Y := Z * comparisonJointScale h j
    let a := comparisonSmoothSource G x Y a₁ v lo hi hlo hhi E
      (comparisonMarkedEndpoint ν block true h j.2 χB)
    let b := comparisonSmoothTarget G x Y a₂ lo hi hlo hhi H
      (comparisonMarkedEndpoint ν block false h j.1 χA)
    smoothComparisonCellCorrelation ν block h j χA χB x Y a₁ a₂ v lo hi hlo hhi E H k =
      (Y : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..1,
        star (localAdditivePolynomial (comparisonCommonRoots lo hi Y) a θ) *
          localAdditivePolynomial (comparisonTargetRoots lo hi Y) b θ *
          comparisonMultiplier ν block h j
            (comparisonFourierTest χA (comparisonCellScale h j.1) a₁ a₂ v)
            (comparisonFourierTest χB (comparisonCellScale h j.2) a₁ a₂ v) k θ := by
  dsimp only
  let Y := Z * comparisonJointScale h j
  let a := comparisonSmoothSource G x Y a₁ v lo hi hlo hhi E
    (comparisonMarkedEndpoint ν block true h j.2 χB)
  let b := comparisonSmoothTarget G x Y a₂ lo hi hlo hhi H
    (comparisonMarkedEndpoint ν block false h j.1 χA)
  let U := Finset.univ.filter (fun u : FreeDraw ν => comparisonCellPair ν block h u = j)
  let w := fun u : FreeDraw ν => (freeDrawLaw ν u : ℂ) *
    comparisonFourierTest χA (comparisonCellScale h j.1) a₁ a₂ v
      (comparisonFreeProduct ν block false u) *
    comparisonFourierTest χB (comparisonCellScale h j.2) a₁ a₂ v
      (comparisonFreeProduct ν block true u)
  let d := fun u : FreeDraw ν => k * (freeDrawProduct ν u : ℤ)
  have hY : 0 < Y := mul_pos hZ (comparisonJointScale_pos h j)
  have hpos (u : FreeDraw ν) (hu : u ∈ U) (n : ℕ)
      (hn : n ∈ comparisonCommonRoots lo hi Y) : 0 ≤ (n : ℤ) + d u := by
    exact (comparison_common_root_positivity ν block h hh hwidth j u z
      (Finset.mem_filter.mp hu).2 lo hi Z k hlo hZ hk n hn).2.le
  have hb (n : ℕ) (hn : n ∉ comparisonTargetRoots lo hi Y) : b n = 0 :=
    comparisonSmoothTarget_zero_outside G x Y a₂ lo hi hlo hhi hY H _ n hn
  have hphase (u : FreeDraw ν) (θ : ℝ) :
      e (-θ * (d u : ℝ)) = e (-(k : ℝ) * θ *
        comparisonFreeProduct ν block false u * comparisonFreeProduct ν block true u) := by
    dsimp only [d]
    rw [freeDrawProduct_eq_comparisonProducts ν block u z]
    push_cast
    congr 1
    ring
  have hm (θ : ℝ) : (∑ u ∈ U, w u * e (-θ * (d u : ℝ))) =
      comparisonMultiplier ν block h j
        (comparisonFourierTest χA (comparisonCellScale h j.1) a₁ a₂ v)
        (comparisonFourierTest χB (comparisonCellScale h j.2) a₁ a₂ v) k θ := by
    unfold comparisonMultiplier
    apply Finset.sum_congr rfl
    intro u hu
    rw [hphase]
  have hex : smoothComparisonCellCorrelation ν block h j χA χB x Y a₁ a₂ v lo hi
      hlo hhi E H k = (Y : ℂ)⁻¹ * ∑ u ∈ U, w u *
        ∑ n ∈ comparisonCommonRoots lo hi Y, star (a n) * b ((n : ℤ) + d u).toNat := by
    unfold smoothComparisonCellCorrelation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    simp only [smoothComparisonTerm]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [w, a, b, d, comparisonFourierTest]
    ring
  change _ = (Y : ℂ)⁻¹ * _
  rw [hex, finite_shift_law_eq_fourier_integral hfourier U w d
    (comparisonCommonRoots lo hi Y) (comparisonTargetRoots lo hi Y) a b hpos hb]
  simp_rw [hm]
  rfl

end Erdos821.P5Core
