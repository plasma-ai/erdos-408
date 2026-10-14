import Erdos821.P5.SmoothComparisonIntegral

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem smooth_comparison_cell_integrable
    {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool)
    (h : ℝ) (j : ℤ × ℤ) (χA χB : CharacterIndex Q)
    (x Y a₁ a₂ lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi)
    (E H : Endpoint) (k : ℤ) (α : (Fin 1 → ℝ) → ℂ) (hα : Integrable α) :
    Integrable (fun ξ => α ξ * smoothComparisonCellCorrelation ν block h j χA χB
      x Y a₁ a₂ (mellinFrequency ξ) lo hi hlo hhi E H k) := by
  let c := fun u : FreeDraw ν => (freeDrawLaw ν u : ℂ) *
    star (charValue χA (comparisonFreeProduct ν block false u)) *
    star (charValue χB (comparisonFreeProduct ν block true u))
  let f := fun (u : FreeDraw ν) (n : ℕ) (ξ : Fin 1 → ℝ) =>
    smoothComparisonTerm G x Y (comparisonCellScale h j.1) (comparisonCellScale h j.2)
      a₁ a₂ (mellinFrequency ξ) lo hi hlo hhi E H
      (comparisonMarkedEndpoint ν block true h j.2 χB)
      (comparisonMarkedEndpoint ν block false h j.1 χA) n
      ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat
      (comparisonFreeProduct ν block false u) (comparisonFreeProduct ν block true u)
  have hiF (u : FreeDraw ν) (n : ℕ) : Integrable (fun ξ => α ξ * f u n ξ) :=
    smoothComparisonTerm_integrable G x Y _ _ a₁ a₂ lo hi hlo hhi E H _ _ n _ _ _ α hα
  have hsum := integrable_finsetSum
    (Finset.univ.filter (fun u : FreeDraw ν => comparisonCellPair ν block h u = j))
    (fun u hu => (integrable_finsetSum (comparisonCommonRoots lo hi Y)
      (fun n hn => hiF u n)).const_mul (c u))
  convert hsum using 1
  funext ξ
  unfold smoothComparisonCellCorrelation
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [c, f]
  ring

end Erdos821.P5Core
