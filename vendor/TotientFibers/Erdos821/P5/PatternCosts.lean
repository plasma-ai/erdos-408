import Erdos821.P5.ResidualRowIdentity

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L

def patternCost {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) : ℝ :=
  sSup (Set.range (fun z : G.BigLabels (J + ell) × G.BigLabels (J + ell) × G.BigAux J =>
    ‖ν.coefficient z.1 z.2.1 z.2.2‖))

theorem patternCost_nonneg {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) : 0 ≤ patternCost ν := by
  apply Real.sSup_nonneg
  rintro r ⟨z, rfl⟩
  exact norm_nonneg _

theorem coefficient_norm_le_patternCost {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (a b : G.BigLabels (J + ell)) (u : G.BigAux J) :
    ‖ν.coefficient a b u‖ ≤ patternCost ν := by
  exact le_csSup (Set.finite_range _).bddAbove ⟨(a, b, u), rfl⟩

theorem residualUnsharedCoefficient_norm_le {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (v : Fin B.count) (z₀ : SharedDraw (B.pattern v))
    (u : FreeDraw (B.pattern v)) (r s : UnsharedDraw (B.pattern v)) :
    ‖residualUnsharedCoefficient B v z₀ u r s‖ ≤ patternCost (B.pattern v) :=
  coefficient_norm_le_patternCost (B.pattern v) _ _ _

theorem bannedPatternCoefficient_norm_le {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (ν : Pattern G J F.ell m) (u : G.Aux J)
    (z : SharedDraw ν) (r s : UnsharedDraw ν) :
    ‖bannedPatternCoefficient A ν u z r s‖ ≤ patternCost ν := by
  unfold bannedPatternCoefficient
  split_ifs
  · exact coefficient_norm_le_patternCost ν _ _ _
  · simpa only [norm_zero] using patternCost_nonneg ν

theorem sum_patternCost_eq_patternMass {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (k : ℤ) (ζ : ℝ) :
    (∑ v : Fin B.count, patternCost (B.pattern v)) = (B.model k ζ).patternMass := rfl

/-- Family errors are paid linearly by their actual coefficient suprema;
no factor depending on the number of patterns is introduced. -/
theorem norm_sum_pattern_errors_le {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (k : ℤ) (ζ K : ℝ)
    (e : Fin B.count → ℂ) (he : ∀ v, ‖e v‖ ≤ K * patternCost (B.pattern v)) :
    ‖∑ v, e v‖ ≤ K * (B.model k ζ).patternMass := by
  calc
    _ ≤ ∑ v, ‖e v‖ := norm_sum_le _ _
    _ ≤ ∑ v, K * patternCost (B.pattern v) := Finset.sum_le_sum (fun v hv => he v)
    _ = _ := by rw [← Finset.mul_sum, sum_patternCost_eq_patternMass B k ζ]

theorem norm_sum_pattern_errors_log_le {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (k : ℤ) (ζ x A C₁ : ℝ) (hL : 0 < L x)
    (e : Fin B.count → ℂ) (he : ∀ v, ‖e v‖ ≤ L x ^ (-A) * patternCost (B.pattern v))
    (hB : (B.model k ζ).patternMass ≤ L x ^ C₁) :
    ‖∑ v, e v‖ ≤ L x ^ (-A + C₁) := by
  calc
    _ ≤ L x ^ (-A) * (B.model k ζ).patternMass := norm_sum_pattern_errors_le B k ζ _ e he
    _ ≤ L x ^ (-A) * L x ^ C₁ := mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hL.le _)
    _ = _ := (Real.rpow_add hL _ _).symm

/-- The shared-draw portion of the actual residual error keeps its linear
pattern cost. The free-ban row is left for its averaged collision estimate. -/
theorem residual_shared_error_le_cost {P : Geometry} {G : Blueprint.Analytic.PrimeGroups}
    {J m Q : ℕ} {h ξ : ℝ} (B : Family P.graph G.graph J m) (hB : B.Residual Q h ξ)
    (v : Fin B.count) (k : ℤ) (ζ : ℝ) (z₀ unused : SharedDraw (B.pattern v))
    (u : FreeDraw (B.pattern v)) (n n' : ℕ) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hD : freeDrawProduct (B.pattern v) u ≠ 0) (hV : ∀ g, 0 < G.graph.V g) :
    ‖residualSharedAverage B v k ζ u unused n n' -
        strippedMarkedRow (B.pattern v) n n' (residualUnsharedCoefficient B v z₀ u)‖ ≤
      patternCost (B.pattern v) * (sharedDampingLoss P G J ^ 2 + 1) *
        unsharedWeight P (B.pattern v) n * unsharedWeight P (B.pattern v) n' *
        sharedExclusionMass (B.pattern v) n n' (freeDrawProduct (B.pattern v) u) +
      ‖unsharedBanRow P (B.pattern v) u n n' (residualUnsharedCoefficient B v z₀ u)‖ := by
  have hM : 0 ≤ sharedExclusionMass (B.pattern v) n n' (freeDrawProduct (B.pattern v) u) :=
    sharedExclusionMass_nonneg (B.pattern v) n n' _ (fun g => (hV g).le)
  have hbad := physicalSharedExclusion_norm_le (B.model k ζ) (B.pattern v) n n'
    (freeDrawProduct (B.pattern v) u)
    (fun z => bannedPatternCoefficient (B.model k ζ) (B.pattern v)
      (assembleAux (B.pattern v) u unused) z) (patternCost (B.pattern v))
    (patternCost_nonneg _) (fun z r s => bannedPatternCoefficient_norm_le _ _ _ z r s)
    (fun g => (hV g).le)
  have hstrip := strippedMarkedRow_norm_le (B.pattern v) n n'
    (residualUnsharedCoefficient B v z₀ u) (patternCost (B.pattern v))
    (patternCost_nonneg _) (residualUnsharedCoefficient_norm_le B v z₀ u)
    (fun g => (hV g).le)
  calc
    _ ≤ _ := residual_shared_row_error_norm_le B hB v k ζ z₀ unused u n n' hn hn' hD hV
    _ ≤ (patternCost (B.pattern v) * sharedDampingLoss P G J ^ 2 *
          unsharedWeight P (B.pattern v) n * unsharedWeight P (B.pattern v) n' *
          sharedExclusionMass (B.pattern v) n n' (freeDrawProduct (B.pattern v) u)) +
        sharedExclusionMass (B.pattern v) n n' (freeDrawProduct (B.pattern v) u) *
          (patternCost (B.pattern v) * unsharedWeight P (B.pattern v) n *
            unsharedWeight P (B.pattern v) n') +
        ‖unsharedBanRow P (B.pattern v) u n n' (residualUnsharedCoefficient B v z₀ u)‖ := by
      exact add_le_add (add_le_add hbad (mul_le_mul_of_nonneg_left hstrip hM)) (le_refl _)
    _ = _ := by ring

end Erdos821.P5Core
