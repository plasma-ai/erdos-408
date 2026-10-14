import Erdos821.P5.StrippedRowAlgebra
import Erdos821.P5.PhysicalSharedExclusion

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic Blueprint.Graph

def residualSharedAverage {P : Geometry} {G : Blueprint.Analytic.PrimeGroups} {J m : ℕ}
    (B : Family P.graph G.graph J m) (v : Fin B.count) (k : ℤ) (ζ : ℝ)
    (u : FreeDraw (B.pattern v)) (unused : SharedDraw (B.pattern v)) (n n' : ℕ) : ℂ :=
  ∑ z : SharedDraw (B.pattern v), (sharedDrawLaw (B.pattern v) z : ℂ) *
    physicalSharedRow (B.model k ζ) (B.pattern v) z n n'
      (bannedPatternCoefficient (B.model k ζ) (B.pattern v)
        (assembleAux (B.pattern v) u unused) z)

theorem residual_good_row_eq {P : Geometry} {G : Blueprint.Analytic.PrimeGroups}
    {J m Q : ℕ} {h ξ : ℝ} (B : Family P.graph G.graph J m) (hB : B.Residual Q h ξ)
    (v : Fin B.count) (k : ℤ) (ζ : ℝ) (z z₀ unused : SharedDraw (B.pattern v))
    (u : FreeDraw (B.pattern v)) (n n' : ℕ) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hD : freeDrawProduct (B.pattern v) u ≠ 0)
    (hz : GoodSharedDraw (B.pattern v) n n' (freeDrawProduct (B.pattern v) u) z) :
    physicalSharedRow (B.model k ζ) (B.pattern v) z n n'
      (bannedPatternCoefficient (B.model k ζ) (B.pattern v)
        (assembleAux (B.pattern v) u unused) z) =
      strippedMarkedRow (B.pattern v) n n' (residualUnsharedCoefficient B v z₀ u) -
        unsharedBanRow P (B.pattern v) u n n' (residualUnsharedCoefficient B v z₀ u) := by
  rw [physicalSharedRow_good_eq_stripped (B.model k ζ) (B.pattern v) z n n' _ hn hn' hD hz]
  have hc : bannedPatternCoefficient (B.model k ζ) (B.pattern v)
      (assembleAux (B.pattern v) u unused) z =
      (fun r s => if UnsharedBan (B.pattern v) r s u
        then residualUnsharedCoefficient B v z₀ u r s else 0) := by
    funext r s
    exact banned_residual_coefficient_good B hB v k ζ z z₀ unused u n n' hn hn' hD hz r s
  rw [hc]
  exact eq_sub_iff_add_eq.mpr (strippedMarkedRow_ban_split (B.pattern v) u n n'
    (residualUnsharedCoefficient B v z₀ u))

/-- Exact decomposition of the actual residual shared average. The two
exclusions are the already-proved physicalSharedExclusion and unsharedBanRow;
the missing mass of good draws remains explicit. -/
theorem residual_shared_average_eq {P : Geometry} {G : Blueprint.Analytic.PrimeGroups}
    {J m Q : ℕ} {h ξ : ℝ} (B : Family P.graph G.graph J m) (hB : B.Residual Q h ξ)
    (v : Fin B.count) (k : ℤ) (ζ : ℝ) (z₀ unused : SharedDraw (B.pattern v))
    (u : FreeDraw (B.pattern v)) (n n' : ℕ) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hD : freeDrawProduct (B.pattern v) u ≠ 0) (hV : ∀ g, G.graph.V g ≠ 0) :
    residualSharedAverage B v k ζ u unused n n' =
      physicalSharedExclusion (B.model k ζ) (B.pattern v) n n' (freeDrawProduct (B.pattern v) u)
        (fun z => bannedPatternCoefficient (B.model k ζ) (B.pattern v)
          (assembleAux (B.pattern v) u unused) z) +
      ((1 - sharedExclusionMass (B.pattern v) n n' (freeDrawProduct (B.pattern v) u) : ℝ) : ℂ) *
        (strippedMarkedRow (B.pattern v) n n' (residualUnsharedCoefficient B v z₀ u) -
          unsharedBanRow P (B.pattern v) u n n' (residualUnsharedCoefficient B v z₀ u)) := by
  let R := strippedMarkedRow (B.pattern v) n n' (residualUnsharedCoefficient B v z₀ u) -
    unsharedBanRow P (B.pattern v) u n n' (residualUnsharedCoefficient B v z₀ u)
  calc
    _ = physicalSharedExclusion (B.model k ζ) (B.pattern v) n n'
        (freeDrawProduct (B.pattern v) u)
        (fun z => bannedPatternCoefficient (B.model k ζ) (B.pattern v)
          (assembleAux (B.pattern v) u unused) z) +
        ∑ z : SharedDraw (B.pattern v),
          if GoodSharedDraw (B.pattern v) n n' (freeDrawProduct (B.pattern v) u) z
          then (sharedDrawLaw (B.pattern v) z : ℂ) * R else 0 := by
      unfold residualSharedAverage physicalSharedExclusion
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hg : GoodSharedDraw (B.pattern v) n n' (freeDrawProduct (B.pattern v) u) z
      · simp only [hg, not_true_eq_false, if_false, if_true, zero_add]
        congr 1
        exact residual_good_row_eq B hB v k ζ z z₀ unused u n n' hn hn' hD hg
      · simp only [hg, not_false_eq_true, if_true, if_false, add_zero]
    _ = _ := by rw [shared_good_average_eq (B.pattern v) n n' _ hV R]

theorem residual_shared_row_error_norm_le {P : Geometry} {G : Blueprint.Analytic.PrimeGroups}
    {J m Q : ℕ} {h ξ : ℝ} (B : Family P.graph G.graph J m) (hB : B.Residual Q h ξ)
    (v : Fin B.count) (k : ℤ) (ζ : ℝ) (z₀ unused : SharedDraw (B.pattern v))
    (u : FreeDraw (B.pattern v)) (n n' : ℕ) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hD : freeDrawProduct (B.pattern v) u ≠ 0) (hV : ∀ g, 0 < G.graph.V g) :
    ‖residualSharedAverage B v k ζ u unused n n' -
        strippedMarkedRow (B.pattern v) n n' (residualUnsharedCoefficient B v z₀ u)‖ ≤
      ‖physicalSharedExclusion (B.model k ζ) (B.pattern v) n n' (freeDrawProduct (B.pattern v) u)
        (fun z => bannedPatternCoefficient (B.model k ζ) (B.pattern v)
          (assembleAux (B.pattern v) u unused) z)‖ +
      sharedExclusionMass (B.pattern v) n n' (freeDrawProduct (B.pattern v) u) *
        ‖strippedMarkedRow (B.pattern v) n n' (residualUnsharedCoefficient B v z₀ u)‖ +
      ‖unsharedBanRow P (B.pattern v) u n n' (residualUnsharedCoefficient B v z₀ u)‖ := by
  let M := sharedExclusionMass (B.pattern v) n n' (freeDrawProduct (B.pattern v) u)
  let S := strippedMarkedRow (B.pattern v) n n' (residualUnsharedCoefficient B v z₀ u)
  let U := unsharedBanRow P (B.pattern v) u n n' (residualUnsharedCoefficient B v z₀ u)
  let E := physicalSharedExclusion (B.model k ζ) (B.pattern v) n n' (freeDrawProduct (B.pattern v) u)
    (fun z => bannedPatternCoefficient (B.model k ζ) (B.pattern v)
      (assembleAux (B.pattern v) u unused) z)
  have hM0 : 0 ≤ M := sharedExclusionMass_nonneg (B.pattern v) n n' _ (fun g => (hV g).le)
  have hM1 : M ≤ 1 := sharedExclusionMass_le_one (B.pattern v) n n' _ hV
  have hid : residualSharedAverage B v k ζ u unused n n' - S =
      E - (M : ℂ) * S - ((1 - M : ℝ) : ℂ) * U := by
    rw [residual_shared_average_eq B hB v k ζ z₀ unused u n n' hn hn' hD (fun g => (hV g).ne')]
    change E + ((1 - M : ℝ) : ℂ) * (S - U) - S = _
    push_cast
    ring
  change ‖residualSharedAverage B v k ζ u unused n n' - S‖ ≤ ‖E‖ + M * ‖S‖ + ‖U‖
  rw [hid]
  calc
    _ ≤ ‖E - (M : ℂ) * S‖ + ‖((1 - M : ℝ) : ℂ) * U‖ := norm_sub_le _ _
    _ ≤ (‖E‖ + ‖(M : ℂ) * S‖) + ‖((1 - M : ℝ) : ℂ) * U‖ := by
      exact add_le_add (norm_sub_le E ((M : ℂ) * S)) (le_refl _)
    _ = ‖E‖ + M * ‖S‖ + (1 - M) * ‖U‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hM0, Real.norm_of_nonneg (sub_nonneg.mpr hM1)]
    _ ≤ _ := by nlinarith [norm_nonneg U]

end Erdos821.P5Core
