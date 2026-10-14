import Erdos821.P5.PatternCosts

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L

/-- Every fixed logarithmic row cost is absorbed by the shared-draw
exclusion mass, uniformly over all endpoint positions of bounded size. -/
theorem shared_row_cost_factor_negligible (P : Geometry) (J m : ℕ) (r A : ℝ) (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, ∀ (G : Blueprint.Analytic.PrimeGroups)
      (ν : Pattern G.graph J P.ell m) (n n' D : ℕ),
      Admissible P x G → 0 < n → 0 < n' → 0 < D →
      (n : ℝ) ≤ x ^ r → (n' : ℝ) ≤ x ^ r → (D : ℝ) ≤ x ^ r →
      (sharedDampingLoss P G J ^ 2 + 1) * unsharedWeight P ν n * unsharedWeight P ν n' *
        sharedExclusionMass ν n n' D ≤ L x ^ (-A) := by
  obtain ⟨Cm, hm⟩ := eventual_unsharedWeight_bound P P.ell m
  let Cd : ℝ := (-2 * Real.log P.q) * (J + P.ell : ℕ) * P.C₀
  have hCd : 0 ≤ Cd := by
    have hlog : Real.log P.q < 0 := Real.log_neg P.damping.1 P.damping.2
    dsimp [Cd]
    exact mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) P.positive.2.1.le
  filter_upwards [hm, shared_exclusion_mass_fixed_cost P J P.ell m r A
    (2 * Cd + 2 * Cm) 2 hr (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hprob hL
  change 1 ≤ L x at hL
  have hLpos : 0 < L x := by linarith
  intro G ν n n' D hG hn hn' hD hnx hn'x hDx
  have hV (g : Fin G.size) : 0 ≤ G.graph.V g := by
    rw [graph_mass]
    exact (P.positive.2.2.1.trans_le (hG.2.2.1 g).1).le
  have hM := sharedExclusionMass_nonneg ν n n' D hV
  have hW := unsharedWeight_nonneg P ν n hV
  have hW' := unsharedWeight_nonneg P ν n' hV
  have hd : sharedDampingLoss P G J ≤ L x ^ Cd := sharedDampingLoss_le_log_power P G J x hL hG
  have hd0 : 0 ≤ sharedDampingLoss P G J := zpow_nonneg P.damping.1.le _
  have hpow : 1 ≤ L x ^ Cd := Real.one_le_rpow hL hCd
  have hcost : sharedDampingLoss P G J ^ 2 + 1 ≤ 2 * (L x ^ Cd) ^ 2 := by
    nlinarith [sq_nonneg (sharedDampingLoss P G J - L x ^ Cd)]
  calc
    _ ≤ (2 * (L x ^ Cd) ^ 2) * L x ^ Cm * L x ^ Cm * sharedExclusionMass ν n n' D := by
      gcongr
      · exact hx G J ν n hG
      · exact hx G J ν n' hG
    _ = 2 * L x ^ (2 * Cd + 2 * Cm) * sharedExclusionMass ν n n' D := by
      rw [← Real.rpow_mul_natCast hLpos.le Cd 2]
      simp only [Nat.cast_ofNat]
      rw [mul_assoc (2 : ℝ), ← Real.rpow_add hLpos,
        mul_assoc (2 : ℝ), ← Real.rpow_add hLpos]
      congr 2
      ring
    _ ≤ _ := hprob G ν n n' D hG hn hn' hD hnx hn'x hDx

/-- The full actual residual shared-row error has arbitrary log saving with
its linear pattern cost; only the separately controlled free-ban row remains. -/
theorem eventual_residual_shared_error_le (P : Geometry) (J m : ℕ) (r A : ℝ) (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, ∀ (G : Blueprint.Analytic.PrimeGroups) (Q : ℕ) (h ξ : ℝ)
      (B : Family P.graph G.graph J m) (v : Fin B.count) (k : ℤ) (ζ : ℝ)
      (z₀ unused : SharedDraw (B.pattern v)) (u : FreeDraw (B.pattern v)) (n n' : ℕ),
      Admissible P x G → B.Residual Q h ξ → 0 < n → 0 < n' →
      (n : ℝ) ≤ x ^ r → (n' : ℝ) ≤ x ^ r → (freeDrawProduct (B.pattern v) u : ℝ) ≤ x ^ r →
      ‖residualSharedAverage B v k ζ u unused n n' -
        strippedMarkedRow (B.pattern v) n n' (residualUnsharedCoefficient B v z₀ u)‖ ≤
      patternCost (B.pattern v) * L x ^ (-A) +
        ‖unsharedBanRow P (B.pattern v) u n n' (residualUnsharedCoefficient B v z₀ u)‖ := by
  filter_upwards [shared_row_cost_factor_negligible P J m r A hr] with x hx
  intro G Q h ξ B v k ζ z₀ unused u n n' hG hB hn hn' hnx hn'x hDx
  have hD : 0 < freeDrawProduct (B.pattern v) u :=
    Finset.prod_pos (fun i hi => (G.graph.prime i.1 _ (u i).property).pos)
  have hV (g : Fin G.size) : 0 < G.graph.V g := by
    rw [graph_mass]
    exact P.positive.2.2.1.trans_le (hG.2.2.1 g).1
  have hs := hx G (B.pattern v) n n' _ hG hn hn' hD hnx hn'x hDx
  have hp := mul_le_mul_of_nonneg_left hs (patternCost_nonneg (B.pattern v))
  calc
    _ ≤ _ := residual_shared_error_le_cost B hB v k ζ z₀ unused u n n' hn.ne' hn'.ne' hD.ne' hV
    _ = patternCost (B.pattern v) *
        ((sharedDampingLoss P G J ^ 2 + 1) * unsharedWeight P (B.pattern v) n *
          unsharedWeight P (B.pattern v) n' *
          sharedExclusionMass (B.pattern v) n n' (freeDrawProduct (B.pattern v) u)) +
        ‖unsharedBanRow P (B.pattern v) u n n' (residualUnsharedCoefficient B v z₀ u)‖ := by ring
    _ ≤ _ := add_le_add hp (le_refl _)

end Erdos821.P5Core
