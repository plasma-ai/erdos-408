import Erdos821.P5.SharedRowBound
import Erdos821.P5.SharedRemoval

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

def physicalSharedExclusion {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (A : Blueprint.Graph.Model P.graph G.graph J m)
    (ν : Blueprint.Graph.Pattern G.graph J P.ell m) (n n' D : ℕ)
    (c : SharedDraw ν → UnsharedDraw ν → UnsharedDraw ν → ℂ) : ℂ :=
  ∑ z : SharedDraw ν, if ¬GoodSharedDraw ν n n' D z
    then (sharedDrawLaw ν z : ℂ) * physicalSharedRow A ν z n n' (c z) else 0

/-- The bad-draw probability controls the actual weighted physical row even
when its coefficients depend on the shared draw. -/
theorem physicalSharedExclusion_norm_le {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (A : Blueprint.Graph.Model P.graph G.graph J m)
    (ν : Blueprint.Graph.Pattern G.graph J P.ell m) (n n' D : ℕ)
    (c : SharedDraw ν → UnsharedDraw ν → UnsharedDraw ν → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ z r s, ‖c z r s‖ ≤ B) (hV : ∀ g, 0 ≤ G.graph.V g) :
    ‖physicalSharedExclusion A ν n n' D c‖ ≤
      B * sharedDampingLoss P G J ^ 2 * unsharedWeight P ν n * unsharedWeight P ν n' *
        sharedExclusionMass ν n n' D := by
  let K := B * sharedDampingLoss P G J ^ 2 * unsharedWeight P ν n * unsharedWeight P ν n'
  have hb (z : SharedDraw ν) : ‖physicalSharedRow A ν z n n' (c z)‖ ≤ K :=
    physicalSharedRow_norm_le A ν z n n' (c z) B hB (hc z) hV
  unfold physicalSharedExclusion
  calc
    _ ≤ ∑ z : SharedDraw ν, if ¬GoodSharedDraw ν n n' D z
        then sharedDrawLaw ν z * K else 0 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro z hz
      by_cases h : GoodSharedDraw ν n n' D z
      · simp only [h, not_true_eq_false, if_false, norm_zero, le_refl]
      · simp only [h, not_false_eq_true, if_true, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (sharedDrawLaw_nonneg ν z hV)]
        exact mul_le_mul_of_nonneg_left (hb z) (sharedDrawLaw_nonneg ν z hV)
    _ = K * sharedExclusionMass ν n n' D := by
      rw [sharedExclusionMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      have he : (¬GoodSharedDraw ν n n' D z) ↔ ∃ i : SharedIndex ν,
          (z i).val ∈ sharedForbidden ν n n' D i (fun j => z j.val) := by
        simp only [GoodSharedDraw, not_forall, not_not]
      simp only [he, mul_ite, mul_zero]
      split_ifs <;> ring

theorem eventual_physicalSharedExclusion_bound (P : Geometry) (J m : ℕ)
    (r C A : ℝ) (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (M : Blueprint.Graph.Model P.graph G.graph J m)
        (ν : Blueprint.Graph.Pattern G.graph J P.ell m) (n n' D : ℕ)
        (c : SharedDraw ν → UnsharedDraw ν → UnsharedDraw ν → ℂ),
        Admissible P x G → 0 < n → 0 < n' → 0 < D →
        (n : ℝ) ≤ x ^ r → (n' : ℝ) ≤ x ^ r → (D : ℝ) ≤ x ^ r →
        (∀ z a b, ‖c z a b‖ ≤ L x ^ C) →
        ‖physicalSharedExclusion M ν n n' D c‖ ≤ L x ^ (-A) := by
  obtain ⟨Cm, hm⟩ := eventual_unsharedWeight_bound P P.ell m
  let Cd : ℝ := (-2 * Real.log P.q) * (J + P.ell : ℕ) * P.C₀
  filter_upwards [hm, shared_exclusion_mass_fixed_cost P J P.ell m r A
    (C + 2 * Cd + 2 * Cm) 1 hr (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hprob hL
  change 1 ≤ L x at hL
  have hLpos : 0 < L x := by linarith
  intro G M ν n n' D c hG hn hn' hD hnx hn'x hDx hc
  have hV (g : Fin G.size) : 0 ≤ G.graph.V g := by
    rw [graph_mass]
    exact (P.positive.2.2.1.trans_le (hG.2.2.1 g).1).le
  have hW := unsharedWeight_nonneg P ν n hV
  have hW' := unsharedWeight_nonneg P ν n' hV
  have hloss : 0 ≤ sharedDampingLoss P G J := zpow_nonneg P.damping.1.le _
  have hd : sharedDampingLoss P G J ≤ L x ^ Cd := sharedDampingLoss_le_log_power P G J x hL hG
  have hmass := sharedExclusionMass_nonneg ν n n' D hV
  calc
    _ ≤ L x ^ C * sharedDampingLoss P G J ^ 2 * unsharedWeight P ν n *
        unsharedWeight P ν n' * sharedExclusionMass ν n n' D :=
      physicalSharedExclusion_norm_le M ν n n' D c (L x ^ C)
        (Real.rpow_nonneg hLpos.le C) hc hV
    _ ≤ L x ^ C * (L x ^ Cd) ^ 2 * L x ^ Cm * L x ^ Cm *
        sharedExclusionMass ν n n' D := by
      gcongr
      · exact hx G J ν n hG
      · exact hx G J ν n' hG
    _ = L x ^ (C + 2 * Cd + 2 * Cm) * sharedExclusionMass ν n n' D := by
      rw [← Real.rpow_mul_natCast hLpos.le Cd 2]
      simp only [Nat.cast_ofNat]
      rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
      congr 2
      ring
    _ ≤ _ := by simpa only [one_mul] using hprob G ν n n' D hG hn hn' hD hnx hn'x hDx

end Erdos821.P5Core
