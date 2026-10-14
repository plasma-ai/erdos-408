import Erdos821.P5.ResidualCoefficient
import Erdos821.P5.FreeMarkedExclusion

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic Blueprint.Graph

/-- The retained free-label ban and its excluded row partition the full
unshared marked row, including endpoints with no admissible lists. -/
theorem strippedMarkedRow_ban_split {P : Geometry} {G : Blueprint.Analytic.PrimeGroups}
    {J m : ℕ} (ν : Pattern G.graph J P.ell m) (u : FreeDraw ν) (n n' : ℕ)
    (c : UnsharedDraw ν → UnsharedDraw ν → ℂ) :
    strippedMarkedRow ν n n' (fun r s => if UnsharedBan ν r s u then c r s else 0) +
      unsharedBanRow P ν u n n' c = strippedMarkedRow ν n n' c := by
  unfold strippedMarkedRow unsharedBanRow
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hp : UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s
  · by_cases hb : UnsharedBan ν r s u <;> simp [hp, hb]
  · have hn : ¬(UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s ∧ ¬UnsharedBan ν r s u) :=
      fun h => hp ⟨h.1, h.2.1⟩
    simp only [hp, hn, if_false, add_zero]

theorem strippedMarkedRow_norm_le {P : Geometry} {G : Blueprint.Analytic.PrimeGroups}
    {J m : ℕ} (ν : Pattern G.graph J P.ell m) (n n' : ℕ)
    (c : UnsharedDraw ν → UnsharedDraw ν → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ r s, ‖c r s‖ ≤ B) (hV : ∀ g, 0 ≤ G.graph.V g) :
    ‖strippedMarkedRow ν n n' c‖ ≤ B * unsharedWeight P ν n * unsharedWeight P ν n' := by
  let f := fun r s : UnsharedDraw ν =>
    if UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s then c r s else 0
  have hp (r s : UnsharedDraw ν) : ‖f r s‖ ≤
      B * (if UnsharedPhysical ν n r then (1 : ℝ) else 0) *
        (if UnsharedPhysical ν n' s then (1 : ℝ) else 0) := by
    by_cases hr : UnsharedPhysical ν n r <;> by_cases hs : UnsharedPhysical ν n' s
    · simpa only [f, hr, hs, and_self, if_true, mul_one] using hc r s
    · simp [f, hr, hs]
    · simp [f, hr, hs]
    · simp [f, hr, hs]
  have hsum : ‖∑ r, ∑ s, f r s‖ ≤ B * unsharedCount ν n * unsharedCount ν n' := by
    calc
      _ ≤ ∑ r, ∑ s, ‖f r s‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r hr => norm_sum_le _ _))
      _ ≤ ∑ r, ∑ s, B * (if UnsharedPhysical ν n r then (1 : ℝ) else 0) *
          (if UnsharedPhysical ν n' s then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun s hs => hp r s))
      _ = _ := by
        unfold unsharedCount
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hd : 0 ≤ strippedDamping P ν n := zpow_nonneg P.damping.1.le _
  have hd' : 0 ≤ strippedDamping P ν n' := zpow_nonneg P.damping.1.le _
  have hmass : 0 ≤ ν.physicalTargetMass := physicalTargetMass_nonneg ν hV
  unfold strippedMarkedRow
  change ‖((_ : ℝ) : ℂ) * (∑ r, ∑ s, f r s)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (strippedDamping P ν n * strippedDamping P ν n' * ν.physicalTargetMass ^ 2) *
        (B * unsharedCount ν n * unsharedCount ν n') := by gcongr
    _ = _ := by unfold unsharedWeight; ring

theorem shared_good_average_eq {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (n n' D : ℕ) (hV : ∀ g, G.V g ≠ 0) (c : ℂ) :
    (∑ z : SharedDraw ν, if GoodSharedDraw ν n n' D z then (sharedDrawLaw ν z : ℂ) * c else 0) =
      ((1 - sharedExclusionMass ν n n' D : ℝ) : ℂ) * c := by
  rw [← sharedDrawLaw_good_mass ν n n' D hV, Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : GoodSharedDraw ν n n' D z <;> simp only [h, if_true, if_false,
    Complex.ofReal_zero, zero_mul]

theorem sharedExclusionMass_le_one {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (n n' D : ℕ) (hV : ∀ g, 0 < G.V g) :
    sharedExclusionMass ν n n' D ≤ 1 := by
  have hg : 0 ≤ ∑ z : SharedDraw ν,
      if GoodSharedDraw ν n n' D z then sharedDrawLaw ν z else 0 := by
    apply Finset.sum_nonneg
    intro z hz
    split_ifs
    · exact sharedDrawLaw_nonneg ν z (fun g => (hV g).le)
    · rfl
  rw [sharedDrawLaw_good_mass ν n n' D (fun g => (hV g).ne')] at hg
  linarith

end Erdos821.P5Core
