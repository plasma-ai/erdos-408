import Erdos821.P5.StrippedPhysicalLists
import Erdos821.P5.SharedExclusionTheorem
import Erdos821.P5.ResidualExt

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Graph

theorem changed_slot_unshared {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (g : P.Group) (i : Fin J) (hi : i ∈ ν.changed g) :
    ν.slot i ∈ unsharedSlots ν g := by
  rw [mem_unsharedSlots]
  rintro ⟨j, heq, hj⟩
  exact hj ((shared_slot_injective ν heq) ▸ hi)

theorem residual_coefficient_assemble_shared_ext {F : FixedData} {P : PrimeGroups}
    {J m Q : ℕ} {h ξ : ℝ} (B : Family F P J m) (hB : B.Residual Q h ξ)
    (v : Fin B.count) (z z' : SharedDraw (B.pattern v))
    (r s : UnsharedDraw (B.pattern v)) (u : P.Aux J) :
    (B.pattern v).coefficient (P.restrictBig (assembleLabels (B.pattern v) z r))
      (P.restrictBig (assembleLabels (B.pattern v) z s)) (fun g => u g.val) =
    (B.pattern v).coefficient (P.restrictBig (assembleLabels (B.pattern v) z' r))
      (P.restrictBig (assembleLabels (B.pattern v) z' s)) (fun g => u g.val) := by
  apply residual_coefficient_changed_ext B hB v
  · intro g i hi
    change assembleLabels (B.pattern v) z r g.val ((B.pattern v).slot i) =
      assembleLabels (B.pattern v) z' r g.val ((B.pattern v).slot i)
    have hm := changed_slot_unshared (B.pattern v) g.val i hi
    rw [show (B.pattern v).slot i =
      (⟨(B.pattern v).slot i, hm⟩ : {i // i ∈ unsharedSlots (B.pattern v) g.val}).val from rfl,
      assembleLabels_unshared, assembleLabels_unshared]
  · intro g i hi
    change assembleLabels (B.pattern v) z s g.val ((B.pattern v).slot i) =
      assembleLabels (B.pattern v) z' s g.val ((B.pattern v).slot i)
    have hm := changed_slot_unshared (B.pattern v) g.val i hi
    rw [show (B.pattern v).slot i =
      (⟨(B.pattern v).slot i, hm⟩ : {i // i ∈ unsharedSlots (B.pattern v) g.val}).val from rfl,
      assembleLabels_unshared, assembleLabels_unshared]
  · intro g i hi
    rfl

theorem sharedDrawLaw_nonneg {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (z : SharedDraw ν) (hV : ∀ g, 0 ≤ P.V g) :
    0 ≤ sharedDrawLaw ν z := by
  apply productLaw_nonneg
  intro i p
  exact inv_nonneg.mpr (mul_nonneg (hV i.1) (Nat.cast_nonneg p.val))

theorem sharedExclusionMass_nonneg {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (n n' D : ℕ) (hV : ∀ g, 0 ≤ P.V g) :
    0 ≤ sharedExclusionMass ν n n' D := by
  apply Finset.sum_nonneg
  intro z hz
  split_ifs
  · exact sharedDrawLaw_nonneg ν z hV
  · rfl

theorem sharedDrawLaw_good_mass {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (n n' D : ℕ) (hV : ∀ g, P.V g ≠ 0) :
    (∑ z : SharedDraw ν, if GoodSharedDraw ν n n' D z then sharedDrawLaw ν z else 0) =
      1 - sharedExclusionMass ν n n' D := by
  have heq : (∑ z : SharedDraw ν,
      if GoodSharedDraw ν n n' D z then sharedDrawLaw ν z else 0) +
      sharedExclusionMass ν n n' D = 1 := by
    rw [sharedExclusionMass, ← Finset.sum_add_distrib, ← sharedDrawLaw_sum ν hV]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases h : GoodSharedDraw ν n n' D z
    · have he : ¬∃ i : SharedIndex ν,
          (z i).val ∈ sharedForbidden ν n n' D i (fun j => z j.val) := by
        simpa only [GoodSharedDraw, not_exists] using h
      simp only [h, he, if_true, if_false, add_zero]
    · have he : ∃ i : SharedIndex ν,
          (z i).val ∈ sharedForbidden ν n n' D i (fun j => z j.val) := by
        simpa only [GoodSharedDraw, not_forall, not_not] using h
      simp only [h, he, if_true, if_false, zero_add]
  linarith

/-- Discarding shared draws has exactly their harmonic mass as cost when the
remaining row is independent of those draws. -/
theorem shared_constant_removal_norm {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (n n' D : ℕ) (hV : ∀ g, 0 < P.V g) (c : ℂ) :
    ‖(∑ z : SharedDraw ν, if GoodSharedDraw ν n n' D z
      then (sharedDrawLaw ν z : ℂ) * c else 0) - c‖ =
        sharedExclusionMass ν n n' D * ‖c‖ := by
  have hsum : (∑ z : SharedDraw ν, if GoodSharedDraw ν n n' D z
      then (sharedDrawLaw ν z : ℂ) * c else 0) =
        ((1 - sharedExclusionMass ν n n' D : ℝ) : ℂ) * c := by
    rw [← sharedDrawLaw_good_mass ν n n' D (fun g => (hV g).ne'), Complex.ofReal_sum,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases h : GoodSharedDraw ν n n' D z <;> simp only [h, if_true, if_false,
      Complex.ofReal_zero, zero_mul]
  rw [hsum]
  have heq : ((1 - sharedExclusionMass ν n n' D : ℝ) : ℂ) * c - c =
      -(sharedExclusionMass ν n n' D : ℂ) * c := by
    push_cast
    ring
  rw [heq, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sharedExclusionMass_nonneg ν n n' D (fun g => (hV g).le))]

theorem shared_constant_removal_negligible (P : Blueprint.Analytic.Geometry)
    (J ell m : ℕ) (r A B K : ℝ) (hr : 0 < r) (hK : 0 ≤ K) :
    ∀ᶠ x : ℝ in Filter.atTop,
      ∀ (G : Blueprint.Analytic.PrimeGroups) (ν : Pattern G.graph J ell m)
        (n n' D : ℕ) (c : ℂ),
        Blueprint.Analytic.Admissible P x G → 0 < n → 0 < n' → 0 < D →
        (n : ℝ) ≤ x ^ r → (n' : ℝ) ≤ x ^ r → (D : ℝ) ≤ x ^ r →
        ‖c‖ ≤ K * Blueprint.Analytic.L x ^ B →
        ‖(∑ z : SharedDraw ν, if GoodSharedDraw ν n n' D z
          then (sharedDrawLaw ν z : ℂ) * c else 0) - c‖ ≤
            Blueprint.Analytic.L x ^ (-A) := by
  filter_upwards [shared_exclusion_mass_fixed_cost P J ell m r A B K hr hK]
    with x hx
  intro G ν n n' D c hG hn hn' hD hnx hn'x hDx hc
  have hV (g : Fin G.size) : 0 < G.graph.V g := by
    rw [Blueprint.Analytic.graph_mass]
    exact P.positive.2.2.1.trans_le (hG.2.2.1 g).1
  rw [shared_constant_removal_norm ν n n' D hV c]
  calc
    _ ≤ sharedExclusionMass ν n n' D * (K * Blueprint.Analytic.L x ^ B) :=
      mul_le_mul_of_nonneg_left hc (sharedExclusionMass_nonneg ν n n' D (fun g => (hV g).le))
    _ = K * Blueprint.Analytic.L x ^ B * sharedExclusionMass ν n n' D := mul_comm _ _
    _ ≤ _ := hx G ν n n' D hG hn hn' hD hnx hn'x hDx

end Erdos821.P5Core
