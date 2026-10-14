import Erdos821.P5.UnsharedBan

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

def unsharedBanRow {G : PrimeGroups} {J ell m : ℕ}
    (P : Geometry) (ν : Blueprint.Graph.Pattern G.graph J ell m) (u : FreeDraw ν)
    (n n' : ℕ) (c : UnsharedDraw ν → UnsharedDraw ν → ℂ) : ℂ :=
  ((strippedDamping P ν n * strippedDamping P ν n' * ν.physicalTargetMass ^ 2 : ℝ) : ℂ) *
    ∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
      if UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s ∧ ¬UnsharedBan ν r s u
      then c r s else 0

theorem unsharedBanRow_norm_le {G : PrimeGroups} {J ell m : ℕ}
    (P : Geometry) (ν : Blueprint.Graph.Pattern G.graph J ell m) (u : FreeDraw ν)
    (n n' : ℕ) (c : UnsharedDraw ν → UnsharedDraw ν → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ r s, ‖c r s‖ ≤ B) (hV : ∀ g, 0 ≤ G.graph.V g) :
    ‖unsharedBanRow P ν u n n' c‖ ≤ B * unsharedWeight P ν n * unsharedWeight P ν n' := by
  let f := fun r s : UnsharedDraw ν =>
    if UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s ∧ ¬UnsharedBan ν r s u
    then c r s else 0
  have hpoint (r s : UnsharedDraw ν) : ‖f r s‖ ≤
      B * (if UnsharedPhysical ν n r then (1 : ℝ) else 0) *
        (if UnsharedPhysical ν n' s then (1 : ℝ) else 0) := by
    by_cases h : UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s ∧ ¬UnsharedBan ν r s u
    · simpa only [f, h, h.1, h.2.1, true_and, not_false_eq_true, if_true, mul_one] using hc r s
    · simp only [f, h, if_false, norm_zero]
      apply mul_nonneg
      · exact mul_nonneg hB (by split_ifs <;> norm_num)
      · split_ifs <;> norm_num
  have hsum : ‖∑ r, ∑ s, f r s‖ ≤ B * unsharedCount ν n * unsharedCount ν n' := by
    calc
      _ ≤ ∑ r, ∑ s, ‖f r s‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r hr => norm_sum_le _ _))
      _ ≤ ∑ r, ∑ s, B * (if UnsharedPhysical ν n r then (1 : ℝ) else 0) *
          (if UnsharedPhysical ν n' s then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun s hs => hpoint r s))
      _ = _ := by
        unfold unsharedCount
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hd : 0 ≤ strippedDamping P ν n := zpow_nonneg P.damping.1.le _
  have hd' : 0 ≤ strippedDamping P ν n' := zpow_nonneg P.damping.1.le _
  unfold unsharedBanRow
  change ‖((_ : ℝ) : ℂ) * (∑ r, ∑ s, f r s)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (strippedDamping P ν n * strippedDamping P ν n' * ν.physicalTargetMass ^ 2) *
        (B * unsharedCount ν n * unsharedCount ν n') := by gcongr
    _ = _ := by unfold unsharedWeight; ring

theorem unsharedBanRow_eq_zero_of_no_collision {G : PrimeGroups} {J ell m : ℕ}
    (P : Geometry) (ν : Blueprint.Graph.Pattern G.graph J ell m) (u : FreeDraw ν)
    (n n' : ℕ) (k : ℤ) (c : UnsharedDraw ν → UnsharedDraw ν → ℂ)
    (hshift : (n' : ℤ) = (n : ℤ) + k * (freeDrawProduct ν u : ℤ))
    (hn : ¬FreeCollisionEvent ν u n) : unsharedBanRow P ν u n n' c = 0 := by
  unfold unsharedBanRow
  have hzero : (∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
      if UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s ∧ ¬UnsharedBan ν r s u
      then c r s else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro s hs
    by_cases h : UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s ∧ ¬UnsharedBan ν r s u
    · exact False.elim (hn (unshared_ban_violation_free_divisor ν r s u n n' k
        h.1 h.2.1 hshift h.2.2))
    · rw [if_neg h]
  rw [hzero, mul_zero]

def weightedFreeBanError {G : PrimeGroups} {J ell m : ℕ}
    (P : Geometry) (ν : Blueprint.Graph.Pattern G.graph J ell m) (x : ℝ)
    (E H : Endpoint) (k : ℤ) (s : FreeDraw ν → Finset ℕ)
    (c : FreeDraw ν → ℕ → UnsharedDraw ν → UnsharedDraw ν → ℂ) : ℝ :=
  ∑ u : FreeDraw ν, freeDrawLaw ν u *
    ∑ n ∈ s u, ‖endpoint G x E n‖ *
      ‖endpoint G x H ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat‖ / (n : ℝ) *
      ‖unsharedBanRow P ν u n ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat (c u n)‖

/-- The full marked free/endpoint ban error, averaged over the actual free
harmonic laws, has arbitrary log saving with unrestricted endpoint sequences. -/
theorem weighted_free_ban_error_negligible (P : Geometry) (J ell m : ℕ)
    (A C τ η R B : ℝ) (hR : 0 < R) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (ν : Blueprint.Graph.Pattern G.graph J ell m)
        (E H : Endpoint) (k : ℤ) (X Y : FreeDraw ν → ℝ) (s : FreeDraw ν → Finset ℕ)
        (c : FreeDraw ν → ℕ → UnsharedDraw ν → UnsharedDraw ν → ℂ),
        Admissible P x G → EndpointBound x C τ η E → EndpointBound x C τ η H →
        (∀ u, 0 < X u ∧ Y u ≤ x ^ (2 : ℕ) ∧ Y u ≤ R * X u ∧
          (∀ n ∈ s u, X u ≤ (n : ℝ)) ∧
          (∀ n ∈ s u, 1 ≤ n ∧ (n : ℝ) ≤ Y u ∧
            0 < (n : ℤ) + k * (freeDrawProduct ν u : ℤ) ∧
            ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat ≤ Y u)) →
        (∀ u n, n ∈ s u → ∀ r t, ‖c u n r t‖ ≤ L x ^ B) →
        weightedFreeBanError P ν x E H k s c ≤ L x ^ (-A) := by
  obtain ⟨Cm, hm⟩ := eventual_unsharedWeight_bound P ell m
  let cost : ℝ := B + 2 * Cm
  filter_upwards [hm, free_slot_average_negligible P J ell m A C τ η R cost 1 hR
    (by norm_num), Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx havg hL
  change 1 ≤ L x at hL
  have hLpos : 0 < L x := by linarith
  intro G ν E H k X Y s c hG hE hH hs hc
  have hV (g : Fin G.size) : 0 < G.graph.V g := by
    rw [graph_mass]
    exact P.positive.2.2.1.trans_le (hG.2.2.1 g).1
  have hpoint (u : FreeDraw ν) (n : ℕ) (hn : n ∈ s u) :
      ‖unsharedBanRow P ν u n ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat (c u n)‖ ≤
        if FreeCollisionEvent ν u n then L x ^ cost else 0 := by
    by_cases h : FreeCollisionEvent ν u n
    · rw [if_pos h]
      calc
        _ ≤ L x ^ B * unsharedWeight P ν n *
            unsharedWeight P ν ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat :=
          unsharedBanRow_norm_le P ν u n _ (c u n) (L x ^ B)
            (Real.rpow_nonneg hLpos.le _) (hc u n hn) (fun g => (hV g).le)
        _ ≤ L x ^ B * L x ^ Cm * L x ^ Cm := by
          have hn0 := unsharedWeight_nonneg P ν n (fun g => (hV g).le)
          have hn'0 := unsharedWeight_nonneg P ν ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat
            (fun g => (hV g).le)
          gcongr
          · exact hx G J ν n hG
          · exact hx G J ν _ hG
        _ = _ := by
          rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
          congr 1
          dsimp [cost]
          ring
    · rw [if_neg h, unsharedBanRow_eq_zero_of_no_collision P ν u n _ k (c u n)
        (Int.toNat_of_nonneg ((hs u).2.2.2.2 n hn).2.2.1.le) h, norm_zero]
  unfold weightedFreeBanError
  calc
    _ ≤ ∑ u : FreeDraw ν, freeDrawLaw ν u *
        ∑ n ∈ s u, ‖endpoint G x E n‖ *
          ‖endpoint G x H ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat‖ / (n : ℝ) *
          (if FreeCollisionEvent ν u n then L x ^ cost else 0) := by
      apply Finset.sum_le_sum
      intro u hu
      apply mul_le_mul_of_nonneg_left _ (freeDrawLaw_nonneg ν u (fun g => (hV g).le))
      exact Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hpoint u n hn) (by positivity))
    _ = ∑ u : FreeDraw ν, freeDrawLaw ν u *
        (1 * L x ^ cost * freeCollisionError ν u x E H k (s u)) := by
      apply Finset.sum_congr rfl
      intro u hu
      congr 1
      unfold freeCollisionError
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> ring
    _ ≤ _ := havg G ν E H k X Y s hG hE hH hs

end Erdos821.P5Core
