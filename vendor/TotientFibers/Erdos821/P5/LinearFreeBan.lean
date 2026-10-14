import Erdos821.P5.PatternCosts

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem unsharedBanRow_mul {G : PrimeGroups} {J ell m : ℕ}
    (P : Geometry) (ν : Blueprint.Graph.Pattern G.graph J ell m) (u : FreeDraw ν)
    (n n' : ℕ) (z : ℂ) (c : UnsharedDraw ν → UnsharedDraw ν → ℂ) :
    unsharedBanRow P ν u n n' (fun r s => z * c r s) =
      z * unsharedBanRow P ν u n n' c := by
  unfold unsharedBanRow
  have hsum : (∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
      if UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s ∧ ¬UnsharedBan ν r s u
      then z * c r s else 0) = z *
      ∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
        if UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s ∧ ¬UnsharedBan ν r s u
        then c r s else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    split_ifs <;> simp
  rw [hsum]
  ring

theorem weightedFreeBanError_mul {G : PrimeGroups} {J ell m : ℕ}
    (P : Geometry) (ν : Blueprint.Graph.Pattern G.graph J ell m) (x : ℝ)
    (E H : Endpoint) (k : ℤ) (s : FreeDraw ν → Finset ℕ) (K : ℝ) (hK : 0 ≤ K)
    (c : FreeDraw ν → ℕ → UnsharedDraw ν → UnsharedDraw ν → ℂ) :
    weightedFreeBanError P ν x E H k s (fun u n r t => (K : ℂ) * c u n r t) =
      K * weightedFreeBanError P ν x E H k s c := by
  unfold weightedFreeBanError
  simp_rw [unsharedBanRow_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [show K * (freeDrawLaw ν u *
    ∑ n ∈ s u, ‖endpoint G x E n‖ *
      ‖endpoint G x H ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat‖ / (n : ℝ) *
      ‖unsharedBanRow P ν u n ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat (c u n)‖) =
    freeDrawLaw ν u * (K *
      ∑ n ∈ s u, ‖endpoint G x E n‖ *
        ‖endpoint G x H ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat‖ / (n : ℝ) *
        ‖unsharedBanRow P ν u n ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat (c u n)‖) by ring]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Normalize by the actual coefficient bound, including its zero case.
The threshold is independent of that bound and of the coefficient array. -/
theorem weighted_free_ban_error_linear (P : Geometry) (J ell m : ℕ)
    (A C τ η R : ℝ) (hR : 0 < R) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (ν : Blueprint.Graph.Pattern G.graph J ell m)
        (E H : Endpoint) (k : ℤ) (X Y : FreeDraw ν → ℝ) (s : FreeDraw ν → Finset ℕ)
        (K : ℝ) (c : FreeDraw ν → ℕ → UnsharedDraw ν → UnsharedDraw ν → ℂ),
        Admissible P x G → EndpointBound x C τ η E → EndpointBound x C τ η H →
        (∀ u, 0 < X u ∧ Y u ≤ x ^ (2 : ℕ) ∧ Y u ≤ R * X u ∧
          (∀ n ∈ s u, X u ≤ (n : ℝ)) ∧
          (∀ n ∈ s u, 1 ≤ n ∧ (n : ℝ) ≤ Y u ∧
            0 < (n : ℤ) + k * (freeDrawProduct ν u : ℤ) ∧
            ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat ≤ Y u)) →
        0 ≤ K → (∀ u n, n ∈ s u → ∀ r t, ‖c u n r t‖ ≤ K) →
        weightedFreeBanError P ν x E H k s c ≤ K * L x ^ (-A) := by
  filter_upwards [weighted_free_ban_error_negligible P J ell m A C τ η R 0 hR]
    with x hx
  intro G ν E H k X Y s K c hG hE hH hs hK hc
  by_cases hK0 : K = 0
  · have hz (u : FreeDraw ν) (n : ℕ) (hn : n ∈ s u) : c u n = 0 := by
      funext r t
      apply norm_eq_zero.mp
      exact le_antisymm (hK0 ▸ hc u n hn r t) (norm_nonneg _)
    have hzero : weightedFreeBanError P ν x E H k s c = 0 := by
      unfold weightedFreeBanError
      apply Finset.sum_eq_zero
      intro u hu
      have hsum : (∑ n ∈ s u, ‖endpoint G x E n‖ *
          ‖endpoint G x H ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat‖ / (n : ℝ) *
          ‖unsharedBanRow P ν u n ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat
            (c u n)‖) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        rw [hz u n hn]
        simp [unsharedBanRow]
      rw [hsum, mul_zero]
    simp [hzero, hK0]
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    let d := fun u n r t => c u n r t / (K : ℂ)
    have hd (u : FreeDraw ν) (n : ℕ) (hn : n ∈ s u) (r t : UnsharedDraw ν) :
        ‖d u n r t‖ ≤ L x ^ (0 : ℝ) := by
      dsimp [d]
      rw [Real.rpow_zero, norm_div, Complex.norm_real, Real.norm_of_nonneg hK]
      exact (div_le_one hKpos).mpr (hc u n hn r t)
    have hcd : c = fun u n r t => (K : ℂ) * d u n r t := by
      funext u n r t
      dsimp [d]
      have hKc : (K : ℂ) ≠ 0 := by exact_mod_cast hK0
      field_simp
    rw [hcd, weightedFreeBanError_mul P ν x E H k s K hK d]
    exact mul_le_mul_of_nonneg_left (hx G ν E H k X Y s d hG hE hH hs hd) hK

/-- The residual family's actual unshared coefficient pays its own pattern
cost, uniformly over the free draws and endpoint positions. -/
theorem residual_free_ban_error_linear (P : Geometry) (J m : ℕ)
    (A C τ η R : ℝ) (hR : 0 < R) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (B : Blueprint.Graph.Family P.graph G.graph J m)
        (v : Fin B.count) (z₀ : SharedDraw (B.pattern v)) (E H : Endpoint) (k : ℤ)
        (X Y : FreeDraw (B.pattern v) → ℝ) (s : FreeDraw (B.pattern v) → Finset ℕ),
        Admissible P x G → EndpointBound x C τ η E → EndpointBound x C τ η H →
        (∀ u, 0 < X u ∧ Y u ≤ x ^ (2 : ℕ) ∧ Y u ≤ R * X u ∧
          (∀ n ∈ s u, X u ≤ (n : ℝ)) ∧
          (∀ n ∈ s u, 1 ≤ n ∧ (n : ℝ) ≤ Y u ∧
            0 < (n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ) ∧
            ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat ≤ Y u)) →
        weightedFreeBanError P (B.pattern v) x E H k s
          (fun u _ => residualUnsharedCoefficient B v z₀ u) ≤
          patternCost (B.pattern v) * L x ^ (-A) := by
  filter_upwards [weighted_free_ban_error_linear P J P.ell m A C τ η R hR] with x hx
  intro G B v z₀ E H k X Y s hG hE hH hs
  exact hx G (B.pattern v) E H k X Y s (patternCost (B.pattern v))
    (fun u _ => residualUnsharedCoefficient B v z₀ u) hG hE hH hs
    (patternCost_nonneg _) (fun u n hn r t => residualUnsharedCoefficient_norm_le B v z₀ u r t)

end Erdos821.P5Core
