import Erdos821.P5.ResidualAverage
import Erdos821.P5.LiftedSharedRow

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem strippedLiftScalar_norm (G : PrimeGroups) (x Z a₁ a₂ : ℝ)
    (E H : Endpoint) (Ψ : ℝ → ℂ) (n n' D : ℕ) :
    ‖strippedLiftScalar G x Z a₁ a₂ E H Ψ n n' D‖ =
      ‖Ψ ((n : ℝ) / (Z * D))‖ * ‖endpoint G x E n‖ * ‖endpoint G x H n'‖ / (n : ℝ) := by
  unfold strippedLiftScalar harmonicCutoff
  simp only [norm_mul, norm_div, norm_mellin, norm_star, Int.cast_natCast,
    Complex.norm_natCast, mul_one]
  ring

/-- The shared average before replacing its actual row by the unshared row.
The finite support is independent of shared draws; the earlier finite-root
identity still needs its support gates discharged before using this sum. -/
def residualAveragedLift {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Blueprint.Graph.Family P.graph G.graph J m) (v : Fin B.count)
    (x Z a₁ a₂ : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ)
    (unused : SharedDraw (B.pattern v)) (s : FreeDraw (B.pattern v) → Finset ℕ) : ℂ :=
  ∑ u : FreeDraw (B.pattern v), (freeDrawLaw (B.pattern v) u : ℂ) *
    ∑ n ∈ s u, strippedLiftScalar G x Z a₁ a₂ E H Ψ n
      ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat
      (freeDrawProduct (B.pattern v) u) *
      residualSharedAverage B v k ζ u unused n
        ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat

def residualStrippedLift {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Blueprint.Graph.Family P.graph G.graph J m) (v : Fin B.count)
    (x Z a₁ a₂ : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ)
    (z₀ : SharedDraw (B.pattern v)) (s : FreeDraw (B.pattern v) → Finset ℕ) : ℂ :=
  ∑ u : FreeDraw (B.pattern v), (freeDrawLaw (B.pattern v) u : ℂ) *
    ∑ n ∈ s u, strippedLiftScalar G x Z a₁ a₂ E H Ψ n
      ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat
      (freeDrawProduct (B.pattern v) u) *
      strippedMarkedRow (B.pattern v) n
        ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat
        (residualUnsharedCoefficient B v z₀ u)

theorem residual_lift_difference_norm_le {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Blueprint.Graph.Family P.graph G.graph J m) (v : Fin B.count)
    (x Z a₁ a₂ : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ)
    (z₀ unused : SharedDraw (B.pattern v)) (s : FreeDraw (B.pattern v) → Finset ℕ)
    (K : ℝ) (hK : 0 ≤ K) (hV : ∀ g, 0 ≤ G.graph.V g)
    (hΨ : ∀ u n, n ∈ s u → ‖Ψ ((n : ℝ) / (Z * freeDrawProduct (B.pattern v) u))‖ ≤ K) :
    ‖residualAveragedLift B v x Z a₁ a₂ E H Ψ k ζ unused s -
      residualStrippedLift B v x Z a₁ a₂ E H Ψ k z₀ s‖ ≤
      K * weightedResidualRowError B v x E H k ζ z₀ unused s := by
  unfold residualAveragedLift residualStrippedLift
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ u : FreeDraw (B.pattern v), freeDrawLaw (B.pattern v) u *
        ∑ n ∈ s u, ‖strippedLiftScalar G x Z a₁ a₂ E H Ψ n
          ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat
          (freeDrawProduct (B.pattern v) u)‖ *
          ‖residualSharedAverage B v k ζ u unused n
              ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat -
            strippedMarkedRow (B.pattern v) n
              ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat
              (residualUnsharedCoefficient B v z₀ u)‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (freeDrawLaw_nonneg _ _ hV)]
      apply mul_le_mul_of_nonneg_left _ (freeDrawLaw_nonneg _ _ hV)
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    _ ≤ ∑ u : FreeDraw (B.pattern v), freeDrawLaw (B.pattern v) u *
        ∑ n ∈ s u, (K * (‖endpoint G x E n‖ *
          ‖endpoint G x H ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat‖ /
          (n : ℝ))) *
          ‖residualSharedAverage B v k ζ u unused n
              ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat -
            strippedMarkedRow (B.pattern v) n
              ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat
              (residualUnsharedCoefficient B v z₀ u)‖ := by
      apply Finset.sum_le_sum
      intro u hu
      apply mul_le_mul_of_nonneg_left _ (freeDrawLaw_nonneg _ _ hV)
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [strippedLiftScalar_norm]
      calc
        _ = ‖Ψ ((n : ℝ) / (Z * freeDrawProduct (B.pattern v) u))‖ *
            (‖endpoint G x E n‖ *
              ‖endpoint G x H ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat‖ /
              (n : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hΨ u n hn) (by positivity)
    _ = _ := by
      unfold weightedResidualRowError
      simp_rw [mul_assoc K, ← Finset.mul_sum]
      simp_rw [← mul_assoc, mul_comm (freeDrawLaw _ _) K, mul_assoc K]
      rw [← Finset.mul_sum]

/-- Replacement of the actual residual shared row by the stripped row,
with its cutoff and Mellin phases and arbitrary endpoint sequences. -/
theorem residual_lift_stripping_negligible (P : Geometry) (J m : ℕ)
    (A C CΨ τ η R : ℝ) (hR : 0 < R) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (Q : ℕ) (h ξ : ℝ)
        (B : Blueprint.Graph.Family P.graph G.graph J m) (v : Fin B.count)
        (Z a₁ a₂ : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ)
        (z₀ unused : SharedDraw (B.pattern v))
        (X Y : FreeDraw (B.pattern v) → ℝ) (s : FreeDraw (B.pattern v) → Finset ℕ),
        Admissible P x G → B.Residual Q h ξ →
        EndpointBound x C τ η E → EndpointBound x C τ η H →
        (∀ u, (freeDrawProduct (B.pattern v) u : ℝ) ≤ x ^ (2 : ℕ)) →
        (∀ u, 0 < X u ∧ 1 ≤ Y u ∧ Y u ≤ x ^ (2 : ℕ) ∧ Y u ≤ R * X u ∧
          (∀ n ∈ s u, X u ≤ (n : ℝ)) ∧
          (∀ n ∈ s u, 1 ≤ n ∧ (n : ℝ) ≤ Y u ∧
            0 < (n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ) ∧
            ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat ≤ Y u)) →
        (∀ u n, n ∈ s u → ‖Ψ ((n : ℝ) / (Z * freeDrawProduct (B.pattern v) u))‖ ≤ L x ^ CΨ) →
        ‖residualAveragedLift B v x Z a₁ a₂ E H Ψ k ζ unused s -
          residualStrippedLift B v x Z a₁ a₂ E H Ψ k z₀ s‖ ≤
          L x ^ (-A) * patternCost (B.pattern v) := by
  filter_upwards [weighted_residual_row_error_negligible P J m (A + CΨ) C τ η R hR,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hL
  change 1 ≤ L x at hL
  have hLpos : 0 < L x := by linarith
  intro G Q h ξ B v Z a₁ a₂ E H Ψ k ζ z₀ unused X Y s hG hB hE hH hD hs hΨ
  have hV (g : Fin G.size) : 0 ≤ G.graph.V g := by
    rw [graph_mass]
    exact (P.positive.2.2.1.trans_le (hG.2.2.1 g).1).le
  calc
    _ ≤ L x ^ CΨ * weightedResidualRowError B v x E H k ζ z₀ unused s :=
      residual_lift_difference_norm_le B v x Z a₁ a₂ E H Ψ k ζ z₀ unused s
        (L x ^ CΨ) (Real.rpow_nonneg hLpos.le _) hV hΨ
    _ ≤ L x ^ CΨ * (patternCost (B.pattern v) * L x ^ (-(A + CΨ))) :=
      mul_le_mul_of_nonneg_left (hx G Q h ξ B v E H k ζ z₀ unused X Y s hG hB hE hH hD hs)
        (Real.rpow_nonneg hLpos.le _)
    _ = _ := by
      rw [show L x ^ CΨ * (patternCost (B.pattern v) * L x ^ (-(A + CΨ))) =
        (L x ^ CΨ * L x ^ (-(A + CΨ))) * patternCost (B.pattern v) by ring,
        ← Real.rpow_add hLpos]
      congr 2
      ring

/-- Summing the signed residual family uses its actual pattern mass, with
no dependence on the number of comparison patterns. -/
theorem residual_family_stripping_negligible (P : Geometry) (J m : ℕ)
    (A C CΨ C₁ τ η R : ℝ) (hR : 0 < R) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (Q : ℕ) (h ξ : ℝ)
        (B : Blueprint.Graph.Family P.graph G.graph J m)
        (Z a₁ a₂ : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ)
        (z₀ unused : (v : Fin B.count) → SharedDraw (B.pattern v))
        (X Y : (v : Fin B.count) → FreeDraw (B.pattern v) → ℝ)
        (s : (v : Fin B.count) → FreeDraw (B.pattern v) → Finset ℕ),
        Admissible P x G → B.Residual Q h ξ →
        EndpointBound x C τ η E → EndpointBound x C τ η H →
        (B.model k ζ).patternMass ≤ L x ^ C₁ →
        (∀ v u, (freeDrawProduct (B.pattern v) u : ℝ) ≤ x ^ (2 : ℕ)) →
        (∀ v u, 0 < X v u ∧ 1 ≤ Y v u ∧ Y v u ≤ x ^ (2 : ℕ) ∧ Y v u ≤ R * X v u ∧
          (∀ n ∈ s v u, X v u ≤ (n : ℝ)) ∧
          (∀ n ∈ s v u, 1 ≤ n ∧ (n : ℝ) ≤ Y v u ∧
            0 < (n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ) ∧
            ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat ≤ Y v u)) →
        (∀ v u n, n ∈ s v u →
          ‖Ψ ((n : ℝ) / (Z * freeDrawProduct (B.pattern v) u))‖ ≤ L x ^ CΨ) →
        ‖(∑ v : Fin B.count, residualAveragedLift B v x Z a₁ a₂ E H Ψ k ζ (unused v) (s v)) -
          ∑ v : Fin B.count, residualStrippedLift B v x Z a₁ a₂ E H Ψ k (z₀ v) (s v)‖ ≤
          L x ^ (-A) := by
  filter_upwards [residual_lift_stripping_negligible P J m (A + C₁) C CΨ τ η R hR,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hL
  change 1 ≤ L x at hL
  have hLpos : 0 < L x := by linarith
  intro G Q h ξ B Z a₁ a₂ E H Ψ k ζ z₀ unused X Y s hG hB hE hH hmass hD hs hΨ
  rw [← Finset.sum_sub_distrib]
  have he (v : Fin B.count) :
      ‖residualAveragedLift B v x Z a₁ a₂ E H Ψ k ζ (unused v) (s v) -
        residualStrippedLift B v x Z a₁ a₂ E H Ψ k (z₀ v) (s v)‖ ≤
        L x ^ (-(A + C₁)) * patternCost (B.pattern v) :=
    hx G Q h ξ B v Z a₁ a₂ E H Ψ k ζ (z₀ v) (unused v) (X v) (Y v) (s v)
      hG hB hE hH (hD v) (hs v) (hΨ v)
  calc
    _ ≤ L x ^ (-(A + C₁) + C₁) :=
      norm_sum_pattern_errors_log_le B k ζ x (A + C₁) C₁ hLpos
        (fun v => residualAveragedLift B v x Z a₁ a₂ E H Ψ k ζ (unused v) (s v) -
          residualStrippedLift B v x Z a₁ a₂ E H Ψ k (z₀ v) (s v)) he hmass
    _ = _ := by congr 1; ring

end Erdos821.P5Core
