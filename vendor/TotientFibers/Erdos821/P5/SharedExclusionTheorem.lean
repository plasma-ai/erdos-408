import Erdos821.P5.SharedProbability
import Erdos821.P5.PrimeFactorCount
import Erdos821.P5.ListScales

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

def sharedExclusionMass {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (n n' D : ℕ) : ℝ :=
  ∑ z : SharedDraw ν,
    if ∃ i : SharedIndex ν, (z i).val ∈ sharedForbidden ν n n' D i (fun j => z j.val)
    then sharedDrawLaw ν z else 0

/-- The harmonic exclusions of shared draws have arbitrary logarithmic
saving. J is fixed before this error precision and the eventual threshold. -/
theorem shared_exclusion_mass_negligible (P : Geometry) (J ell m : ℕ) (r A : ℝ)
    (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (ν : Blueprint.Graph.Pattern G.graph J ell m) (n n' D : ℕ),
        Admissible P x G → 0 < n → 0 < n' → 0 < D →
        (n : ℝ) ≤ x ^ r → (n' : ℝ) ≤ x ^ r → (D : ℝ) ≤ x ^ r →
        sharedExclusionMass ν n n' D ≤ L x ^ (-A) := by
  let u : ℝ := 2 * J * P.C₀
  let v : ℝ := r / Real.log 2
  let K : ℝ := u * (3 * v + u) * P.vmin⁻¹
  have hC₀ : 0 < P.C₀ := P.positive.2.1
  have hu : 0 ≤ u := by dsimp [u]; exact mul_nonneg (by positivity) P.positive.2.1.le
  have hv : 0 < v := div_pos hr (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  filter_upwards [eventual_constant_log_power_mul_exp_neg P.a A 2 K P.ordered.1,
    eventually_ge_atTop (1 : ℝ)] with x hx hxx
  intro G ν n n' D hG hn hn' hD hnx hn'x hDx
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L x := by linarith [hx.1]
  have hcount := admissible_count_le P G x hG
  have hTL : T x ≤ L x := by
    change Real.log (L x) ≤ L x
    linarith [Real.log_le_sub_one_of_pos hLpos]
  have hMc : (Fintype.card (SharedIndex ν) : ℝ) ≤ (J : ℝ) * G.size := by
    exact_mod_cast sharedIndex_card_le ν
  have hM : (Fintype.card (SharedIndex ν) : ℝ) ≤ u * L x := by
    calc
      _ ≤ (J : ℝ) * G.size := hMc
      _ ≤ (J : ℝ) * (2 * P.C₀ * T x) :=
        mul_le_mul_of_nonneg_left hcount (Nat.cast_nonneg J)
      _ ≤ (J : ℝ) * (2 * P.C₀ * L x) := by gcongr
      _ = u * L x := by dsimp [u]; ring
  have hncount := primeFactors_card_le_log_scale x r hxpos n hn hnx
  have hn'count := primeFactors_card_le_log_scale x r hxpos n' hn' hn'x
  have hDcount := primeFactors_card_le_log_scale x r hxpos D hD hDx
  have hN : ((n.primeFactors.card + n'.primeFactors.card + D.primeFactors.card +
      Fintype.card (SharedIndex ν) : ℕ) : ℝ) ≤ (3 * v + u) * L x := by
    push_cast
    dsimp [v] at *
    linarith
  have hprob := shared_draw_exclusion_probability P G x hx.1 hG ν n n' D
  change sharedExclusionMass ν n n' D ≤ _ at hprob
  calc
    _ ≤ (Fintype.card (SharedIndex ν) : ℝ) *
        (n.primeFactors.card + n'.primeFactors.card + D.primeFactors.card +
          Fintype.card (SharedIndex ν) : ℕ) * (P.vmin⁻¹ * Real.exp (-(L x ^ P.a))) := hprob
    _ ≤ (u * L x) * ((3 * v + u) * L x) * (P.vmin⁻¹ * Real.exp (-(L x ^ P.a))) := by
      have hvmin : 0 < P.vmin := P.positive.2.2.1
      gcongr
    _ = K * L x ^ (2 : ℝ) * Real.exp (-(L x ^ P.a)) := by
      rw [Real.rpow_two]
      dsimp [K]
      ring
    _ ≤ _ := hx.2

theorem shared_exclusion_mass_fixed_cost (P : Geometry) (J ell m : ℕ) (r A B K : ℝ)
    (hr : 0 < r) (hK : 0 ≤ K) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (ν : Blueprint.Graph.Pattern G.graph J ell m) (n n' D : ℕ),
        Admissible P x G → 0 < n → 0 < n' → 0 < D →
        (n : ℝ) ≤ x ^ r → (n' : ℝ) ≤ x ^ r → (D : ℝ) ≤ x ^ r →
        K * L x ^ B * sharedExclusionMass ν n n' D ≤ L x ^ (-A) := by
  filter_upwards [shared_exclusion_mass_negligible P J ell m r (A + B + 1) hr,
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 K)] with x hx hL
  change max 1 K ≤ L x at hL
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hL)
  have hKL : K ≤ L x := (le_max_right _ _).trans hL
  intro G ν n n' D hG hn hn' hD hnx hn'x hDx
  calc
    _ ≤ K * L x ^ B * L x ^ (-(A + B + 1)) :=
      mul_le_mul_of_nonneg_left (hx G ν n n' D hG hn hn' hD hnx hn'x hDx)
        (mul_nonneg hK (Real.rpow_nonneg hLpos.le B))
    _ ≤ L x * L x ^ B * L x ^ (-(A + B + 1)) := by gcongr
    _ = L x ^ (-A) := by
      have hprod : L x * L x ^ B = L x ^ (1 + B) := by
        rw [Real.rpow_add hLpos, Real.rpow_one]
      rw [hprod, ← Real.rpow_add hLpos]
      congr 1
      ring

end Erdos821.P5Core
