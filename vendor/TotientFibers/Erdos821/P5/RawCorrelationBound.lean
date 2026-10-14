import Erdos821.P5.StrippedFamilyCancellation

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- The remaining obligation is the signed comparison sum, for any raw
pattern of the actual residual family. The error has arbitrary log saving. -/
theorem residual_family_shiftCorrelation_bound (hsep : Blueprint.FourierSeparation)
    (ht : Blueprint.TransferenceInputs) (hid : IdealConstruction)
    (P : Geometry) (D C τ η lo hi : ℝ) (bounds : ℕ → ℝ)
    (hD : 0 < D) (hC : 0 < C) (hτ : 0 < τ) (hτhi : τ ≤ 1)
    (hlo : 0 < lo) (hhi : lo < hi) (hbounds : ∀ j, 0 ≤ bounds j) :
    ∃ m J₀ : ℕ, ∃ C₁ qexp hexp ξexp : ℝ,
      0 < qexp ∧ 0 < hexp ∧ 0 < ξexp ∧
      ∀ J : ℕ, J₀ ≤ J → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
        ∀ (G : PrimeGroups), Admissible P x G → ∃ B : Family P.graph G.graph J m,
          B.Residual ⌊L x ^ qexp⌋₊ (L x ^ (-hexp)) (L x ^ (-ξexp)) ∧
          (B.model 1 0).patternMass ≤ L x ^ C₁ ∧
          ∀ raw : Fin B.count, (∀ g, (B.pattern raw).changed g = ∅) →
            (∀ a b u, (B.pattern raw).coefficient a b u = 1) →
            ∀ (E H : Endpoint) (k : ℤ) (Z a₁ a₂ : ℝ) (Ψ : ℝ → ℂ)
              (z₀ : (v : Fin B.count) → SharedDraw (B.pattern v)),
              EndpointBound x C τ η E → EndpointBound x C τ η H →
              k ≠ 0 → |(k : ℝ)| ≤ L x ^ C → x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C →
              |a₁| ≤ L x ^ C → |a₂| ≤ L x ^ C → CutoffBound x C lo hi Ψ bounds →
              ‖shiftCorrelation P G x Z a₁ a₂ k E H Ψ lo hi‖ ≤
                ‖strippedComparisonSum B raw x Z a₁ a₂ lo hi E H Ψ k z₀‖ + K * L x ^ (-D) := by
  obtain ⟨m, J₀, C₁, qexp, hexp, ξexp, hq, hh, hξ, hfamily⟩ :=
    residual_family_stripped_lift_bound hsep ht hid P D C τ η lo hi bounds
      hD hC hτ hτhi hlo hhi hbounds
  refine ⟨m, J₀, C₁, qexp, hexp, ξexp, hq, hh, hξ, ?_⟩
  intro J hJ
  obtain ⟨K, hK, hstrip⟩ := hfamily J hJ
  refine ⟨K, hK, ?_⟩
  filter_upwards [hstrip, eventual_cutoff_draw_ranges P J P.ell m C lo hi hC hlo hhi]
    with x hstrip hrange
  intro G hG
  obtain ⟨B, hres, hmass, hstrip⟩ := hstrip G hG
  refine ⟨B, hres, hmass, ?_⟩
  intro raw he hc E H k Z a₁ a₂ Ψ z₀ hE hH hk hkbound hZlo hZhi ha₁ ha₂ hΨ
  let u₀ : FreeDraw (B.pattern raw) := fun i => False.elim (by
    have hf : False := by simpa [he i.1] using i.2.property
    exact hf)
  have hprod := freeDrawProduct_eq_one_of_empty (B.pattern raw) he u₀
  obtain ⟨hZpos, hX1, hkhalf, hDCx, hYx, hshared⟩ :=
    hrange G (B.pattern raw) u₀ Z k hG hkbound hZlo hZhi
  simp only [hprod, Nat.cast_one, mul_one] at hX1
  have hV (g : Fin G.size) : G.graph.V g ≠ 0 := by
    rw [graph_mass]
    exact (P.positive.2.2.1.trans_le (hG.2.2.1 g).1).ne'
  have hnorm := hstrip E H k Z a₁ a₂ Ψ z₀ hE hH hk hkbound hZlo hZhi ha₁ ha₂ hΨ
  let S := ∑ v : Fin B.count, residualStrippedLift B v x Z a₁ a₂ E H Ψ k (z₀ v)
    (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u))
  let A := strippedComparisonSum B raw x Z a₁ a₂ lo hi E H Ψ k z₀
  have hsum : S = shiftCorrelation P G x Z a₁ a₂ k E H Ψ lo hi + A := by
    dsimp only [S, A]
    rw [stripped_family_eq_raw_add_comparison B raw x Z a₁ a₂ lo hi E H Ψ k z₀,
      raw_stripped_lift_eq_shiftCorrelation B raw he hc hV (z₀ raw)
        x Z a₁ a₂ lo hi E H Ψ k hlo hhi hZpos hX1 hkhalf]
  have heq : shiftCorrelation P G x Z a₁ a₂ k E H Ψ lo hi = S - A := by rw [hsum]; ring
  change ‖_‖ ≤ ‖A‖ + K * L x ^ (-D)
  rw [heq]
  exact (norm_sub_le S A).trans (by linarith [hnorm])

end Erdos821.P5Core
