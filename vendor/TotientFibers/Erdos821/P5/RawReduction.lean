import Erdos821.P5.RawCorrelation

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- All signed comparison patterns, with their actual unshared marked
coefficients, after excluding the raw pattern from the family. -/
def strippedComparisonSum {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Blueprint.Graph.Family P.graph G.graph J m) (raw : Fin B.count)
    (x Z a₁ a₂ lo hi : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ)
    (z₀ : (v : Fin B.count) → SharedDraw (B.pattern v)) : ℂ :=
  ∑ v ∈ (Finset.univ : Finset (Fin B.count)).erase raw,
    residualStrippedLift B v x Z a₁ a₂ E H Ψ k (z₀ v)
      (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u))

theorem stripped_family_eq_raw_add_comparison {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Blueprint.Graph.Family P.graph G.graph J m) (raw : Fin B.count)
    (x Z a₁ a₂ lo hi : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ)
    (z₀ : (v : Fin B.count) → SharedDraw (B.pattern v)) :
    (∑ v : Fin B.count, residualStrippedLift B v x Z a₁ a₂ E H Ψ k (z₀ v)
      (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u))) =
      residualStrippedLift B raw x Z a₁ a₂ E H Ψ k (z₀ raw)
        (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern raw) u)) +
      strippedComparisonSum B raw x Z a₁ a₂ lo hi E H Ψ k z₀ := by
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ raw)).symm

/-- Cancellation of the full lift and the signed comparison sum suffices
for the raw correlation; the exact family stripping error is paid once. -/
theorem raw_correlation_le_of_stripping {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Blueprint.Graph.Family P.graph G.graph J m) (raw : Fin B.count)
    (he : ∀ g, (B.pattern raw).changed g = ∅)
    (hc : ∀ a b u, (B.pattern raw).coefficient a b u = 1)
    (hV : ∀ g, G.graph.V g ≠ 0)
    (x Y Z a₁ a₂ lo hi : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ ε : ℝ)
    (z₀ unused : (v : Fin B.count) → SharedDraw (B.pattern v))
    (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z)
    (hX : 1 ≤ lo * Z) (hk : |(k : ℝ)| ≤ lo * Z / 2)
    (herr : ‖fullResidualLift B x Y Z a₁ a₂ E H Ψ k ζ unused -
      ∑ v : Fin B.count, residualStrippedLift B v x Z a₁ a₂ E H Ψ k (z₀ v)
        (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u))‖ ≤ ε) :
    ‖shiftCorrelation P G x Z a₁ a₂ k E H Ψ lo hi‖ ≤
      ‖fullResidualLift B x Y Z a₁ a₂ E H Ψ k ζ unused‖ +
      ‖strippedComparisonSum B raw x Z a₁ a₂ lo hi E H Ψ k z₀‖ + ε := by
  let F := fullResidualLift B x Y Z a₁ a₂ E H Ψ k ζ unused
  let S := ∑ v : Fin B.count, residualStrippedLift B v x Z a₁ a₂ E H Ψ k (z₀ v)
    (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u))
  let C := strippedComparisonSum B raw x Z a₁ a₂ lo hi E H Ψ k z₀
  have hsum : S = shiftCorrelation P G x Z a₁ a₂ k E H Ψ lo hi + C := by
    dsimp only [S, C]
    rw [stripped_family_eq_raw_add_comparison B raw x Z a₁ a₂ lo hi E H Ψ k z₀,
      raw_stripped_lift_eq_shiftCorrelation B raw he hc hV (z₀ raw)
        x Z a₁ a₂ lo hi E H Ψ k hlo hhi hZ hX hk]
  have hid : shiftCorrelation P G x Z a₁ a₂ k E H Ψ lo hi = F - C - (F - S) := by
    rw [hsum]
    ring
  change ‖_‖ ≤ ‖F‖ + ‖C‖ + ε
  rw [hid]
  exact (norm_sub_le (F - C) (F - S)).trans (add_le_add (norm_sub_le F C) herr)

/-- Uniform reduction of the frozen correlation to the full physical
residual lift and its signed stripped comparisons, with arbitrary log saving.
The raw pattern is extracted from the actual Family.Residual witness. -/
theorem eventual_shiftCorrelation_reduction (P : Geometry) (J m : ℕ)
    (A C C₁ τ η lo hi : ℝ) (bounds : ℕ → ℝ)
    (hC : 0 < C) (hlo : 0 < lo) (hhi : lo < hi) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (Q : ℕ) (h ξ : ℝ)
        (B : Blueprint.Graph.Family P.graph G.graph J m)
        (Z a₁ a₂ : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ)
        (z₀ unused : (v : Fin B.count) → SharedDraw (B.pattern v)),
        Admissible P x G → B.Residual Q h ξ →
        EndpointBound x C τ η E → EndpointBound x C τ η H →
        (B.model k ζ).patternMass ≤ L x ^ C₁ →
        |(k : ℝ)| ≤ L x ^ C → x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C →
        CutoffBound x C lo hi Ψ bounds → ζ = -a₁ - a₂ →
        ∃ raw : Fin B.count,
          (∀ g, (B.pattern raw).changed g = ∅) ∧
          (∀ a b u, (B.pattern raw).coefficient a b u = 1) ∧
          ‖shiftCorrelation P G x Z a₁ a₂ k E H Ψ lo hi‖ ≤
            ‖fullResidualLift B x (x ^ (2 : ℕ)) Z a₁ a₂ E H Ψ k ζ unused‖ +
            ‖strippedComparisonSum B raw x Z a₁ a₂ lo hi E H Ψ k z₀‖ + L x ^ (-A) := by
  filter_upwards [full_residual_stripping_negligible P J m A C C₁ τ η lo hi bounds hC hlo hhi,
    eventual_cutoff_draw_ranges P J P.ell m C lo hi hC hlo hhi] with x hstrip hrange
  intro G Q h ξ B Z a₁ a₂ E H Ψ k ζ z₀ unused hG hB hE hH hmass hk hZlo hZhi hΨ hζ
  obtain ⟨raw, block, he, hc, hcomparisons⟩ := hB
  let u₀ : FreeDraw (B.pattern raw) := fun i => False.elim (by
    have hf : False := by simpa [he i.1] using i.2.property
    exact hf)
  have hprod : freeDrawProduct (B.pattern raw) u₀ = 1 :=
    freeDrawProduct_eq_one_of_empty (B.pattern raw) he u₀
  obtain ⟨hZpos, hX1, hkhalf, hDCx, hYx, hshared⟩ :=
    hrange G (B.pattern raw) u₀ Z k hG hk hZlo hZhi
  simp only [hprod, Nat.cast_one, mul_one] at hX1
  have hV (g : Fin G.size) : G.graph.V g ≠ 0 := by
    rw [graph_mass]
    exact (P.positive.2.2.1.trans_le (hG.2.2.1 g).1).ne'
  refine ⟨raw, he, hc, ?_⟩
  apply raw_correlation_le_of_stripping B raw he hc hV x (x ^ (2 : ℕ)) Z a₁ a₂ lo hi E H Ψ
    k ζ (L x ^ (-A)) z₀ unused hlo hhi hZpos hX1 hkhalf
  exact hstrip G Q h ξ B Z a₁ a₂ E H Ψ k ζ z₀ unused hG ⟨raw, block, he, hc, hcomparisons⟩
    hE hH hmass hk hZlo hZhi hΨ hζ

end Erdos821.P5Core
