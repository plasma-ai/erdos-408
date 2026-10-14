import Erdos821.P5.ComparisonFourierArcBound
import Erdos821.P5.SmoothEndpointSquareTask
import Erdos821.P5.SmoothComparisonParameters

noncomputable section
open scoped BigOperators Classical
open Filter MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem smooth_cell_norm_le_of_square_bounds
    (hfourier : FourierArcTask) {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool)
    (h : ℝ) (hh : 0 < h) (hwidth : Real.exp (2 * h) ≤ 2)
    (j : ℤ × ℤ) (χA χB : CharacterIndex Q) (z : SharedDraw ν)
    (x Z a₁ a₂ v lo hi S : ℝ) (E H : Endpoint) (k : ℤ)
    (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z)
    (hk : |(k : ℝ)| ≤ lo * Z / 8) (hG : Admissible P x G) (hS : 0 ≤ S) :
    let Y := Z * comparisonJointScale h j
    sqNorm (comparisonCommonRoots lo hi Y)
      (comparisonSmoothSource G x Y a₁ v lo hi hlo hhi E
        (comparisonMarkedEndpoint ν block true h j.2 χB)) ≤ S →
    sqNorm (comparisonTargetRoots lo hi Y)
      (comparisonSmoothTarget G x Y a₂ lo hi hlo hhi H
        (comparisonMarkedEndpoint ν block false h j.1 χA)) ≤ S →
    ‖smoothComparisonCellCorrelation ν block h j χA χB x Y a₁ a₂ v lo hi hlo hhi E H k‖ ≤
      Y⁻¹ * S := by
  dsimp only
  intro ha hb
  have hV (g : Fin G.size) : 0 < G.graph.V g := by
    rw [graph_mass]
    exact P.positive.2.2.1.trans_le (hG.2.2.1 g).1
  have hm := smoothComparisonCellCorrelation_arc_bound hfourier ν block h hh hwidth
    j χA χB z x Z a₁ a₂ v lo hi E H k hlo hhi hZ hk hG
    ∅ 0 S S 0 1 (by norm_num) hS hS (by norm_num) (by norm_num) ha hb
    (fun θ hθ haway => comparisonMultiplier_norm_le_one _ _ _ _ _ _ _ θ hV
      (fun n => ⟨comparisonFourierTest_norm_le _ _ _ _ _ n,
        comparisonFourierTest_norm_le _ _ _ _ _ n⟩))
    (fun c hc => False.elim (Finset.notMem_empty c hc))
  simpa only [Finset.card_empty, Nat.cast_zero, one_mul, zero_mul, add_zero,
    Real.mul_self_sqrt hS] using hm

/-- All frequencies have a fixed-power cell bound. This is independent of
the requested main-range saving and supplies the Mellin tail majorant. -/
theorem eventual_smooth_cell_all_frequency_bound
    (hfourier : FourierArcTask) (hsquare : SmoothEndpointSquareTask)
    (P : Geometry) (m : ℕ) (C τ η lo hi hexp : ℝ)
    (hC : 0 < C) (hlo : 0 < lo) (hhi : lo < hi) (hh : 0 < hexp) :
    ∃ C₂ K : ℝ, 0 ≤ C₂ ∧ 0 < K ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ (G : PrimeGroups) (J Q : ℕ) (ν : Pattern G.graph J P.ell m)
          (block : G.graph.BigGroup → Bool) (j : ℤ × ℤ)
          (χA χB : CharacterIndex Q) (z : SharedDraw ν)
          (E H : Endpoint) (Z a₁ a₂ v : ℝ) (k : ℤ),
          Admissible P x G →
          (∀ side : Bool, ∃ g : G.graph.BigGroup,
            block g = side ∧ (ν.changed g.val).Nonempty) →
          j ∈ comparisonCells ν block (L x ^ (-hexp)) →
          EndpointBound x C τ η E → EndpointBound x C τ η H →
          x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C → |(k : ℝ)| ≤ L x ^ C →
          ‖smoothComparisonCellCorrelation ν block (L x ^ (-hexp)) j χA χB
            x (Z * comparisonJointScale (L x ^ (-hexp)) j) a₁ a₂ v lo hi hlo hhi E H k‖ ≤
            K * L x ^ C₂ := by
  obtain ⟨C₂, K, hC₂, hK, hx⟩ := hsquare P m C τ η lo hi hC hlo hhi
  refine ⟨C₂, K, hC₂, hK, ?_⟩
  filter_upwards [hx, eventual_comparisonY_range P m hexp C (0.01 : ℝ) hh (by norm_num),
    eventual_comparison_shift_margin C lo hlo, eventual_comparison_double_cell_width hexp hh,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
    with x hx hrange hmargin hwidth hL
  change 1 ≤ L x at hL
  intro G J Q ν block j χA χB z E H Z a₁ a₂ v k hG hne hj hE hH hZlo hZhi hk
  let Y := Z * comparisonJointScale (L x ^ (-hexp)) j
  obtain ⟨hZ, hk8⟩ := hmargin Z k hZlo hk
  have hY : 0 < Y := mul_pos hZ (comparisonJointScale_pos _ _)
  have hYr := hrange G J P.ell ν block j Z hG hne hj hZlo hZhi
  norm_num only at hYr
  have hs := (hx G J Q ν block (L x ^ (-hexp)) j.2 χB E Y a₁ v hlo hhi hG hE
    (by norm_num only; exact hYr.1) (by norm_num only; exact hYr.2)).1
  have ht := (hx G J Q ν block (L x ^ (-hexp)) j.1 χA H Y a₂ v hlo hhi hG hH
    (by norm_num only; exact hYr.1) (by norm_num only; exact hYr.2)).2
  have hm := smooth_cell_norm_le_of_square_bounds hfourier ν block _ hwidth.1 hwidth.2
    j χA χB z x Z a₁ a₂ v lo hi (K * Y * L x ^ C₂) E H k hlo hhi hZ hk8 hG
    (by positivity) hs ht
  apply hm.trans_eq
  change Y⁻¹ * (K * Y * L x ^ C₂) = K * L x ^ C₂
  field_simp [hY.ne']

end Erdos821.P5Core
