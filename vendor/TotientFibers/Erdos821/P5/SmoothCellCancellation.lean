import Erdos821.P5.ComparisonMajorArcAdapter
import Erdos821.P5.ComparisonArcNumerics
import Erdos821.P5.SmoothCellSquareBound
import Erdos821.P5.ComparisonFiniteMinorArcs
import Erdos821.P5Minor.MinorArcTask

noncomputable section
open scoped BigOperators Classical
open Filter MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- Complete cancellation on one actual smooth comparison cell, conditional
only on the assigned Fourier, minor adapter, marked energy and square tasks.
Square costs precede the minor saving and Carc; energy and discrepancy are
chosen afterwards. No bound on the number of patterns is used. -/
theorem eventual_smooth_comparison_cell_cancellation
    (hfourier : FourierArcTask) (hadapter : ComparisonMinorArcAdapterTask)
    (henergy : MarkedEndpointEnergyTask) (hsquare : SmoothEndpointSquareTask)
    (P : Geometry) (m : ℕ) (D C Cv τ η lo hi hexp : ℝ)
    (hD : 0 < D) (hC : 0 < C) (hlo : 0 < lo) (hhi : lo < hi) (hh : 0 < hexp) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧
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
          k ≠ 0 → |(k : ℝ)| ≤ L x ^ C →
          x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C →
          |a₁| ≤ L x ^ C → |v| ≤ L x ^ Cv → discrepancy x B E.alpha →
          ‖smoothComparisonCellCorrelation ν block (L x ^ (-hexp)) j χA χB
            x (Z * comparisonJointScale (L x ^ (-hexp)) j) a₁ a₂ v lo hi hlo hhi E H k‖ ≤
            K * L x ^ (-D) := by
  obtain ⟨C₂, Ks, hC₂, hKs, hsq⟩ := hsquare P m C τ η lo hi hC hlo hhi
  obtain ⟨Carc, Km, hCarc, hKm, hminor⟩ := eventual_comparison_finite_minor_arcs
    hadapter minorArcTask_proof P m C (D + C₂) hexp hC (by linarith) hh
  let Ae := 2 * D + 4 * Carc + C₂
  have hAe : 0 < Ae := by dsimp only [Ae]; positivity
  obtain ⟨B, Ke, hB, hKe, hmajor⟩ := eventual_comparison_major_arc_energy henergy
    P m C Cv τ η lo hi hexp Carc Ae hC hlo hhi hh hCarc hAe
  refine ⟨B, Km * Ks + 4 * Real.sqrt (Ke * Ks), hB, by positivity, ?_⟩
  filter_upwards [hsq, hminor, hmajor,
    eventual_comparison_arc_scales P m hexp Carc hh hCarc,
    eventual_comparisonY_range P m hexp C (0.01 : ℝ) hh (by norm_num),
    eventual_comparison_double_cell_width hexp hh,
    eventual_comparison_shift_margin C lo hlo] with x hsq hminor hmajor hscale hYr hwidth hmargin
  intro G J Q ν block j χA χB z E H Z a₁ a₂ v k hG hne hj hE hH hk hkb hZlo hZhi ha hv hdisc
  let Y := Z * comparisonJointScale (L x ^ (-hexp)) j
  let centers := rationalArcCenters ⌊L x ^ Carc⌋₊
  let Δ := L x ^ Carc / comparisonJointScale (L x ^ (-hexp)) j
  obtain ⟨hZ, hk8⟩ := hmargin Z k hZlo hkb
  have hY : 0 < Y := mul_pos hZ (comparisonJointScale_pos _ _)
  have hL : 0 < L x := by linarith [hscale.2.1]
  have hsc := hscale.2.2 G J P.ell ν block j hG hne hj
  have hr := hYr G J P.ell ν block j Z hG hne hj hZlo hZhi
  norm_num only at hr
  have hsa := (hsq G J Q ν block (L x ^ (-hexp)) j.2 χB E Y a₁ v hlo hhi hG hE
    (by norm_num only; exact hr.1) (by norm_num only; exact hr.2)).1
  have hsb := (hsq G J Q ν block (L x ^ (-hexp)) j.1 χA H Y a₂ v hlo hhi hG hH
    (by norm_num only; exact hr.1) (by norm_num only; exact hr.2)).2
  have hbound := smoothComparisonCellCorrelation_arc_bound hfourier ν block _ hwidth.1 hwidth.2
    j χA χB z x Z a₁ a₂ v lo hi E H k hlo hhi hZ hk8 hG centers Δ
    (Ks * Y * L x ^ C₂) (Ks * Y * L x ^ C₂)
    (Ke * Y * L x ^ (-Ae)) (Km * L x ^ (-(D + C₂)))
    hsc.1.le (by positivity) (by positivity) (by positivity) (by positivity) hsa hsb
    (fun θ hθ haway => hminor G J P.ell Q ν block j χA χB a₁ a₂ v k θ
      hG hne hj hk hkb hθ haway)
    (fun c hc => hmajor G J Q ν block j χB E Z a₁ v hG hne hj hE hZlo hZhi ha hv hdisc c hc)
  exact hbound.trans (comparison_arc_log_bound Y (L x) D C₂ Carc Ks Ke Km
    (centers.card : ℝ) hY hL hKs.le hKe.le hsc.2.2.2.2)

end Erdos821.P5Core
