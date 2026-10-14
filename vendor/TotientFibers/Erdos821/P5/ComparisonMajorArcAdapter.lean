import Erdos821.P5.ComparisonEnergyExponents
import Erdos821.P5.ComparisonArcScales
import Erdos821.P5.SmoothComparisonParameters

noncomputable section
open scoped BigOperators Classical
open Filter MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem rationalArcCenters_witness (R : ℕ) (c : ℝ) (hc : c ∈ rationalArcCenters R) :
    ∃ (r : ℕ) (u : ℤ), 1 ≤ r ∧ r ≤ R ∧ c = (u : ℝ) / r := by
  obtain ⟨r, hr, hc⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hc
  exact ⟨r, u, (Finset.mem_Icc.mp hr).1, (Finset.mem_Icc.mp hr).2, heq.symm⟩

/-- Applies the marked endpoint task to all actual comparison major arcs.
The exponent controlling the endpoint, frequency and rational denominator
is fixed before the discrepancy exponent and the lift depth. -/
theorem eventual_comparison_major_arc_energy
    (henergy : MarkedEndpointEnergyTask)
    (P : Geometry) (m : ℕ) (C Cv τ η lo hi hexp Carc A : ℝ)
    (hC : 0 < C) (hlo : 0 < lo) (hhi : lo < hi)
    (hh : 0 < hexp) (hCarc : 0 < Carc) (hA : 0 < A) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ (G : PrimeGroups) (J Q : ℕ) (ν : Pattern G.graph J P.ell m)
          (block : G.graph.BigGroup → Bool) (j : ℤ × ℤ) (χ : CharacterIndex Q)
          (E : Endpoint) (Z a v : ℝ),
          Admissible P x G →
          (∀ side : Bool, ∃ g : G.graph.BigGroup,
            block g = side ∧ (ν.changed g.val).Nonempty) →
          j ∈ comparisonCells ν block (L x ^ (-hexp)) →
          EndpointBound x C τ η E →
          x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C →
          |a| ≤ L x ^ C → |v| ≤ L x ^ Cv → discrepancy x B E.alpha →
          ∀ c ∈ rationalArcCenters ⌊L x ^ Carc⌋₊,
            let Y := Z * comparisonJointScale (L x ^ (-hexp)) j
            let Δ := L x ^ Carc / comparisonJointScale (L x ^ (-hexp)) j
            (∫ θ in (c - Δ)..(c + Δ),
              ‖localAdditivePolynomial (comparisonCommonRoots lo hi Y)
                (comparisonSmoothSource G x Y a v lo hi hlo hhi E
                  (comparisonMarkedEndpoint ν block true (L x ^ (-hexp)) j.2 χ)) θ‖ ^ 2) ≤
              K * Y * L x ^ (-A) := by
  let Ce := max (max C Cv + 1) Carc
  have hCe : 0 < Ce := (by linarith [le_max_left C Cv] : 0 < max C Cv + 1).trans_le
    (le_max_left _ _)
  have hCCe : C ≤ Ce := (le_max_left C Cv).trans
    ((by linarith : max C Cv ≤ max C Cv + 1).trans (le_max_left _ _))
  obtain ⟨bounds, hb, hcut⟩ := comparisonHarmonicSizeCutoff_bounds lo hi hlo hhi
  obtain ⟨B, K, hB, hK, he⟩ := henergy P (P.ell + m) Ce A τ η (lo / 2)
    (2 * hi + lo) bounds hCe hA (by positivity) (by linarith) hb
  refine ⟨B, K, hB, hK, ?_⟩
  filter_upwards [he, eventual_comparison_arc_scales P m hexp Carc hh hCarc,
    eventual_comparisonY_range P m hexp C (0.01 : ℝ) hh (by norm_num),
    eventual_comparison_small_mark P,
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)] with x he hscale hYrange hsmall hL2
  change 2 ≤ L x at hL2
  have hL : 1 ≤ L x := by linarith
  have hLp : 0 < L x := by linarith
  intro G J Q ν block j χ E Z a v hG hne hj hE hZlo hZhi ha hv hdisc c hc
  dsimp only
  let H' := comparisonJointScale (L x ^ (-hexp)) j
  let Y := Z * H'
  let H := H' / L x ^ Carc
  have hZ : 0 < Z := (mul_pos (by linarith [hscale.1] : 0 < x)
    (Real.rpow_pos_of_pos hLp _)).trans_le hZlo
  have hY : 0 < Y := mul_pos hZ (comparisonJointScale_pos _ _)
  have hranges := hYrange G J P.ell ν block j Z hG hne hj hZlo hZhi
  norm_num only at hranges
  have hsc := hscale.2.2 G J P.ell ν block j hG hne hj
  obtain ⟨r, u, hr, hrR, rfl⟩ := rationalArcCenters_witness _ c hc
  have hrRcast : (r : ℝ) ≤ (⌊L x ^ Carc⌋₊ : ℝ) := by exact_mod_cast hrR
  have hrpow : (r : ℝ) ≤ L x ^ Carc := hrRcast.trans
    (Nat.floor_le (Real.rpow_nonneg hLp.le _))
  have hrCe := hrpow.trans (Real.rpow_le_rpow_of_exponent_le hL (le_max_right _ _ : Carc ≤ Ce))
  have hvCe := (comparison_energy_frequency_bound x C Cv a v hL2 ha hv).trans
    (Real.rpow_le_rpow_of_exponent_le hL (le_max_left _ _ : max C Cv + 1 ≤ Ce))
  have he' := he G E Y H (-a - v) ν.t
    (comparisonEnergyMark ν block true (L x ^ (-hexp)) j.2 χ)
    (comparisonHarmonicSizeCutoff lo hi hlo hhi) r u hG
    (comparison_endpoint_bound_enlarge x C Ce τ η E hL hCCe hE)
    (by norm_num only; exact hranges.1) (by norm_num only; exact hranges.2)
    hsc.2.2.1 hsc.2.2.2.1 hvCe
    (comparisonEnergyMark_slot_bound ν) (hsmall G J m ν hG)
    (comparisonEnergyMark_norm_le ν block true _ _ χ)
    (comparisonEnergyMark_big_ext ν block true _ _ χ)
    (hcut x Ce hL hCe.le) hr hrCe hdisc
  rw [comparison_source_arc_energy_eq_markedEnergy ν block true (L x ^ (-hexp))
    j.2 χ x Y a v lo hi ((u : ℝ) / r) (L x ^ Carc / H') hlo hhi hY E]
  simpa only [H, neg_div, one_div_div, comparisonCommonRoots] using he'

end Erdos821.P5Core
