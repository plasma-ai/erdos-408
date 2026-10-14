import Erdos821.P5MinorAdapter.FreeTuple
import Erdos821.P5Minor.MinorArcTask

set_option autoImplicit false

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open Filter
set_option maxHeartbeats 0

namespace Erdos821.P5Madapt
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

attribute [local instance] graphPrimeFintype adapterTupleFintype

theorem mu_sum (G : Blueprint.Analytic.PrimeGroups) (g : Fin G.size)
    (hmass : 0 < Blueprint.Analytic.mass G g) :
    (∑ p : Blueprint.Analytic.Label G g, Blueprint.Analytic.mu G g p.val) = 1 := by
  have hne : Blueprint.Analytic.mass G g ≠ 0 := ne_of_gt hmass
  have h1 : (∑ p : Blueprint.Analytic.Label G g, Blueprint.Analytic.mu G g p.val) =
      ∑ p ∈ G.primes g, Blueprint.Analytic.mu G g p :=
    Finset.sum_coe_sort (G.primes g) (fun p => Blueprint.Analytic.mu G g p)
  rw [h1]
  unfold Blueprint.Analytic.mu Blueprint.Analytic.mass
  have h2 : ∀ p ∈ G.primes g,
      1 / ((∑ q ∈ G.primes g, 1 / (q : ℝ)) * (p : ℝ)) =
      (∑ q ∈ G.primes g, 1 / (q : ℝ))⁻¹ * (1 / (p : ℝ)) := by
    intro p _
    ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  exact inv_mul_cancel₀ hne

theorem tupleWeight_sum (G : Blueprint.Analytic.PrimeGroups) (k : Fin G.size → ℕ)
    (hmass : ∀ g, 0 < Blueprint.Analytic.mass G g) :
    (∑ z : Blueprint.Analytic.Tuple G k, Blueprint.Analytic.tupleWeight G k z) = 1 := by
  unfold Blueprint.Analytic.tupleWeight
  trans ∏ g : Fin G.size, ∑ z : Fin (k g) → Blueprint.Analytic.Label G g,
    ∏ j : Fin (k g), Blueprint.Analytic.mu G g (z j).val
  · exact (Fintype.prod_sum (fun (g : Fin G.size)
      (z : Fin (k g) → Blueprint.Analytic.Label G g) =>
      ∏ j : Fin (k g), Blueprint.Analytic.mu G g (z j).val)).symm
  apply Finset.prod_eq_one
  intro g _
  trans ∏ _j : Fin (k g), ∑ p : Blueprint.Analytic.Label G g,
    Blueprint.Analytic.mu G g p.val
  · exact (Fintype.prod_sum (fun (_j : Fin (k g))
      (p : Blueprint.Analytic.Label G g) => Blueprint.Analytic.mu G g p.val)).symm
  · apply Finset.prod_eq_one
    intro _ _
    exact mu_sum G g (hmass g)

theorem tupleWeight_nonneg (G : Blueprint.Analytic.PrimeGroups) (k : Fin G.size → ℕ)
    (z : Blueprint.Analytic.Tuple G k) :
    0 ≤ Blueprint.Analytic.tupleWeight G k z :=
  Erdos821.S34.Proofs.tupleWeight_nonneg (Erdos821.S34Core.coreGroups G) k z

theorem tupleNorm_sq_le_one (G : Blueprint.Analytic.PrimeGroups) (k : Fin G.size → ℕ)
    (hmass : ∀ g, 0 < Blueprint.Analytic.mass G g)
    (f : Blueprint.Analytic.Tuple G k → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) :
    (Blueprint.Analytic.tupleNorm G k f) ^ 2 ≤ 1 := by
  have hsq : (Blueprint.Analytic.tupleNorm G k f) ^ 2 =
      ∑ z, Blueprint.Analytic.tupleWeight G k z * ‖f z‖ ^ 2 :=
    Erdos821.S34.Proofs.tupleNorm_sq (Erdos821.S34Core.coreGroups G) k f
  rw [hsq, ← tupleWeight_sum G k hmass]
  apply Finset.sum_le_sum
  intro z _
  have hfz : ‖f z‖ ^ 2 ≤ 1 := by
    nlinarith [hf z, norm_nonneg (f z)]
  exact mul_le_of_le_one_right (tupleWeight_nonneg G k z) hfz

def cellTupleTest (G' : Blueprint.Analytic.PrimeGroups) (k : Fin G'.size → ℕ)
    (h : ℝ) (j : ℤ) (f : ℕ → ℂ) (z : Blueprint.Analytic.Tuple G' k) : ℂ :=
  if Blueprint.Analytic.cell h (Blueprint.Analytic.product G' k z) = j then
    f (Blueprint.Analytic.product G' k z)
  else 0

theorem cellTupleTest_norm_le (G' : Blueprint.Analytic.PrimeGroups) (k : Fin G'.size → ℕ)
    (h : ℝ) (j : ℤ) (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (z : Blueprint.Analytic.Tuple G' k) :
    ‖cellTupleTest G' k h j f z‖ ≤ 1 := by
  unfold cellTupleTest
  split_ifs
  · exact hf _
  · simp

def cellProductSupport (G' : Blueprint.Analytic.PrimeGroups) (k : Fin G'.size → ℕ)
    (h : ℝ) (j : ℤ) : Finset ℕ :=
  (Finset.univ.image (Blueprint.Analytic.product G' k)).filter
    (fun n => Blueprint.Analytic.cell h n = j)

def cellIntSupport (G' : Blueprint.Analytic.PrimeGroups) (k : Fin G'.size → ℕ)
    (h : ℝ) (j : ℤ) : Finset ℤ :=
  (cellProductSupport G' k h j).map ⟨Nat.cast, Nat.cast_injective⟩

def collapsedIntCoeff (G' : Blueprint.Analytic.PrimeGroups) (k : Fin G'.size → ℕ)
    (h : ℝ) (j : ℤ) (f : ℕ → ℂ) (n : ℤ) : ℂ :=
  Blueprint.Analytic.collapse G' k (cellTupleTest G' k h j f) n.toNat

theorem tuple_product_pos (G' : Blueprint.Analytic.PrimeGroups) (k : Fin G'.size → ℕ)
    (z : Blueprint.Analytic.Tuple G' k) :
    0 < Blueprint.Analytic.product G' k z := by
  unfold Blueprint.Analytic.product
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  exact (G'.prime g (z g i).val (z g i).property).pos

theorem mem_cellProductSupport_pos_and_cell (G' : Blueprint.Analytic.PrimeGroups)
    (k : Fin G'.size → ℕ) (h : ℝ) (j : ℤ) {n : ℕ}
    (hn : n ∈ cellProductSupport G' k h j) :
    0 < n ∧ Blueprint.Analytic.cell h n = j := by
  rcases Finset.mem_filter.mp hn with ⟨himg, hcell⟩
  rcases Finset.mem_image.mp himg with ⟨z, _, rfl⟩
  exact ⟨tuple_product_pos G' k z, hcell⟩

theorem mem_cellIntSupport_bounds (G' : Blueprint.Analytic.PrimeGroups)
    (k : Fin G'.size → ℕ) (h : ℝ) (hh : 0 < h) (hexp : Real.exp h ≤ 2)
    (j : ℤ) {m : ℤ} (hm : m ∈ cellIntSupport G' k h j) :
    Erdos821.P5Core.comparisonCellScale h j ≤ (m : ℝ) ∧
      (m : ℝ) ≤ 2 * Erdos821.P5Core.comparisonCellScale h j := by
  rcases Finset.mem_map.mp hm with ⟨n, hn, rfl⟩
  change ((n : ℤ) : ℝ) ≥ _ ∧ _
  obtain ⟨hpos, hcell⟩ := mem_cellProductSupport_pos_and_cell G' k h j hn
  obtain ⟨hlo, hhi⟩ := Erdos821.P5Core.comparisonCellScale_bounds h hh n hpos
  rw [hcell] at hlo hhi
  simp only [Function.Embedding.coeFn_mk, Int.cast_natCast]
  refine ⟨hlo, hhi.le.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hexp (Erdos821.P5Core.comparisonCellScale_pos h j).le

theorem collapse_sum_eq_tuple_sum (G' : Blueprint.Analytic.PrimeGroups)
    (k : Fin G'.size → ℕ) (h : ℝ) (j : ℤ) (f : ℕ → ℂ) (Φ : ℕ → ℂ) :
    (∑ n ∈ cellProductSupport G' k h j,
        Blueprint.Analytic.collapse G' k (cellTupleTest G' k h j f) n * Φ n) =
      ∑ z : Blueprint.Analytic.Tuple G' k,
        (Blueprint.Analytic.tupleWeight G' k z : ℂ) *
          cellTupleTest G' k h j f z * Φ (Blueprint.Analytic.product G' k z) := by
  unfold Blueprint.Analytic.collapse Blueprint.Analytic.expect
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  have hite : (∑ n ∈ cellProductSupport G' k h j,
      (Blueprint.Analytic.tupleWeight G' k z : ℂ) *
        (if Blueprint.Analytic.product G' k z = n then cellTupleTest G' k h j f z else 0) *
        Φ n) =
      ∑ n ∈ cellProductSupport G' k h j,
        if Blueprint.Analytic.product G' k z = n then
          (Blueprint.Analytic.tupleWeight G' k z : ℂ) * cellTupleTest G' k h j f z * Φ n
        else 0 := by
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> ring
  rw [hite, Finset.sum_ite_eq]
  by_cases hcell : Blueprint.Analytic.cell h (Blueprint.Analytic.product G' k z) = j
  · have hmem : Blueprint.Analytic.product G' k z ∈ cellProductSupport G' k h j := by
      unfold cellProductSupport
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩, hcell⟩
    rw [ite_eq_left hmem]
  · have hzero : cellTupleTest G' k h j f z = 0 := by
      unfold cellTupleTest
      exact ite_eq_right hcell
    rw [hzero]
    simp

theorem comparisonMultiplier_eq_int_bilinear {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool)
    (h : ℝ) (j : ℤ × ℤ) (fA fB : ℕ → ℂ) (k : ℤ) (θ : ℝ)
    (hV : ∀ g : G.Group, 0 < G.V g) :
    let G' := Erdos821.P4Probe.analyticGroups G
    let kA : Fin G'.size → ℕ := sideCounts ν block false
    let kB : Fin G'.size → ℕ := sideCounts ν block true
    Erdos821.P5Core.comparisonMultiplier ν block h j fA fB k θ =
      ∑ n ∈ cellIntSupport G' kA h j.1,
        ∑ v ∈ cellIntSupport G' kB h j.2,
          collapsedIntCoeff G' kA h j.1 fA n *
          collapsedIntCoeff G' kB h j.2 fB v *
          Blueprint.Analytic.e (-(k : ℝ) * θ * n * v) := by
  intro G' kA kB
  have hmap :
      (∑ n ∈ cellIntSupport G' kA h j.1,
        ∑ v ∈ cellIntSupport G' kB h j.2,
          collapsedIntCoeff G' kA h j.1 fA n *
          collapsedIntCoeff G' kB h j.2 fB v *
          Blueprint.Analytic.e (-(k : ℝ) * θ * n * v)) =
      ∑ n ∈ cellProductSupport G' kA h j.1,
        ∑ v ∈ cellProductSupport G' kB h j.2,
          Blueprint.Analytic.collapse G' kA (cellTupleTest G' kA h j.1 fA) n *
          Blueprint.Analytic.collapse G' kB (cellTupleTest G' kB h j.2 fB) v *
          Blueprint.Analytic.e (-(k : ℝ) * θ * (n : ℝ) * (v : ℝ)) := by
    unfold cellIntSupport collapsedIntCoeff
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro v _
    simp only [Function.Embedding.coeFn_mk, Int.toNat_natCast, Int.cast_natCast]
  rw [hmap]
  have hcollapse :
      (∑ n ∈ cellProductSupport G' kA h j.1,
        ∑ v ∈ cellProductSupport G' kB h j.2,
          Blueprint.Analytic.collapse G' kA (cellTupleTest G' kA h j.1 fA) n *
          Blueprint.Analytic.collapse G' kB (cellTupleTest G' kB h j.2 fB) v *
          Blueprint.Analytic.e (-(k : ℝ) * θ * (n : ℝ) * (v : ℝ))) =
      ∑ zA : Blueprint.Analytic.Tuple G' kA,
        ∑ zB : Blueprint.Analytic.Tuple G' kB,
          ((Blueprint.Analytic.tupleWeight G' kA zA *
            Blueprint.Analytic.tupleWeight G' kB zB : ℝ) : ℂ) *
            (cellTupleTest G' kA h j.1 fA zA *
             cellTupleTest G' kB h j.2 fB zB *
             Blueprint.Analytic.e (-(k : ℝ) * θ *
               (Blueprint.Analytic.product G' kA zA : ℝ) *
               (Blueprint.Analytic.product G' kB zB : ℝ))) := by
    have hinner (n : ℕ) :
        (∑ v ∈ cellProductSupport G' kB h j.2,
          Blueprint.Analytic.collapse G' kA (cellTupleTest G' kA h j.1 fA) n *
          Blueprint.Analytic.collapse G' kB (cellTupleTest G' kB h j.2 fB) v *
          Blueprint.Analytic.e (-(k : ℝ) * θ * (n : ℝ) * (v : ℝ))) =
        Blueprint.Analytic.collapse G' kA (cellTupleTest G' kA h j.1 fA) n *
          ∑ zB : Blueprint.Analytic.Tuple G' kB,
            (Blueprint.Analytic.tupleWeight G' kB zB : ℂ) *
              cellTupleTest G' kB h j.2 fB zB *
              Blueprint.Analytic.e (-(k : ℝ) * θ * (n : ℝ) *
                (Blueprint.Analytic.product G' kB zB : ℝ)) := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, collapse_sum_eq_tuple_sum G' kB h j.2 fB]
      simp_rw [mul_assoc]
      rfl
    simp_rw [hinner]
    rw [collapse_sum_eq_tuple_sum G' kA h j.1 fA]
    apply Finset.sum_congr rfl
    intro zA _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro zB _
    push_cast
    ring
  rw [hcollapse]
  let H : Blueprint.Analytic.Tuple G' kA → Blueprint.Analytic.Tuple G' kB → ℂ :=
    fun zA zB =>
      cellTupleTest G' kA h j.1 fA zA *
      cellTupleTest G' kB h j.2 fB zB *
      Blueprint.Analytic.e (-(k : ℝ) * θ *
        (Blueprint.Analytic.product G' kA zA : ℝ) *
        (Blueprint.Analytic.product G' kB zB : ℝ))
  have hpair := freeDraw_pair_expect ν block hV H
  have hpair' :
      (∑ zA : Blueprint.Analytic.Tuple G' kA,
        ∑ zB : Blueprint.Analytic.Tuple G' kB,
          ((Blueprint.Analytic.tupleWeight G' kA zA *
            Blueprint.Analytic.tupleWeight G' kB zB : ℝ) : ℂ) * H zA zB) =
      ∑ u : Erdos821.P5Core.FreeDraw ν,
        (Erdos821.P5Core.freeDrawLaw ν u : ℂ) *
          H (sideTuple ν block false u) (sideTuple ν block true u) :=
    hpair.symm
  change Erdos821.P5Core.comparisonMultiplier ν block h j fA fB k θ =
    ∑ zA : Blueprint.Analytic.Tuple G' kA,
      ∑ zB : Blueprint.Analytic.Tuple G' kB,
        ((Blueprint.Analytic.tupleWeight G' kA zA *
          Blueprint.Analytic.tupleWeight G' kB zB : ℝ) : ℂ) * H zA zB
  rw [hpair']
  unfold Erdos821.P5Core.comparisonMultiplier
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  dsimp [H, cellTupleTest]
  rw [sideTuple_product_eq ν block false u, sideTuple_product_eq ν block true u]
  by_cases hA : Blueprint.Analytic.cell h (Erdos821.P5Core.comparisonFreeProduct ν block false u) = j.1 <;>
    by_cases hB : Blueprint.Analytic.cell h (Erdos821.P5Core.comparisonFreeProduct ν block true u) = j.2 <;>
    (simp [Erdos821.P5Core.comparisonCellPair, Prod.ext_iff, hA, hB]; try ring)

theorem collapsedIntCoeff_sq_sum_le (G' : Blueprint.Analytic.PrimeGroups)
    (k : Fin G'.size → ℕ) (hmass : ∀ g, 0 < Blueprint.Analytic.mass G' g)
    (h : ℝ) (hh : 0 < h) (j : ℤ) (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (M : ℝ) (hM : 0 ≤ M)
    (hatom : ∀ n : ℕ, 0 < n → Blueprint.Analytic.rho G' k n ≤ M / (n : ℝ)) :
    (∑ n ∈ cellIntSupport G' k h j, ‖collapsedIntCoeff G' k h j f n‖ ^ 2) ≤
      M / Erdos821.P5Core.comparisonCellScale h j := by
  have hmap :
      (∑ n ∈ cellIntSupport G' k h j, ‖collapsedIntCoeff G' k h j f n‖ ^ 2) =
        Blueprint.Analytic.sqNorm (cellProductSupport G' k h j)
          (Blueprint.Analytic.collapse G' k (cellTupleTest G' k h j f)) := by
    unfold cellIntSupport collapsedIntCoeff Blueprint.Analytic.sqNorm
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro n _
    simp only [Function.Embedding.coeFn_mk, Int.toNat_natCast]
  rw [hmap]
  let U := Erdos821.P5Core.comparisonCellScale h j
  have hUpos : 0 < U := Erdos821.P5Core.comparisonCellScale_pos h j
  have hR : 0 ≤ M / U := div_nonneg hM hUpos.le
  have hρ : ∀ n ∈ cellProductSupport G' k h j, Blueprint.Analytic.rho G' k n ≤ M / U := by
    intro n hn
    obtain ⟨hpos, hcell⟩ := mem_cellProductSupport_pos_and_cell G' k h j hn
    obtain ⟨hlo, _⟩ := Erdos821.P5Core.comparisonCellScale_bounds h hh n hpos
    rw [hcell] at hlo
    exact (hatom n hpos).trans (div_le_div_of_nonneg_left hM hUpos hlo)
  have hcol := Blueprint.Analytic.collapse_l2_proof G' k (cellTupleTest G' k h j f)
    (cellProductSupport G' k h j) (M / U) hR hρ
  have hnorm : (Blueprint.Analytic.tupleNorm G' k (cellTupleTest G' k h j f)) ^ 2 ≤ 1 :=
    tupleNorm_sq_le_one G' k hmass (cellTupleTest G' k h j f)
      (cellTupleTest_norm_le G' k h j f hf)
  exact hcol.trans (mul_le_of_le_one_right hR hnorm)

theorem eventual_cell_scale_lower_half (P : Geometry) (hexp : ℝ) (hh : 0 < hexp) :
    ∀ᶠ x : ℝ in atTop, L x ^ (P.c / 2) ≤ L x ^ P.c - L x ^ (-hexp) := by
  have hc : 0 < P.c := by
    rcases P.ordered with ⟨_, _, hbc, _⟩
    linarith
  have hc2 : 0 < P.c / 2 := half_pos hc
  have hLc2 := ((tendsto_rpow_atTop hc2).comp Real.tendsto_log_atTop).eventually_ge_atTop (2 : ℝ)
  have hL1 := Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)
  filter_upwards [hLc2, hL1] with x h2 h1
  change 2 ≤ L x ^ (P.c / 2) at h2
  change 1 ≤ L x at h1
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one h1
  have hneg : L x ^ (-hexp) ≤ 1 := by
    rw [Real.rpow_neg hLpos.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow h1 hh.le)
  have hsq : L x ^ P.c = L x ^ (P.c / 2) * L x ^ (P.c / 2) := by
    rw [← Real.rpow_add hLpos]
    congr 1
    ring
  nlinarith

end Erdos821.P5Madapt

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups
open Erdos821.P5Madapt

theorem ComparisonMinorArcAdapterTask_proof : ComparisonMinorArcAdapterTask := by
  intro hminor P m C A hexp hC hA hh
  let Catom : ℝ := P.C₀ * (Real.log (Nat.factorial m) + m * Real.log (max 1 P.vmin⁻¹))
  let C' : ℝ := max C (Catom + 1)
  have hC' : 0 < C' := lt_of_lt_of_le hC (le_max_left _ _)
  let δ : ℝ := P.c / 2
  have hc : 0 < P.c := by
    rcases P.ordered with ⟨_, _, hbc, _⟩
    linarith
  have hδ : 0 < δ := half_pos hc
  obtain ⟨Carc, K, hCarc, hK, hminor_ev⟩ :=
    hminor Blueprint.Analytic.integer_bilinear_proof C' δ A hC' hδ hA
  refine ⟨Carc, K, hCarc, hK, ?_⟩
  filter_upwards [hminor_ev,
    Blueprint.Analytic.product_atom_bound_proof P m,
    eventual_comparisonJointScale_bounds P m hexp (2 : ℝ) hh (by norm_num),
    Erdos821.S34Core.eventually_cell_width hexp hh,
    eventual_cell_scale_lower_half P hexp hh]
    with x hmin hatom hjoint hwidth hhalf
  intro G J ell ν block j fA fB k θ hG hne hj hf hk hkb harc
  let h : ℝ := L x ^ (-hexp)
  let U : ℝ := comparisonCellScale h j.1
  let V : ℝ := comparisonCellScale h j.2
  let G' : Blueprint.Analytic.PrimeGroups := Erdos821.P4Probe.analyticGroups G.graph
  let kA : Fin G'.size → ℕ := sideCounts ν block false
  let kB : Fin G'.size → ℕ := sideCounts ν block true
  let s : Finset ℤ := cellIntSupport G' kA h j.1
  let t : Finset ℤ := cellIntSupport G' kB h j.2
  let a : ℤ → ℂ := collapsedIntCoeff G' kA h j.1 fA
  let b : ℤ → ℂ := collapsedIntCoeff G' kB h j.2 fB
  have hvmin : 0 < P.vmin := P.positive.2.2.1
  have hmass (g : Fin G'.size) : 0 < Blueprint.Analytic.mass G' g := by
    change 0 < Blueprint.Analytic.mass G g
    exact lt_of_lt_of_le hvmin (hG.2.2.1 g).1
  have hV (g : G.graph.Group) : 0 < G.graph.V g := by
    rw [Blueprint.Analytic.graph_mass G g]
    exact hmass g
  rw [comparisonMultiplier_eq_int_bilinear ν block h j fA fB k θ hV]
  obtain ⟨u₀, _, hu₀⟩ := Finset.mem_image.mp hj
  have hcellA : cell h (comparisonFreeProduct ν block false u₀) = j.1 :=
    congrArg Prod.fst hu₀
  have hcellB : cell h (comparisonFreeProduct ν block true u₀) = j.2 :=
    congrArg Prod.snd hu₀
  have hU_lower : Real.exp (L x ^ δ) ≤ U := by
    have hlow := admissible_comparisonCellScale_lower P G x ν block false u₀ h hwidth.1 hG (hne false)
    rw [hcellA] at hlow
    exact (Real.exp_le_exp.mpr hhalf).trans hlow
  have hV_lower : Real.exp (L x ^ δ) ≤ V := by
    have hlow := admissible_comparisonCellScale_lower P G x ν block true u₀ h hwidth.1 hG (hne true)
    rw [hcellB] at hlow
    exact (Real.exp_le_exp.mpr hhalf).trans hlow
  have hUV_upper : U * V ≤ x ^ (2 : ℕ) := by
    have hup : U * V ≤ x ^ (2 : ℝ) := (hjoint.2.2 G J ell ν block j hG hne hj).2
    rwa [← Real.rpow_natCast x 2, Nat.cast_ofNat]
  have hkb' : |(k : ℝ)| ≤ L x ^ C' :=
    hkb.trans (Real.rpow_le_rpow_of_exponent_le hjoint.2.1 (le_max_left _ _))
  have hexp2 : Real.exp h ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hwidth.2
  have hs_bounds : ∀ n ∈ s, U ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * U :=
    fun n hn => mem_cellIntSupport_bounds G' kA h hwidth.1 hexp2 j.1 hn
  have ht_bounds : ∀ n ∈ t, V ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * V :=
    fun n hn => mem_cellIntSupport_bounds G' kB h hwidth.1 hexp2 j.2 hn
  have hG' : Admissible P x G' := by
    dsimp [G']
    rwa [analyticGroups_graph G]
  have hkA : bigSlots G' kA m := sideCounts_bigSlots ν block false (hne false)
  have hkB : bigSlots G' kB m := sideCounts_bigSlots ν block true (hne true)
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hjoint.2.1
  have hM_nonneg : 0 ≤ L x ^ Catom := Real.rpow_nonneg hLpos.le _
  have hM_le : L x ^ Catom ≤ L x ^ C' := by
    apply Real.rpow_le_rpow_of_exponent_le hjoint.2.1
    exact (le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)
  have ha_sq : (∑ n ∈ s, ‖a n‖ ^ 2) ≤ L x ^ C' / U := by
    have h1 := collapsedIntCoeff_sq_sum_le G' kA hmass h hwidth.1 j.1 fA
      (fun n => (hf n).1) (L x ^ Catom) hM_nonneg (hatom G' hG' kA hkA)
    exact h1.trans (div_le_div_of_nonneg_right hM_le (comparisonCellScale_pos h j.1).le)
  have hb_sq : (∑ n ∈ t, ‖b n‖ ^ 2) ≤ L x ^ C' / V := by
    have h1 := collapsedIntCoeff_sq_sum_le G' kB hmass h hwidth.1 j.2 fB
      (fun n => (hf n).2) (L x ^ Catom) hM_nonneg (hatom G' hG' kB hkB)
    exact h1.trans (div_le_div_of_nonneg_right hM_le (comparisonCellScale_pos h j.2).le)
  exact hmin U V θ k s t a b hU_lower hV_lower hUV_upper hk hkb'
    hs_bounds ht_bounds ha_sq hb_sq harc

example : ComparisonMinorArcAdapterTask := @ComparisonMinorArcAdapterTask_proof


end Erdos821.P5Core

namespace Erdos821.P5Madapt

theorem ComparisonMinorArcAdapterTask_proof : Erdos821.P5Core.ComparisonMinorArcAdapterTask :=
  Erdos821.P5Core.ComparisonMinorArcAdapterTask_proof


end Erdos821.P5Madapt
