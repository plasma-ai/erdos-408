import Erdos821.P5.PhysicalKernelSupport

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem stateMass_mul_kernel_norm {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (z z' : A.State) :
    A.stateMass z * ‖A.physicalKernel false z z'‖ =
      A.stateMass z' * ‖A.physicalKernel false z z'‖ := by
  by_cases hz : G.physical (J + F.ell) z.1 z.2
  · by_cases hz' : G.physical (J + F.ell) z'.1 z'.2
    · simp only [Model.stateMass, hz, hz', ite_true]
    · rw [physicalKernel_zero_of_not_physical A false z z' (Or.inr hz'), norm_zero, mul_zero, mul_zero]
  · rw [physicalKernel_zero_of_not_physical A false z z' (Or.inl hz), norm_zero, mul_zero, mul_zero]

theorem physical_normBound_of_neighbor_bounds {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (hV : ∀ g, 0 < G.V g) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ z, (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z z'‖) ≤ R)
    (hcol : ∀ z, (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z' z‖) ≤ R) :
    NormBound A.stateMass (A.physicalKernel false) R := by
  have hrow' (z : A.State) (t : Finset A.State) :
      (∑ z' ∈ t, ‖A.physicalKernel false z z'‖) ≤ R := by
    calc
      _ ≤ ∑ z' ∈ t, ‖A.physicalKernel true z z'‖ := Finset.sum_le_sum
        (fun z' hz' => physicalKernel_norm_le_absolute A (fun g => (hV g).le) z z')
      _ ≤ ∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z z'‖ :=
        norm_sum_le_of_support t _ _ (fun z' hz' => physicalKernel_zero_outside_neighbors A true z z' hz')
      _ ≤ R := hrow z
  have hcol' (z : A.State) (s : Finset A.State) :
      (∑ z' ∈ s, A.stateMass z' * ‖A.physicalKernel false z' z‖) ≤ R * A.stateMass z := by
    simp_rw [stateMass_mul_kernel_norm, ← Finset.mul_sum]
    calc
      _ ≤ A.stateMass z * (∑ z' ∈ s, ‖A.physicalKernel true z' z‖) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum
          (fun z' hz' => physicalKernel_norm_le_absolute A (fun g => (hV g).le) z' z))
          (graph_stateMass_nonneg A hV z)
      _ ≤ A.stateMass z * (∑ z' ∈ A.neighbors z.1, ‖A.physicalKernel true z' z‖) :=
        mul_le_mul_of_nonneg_left (norm_sum_le_of_support s _ _
          (fun z' hz' => physicalKernel_zero_outside_reverse_neighbors A true z' z hz'))
          (graph_stateMass_nonneg A hV z)
      _ ≤ A.stateMass z * R := mul_le_mul_of_nonneg_left (hcol z) (graph_stateMass_nonneg A hV z)
      _ = _ := mul_comm _ _
  have h := S2Core.finite_support_schur A.stateMass (fun _ => 1) (A.physicalKernel false) R R
    (graph_stateMass_nonneg A hV) (fun _ => zero_lt_one) hR hR
    (fun z t => by simpa only [mul_one] using hrow' z t)
    (fun z s => by simpa only [mul_one] using hcol' z s)
  simpa only [Real.sqrt_mul_self hR] using h

theorem pairing_le_of_normBound {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (R X : ℝ) (t : Finset A.State)
    (f : ℤ → ℂ) (g : A.State → ℂ)
    (h : NormBound A.stateMass (A.physicalKernel false) R) :
    ‖A.pairing X t f g‖ ≤ R * A.normOn ((dyad X).product Finset.univ) (fun z => f z.1) *
      A.normOn t g := by
  have hb := h ((dyad X).product Finset.univ) t (fun z => f z.1) g
  simpa only [Model.pairing, Model.normOn, dyad, Finset.product_eq_sprod,
    Finset.sum_product] using hb

end Erdos821.P5Core
