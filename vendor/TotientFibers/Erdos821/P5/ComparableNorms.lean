import Erdos821.P5.ComparableTargets
import Erdos821.P5.EndpointRangeNorms

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T

theorem graph_stateMass_nonneg {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (hV : ∀ g, 0 < G.V g) (z : A.State) :
    0 ≤ A.stateMass z := by
  unfold Model.stateMass
  split_ifs
  · exact markMass_nonneg G (J + F.ell) hV
  · exact le_rfl

theorem graph_normOn_sq {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (hV : ∀ g, 0 < G.V g)
    (s : Finset A.State) (f : A.State → ℂ) :
    A.normOn s f ^ 2 = ∑ z ∈ s, A.stateMass z * ‖f z‖ ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg (fun z hz =>
    mul_nonneg (graph_stateMass_nonneg A hV z) (sq_nonneg _)))

theorem graph_normOn_sq_le_of_subset {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (hV : ∀ g, 0 < G.V g)
    (s t : Finset A.State) (f : A.State → ℂ) (hst : s ⊆ t) :
    A.normOn s f ^ 2 ≤ A.normOn t f ^ 2 := by
  rw [graph_normOn_sq A hV, graph_normOn_sq A hV]
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun z hz hnot =>
    mul_nonneg (graph_stateMass_nonneg A hV z) (sq_nonneg _))

/-- The target interval is the disjoint union of exactly three comparable
dyads, so no extra factor depending on the family or its pattern count occurs. -/
theorem comparable_normOn_sq_eq {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (hV : ∀ g, 0 < G.V g)
    (X : ℝ) (hX : 0 < X) (f : A.State → ℂ) :
    A.normOn ((comparableRoots X).product Finset.univ) f ^ 2 =
      A.normOn ((dyad (X / 2)).product Finset.univ) f ^ 2 +
      A.normOn ((dyad X).product Finset.univ) f ^ 2 +
      A.normOn ((dyad (2 * X)).product Finset.univ) f ^ 2 := by
  have hd₁ : Disjoint (dyad (X / 2)) (dyad X) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have ha := ((mem_graph_dyad (X / 2) n).mp hn).2
    have hb := ((mem_graph_dyad X n).mp hn').1
    linarith
  have hd₂ : Disjoint (dyad (X / 2) ∪ dyad X) (dyad (2 * X)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have hb := ((mem_graph_dyad (2 * X) n).mp hn').1
    rcases Finset.mem_union.mp hn with hn | hn
    · have ha := ((mem_graph_dyad (X / 2) n).mp hn).2
      linarith
    · have ha := ((mem_graph_dyad X n).mp hn).2
      linarith
  simp only [graph_normOn_sq A hV, Finset.product_eq_sprod, Finset.sum_product]
  rw [comparableRoots_eq_three_dyads X hX.le, Finset.sum_union hd₂, Finset.sum_union hd₁]

theorem comparable_normOn_le {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (hV : ∀ g, 0 < G.V g)
    (X R : ℝ) (hX : 0 < X) (hR : 0 ≤ R) (T : Finset ℤ) (f : A.State → ℂ)
    (h₀ : A.normOn ((dyad (X / 2)).product Finset.univ) f ≤ Real.sqrt (X / 2) * R)
    (h₁ : A.normOn ((dyad X).product Finset.univ) f ≤ Real.sqrt X * R)
    (h₂ : A.normOn ((dyad (2 * X)).product Finset.univ) f ≤ Real.sqrt (2 * X) * R) :
    A.normOn ((T ∩ comparableRoots X).product Finset.univ) f ≤ 2 * Real.sqrt X * R := by
  have hs : (T ∩ comparableRoots X).product (Finset.univ : Finset A.Labels) ⊆
      (comparableRoots X).product Finset.univ := by
    intro z hz
    obtain ⟨hn, ha⟩ := Finset.mem_product.mp hz
    exact Finset.mem_product.mpr ⟨(Finset.mem_inter.mp hn).2, ha⟩
  have hsq := graph_normOn_sq_le_of_subset A hV _ _ f hs
  rw [comparable_normOn_sq_eq A hV X hX f] at hsq
  have hsq₀ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h₀ 2
  have hsq₁ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h₁ 2
  have hsq₂ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h₂ 2
  rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ X / 2)] at hsq₀
  rw [mul_pow, Real.sq_sqrt hX.le] at hsq₁
  rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 2 * X)] at hsq₂
  change A.normOn ((dyad (X / 2)).product Finset.univ) f ^ 2 ≤ X / 2 * R ^ 2 at hsq₀
  change A.normOn ((dyad X).product Finset.univ) f ^ 2 ≤ X * R ^ 2 at hsq₁
  change A.normOn ((dyad (2 * X)).product Finset.univ) f ^ 2 ≤ 2 * X * R ^ 2 at hsq₂
  have hnonneg : 0 ≤ A.normOn ((T ∩ comparableRoots X).product Finset.univ) f :=
    Real.sqrt_nonneg _
  have htarget : 0 ≤ 2 * Real.sqrt X * R := by positivity
  have htargetSq : (2 * Real.sqrt X * R) ^ 2 = 4 * X * R ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hX.le]
    ring
  apply (sq_le_sq₀ hnonneg htarget).mp
  rw [htargetSq]
  nlinarith [sq_nonneg R]

end Erdos821.P5Core
