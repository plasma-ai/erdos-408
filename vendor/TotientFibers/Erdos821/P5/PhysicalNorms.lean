import Erdos821.P5.HarmonicLists
import Erdos821.P5.EndpointLists
import Erdos821.Blueprint.Transference

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem graph_dyad_positive {X : ℝ} (hX : 1 ≤ X) {n : ℤ}
    (hn : n ∈ Blueprint.Graph.dyad X) : 0 < n := by
  have hlo : X ≤ (n : ℝ) := Int.ceil_le.mp (Finset.mem_Ico.mp hn).1
  have hnR : (0 : ℝ) < n := by linarith
  exact_mod_cast hnR

theorem graph_dyad_nat_mem {X : ℝ} (hX : 1 ≤ X) {n : ℤ}
    (hn : n ∈ Blueprint.Graph.dyad X) : n.toNat ∈ Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊ := by
  have hn0 := (graph_dyad_positive hX hn).le
  have hcast : (n.toNat : ℝ) = n := by
    exact_mod_cast Int.toNat_of_nonneg hn0
  have hlo : X ≤ (n : ℝ) := Int.ceil_le.mp (Finset.mem_Ico.mp hn).1
  have hhi : (n : ℝ) < 2 * X := Int.lt_ceil.mp (Finset.mem_Ico.mp hn).2
  exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr (by rwa [hcast]),
    Nat.le_floor (by rw [hcast]; exact hhi.le)⟩

theorem physical_dyad_square_sum (G : PrimeGroups) (M : ℕ) (X : ℝ)
    (a : G.graph.Labels M) (hX : 1 ≤ X) (f : ℕ → ℂ) :
    (∑ n ∈ (Blueprint.Graph.dyad X).filter (fun n => G.graph.physical M n a),
      ‖f n.toNat‖ ^ 2) ≤
      ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter (fun n => listProduct G.graph a ∣ n),
        ‖f n‖ ^ 2 := by
  classical
  let I := (Blueprint.Graph.dyad X).filter (fun n => G.graph.physical M n a)
  have hinj : Set.InjOn Int.toNat (I : Set ℤ) := by
    intro n hn m hm heq
    have hn0 := (graph_dyad_positive hX (Finset.mem_filter.mp hn).1).le
    have hm0 := (graph_dyad_positive hX (Finset.mem_filter.mp hm).1).le
    have h := congrArg (fun v : ℕ => (v : ℤ)) heq
    simpa only [Int.toNat_of_nonneg hn0, Int.toNat_of_nonneg hm0] using h
  have hsub : I.image Int.toNat ⊆
      (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter (fun n => listProduct G.graph a ∣ n) := by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hnd, hnp⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨graph_dyad_nat_mem hX hnd,
      physical_listProduct_dvd G.graph a (graph_dyad_positive hX hnd).le hnp⟩
  calc
    _ = ∑ v ∈ I.image Int.toNat, ‖f v‖ ^ 2 := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v hv hnot => sq_nonneg _)

/-- Endpoint moment bound in the actual graph state measure. The moment constants
do not depend on the number of marks, probes, or groups. -/
theorem physical_endpoint_square_sum :
    ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧
      ∀ (G : PrimeGroups) (x C τ η X : ℝ) (E : Endpoint),
        1 ≤ L x → EndpointBound x C τ η E → 1 ≤ X →
        (∀ g, 0 < mass G g) →
        ∀ (F : Blueprint.Graph.FixedData) (J m : ℕ)
          (A : Blueprint.Graph.Model F G.graph J m),
          (∀ a : A.Labels, (listProduct G.graph a : ℝ) ≤ X) →
          (∑ z ∈ (Blueprint.Graph.dyad X).product Finset.univ,
            A.stateMass z * ‖endpoint G x E z.1.toNat‖ ^ 2) ≤
              K * X * L x ^ (4 * C) * Real.log (4 * X) ^ c := by
  obtain ⟨c, K, hc, hK, hm⟩ := endpoint_square_sum_lists
  refine ⟨c, K, hc, hK, ?_⟩
  intro G x C τ η X E hL hE hX hV F J m A hD
  have hVG (g : G.graph.Group) : 0 < G.graph.V g := by
    simpa only [graph_mass] using hV g
  let s := (Finset.univ : Finset A.Labels).filter (fun a => ∀ g, Function.Injective (a g))
  have hbound := hm G x C τ η X E hL hE hX s
    (fun a => listProduct G.graph a) (fun _ => G.graph.markMass (J + F.ell))
    (fun a ha => ⟨listProduct_pos G.graph a,
      hD a, listProduct_primeFactors G.graph a (Finset.mem_filter.mp ha).2⟩)
    (fun a ha => markMass_nonneg G.graph _ hVG)
    (physical_list_harmonic_mass G.graph _ hVG)
  apply le_trans ?_ hbound
  simp only [Finset.product_eq_sprod]
  rw [Finset.sum_product (Blueprint.Graph.dyad X) (Finset.univ : Finset A.Labels)
    (fun z : ℤ × A.Labels => A.stateMass z * ‖endpoint G x E z.1.toNat‖ ^ 2),
    Finset.sum_comm]
  dsimp only [s]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hinj : ∀ g, Function.Injective (a g)
  · rw [if_pos hinj]
    calc
      _ = G.graph.markMass (J + F.ell) *
          ∑ n ∈ (Blueprint.Graph.dyad X).filter (fun n => G.graph.physical (J + F.ell) n a),
            ‖endpoint G x E n.toNat‖ ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n hn
        simp only [Blueprint.Graph.Model.stateMass]
        split_ifs <;> simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (physical_dyad_square_sum G _ X a hX (endpoint G x E))
        (markMass_nonneg G.graph _ hVG)
  · rw [if_neg hinj]
    have hnot (n : ℤ) : ¬ G.graph.physical (J + F.ell) n a := by
      intro hp
      exact hinj (fun g => (hp g).1)
    simp only [Blueprint.Graph.Model.stateMass, hnot, if_false, zero_mul, Finset.sum_const_zero,
      le_refl]

end Erdos821.P5Core
