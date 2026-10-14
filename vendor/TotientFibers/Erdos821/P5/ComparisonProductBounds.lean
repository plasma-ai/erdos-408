import Erdos821.P5.ComparisonFactors
import Erdos821.P5.ListScales

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem comparisonFreeProduct_pos {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (u : FreeDraw ν) : 0 < comparisonFreeProduct ν block side u := by
  apply Finset.prod_pos
  intro g hg
  apply Finset.prod_pos
  intro i hi
  split_ifs
  · exact (G.prime g.val _ (u _).property).pos
  · exact Nat.zero_lt_one

theorem comparisonFreeProduct_log_le {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (u : FreeDraw ν) (R : ℝ) (hR : 0 ≤ R)
    (hp : ∀ g : G.BigGroup, ∀ i : {i : Fin J // i ∈ ν.changed g.val},
      Real.log ((u ⟨g.val, i⟩).val : ℝ) ≤ R) :
    Real.log (comparisonFreeProduct ν block side u) ≤
      (m : ℝ) * Fintype.card G.BigGroup * R := by
  let f (g : G.BigGroup) (i : Fin J) : ℕ :=
    if hi : block g = side ∧ i ∈ ν.changed g.val then
      (u ⟨g.val, ⟨i, hi.2⟩⟩).val else 1
  have hf (g : G.BigGroup) (i : Fin J) : 0 < (f g i : ℝ) := by
    dsimp only [f]
    split_ifs
    · exact_mod_cast (G.prime g.val _ (u _).property).pos
    · norm_num
  change Real.log ((∏ g : G.BigGroup, ∏ i : Fin J, f g i : ℕ) : ℝ) ≤ _
  simp only [Nat.cast_prod]
  rw [Real.log_prod (fun g hg => (Finset.prod_pos (fun i hi => hf g i)).ne')]
  simp_rw [Real.log_prod (fun i hi => (hf _ i).ne')]
  have hterm (g : G.BigGroup) (i : Fin J) :
      Real.log (f g i : ℝ) ≤ if i ∈ ν.changed g.val then R else 0 := by
    dsimp only [f]
    by_cases hsel : block g = side ∧ i ∈ ν.changed g.val
    · rw [dite_eq_left hsel, ite_eq_left hsel.2]
      exact hp g ⟨i, hsel.2⟩
    · rw [dite_eq_right hsel, Nat.cast_one, Real.log_one]
      split_ifs
      · exact hR
      · rfl
  have hg (g : G.BigGroup) : (∑ i : Fin J, Real.log (f g i : ℝ)) ≤ (m : ℝ) * R := by
    calc
      _ ≤ ∑ i : Fin J, if i ∈ ν.changed g.val then R else 0 :=
        Finset.sum_le_sum (fun i hi => hterm g i)
      _ = ((ν.changed g.val).card : ℝ) * R := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast ν.bound g.val) hR
  calc
    _ ≤ ∑ _g : G.BigGroup, (m : ℝ) * R := Finset.sum_le_sum (fun g h => hg g)
    _ = _ := by simp; ring

theorem admissible_comparisonFreeProduct_log_le (P : Geometry) (G : PrimeGroups) (x : ℝ)
    {J ell m : ℕ} (ν : Pattern G.graph J ell m) (block : G.graph.BigGroup → Bool)
    (side : Bool) (u : FreeDraw ν) (hL : 1 ≤ L x) (hG : Admissible P x G) :
    Real.log (comparisonFreeProduct ν block side u) ≤
      2 * (m : ℝ) * P.C₀ * T x * L x ^ P.d := by
  have hLpos : 0 < L x := by linarith
  have hb := comparisonFreeProduct_log_le ν block side u (L x ^ P.d)
    (Real.rpow_nonneg hLpos.le _) (by
      intro g i
      have hpos : (0 : ℝ) < (u ⟨g.val, i⟩).val := by
        exact_mod_cast (G.prime g.val _ (u _).property).pos
      exact (Real.log_le_log hpos
        (admissible_prime_upper P G x hL hG g.val _ (u _).property)).trans_eq
          (Real.log_exp _))
  have hcard : (Fintype.card G.graph.BigGroup : ℝ) ≤ 2 * P.C₀ * T x := by
    have hc : Fintype.card G.graph.BigGroup ≤ G.size := by
      simpa only [Fintype.card_fin] using
        Fintype.card_subtype_le (fun g : Fin G.size => G.graph.big g = true)
    exact (Nat.cast_le.mpr hc).trans (admissible_count_le P G x hG)
  calc
    _ ≤ (m : ℝ) * Fintype.card G.graph.BigGroup * L x ^ P.d := hb
    _ ≤ (m : ℝ) * (2 * P.C₀ * T x) * L x ^ P.d :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg m))
        (Real.rpow_nonneg hLpos.le _)
    _ = _ := by ring

theorem comparisonFreeProduct_selected_prime_dvd {G : Blueprint.Graph.PrimeGroups}
    {J ell m : ℕ} (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (u : FreeDraw ν) (g : G.BigGroup) (i : Fin J)
    (hg : block g = side) (hi : i ∈ ν.changed g.val) :
    (u ⟨g.val, ⟨i, hi⟩⟩).val ∣ comparisonFreeProduct ν block side u := by
  let f (g : G.BigGroup) (i : Fin J) : ℕ :=
    if hc : block g = side ∧ i ∈ ν.changed g.val then
      (u ⟨g.val, ⟨i, hc.2⟩⟩).val else 1
  have hinner := Finset.dvd_prod_of_mem (fun j : Fin J => f g j) (Finset.mem_univ i)
  have houter := Finset.dvd_prod_of_mem (fun g : G.BigGroup => ∏ j : Fin J, f g j)
    (Finset.mem_univ g)
  have he : f g i = (u ⟨g.val, ⟨i, hi⟩⟩).val := by simp [f, hg, hi]
  rw [he] at hinner
  exact hinner.trans houter

theorem admissible_comparisonFreeProduct_lower (P : Geometry) (G : PrimeGroups) (x : ℝ)
    {J ell m : ℕ} (ν : Pattern G.graph J ell m) (block : G.graph.BigGroup → Bool)
    (side : Bool) (u : FreeDraw ν) (hG : Admissible P x G)
    (hne : ∃ g : G.graph.BigGroup, block g = side ∧ (ν.changed g.val).Nonempty) :
    Real.exp (L x ^ P.c) ≤ (comparisonFreeProduct ν block side u : ℝ) := by
  obtain ⟨g, hg, i, hi⟩ := hne
  have hsmall : g.val ∉ G.small := by
    simpa only [PrimeGroups.graph, decide_eq_true_eq] using g.property
  have hp := hG.2.2.2.1 g.val _ (u ⟨g.val, ⟨i, hi⟩⟩).property
  simp only [hsmall, ite_false] at hp
  have hdiv := comparisonFreeProduct_selected_prime_dvd ν block side u g i hg hi
  exact hp.1.trans (Nat.cast_le.mpr
    (Nat.le_of_dvd (comparisonFreeProduct_pos ν block side u) hdiv))

end Erdos821.P5Core
