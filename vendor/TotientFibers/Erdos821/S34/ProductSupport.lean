import Erdos821.S34.ProductLaws
import Erdos821.S34.OwnedLeafProofs

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

theorem tuple_product_pos (G : PrimeGroups) (k : Fin G.size → ℕ) (z : Tuple G k) :
    0 < product G k z := by
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro j _
  exact (G.prime g (z g j).val (z g j).property).pos

theorem log_tuple_product (G : PrimeGroups) (k : Fin G.size → ℕ) (z : Tuple G k) :
    Real.log (product G k z) = ∑ g, ∑ j, Real.log (z g j).val := by
  simp only [product, Nat.cast_prod]
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro g _
    rw [Real.log_prod]
    intro j _
    exact_mod_cast (G.prime g (z g j).val (z g j).property).ne_zero
  · intro g _
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact_mod_cast (G.prime g (z g j).val (z g j).property).ne_zero

theorem slot_count_bound (G : PrimeGroups) (k : Fin G.size → ℕ) (m : ℕ)
    (hk : bigSlots G k m) : (∑ g, k g) ≤ m * G.big.card := by
  calc
    _ = ∑ g ∈ G.big, k g := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro g _ hg
      apply (hk.2 g).2
      simpa [PrimeGroups.big] using hg
    _ ≤ ∑ _g ∈ G.big, m := Finset.sum_le_sum fun g _ => (hk.2 g).1
    _ = _ := by simp [mul_comm]

theorem log_product_bounds (P : Geometry) (x : ℝ) (G : PrimeGroups)
    (hL : 0 ≤ L x) (hG : Admissible P x G) (k : Fin G.size → ℕ) (m : ℕ)
    (hk : bigSlots G k m) (z : Tuple G k) :
    L x ^ P.c ≤ Real.log (product G k z) ∧
      Real.log (product G k z) ≤ (m : ℝ) * P.C₀ * T x * L x ^ P.d := by
  have hlabel (g : Fin G.size) (j : Fin (k g)) :
      L x ^ P.c ≤ Real.log (z g j).val ∧ Real.log (z g j).val ≤ L x ^ P.d := by
    have hbig : g ∉ G.small := by
      intro hg
      have hz := (hk.2 g).2 hg
      have hj := j.isLt
      omega
    have hp := hG.2.2.2.1 g (z g j).val (z g j).property
    rw [if_neg hbig] at hp
    have hpos : (0 : ℝ) < (z g j).val := by
      exact_mod_cast (G.prime g (z g j).val (z g j).property).pos
    constructor
    · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hp.1
    · simpa only [Real.log_exp] using Real.log_le_log hpos hp.2
  rw [log_tuple_product]
  have hnonneg (g : Fin G.size) (j : Fin (k g)) : 0 ≤ Real.log (z g j).val :=
    Real.log_natCast_nonneg _
  constructor
  · have hex : ∃ g, 0 < k g := by
      by_contra! h
      have hz : (∑ g, k g) = 0 := Finset.sum_eq_zero fun g _ => Nat.eq_zero_of_le_zero (h g)
      have hspos := hk.1
      omega
    obtain ⟨g, hg⟩ := hex
    let j : Fin (k g) := ⟨0, hg⟩
    exact (hlabel g j).1.trans ((Finset.single_le_sum (fun j _ => hnonneg g j)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun g => ∑ j, Real.log (z g j).val)
        (fun g _ => Finset.sum_nonneg fun j _ => hnonneg g j) (Finset.mem_univ g)))
  · calc
      _ ≤ ∑ g, ∑ _j : Fin (k g), L x ^ P.d :=
        Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun j _ => (hlabel g j).2
      _ = (∑ g, (k g : ℝ)) * L x ^ P.d := by simp [← Finset.sum_mul]
      _ ≤ ((m : ℝ) * (G.big.card : ℝ)) * L x ^ P.d := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL _)
        exact_mod_cast slot_count_bound G k m hk
      _ ≤ _ := by
        have hb := hG.2.1.2
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have hd : 0 ≤ L x ^ P.d := Real.rpow_nonneg hL _
        nlinarith [mul_le_mul_of_nonneg_left hb hm,
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hm) hd]

end
end Erdos821.S34Core
