import Erdos821.S34.PrimeProducts

set_option autoImplicit false

open scoped BigOperators Classical

namespace Erdos821.S34Core

noncomputable section

theorem tupleWeight_factorized (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ)
    (z : S34.Core.Tuple G k) :
    S34.Core.tupleWeight G k z =
      (∏ g, (S34.Core.mass G g)⁻¹ ^ k g) * (S34.Core.product G k z : ℝ)⁻¹ := by
  simp only [S34.Core.tupleWeight, S34.Core.mu, one_div, mul_inv_rev,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    S34.Core.product, Nat.cast_prod, Finset.prod_inv_distrib]
  ring

theorem rho_fiber_formula (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ) (n : ℕ) :
    S34.Core.rho G k n = (tupleFiber G k n).card *
      ((∏ g, (S34.Core.mass G g)⁻¹ ^ k g) * (n : ℝ)⁻¹) := by
  change (∑ z ∈ Finset.univ, if S34.Core.product G k z = n then
    S34.Core.tupleWeight G k z else 0) = _
  rw [← Finset.sum_filter]
  calc
    _ = ∑ _ ∈ tupleFiber G k n, (∏ g, (S34.Core.mass G g)⁻¹ ^ k g) * (n : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [tupleWeight_factorized, (Finset.mem_filter.mp hz).2]
    _ = _ := by simp

/-- Finite atom estimate before inserting the logarithmic group bounds. -/
theorem product_atom_finite (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ)
    (n : ℕ) :
    S34.Core.rho G k n ≤
      (∏ g, (Nat.factorial (k g) : ℝ) * (S34.Core.mass G g)⁻¹ ^ k g) / n := by
  have hc : ((tupleFiber G k n).card : ℝ) ≤ ∏ g, (Nat.factorial (k g) : ℝ) := by
    exact_mod_cast tupleFiber_card_le G k n
  have hw : 0 ≤ (∏ g, (S34.Core.mass G g)⁻¹ ^ k g) * (n : ℝ)⁻¹ := by
    apply mul_nonneg
    · apply Finset.prod_nonneg
      intro g _
      exact pow_nonneg (inv_nonneg.mpr (S34.Proofs.mass_nonneg G g)) _
    · positivity
  rw [rho_fiber_formula]
  have h := mul_le_mul_of_nonneg_right hc hw
  simpa only [Finset.prod_mul_distrib, div_eq_mul_inv, mul_assoc] using h

theorem product_atom_group_count (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ)
    (m : ℕ) (S : Finset (Fin G.size)) (v : ℝ) (hv : 0 < v)
    (hmass : ∀ g ∈ S, v ≤ S34.Core.mass G g)
    (hcap : ∀ g, k g ≤ m) (hinactive : ∀ g, g ∉ S → k g = 0) (n : ℕ) :
    S34.Core.rho G k n ≤
      ((Nat.factorial m : ℝ) * (max 1 v⁻¹) ^ m) ^ S.card / n := by
  let cost : Fin G.size → ℝ := fun g =>
    (Nat.factorial (k g) : ℝ) * (S34.Core.mass G g)⁻¹ ^ k g
  have hcost₀ (g : Fin G.size) : 0 ≤ cost g := by
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg
      (inv_nonneg.mpr (S34.Proofs.mass_nonneg G g)) _)
  have hcost (g : Fin G.size) (hg : g ∈ S) :
      cost g ≤ (Nat.factorial m : ℝ) * (max 1 v⁻¹) ^ m := by
    have hfac : (Nat.factorial (k g) : ℝ) ≤ Nat.factorial m := by
      exact_mod_cast Nat.factorial_le (hcap g)
    have hinv : (S34.Core.mass G g)⁻¹ ≤ v⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hv (hmass g hg)
    have hp : (S34.Core.mass G g)⁻¹ ^ k g ≤ (max 1 v⁻¹) ^ m :=
      (pow_le_pow_left₀ (inv_nonneg.mpr (S34.Proofs.mass_nonneg G g))
        (hinv.trans (le_max_right _ _)) (k g)).trans
          (pow_le_pow_right₀ (le_max_left _ _) (hcap g))
    exact mul_le_mul hfac hp
      (pow_nonneg (inv_nonneg.mpr (S34.Proofs.mass_nonneg G g)) _) (Nat.cast_nonneg _)
  have hdrop : (∏ g, cost g) = ∏ g ∈ S, cost g := by
    symm
    apply Finset.prod_subset (Finset.subset_univ S)
    intro g _ hg
    dsimp [cost]
    rw [hinactive g hg]
    simp
  have hprod : (∏ g, cost g) ≤
      ((Nat.factorial m : ℝ) * (max 1 v⁻¹) ^ m) ^ S.card := by
    rw [hdrop]
    calc
      _ ≤ ∏ _ ∈ S, (Nat.factorial m : ℝ) * (max 1 v⁻¹) ^ m :=
        Finset.prod_le_prod₀ (fun g _ => hcost₀ g) hcost
      _ = _ := by simp
  exact (product_atom_finite G k n).trans
    (div_le_div_of_nonneg_right hprod (Nat.cast_nonneg _))

theorem group_cost_log_power (m s : ℕ) (v C L : ℝ) (hv : 0 < v)
    (hL : 1 ≤ L) (hs : (s : ℝ) ≤ C * Real.log L) :
    ((Nat.factorial m : ℝ) * (max 1 v⁻¹) ^ m) ^ s ≤
      L ^ (C * (Real.log (Nat.factorial m) + m * Real.log (max 1 v⁻¹))) := by
  have hfacpos : 0 < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hfac : (1 : ℝ) ≤ Nat.factorial m := by
    exact_mod_cast (show 1 ≤ Nat.factorial m by have := Nat.factorial_pos m; omega)
  have hmax : (1 : ℝ) ≤ max 1 v⁻¹ := le_max_left _ _
  have hpow : (1 : ℝ) ≤ (max 1 v⁻¹) ^ m := one_le_pow₀ hmax
  have hbase : 1 ≤ (Nat.factorial m : ℝ) * (max 1 v⁻¹) ^ m := by
    simpa only [one_mul] using mul_le_mul hfac hpow (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)
  have hbasepos : 0 < (Nat.factorial m : ℝ) * (max 1 v⁻¹) ^ m := lt_of_lt_of_le zero_lt_one hbase
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  calc
    _ = ((Nat.factorial m : ℝ) * (max 1 v⁻¹) ^ m) ^ (s : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ ((Nat.factorial m : ℝ) * (max 1 v⁻¹) ^ m) ^ (C * Real.log L) :=
      Real.rpow_le_rpow_of_exponent_le hbase hs
    _ = _ := by
      rw [Real.rpow_def_of_pos hbasepos, Real.rpow_def_of_pos hLpos,
        Real.log_mul (ne_of_gt hfacpos) (by positivity), Real.log_pow]
      congr 1
      ring

end
end Erdos821.S34Core
