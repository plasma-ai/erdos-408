import Erdos408.Extraction.Allocation.Failure.Coins
import Erdos408.Extraction.Allocation.Failure.Sieve

/-!
# The `u`-side comparison

For one free factor `e` (the first core factor of the product `v = e c`, with
`c = r d` fixed), the expanded generating function
`Ψ(u) = ∏_{g ∈ F} (1 - α_g ℓ(ω_g(u)))` at `u = e c - 1` is summed against the
rough weight `w(e)`. Each term of the expansion is a residue condition
`e c ≡ 1 (mod p)`, `p ∈ U`, so the relative residue estimate gives
`S_U = S_∅ π^U + O(δ S_∅ π^U + E)` with the independent model `π_p = 1/(p - 1)`
for `p ∤ c` and `π_p = 0` for `p ∣ c`. Summing the expansion:

`∑ w Ψ ≤ S_∅ ∏_g (1 - α_g (μ_g - e₂,g)) + δ S_∅ ∏_g (1 + |α_g| (μ_g + e₂,g)) + E ∏_g #K_g`,

with `μ_g = ∑_{p ∈ g} π_p` and `e₂,g = ∑_{|K| = 2} π^K`.
-/

namespace Erdos408

open Finset

noncomputable section

/-- `∑_{K ⊆ g, |K| ≤ 2} f(K) = f(∅) + ∑_{p ∈ g} f({p}) + ∑_{|K| = 2} f(K)`. -/
lemma sum_lowSubsets_eq_add (g : Finset ℕ) (f : Finset ℕ → ℝ) :
    ∑ K ∈ lowSubsets g, f K = f ∅ + ∑ p ∈ g, f {p} + ∑ K ∈ g.powersetCard 2, f K := by
  have hsplit : lowSubsets g = (g.powersetCard 0 ∪ g.powersetCard 1) ∪ g.powersetCard 2 := by
    ext K
    simp only [lowSubsets, mem_filter, mem_powerset, mem_union, mem_powersetCard]
    by_cases h : K ⊆ g
    · simp only [h, true_and]
      omega
    · simp [h]
  have hd1 : Disjoint (g.powersetCard 0) (g.powersetCard 1) := by
    rw [disjoint_left]
    intro K h1 h2
    have := (mem_powersetCard.1 h1).2
    have := (mem_powersetCard.1 h2).2
    omega
  have hd2 : Disjoint (g.powersetCard 0 ∪ g.powersetCard 1) (g.powersetCard 2) := by
    rw [disjoint_left]
    intro K h1 h2
    have := (mem_powersetCard.1 h2).2
    rcases mem_union.1 h1 with h | h <;> have := (mem_powersetCard.1 h).2 <;> omega
  rw [hsplit, sum_union hd2, sum_union hd1, powersetCard_zero, sum_singleton, powersetCard_one,
    sum_map]
  rfl

/-- The model weight `π_p = [p ∤ c] / (p - 1)`. -/
def modelWeight (c p : ℕ) : ℝ :=
  if p ∣ c then 0 else 1 / ((p : ℝ) - 1)

/-- The model weights are nonnegative. -/
lemma modelWeight_nonneg {c p : ℕ} (hp : p.Prime) : 0 ≤ modelWeight c p := by
  unfold modelWeight
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  split_ifs
  · exact le_rfl
  · exact one_div_nonneg.2 (by linarith)

/-- The model sum over the expansion of one group. -/
lemma sum_lowSubsets_lowCoeff_mul_prod (g : Finset ℕ) (α : ℝ) (π : ℕ → ℝ) :
    ∑ K ∈ lowSubsets g, lowCoeff α K.card * ∏ p ∈ K, π p =
      1 - α * (∑ p ∈ g, π p - ∑ K ∈ g.powersetCard 2, ∏ p ∈ K, π p) := by
  rw [sum_lowSubsets_eq_add]
  have h2 : ∀ K ∈ g.powersetCard 2, lowCoeff α K.card * ∏ p ∈ K, π p = α * ∏ p ∈ K, π p := by
    intro K hK
    rw [(mem_powersetCard.1 hK).2]
    simp [lowCoeff]
  rw [sum_congr rfl h2, ← mul_sum]
  simp [lowCoeff, ← mul_sum]
  ring

/-- The absolute model sum over the expansion of one group. -/
lemma sum_lowSubsets_abs_lowCoeff_mul_prod (g : Finset ℕ) (α : ℝ) (π : ℕ → ℝ) :
    ∑ K ∈ lowSubsets g, |lowCoeff α K.card| * ∏ p ∈ K, π p =
      1 + |α| * (∑ p ∈ g, π p + ∑ K ∈ g.powersetCard 2, ∏ p ∈ K, π p) := by
  rw [sum_lowSubsets_eq_add]
  have h2 : ∀ K ∈ g.powersetCard 2, |lowCoeff α K.card| * ∏ p ∈ K, π p =
      |α| * ∏ p ∈ K, π p := by
    intro K hK
    rw [(mem_powersetCard.1 hK).2]
    simp [lowCoeff]
  rw [sum_congr rfl h2, ← mul_sum]
  simp [lowCoeff, ← mul_sum, abs_neg]
  ring

/-- `|c_α(k)| ≤ 1` for `|α| ≤ 1`. -/
lemma abs_lowCoeff_le {α : ℝ} (hα : |α| ≤ 1) (k : ℕ) : |lowCoeff α k| ≤ 1 := by
  unfold lowCoeff
  split_ifs <;> simp [abs_neg, hα]

/-- The `u`-side comparison for one free factor. -/
theorem sum_rough_mul_prod_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (F : Finset (Finset ℕ))
    (hFS : ∀ g ∈ F, g ⊆ S) (hdisj : (F : Set (Finset ℕ)).PairwiseDisjoint id)
    (α : Finset ℕ → ℝ) (hα : ∀ g ∈ F, |α g| ≤ 1) {c : ℕ} (hc : 1 ≤ c) {A B : ℕ} (hA : 1 ≤ A)
    {w : ℕ → ℝ} (hw0 : ∀ e, 0 ≤ w e) {δ E : ℝ} (hE : 0 ≤ E)
    (hstar : ∀ U ⊆ S, (∀ p ∈ U, ¬ p ∣ c) →
      |∑ e ∈ Ioc A B, (if (∀ p ∈ S, ¬ p ∣ e) ∧ ∀ p ∈ U, e * c ≡ 1 [MOD p] then w e else 0) -
          (∑ e ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ e then w e else 0)) / ∏ p ∈ U, ((p : ℝ) - 1)| ≤
        δ * ((∑ e ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ e then w e else 0)) /
          ∏ p ∈ U, ((p : ℝ) - 1)) + E) :
    ∑ e ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ e then w e else 0) *
        ∏ g ∈ F, (1 - α g * ell (primeCount g (e * c - 1))) ≤
      (∑ e ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ e then w e else 0)) *
          ∏ g ∈ F, (1 - α g * (∑ p ∈ g, modelWeight c p -
            ∑ K ∈ g.powersetCard 2, ∏ p ∈ K, modelWeight c p)) +
        δ * (∑ e ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ e then w e else 0)) *
          ∏ g ∈ F, (1 + |α g| * (∑ p ∈ g, modelWeight c p +
            ∑ K ∈ g.powersetCard 2, ∏ p ∈ K, modelWeight c p)) +
        E * ∏ g ∈ F, ((lowSubsets g).card : ℝ) := by
  classical
  set S0 := ∑ e ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ e then w e else 0) with hS0
  have hS00 : 0 ≤ S0 := sum_nonneg fun e _ => by split_ifs <;> simp [hw0 e]
  clear_value S0
  set SU : Finset ℕ → ℝ := fun U =>
    ∑ e ∈ Ioc A B, (if (∀ p ∈ S, ¬ p ∣ e) ∧ ∀ p ∈ U, e * c ≡ 1 [MOD p] then w e else 0)
  set π : ℕ → ℝ := fun p => modelWeight c p
  set ι := Fintype.piFinset (fun g : F => lowSubsets g.1)
  have hUS : ∀ κ ∈ ι, (Finset.univ : Finset F).biUnion κ ⊆ S := by
    intro κ hκ p hp
    obtain ⟨g, -, hpg⟩ := mem_biUnion.1 hp
    have := Fintype.mem_piFinset.1 hκ g
    exact hFS g.1 g.2 (mem_powerset.1 (mem_filter.1 this).1 hpg)
  -- each `S_U` is `π^U S_∅ + O(δ π^U S_∅ + E)`
  have hcomp : ∀ κ ∈ ι, |SU ((Finset.univ : Finset F).biUnion κ) -
      (∏ p ∈ (Finset.univ : Finset F).biUnion κ, π p) * S0| ≤
        δ * ((∏ p ∈ (Finset.univ : Finset F).biUnion κ, π p) * S0) + E := by
    intro κ hκ
    by_cases hdv : ∃ p ∈ (Finset.univ : Finset F).biUnion κ, p ∣ c
    · obtain ⟨p, hp, hpc⟩ := hdv
      have hπ0 : ∏ p ∈ (Finset.univ : Finset F).biUnion κ, π p = 0 :=
        prod_eq_zero hp (by simp [π, modelWeight, hpc])
      have hSU0 : SU ((Finset.univ : Finset F).biUnion κ) = 0 := by
        refine sum_eq_zero fun e _ => ?_
        rw [ite_eq_right]
        rintro ⟨-, h⟩
        have h1 := h p hp
        have h2 : e * c ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.2 (dvd_mul_of_dvd_right hpc e)
        have h3 := h1.symm.trans h2
        have hp1 := (hS p (hUS κ hκ hp)).one_lt
        rw [Nat.ModEq, Nat.zero_mod, Nat.mod_eq_of_lt hp1] at h3
        exact one_ne_zero h3
      rw [hπ0, hSU0]
      simpa using hE
    · push Not at hdv
      have hπ : ∏ p ∈ (Finset.univ : Finset F).biUnion κ, π p =
          1 / ∏ p ∈ (Finset.univ : Finset F).biUnion κ, ((p : ℝ) - 1) := by
        rw [one_div, ← prod_inv_distrib]
        exact prod_congr rfl fun p hp => by simp [π, modelWeight, hdv p hp]
      have h := hstar ((Finset.univ : Finset F).biUnion κ) (hUS κ hκ) hdv
      rw [hπ]
      rw [div_mul_eq_mul_div, one_mul]
      exact h
  -- the expansion
  have hexp : ∀ e ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ e then w e else 0) *
      ∏ g ∈ F, (1 - α g * ell (primeCount g (e * c - 1))) =
      ∑ κ ∈ ι, (∏ g, lowCoeff (α g.1) (κ g).card) *
        (if (∀ p ∈ S, ¬ p ∣ e) ∧ ∀ p ∈ (Finset.univ : Finset F).biUnion κ, e * c ≡ 1 [MOD p]
          then w e else 0) := by
    intro e he
    have he1 : 1 ≤ e * c := one_le_mul (by have := (mem_Ioc.1 he).1; omega) hc
    rw [prod_one_sub_mul_ell_eq, mul_sum]
    refine sum_congr rfl fun κ _ => ?_
    have hcong : (∀ p ∈ (Finset.univ : Finset F).biUnion κ, p ∣ e * c - 1) ↔
        ∀ p ∈ (Finset.univ : Finset F).biUnion κ, e * c ≡ 1 [MOD p] :=
      forall₂_congr fun p _ => ((Nat.modEq_iff_dvd' he1).symm.trans ⟨Nat.ModEq.symm,
        Nat.ModEq.symm⟩)
    by_cases hr : ∀ p ∈ S, ¬ p ∣ e
    · by_cases hd0 : ∀ p ∈ (Finset.univ : Finset F).biUnion κ, p ∣ e * c - 1
      · rw [ite_eq_left hr, ite_eq_left hd0, ite_eq_left ⟨hr, hcong.1 hd0⟩]
        ring
      · rw [ite_eq_left hr, ite_eq_right hd0, ite_eq_right fun h => hd0 (hcong.2 h.2)]
        ring
    · rw [ite_eq_right hr, zero_mul, ite_eq_right (show ¬((∀ p ∈ S, ¬ p ∣ e) ∧
        ∀ p ∈ (Finset.univ : Finset F).biUnion κ, e * c ≡ 1 [MOD p]) from fun h => hr h.1),
        mul_zero]
  rw [sum_congr rfl hexp, sum_comm]
  -- the model sums factor over the groups
  have hdisjκ : ∀ κ ∈ ι, ((Finset.univ : Finset F) : Set F).PairwiseDisjoint κ := by
    intro κ hκ g _ g' _ hgg'
    have h1 := mem_powerset.1 (mem_filter.1 (Fintype.mem_piFinset.1 hκ g)).1
    have h2 := mem_powerset.1 (mem_filter.1 (Fintype.mem_piFinset.1 hκ g')).1
    exact disjoint_of_subset_left h1 (disjoint_of_subset_right h2
      (hdisj g.2 g'.2 fun h => hgg' (Subtype.ext h)))
  have hmodel : ∑ κ ∈ ι, (∏ g, lowCoeff (α g.1) (κ g).card) *
      ∏ p ∈ (Finset.univ : Finset F).biUnion κ, π p =
      ∏ g ∈ F, (1 - α g * (∑ p ∈ g, π p - ∑ K ∈ g.powersetCard 2, ∏ p ∈ K, π p)) := by
    rw [← prod_coe_sort F]
    simp_rw [← sum_lowSubsets_lowCoeff_mul_prod]
    rw [prod_univ_sum]
    refine sum_congr rfl fun κ hκ => ?_
    rw [prod_mul_distrib, prod_biUnion (hdisjκ κ hκ)]
  have habs : ∑ κ ∈ ι, |(∏ g, lowCoeff (α g.1) (κ g).card)| *
      ∏ p ∈ (Finset.univ : Finset F).biUnion κ, π p =
      ∏ g ∈ F, (1 + |α g| * (∑ p ∈ g, π p + ∑ K ∈ g.powersetCard 2, ∏ p ∈ K, π p)) := by
    rw [← prod_coe_sort F]
    simp_rw [← sum_lowSubsets_abs_lowCoeff_mul_prod]
    rw [prod_univ_sum]
    refine sum_congr rfl fun κ hκ => ?_
    rw [prod_mul_distrib, prod_biUnion (hdisjκ κ hκ), abs_prod]
  have hcard : ∑ κ ∈ ι, |∏ g, lowCoeff (α g.1) (κ g).card| ≤
      ∏ g ∈ F, ((lowSubsets g).card : ℝ) := by
    have h : ∑ κ ∈ ι, |∏ g, lowCoeff (α g.1) (κ g).card| =
        ∏ g : F, ∑ K ∈ lowSubsets g.1, |lowCoeff (α g.1) K.card| := by
      rw [prod_univ_sum]
      exact sum_congr rfl fun κ _ => abs_prod _ _
    rw [h, ← prod_coe_sort F]
    refine prod_le_prod₀ (fun g _ => sum_nonneg fun K _ => abs_nonneg _) fun g _ => ?_
    calc ∑ K ∈ lowSubsets g.1, |lowCoeff (α g.1) K.card| ≤ ∑ _K ∈ lowSubsets g.1, (1 : ℝ) :=
          sum_le_sum fun K _ => abs_lowCoeff_le (hα g.1 g.2) _
      _ = _ := by rw [sum_const, nsmul_eq_mul, mul_one]
  have hπ0 : ∀ κ ∈ ι, 0 ≤ ∏ p ∈ (Finset.univ : Finset F).biUnion κ, π p := fun κ hκ =>
    prod_nonneg fun p hp => modelWeight_nonneg (hS p (hUS κ hκ hp))
  -- assembling
  calc ∑ κ ∈ ι, ∑ e ∈ Ioc A B, (∏ g, lowCoeff (α g.1) (κ g).card) *
        (if (∀ p ∈ S, ¬ p ∣ e) ∧ ∀ p ∈ (Finset.univ : Finset F).biUnion κ,
          e * c ≡ 1 [MOD p] then w e else 0)
      = ∑ κ ∈ ι, (∏ g, lowCoeff (α g.1) (κ g).card) *
          SU ((Finset.univ : Finset F).biUnion κ) := sum_congr rfl fun κ _ => by rw [mul_sum]
    _ ≤ ∑ κ ∈ ι, ((∏ g, lowCoeff (α g.1) (κ g).card) *
          ((∏ p ∈ (Finset.univ : Finset F).biUnion κ, π p) * S0) +
          |(∏ g, lowCoeff (α g.1) (κ g).card)| *
            (δ * ((∏ p ∈ (Finset.univ : Finset F).biUnion κ, π p) * S0) + E)) := by
        refine sum_le_sum fun κ hκ => ?_
        have h := hcomp κ hκ
        have : (∏ g, lowCoeff (α g.1) (κ g).card) * SU ((Finset.univ : Finset F).biUnion κ) -
            (∏ g, lowCoeff (α g.1) (κ g).card) *
              ((∏ p ∈ (Finset.univ : Finset F).biUnion κ, π p) * S0) ≤
            |(∏ g, lowCoeff (α g.1) (κ g).card)| *
              (δ * ((∏ p ∈ (Finset.univ : Finset F).biUnion κ, π p) * S0) + E) := by
          rw [← mul_sub]
          refine (le_abs_self _).trans ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
        linarith
    _ = S0 * (∑ κ ∈ ι, (∏ g, lowCoeff (α g.1) (κ g).card) *
            ∏ p ∈ (Finset.univ : Finset F).biUnion κ, π p) +
          δ * S0 * (∑ κ ∈ ι, |(∏ g, lowCoeff (α g.1) (κ g).card)| *
            ∏ p ∈ (Finset.univ : Finset F).biUnion κ, π p) +
          E * ∑ κ ∈ ι, |(∏ g, lowCoeff (α g.1) (κ g).card)| := by
        simp only [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun κ _ => by ring
    _ ≤ _ := by
        rw [hmodel, habs]
        have := mul_le_mul_of_nonneg_left hcard hE
        linarith

end

end Erdos408
