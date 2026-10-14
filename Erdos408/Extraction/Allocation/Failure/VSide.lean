import Erdos408.Extraction.Allocation.Euler
import Erdos408.Extraction.Allocation.Failure.USide

/-!
# The `v`-side: the candidate part of `v`

The `u`-side model of a group `g` at the candidate part `d = v_P` is
`1 - α_g(d) (μ_g - e₂,g)`, where `α_g(d) = θ c₁ W_g(d) / V_g`. It lies in
`[0, 1]`, and when exactly one prime of `g` divides `d` it is at most
`1 - θ c₁ / 5`: then `W_g(d) = 1/V_g`, and the model mass `μ_g` of the other
primes of `g` is at least `2/5`.

The candidate part ranges over the `P`-factored `d`, weighted by `1/d`. The
weight is multiplicative over the disjoint groups, so the sum factors into
local sums, and the local sum of a group of the family loses a fixed fraction:
`∑_{d} [no lone prime in g] / d ≤ ∏_{p ∈ g} (1 - 1/p)⁻¹ - V_g`.
-/

namespace Erdos408

open Finset Real

noncomputable section

/-- The `u`-side coefficient `α_g(d) = θ c₁ W_g(d) / V_g` of a group. -/
def sideAlpha (c₁ : ℝ) (g : Finset ℕ) (d : ℕ) : ℝ :=
  chernoffTheta * c₁ * markedWeight {g} (1 / 2) id d / harmonicMass g

/-- The `u`-side model mass `μ_g - e₂,g` of a group, with `π = [p ∤ c] / (p - 1)`. -/
def sideModel (g : Finset ℕ) (c : ℕ) : ℝ :=
  ∑ p ∈ g, modelWeight c p - ∑ K ∈ g.powersetCard 2, ∏ p ∈ K, modelWeight c p

/-- The absolute `u`-side model mass `μ_g + e₂,g` of a group. -/
def sideModelAbs (g : Finset ℕ) (c : ℕ) : ℝ :=
  ∑ p ∈ g, modelWeight c p + ∑ K ∈ g.powersetCard 2, ∏ p ∈ K, modelWeight c p

/-- The facts about one group used on the `v`-side. -/
structure SideGroup (g : Finset ℕ) : Prop where
  mass_ge : 1 / 2 ≤ harmonicMass g
  mass_le : harmonicMass g ≤ 4 / 5
  prime : ∀ p ∈ g, p.Prime
  large : ∀ p ∈ g, 100 ≤ p

section Group

variable {g : Finset ℕ} (hg : SideGroup g)
include hg

/-- `μ_g ≤ (100/99) V_g ≤ 1`. -/
lemma SideGroup.sum_modelWeight_le (c : ℕ) : ∑ p ∈ g, modelWeight c p ≤ 1 := by
  have h : ∀ p ∈ g, modelWeight c p ≤ 100 / 99 * ((1 : ℝ) / p) := by
    intro p hp
    have h100 : (100 : ℝ) ≤ p := by exact_mod_cast hg.large p hp
    unfold modelWeight
    split_ifs
    · positivity
    · rw [div_le_iff₀ (by linarith)]
      field_simp
      linarith
  calc ∑ p ∈ g, modelWeight c p ≤ ∑ p ∈ g, 100 / 99 * ((1 : ℝ) / p) := sum_le_sum h
    _ = 100 / 99 * harmonicMass g := by rw [← mul_sum]; rfl
    _ ≤ 1 := by have := hg.mass_le; linarith

/-- The model weights of a group are nonnegative. -/
lemma SideGroup.modelWeight_nonneg (c : ℕ) : ∀ p ∈ g, 0 ≤ modelWeight c p :=
  fun p hp => Erdos408.modelWeight_nonneg (hg.prime p hp)

/-- `0 ≤ μ_g - e₂,g ≤ 1`, and `μ_g - e₂,g ≥ μ_g / 2`. -/
lemma SideGroup.sideModel_mem (c : ℕ) :
    0 ≤ sideModel g c ∧ sideModel g c ≤ 1 ∧ (∑ p ∈ g, modelWeight c p) / 2 ≤ sideModel g c := by
  have hμ := hg.sum_modelWeight_le c
  have hμ0 : 0 ≤ ∑ p ∈ g, modelWeight c p := sum_nonneg (hg.modelWeight_nonneg c)
  have he2 := sum_powersetCard_two_prod_le g (hg.modelWeight_nonneg c)
  have he20 : 0 ≤ ∑ K ∈ g.powersetCard 2, ∏ p ∈ K, modelWeight c p :=
    sum_nonneg fun K hK => prod_nonneg fun p hp =>
      hg.modelWeight_nonneg c p ((mem_powersetCard.1 hK).1 hp)
  unfold sideModel
  refine ⟨by nlinarith, by linarith, by nlinarith⟩

/-- `0 ≤ μ_g + e₂,g ≤ 3/2`. -/
lemma SideGroup.sideModelAbs_le (c : ℕ) : sideModelAbs g c ≤ 3 / 2 := by
  have hμ := hg.sum_modelWeight_le c
  have hμ0 : 0 ≤ ∑ p ∈ g, modelWeight c p := sum_nonneg (hg.modelWeight_nonneg c)
  have he2 := sum_powersetCard_two_prod_le g (hg.modelWeight_nonneg c)
  unfold sideModelAbs
  nlinarith

/-- `0 ≤ α_g(d) ≤ 1` for `0 ≤ c₁ ≤ 1/4`. -/
lemma SideGroup.sideAlpha_mem {c₁ : ℝ} (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1 / 4) (d : ℕ) :
    0 ≤ sideAlpha c₁ g d ∧ sideAlpha c₁ g d ≤ 1 := by
  obtain ⟨h1, h2⟩ := markedWeight_half_mem hg.mass_ge d
  have hV := hg.mass_ge
  have hθ := chernoffTheta_pos
  have hθ1 := chernoffTheta_le_one
  unfold sideAlpha
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by linarith)]
  calc chernoffTheta * c₁ * markedWeight {g} (1 / 2) id d ≤ 1 * (1 / 4) * 2 := by gcongr
    _ ≤ harmonicMass g := by linarith

/-- The `u`-side model of a group lies in `[0, 1]`, and is at most `1 - θ c₁ / 5` when exactly
one prime of `g` divides `d` (with `p ∣ c ↔ p ∣ d` on `g`). -/
lemma SideGroup.one_sub_sideAlpha_mul_le {c₁ : ℝ} (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1 / 4) {c d : ℕ}
    (hcd : ∀ p ∈ g, p ∣ c ↔ p ∣ d) :
    0 ≤ 1 - sideAlpha c₁ g d * sideModel g c ∧
      1 - sideAlpha c₁ g d * sideModel g c ≤
        1 - chernoffTheta * c₁ / 5 * (if primeCount g d = 1 then 1 else 0) := by
  obtain ⟨hα0, hα1⟩ := hg.sideAlpha_mem hc₁ hc₁' d
  obtain ⟨hm0, hm1, hm2⟩ := hg.sideModel_mem c
  refine ⟨by nlinarith, ?_⟩
  split_ifs with h1
  · -- a lone prime `p₀` of `g` divides `d`
    have hV := hg.mass_le
    have hV' := hg.mass_ge
    have hθ := chernoffTheta_pos
    have hmw : markedWeight {g} (1 / 2) id d = 1 / harmonicMass g := by
      rw [markedWeight_singleton]
      simp only [id, h1]
      norm_num
    have hα : chernoffTheta * c₁ ≤ sideAlpha c₁ g d := by
      have he : sideAlpha c₁ g d = chernoffTheta * c₁ * (1 / harmonicMass g ^ 2) := by
        unfold sideAlpha
        rw [hmw]
        field_simp
      rw [he]
      refine le_mul_of_one_le_right (by positivity) ?_
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    -- `μ_g ≥ V_g - 1/p₀ ≥ 2/5`
    have hμ : 2 / 5 ≤ ∑ p ∈ g, modelWeight c p := by
      obtain ⟨p₀, hp₀⟩ := card_eq_one.1 h1
      have hp₀g : p₀ ∈ g := (mem_filter.1 (hp₀ ▸ mem_singleton_self p₀)).1
      have hlow : ∀ p ∈ g, (1 : ℝ) / p - (if p = p₀ then (1 : ℝ) / p else 0) ≤
          modelWeight c p := by
        intro p hp
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hg.prime p hp).two_le
        by_cases hpp : p = p₀
        · simp only [hpp, ↓reduceIte, sub_self]
          exact hg.modelWeight_nonneg c p₀ hp₀g
        · have hnd : ¬ p ∣ d := by
            intro hpd
            have : p ∈ g.filter (· ∣ d) := mem_filter.2 ⟨hp, hpd⟩
            rw [hp₀] at this
            exact hpp (mem_singleton.1 this)
          have hnc : ¬ p ∣ c := fun h => hnd ((hcd p hp).1 h)
          simp only [hpp, ↓reduceIte, sub_zero, modelWeight, hnc]
          exact one_div_le_one_div_of_le (by linarith) (by linarith)
      have := sum_le_sum hlow
      rw [sum_sub_distrib, sum_ite_eq' g p₀, ite_eq_left hp₀g] at this
      have h100 : (100 : ℝ) ≤ p₀ := by exact_mod_cast hg.large p₀ hp₀g
      have : (1 : ℝ) / p₀ ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num) h100
      unfold harmonicMass at hV'
      linarith
    have hm : 1 / 5 ≤ sideModel g c := by linarith
    have := mul_le_mul hα hm (by norm_num) hα0
    linarith
  · nlinarith

end Group

/-! ### Factoring over the groups -/

/-- A number whose primes lie in the disjoint groups `𝒢` is the product of its group parts. -/
lemma prod_keepPrimes_eq {𝒢 : Finset (Finset ℕ)} (hdisj : (𝒢 : Set (Finset ℕ)).PairwiseDisjoint id)
    {d : ℕ} (hd : d ≠ 0) (hdP : ∀ p ∈ d.primeFactors, p ∈ 𝒢.biUnion id) :
    ∏ g ∈ 𝒢, keepPrimes g d = d := by
  refine Nat.eq_of_factorization_eq (prod_ne_zero_iff.2 fun g _ => keepPrimes_ne_zero g d) hd
    fun p => ?_
  rw [Nat.factorization_prod fun g _ => keepPrimes_ne_zero g d, Finsupp.coe_finsetSum,
    Finset.sum_apply]
  simp only [factorization_keepPrimes, Finsupp.filter_apply]
  by_cases hp : p ∈ d.primeFactors
  · obtain ⟨g₀, hg₀, hpg₀⟩ := mem_biUnion.1 (hdP p hp)
    rw [sum_eq_single g₀]
    · simp [show p ∈ g₀ from hpg₀]
    · intro g hg hne
      have : p ∉ g := fun hpg => disjoint_left.1 (hdisj hg hg₀ hne) hpg hpg₀
      simp [this]
    · exact fun h => absurd hg₀ h
  · have : d.factorization p = 0 := Finsupp.notMem_support_iff.1 (by
      rwa [Nat.support_factorization])
    rw [this]
    exact sum_eq_zero fun g _ => by split_ifs <;> rfl

/-- Sums of products over the group parts factor: `∑_{d ∈ D} ∏_g h_g(d_g) ≤ ∏_g ∑_{m} h_g(m)`. -/
lemma sum_prod_keepPrimes_le {𝒢 : Finset (Finset ℕ)}
    (hdisj : (𝒢 : Set (Finset ℕ)).PairwiseDisjoint id) {D : Finset ℕ}
    (hD : ∀ d ∈ D, d ≠ 0 ∧ ∀ p ∈ d.primeFactors, p ∈ 𝒢.biUnion id) (Dg : Finset ℕ → Finset ℕ)
    (hDg : ∀ d ∈ D, ∀ g ∈ 𝒢, keepPrimes g d ∈ Dg g) (h : Finset ℕ → ℕ → ℝ)
    (hh : ∀ g ∈ 𝒢, ∀ m ∈ Dg g, 0 ≤ h g m) :
    ∑ d ∈ D, ∏ g ∈ 𝒢, h g (keepPrimes g d) ≤ ∏ g ∈ 𝒢, ∑ m ∈ Dg g, h g m := by
  classical
  rw [← prod_coe_sort 𝒢 (fun g => ∑ m ∈ Dg g, h g m), prod_univ_sum]
  set ι : ℕ → (𝒢 → ℕ) := fun d g => keepPrimes g.1 d
  have hinj : Set.InjOn ι D := by
    intro d hd d' hd' hdd
    rw [← prod_keepPrimes_eq hdisj (hD d hd).1 (hD d hd).2,
      ← prod_keepPrimes_eq hdisj (hD d' hd').1 (hD d' hd').2, ← prod_coe_sort 𝒢,
      ← prod_coe_sort 𝒢]
    exact prod_congr rfl fun g _ => congrFun hdd g
  calc ∑ d ∈ D, ∏ g ∈ 𝒢, h g (keepPrimes g d) = ∑ d ∈ D, ∏ g : 𝒢, h g.1 (ι d g) :=
        sum_congr rfl fun d _ => (prod_coe_sort 𝒢 _).symm
    _ = ∑ κ ∈ D.image ι, ∏ g : 𝒢, h g.1 (κ g) :=
        (sum_image (f := fun κ => ∏ g : 𝒢, h g.1 (κ g)) hinj).symm
    _ ≤ ∑ κ ∈ Fintype.piFinset (fun g : 𝒢 => Dg g.1), ∏ g : 𝒢, h g.1 (κ g) := by
        refine sum_le_sum_of_subset_of_nonneg (fun κ hκ => ?_) fun κ hκ _ =>
          prod_nonneg fun g _ => hh g.1 g.2 _ (Fintype.mem_piFinset.1 hκ g)
        obtain ⟨d, hd, rfl⟩ := mem_image.1 hκ
        exact Fintype.mem_piFinset.2 fun g => hDg d hd g.1 g.2

/-- Group parts keep the primes of the group. -/
lemma primeCount_keepPrimes {g : Finset ℕ} (hg : ∀ p ∈ g, p.Prime) {d : ℕ} (hd : d ≠ 0) :
    primeCount g (keepPrimes g d) = primeCount g d := by
  unfold primeCount
  congr 1
  refine filter_congr fun p hp => ?_
  rw [(hg p hp).dvd_iff_one_le_factorization (keepPrimes_ne_zero g d),
    (hg p hp).dvd_iff_one_le_factorization hd, factorization_keepPrimes,
    Finsupp.filter_apply_pos _ _ hp]

end

end Erdos408
