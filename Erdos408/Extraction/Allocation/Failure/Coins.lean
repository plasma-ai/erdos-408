module

public import Erdos408.Extraction.Allocation.Endpoint

/-!
# The coin generating function

The algebra of E6 before any arithmetic.

* Chernoff: with `θ = 1 - e⁻¹`, the probability of fewer than `c₂ T` successes
  in a family `F` is at most `e^{c₂ T} ∏_{g ∈ F} (1 - θ s_g)`, since
  `∑_P w(P) e^{-|P ∩ F|} = ∏_{g ∈ F} (1 - θ s_g)`.
* The depth-two Bonferroni bound `ℓ(ω) = ω - C(ω, 2) ≤ ω 2^{1 - ω}`, so the
  `u`-side weight of a group is at least `ℓ(ω_g(u)) / V_g`, and
  `1 - θ s_g ≤ 1 - α_g ℓ(ω_g(u))` with `α_g = θ c₁ W_g(v) / V_g`.
* The expansion `1 - α ℓ(ω_g(u)) = ∑_{K ⊆ g, |K| ≤ 2} c_α(|K|) [K ∣ u]`, with
  `c_α(0) = 1`, `c_α(1) = -α`, `c_α(2) = α`, and its product over a family.
-/

@[expose] public section

namespace Erdos408

open Finset Real

noncomputable section

/-! ### Chernoff -/

/-- The Chernoff parameter `θ = 1 - e⁻¹`. -/
def chernoffTheta : ℝ := 1 - Real.exp (-1)

/-- `θ > 0`. -/
lemma chernoffTheta_pos : 0 < chernoffTheta := by
  rw [chernoffTheta, sub_pos]
  linarith [Real.exp_neg_one_lt_d9]

/-- `θ ≤ 1`. -/
lemma chernoffTheta_le_one : chernoffTheta ≤ 1 := by
  rw [chernoffTheta]
  linarith [exp_pos (-1)]

/-- `∑_P w(P) e^{-|P ∩ F|} = ∏_{g ∈ F} (1 - θ s_g)` for a family `F ⊆ 𝒞`. -/
lemma sum_patternWeight_mul_exp_eq (c₁ x : ℝ) (w : ℕ) {F : Finset (Finset ℕ)}
    (hF : F ⊆ candidateGroups x) :
    ∑ P ∈ (candidateGroups x).powerset,
        patternWeight c₁ x P w * Real.exp (-((P ∩ F).card : ℝ)) =
      ∏ g ∈ F, (1 - chernoffTheta * successCoin c₁ g w) := by
  have hε : ∀ P : Finset (Finset ℕ), Real.exp (-((P ∩ F).card : ℝ)) =
      ∏ g ∈ P, (if g ∈ F then Real.exp (-1) else 1) := by
    intro P
    rw [prod_ite_mem, prod_const, ← Real.exp_nat_mul]
    ring_nf
  have h := prod_add (fun g => successCoin c₁ g w * (if g ∈ F then Real.exp (-1) else 1))
    (fun g => 1 - successCoin c₁ g w) (candidateGroups x)
  have hl : ∏ g ∈ candidateGroups x,
      (successCoin c₁ g w * (if g ∈ F then Real.exp (-1) else 1) + (1 - successCoin c₁ g w)) =
      ∏ g ∈ candidateGroups x, (if g ∈ F then 1 - chernoffTheta * successCoin c₁ g w else 1) :=
    prod_congr rfl fun g _ => by
      unfold chernoffTheta
      split_ifs <;> ring
  rw [hl, prod_ite_mem, inter_eq_right.2 hF] at h
  rw [h]
  refine sum_congr rfl fun P _ => ?_
  rw [patternWeight, hε, prod_mul_distrib]
  ring

/-- Chernoff: few successes in either family have probability at most
`e^{c₂ T} (∏_{small} (1 - θ s_g) + ∏_{big} (1 - θ s_g))`. -/
theorem failureProb_le_exp_mul {c₁ c₂ x : ℝ} {w : ℕ}
    (hs : ∀ g ∈ candidateGroups x, 0 ≤ successCoin c₁ g w ∧ successCoin c₁ g w ≤ 1) :
    failureProb c₁ c₂ x w ≤ Real.exp (c₂ * logLog x) *
      (∏ g ∈ smallGroups x, (1 - chernoffTheta * successCoin c₁ g w) +
        ∏ g ∈ bigGroups x, (1 - chernoffTheta * successCoin c₁ g w)) := by
  set τ := c₂ * logLog x
  have hpw : ∀ P ∈ (candidateGroups x).powerset, 0 ≤ patternWeight c₁ x P w :=
    fun P hP => patternWeight_nonneg hs (mem_powerset.1 hP)
  -- pointwise: `[¬ many] ≤ e^{τ - |P ∩ S|} + e^{τ - |P ∩ B|}`
  have hpt : ∀ P : Finset (Finset ℕ), ¬ ManySuccesses c₂ x P →
      1 ≤ Real.exp (τ - ((P ∩ smallGroups x).card : ℝ)) +
        Real.exp (τ - ((P ∩ bigGroups x).card : ℝ)) := by
    intro P hP
    rw [ManySuccesses, not_and_or] at hP
    rcases hP with h | h <;> push Not at h
    · have := one_le_exp (show 0 ≤ τ - ((P ∩ smallGroups x).card : ℝ) by linarith)
      linarith [exp_pos (τ - ((P ∩ bigGroups x).card : ℝ))]
    · have := one_le_exp (show 0 ≤ τ - ((P ∩ bigGroups x).card : ℝ) by linarith)
      linarith [exp_pos (τ - ((P ∩ smallGroups x).card : ℝ))]
  calc failureProb c₁ c₂ x w
      ≤ ∑ P ∈ (candidateGroups x).powerset with ¬ ManySuccesses c₂ x P, patternWeight c₁ x P w *
          (Real.exp (τ - ((P ∩ smallGroups x).card : ℝ)) +
            Real.exp (τ - ((P ∩ bigGroups x).card : ℝ))) :=
        sum_le_sum fun P hP => le_mul_of_one_le_right (hpw P (mem_filter.1 hP).1)
          (hpt P (mem_filter.1 hP).2)
    _ ≤ ∑ P ∈ (candidateGroups x).powerset, patternWeight c₁ x P w *
          (Real.exp (τ - ((P ∩ smallGroups x).card : ℝ)) +
            Real.exp (τ - ((P ∩ bigGroups x).card : ℝ))) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun P hP _ =>
          mul_nonneg (hpw P hP) (by positivity)
    _ = Real.exp τ * (∑ P ∈ (candidateGroups x).powerset,
            patternWeight c₁ x P w * Real.exp (-((P ∩ smallGroups x).card : ℝ)) +
          ∑ P ∈ (candidateGroups x).powerset,
            patternWeight c₁ x P w * Real.exp (-((P ∩ bigGroups x).card : ℝ))) := by
        rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun P _ => ?_
        rw [sub_eq_add_neg, sub_eq_add_neg, exp_add, exp_add]
        ring
    _ = _ := by
        rw [sum_patternWeight_mul_exp_eq c₁ x w subset_union_left,
          sum_patternWeight_mul_exp_eq c₁ x w subset_union_right]

/-! ### The depth-two lower bound -/

/-- The depth-two Bonferroni polynomial `ℓ(ω) = ω - C(ω, 2)`. -/
def ell (n : ℕ) : ℝ := n - (n.choose 2 : ℝ)

/-- `ℓ(ω) ≤ 1`. -/
lemma ell_le_one (n : ℕ) : ell n ≤ 1 := by
  unfold ell
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num [Nat.choose]
  · rw [Nat.choose_two_right]
    have h2 : (n : ℝ) * (n - 1) / 2 ≤ ((n * (n - 1) / 2 : ℕ) : ℝ) + 1 := by
      have := Nat.div_add_mod (n * (n - 1)) 2
      have hm := Nat.mod_lt (n * (n - 1)) (show 0 < 2 by norm_num)
      have : ((n * (n - 1) : ℕ) : ℝ) = 2 * ((n * (n - 1) / 2 : ℕ) : ℝ) +
          ((n * (n - 1) % 2 : ℕ) : ℝ) := by exact_mod_cast this.symm
      have hm' : ((n * (n - 1) % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega)
      rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one] at this
      linarith
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith

/-- `ℓ(ω) ≤ ω 2^{1 - ω}`. -/
lemma ell_le_natCast_mul_zpow (n : ℕ) : ell n ≤ (n : ℝ) * (1 / 2 : ℝ) ^ ((n : ℤ) - 1) := by
  unfold ell
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num [Nat.choose]
  · have h0 : 0 ≤ (n : ℝ) * (1 / 2 : ℝ) ^ ((n : ℤ) - 1) := by positivity
    have : (n : ℝ) ≤ (n.choose 2 : ℝ) := by
      rw [Nat.choose_two_right]
      have : n ≤ n * (n - 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        have : 2 ≤ n - 1 := by omega
        exact Nat.mul_le_mul_left n this
      exact_mod_cast this
    linarith

/-- The weight of one group is at least `ℓ(ω_g(n)) / V_g`. -/
lemma ell_div_le_markedWeight {g : Finset ℕ} (hg : 0 < harmonicMass g) (n : ℕ) :
    ell (primeCount g n) / harmonicMass g ≤ markedWeight {g} (1 / 2) id n := by
  rw [markedWeight_singleton]
  exact div_le_div_of_nonneg_right (ell_le_natCast_mul_zpow _) hg.le

/-- `1 - θ s_g(u) ≤ 1 - α_g ℓ(ω_g(u))` with `α_g = θ c₁ W_g(u + 1) / V_g`. -/
lemma one_sub_mul_successCoin_le {c₁ : ℝ} (hc₁ : 0 ≤ c₁) {g : Finset ℕ}
    (hg : 0 < harmonicMass g) (w : ℕ) :
    1 - chernoffTheta * successCoin c₁ g w ≤
      1 - chernoffTheta * c₁ * markedWeight {g} (1 / 2) id (w + 1) / harmonicMass g *
        ell (primeCount g w) := by
  have hmw : 0 ≤ markedWeight {g} (1 / 2) id (w + 1) := by
    rw [markedWeight_singleton]
    exact div_nonneg (by positivity) hg.le
  have h := ell_div_le_markedWeight hg w
  have hθ := chernoffTheta_pos.le
  unfold successCoin
  have : chernoffTheta * c₁ * markedWeight {g} (1 / 2) id (w + 1) / harmonicMass g *
      ell (primeCount g w) = chernoffTheta * c₁ * markedWeight {g} (1 / 2) id (w + 1) *
        (ell (primeCount g w) / harmonicMass g) := by ring
  rw [this]
  have := mul_le_mul_of_nonneg_left h (by positivity :
    0 ≤ chernoffTheta * c₁ * markedWeight {g} (1 / 2) id (w + 1))
  nlinarith

/-! ### The expansion -/

/-- The subsets of at most two primes of a group. -/
def lowSubsets (g : Finset ℕ) : Finset (Finset ℕ) :=
  g.powerset.filter (·.card ≤ 2)

/-- The coefficients `c_α(0) = 1`, `c_α(1) = -α`, `c_α(2) = α` of the expansion. -/
def lowCoeff (α : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then -α else α

/-- `∑_{m ≤ n} C(n, m) f(m) = f(0) + n f(1) + C(n, 2) f(2)` when `f` vanishes beyond `2`. -/
private lemma sum_range_choose_mul_eq (n : ℕ) (f : ℕ → ℝ) (hf : ∀ m, 2 < m → f m = 0) :
    ∑ m ∈ range (n + 1), (n.choose m : ℝ) * f m = f 0 + n * f 1 + (n.choose 2 : ℝ) * f 2 := by
  have h1 : ∑ m ∈ range (n + 1), (n.choose m : ℝ) * f m =
      ∑ m ∈ range (n + 3), (n.choose m : ℝ) * f m := by
    refine sum_subset (range_subset_range.2 (by omega)) fun m hm hm' => ?_
    rw [mem_range] at hm'
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  have h2 : ∑ m ∈ range 3, (n.choose m : ℝ) * f m =
      ∑ m ∈ range (n + 3), (n.choose m : ℝ) * f m := by
    refine sum_subset (range_subset_range.2 (by omega)) fun m hm hm' => ?_
    rw [mem_range] at hm'
    rw [hf m (by omega), mul_zero]
  rw [h1, ← h2]
  simp [sum_range_succ]

/-- `1 - α ℓ(ω_g(u)) = ∑_{K ⊆ g, |K| ≤ 2} c_α(|K|) [∀ p ∈ K, p ∣ u]`. -/
lemma sum_lowSubsets_eq (g : Finset ℕ) (α : ℝ) (w : ℕ) :
    ∑ K ∈ lowSubsets g, lowCoeff α K.card * (if ∀ p ∈ K, p ∣ w then 1 else 0) =
      1 - α * ell (primeCount g w) := by
  set s := g.filter (· ∣ w)
  have hfilt : (lowSubsets g).filter (fun K => ∀ p ∈ K, p ∣ w) =
      s.powerset.filter (·.card ≤ 2) := by
    ext K
    simp only [lowSubsets, mem_filter, mem_powerset, s, subset_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨fun p hp => ⟨h1 hp, h3 p hp⟩, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨fun p hp => (h1 hp).1, h2⟩, fun p hp => (h1 hp).2⟩
  have : ∑ K ∈ lowSubsets g, lowCoeff α K.card * (if ∀ p ∈ K, p ∣ w then 1 else 0) =
      ∑ K ∈ (lowSubsets g).filter (fun K => ∀ p ∈ K, p ∣ w), lowCoeff α K.card := by
    rw [sum_filter]
    exact sum_congr rfl fun K _ => by split_ifs <;> ring
  rw [this, hfilt, sum_filter,
    sum_powerset_apply_card (fun m => if m ≤ 2 then lowCoeff α m else 0)]
  simp only [nsmul_eq_mul]
  rw [sum_range_choose_mul_eq _ _ fun m hm => by simp [show ¬ m ≤ 2 by omega]]
  simp only [lowCoeff, ell, primeCount, s]
  norm_num
  ring

/-- The expansion of `∏_{g ∈ F} (1 - α_g ℓ(ω_g(u)))` over choices of at most two primes in each
group: the term of `κ` is `∏_g c_{α_g}(|κ_g|)` times `[∀ p ∈ ⋃ κ_g, p ∣ u]`. -/
theorem prod_one_sub_mul_ell_eq (F : Finset (Finset ℕ)) (α : Finset ℕ → ℝ) (w : ℕ) :
    ∏ g ∈ F, (1 - α g * ell (primeCount g w)) =
      ∑ κ ∈ Fintype.piFinset (fun g : F => lowSubsets g.1),
        (∏ g, lowCoeff (α g.1) (κ g).card) *
          (if ∀ p ∈ (Finset.univ : Finset F).biUnion κ, p ∣ w then 1 else 0) := by
  rw [← prod_coe_sort F]
  simp_rw [← sum_lowSubsets_eq]
  rw [prod_univ_sum]
  refine sum_congr rfl fun κ _ => ?_
  rw [prod_mul_distrib]
  congr 1
  rw [prod_ite_zero, prod_const_one]
  congr 1
  apply propext
  simp only [mem_biUnion, mem_univ, true_and, forall_exists_index]
  exact ⟨fun h p g hp => h g trivial p hp, fun h g _ p hp => h p g hp⟩

end

end Erdos408
