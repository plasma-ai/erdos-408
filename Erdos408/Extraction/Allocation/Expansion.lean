import Erdos408.Extraction.Allocation.Coefficients

/-!
# Success coins and the signed expansions

E6–E7 of the blueprint. Toss independent coins in the candidate groups `𝒞`
with success probability
`s_g(w) = c₁ [q₀^{ω_g(w) - 1} ω_g(w) / V_g] [q₀^{ω_g(w+1) - 1} ω_g(w+1) / V_g]`,
with `q₀ = 1/2` on both endpoints `u = w` and `v = w + 1`. The success
patterns `P ⊆ 𝒞` have weights `∏_{g ∈ P} s_g ∏_{g ∉ P} (1 - s_g)`, summing to
`1`. Those with at least `c₂ T` successes of each kind form the success
probability; the rest is the failure probability, removed before any signed
expansion. Expanding the failure factors of a retained pattern gives
`∑_{Q ⊆ 𝒞 ∖ P} (-1)^{|Q|} ∏_{g ∈ P ∪ Q} s_g`, and the product of coins over
a set `S` is `c₁^{|S|} W_{1,q₀}(w) W_{1,q₀}(w+1)` for the active groups `S`.

The clustered inert polynomial likewise expands into monomials
`∏_{(c,i) ∈ S} w_{c,i}`, each a marked weight of `|S|` bands.
-/

namespace Erdos408

open Finset

noncomputable section

/-! ### Products of marked weights -/

/-- A product of `zpow`s of a nonzero number is the `zpow` of the sum. -/
lemma prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) {q : ℝ} (hq : q ≠ 0) (f : ι → ℤ) :
    ∏ i ∈ s, q ^ f i = q ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, zpow_add₀ hq]

/-- A marked weight is the product of its single-group weights. -/
lemma markedWeight_eq_prod {ι : Type*} (s : Finset ι) {q : ℝ} (hq : q ≠ 0)
    (G : ι → Finset ℕ) (n : ℕ) :
    markedWeight s q G n = ∏ i ∈ s, markedWeight {i} q G n := by
  simp only [markedWeight, sum_singleton, card_singleton, prod_singleton]
  rw [prod_mul_distrib, prod_zpow_eq_zpow_sum s hq]
  congr 2
  push_cast
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]

/-- The single-band weight is the marked weight of one band. -/
lemma bandWeight_eq (q x a : ℝ) (n : ℕ) {ι : Type*} (i : ι) (G : ι → Finset ℕ)
    (hG : G i = band x a) : bandWeight q x a n = markedWeight {i} q G n := by
  simp [bandWeight, markedWeight, hG]

/-! ### Expanding products of `1 - y` -/

/-- `∏_{i ∈ s} (1 - y_i) = ∑_{t ⊆ s} (-1)^{|t|} ∏_{i ∈ t} y_i`. -/
lemma prod_one_sub_eq_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (y : ι → ℝ) :
    ∏ i ∈ s, (1 - y i) = ∑ t ∈ s.powerset, (-1) ^ t.card * ∏ i ∈ t, y i := by
  have h := prod_add (fun i => -y i) (fun _ => (1 : ℝ)) s
  simp only [prod_const_one, mul_one, prod_neg] at h
  rw [← h]
  exact prod_congr rfl fun i _ => by ring

/-! ### Success coins -/

/-- The success coin `s_g(w)` with `q₀ = 1/2` at `u = w` and `v = w + 1`. -/
def successCoin (c₁ : ℝ) (g : Finset ℕ) (w : ℕ) : ℝ :=
  c₁ * markedWeight {g} (1 / 2) id w * markedWeight {g} (1 / 2) id (w + 1)

/-- A pattern has many successes: at least `c₂ T` groups of each kind. -/
def ManySuccesses (c₂ x : ℝ) (P : Finset (Finset ℕ)) : Prop :=
  c₂ * logLog x ≤ (P ∩ smallGroups x).card ∧ c₂ * logLog x ≤ (P ∩ bigGroups x).card

/-- Many successes is decided classically. -/
noncomputable instance (c₂ x : ℝ) : DecidablePred (ManySuccesses c₂ x) :=
  fun _ => Classical.dec _

/-- The weight `∏_{g ∈ P} s_g ∏_{g ∈ 𝒞 ∖ P} (1 - s_g)` of the success pattern
`P`. -/
def patternWeight (c₁ x : ℝ) (P : Finset (Finset ℕ)) (w : ℕ) : ℝ :=
  (∏ g ∈ P, successCoin c₁ g w) * ∏ g ∈ candidateGroups x \ P, (1 - successCoin c₁ g w)

/-- The probability of many successes. -/
def successProb (c₁ c₂ x : ℝ) (w : ℕ) : ℝ :=
  ∑ P ∈ (candidateGroups x).powerset with ManySuccesses c₂ x P, patternWeight c₁ x P w

/-- The probability of few successes in either family. -/
def failureProb (c₁ c₂ x : ℝ) (w : ℕ) : ℝ :=
  ∑ P ∈ (candidateGroups x).powerset with ¬ ManySuccesses c₂ x P, patternWeight c₁ x P w

/-- The success and failure probabilities add up to `1`. -/
lemma successProb_add_failureProb (c₁ c₂ x : ℝ) (w : ℕ) :
    successProb c₁ c₂ x w + failureProb c₁ c₂ x w = 1 := by
  rw [successProb, failureProb, sum_filter_add_sum_filter_not]
  have h := prod_add (fun g => successCoin c₁ g w) (fun g => 1 - successCoin c₁ g w)
    (candidateGroups x)
  simp only [add_sub_cancel, prod_const_one] at h
  exact h.symm

/-- With coins in `[0, 1]`, pattern weights are nonnegative. -/
lemma patternWeight_nonneg {c₁ x : ℝ} {w : ℕ}
    (hs : ∀ g ∈ candidateGroups x, 0 ≤ successCoin c₁ g w ∧ successCoin c₁ g w ≤ 1)
    {P : Finset (Finset ℕ)} (hP : P ⊆ candidateGroups x) : 0 ≤ patternWeight c₁ x P w :=
  mul_nonneg (prod_nonneg fun g hg => (hs g (hP hg)).1)
    (prod_nonneg fun g hg => sub_nonneg.2 (hs g (mem_sdiff.1 hg).1).2)

/-- With coins in `[0, 1]`, the success probability lies in `[0, 1]`. -/
lemma successProb_mem_Icc {c₁ c₂ x : ℝ} {w : ℕ}
    (hs : ∀ g ∈ candidateGroups x, 0 ≤ successCoin c₁ g w ∧ successCoin c₁ g w ≤ 1) :
    0 ≤ successProb c₁ c₂ x w ∧ successProb c₁ c₂ x w ≤ 1 := by
  have h₁ : 0 ≤ successProb c₁ c₂ x w :=
    sum_nonneg fun _ hP => patternWeight_nonneg hs (mem_powerset.1 (mem_filter.1 hP).1)
  have h₂ : 0 ≤ failureProb c₁ c₂ x w :=
    sum_nonneg fun _ hP => patternWeight_nonneg hs (mem_powerset.1 (mem_filter.1 hP).1)
  have := successProb_add_failureProb c₁ c₂ x w
  exact ⟨h₁, by linarith⟩

/-- The failure probability is nonnegative when the coins lie in `[0, 1]`. -/
lemma failureProb_nonneg {c₁ c₂ x : ℝ} {w : ℕ}
    (hs : ∀ g ∈ candidateGroups x, 0 ≤ successCoin c₁ g w ∧ successCoin c₁ g w ≤ 1) :
    0 ≤ failureProb c₁ c₂ x w :=
  sum_nonneg fun _ hP => patternWeight_nonneg hs (mem_powerset.1 (mem_filter.1 hP).1)

/-- The product of the coins over `S` is `c₁^{|S|} W_{1,q₀}(w) W_{1,q₀}(w + 1)`. -/
lemma prod_successCoin (c₁ : ℝ) (S : Finset (Finset ℕ)) (w : ℕ) :
    ∏ g ∈ S, successCoin c₁ g w =
      c₁ ^ S.card * markedWeight S (1 / 2) id w * markedWeight S (1 / 2) id (w + 1) := by
  rw [markedWeight_eq_prod S (by norm_num) id w, markedWeight_eq_prod S (by norm_num) id (w + 1),
    ← prod_const, ← prod_mul_distrib, ← prod_mul_distrib]
  rfl

/-- The signed expansion of the success probability:
`∑_{P good} ∑_{Q ⊆ 𝒞 ∖ P} (-1)^{|Q|} c₁^{|P ∪ Q|} W_{1,q₀}(w) W_{1,q₀}(w + 1)`,
with the active set `P ∪ Q`. -/
lemma successProb_eq (c₁ c₂ x : ℝ) (w : ℕ) :
    successProb c₁ c₂ x w =
      ∑ P ∈ (candidateGroups x).powerset with ManySuccesses c₂ x P,
        ∑ Q ∈ (candidateGroups x \ P).powerset, (-1) ^ Q.card * c₁ ^ (P ∪ Q).card *
          (markedWeight (P ∪ Q) (1 / 2) id w * markedWeight (P ∪ Q) (1 / 2) id (w + 1)) := by
  refine sum_congr rfl fun P _ => ?_
  rw [patternWeight, prod_one_sub_eq_sum, mul_sum]
  refine sum_congr rfl fun Q hQ => ?_
  have hPQ : Disjoint P Q := disjoint_of_subset_right (mem_powerset.1 hQ) disjoint_sdiff
  rw [show ∀ a b c d : ℝ, a * b * (c * d) = a * (b * c * d) by intros; ring,
    ← prod_successCoin, prod_union hPQ]
  ring

/-! ### The inert polynomial -/

/-- The monomial `∏_{(c,i) ∈ S} w_{c,i}(n)` of the inert polynomial. -/
def inertMonomial (q : ℝ) (K : ℕ) (x : ℝ) (S : Finset (ℕ × ℕ)) (n : ℕ) : ℝ :=
  ∏ p ∈ S, bandWeight q x (inertExponent K x p.1 p.2) n

/-- The expansion of the clustered inert polynomial into monomials. -/
lemma inertPoly_eq_sum (q cw : ℝ) (K : ℕ) (CN x : ℝ) (n : ℕ) :
    inertPoly q cw K CN x n =
      ∑ U ∈ (range K).powerset, ∑ S ∈ (U ×ˢ range (inertPerCluster K CN x)).powerset,
        (-1) ^ (U.card + S.card) * cw ^ S.card * inertMonomial q K x S n := by
  rw [inertPoly, prod_one_sub_eq_sum]
  refine sum_congr rfl fun U _ => ?_
  rw [← prod_product' (f := fun c i => 1 - cw * bandWeight q x (inertExponent K x c i) n),
    prod_one_sub_eq_sum, mul_sum]
  refine sum_congr rfl fun S _ => ?_
  rw [inertMonomial, prod_mul_distrib, prod_const, pow_add]
  ring

/-- A monomial is the marked weight of its bands, enumerated by `Fin |S|`. -/
lemma inertMonomial_eq (q : ℝ) (hq : q ≠ 0) (K : ℕ) (x : ℝ) (S : Finset (ℕ × ℕ)) (n : ℕ) :
    inertMonomial q K x S n =
      markedWeight Finset.univ q (fun i : Fin S.card =>
        band x (inertExponent K x (S.equivFin.symm i).1.1 (S.equivFin.symm i).1.2)) n := by
  rw [markedWeight_eq_prod _ hq, inertMonomial, ← prod_coe_sort S]
  rw [← (S.equivFin.symm).prod_comp]
  exact prod_congr rfl fun i _ => bandWeight_eq q x _ n i _ rfl

end

end Erdos408
