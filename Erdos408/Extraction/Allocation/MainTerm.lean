import Erdos408.Extraction.Allocation.TwoSided

/-!
# The signed expansion of the retained patterns

On the retained patterns the clipped-core sum
`∑_w Φ(w/x) P(w) (f_𝔟 - C_𝔟)(w) G(w + 1) S(w)` expands into
`∑_{(P, Q)} ∑_{(U, S)} ± c₁^{|P ∪ Q|} c_w^{|S|} x · Σ(P ∪ Q, S)`, where
`(P, Q)` runs over the retained patterns `P` and the expanded failure sets
`Q ⊆ 𝒞 ∖ P`, `(U, S)` over the monomials of the inert polynomial, and
`Σ(Act, S)` is the two-sided correlation sum of `TwoSidedCorrelation`. There
are at most `4^{|𝒞|} · 2^K 2^{K N/K}` terms, each with coefficient at most
`1` in absolute value.
-/

namespace Erdos408

open Finset

noncomputable section

/-- The pairs `(P, Q)`: a retained pattern `P` and a set `Q ⊆ 𝒞 ∖ P` of
expanded failure factors. -/
def patternIndex (c₂ x : ℝ) : Finset (Σ _ : Finset (Finset ℕ), Finset (Finset ℕ)) :=
  ((candidateGroups x).powerset.filter (ManySuccesses c₂ x)).sigma
    fun P => (candidateGroups x \ P).powerset

/-- The monomials `(U, S)` of the inert polynomial. -/
def monomialIndex (K : ℕ) (CN x : ℝ) : Finset (Σ _ : Finset ℕ, Finset (ℕ × ℕ)) :=
  (range K).powerset.sigma fun U => (U ×ˢ range (inertPerCluster K CN x)).powerset

/-- The coefficient `(-1)^{|Q|} c₁^{|P ∪ Q|} (-1)^{|U| + |S|} c_w^{|S|}` of a
term. -/
def expansionCoeff (c₁ cw : ℝ) (i : Σ _ : Finset (Finset ℕ), Finset (Finset ℕ))
    (m : Σ _ : Finset ℕ, Finset (ℕ × ℕ)) : ℝ :=
  (-1) ^ i.2.card * c₁ ^ (i.1 ∪ i.2).card * ((-1) ^ (m.1.card + m.2.card) * cw ^ m.2.card)

/-- The signed expansion of the clipped-core sum on the retained patterns. -/
theorem sum_mul_successProb_eq (q cw : ℝ) (hq : q ≠ 0) (K : ℕ) (CN : ℝ) {x : ℝ} (hx : 0 < x)
    (κ : ℝ) (Φ : ℝ → ℝ) {k : ℕ} (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) (G : ℕ → ℝ)
    (c₁ c₂ : ℝ) :
    ∑ w ∈ Icc 1 ⌊κ * x⌋₊,
        Φ (w / x) * endpoint q cw K CN x u v B w * G (w + 1) * successProb c₁ c₂ x w =
      ∑ i ∈ patternIndex c₂ x, ∑ m ∈ monomialIndex K CN x,
        expansionCoeff c₁ cw i m * x * twoSidedSum q K x κ Φ m.2 u v B G (i.1 ∪ i.2) := by
  have hterm : ∀ w ∈ Icc 1 ⌊κ * x⌋₊,
      Φ (w / x) * endpoint q cw K CN x u v B w * G (w + 1) * successProb c₁ c₂ x w =
        ∑ i ∈ patternIndex c₂ x, ∑ m ∈ monomialIndex K CN x, expansionCoeff c₁ cw i m * x *
          ((fun y => y * Φ y) (w / x) / w *
            (markedWeight Finset.univ q (fun i => band x (monomialExponents K x m.2 i)) w *
              (slotCount x u v B w - slotMean x u v B)) *
            G (w + 1) * markedWeight (i.1 ∪ i.2) (1 / 2) id w *
            markedWeight (i.1 ∪ i.2) (1 / 2) id (w + 1)) := by
    intro w hw
    have hw0 : (w : ℝ) ≠ 0 := by
      have := (mem_Icc.1 hw).1
      positivity
    have hΦw : Φ (w / x) = x * ((w / x * Φ (w / x)) / w) := by
      field_simp
    rw [successProb_eq, sum_sigma', endpoint, inertPoly_eq_sum, sum_sigma']
    simp only [sum_mul, mul_sum]
    rw [patternIndex, monomialIndex]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro m _
    rw [inertMonomial_eq q hq, expansionCoeff]
    conv_lhs => rw [hΦw]
    simp only [monomialExponents]
    ring
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [twoSidedSum, mul_sum]
  rfl

/-- There are at most `4^{|𝒞|}` pairs `(P, Q)`. -/
lemma card_patternIndex_le (c₂ x : ℝ) :
    (patternIndex c₂ x).card ≤ 4 ^ (candidateGroups x).card := by
  rw [patternIndex, card_sigma]
  calc ∑ P ∈ (candidateGroups x).powerset.filter (ManySuccesses c₂ x),
        (candidateGroups x \ P).powerset.card
      ≤ ∑ _P ∈ (candidateGroups x).powerset, 2 ^ (candidateGroups x).card := by
        refine (sum_le_sum_of_subset (filter_subset _ _)).trans (sum_le_sum fun P _ => ?_)
        rw [card_powerset]
        exact Nat.pow_le_pow_right (by norm_num) (card_le_card sdiff_subset)
    _ = 4 ^ (candidateGroups x).card := by
        rw [sum_const, card_powerset, smul_eq_mul, ← mul_pow]
        norm_num

/-- There are at most `2^K 2^{K N/K}` monomials. -/
lemma card_monomialIndex_le (K : ℕ) (CN x : ℝ) :
    (monomialIndex K CN x).card ≤ 2 ^ K * 2 ^ (K * inertPerCluster K CN x) := by
  rw [monomialIndex, card_sigma]
  calc ∑ U ∈ (range K).powerset, (U ×ˢ range (inertPerCluster K CN x)).powerset.card
      ≤ ∑ _U ∈ (range K).powerset, 2 ^ (K * inertPerCluster K CN x) := by
        refine sum_le_sum fun U hU => ?_
        rw [card_powerset, card_product, card_range]
        refine Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ ?_)
        simpa using card_le_card (mem_powerset.1 hU)
    _ = _ := by rw [sum_const, card_powerset, card_range, smul_eq_mul]

/-- With `0 ≤ c₁, c_w ≤ 1`, the coefficients are at most `1`. -/
lemma abs_expansionCoeff_le {c₁ cw : ℝ} (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1) (hcw : 0 ≤ cw)
    (hcw' : cw ≤ 1) (i : Σ _ : Finset (Finset ℕ), Finset (Finset ℕ))
    (m : Σ _ : Finset ℕ, Finset (ℕ × ℕ)) : |expansionCoeff c₁ cw i m| ≤ 1 := by
  simp only [expansionCoeff, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg hc₁, abs_of_nonneg hcw]
  have h1 := pow_le_one₀ (n := (i.1 ∪ i.2).card) hc₁ hc₁'
  have h2 := pow_le_one₀ (n := m.2.card) hcw hcw'
  have h3 : 0 ≤ cw ^ m.2.card := by positivity
  nlinarith

/-- The signed expansion is at most the number of terms times `x C* L^{-A}`. -/
theorem abs_sum_expansion_le {c₁ cw c₂ x : ℝ} {K : ℕ} {CN : ℝ} (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1)
    (hcw : 0 ≤ cw) (hcw' : cw ≤ 1) (hx : 0 ≤ x) {F : (Σ _ : Finset (Finset ℕ), Finset (Finset ℕ)) →
      (Σ _ : Finset ℕ, Finset (ℕ × ℕ)) → ℝ} {R : ℝ}
    (hF : ∀ i ∈ patternIndex c₂ x, ∀ m ∈ monomialIndex K CN x, |F i m| ≤ R) :
    |∑ i ∈ patternIndex c₂ x, ∑ m ∈ monomialIndex K CN x, expansionCoeff c₁ cw i m * x * F i m| ≤
      (patternIndex c₂ x).card * (monomialIndex K CN x).card * (x * R) := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_assoc, ← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun i hi => (abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun m hm => ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hx]
  have h1 := abs_expansionCoeff_le hc₁ hc₁' hcw hcw' i m
  have h2 := hF i hi m hm
  have hR : 0 ≤ R := (abs_nonneg _).trans h2
  calc |expansionCoeff c₁ cw i m| * x * |F i m| ≤ 1 * x * R := by gcongr
    _ = x * R := by ring

end

end Erdos408
