module

public import Erdos408.Extraction.Allocation.Strip

/-!
# The proxy coefficient and its core

For `v = m₁ ⋯ m_j`, the proxy sum weights `v` by the proxy coefficient
`A_j(v) = ∑_{m₁ ⋯ m_j = v} ∏ a_j(m_i)`. The stripped proxy splits as
`a_j(m) = b(m̄) j^{-Ω_P(m)}` with `b(e) = [e > x^γ] [e Y-rough] / (D_j log e)`,
so the allocation identity gives `A_j(v) = G_j(v) ρ_j(v)` with the core
`G_j(v) = ∑_{e₁ ⋯ e_j = v̄} ∏ b(e_i)` and the allocation factor
`ρ_j(v) = d_j(v_P) j^{-Ω_P(v)} ∈ [0, 1]`, equal to `1` unless a candidate
square divides `v`. The core depends only on `v̄`, so it is invariant
under every candidate prime, active or not.
-/

@[expose] public section

namespace Erdos408

open Finset

noncomputable section

/-- The candidate groups `𝒞`, small and big. -/
def candidateGroups (x : ℝ) : Finset (Finset ℕ) :=
  smallGroups x ∪ bigGroups x

/-- The factor `b(e) = [e > x^γ] [e Y-rough] / (D_j log e)` of the core. -/
def coreFactor (x γ : ℝ) (j e : ℕ) : ℝ :=
  if x ^ γ < e ∧ ∀ p ∈ e.primeFactors, proxyCutoff x < p then
    1 / (dampedDensity x j * Real.log e)
  else 0

/-- The core `G_j(v) = ∑_{e₁ ⋯ e_j = v̄} ∏ b(e_i)`. -/
def proxyCore (x γ : ℝ) (j v : ℕ) : ℝ :=
  ∑ e ∈ Nat.finMulAntidiag j (candidateStrip x v), ∏ i, coreFactor x γ j (e i)

/-- The proxy coefficient `A_j(v) = ∑_{m₁ ⋯ m_j = v} ∏ a_j(m_i)`. -/
def proxyCoeff (x γ : ℝ) (j v : ℕ) : ℝ :=
  ∑ m ∈ Nat.finMulAntidiag j v, ∏ i, strippedProxy x γ j (m i)

/-- The allocation factor `ρ_j(v) = d_j(v_P) j^{-Ω_P(v)}`. -/
def allocationFactor (x : ℝ) (j v : ℕ) : ℝ :=
  (Nat.finMulAntidiag j (keepPrimes (candidatePrimes x) v)).card *
    ((j : ℝ)⁻¹) ^ candidateOmega x v

/-! ### The allocation identity -/

/-- `Ω_P(n) = Ω(n_P)`. -/
lemma candidateOmega_eq_cardFactors (x : ℝ) (n : ℕ) :
    candidateOmega x n = ArithmeticFunction.cardFactors (keepPrimes (candidatePrimes x) n) := by
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization, factorization_keepPrimes,
    Finsupp.sum, Finsupp.support_filter, Nat.support_factorization, candidateOmega]
  refine sum_congr rfl fun p hp => ?_
  rw [Finsupp.filter_apply_pos _ _ (mem_filter.1 hp).2]

/-- `Ω_P(n) = Ω_P(n_P)`. -/
lemma candidateOmega_keepPrimes (x : ℝ) (n : ℕ) :
    candidateOmega x (keepPrimes (candidatePrimes x) n) = candidateOmega x n := by
  rw [candidateOmega_eq_cardFactors, candidateOmega_eq_cardFactors]
  congr 1
  refine Nat.eq_of_factorization_eq (keepPrimes_ne_zero _ _) (keepPrimes_ne_zero _ _)
    fun p => ?_
  rw [factorization_keepPrimes, factorization_keepPrimes]
  simp only [Finsupp.filter_apply]
  split_ifs <;> rfl

/-- The stripped proxy splits as `a_j(m) = b(m̄) j^{-Ω_P(m_P)}`. -/
lemma strippedProxy_eq (x γ : ℝ) (j m : ℕ) :
    strippedProxy x γ j m = coreFactor x γ j (candidateStrip x m) *
      ((j : ℝ)⁻¹) ^ candidateOmega x (keepPrimes (candidatePrimes x) m) := by
  rw [candidateOmega_keepPrimes]
  unfold strippedProxy coreFactor dampedWeight
  split_ifs with h₁ h₂ h₃ h₃ <;> first | (exfalso; tauto) | ring

/-- `Ω` is additive over products of nonzero factors. -/
lemma cardFactors_prod {ι : Type*} (s : Finset ι) {f : ι → ℕ} (hf : ∀ i ∈ s, f i ≠ 0) :
    ArithmeticFunction.cardFactors (∏ i ∈ s, f i) =
      ∑ i ∈ s, ArithmeticFunction.cardFactors (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, ArithmeticFunction.cardFactors_mul
      (hf a (mem_insert_self a s)) (prod_ne_zero_iff.2 fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

/-- The allocation identity `A_j(v) = G_j(v) ρ_j(v)`. -/
theorem proxyCoeff_eq (x γ : ℝ) (j : ℕ) {v : ℕ} (hv : v ≠ 0) :
    proxyCoeff x γ j v = proxyCore x γ j v * allocationFactor x j v := by
  simp only [proxyCoeff, proxyCore, strippedProxy_eq, candidateStrip]
  rw [sum_finMulAntidiag_eq_mul _ _ hv (coreFactor x γ j)
    fun c => ((j : ℝ)⁻¹) ^ candidateOmega x c]
  congr 1
  rw [allocationFactor, ← nsmul_eq_mul, ← sum_const]
  refine sum_congr rfl fun c hc => ?_
  rw [prod_pow_eq_pow_sum]
  congr 1
  have hc0 := Nat.ne_zero_of_mem_finMulAntidiag hc
  simp_rw [candidateOmega_eq_cardFactors]
  rw [← cardFactors_prod _ fun i _ => keepPrimes_ne_zero _ _, keepPrimes_prod hc0,
    Nat.prod_eq_of_mem_finMulAntidiag hc, ← candidateOmega_eq_cardFactors,
    ← candidateOmega_eq_cardFactors, candidateOmega_keepPrimes]

/-- The allocation factor is nonnegative. -/
lemma allocationFactor_nonneg (x : ℝ) (j v : ℕ) : 0 ≤ allocationFactor x j v := by
  unfold allocationFactor
  positivity

/-- The allocation factor is at most `1`, since `d_j(n) ≤ j^{Ω(n)}`. -/
lemma allocationFactor_le_one (x : ℝ) {j : ℕ} (hj : 1 ≤ j) (v : ℕ) :
    allocationFactor x j v ≤ 1 := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  rw [allocationFactor, candidateOmega_eq_cardFactors, inv_pow, ← div_eq_mul_inv,
    div_le_one (by positivity)]
  exact_mod_cast card_finMulAntidiag_le j _

/-- Off the candidate-square multiples the allocation factor is exactly `1`:
`j^{ω_P(v)} j^{-ω_P(v)} = 1`. -/
lemma allocationFactor_eq_one (x : ℝ) {j : ℕ} (hj : 1 ≤ j) {v : ℕ}
    (hv : Squarefree (keepPrimes (candidatePrimes x) v)) : allocationFactor x j v = 1 := by
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  rw [allocationFactor, Nat.card_finMulAntidiag_of_squarefree hv,
    (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
      (keepPrimes_ne_zero _ _)).2 hv, ← candidateOmega_eq_cardFactors]
  push_cast
  rw [← mul_pow, mul_inv_cancel₀ hj0, one_pow]

/-- If the candidate part of `v ≠ 0` is not squarefree, then `p² ∣ v` for a
candidate prime `p`. -/
lemma exists_sq_dvd_of_not_squarefree (x : ℝ) {v : ℕ} (hv : v ≠ 0)
    (h : ¬ Squarefree (keepPrimes (candidatePrimes x) v)) :
    ∃ p ∈ candidatePrimes x, p * p ∣ v := by
  rw [Nat.squarefree_iff_prime_squarefree] at h
  push Not at h
  obtain ⟨p, hp, hpp⟩ := h
  refine ⟨p, mem_of_mem_primeFactors_keepPrimes (Nat.mem_primeFactors.2
    ⟨hp, (dvd_mul_right p p).trans hpp, keepPrimes_ne_zero _ _⟩), hpp.trans ?_⟩
  exact ⟨stripPrimes _ v, by rw [mul_comm, stripPrimes_mul_keepPrimes _ hv]⟩

/-! ### Positivity and invariance -/

/-- The candidate primes are prime. -/
lemma prime_of_mem_candidatePrimes {x : ℝ} {p : ℕ} (hp : p ∈ candidatePrimes x) :
    p.Prime := by
  obtain ⟨g, hg, hpg⟩ := mem_biUnion.1 hp
  rcases mem_union.1 hg with hg | hg <;>
  · obtain ⟨i, -, rfl⟩ := mem_image.1 hg
    exact (mem_filter.1 hpg).2

/-- The damped density is positive for `j ≥ 1`. -/
lemma dampedDensity_pos (x : ℝ) {j : ℕ} (hj : 1 ≤ j) : 0 < dampedDensity x j := by
  have hj1 : (j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hj)
  refine mul_pos (prod_pos fun p hp => ?_) (prod_pos fun p hp => inv_pos.2 ?_)
  · have hp2 : (2 : ℝ) ≤ p := by
      have := (mem_filter.1 hp).1
      rw [mem_Icc, Nat.ceil_le] at this
      exact this.1
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_candidatePrimes hp).two_le
    rw [sub_pos, div_lt_one (by linarith)]
    linarith

/-- The core factor is nonnegative when `x^γ ≥ 1`. -/
lemma coreFactor_nonneg {x γ : ℝ} {j : ℕ} (hj : 1 ≤ j) (hxγ : 1 ≤ x ^ γ) (e : ℕ) :
    0 ≤ coreFactor x γ j e := by
  unfold coreFactor
  split_ifs with h
  · have := dampedDensity_pos x hj
    have : 0 < Real.log e := Real.log_pos (by linarith [h.1])
    positivity
  · exact le_rfl

/-- The core is nonnegative when `x^γ ≥ 1`. -/
lemma proxyCore_nonneg {x γ : ℝ} {j : ℕ} (hj : 1 ≤ j) (hxγ : 1 ≤ x ^ γ) (v : ℕ) :
    0 ≤ proxyCore x γ j v :=
  sum_nonneg fun _ _ => prod_nonneg fun _ _ => coreFactor_nonneg hj hxγ _

/-- The core is invariant under stripping any set of candidate primes. -/
lemma proxyCore_stripPrimes {x γ : ℝ} {j : ℕ} {S : Finset ℕ} (hS : S ⊆ candidatePrimes x)
    (v : ℕ) : proxyCore x γ j (stripPrimes S v) = proxyCore x γ j v := by
  rw [proxyCore, proxyCore, candidateStrip, candidateStrip, stripPrimes_stripPrimes hS]

end

end Erdos408
