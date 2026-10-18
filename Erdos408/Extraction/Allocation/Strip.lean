module

public import Erdos408.Extraction.Defs
public import Mathlib.Algebra.Order.Antidiag.Nat

/-!
# The allocation identity

Write `n_P` for the part of `n` made of the primes of a set `P`, so that
`n = n̄ · n_P` with `n̄ = stripPrimes P n`. A `d`-fold factorization of `n`
is the same as a pair of `d`-fold factorizations of `n̄` and of `n_P`
(`sum_finMulAntidiag_eq_mul`). For the stripped proxy, whose coefficient
splits as a function of `m̄` times `j^{-Ω_P(m)}`, this gives the exact
allocation identity behind the allocation step of *The normal order of the
number of iterations of Euler's function* (Plasma AI, 2026), §6.3:

  `∑_{m₁ ⋯ m_j = v} ∏ a_j(m_i) = G_j(v) · d_j(v_P) j^{-Ω_P(v)}`,

where `G_j(v) = ∑_{e₁ ⋯ e_j = v̄} ∏ b(e_i)` is the core. The allocation
factor `d_j(v_P) j^{-Ω_P(v)}` lies in `[0, 1]` and is exactly `1` off the
candidate-square multiples, since then `d_j(v_P) = j^{ω(v_P)} = j^{Ω_P(v)}`.
-/

@[expose] public section

namespace Erdos408

open Finset

noncomputable section

/-! ### Splitting off the primes of a set -/

/-- `n_P`: the part of `n` made of the primes of `P`, with multiplicity. -/
def keepPrimes (P : Finset ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors with p ∈ P, p ^ n.factorization p

/-- A product of prime powers over a filter of the prime factors is the
`Finsupp` product of the filtered factorization. -/
private lemma prod_filter_eq_prod (q : ℕ → Prop) [DecidablePred q] (n : ℕ) :
    ∏ p ∈ n.primeFactors with q p, p ^ n.factorization p =
      (n.factorization.filter q).prod fun p k => p ^ k := by
  rw [Finsupp.prod, Finsupp.support_filter, Nat.support_factorization]
  refine prod_congr rfl fun p hp => ?_
  rw [Finsupp.filter_apply_pos _ _ (mem_filter.1 hp).2]

/-- The factorization of a filtered product of prime powers is the filtered
factorization. -/
private lemma factorization_prod_filter (q : ℕ → Prop) [DecidablePred q] (n : ℕ) :
    (∏ p ∈ n.primeFactors with q p, p ^ n.factorization p).factorization =
      n.factorization.filter q := by
  rw [prod_filter_eq_prod]
  refine Nat.factorization_prod_pow_eq_self fun p hp => ?_
  rw [Finsupp.support_filter, Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1

/-- The factorization of `n̄` is that of `n` off `P`. -/
lemma factorization_stripPrimes (P : Finset ℕ) (n : ℕ) :
    (stripPrimes P n).factorization = n.factorization.filter (· ∉ P) :=
  factorization_prod_filter _ n

/-- The factorization of `n_P` is that of `n` on `P`. -/
lemma factorization_keepPrimes (P : Finset ℕ) (n : ℕ) :
    (keepPrimes P n).factorization = n.factorization.filter (· ∈ P) :=
  factorization_prod_filter _ n

/-- `n̄` is never zero. -/
lemma stripPrimes_ne_zero (P : Finset ℕ) (n : ℕ) : stripPrimes P n ≠ 0 :=
  prod_ne_zero_iff.2 fun _ hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).ne_zero

/-- `n_P` is never zero. -/
lemma keepPrimes_ne_zero (P : Finset ℕ) (n : ℕ) : keepPrimes P n ≠ 0 :=
  prod_ne_zero_iff.2 fun _ hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).ne_zero

/-- `n = n̄ · n_P` for `n ≠ 0`. -/
lemma stripPrimes_mul_keepPrimes (P : Finset ℕ) {n : ℕ} (hn : n ≠ 0) :
    stripPrimes P n * keepPrimes P n = n := by
  refine Nat.eq_of_factorization_eq
    (mul_ne_zero (stripPrimes_ne_zero P n) (keepPrimes_ne_zero P n)) hn fun p => ?_
  rw [Nat.factorization_mul (stripPrimes_ne_zero P n) (keepPrimes_ne_zero P n),
    factorization_stripPrimes, factorization_keepPrimes, Finsupp.add_apply,
    Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases h : p ∈ P <;> simp [h]

/-- A number whose factorization is supported off `P` (or on `P`) is
recovered from its factorization filtered accordingly. -/
private lemma eq_of_factorization_filter {q : ℕ → Prop} [DecidablePred q] {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hqa : ∀ p ∈ a.primeFactors, q p)
    (hqb : ∀ p ∈ b.primeFactors, ¬ q p) :
    (a * b).factorization.filter q = a.factorization := by
  rw [Nat.factorization_mul ha hb, Finsupp.filter_add]
  ext p
  rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases h : q p
  · have : b.factorization p = 0 := by
      by_contra hne
      exact hqb p (Nat.support_factorization b ▸ Finsupp.mem_support_iff.2 hne) h
    simp [h, this]
  · have : a.factorization p = 0 := by
      by_contra hne
      exact h (hqa p (Nat.support_factorization a ▸ Finsupp.mem_support_iff.2 hne))
    simp [h, this]

/-- If `e` has no prime of `P` and `c` only primes of `P`, then the strip of
`e c` is `e` and its `P`-part is `c`. -/
lemma stripPrimes_keepPrimes_mul {P : Finset ℕ} {e c : ℕ} (he : e ≠ 0) (hc : c ≠ 0)
    (heP : ∀ p ∈ e.primeFactors, p ∉ P) (hcP : ∀ p ∈ c.primeFactors, p ∈ P) :
    stripPrimes P (e * c) = e ∧ keepPrimes P (e * c) = c := by
  constructor
  · refine Nat.eq_of_factorization_eq (stripPrimes_ne_zero P _) he fun p => ?_
    rw [factorization_stripPrimes, eq_of_factorization_filter he hc heP
      fun p hp h => h (hcP p hp)]
  · refine Nat.eq_of_factorization_eq (keepPrimes_ne_zero P _) hc fun p => ?_
    rw [factorization_keepPrimes, mul_comm, eq_of_factorization_filter hc he hcP
      fun p hp h => heP p hp h]

/-- The prime factors of `n̄` avoid `P`. -/
lemma not_mem_of_mem_primeFactors_stripPrimes {P : Finset ℕ} {n p : ℕ}
    (hp : p ∈ (stripPrimes P n).primeFactors) : p ∉ P := by
  rw [← Nat.support_factorization, factorization_stripPrimes, Finsupp.support_filter] at hp
  exact (mem_filter.1 hp).2

/-- The prime factors of `n_P` lie in `P`. -/
lemma mem_of_mem_primeFactors_keepPrimes {P : Finset ℕ} {n p : ℕ}
    (hp : p ∈ (keepPrimes P n).primeFactors) : p ∈ P := by
  rw [← Nat.support_factorization, factorization_keepPrimes, Finsupp.support_filter] at hp
  exact (mem_filter.1 hp).2

/-- The prime factors of a divisor of `n̄` avoid `P`. -/
lemma not_mem_of_dvd_stripPrimes {P : Finset ℕ} {n e p : ℕ} (he : e ∣ stripPrimes P n)
    (hp : p ∈ e.primeFactors) : p ∉ P :=
  not_mem_of_mem_primeFactors_stripPrimes
    (Nat.primeFactors_mono he (stripPrimes_ne_zero P n) hp)

/-- The prime factors of a divisor of `n_P` lie in `P`. -/
lemma mem_of_dvd_keepPrimes {P : Finset ℕ} {n c p : ℕ} (hc : c ∣ keepPrimes P n)
    (hp : p ∈ c.primeFactors) : p ∈ P :=
  mem_of_mem_primeFactors_keepPrimes (Nat.primeFactors_mono hc (keepPrimes_ne_zero P n) hp)

/-- The strip of a product of nonzero factors is the product of the strips. -/
lemma stripPrimes_prod {P : Finset ℕ} {d : ℕ} {m : Fin d → ℕ} (hm : ∀ i, m i ≠ 0) :
    ∏ i, stripPrimes P (m i) = stripPrimes P (∏ i, m i) := by
  refine Nat.eq_of_factorization_eq (prod_ne_zero_iff.2 fun i _ => stripPrimes_ne_zero P _)
    (stripPrimes_ne_zero P _) fun p => ?_
  rw [Nat.factorization_prod fun i _ => stripPrimes_ne_zero P _, factorization_stripPrimes,
    Nat.factorization_prod fun i _ => hm i, Finsupp.filter_sum]
  simp only [factorization_stripPrimes]

/-- The `P`-part of a product of nonzero factors is the product of the
`P`-parts. -/
lemma keepPrimes_prod {P : Finset ℕ} {d : ℕ} {m : Fin d → ℕ} (hm : ∀ i, m i ≠ 0) :
    ∏ i, keepPrimes P (m i) = keepPrimes P (∏ i, m i) := by
  refine Nat.eq_of_factorization_eq (prod_ne_zero_iff.2 fun i _ => keepPrimes_ne_zero P _)
    (keepPrimes_ne_zero P _) fun p => ?_
  rw [Nat.factorization_prod fun i _ => keepPrimes_ne_zero P _, factorization_keepPrimes,
    Nat.factorization_prod fun i _ => hm i, Finsupp.filter_sum]
  simp only [factorization_keepPrimes]

/-- Stripping a subset first does not change the strip. -/
lemma stripPrimes_stripPrimes {P Q : Finset ℕ} (hQP : Q ⊆ P) (n : ℕ) :
    stripPrimes P (stripPrimes Q n) = stripPrimes P n := by
  refine Nat.eq_of_factorization_eq (stripPrimes_ne_zero P _) (stripPrimes_ne_zero P _)
    fun p => ?_
  rw [factorization_stripPrimes, factorization_stripPrimes, factorization_stripPrimes,
    Finsupp.filter_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases h : p ∈ P
  · simp [h]
  · have hq : p ∉ Q := fun hq => h (hQP hq)
    simp [h, hq]

/-! ### Splitting factorizations -/

/-- A `d`-fold factorization of `n` is a pair of `d`-fold factorizations of
`n̄` and of `n_P`. -/
theorem sum_finMulAntidiag_eq_mul (P : Finset ℕ) (d : ℕ) {n : ℕ} (hn : n ≠ 0)
    (φ ψ : ℕ → ℝ) :
    ∑ m ∈ Nat.finMulAntidiag d n, ∏ i, φ (stripPrimes P (m i)) * ψ (keepPrimes P (m i)) =
      (∑ e ∈ Nat.finMulAntidiag d (stripPrimes P n), ∏ i, φ (e i)) *
        ∑ c ∈ Nat.finMulAntidiag d (keepPrimes P n), ∏ i, ψ (c i) := by
  rw [sum_mul_sum, ← sum_product']
  simp_rw [← prod_mul_distrib]
  refine sum_nbij' (fun m => (fun i => stripPrimes P (m i), fun i => keepPrimes P (m i)))
    (fun ec i => ec.1 i * ec.2 i) ?_ ?_ ?_ ?_ fun _ _ => rfl
  · intro m hm
    have hm' := Nat.ne_zero_of_mem_finMulAntidiag hm
    have hprod := Nat.prod_eq_of_mem_finMulAntidiag hm
    simp only [mem_product, Nat.mem_finMulAntidiag]
    exact ⟨⟨by rw [stripPrimes_prod hm', hprod], stripPrimes_ne_zero P n⟩,
      by rw [keepPrimes_prod hm', hprod], keepPrimes_ne_zero P n⟩
  · rintro ⟨e, c⟩ hec
    simp only [mem_product, Nat.mem_finMulAntidiag] at hec ⊢
    refine ⟨?_, hn⟩
    rw [prod_mul_distrib, hec.1.1, hec.2.1, stripPrimes_mul_keepPrimes P hn]
  · intro m hm
    funext i
    exact stripPrimes_mul_keepPrimes P (Nat.ne_zero_of_mem_finMulAntidiag hm i)
  · rintro ⟨e, c⟩ hec
    simp only [mem_product] at hec
    have h : ∀ i, stripPrimes P (e i * c i) = e i ∧ keepPrimes P (e i * c i) = c i :=
      fun i => stripPrimes_keepPrimes_mul (Nat.ne_zero_of_mem_finMulAntidiag hec.1 i)
        (Nat.ne_zero_of_mem_finMulAntidiag hec.2 i)
        (fun p hp => not_mem_of_dvd_stripPrimes (Nat.dvd_of_mem_finMulAntidiag hec.1 i) hp)
        (fun p hp => mem_of_dvd_keepPrimes (Nat.dvd_of_mem_finMulAntidiag hec.2 i) hp)
    simp only [Prod.mk.injEq]
    exact ⟨funext fun i => (h i).1, funext fun i => (h i).2⟩

/-- There are at most `d^{Ω(n)}` ways to write `n` as a product of `d`
factors. -/
theorem card_finMulAntidiag_le (d : ℕ) :
    ∀ n : ℕ, (Nat.finMulAntidiag d n).card ≤ d ^ ArithmeticFunction.cardFactors n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp [Nat.finMulAntidiag_zero_right]
      · simp [Nat.finMulAntidiag_one]
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    obtain ⟨m, rfl⟩ := hpn
    have hm : m ≠ 0 := by rintro rfl; omega
    have hlt : m < p * m := lt_mul_left (Nat.pos_of_ne_zero hm) hp.one_lt
    rw [ArithmeticFunction.cardFactors_mul hp.ne_zero hm,
      ArithmeticFunction.cardFactors_apply_prime hp, add_comm, pow_succ']
    -- every factorization of `p m` multiplies one factor of a factorization of `m` by `p`
    calc (Nat.finMulAntidiag d (p * m)).card
        ≤ ((univ : Finset (Fin d)) ×ˢ Nat.finMulAntidiag d m).card := by
          refine card_le_card_of_surjOn
            (fun ig => Function.update ig.2 ig.1 (p * ig.2 ig.1)) fun f hf => ?_
          have hf' := Nat.prod_eq_of_mem_finMulAntidiag hf
          obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1
            (hf' ▸ dvd_mul_right p m)
          obtain ⟨a, ha⟩ := hi
          refine ⟨(i, Function.update f i a), ?_, ?_⟩
          · simp only [coe_product, coe_univ, Set.mem_prod, Set.mem_univ, mem_coe,
              Nat.mem_finMulAntidiag, true_and]
            refine ⟨?_, hm⟩
            rw [← mul_prod_erase univ f (mem_univ i), ha, mul_assoc] at hf'
            rw [prod_update_of_mem (mem_univ i), ← Nat.eq_of_mul_eq_mul_left hp.pos hf']
            congr 1
            exact prod_congr (by ext; simp) fun _ _ => rfl
          · simp [← ha]
      _ ≤ d * d ^ ArithmeticFunction.cardFactors m := by
          rw [card_product, card_univ, Fintype.card_fin]
          exact Nat.mul_le_mul_left _ (ih m hlt)

end

end Erdos408
