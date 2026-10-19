module

public import Erdos408.Extraction.TypeII.Euler
public import Erdos408.Extraction.TypeII.PrimeSums

/-!
# The damped weight is completely multiplicative

`n = n̄ · n_P`, where `n̄` strips the candidate primes and `n_P` is the
candidate part, and `log n = log n̄ + ∑_{p ∈ P} v_p(n) log p`. The damped weight
`g_j(n) = [n̄ Y-rough] j^{-Ω_P(n)}` is the completely multiplicative function
with prime values `1/j` on candidate primes, `0` on the other primes `≤ Y`,
and `1` above `Y`.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real

/-! ### Stripping a set of primes -/

section Strip

variable (P : Finset ℕ)

/-- The part of `n` made of the primes of `P`. -/
noncomputable def partPrimes (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors with p ∈ P, p ^ n.factorization p

theorem stripPrimes_eq_prod (n : ℕ) :
    stripPrimes P n = (n.factorization.filter (· ∉ P)).prod (· ^ ·) := by
  rw [Finsupp.prod_filter_index, Finsupp.support_filter, Nat.support_factorization]
  rfl

theorem factorization_stripPrimes (n : ℕ) :
    (stripPrimes P n).factorization = n.factorization.filter (· ∉ P) := by
  rw [stripPrimes_eq_prod]
  refine Nat.prod_pow_factorization_eq_self fun p hp => ?_
  rw [Finsupp.support_filter, mem_filter, Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors hp.1

theorem primeFactors_stripPrimes (n : ℕ) :
    (stripPrimes P n).primeFactors = n.primeFactors.filter (· ∉ P) := by
  rw [← Nat.support_factorization, factorization_stripPrimes, Finsupp.support_filter,
    Nat.support_factorization]

theorem stripPrimes_ne_zero (n : ℕ) : stripPrimes P n ≠ 0 := by
  unfold stripPrimes
  exact prod_ne_zero_iff.2 fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).ne_zero

theorem partPrimes_ne_zero (n : ℕ) : partPrimes P n ≠ 0 := by
  unfold partPrimes
  exact prod_ne_zero_iff.2 fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).ne_zero

/-- `n = n̄ · n_P`. -/
theorem stripPrimes_mul_partPrimes {n : ℕ} (hn : n ≠ 0) :
    stripPrimes P n * partPrimes P n = n := by
  have h := Finsupp.prod_filter_mul_prod_filter_not (f := n.factorization) (p := (· ∉ P))
    (g := (· ^ ·))
  have hpart : (n.factorization.filter fun a => ¬a ∉ P).prod (· ^ ·) = partPrimes P n := by
    rw [Finsupp.prod_filter_index, Finsupp.support_filter, Nat.support_factorization]
    unfold partPrimes
    simp only [not_not]
  rw [Nat.prod_factorization_pow_eq_self hn, ← stripPrimes_eq_prod, hpart] at h
  exact h

theorem stripPrimes_dvd (n : ℕ) : stripPrimes P n ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero _
  exact Dvd.intro _ (stripPrimes_mul_partPrimes P hn)

theorem stripPrimes_le {n : ℕ} (hn : n ≠ 0) : stripPrimes P n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (stripPrimes_dvd P n)

theorem partPrimes_eq_prod (n : ℕ) :
    partPrimes P n = (n.factorization.filter (· ∈ P)).prod (· ^ ·) := by
  rw [Finsupp.prod_filter_index, Finsupp.support_filter, Nat.support_factorization]
  rfl

theorem factorization_partPrimes (n : ℕ) :
    (partPrimes P n).factorization = n.factorization.filter (· ∈ P) := by
  rw [partPrimes_eq_prod]
  refine Nat.prod_pow_factorization_eq_self fun p hp => ?_
  rw [Finsupp.support_filter, mem_filter, Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors hp.1

theorem primeFactors_partPrimes (n : ℕ) :
    (partPrimes P n).primeFactors = n.primeFactors.filter (· ∈ P) := by
  rw [← Nat.support_factorization, factorization_partPrimes, Finsupp.support_filter,
    Nat.support_factorization]

theorem partPrimes_le {n : ℕ} (hn : n ≠ 0) : partPrimes P n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Dvd.intro_left _ (stripPrimes_mul_partPrimes P hn))

/-- `log n = log n̄ + ∑_{p ∈ P} v_p(n) log p`. -/
theorem log_eq_log_stripPrimes_add {n : ℕ} (hn : n ≠ 0) :
    Real.log n = Real.log (stripPrimes P n) +
      ∑ p ∈ n.primeFactors with p ∈ P, (n.factorization p : ℝ) * Real.log p := by
  conv_lhs => rw [← stripPrimes_mul_partPrimes P hn]
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast stripPrimes_ne_zero P n)
    (by exact_mod_cast partPrimes_ne_zero P n)]
  congr 1
  unfold partPrimes
  rw [Nat.cast_prod, Real.log_prod (fun p hp => by
    have := (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).ne_zero
    positivity)]
  refine sum_congr rfl fun p _ => ?_
  rw [Nat.cast_pow, Real.log_pow]

end Strip

/-! ### The damped weight -/

/-- The prime values of the damped weight: `1/j` on candidate primes, `0` on the other
primes up to `Y`, and `1` above `Y`. -/
noncomputable def proxyLoc (x : ℝ) (j : ℕ) (p : ℕ) : ℝ :=
  if p ∈ candidatePrimes x then (j : ℝ)⁻¹ else if (p : ℝ) ≤ proxyCutoff x then 0 else 1

/-- `g_j = cmul (proxyLoc x j)` on positive integers. -/
theorem dampedWeight_eq_cmul (x : ℝ) (j : ℕ) {n : ℕ} (hn : n ≠ 0) :
    dampedWeight x j n = cmul (proxyLoc x j) n := by
  rw [cmul_apply hn, Finsupp.prod, Nat.support_factorization,
    ← prod_filter_mul_prod_filter_not n.primeFactors (· ∈ candidatePrimes x)]
  have h1 : ∏ p ∈ n.primeFactors with p ∈ candidatePrimes x,
      proxyLoc x j p ^ n.factorization p = ((j : ℝ)⁻¹) ^ candidateOmega x n := by
    rw [candidateOmega, ← prod_pow_eq_pow_sum]
    exact prod_congr rfl fun p hp => by simp [proxyLoc, (mem_filter.1 hp).2]
  rw [h1, dampedWeight, candidateStrip, primeFactors_stripPrimes]
  split_ifs with h
  · rw [prod_eq_one fun p hp => ?_, mul_one]
    obtain ⟨hpn, hpP⟩ := mem_filter.1 hp
    have := h p (mem_filter.2 ⟨hpn, hpP⟩)
    simp [proxyLoc, hpP, not_le.2 this]
  · push Not at h
    obtain ⟨p, hp, hpY⟩ := h
    rw [prod_eq_zero hp, mul_zero]
    obtain ⟨hpn, hpP⟩ := mem_filter.1 hp
    have hv : n.factorization p ≠ 0 :=
      (Nat.prime_of_mem_primeFactors hpn).factorization_pos_of_dvd hn
        (Nat.dvd_of_mem_primeFactors hpn) |>.ne'
    simp [proxyLoc, hpP, hpY, hv]

theorem dampedWeight_nonneg (x : ℝ) (j n : ℕ) : 0 ≤ dampedWeight x j n := by
  unfold dampedWeight
  split_ifs
  · positivity
  · exact le_rfl

theorem dampedWeight_le_one (x : ℝ) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) : dampedWeight x j n ≤ 1 := by
  unfold dampedWeight
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  split_ifs
  · exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hj')
  · exact zero_le_one

/-! ### Candidate primes -/

/-- Candidate primes are primes in `[exp(L^{0.28}), exp(L^{0.45})]`. -/
theorem mem_candidatePrimes {x : ℝ} (hL : 1 ≤ Real.log x) {p : ℕ} (hp : p ∈ candidatePrimes x) :
    p.Prime ∧ Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (45 / 100 : ℝ)) := by
  unfold candidatePrimes at hp
  obtain ⟨G, hG, hpG⟩ := mem_biUnion.1 hp
  -- a group `[e^y, e^{2y})` with `L^a ≤ y` and `2y ≤ L^b`
  have key : ∀ a b : ℝ, 28 / 100 ≤ a → b ≤ 45 / 100 → G ∈ doublingGroups x a b →
      p.Prime ∧ Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.log x ^ (45 / 100 : ℝ)) := by
    intro a b ha hb hGab
    unfold doublingGroups at hGab
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hGab
    have hi2 := (mem_filter.1 hi).2
    unfold dyadicGroup at hpG
    obtain ⟨hpp, hlo, hhi⟩ := mem_primesIcc.1 hpG
    have hLa : Real.log x ^ (28 / 100 : ℝ) ≤ Real.log x ^ a :=
      Real.rpow_le_rpow_of_exponent_le hL ha
    have hLb : Real.log x ^ b ≤ Real.log x ^ (45 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL hb
    have h2i : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    have hLa0 : 0 ≤ Real.log x ^ a := by positivity
    refine ⟨hpp, ?_, ?_⟩
    · calc Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ Real.exp (2 ^ i * Real.log x ^ a) := by
            gcongr; nlinarith
        _ ≤ ⌈Real.exp (2 ^ i * Real.log x ^ a)⌉₊ := Nat.le_ceil _
        _ ≤ p := by exact_mod_cast hlo
    · rw [Nat.floor_natCast] at hhi
      have hlt : p < ⌈Real.exp (2 * (2 ^ i * Real.log x ^ a))⌉₊ := by
        have := Nat.ceil_pos.2 (Real.exp_pos (2 * (2 ^ i * Real.log x ^ a)))
        omega
      have hlt' := Nat.lt_ceil.1 hlt
      calc (p : ℝ) ≤ Real.exp (2 * (2 ^ i * Real.log x ^ a)) := hlt'.le
        _ ≤ Real.exp (Real.log x ^ (45 / 100 : ℝ)) := by
          gcongr
          calc 2 * (2 ^ i * Real.log x ^ a) = 2 ^ (i + 1) * Real.log x ^ a := by ring
            _ ≤ Real.log x ^ b := hi2
            _ ≤ _ := hLb
  rcases mem_union.1 hG with h | h
  · exact key _ _ le_rfl (by norm_num) h
  · exact key _ _ (by norm_num) le_rfl h

/-! ### Pointwise bounds for the proxies -/

/-- The density `D_j` is at least `∏_{p ≤ Y} (1 - 1/p) > 0`. -/
theorem prod_le_dampedDensity {x : ℝ} (hL : 1 ≤ Real.log x) {j : ℕ} (hj : 1 ≤ j) :
    0 < ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) ∧
      ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) ≤ dampedDensity x j := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hpos : 0 < ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) :=
    prod_pos fun p hp => by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesIcc.1 hp).1.two_le
      rw [sub_pos, div_lt_one (by linarith)]
      linarith
  refine ⟨hpos, ?_⟩
  unfold dampedDensity
  refine le_mul_of_one_le_right hpos.le (one_le_prod₀ fun p hp => ?_)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_candidatePrimes hL hp).1.two_le
  have ht : (j : ℝ)⁻¹ / p ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    have := inv_le_one_of_one_le₀ hj'
    linarith
  have ht0 : 0 ≤ (j : ℝ)⁻¹ / p := by positivity
  rw [one_le_inv₀ (by linarith)]
  linarith

theorem dampedDensity_pos {x : ℝ} (hL : 1 ≤ Real.log x) {j : ℕ} (hj : 1 ≤ j) :
    0 < dampedDensity x j :=
  lt_of_lt_of_le (prod_le_dampedDensity hL hj).1 (prod_le_dampedDensity hL hj).2

/-- `a_j^0(n) ≤ [x^γ < n] g_j(n) / (D_j γ L)`. -/
theorem unstrippedProxy_le {x γ : ℝ} (hx : 1 < x) (hL : 1 ≤ Real.log x) (hγ : 0 < γ) {j : ℕ}
    (hj : 1 ≤ j) (n : ℕ) :
    0 ≤ unstrippedProxy x γ j n ∧ unstrippedProxy x γ j n ≤
      (if x ^ γ < n then dampedWeight x j n else 0) /
        (dampedDensity x j * (γ * Real.log x)) := by
  have hD := dampedDensity_pos hL hj
  have hg := dampedWeight_nonneg x j n
  unfold unstrippedProxy
  split_ifs with h
  · have hn : γ * Real.log x < Real.log n := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_lt_log (by positivity) h
    have hγL : 0 < γ * Real.log x := by positivity
    refine ⟨div_nonneg hg (mul_nonneg hD.le (hγL.trans hn).le), ?_⟩
    exact div_le_div_of_nonneg_left hg (by positivity)
      (mul_le_mul_of_nonneg_left hn.le hD.le)
  · simp

/-- `a_j(n) ≤ [x^γ < n] g_j(n) / (D_j γ L)`, since `n̄ ≤ n`. -/
theorem strippedProxy_le {x γ : ℝ} (hx : 1 < x) (hL : 1 ≤ Real.log x) (hγ : 0 < γ) {j : ℕ}
    (hj : 1 ≤ j) (n : ℕ) :
    0 ≤ strippedProxy x γ j n ∧ strippedProxy x γ j n ≤
      (if x ^ γ < n then dampedWeight x j n else 0) /
        (dampedDensity x j * (γ * Real.log x)) := by
  have hD := dampedDensity_pos hL hj
  have hg := dampedWeight_nonneg x j n
  have hxγ : 1 ≤ x ^ γ := Real.one_le_rpow hx.le hγ.le
  unfold strippedProxy
  split_ifs with h h'
  · have hn : γ * Real.log x < Real.log (candidateStrip x n) := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_lt_log (by positivity) h
    have hγL : 0 < γ * Real.log x := by positivity
    refine ⟨div_nonneg hg (mul_nonneg hD.le (hγL.trans hn).le), ?_⟩
    exact div_le_div_of_nonneg_left hg (by positivity)
      (mul_le_mul_of_nonneg_left hn.le hD.le)
  · exfalso
    apply h'
    rcases eq_or_ne n 0 with rfl | hn
    · simp [candidateStrip, stripPrimes] at h
      linarith
    exact lt_of_lt_of_le h (by exact_mod_cast stripPrimes_le _ hn)
  · exact ⟨le_rfl, div_nonneg hg (mul_nonneg hD.le (by positivity))⟩
  · simp

end Erdos408.TypeII
