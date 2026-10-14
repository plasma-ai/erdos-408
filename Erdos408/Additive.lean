module

public import Erdos408.Statement
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Factorization.Induction

/-!
# The completely additive companion of the totient height

`F` is the completely additive function with `F 2 = 1` and `F p = F (p - 1)`
for every odd prime `p`, as in Erdős, Granville, Pomerance and Spiro (1990,
p. 166). Since `F (φ n) = F n - 1` for even `n` and `F (φ n) = F n` for odd
`n`, the height `f n` equals `F n` for even `n ≥ 2` and `F n + 1` for odd
`n ≥ 3`. Induction over the primes gives
`log n / log 3 ≤ F n ≤ log n / log 2`.
-/

@[expose] public section

namespace Erdos408

/-- The completely additive function with `F 2 = 1` and `F p = F (p - 1)` for
every odd prime `p`. -/
noncomputable def F (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else
    ∑ p ∈ n.primeFactors.attach, n.factorization p * if (p : ℕ) = 2 then 1 else F (p - 1)
termination_by n
decreasing_by
  have hp := Nat.prime_of_mem_primeFactors p.2
  have hle := Nat.le_of_mem_primeFactors p.2
  have := hp.two_le
  omega

/-- Unfolding `F` at `n ≥ 2`. -/
private theorem F_eq_sum {n : ℕ} (hn : 2 ≤ n) :
    F n = ∑ p ∈ n.primeFactors, n.factorization p * if p = 2 then 1 else F (p - 1) := by
  rw [F, ite_eq_right (by omega)]
  exact Finset.sum_attach n.primeFactors fun p =>
    n.factorization p * if p = 2 then 1 else F (p - 1)

/-- `F` vanishes at `0`. -/
theorem F_zero : F 0 = 0 := by
  rw [F]
  simp

/-- `F` vanishes at `1`. -/
theorem F_one : F 1 = 0 := by
  rw [F]
  simp

/-- The value of `F` at a prime. -/
private theorem F_prime {p : ℕ} (hp : p.Prime) : F p = if p = 2 then 1 else F (p - 1) := by
  rw [F_eq_sum hp.two_le, hp.primeFactors, Finset.sum_singleton, hp.factorization_self,
    one_mul]

/-- `F n` is the sum of `F q` over the prime factors `q` of `n`, counted with
multiplicity. -/
theorem F_eq_sum_factorization {n : ℕ} (hn : n ≠ 0) :
    F n = ∑ q ∈ n.primeFactors, n.factorization q * F q := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    simp [F_one]
  rw [F_eq_sum h]
  exact Finset.sum_congr rfl fun q hq => by rw [F_prime (Nat.prime_of_mem_primeFactors hq)]

/-- `F n` as a `Finsupp.sum` over the factorization of `n`. -/
private theorem F_eq_finsuppSum {n : ℕ} (hn : n ≠ 0) :
    F n = n.factorization.sum fun q e => e * F q := by
  rw [F_eq_sum_factorization hn, Finsupp.sum, Nat.support_factorization]

/-- `F` is completely additive. -/
theorem F_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : F (m * n) = F m + F n := by
  rw [F_eq_finsuppSum (mul_ne_zero hm hn), Nat.factorization_mul hm hn,
    Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
    ← F_eq_finsuppSum hm, ← F_eq_finsuppSum hn]

/-- `F 2 = 1`. -/
theorem F_two : F 2 = 1 := by
  rw [F_prime Nat.prime_two, ite_eq_left rfl]

/-- `F p = F (p - 1)` for every odd prime `p`. -/
theorem F_prime_of_ne_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : F p = F (p - 1) := by
  rw [F_prime hp, ite_eq_right h2]

/-- `F` of a power. -/
private theorem F_pow {p : ℕ} (hp : p ≠ 0) (k : ℕ) : F (p ^ k) = k * F p := by
  induction k with
  | zero => simp [F_one]
  | succ k ih => rw [pow_succ, F_mul (pow_ne_zero _ hp) hp, ih]; ring

/-- An odd prime `p` satisfies `F p = 1 + F m` where `p = 2 m + 1`. -/
private theorem F_odd_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    1 ≤ (p - 1) / 2 ∧ p = 2 * ((p - 1) / 2) + 1 ∧ F p = 1 + F ((p - 1) / 2) := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two h2
  have := hp.two_le
  refine ⟨by omega, by omega, ?_⟩
  rw [F_prime_of_ne_two hp h2, show p - 1 = 2 * ((p - 1) / 2) by omega,
    F_mul two_ne_zero (by omega), F_two]
  congr 2
  omega

/-- Induction over the positive integers through primes and products. -/
private theorem induction_on_primes_mul {P : ℕ → Prop} (h1 : P 1)
    (hp : ∀ p, p.Prime → (∀ m, m ≠ 0 → m < p → P m) → P p)
    (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → P a → P b → P (a * b)) : ∀ n, n ≠ 0 → P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      exact h1
    have hmin := Nat.minFac_prime (show n ≠ 1 by omega)
    have hle := Nat.minFac_le (show 0 < n by omega)
    have hdvd := Nat.minFac_dvd n
    have hq : n / n.minFac < n := Nat.div_lt_self (by omega) hmin.one_lt
    have hq0 : n / n.minFac ≠ 0 := (Nat.div_pos hle hmin.pos).ne'
    rw [← Nat.mul_div_cancel' hdvd]
    exact hmul _ _ hmin.ne_zero hq0
      (hp _ hmin fun m hm hlt => ih m (by omega) hm) (ih _ hq hq0)

/-- The lower bound `log n / log 3 ≤ F n`. -/
theorem log_div_log_three_le_F {n : ℕ} (hn : n ≠ 0) : Real.log n / Real.log 3 ≤ F n := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine induction_on_primes_mul (P := fun n => Real.log n / Real.log 3 ≤ F n)
    (by simp [F_one]) (fun p hp ih => ?_) (fun a b ha hb iha ihb => ?_) n hn
  · by_cases h2 : p = 2
    · subst h2
      simp only [F_two, Nat.cast_one, Nat.cast_ofNat]
      rw [div_le_one h3]
      exact Real.log_le_log (by norm_num) (by norm_num)
    obtain ⟨hm1, hpm, hF⟩ := F_odd_prime hp h2
    set m := (p - 1) / 2
    have ihm := ih m (by omega) (by omega)
    -- `log p ≤ log (3 m) = log 3 + log m`
    have hlog : Real.log p ≤ Real.log 3 + Real.log m := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      exact Real.log_le_log (by exact_mod_cast hp.pos) (by rw [hpm]; push_cast; linarith)
    rw [hF, Nat.cast_add, Nat.cast_one, div_le_iff₀ h3]
    rw [div_le_iff₀ h3] at ihm
    linarith
  · rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity), add_div, F_mul ha hb,
      Nat.cast_add]
    exact add_le_add iha ihb

/-- The upper bound `F n ≤ log n / log 2`. -/
theorem F_le_log_div_log_two {n : ℕ} (hn : n ≠ 0) : (F n : ℝ) ≤ Real.log n / Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine induction_on_primes_mul (P := fun n => (F n : ℝ) ≤ Real.log n / Real.log 2)
    (by simp [F_one]) (fun p hp ih => ?_) (fun a b ha hb iha ihb => ?_) n hn
  · by_cases hp2 : p = 2
    · subst hp2
      simp only [F_two, Nat.cast_one, Nat.cast_ofNat, div_self h2.ne', le_refl]
    obtain ⟨hm1, hpm, hF⟩ := F_odd_prime hp hp2
    set m := (p - 1) / 2
    have ihm := ih m (by omega) (by omega)
    -- `log 2 + log m = log (2 m) ≤ log p`
    have hlog : Real.log 2 + Real.log m ≤ Real.log p := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (by positivity) (by rw [hpm]; push_cast; linarith)
    rw [hF, Nat.cast_add, Nat.cast_one, le_div_iff₀ h2]
    rw [le_div_iff₀ h2] at ihm
    linarith
  · rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity), add_div, F_mul ha hb,
      Nat.cast_add]
    exact add_le_add iha ihb

/-- `F` drops by one under `φ` at even arguments and is unchanged at odd ones. -/
private theorem F_totient_add {n : ℕ} (hn : n ≠ 0) :
    F (Nat.totient n) + (if 2 ∣ n then 1 else 0) = F n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
    rw [Nat.totient_prime_pow hp hk, F_mul (pow_ne_zero _ hp.ne_zero) hp1, F_pow hp.ne_zero,
      F_pow hp.ne_zero]
    by_cases h2 : p = 2
    · subst h2
      rw [ite_eq_left (dvd_pow_self 2 hk.ne'), F_two]
      simp only [Nat.reduceSub, F_one]
      omega
    · have hndvd : ¬ 2 ∣ p ^ k := fun h =>
        h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
          (Nat.prime_two.dvd_of_dvd_pow h)).symm
      rw [ite_eq_right hndvd, ← F_prime_of_ne_two hp h2]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
      simp only [zero_add, Nat.add_sub_cancel]
      ring
  | zero => exact absurd rfl hn
  | one => simp [F_one]
  | coprime a b ha hb hab iha ihb =>
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have iha := iha ha0
    have ihb := ihb hb0
    rw [Nat.totient_mul hab, F_mul (by simpa using ha0) (by simpa using hb0), F_mul ha0 hb0]
    have hmul : 2 ∣ a * b ↔ 2 ∣ a ∨ 2 ∣ b := Nat.prime_two.dvd_mul
    -- `a` and `b` are not both even
    have hnot : ¬ (2 ∣ a ∧ 2 ∣ b) := fun h => by
      have := Nat.dvd_gcd h.1 h.2
      rw [hab.gcd_eq_one] at this
      omega
    split_ifs at iha ihb ⊢ <;> omega

/-- Iterates of `φ` that reach `1` exactly from step `c ≥ 1` on give `f n = c`. -/
private theorem f_eq_of_iterate_iff {n c : ℕ} (hc : 1 ≤ c)
    (h : ∀ k, 1 ≤ k → (Nat.totient^[k] n = 1 ↔ c ≤ k)) : f n = c :=
  le_antisymm (Nat.sInf_le ⟨hc, (h c hc).2 le_rfl⟩)
    (le_csInf ⟨c, hc, (h c hc).2 le_rfl⟩ fun k hk => (h k hk.1).1 hk.2)

/-- For even `n ≥ 2`, `φ^[k] n = 1` exactly when `k ≥ F n`. -/
private theorem iterate_totient_eq_one_iff_of_even {n : ℕ} (hn : 2 ≤ n) (he : Even n) (k : ℕ) :
    Nat.totient^[k] n = 1 ↔ F n ≤ k := by
  induction k generalizing n with
  | zero =>
    obtain ⟨m, rfl⟩ := he
    rw [← two_mul, F_mul two_ne_zero (by omega), F_two]
    simp only [Function.iterate_zero, id_eq]
    omega
  | succ k ih =>
    have hF := F_totient_add (show n ≠ 0 by omega)
    rw [ite_eq_left (even_iff_two_dvd.1 he)] at hF
    rw [Function.iterate_succ_apply]
    by_cases h1 : Nat.totient n = 1
    · rw [h1, Function.iterate_fixed Nat.totient_one, ← hF, h1, F_one]
      simp
    have h0 : Nat.totient n ≠ 0 := (Nat.totient_pos.2 (by omega)).ne'
    have h3 : 2 < n := by
      by_contra h
      exact h1 (Nat.totient_eq_one_iff.2 (by omega))
    rw [ih (by omega) (Nat.totient_even h3)]
    omega

/-- The height of an even `n ≥ 2` is `F n`. -/
theorem f_eq_F_of_even {n : ℕ} (hn : 2 ≤ n) (he : Even n) : f n = F n := by
  have hF := (iterate_totient_eq_one_iff_of_even hn he 0).not.1
    (by simp only [Function.iterate_zero, id_eq]; omega)
  exact f_eq_of_iterate_iff (by omega) fun k _ => iterate_totient_eq_one_iff_of_even hn he k

/-- The height of an odd `n ≥ 3` is `F n + 1`. -/
theorem f_eq_F_add_one_of_odd {n : ℕ} (hn : 2 ≤ n) (ho : Odd n) : f n = F n + 1 := by
  have h3 : 2 < n := by obtain ⟨m, rfl⟩ := ho; omega
  have hF := F_totient_add (show n ≠ 0 by omega)
  rw [ite_eq_right (Nat.not_even_iff_odd.2 ho ∘ even_iff_two_dvd.2), add_zero] at hF
  have h2 : 2 ≤ Nat.totient n := by
    have h0 : Nat.totient n ≠ 0 := (Nat.totient_pos.2 (by omega)).ne'
    have h1 : Nat.totient n ≠ 1 := fun h => by have := Nat.totient_eq_one_iff.1 h; omega
    omega
  refine f_eq_of_iterate_iff (by omega) fun k hk => ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [Function.iterate_succ_apply, iterate_totient_eq_one_iff_of_even h2 (Nat.totient_even h3),
    hF]
  omega

/-- `f n` and `F n` differ by at most one for `n ≥ 1`. -/
theorem abs_f_sub_F_le_one {n : ℕ} (hn : 1 ≤ n) : |(f n : ℝ) - F n| ≤ 1 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    have : f 1 = 1 :=
      f_eq_of_iterate_iff le_rfl fun k hk => by simp [Function.iterate_fixed Nat.totient_one, hk]
    simp [this, F_one]
  rcases Nat.even_or_odd n with he | ho
  · simp [f_eq_F_of_even h he]
  · simp [f_eq_F_add_one_of_odd h ho]

end Erdos408
