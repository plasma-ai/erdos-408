module

public import PrimeNumberTheoremAnd.IEANTN.Mertens

/-!
# Counting rough numbers

The number `Φ_Y(n)` of `b ≤ n` whose prime factors all exceed `Y` is at most
`A n / log Y + 1`, for an absolute `A` and `log Y` large. This is the only
sieve bound steps E4–E5 need.

The proof is Chebyshev's. For `n ≥ Y`, write `log b = ∑_{d ∣ b} Λ(d)`: a
rough `b` divisible by `d = p^k` has `p > Y`, and `b / d` is rough. So

  `Φ(n) log n ≤ 2n + ∑_{Y < d ≤ n} Λ(d) Φ(n / d)
    ≤ 2n + (A n / log Y)(log(n / Y) + 2E) + ψ(n)`

by induction, using Mertens' first theorem `∑_{d ≤ y} Λ(d)/d = log y + O(1)`
and `ψ(n) ≪ n`. This closes for `A = 2 (2 + C_ψ)` once `log Y ≥ 4E`.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real ArithmeticFunction

/-- The number of `Y`-rough `b ≤ n`: those whose prime factors all exceed `Y`. -/
noncomputable def roughCount (Y : ℝ) (n : ℕ) : ℕ :=
  ((Icc 1 n).filter fun b => ∀ p : ℕ, p ∈ b.primeFactors → Y < p).card

/-- Below `Y` the only rough number is `1`. -/
theorem roughCount_le_one {Y : ℝ} {n : ℕ} (h : (n : ℝ) < Y) : roughCount Y n ≤ 1 := by
  unfold roughCount
  refine (card_le_card fun b hb => ?_).trans (card_singleton 1).le
  obtain ⟨hb1, hrough⟩ := mem_filter.1 hb
  obtain ⟨h1, hbn⟩ := mem_Icc.1 hb1
  rw [mem_singleton]
  by_contra hne
  have hp := Nat.minFac_prime hne
  have hmem : b.minFac ∈ b.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, Nat.minFac_dvd b, by omega⟩
  have hle : (b.minFac : ℝ) ≤ n := by exact_mod_cast (Nat.minFac_le (by omega)).trans hbn
  linarith [hrough _ hmem]

/-- `∑_{b ≤ n} log(n / b) ≤ 2n`, from Stirling's lower bound `log n! ≥ n log n - 2n`. -/
theorem sum_log_div_le (n : ℕ) : ∑ b ∈ Icc 1 n, Real.log ((n : ℝ) / b) ≤ 2 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hge := Mertens.sum_log_ge (x := (n : ℝ)) (by exact_mod_cast hn)
  rw [Nat.floor_natCast] at hge
  have hIcc : Icc 1 n = Ioc 0 n := by
    ext b; simp only [mem_Icc, mem_Ioc]; omega
  have hsplit : ∑ b ∈ Icc 1 n, Real.log ((n : ℝ) / b) =
      n * Real.log n - ∑ b ∈ Ioc 0 n, Real.log b := by
    rw [hIcc, Finset.sum_congr rfl fun b hb => Real.log_div (by positivity)
      (by have := (mem_Ioc.1 hb).1; positivity), sum_sub_distrib]
    simp
  rw [hsplit]
  linarith

/-- A rough multiple `b ≤ n` of `d ≥ 1` is `d c` with `c ≤ n / d` rough, so there are at
most `Φ(n / d)` of them. -/
theorem card_rough_dvd_le {Y : ℝ} {n d : ℕ} (hd : 0 < d) :
    (((Icc 1 n).filter fun b => ∀ p : ℕ, p ∈ b.primeFactors → Y < p).filter (d ∣ ·)).card ≤
      roughCount Y (n / d) := by
  unfold roughCount
  refine card_le_card_of_injOn (fun b => b / d) (fun b hb => ?_) ?_
  · rw [mem_coe, mem_filter, mem_filter, mem_Icc] at hb
    rw [mem_coe, mem_filter, mem_Icc]
    obtain ⟨⟨⟨h1, hbn⟩, hr⟩, hdb⟩ := hb
    obtain ⟨c, rfl⟩ := hdb
    dsimp only
    rw [Nat.mul_div_cancel_left c hd]
    have hc : 0 < c := by
      rcases Nat.eq_zero_or_pos c with rfl | h
      · simp at h1
      · exact h
    refine ⟨⟨hc, (Nat.le_div_iff_mul_le hd).2 (by linarith [Nat.mul_comm d c])⟩, fun p hp => ?_⟩
    exact hr p (Nat.primeFactors_mono (Dvd.intro_left d rfl) (by positivity) hp)
  · intro b hb b' hb' h
    rw [mem_coe, mem_filter] at hb hb'
    obtain ⟨c, rfl⟩ := hb.2
    obtain ⟨c', rfl⟩ := hb'.2
    simp only [Nat.mul_div_cancel_left _ hd] at h
    rw [h]

/-- Chebyshev's bound for rough numbers: `Φ_Y(n) ≤ A n / log Y + 1` once `log Y` is
large. -/
theorem roughCount_le : ∃ A C₁ : ℝ, 0 < A ∧ ∀ Y : ℝ, 2 ≤ Y → C₁ ≤ Real.log Y →
    ∀ n : ℕ, (roughCount Y n : ℝ) ≤ A * n / Real.log Y + 1 := by
  set E : ℝ := Real.log 4 + 4 with hE
  have hE0 : 0 < E := by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  refine ⟨2 * (2 + E), 4 * E + 1, by positivity, fun Y hY hlY n => ?_⟩
  have hℓ : 0 < Real.log Y := by linarith
  set A : ℝ := 2 * (2 + E) with hA
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hnY : (n : ℝ) < Y
  · have := roughCount_le_one hnY
    have : (roughCount Y n : ℝ) ≤ 1 := by exact_mod_cast this
    have : 0 ≤ A * n / Real.log Y := by positivity
    linarith
  push Not at hnY
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hlogn : Real.log Y ≤ Real.log n := Real.log_le_log (by linarith) hnY
  set R := (Icc 1 n).filter fun b => ∀ p : ℕ, p ∈ b.primeFactors → Y < p with hR
  -- `log n · Φ(n) ≤ ∑_R log b + ∑_{b ≤ n} log(n/b)`
  have hsplit : Real.log n * (R.card : ℝ) ≤ ∑ b ∈ R, Real.log b + 2 * n := by
    have h1 : Real.log n * (R.card : ℝ) =
        ∑ b ∈ R, Real.log b + ∑ b ∈ R, Real.log ((n : ℝ) / b) := by
      rw [← sum_add_distrib, mul_comm, ← nsmul_eq_mul, ← sum_const]
      refine sum_congr rfl fun b hb => ?_
      have hb0 : (0 : ℝ) < b := by
        have := (mem_Icc.1 (mem_filter.1 hb).1).1; exact_mod_cast this
      rw [Real.log_div (by positivity) hb0.ne']
      ring
    have h2 : ∑ b ∈ R, Real.log ((n : ℝ) / b) ≤ ∑ b ∈ Icc 1 n, Real.log ((n : ℝ) / b) := by
      refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun b hb _ => ?_
      obtain ⟨h1, hbn⟩ := mem_Icc.1 hb
      have hb0 : (0 : ℝ) < b := by exact_mod_cast h1
      exact Real.log_nonneg ((one_le_div hb0).2 (by exact_mod_cast hbn))
    linarith [sum_log_div_le n]
  -- `∑_R log b = ∑_{d ≤ n} Λ(d) #{b ∈ R : d ∣ b}`
  have hswap : ∑ b ∈ R, Real.log b =
      ∑ d ∈ Icc 1 n, Λ d * ((R.filter (d ∣ ·)).card : ℝ) := by
    have : ∑ b ∈ R, Real.log b = ∑ b ∈ R, ∑ d ∈ b.divisors, Λ d :=
      sum_congr rfl fun b _ => vonMangoldt_sum.symm
    rw [this, sum_comm' (t' := Icc 1 n) (s' := fun d => R.filter (d ∣ ·))]
    · refine sum_congr rfl fun d _ => ?_
      rw [sum_const, nsmul_eq_mul, mul_comm]
    · intro b d
      simp only [Nat.mem_divisors, mem_filter, mem_Icc, hR]
      constructor
      · rintro ⟨⟨⟨h1, hbn⟩, hr⟩, hdb, hb0⟩
        exact ⟨⟨⟨⟨h1, hbn⟩, hr⟩, hdb⟩, Nat.pos_of_dvd_of_pos hdb (by omega),
          (Nat.le_of_dvd (by omega) hdb).trans hbn⟩
      · rintro ⟨⟨⟨⟨h1, hbn⟩, hr⟩, hdb⟩, -⟩
        exact ⟨⟨⟨h1, hbn⟩, hr⟩, hdb, by omega⟩
  -- each `d` contributes at most `Λ(d) (A n / (d log Y) + 1)`, and only for `d > Y`
  have hterm : ∀ d ∈ Icc 1 n, Λ d * ((R.filter (d ∣ ·)).card : ℝ) ≤
      if Y < d then Λ d * (A * n / (d * Real.log Y) + 1) else 0 := by
    intro d hd
    obtain ⟨hd1, hdn⟩ := mem_Icc.1 hd
    by_cases hΛ : Λ d = 0
    · rw [hΛ, zero_mul]; split_ifs <;> simp
    have hpp : IsPrimePow d := vonMangoldt_ne_zero_iff.1 hΛ
    have hd2 : d ≠ 1 := hpp.ne_one
    have hp := Nat.minFac_prime hd2
    by_cases hpY : (d.minFac : ℝ) ≤ Y
    · -- no rough number is divisible by `d`
      have hempty : R.filter (d ∣ ·) = ∅ := by
        refine filter_eq_empty_iff.2 fun b hb hdb => ?_
        obtain ⟨hb1, hr⟩ := mem_filter.1 hb
        have hb0 : b ≠ 0 := by have := (mem_Icc.1 hb1).1; omega
        have := hr _ (Nat.mem_primeFactors.2 ⟨hp, (Nat.minFac_dvd d).trans hdb, hb0⟩)
        linarith
      rw [hempty, card_empty, Nat.cast_zero, mul_zero]
      split_ifs
      · exact mul_nonneg vonMangoldt_nonneg (by positivity)
      · exact le_rfl
    push Not at hpY
    have hYd : Y < d := lt_of_lt_of_le hpY (by exact_mod_cast Nat.minFac_le (by omega))
    simp only [hYd, ite_true]
    refine mul_le_mul_of_nonneg_left ?_ vonMangoldt_nonneg
    have hdiv : n / d < n := Nat.div_lt_self hn0 (by omega)
    have hcard := (card_rough_dvd_le (Y := Y) (n := n) (d := d) (by omega))
    have hih := ih (n / d) hdiv
    have hnd : ((n / d : ℕ) : ℝ) ≤ n / d := Nat.cast_div_le
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    calc ((R.filter (d ∣ ·)).card : ℝ) ≤ roughCount Y (n / d) := by exact_mod_cast hcard
      _ ≤ A * ((n / d : ℕ) : ℝ) / Real.log Y + 1 := hih
      _ ≤ A * (n / d) / Real.log Y + 1 := by gcongr
      _ = A * n / (d * Real.log Y) + 1 := by field_simp
  -- Mertens: `∑_{Y < d ≤ n} Λ(d) / d ≤ log n - log Y + 2E`
  have hmert : ∑ d ∈ (Icc 1 n).filter (fun d : ℕ => Y < d), Λ d / d ≤
      Real.log n - Real.log Y + 2 * E := by
    have hn := Mertens.sum_mangoldt_div_eq_log (x := (n : ℝ)) hn1
    have hy := Mertens.sum_mangoldt_div_eq_log (x := Y) (by linarith)
    rw [Nat.floor_natCast] at hn
    have hfl : ⌊Y⌋₊ ≤ n := Nat.floor_le_of_le hnY
    have hsplit : ∑ d ∈ Ioc 0 n, Λ d / d =
        ∑ d ∈ Ioc 0 ⌊Y⌋₊, Λ d / d + ∑ d ∈ (Icc 1 n).filter (fun d : ℕ => Y < d), Λ d / d := by
      rw [← sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
      congr 1
      refine sum_congr ?_ fun _ _ => rfl
      ext d
      simp only [mem_Ioc, mem_filter, mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by omega, h2⟩, (Nat.floor_lt' (by omega)).1 h1⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨(Nat.floor_lt' (by omega)).2 h3, h2⟩
    rw [abs_le] at hn hy
    linarith [hn.2, hy.1]
  have hpsi : ∑ d ∈ Icc 1 n, Λ d ≤ E * n := by
    have := Chebyshev.psi_le_const_mul_self (x := (n : ℝ)) (by positivity)
    rw [Chebyshev.psi, Nat.floor_natCast] at this
    have hIcc : Icc 1 n = Ioc 0 n := by ext b; simp only [mem_Icc, mem_Ioc]; omega
    rw [hIcc]
    linarith
  have hsum : ∑ b ∈ R, Real.log b ≤
      A * n / Real.log Y * (Real.log n - Real.log Y + 2 * E) + E * n := by
    rw [hswap]
    refine (sum_le_sum hterm).trans ?_
    rw [← sum_filter]
    have : ∑ d ∈ (Icc 1 n).filter (fun d : ℕ => Y < d), Λ d * (A * n / (d * Real.log Y) + 1) =
        A * n / Real.log Y * ∑ d ∈ (Icc 1 n).filter (fun d : ℕ => Y < d), Λ d / d +
          ∑ d ∈ (Icc 1 n).filter (fun d : ℕ => Y < d), Λ d := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun d hd => ?_
      have : (0 : ℝ) < d := by
        have := (mem_Icc.1 (mem_filter.1 hd).1).1; exact_mod_cast this
      field_simp
    rw [this]
    have h1 : ∑ d ∈ (Icc 1 n).filter (fun d : ℕ => Y < d), Λ d ≤ ∑ d ∈ Icc 1 n, Λ d :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => vonMangoldt_nonneg
    have h2 : 0 ≤ A * n / Real.log Y := by positivity
    have := mul_le_mul_of_nonneg_left hmert h2
    linarith
  -- close the induction
  have hfinal : (R.card : ℝ) ≤ A * n / Real.log Y := by
    have hlogn0 : 0 < Real.log n := lt_of_lt_of_le hℓ hlogn
    rw [← mul_le_mul_iff_of_pos_left hlogn0]
    have hkey : 2 * E * A ≤ A / 2 * Real.log Y := by
      have : 4 * E ≤ Real.log Y := by linarith
      nlinarith
    have : A * n / Real.log Y * (2 * E) ≤ A / 2 * n := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hℓ]
      nlinarith
    have hAn : A * n / Real.log Y * Real.log Y = A * n := by field_simp
    nlinarith
  show ((roughCount Y n : ℕ) : ℝ) ≤ _
  unfold roughCount
  rw [← hR]
  linarith

end Erdos408.TypeII
