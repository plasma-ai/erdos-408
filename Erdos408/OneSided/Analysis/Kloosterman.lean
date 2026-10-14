import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-!
# A weak Kloosterman bound

PD `det:weak-kloosterman`: for every `ε > 0`,
`|K_m(h, k)| ≤ C_ε m^{3/4 + ε} (h, k, m)^{1/4}`, where
`K_m(h, k) = ∑_{y ∈ (ℤ/m)^×} e((h y + k y⁻¹)/m)`. The proof is elementary.

* The fourth moment over all `(h, k)` is `m² T_m`, where `T_m` counts unit quadruples with
  equal sums and equal inverse sums. Clearing denominators gives
  `m ∣ (y₁ + y₂)(z₁ - y₁)(z₁ - y₂)`. The linear map to these three forms has kernel of size
  at most two, and `#{(A, B, C) : m ∣ A B C} ≤ (∑_A (A, m))² ≤ (m τ(m))²`, so
  `T_m ≤ 2 m² τ(m)²`.
* `K_m` is constant on the orbits `(h s, k s⁻¹)`, and the stabilizer of `(h, k)` has at
  most `(h, k, m)` elements. Hence
  `φ(m) |K_m(h, k)|⁴ ≤ (h, k, m) m² T_m`.
* With `m / φ(m) ≤ τ(m)` this gives `|K_m(h, k)|⁴ ≤ 2 (h, k, m) m³ τ(m)³`. Finish with the
  divisor bound `τ(n) ≤ C_ε n^ε`.

The sums are taken over `ZMod m` with the standard additive character, through
`kloostermanZMod`, which agrees with `kloosterman` for `m ≥ 1`.
-/

namespace Erdos408.OneSided

open Finset

/-- The Kloosterman sum `K_m(h, k) = ∑_{y ∈ (ℤ/m)^×} e((h y + k y⁻¹)/m)`, over the
representatives `0 ≤ y < m` coprime to `m`. -/
noncomputable def kloosterman (m h k : ℕ) : ℂ :=
  ∑ y ∈ (Finset.range m).filter (Nat.Coprime · m),
    Complex.exp (2 * Real.pi * Complex.I *
      (((h * y + k * ((y : ZMod m)⁻¹).val : ℕ) : ℝ) / m))

/-! ### The divisor bound -/

/-- Each prime power contributes a bounded factor: `a + 1 ≤ B p^{a ε}` for every prime `p`,
and `a + 1 ≤ p^{a ε}` once `p ≥ 2^{1/ε}`. -/
theorem add_one_le_rpow_pow {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ p a : ℕ, 2 ≤ p →
      ((a : ℝ) + 1 ≤ B * ((p : ℝ) ^ ε) ^ a) ∧
      ((2 : ℝ) ^ (1 / ε) ≤ p → (a : ℝ) + 1 ≤ ((p : ℝ) ^ ε) ^ a) := by
  set c := Real.log 2 * ε
  have hc : 0 < c := mul_pos (Real.log_pos one_lt_two) hε
  refine ⟨max 1 c⁻¹, le_max_left _ _, fun p a hp => ⟨?_, fun hP => ?_⟩⟩
  · -- `p^ε ≥ 2^ε = e^c`, and `(e^c)^a ≥ 1 + a c`
    have h2 : Real.exp c ≤ (p : ℝ) ^ ε := by
      rw [Real.rpow_def_of_pos (by positivity)]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
        (Real.log_le_log (by norm_num) (by exact_mod_cast hp)) hε.le)
    have h3 : 1 + a * c ≤ ((p : ℝ) ^ ε) ^ a := by
      calc 1 + a * c ≤ Real.exp (a * c) := by linarith [Real.add_one_le_exp (a * c)]
        _ = Real.exp c ^ a := Real.exp_nat_mul c a
        _ ≤ _ := by gcongr
    calc (a : ℝ) + 1 ≤ max 1 c⁻¹ * (1 + a * c) := by
          have h4 : 1 ≤ max 1 c⁻¹ * c := by
            calc (1 : ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
              _ ≤ _ := by gcongr; exact le_max_right _ _
          nlinarith [le_max_left 1 c⁻¹, (a.cast_nonneg : (0 : ℝ) ≤ a)]
      _ ≤ _ := by gcongr
  · -- `p^ε ≥ 2`, and `2^a ≥ a + 1`
    have h2 : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
        _ ≤ _ := by gcongr
    calc (a : ℝ) + 1 ≤ 2 ^ a := by exact_mod_cast Nat.lt_two_pow_self
      _ ≤ _ := by gcongr

/-- The divisor bound `τ(n) ≤ C_ε n^ε`. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨B, hB, hBp⟩ := add_one_le_rpow_pow hε
  set P := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  refine ⟨B ^ P, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  -- the factor of `p` in the product is at most `c p = B` or `1`
  set c : ℕ → ℝ := fun p => if p < P then B else 1
  have hfac : ∀ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) ≤
      c p * ((p : ℝ) ^ n.factorization p) ^ ε := by
    intro p hp
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    rw [← Real.rpow_pow_comm (by positivity)]
    push_cast
    by_cases hpP : p < P
    · simpa [c, hpP] using (hBp p (n.factorization p) hp2).1
    · simp only [c, hpP, ite_false, one_mul]
      refine (hBp p _ hp2).2 ?_
      exact (Nat.le_ceil _).trans (by exact_mod_cast not_lt.1 hpP)
  -- the product of the `c p` is at most `B ^ P`
  have hc : ∏ p ∈ n.primeFactors, c p ≤ B ^ P := by
    rw [prod_ite, prod_const, prod_const_one, mul_one]
    refine pow_le_pow_right₀ hB ((card_le_card fun p hp => ?_).trans (card_range P).le)
    exact mem_range.2 (mem_filter.1 hp).2
  calc (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) := by
        rw [Nat.card_divisors hn0]; push_cast; rfl
    _ ≤ ∏ p ∈ n.primeFactors, c p * ((p : ℝ) ^ n.factorization p) ^ ε :=
        prod_le_prod₀ (fun _ _ => by positivity) hfac
    _ = (∏ p ∈ n.primeFactors, c p) * (n : ℝ) ^ ε := by
        rw [prod_mul_distrib, Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
        congr 2
        conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
        rw [Nat.prod_factorization_eq_prod_primeFactors]
        push_cast; rfl
    _ ≤ B ^ P * (n : ℝ) ^ ε := by gcongr

/-- `m ≤ φ(m) τ(m)`: `m / φ(m) = ∏_{p ∣ m} p / (p - 1) ≤ 2^{ω(m)} ≤ τ(m)`. -/
theorem le_totient_mul_card_divisors (n : ℕ) : n ≤ n.totient * n.divisors.card := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact Nat.zero_le _
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) :=
    prod_pos fun p hp => Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt
  -- each `p ≤ 2 (p - 1) ≤ (a_p + 1)(p - 1)`
  have hp : ∏ p ∈ n.primeFactors, p ≤ n.divisors.card * ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [Nat.card_divisors hn, ← prod_mul_distrib]
    refine prod_le_prod fun p hp => ?_
    have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have ha : 1 ≤ n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1
      (by rwa [Nat.support_factorization]))
    calc p ≤ 2 * (p - 1) := by omega
      _ ≤ (n.factorization p + 1) * (p - 1) := Nat.mul_le_mul_right _ (by omega)
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  rw [← Nat.totient_mul_prod_primeFactors, mul_assoc]
  exact Nat.mul_le_mul_left _ hp

/-! ### Counting solutions mod `m` -/

section Residues

variable {m : ℕ} [NeZero m]

/-- In `ZMod m`, `n C = 0` exactly when `m ∣ n C.val`. -/
theorem natCast_mul_eq_zero_iff (n : ℕ) (C : ZMod m) :
    (n : ZMod m) * C = 0 ↔ m ∣ n * C.val := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val]

/-- At most `m / d` residues mod `m` have a representative divisible by `d ∣ m`. -/
theorem card_filter_dvd_val_le {d : ℕ} (hd : d ∣ m) :
    #{A : ZMod m | d ∣ A.val} ≤ m / d := by
  calc #{A : ZMod m | d ∣ A.val}
      ≤ #((range (m / d)).image fun j => ((d * j : ℕ) : ZMod m)) := by
        refine card_le_card fun A hA => ?_
        obtain ⟨j, hj⟩ := (mem_filter.1 hA).2
        refine mem_image.2 ⟨j, mem_range.2 ?_, by rw [← hj, ZMod.natCast_zmod_val]⟩
        rw [Nat.lt_div_iff_mul_lt' hd, ← hj]
        exact ZMod.val_lt A
    _ ≤ m / d := card_image_le.trans (card_range _).le

/-- At most `(n, m)` residues `C` mod `m` satisfy `n C = 0`. -/
theorem card_filter_natCast_mul_eq_zero_le (n : ℕ) :
    #{C : ZMod m | (n : ZMod m) * C = 0} ≤ Nat.gcd n m := by
  have hm := NeZero.ne m
  have hg : 0 < Nat.gcd n m := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hm)
  have hgm : m / Nat.gcd n m ∣ m := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right n m)
  calc #{C : ZMod m | (n : ZMod m) * C = 0}
      ≤ #{C : ZMod m | m / Nat.gcd n m ∣ C.val} := by
        refine card_le_card fun C hC => mem_filter.2 ⟨mem_univ _, ?_⟩
        have h := (natCast_mul_eq_zero_iff n C).1 (mem_filter.1 hC).2
        -- cancel `(n, m)` and use that `m / (n, m)` is coprime to `n / (n, m)`
        refine (Nat.coprime_div_gcd_div_gcd hg).symm.dvd_of_dvd_mul_left ?_
        obtain ⟨t, ht⟩ := h
        refine ⟨t, Nat.eq_of_mul_eq_mul_left hg ?_⟩
        rw [← mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_left n m), ← mul_assoc,
          Nat.mul_div_cancel' (Nat.gcd_dvd_right n m), ht]
    _ ≤ m / (m / Nat.gcd n m) := card_filter_dvd_val_le hgm
    _ = Nat.gcd n m := Nat.div_div_self (Nat.gcd_dvd_right n m) hm

/-- `∑_{A mod m} (A, m) ≤ m τ(m)`: bound `(A, m)` by the sum of the divisors of `m` dividing
`A`, and count the `A` divisible by each one. -/
theorem sum_gcd_val_le : ∑ A : ZMod m, Nat.gcd A.val m ≤ m * m.divisors.card := by
  calc ∑ A : ZMod m, Nat.gcd A.val m
      ≤ ∑ A : ZMod m, ∑ d ∈ m.divisors, if d ∣ A.val then d else 0 := by
        refine sum_le_sum fun A _ => ?_
        have hmem : Nat.gcd A.val m ∈ m.divisors :=
          Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right _ _, NeZero.ne m⟩
        refine le_trans ?_ (single_le_sum (fun _ _ => Nat.zero_le _) hmem)
        rw [ite_eq_left_iff.2 fun h => absurd (Nat.gcd_dvd_left _ _) h]
    _ = ∑ d ∈ m.divisors, d * #{A : ZMod m | d ∣ A.val} := by
        rw [sum_comm]
        refine sum_congr rfl fun d _ => ?_
        rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ d ∈ m.divisors, d * (m / d) :=
        sum_le_sum fun d hd =>
          Nat.mul_le_mul_left _ (card_filter_dvd_val_le (Nat.dvd_of_mem_divisors hd))
    _ = m * m.divisors.card := by
        rw [sum_congr rfl fun d hd => Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd), sum_const,
          smul_eq_mul, mul_comm]

/-- `#{(A, B, C) mod m : A B C = 0} ≤ (m τ(m))²`: for fixed `A, B` there are at most
`(A B, m) ≤ (A, m) (B, m)` choices of `C`. -/
theorem card_filter_mul_mul_eq_zero_le :
    #{v : ZMod m × ZMod m × ZMod m | v.1 * v.2.1 * v.2.2 = 0} ≤ (m * m.divisors.card) ^ 2 := by
  calc #{v : ZMod m × ZMod m × ZMod m | v.1 * v.2.1 * v.2.2 = 0}
      = ∑ A : ZMod m, ∑ B : ZMod m, #{C : ZMod m | A * B * C = 0} := by
        simp only [card_filter, Fintype.sum_prod_type]
    _ ≤ ∑ A : ZMod m, ∑ B : ZMod m, Nat.gcd A.val m * Nat.gcd B.val m := by
        refine sum_le_sum fun A _ => sum_le_sum fun B _ => ?_
        have h := card_filter_natCast_mul_eq_zero_le (m := m) (A.val * B.val)
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h
        have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
        exact h.trans (Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_right _ hm)
          (Nat.gcd_pos_of_pos_right _ hm)) (Nat.gcd_mul_left_dvd_mul_gcd m _ _))
    _ = (∑ A : ZMod m, Nat.gcd A.val m) ^ 2 := by rw [sq, sum_mul_sum]
    _ ≤ (m * m.divisors.card) ^ 2 := Nat.pow_le_pow_left sum_gcd_val_le 2

/-- At most two residues mod `m` satisfy `2 t = 0`. -/
theorem card_filter_two_mul_eq_zero_le : #{t : ZMod m | 2 * t = 0} ≤ 2 := by
  have h := card_filter_natCast_mul_eq_zero_le (m := m) 2
  rw [Nat.cast_ofNat] at h
  exact h.trans (Nat.gcd_le_left _ two_pos)

/-- The forms `(y₁ + y₂, z₁ - y₁, z₁ - y₂)` map `(ℤ/m)³` to itself with fibres of size at most
two, so `#{(y₁, y₂, z₁) : (y₁ + y₂)(z₁ - y₁)(z₁ - y₂) = 0} ≤ 2 (m τ(m))²`. -/
theorem card_filter_cubic_le :
    #{x : ZMod m × ZMod m × ZMod m | (x.1 + x.2.1) * (x.2.2 - x.1) * (x.2.2 - x.2.1) = 0} ≤
      2 * (m * m.divisors.card) ^ 2 := by
  set L : ZMod m × ZMod m × ZMod m → ZMod m × ZMod m × ZMod m :=
    fun x => (x.1 + x.2.1, x.2.2 - x.1, x.2.2 - x.2.1)
  refine (card_le_mul_card_image_of_maps_to (f := L)
    (t := {v : ZMod m × ZMod m × ZMod m | v.1 * v.2.1 * v.2.2 = 0}) (fun x hx => ?_) 2
    (fun v _ => ?_)).trans (Nat.mul_le_mul_left _ card_filter_mul_mul_eq_zero_le)
  · exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hx).2⟩
  -- a fibre injects into `{t : 2 t = 0}` through `x ↦ x.1 - x₀.1`
  by_cases hv : ∃ x₀, L x₀ = v
  · obtain ⟨x₀, rfl⟩ := hv
    refine (card_le_card_of_injOn (fun x => x.1 - x₀.1) (fun x hx => ?_) ?_).trans
      card_filter_two_mul_eq_zero_le
    · have h := Prod.ext_iff.1 (mem_filter.1 hx).2
      have h' := Prod.ext_iff.1 h.2
      simp only [L] at h h'
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      linear_combination h.1 + h'.2 - h'.1
    · intro x hx x' hx' hxx'
      have h := Prod.ext_iff.1 ((mem_filter.1 hx).2.trans (mem_filter.1 hx').2.symm)
      have h' := Prod.ext_iff.1 h.2
      simp only [L] at h h' hxx'
      have h1 : x.1 = x'.1 := by simpa using hxx'
      ext
      · exact h1
      · linear_combination h.1 - h1
      · linear_combination h'.1 + h1
  · simp only [not_exists] at hv
    rw [filter_false_of_mem fun x _ => hv x, card_empty]
    exact Nat.zero_le _

/-- At most `(h, k, m)` residues `C` mod `m` satisfy `h C = k C = 0`. -/
theorem card_filter_mul_eq_zero_and_le (h k : ℕ) :
    #{C : ZMod m | (h : ZMod m) * C = 0 ∧ (k : ZMod m) * C = 0} ≤ Nat.gcd (Nat.gcd h k) m := by
  refine le_trans (card_le_card fun C hC => mem_filter.2 ⟨mem_univ _, ?_⟩)
    (card_filter_natCast_mul_eq_zero_le (Nat.gcd h k))
  obtain ⟨hh, hk⟩ := (mem_filter.1 hC).2
  rw [natCast_mul_eq_zero_iff] at hh hk ⊢
  rw [← Nat.gcd_mul_right]
  exact Nat.dvd_gcd hh hk

/-! ### The fourth moment -/

variable (m) in
/-- `T_m`: the number of unit quadruples `((y₁, y₂), (z₁, z₂))` mod `m` with
`y₁ + y₂ = z₁ + z₂` and `y₁⁻¹ + y₂⁻¹ = z₁⁻¹ + z₂⁻¹`. -/
noncomputable def quadCount : ℕ :=
  #{q : ((ZMod m)ˣ × (ZMod m)ˣ) × ((ZMod m)ˣ × (ZMod m)ˣ) |
    (q.1.1 : ZMod m) + q.1.2 = q.2.1 + q.2.2 ∧
      ((q.1.1⁻¹ : (ZMod m)ˣ) : ZMod m) + ↑q.1.2⁻¹ = ↑q.2.1⁻¹ + ↑q.2.2⁻¹}

/-- `T_m ≤ 2 (m τ(m))²`: the quadruple is determined by `(y₁, y₂, z₁)`, and clearing
denominators gives `(y₁ + y₂)(z₁ - y₁)(z₁ - y₂) = 0`. -/
theorem quadCount_le : quadCount m ≤ 2 * (m * m.divisors.card) ^ 2 := by
  refine le_trans (card_le_card_of_injOn
    (fun q => ((q.1.1 : ZMod m), (q.1.2 : ZMod m), (q.2.1 : ZMod m))) (fun q hq => ?_)
    fun q hq q' hq' hqq' => ?_) card_filter_cubic_le
  · obtain ⟨⟨y₁, y₂⟩, z₁, z₂⟩ := q
    obtain ⟨h₁, h₂⟩ := (mem_filter.1 hq).2
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    have hy₁ := y₁.mul_inv
    have hy₂ := y₂.mul_inv
    have hz₁ := z₁.mul_inv
    have hz₂ := z₂.mul_inv
    dsimp only at h₁ h₂
    linear_combination (↑y₁ * ↑y₂ - (↑y₁ + ↑y₂) * ↑z₁ : ZMod m) * h₁ -
      (↑y₁ * ↑y₂ * ↑z₁ * ↑z₂ : ZMod m) * h₂ + (↑y₂ * ↑z₁ * ↑z₂ : ZMod m) * hy₁ +
      (↑y₁ * ↑z₁ * ↑z₂ : ZMod m) * hy₂ - (↑y₁ * ↑y₂ * ↑z₂ : ZMod m) * hz₁ -
      (↑y₁ * ↑y₂ * ↑z₁ : ZMod m) * hz₂
  · obtain ⟨⟨y₁, y₂⟩, z₁, z₂⟩ := q
    obtain ⟨⟨y₁', y₂'⟩, z₁', z₂'⟩ := q'
    simp only [Prod.mk.injEq] at hqq'
    obtain ⟨h₁, h₂, h₃⟩ := hqq'
    have h := (mem_filter.1 hq).2.1
    have h' := (mem_filter.1 hq').2.1
    simp only [Prod.mk.injEq, Units.ext_iff]
    refine ⟨⟨h₁, h₂⟩, h₃, ?_⟩
    linear_combination h' - h + h₁ + h₂ - h₃

variable (m) in
/-- The Kloosterman sum over `ZMod m`: `∑_{u ∈ (ℤ/m)^×} e((a u + b u⁻¹)/m)`. -/
noncomputable def kloostermanZMod (a b : ZMod m) : ℂ :=
  ∑ u : (ZMod m)ˣ, ZMod.stdAddChar (a * (u : ZMod m) + b * ((u⁻¹ : (ZMod m)ˣ) : ZMod m))

/-- The `range`-based Kloosterman sum agrees with the sum over the units of `ZMod m`. -/
theorem kloosterman_eq_kloostermanZMod (h k : ℕ) :
    kloosterman m h k = kloostermanZMod m h k := by
  rw [kloosterman, kloostermanZMod]
  symm
  refine sum_bij' (fun u _ => (u : ZMod m).val)
    (fun y hy => ZMod.unitOfCoprime y (mem_filter.1 hy).2) (fun u _ => ?_) (fun y hy => ?_)
    (fun u _ => ?_) (fun y hy => ?_) (fun u _ => ?_)
  · exact mem_filter.2 ⟨mem_range.2 (ZMod.val_lt _), ZMod.val_coe_unit_coprime u⟩
  · exact mem_univ _
  · ext
    rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast,
      Nat.mod_eq_of_lt (mem_range.1 (mem_filter.1 hy).1)]
  · have hu : (h : ZMod m) * (u : ZMod m) + k * ((u⁻¹ : (ZMod m)ˣ) : ZMod m) =
        ((h * (u : ZMod m).val + k * (((u : ZMod m).val : ZMod m)⁻¹).val : ℕ) : ZMod m) := by
      push_cast
      simp only [ZMod.natCast_zmod_val, ZMod.inv_coe_unit]
    rw [hu, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
    push_cast
    ring_nf

/-- The fourth moment `∑_{a, b mod m} |K_m(a, b)|⁴ = m² T_m`, by additive orthogonality. -/
theorem sum_norm_kloostermanZMod_pow_four :
    ∑ a : ZMod m, ∑ b : ZMod m, ‖kloostermanZMod m a b‖ ^ 4 = (m : ℝ) ^ 2 * quadCount m := by
  set Q := ((ZMod m)ˣ × (ZMod m)ˣ) × ((ZMod m)ˣ × (ZMod m)ˣ)
  -- the sum and inverse-sum differences of a quadruple
  set X : Q → ZMod m := fun q => q.1.1 + q.1.2 - q.2.1 - q.2.2
  set Y : Q → ZMod m := fun q =>
    ((q.1.1⁻¹ : (ZMod m)ˣ) : ZMod m) + ↑q.1.2⁻¹ - ↑q.2.1⁻¹ - ↑q.2.2⁻¹
  -- expand `|K|⁴ = K² conj(K)²` as a sum over quadruples
  have hsq : ∀ f : (ZMod m)ˣ → ℂ, (∑ u, f u) * (∑ u, f u) = ∑ p : (ZMod m)ˣ × (ZMod m)ˣ,
      f p.1 * f p.2 := fun f => by
    rw [Fintype.sum_mul_sum]; exact (Fintype.sum_prod_type' _).symm
  have hexp : ∀ a b : ZMod m, ((‖kloostermanZMod m a b‖ ^ 4 : ℝ) : ℂ) =
      ∑ q : Q, ZMod.stdAddChar (a * X q) * ZMod.stdAddChar (b * Y q) := by
    intro a b
    have hconj : (starRingEnd ℂ) (kloostermanZMod m a b) = ∑ u : (ZMod m)ˣ,
        ZMod.stdAddChar (-(a * (u : ZMod m) + b * ((u⁻¹ : (ZMod m)ˣ) : ZMod m))) := by
      rw [kloostermanZMod, map_sum]
      exact sum_congr rfl fun u _ => (AddChar.map_neg_eq_conj _ _).symm
    rw [show ‖kloostermanZMod m a b‖ ^ 4 = (‖kloostermanZMod m a b‖ ^ 2) ^ 2 by ring,
      Complex.ofReal_pow, Complex.ofReal_pow, ← Complex.mul_conj', hconj, mul_pow, sq, sq,
      kloostermanZMod, hsq, hsq, Fintype.sum_mul_sum]
    refine (Fintype.sum_prod_type' _).symm.trans (sum_congr rfl fun q _ => ?_)
    simp only [← AddChar.map_add_eq_mul]
    congr 1
    simp only [X, Y]
    ring
  -- sum over `(a, b)` first: each orthogonality sum is `m` or `0`
  apply Complex.ofReal_injective
  calc ((∑ a : ZMod m, ∑ b : ZMod m, ‖kloostermanZMod m a b‖ ^ 4 : ℝ) : ℂ)
      = ∑ q : Q, (∑ a : ZMod m, ZMod.stdAddChar (a * X q)) *
          ∑ b : ZMod m, ZMod.stdAddChar (b * Y q) := by
        simp only [Complex.ofReal_sum, hexp, Fintype.sum_mul_sum]
        rw [sum_congr rfl fun a _ => sum_comm, sum_comm]
    _ = ∑ q : Q, (if X q = 0 then (m : ℂ) else 0) * (if Y q = 0 then (m : ℂ) else 0) := by
        simp only [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar m), ZMod.card, Nat.cast_ite,
          Nat.cast_zero]
    _ = (((m : ℝ) ^ 2 * quadCount m : ℝ) : ℂ) := by
        simp only [ite_zero_mul_ite_zero, ← sum_filter, sum_const, nsmul_eq_mul, quadCount,
          X, Y, sub_sub, sub_eq_zero]
        push_cast
        ring

/-! ### The orbit bound -/

/-- `K_m(a s, b s⁻¹) = K_m(a, b)` for a unit `s`: substitute `u ↦ s u`. -/
theorem kloostermanZMod_mul_units (a b : ZMod m) (s : (ZMod m)ˣ) :
    kloostermanZMod m (a * s) (b * ↑s⁻¹) = kloostermanZMod m a b := by
  refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun u => ?_
  simp only [Equiv.coe_mulLeft, mul_inv_rev, Units.val_mul]
  congr 1
  ring

/-- **The orbit bound** `φ(m) |K_m(h, k)|⁴ ≤ (h, k, m) ∑_{a, b} |K_m(a, b)|⁴`: the sum is
constant on the orbit `s ↦ (h s, k s⁻¹)`, whose fibres have at most `(h, k, m)` points. -/
theorem totient_mul_norm_pow_four_le (h k : ℕ) :
    (m.totient : ℝ) * ‖kloostermanZMod m h k‖ ^ 4 ≤
      (Nat.gcd (Nat.gcd h k) m : ℝ) *
        ∑ a : ZMod m, ∑ b : ZMod m, ‖kloostermanZMod m a b‖ ^ 4 := by
  set F : ZMod m × ZMod m → ℝ := fun p => ‖kloostermanZMod m p.1 p.2‖ ^ 4
  set f : (ZMod m)ˣ → ZMod m × ZMod m :=
    fun s => ((h : ZMod m) * s, (k : ZMod m) * ((s⁻¹ : (ZMod m)ˣ) : ZMod m))
  -- a fibre of `f` injects into `{C : h C = k C = 0}` through `s ↦ s - s₀`
  have hfib : ∀ p, #{s | f s = p} ≤ Nat.gcd (Nat.gcd h k) m := by
    intro p
    by_cases hp : ∃ s₀, f s₀ = p
    · obtain ⟨s₀, rfl⟩ := hp
      refine le_trans (card_le_card_of_injOn (fun s => (s : ZMod m) - s₀) (fun s hs => ?_)
        fun s _ s' _ hss' => Units.ext (sub_left_inj.1 hss')) (card_filter_mul_eq_zero_and_le h k)
      obtain ⟨e₁, e₂⟩ := Prod.ext_iff.1 (mem_filter.1 hs).2
      have hs := s.mul_inv
      have hs₀ := s₀.mul_inv
      refine mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
      · linear_combination e₁
      · linear_combination (-((s : ZMod m) * s₀)) * e₂ + (k * s₀ : ZMod m) * hs -
          (k * s : ZMod m) * hs₀
    · simp only [not_exists] at hp
      rw [filter_false_of_mem fun s _ => hp s, card_empty]
      exact Nat.zero_le _
  have hF : ∀ p, 0 ≤ F p := fun p => by positivity
  calc (m.totient : ℝ) * ‖kloostermanZMod m h k‖ ^ 4 = ∑ s, F (f s) := by
        simp only [F, f, kloostermanZMod_mul_units, sum_const, card_univ,
          ZMod.card_units_eq_totient, nsmul_eq_mul]
    _ = ∑ p ∈ univ.image f, #{s | f s = p} • F p := sum_comp _ _
    _ ≤ ∑ p ∈ univ.image f, Nat.gcd (Nat.gcd h k) m • F p :=
        sum_le_sum fun p _ => nsmul_le_nsmul_left (hF p) (hfib p)
    _ ≤ ∑ p, Nat.gcd (Nat.gcd h k) m • F p :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _ => nsmul_nonneg (hF p) _
    _ = _ := by
        rw [← smul_sum, nsmul_eq_mul, Fintype.sum_prod_type]

/-- `|K_m(h, k)|⁴ ≤ 2 (h, k, m) m³ τ(m)³`. -/
theorem norm_kloostermanZMod_pow_four_le (h k : ℕ) :
    ‖kloostermanZMod m h k‖ ^ 4 ≤
      2 * (Nat.gcd (Nat.gcd h k) m : ℝ) * (m : ℝ) ^ 3 * (m.divisors.card : ℝ) ^ 3 := by
  set K := ‖kloostermanZMod m h k‖
  set g := (Nat.gcd (Nat.gcd h k) m : ℝ)
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have h₁ := totient_mul_norm_pow_four_le (m := m) h k
  rw [sum_norm_kloostermanZMod_pow_four] at h₁
  have h₂ : (quadCount m : ℝ) ≤ 2 * (m * (m.divisors.card : ℝ)) ^ 2 := by
    exact_mod_cast quadCount_le
  have h₃ : (m : ℝ) ≤ m.totient * (m.divisors.card : ℝ) := by
    exact_mod_cast le_totient_mul_card_divisors m
  refine le_of_mul_le_mul_left ?_ hm
  calc (m : ℝ) * K ^ 4 ≤ m.totient * (m.divisors.card : ℝ) * K ^ 4 := by gcongr
    _ = (m.divisors.card : ℝ) * (m.totient * K ^ 4) := by ring
    _ ≤ (m.divisors.card : ℝ) * (g * ((m : ℝ) ^ 2 * quadCount m)) := by gcongr
    _ ≤ (m.divisors.card : ℝ) *
          (g * ((m : ℝ) ^ 2 * (2 * (m * (m.divisors.card : ℝ)) ^ 2))) := by gcongr
    _ = m * (2 * g * (m : ℝ) ^ 3 * (m.divisors.card : ℝ) ^ 3) := by ring

end Residues

/-- PD `det:weak-kloosterman`: `|K_m(h, k)| ≤ C_ε m^{3/4 + ε} (h, k, m)^{1/4}`. -/
theorem norm_kloosterman_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ m h k : ℕ, 1 ≤ m →
      ‖kloosterman m h k‖ ≤
        C * (m : ℝ) ^ (3 / 4 + ε) * ((Nat.gcd (Nat.gcd h k) m : ℕ) : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨D, hD⟩ := card_divisors_le_rpow (ε := 4 * ε / 3) (by positivity)
  have hD0 : 0 ≤ D := by linarith [show (1 : ℝ) ≤ D by simpa using hD 1 le_rfl]
  refine ⟨(2 * D ^ 3) ^ (1 / 4 : ℝ), fun m h k hm => ?_⟩
  have : NeZero m := ⟨by omega⟩
  rw [kloosterman_eq_kloostermanZMod]
  set g := ((Nat.gcd (Nat.gcd h k) m : ℕ) : ℝ)
  have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  -- the fourth power of the claimed bound is `2 D³ m^{3 + 4 ε} (h, k, m)`
  have hX : ((2 * D ^ 3) ^ (1 / 4 : ℝ) * (m : ℝ) ^ (3 / 4 + ε) * g ^ (1 / 4 : ℝ)) ^ 4 =
      2 * D ^ 3 * (m : ℝ) ^ (3 + 4 * ε) * g := by
    rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast (by positivity),
      ← Real.rpow_mul_natCast hm0, ← Real.rpow_mul_natCast hg0,
      show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, show (3 / 4 + ε) * (4 : ℕ) = 3 + 4 * ε by
        push_cast; ring, Real.rpow_one, Real.rpow_one]
  -- the divisor bound with exponent `4 ε / 3`
  have hτ : ((m.divisors.card : ℝ)) ^ 3 ≤ D ^ 3 * (m : ℝ) ^ (4 * ε) := by
    calc ((m.divisors.card : ℝ)) ^ 3 ≤ (D * (m : ℝ) ^ (4 * ε / 3)) ^ 3 := by
          gcongr; exact hD m hm
      _ = D ^ 3 * (m : ℝ) ^ (4 * ε) := by
          rw [mul_pow, ← Real.rpow_mul_natCast hm0]; norm_num
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) four_ne_zero).1 ?_
  rw [hX]
  calc ‖kloostermanZMod m h k‖ ^ 4
      ≤ 2 * g * (m : ℝ) ^ 3 * (m.divisors.card : ℝ) ^ 3 :=
        norm_kloostermanZMod_pow_four_le h k
    _ ≤ 2 * g * (m : ℝ) ^ 3 * (D ^ 3 * (m : ℝ) ^ (4 * ε)) := by gcongr
    _ = 2 * D ^ 3 * (m : ℝ) ^ (3 + 4 * ε) * g := by
        rw [Real.rpow_add (by exact_mod_cast hm), Real.rpow_ofNat]
        ring

end Erdos408.OneSided
