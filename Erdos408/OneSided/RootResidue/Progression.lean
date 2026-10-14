module

public import Erdos408.OneSided.Analysis.Divisor
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Progressions and the Euler factor

The elementary counts of PD Lemma 3.3 (`blueprint/one_sided_type_ii.md` §5.2).

* `prog α β q r = {c ∈ [α, β) : c ≡ r (mod q)}`, written as the image of a range of `j` under
  `j ↦ r + q j`, has `(β - α)/q + O(1)` elements.
* `abs_card_coprime_sub_le`: the `c ∈ [α, β)` with `c ≡ w (mod S)` and `(c, u) = 1` number
  `(β - α)/S · ∑_{l ∣ u, (l, S) = 1} μ(l)/l + O(τ(u))`, if `w` is a unit mod `(u, S)`.
* `abs_sum_eulerFactor_sub_le`: the Euler factor `∑_{l ∣ u, (l, S) = 1} μ(l)/l` averages over
  `u ∈ [α, β)`, `u ≡ w (mod S)`, to `(β - α)/S · ∑_{(l, S) = 1} μ(l)/l²`, with error
  `3 + log(β + 1)`.
-/

@[expose] public section

namespace Erdos408.OneSided.RootResidue

open Finset

/-! ### Progressions -/

/-- `n ∈ [⌈α⌉, ⌈β⌉)` exactly when `α ≤ n < β`. -/
theorem mem_Ico_ceil {α β : ℝ} {n : ℕ} : n ∈ Ico ⌈α⌉₊ ⌈β⌉₊ ↔ α ≤ n ∧ (n : ℝ) < β := by
  rw [mem_Ico, Nat.ceil_le, Nat.lt_ceil]

/-- `⌈z⌉₊ < z + 1` for `z > -1`. -/
theorem natCeil_lt_add_one {z : ℝ} (hz : -1 < z) : (⌈z⌉₊ : ℝ) < z + 1 := by
  rcases le_total 0 z with h | h
  · exact Nat.ceil_lt_add_one h
  · rw [Nat.ceil_eq_zero.2 h, Nat.cast_zero]
    linarith

/-- The progression `{c ∈ [α, β) : c ≡ r (mod q)}`, as the image of `j ↦ r + q j`. -/
noncomputable def prog (α β : ℝ) (q r : ℕ) : Finset ℕ :=
  (Ico ⌈(α - r) / q⌉₊ ⌈(β - r) / q⌉₊).image fun j => r + q * j

/-- `c ∈ prog α β q r` exactly when `c ≡ r (mod q)` and `α ≤ c < β`. -/
theorem mem_prog {α β : ℝ} {q r c : ℕ} (hq : 0 < q) (hr : r < q) :
    c ∈ prog α β q r ↔ c % q = r ∧ α ≤ c ∧ (c : ℝ) < β := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.2 hq
  rw [prog, mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨h₁, h₂⟩ := mem_Ico_ceil.1 hj
    rw [div_le_iff₀ hq'] at h₁
    rw [lt_div_iff₀ hq'] at h₂
    refine ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr], ?_, ?_⟩ <;> push_cast <;>
      linarith
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨c / q, mem_Ico_ceil.2 ⟨?_, ?_⟩, ?_⟩
    · have hc : (c : ℝ) = r + q * (c / q : ℕ) := by
        exact_mod_cast (h₁ ▸ Nat.mod_add_div c q).symm
      rw [div_le_iff₀ hq']
      linarith
    · have hc : (c : ℝ) = r + q * (c / q : ℕ) := by
        exact_mod_cast (h₁ ▸ Nat.mod_add_div c q).symm
      rw [lt_div_iff₀ hq']
      linarith
    · rw [← h₁, Nat.mod_add_div]

/-- `|#prog α β q r - (β - α)/q| ≤ 1` for `0 ≤ α ≤ β` and `r < q`. -/
theorem abs_card_prog_sub_le {α β : ℝ} {q r : ℕ} (hq : 0 < q) (hr : r < q) (hα : 0 ≤ α)
    (hαβ : α ≤ β) : |(#(prog α β q r) : ℝ) - (β - α) / q| ≤ 1 := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.2 hq
  set x := (α - r) / q
  set y := (β - r) / q
  have hx : -1 < x := by
    rw [lt_div_iff₀ hq']
    have : (r : ℝ) < q := by exact_mod_cast hr
    linarith
  have hxy : x ≤ y := div_le_div_of_nonneg_right (by linarith) hq'.le
  have hyx : (β - α) / q = y - x := by simp only [x, y]; ring
  have hcard : #(prog α β q r) = ⌈y⌉₊ - ⌈x⌉₊ := by
    rw [prog, card_image_of_injective _ fun i j hij => by simpa [hq.ne'] using hij, Nat.card_Ico]
  rw [hcard, Nat.cast_sub (Nat.ceil_mono hxy), hyx, abs_le]
  have h₁ := Nat.le_ceil x
  have h₂ := Nat.le_ceil y
  have h₃ := natCeil_lt_add_one hx
  have h₄ := natCeil_lt_add_one (hx.trans_le hxy)
  constructor <;> linarith

/-- The `x ∈ [α, β)` with `x ≡ w (mod S)` and `l ∣ x`, for `(l, S) = 1`, form one progression
mod `S l` (CRT), so there are `(β - α)/(S l) + O(1)` of them. -/
theorem abs_card_modEq_dvd_sub_le {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) {S l : ℕ} (hS : 0 < S)
    (hl : 0 < l) (hlS : l.Coprime S) (w : ℕ) :
    |(#{x ∈ Ico ⌈α⌉₊ ⌈β⌉₊ | x ≡ w [MOD S] ∧ l ∣ x} : ℝ) - (β - α) / (S * l : ℕ)| ≤ 1 := by
  have hq : 0 < S * l := Nat.mul_pos hS hl
  set z := (Nat.chineseRemainder hlS.symm w 0 : ℕ)
  have hz := (Nat.chineseRemainder hlS.symm w 0).2
  have hset : ({x ∈ Ico ⌈α⌉₊ ⌈β⌉₊ | x ≡ w [MOD S] ∧ l ∣ x} : Finset ℕ) =
      prog α β (S * l) (z % (S * l)) := by
    ext x
    rw [mem_filter, mem_Ico_ceil, mem_prog hq (Nat.mod_lt _ hq)]
    -- `x ≡ w (S) ∧ l ∣ x ↔ x ≡ z (S l)`
    have hiff : (x ≡ w [MOD S] ∧ l ∣ x) ↔ x ≡ z [MOD S * l] := by
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hlS.symm, ← Nat.modEq_zero_iff_dvd]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁.trans hz.1.symm, h₂.trans hz.2.symm⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁.trans hz.1, h₂.trans hz.2⟩
    rw [hiff]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩
  rw [hset]
  exact abs_card_prog_sub_le hq (Nat.mod_lt _ hq) hα hαβ

/-! ### Coprime counts -/

/-- `∑_{d ∣ n} μ(d) = [n = 1]`. -/
theorem sum_divisors_moebius (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => (f n : ℝ))
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  push_cast at h
  exact h

/-- Möbius inversion of coprimality: `[(c, u) = 1] = ∑_{l ∣ u, l ∣ c} μ(l)` for `u ≠ 0`. -/
theorem coprime_indicator_eq {u : ℕ} (hu : u ≠ 0) (c : ℕ) :
    (if c.Coprime u then (1 : ℝ) else 0) =
      ∑ l ∈ u.divisors with l ∣ c, (ArithmeticFunction.moebius l : ℝ) := by
  have hdiv : (Nat.gcd c u).divisors = {l ∈ u.divisors | l ∣ c} := by
    ext l
    simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff, ne_eq,
      Nat.gcd_eq_zero_iff, hu, and_false, not_false_eq_true, and_true]
    tauto
  rw [← hdiv, sum_divisors_moebius]

/-- The Euler factor `∑_{l ∣ u, (l, S) = 1} μ(l)/l = ∏_{p ∣ u, p ∤ S}(1 - 1/p)`. -/
noncomputable def eulerFactor (S u : ℕ) : ℝ :=
  ∑ l ∈ u.divisors with l.Coprime S, (ArithmeticFunction.moebius l : ℝ) / l

/-- `|∑_{l ∣ u, (l, S) = 1} μ(l)/l| ≤ τ(u)`. -/
theorem abs_eulerFactor_le (S u : ℕ) : |eulerFactor S u| ≤ u.divisors.card := by
  calc |eulerFactor S u| ≤ ∑ l ∈ u.divisors with l.Coprime S,
        |(ArithmeticFunction.moebius l : ℝ) / l| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ u.divisors with l.Coprime S, (1 : ℝ) := sum_le_sum fun l hl => ?_
    _ ≤ u.divisors.card := ?_
  · have hl1 : (1 : ℝ) ≤ l := by
      exact_mod_cast Nat.pos_of_mem_divisors (mem_filter.1 hl).1
    rw [abs_div, Nat.abs_cast]
    have : |(ArithmeticFunction.moebius l : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    exact (div_le_div_of_nonneg_right this (by linarith)).trans
      ((div_le_one (by linarith)).2 hl1)
  · rw [sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast card_filter_le _ _

/-- **The coprime count.** If `w` is a unit mod `(u, S)`, the `c ∈ [α, β)` with
`c ≡ w (mod S)` and `(c, u) = 1` number `(β - α)/S · eulerFactor S u + O(τ(u))`. -/
theorem abs_card_coprime_sub_le {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) {S u : ℕ} (hS : 0 < S)
    (hu : 0 < u) {w : ℕ} (hw : w.Coprime (Nat.gcd u S)) :
    |(#{c ∈ Ico ⌈α⌉₊ ⌈β⌉₊ | c ≡ w [MOD S] ∧ c.Coprime u} : ℝ) -
        (β - α) / S * eulerFactor S u| ≤ u.divisors.card := by
  set I := Ico ⌈α⌉₊ ⌈β⌉₊
  set N : ℕ → ℝ := fun l => #{x ∈ I | x ≡ w [MOD S] ∧ l ∣ x}
  -- Möbius inversion of `(c, u) = 1`
  have hinv : (#{c ∈ I | c ≡ w [MOD S] ∧ c.Coprime u} : ℝ) =
      ∑ l ∈ u.divisors, (ArithmeticFunction.moebius l : ℝ) * N l := by
    rw [← filter_filter, card_filter, Nat.cast_sum]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, coprime_indicator_eq hu.ne']
    rw [sum_comm' (t' := u.divisors) (s' := fun l => {x ∈ I | x ≡ w [MOD S] ∧ l ∣ x})]
    · refine sum_congr rfl fun l _ => ?_
      rw [sum_const, nsmul_eq_mul, mul_comm]
    · intro x l
      simp only [mem_filter]
      tauto
  -- the divisors `l` sharing a prime with `S` contribute nothing
  have hzero : ∀ l ∈ u.divisors, ¬ l.Coprime S → N l = 0 := by
    intro l hl hlS
    obtain ⟨p, hp, hpl, hpS⟩ := Nat.Prime.not_coprime_iff_dvd.1 hlS
    simp only [N, Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
    rintro x - ⟨hxw, hlx⟩
    have hpu : p ∣ Nat.gcd u S := Nat.dvd_gcd (hpl.trans (Nat.dvd_of_mem_divisors hl)) hpS
    have hpw : p ∣ w := by
      have := (Nat.ModEq.of_dvd hpS hxw).symm
      exact (Nat.modEq_zero_iff_dvd.1 (this.trans
        (Nat.modEq_zero_iff_dvd.2 (hpl.trans hlx))))
    have h1 : p ∣ 1 := by
      have := Nat.dvd_gcd hpw hpu
      rwa [hw.gcd_eq_one] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hrestrict : ∑ l ∈ u.divisors, (ArithmeticFunction.moebius l : ℝ) * N l =
      ∑ l ∈ u.divisors with l.Coprime S, (ArithmeticFunction.moebius l : ℝ) * N l := by
    rw [sum_filter]
    refine sum_congr rfl fun l hl => ?_
    by_cases hlS : l.Coprime S
    · rw [ite_eq_left_iff.2 fun h => absurd hlS h]
    · rw [ite_eq_right_iff.2 fun h => absurd h hlS, hzero l hl hlS, mul_zero]
  have hmain : (β - α) / S * eulerFactor S u = ∑ l ∈ u.divisors with l.Coprime S,
      (ArithmeticFunction.moebius l : ℝ) * ((β - α) / (S * l : ℕ)) := by
    rw [eulerFactor, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    push_cast
    ring
  rw [hinv, hrestrict, hmain, ← sum_sub_distrib]
  calc |∑ l ∈ u.divisors with l.Coprime S, ((ArithmeticFunction.moebius l : ℝ) * N l -
        (ArithmeticFunction.moebius l : ℝ) * ((β - α) / (S * l : ℕ)))|
      ≤ ∑ l ∈ u.divisors with l.Coprime S, (1 : ℝ) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l hl => ?_)
        have hl0 : 0 < l := Nat.pos_of_mem_divisors (mem_filter.1 hl).1
        rw [← mul_sub, abs_mul]
        have h₁ : |(ArithmeticFunction.moebius l : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have h₂ := abs_card_modEq_dvd_sub_le hα hαβ hS hl0 (mem_filter.1 hl).2 w
        calc |(ArithmeticFunction.moebius l : ℝ)| * |N l - (β - α) / (S * l : ℕ)|
            ≤ 1 * 1 := mul_le_mul h₁ h₂ (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ ≤ u.divisors.card := by
        rw [sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast card_filter_le _ _

/-! ### The average of the Euler factor -/

/-- The terms `[(l, S) = 1] μ(l)/l²` of the coprime density. -/
noncomputable def densityTerm (S l : ℕ) : ℝ :=
  if l.Coprime S then (ArithmeticFunction.moebius l : ℝ) / l ^ 2 else 0

/-- The coprime density `∑_{(l, S) = 1} μ(l)/l² = c₂ ∏_{p ∣ S}(1 - p^{-2})⁻¹`. -/
noncomputable def coprimeDensity (S : ℕ) : ℝ := ∑' l : ℕ, densityTerm S l

/-- `|[(l, S) = 1] μ(l)/l²| ≤ 1/l²`. -/
theorem abs_densityTerm_le (S l : ℕ) : |densityTerm S l| ≤ ((l : ℝ) ^ 2)⁻¹ := by
  unfold densityTerm
  split_ifs
  · rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (l : ℝ) ^ 2), div_eq_mul_inv]
    have : |(ArithmeticFunction.moebius l : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    exact (mul_le_of_le_one_left (by positivity) this)
  · rw [abs_zero]
    positivity

/-- The terms of the coprime density are summable. -/
theorem summable_densityTerm (S : ℕ) : Summable (densityTerm S) :=
  Summable.of_norm_bounded (Real.summable_nat_pow_inv.2 one_lt_two) fun l => by
    rw [Real.norm_eq_abs]; exact abs_densityTerm_le S l

/-- The tail bound `|∑_{l ≥ K} [(l, S) = 1] μ(l)/l²| ≤ 2/K`. -/
theorem abs_coprimeDensity_sub_le (S : ℕ) {K : ℕ} (hK : 0 < K) :
    |coprimeDensity S - ∑ l ∈ range K, densityTerm S l| ≤ 2 / K := by
  set g : ℕ → ℝ := fun i => (((i + K : ℕ) : ℝ) ^ 2)⁻¹
  have hg0 : ∀ i, 0 ≤ g i := fun i => by positivity
  -- the partial sums of `g` are at most `2 / K`
  have hpart : ∀ n, ∑ i ∈ range n, g i ≤ 2 / K := by
    intro n
    have h := sum_Ioo_inv_sq_le (α := ℝ) (K - 1) (K + n)
    rw [Nat.cast_sub hK, Nat.cast_one, sub_add_cancel] at h
    refine le_trans (le_of_eq ?_) h
    have hI : Ioo (K - 1) (K + n) = Ico K (K + n) := by ext; simp only [mem_Ioo, mem_Ico]; omega
    rw [hI, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    exact sum_congr rfl fun i _ => by simp only [g]; push_cast; ring
  have hgs : Summable g := summable_of_sum_range_le hg0 hpart
  have htail : Summable fun i => densityTerm S (i + K) :=
    (summable_nat_add_iff K).2 (summable_densityTerm S)
  rw [coprimeDensity, ← (summable_densityTerm S).sum_add_tsum_nat_add K, add_sub_cancel_left]
  calc |∑' i, densityTerm S (i + K)| ≤ ∑' i, |densityTerm S (i + K)| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' i, g i := by
        refine htail.abs.tsum_le_tsum (fun i => ?_) hgs
        have := abs_densityTerm_le S (i + K)
        simpa only [g] using this
    _ ≤ 2 / K := Real.tsum_le_of_sum_range_le hg0 hpart

/-- **The Euler average.** For `1 ≤ α ≤ β`,
`∑_{u ∈ [α, β), u ≡ w (S)} eulerFactor S u = (β - α)/S · coprimeDensity S + O(log β)`:
expand the factor and count the `u` in each progression `u ≡ w (S)`, `l ∣ u`. -/
theorem abs_sum_eulerFactor_sub_le {α β : ℝ} (hα : 1 ≤ α) (hαβ : α ≤ β) {S : ℕ} (hS : 0 < S)
    (w : ℕ) :
    |∑ u ∈ Ico ⌈α⌉₊ ⌈β⌉₊ with u ≡ w [MOD S], eulerFactor S u -
        (β - α) / S * coprimeDensity S| ≤ 3 + Real.log (β + 1) := by
  set I := Ico ⌈α⌉₊ ⌈β⌉₊
  set N := ⌈β⌉₊
  set L := ({l ∈ Icc 1 N | l.Coprime S} : Finset ℕ)
  set C : ℕ → ℝ := fun l => #{x ∈ I | x ≡ w [MOD S] ∧ l ∣ x}
  have hβ : 1 ≤ β := hα.trans hαβ
  have hN : (N : ℝ) < β + 1 := Nat.ceil_lt_add_one (by linarith)
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; linarith)
  -- step 1: swap the sums
  have hswap : ∑ u ∈ I with u ≡ w [MOD S], eulerFactor S u =
      ∑ l ∈ L, (ArithmeticFunction.moebius l : ℝ) / l * C l := by
    have hu : ∀ u ∈ ({u ∈ I | u ≡ w [MOD S]} : Finset ℕ), eulerFactor S u =
        ∑ l ∈ L, if l ∣ u then (ArithmeticFunction.moebius l : ℝ) / l else 0 := by
      intro u hu
      have hu1 : 1 ≤ u := Nat.one_le_iff_ne_zero.2 fun h => by
        have := (mem_Ico_ceil.1 (mem_filter.1 hu).1).1
        rw [h, Nat.cast_zero] at this
        linarith
      have huN : u < N := (mem_Ico.1 (mem_filter.1 hu).1).2
      rw [eulerFactor, ← sum_filter]
      refine sum_congr ?_ fun _ _ => rfl
      ext l
      simp only [mem_filter, Nat.mem_divisors, mem_Icc, L]
      constructor
      · rintro ⟨⟨hlu, -⟩, hlS⟩
        exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hlu hu1, (Nat.le_of_dvd hu1 hlu).trans huN.le⟩, hlS⟩, hlu⟩
      · rintro ⟨⟨-, hlS⟩, hlu⟩
        exact ⟨⟨hlu, by omega⟩, hlS⟩
    rw [sum_congr rfl hu, sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm, filter_filter]
  -- step 2: the main term in terms of the partial density
  have hpartial : ∑ l ∈ L, (ArithmeticFunction.moebius l : ℝ) / l * ((β - α) / (S * l : ℕ)) =
      (β - α) / S * ∑ l ∈ range (N + 1), densityTerm S l := by
    have hL : ∑ l ∈ range (N + 1), densityTerm S l = ∑ l ∈ L, densityTerm S l := by
      refine (sum_subset (fun l hl => ?_) fun l _ hl => ?_).symm
      · have := mem_Icc.1 (mem_filter.1 hl).1
        exact mem_range.2 (by omega)
      · unfold densityTerm
        split_ifs with hlS
        · have hl0 : l = 0 := by
            by_contra h0
            exact hl (mem_filter.2 ⟨mem_Icc.2 ⟨Nat.pos_of_ne_zero h0,
              by have := mem_range.1 ‹l ∈ range (N + 1)›; omega⟩, hlS⟩)
          simp [hl0]
        · rfl
    rw [hL, mul_sum]
    refine sum_congr rfl fun l hl => ?_
    rw [densityTerm, ite_eq_left_iff.2 fun h => absurd (mem_filter.1 hl).2 h]
    push_cast
    ring
  -- step 3: the progression counts, and the tail of the density
  have hcount : |∑ l ∈ L, (ArithmeticFunction.moebius l : ℝ) / l *
      (C l - (β - α) / (S * l : ℕ))| ≤ 1 + Real.log (β + 1) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ l ∈ L, |(ArithmeticFunction.moebius l : ℝ) / l * (C l - (β - α) / (S * l : ℕ))|
        ≤ ∑ l ∈ L, (l : ℝ)⁻¹ := by
          refine sum_le_sum fun l hl => ?_
          have hl1 := (mem_Icc.1 (mem_filter.1 hl).1).1
          have h₁ : |(ArithmeticFunction.moebius l : ℝ)| ≤ 1 := by
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          have h₂ := abs_card_modEq_dvd_sub_le (by linarith) hαβ hS hl1 (mem_filter.1 hl).2 w
          rw [abs_mul, abs_div, Nat.abs_cast, div_eq_mul_inv]
          calc |(ArithmeticFunction.moebius l : ℝ)| * (l : ℝ)⁻¹ * |C l - (β - α) / (S * l : ℕ)|
              ≤ 1 * (l : ℝ)⁻¹ * 1 := by gcongr
            _ = (l : ℝ)⁻¹ := by ring
      _ ≤ ∑ l ∈ Icc 1 N, (l : ℝ)⁻¹ :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
      _ ≤ 1 + Real.log N := sum_Icc_inv_le N
      _ ≤ 1 + Real.log (β + 1) := by
          have : (0 : ℝ) < N := by exact_mod_cast hN1
          gcongr
  have htail : |(β - α) / S * (∑ l ∈ range (N + 1), densityTerm S l - coprimeDensity S)| ≤ 2 := by
    have h := abs_coprimeDensity_sub_le S (Nat.succ_pos N)
    rw [abs_sub_comm] at h
    have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast hS
    have hβN : β - α ≤ ((N + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil β]
    rw [abs_mul, abs_of_nonneg (div_nonneg (by linarith) (by linarith))]
    calc (β - α) / S * |∑ l ∈ range (N + 1), densityTerm S l - coprimeDensity S|
        ≤ ((N + 1 : ℕ) : ℝ) * (2 / ((N + 1 : ℕ) : ℝ)) := by
          gcongr
          exact (div_le_self (by linarith) hS1).trans hβN
      _ = 2 := by field_simp
  rw [hswap]
  have hsplit : ∑ l ∈ L, (ArithmeticFunction.moebius l : ℝ) / l * C l -
      (β - α) / S * coprimeDensity S =
      ∑ l ∈ L, (ArithmeticFunction.moebius l : ℝ) / l * (C l - (β - α) / (S * l : ℕ)) +
        (β - α) / S * (∑ l ∈ range (N + 1), densityTerm S l - coprimeDensity S) := by
    simp only [mul_sub, sum_sub_distrib]
    rw [hpartial]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  linarith

end Erdos408.OneSided.RootResidue
