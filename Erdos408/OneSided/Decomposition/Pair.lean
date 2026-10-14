import Erdos408.OneSided.Cauchy
import Erdos408.OneSided.Decomposition.Count

/-!
# The two squares at fixed label products

`Q_Y - Q_Y^maj` is `∏V_i⁻² ∑_{p, p'} η(a/Y) η(b/Y) E(a, b)` with `a = ∏ p_i`, `b = ∏ p'_i`
and the pair error
`E(a, b) = ∑_{m,n,r,s} α_m ᾱ_r β_n β̄_s ([∃ h ≥ 1 : mn - 1 = ah, rs - 1 = bh] - 𝓗_𝔐)`.

For `a, b ∈ (Y, 4Y)`, `|E(a, b)| ≤ L^{4C} (∑_{h ≤ 4X/Y} τ(1 + ah) τ(1 + bh) +
(4 L^{3A₀}/Y) · 11 ∑_{k ≤ M} τ(k)²)`: the kernel `𝓗_𝔐` is at most the measure
`4 L^{3A₀}/Y` of the arcs and vanishes unless `|bmn - ars| < 5Y` (PD Lemma 1.2 and
`mem:unshared-collisions`).
-/

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

/-! ### The kernel -/

/-- `0 ≤ ψ ≤ 1`. -/
theorem norm_plateau_le (u : ℝ) : ‖((plateau u : ℝ) : ℂ)‖ ≤ 1 := by
  unfold plateau
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (smoothTransition.nonneg _)]
  exact smoothTransition.le_one _

/-- `ψ(u) ≠ 0` only for `|u| < 5`. -/
theorem abs_lt_of_plateau_ne_zero {u : ℝ} (h : plateau u ≠ 0) : |u| < 5 := by
  by_contra hu
  exact h (smoothTransition.zero_of_nonpos (by linarith))

/-- The arcs have total measure at most `4 L^{3A₀}/Y`: at most `L^{2A₀}` arcs of length
`4 L^{A₀}/Y`. -/
theorem norm_arcIntegral_le (A₀ : ℝ) {x Y : ℝ} (hL : 0 < Real.log x) (hY : 0 < Y) (n : ℤ) :
    ‖arcIntegral A₀ x Y n‖ ≤ 4 * Real.log x ^ (3 * A₀) / Y := by
  set L := Real.log x
  set N := ⌊L ^ A₀⌋₊
  have hLA : 0 ≤ L ^ A₀ := Real.rpow_nonneg hL.le _
  have hc : 0 ≤ 2 * L ^ A₀ / Y := by positivity
  -- each arc integral is at most its length
  have harc : ∀ h k : ℕ, ‖∫ θ in (-(2 * L ^ A₀ / Y))..(2 * L ^ A₀ / Y),
      Complex.exp (2 * π * Complex.I * ((((h : ℝ) / k + θ) * n : ℝ) : ℂ))‖ ≤
        4 * L ^ A₀ / Y := by
    intro h k
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) fun θ _ => ?_).trans ?_
    · rw [show 2 * π * Complex.I * ((((h : ℝ) / k + θ) * n : ℝ) : ℂ) =
          ((2 * π * (((h : ℝ) / k + θ) * n) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact (Complex.norm_exp_ofReal_mul_I _).le
    · rw [one_mul, sub_neg_eq_add, abs_of_nonneg (by linarith)]
      exact le_of_eq (by ring)
  calc ‖arcIntegral A₀ x Y n‖
      ≤ ∑ k ∈ Icc 1 N, ∑ h ∈ (range k).filter (fun h => Nat.Coprime h k),
          4 * L ^ A₀ / Y := by
        unfold arcIntegral
        refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
        exact (norm_sum_le _ _).trans (sum_le_sum fun h _ => harc h k)
    _ ≤ ∑ _k ∈ Icc 1 N, (N : ℝ) * (4 * L ^ A₀ / Y) := by
        refine sum_le_sum fun k hk => ?_
        rw [sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast (card_filter_le _ _).trans ((card_range k).le.trans (mem_Icc.1 hk).2)
    _ = (N : ℝ) * N * (4 * L ^ A₀ / Y) := by
        rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel, mul_assoc]
    _ ≤ L ^ A₀ * L ^ A₀ * (4 * L ^ A₀ / Y) := by
        have hN : (N : ℝ) ≤ L ^ A₀ := Nat.floor_le hLA
        gcongr
    _ = 4 * L ^ (3 * A₀) / Y := by
        rw [show 3 * A₀ = A₀ + A₀ + A₀ by ring, Real.rpow_add hL, Real.rpow_add hL]
        ring

/-- `|𝓗_𝔐(t; a, b)| ≤ 4 L^{3A₀}/Y`, and it vanishes unless `|t| ≤ 5Y`. -/
theorem norm_majorWeight_le (A₀ : ℝ) {x Y : ℝ} (hL : 0 < Real.log x) (hY : 0 < Y)
    (t a b : ℤ) :
    ‖majorWeight A₀ x Y t a b‖ ≤
      4 * Real.log x ^ (3 * A₀) / Y * (if |(t : ℝ)| ≤ 5 * Y then 1 else 0) := by
  unfold majorWeight
  split_ifs with ht
  · rw [mul_one, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_plateau_le _) |>.trans
      (norm_arcIntegral_le A₀ hL hY _)
  · -- outside `|t| ≤ 5Y` the plateau vanishes
    have hψ : plateau (t / Y) = 0 := by
      by_contra hψ
      have := abs_lt_of_plateau_ne_zero hψ
      rw [abs_div, abs_of_pos hY, div_lt_iff₀ hY] at this
      exact ht this.le
    rw [hψ, mul_zero, Complex.ofReal_zero, zero_mul, norm_zero]

/-! ### The pair error -/

open scoped Classical in
/-- The pair error `E(a, b)`: the inner sum of `Q_Y - Q_Y^maj` at the label products
`a, b`. -/
noncomputable def pairError (A₀ x : ℝ) (d : Data K) (Y : ℝ) (a b : ℕ) : ℂ :=
  ∑ m ∈ d.mRange, ∑ n ∈ d.nRange, ∑ r ∈ d.mRange, ∑ s ∈ d.nRange,
    d.α m * star (d.α r) * d.β n * star (d.β s) *
      ((if ∃ h, 1 ≤ h ∧ m * n - 1 = a * h ∧ r * s - 1 = b * h then 1 else 0) -
        majorWeight A₀ x Y (b * m * n - a * r * s) a b)

/-- `Q_Y - Q_Y^maj = ∏V_i⁻² ∑_{p, p'} η(a/Y) η(b/Y) E(a, b)`. -/
theorem cauchySquare_sub_majorSquare (A₀ x : ℝ) (d : Data K) (Y : ℝ) :
    cauchySquare x d Y - majorSquare A₀ x d Y =
      ((d.bandMass x)⁻¹ ^ 2 : ℝ) * ∑ p ∈ d.labels x, ∑ p' ∈ d.labels x,
        (dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) : ℝ) *
          pairError A₀ x d Y (∏ i, p i) (∏ i, p' i) := by
  unfold cauchySquare majorSquare pairError
  rw [← mul_sub, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun p _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun p' _ => ?_
  rw [← mul_sub]
  congr 1
  simp only [← sum_sub_distrib]
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => sum_congr rfl fun r _ =>
    sum_congr rfl fun s _ => ?_
  split_ifs <;> ring

/-- The pair error at `a, b ∈ (Y, 4Y)`: at most
`L^{4C} (∑_{h ≤ 4X/Y} τ(1 + ah) τ(1 + bh) + (4 L^{3A₀}/Y) · 11 ∑_{k ≤ M} τ(k)²)`. -/
theorem norm_pairError_le (A₀ : ℝ) {C x : ℝ} {d : Data K} (hL : 0 < Real.log x)
    (hα : ∀ m, ‖d.α m‖ ≤ Real.log x ^ C) (hβ : ∀ n, ‖d.β n‖ ≤ Real.log x ^ C)
    (hHm : 1 ≤ d.Hm) (hHn : 1 ≤ d.Hn) {Y : ℝ} (hY : 0 < Y) {a b : ℕ} (ha : Y < a)
    (hb : Y < b) :
    ‖pairError A₀ x d Y a b‖ ≤ Real.log x ^ (4 * C) *
      (∑ h ∈ Icc 1 ⌊4 * d.X / Y⌋₊, ((1 + a * h).divisors.card : ℝ) *
          (1 + b * h).divisors.card +
        4 * Real.log x ^ (3 * A₀) / Y *
          (11 * ∑ k ∈ Icc 1 (⌊2 * d.Hm⌋₊ * ⌊2 * d.Hn⌋₊), (k.divisors.card : ℝ) ^ 2)) := by
  classical
  set L := Real.log x
  set w := 4 * L ^ (3 * A₀) / Y
  have hw : 0 ≤ w := by positivity
  have ha0 : 0 < a := by exact_mod_cast hY.trans ha
  have hb0 : 0 < b := by exact_mod_cast hY.trans hb
  -- the ranges: `1 ≤ mn ≤ M`, and `mn ≤ 4X`
  have hrange : ∀ m ∈ d.mRange, ∀ n ∈ d.nRange,
      1 ≤ m * n ∧ m * n ≤ ⌊2 * d.Hm⌋₊ * ⌊2 * d.Hn⌋₊ ∧ ((m * n : ℕ) : ℝ) ≤ 4 * d.X := by
    intro m hm n hn
    rw [Data.mRange, mem_Icc] at hm
    rw [Data.nRange, mem_Icc] at hn
    have hm1 : 1 ≤ m := (Nat.one_le_ceil_iff.2 (by linarith)).trans hm.1
    have hn1 : 1 ≤ n := (Nat.one_le_ceil_iff.2 (by linarith)).trans hn.1
    have hm2 : (m : ℝ) ≤ 2 * d.Hm := (Nat.le_floor_iff (by linarith)).1 hm.2
    have hn2 : (n : ℝ) ≤ 2 * d.Hn := (Nat.le_floor_iff (by linarith)).1 hn.2
    refine ⟨Nat.mul_le_mul hm1 hn1, Nat.mul_le_mul hm.2 hn.2, ?_⟩
    push_cast
    unfold Data.X
    nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n]
  -- a raw solution has `Y h < a h < mn ≤ 4X`
  have hZ : ∀ m ∈ d.mRange, ∀ n ∈ d.nRange, ∀ h, 1 ≤ h → m * n - 1 = a * h →
      h ≤ ⌊4 * d.X / Y⌋₊ := by
    intro m hm n hn h h1 hmn
    refine Nat.le_floor ?_
    have hah : ((a * h : ℕ) : ℝ) ≤ ((m * n : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have := (hrange m hm n hn).2.2
    push_cast at hah this
    have hYh : Y * h ≤ a * h := mul_le_mul_of_nonneg_right ha.le (Nat.cast_nonneg _)
    rw [le_div_iff₀ hY]
    linarith
  -- the coefficients have size at most `L^{4C}`
  have hcoef : ∀ m n r s : ℕ, ‖d.α m * star (d.α r) * d.β n * star (d.β s)‖ ≤ L ^ (4 * C) := by
    intro m n r s
    rw [norm_mul, norm_mul, norm_mul, norm_star, norm_star,
      show 4 * C = C + C + C + C by ring, Real.rpow_add hL, Real.rpow_add hL, Real.rpow_add hL]
    gcongr
    exacts [hα m, hα r, hβ n, hβ s]
  -- termwise: the raw indicator plus the kernel bound
  have hterm : ∀ m n r s : ℕ,
      ‖d.α m * star (d.α r) * d.β n * star (d.β s) *
        ((if ∃ h, 1 ≤ h ∧ m * n - 1 = a * h ∧ r * s - 1 = b * h then 1 else 0) -
          majorWeight A₀ x Y (b * m * n - a * r * s) a b)‖ ≤
      L ^ (4 * C) * ((if ∃ h, 1 ≤ h ∧ m * n - 1 = a * h ∧ r * s - 1 = b * h then 1 else 0) +
        w * (if |(b : ℝ) * ((m * n : ℕ) : ℝ) - a * ((r * s : ℕ) : ℝ)| ≤ 5 * Y then 1 else 0)) := by
    intro m n r s
    rw [norm_mul]
    refine mul_le_mul (hcoef m n r s) ((norm_sub_le _ _).trans (add_le_add ?_ ?_))
      (norm_nonneg _) (by positivity)
    · split_ifs <;> simp
    · refine (norm_majorWeight_le A₀ hL hY _ _ _).trans_eq ?_
      push_cast
      simp only [w, L]
      ring_nf
  calc ‖pairError A₀ x d Y a b‖
      ≤ ∑ m ∈ d.mRange, ∑ n ∈ d.nRange, ∑ r ∈ d.mRange, ∑ s ∈ d.nRange,
          L ^ (4 * C) * ((if ∃ h, 1 ≤ h ∧ m * n - 1 = a * h ∧ r * s - 1 = b * h then 1 else 0) +
            w * (if |(b : ℝ) * ((m * n : ℕ) : ℝ) - a * ((r * s : ℕ) : ℝ)| ≤ 5 * Y then 1
              else 0)) := by
        unfold pairError
        refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
        refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
        refine (norm_sum_le _ _).trans (sum_le_sum fun r _ => ?_)
        exact (norm_sum_le _ _).trans (sum_le_sum fun s _ => hterm m n r s)
    _ = L ^ (4 * C) * (∑ m ∈ d.mRange, ∑ n ∈ d.nRange, ∑ r ∈ d.mRange, ∑ s ∈ d.nRange,
          (if ∃ h, 1 ≤ h ∧ m * n - 1 = a * h ∧ r * s - 1 = b * h then (1 : ℝ) else 0) +
          w * ∑ m ∈ d.mRange, ∑ n ∈ d.nRange, ∑ r ∈ d.mRange, ∑ s ∈ d.nRange,
            (if |(b : ℝ) * ((m * n : ℕ) : ℝ) - a * ((r * s : ℕ) : ℝ)| ≤ 5 * Y then (1 : ℝ)
              else 0)) := by
        simp only [mul_sum, ← sum_add_distrib, mul_add]
    _ ≤ _ := by
        gcongr
        · exact sum_ite_exists_le _ _ ha0 hb0 hZ
        · exact sum_ite_abs_le _ _ (fun m hm n hn => ⟨(hrange m hm n hn).1,
            (hrange m hm n hn).2.1⟩) hY ha hb

/-- The pair error at `a, b ∈ (Y, 4Y)` in closed form:
`|E(a, b)| ≤ (X/Y) L^{4C} L³ (160 + 1408 L^{3A₀})`, once `X ≥ 1`, `1 + log(17X) ≤ 2L` and
`(17X)^{3/4} ≤ X/Y` (so `Y ≤ X^{1/4}`, as in PD (3.9)). -/
theorem norm_pairError_le_of (A₀ : ℝ) {C x : ℝ} {d : Data K} (hL : 1 ≤ Real.log x)
    (hα : ∀ m, ‖d.α m‖ ≤ Real.log x ^ C) (hβ : ∀ n, ‖d.β n‖ ≤ Real.log x ^ C)
    (hHm : 1 ≤ d.Hm) (hHn : 1 ≤ d.Hn) (hX : 1 ≤ d.X)
    (hlog : 1 + Real.log (17 * d.X) ≤ 2 * Real.log x) {Y : ℝ} (hY : 0 < Y)
    (h34 : (17 * d.X) ^ (3 / 4 : ℝ) ≤ d.X / Y) {a b : ℕ} (ha : Y < a) (hb : Y < b)
    (ha4 : (a : ℝ) < 4 * Y) (hb4 : (b : ℝ) < 4 * Y) :
    ‖pairError A₀ x d Y a b‖ ≤ d.X / Y * Real.log x ^ (4 * C) * Real.log x ^ 3 *
      (160 + 1408 * Real.log x ^ (3 * A₀)) := by
  set L := Real.log x
  set Z := ⌊4 * d.X / Y⌋₊
  set M := ⌊2 * d.Hm⌋₊ * ⌊2 * d.Hn⌋₊
  have hL0 : 0 < L := by linarith
  have h17 : 1 ≤ 17 * d.X := by linarith
  have hXY : 0 ≤ d.X / Y := div_nonneg (by linarith) hY.le
  -- a logarithm below `log(17X)` costs at most `(2L)³`
  have hcube : ∀ N : ℕ, (N : ℝ) ≤ 17 * d.X → (1 + Real.log N) ^ 3 ≤ (2 * L) ^ 3 := by
    intro N hN
    have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    refine pow_le_pow_left₀ (by linarith) ?_ 3
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]
      linarith [Real.log_nonneg h17]
    · linarith [Real.log_le_log (by exact_mod_cast h0) hN]
  -- the divisor moment up to `M ≤ 4X`
  have hM : (M : ℝ) ≤ 4 * d.X := by
    have h₁ : (⌊2 * d.Hm⌋₊ : ℝ) ≤ 2 * d.Hm := Nat.floor_le (by linarith)
    have h₂ : (⌊2 * d.Hn⌋₊ : ℝ) ≤ 2 * d.Hn := Nat.floor_le (by linarith)
    simp only [M, Nat.cast_mul]
    unfold Data.X
    nlinarith [Nat.cast_nonneg (α := ℝ) ⌊2 * d.Hm⌋₊, Nat.cast_nonneg (α := ℝ) ⌊2 * d.Hn⌋₊]
  have hS : ∑ k ∈ Icc 1 M, (k.divisors.card : ℝ) ^ 2 ≤ 32 * d.X * L ^ 3 := by
    refine (sum_card_divisors_sq_le M).trans ?_
    calc (M : ℝ) * (1 + Real.log M) ^ 3 ≤ (4 * d.X) * (2 * L) ^ 3 :=
          mul_le_mul hM (hcube M (by linarith)) (by positivity) (by linarith)
      _ = 32 * d.X * L ^ 3 := by ring
  -- the moment along `1 + l h`, `h ≤ Z`, for `l < 4Y`
  have hZ : (Z : ℝ) ≤ 4 * d.X / Y := Nat.floor_le (by positivity)
  have hprog : ∀ l : ℕ, (l : ℝ) < 4 * Y →
      ∑ h ∈ Icc 1 Z, (((1 + l * h).divisors.card : ℕ) : ℝ) ^ 2 ≤ 160 * (d.X / Y) * L ^ 3 := by
    intro l hl
    have hlZ : ((1 + l * Z : ℕ) : ℝ) ≤ 17 * d.X := by
      push_cast
      have : (l : ℝ) * Z ≤ 4 * Y * (4 * d.X / Y) :=
        mul_le_mul hl.le hZ (Nat.cast_nonneg _) (by linarith)
      rw [show 4 * Y * (4 * d.X / Y) = 16 * d.X by field_simp; ring] at this
      linarith
    refine (sum_card_divisors_one_add_mul_sq_le l Z).trans ?_
    have h₁ : ((1 + l * Z : ℕ) : ℝ) ^ (3 / 4 : ℝ) ≤ d.X / Y :=
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hlZ (by norm_num)).trans h34
    calc 4 * (Z + ((1 + l * Z : ℕ) : ℝ) ^ (3 / 4 : ℝ)) * (1 + Real.log ((1 + l * Z : ℕ) : ℝ)) ^ 3
        ≤ 4 * (4 * d.X / Y + d.X / Y) * (2 * L) ^ 3 :=
          mul_le_mul (by gcongr) (hcube _ hlZ)
            (pow_nonneg (by linarith [Real.log_natCast_nonneg (1 + l * Z)]) 3) (by positivity)
      _ = 160 * (d.X / Y) * L ^ 3 := by ring
  have hR : ∑ h ∈ Icc 1 Z, ((1 + a * h).divisors.card : ℝ) * (1 + b * h).divisors.card ≤
      160 * (d.X / Y) * L ^ 3 := by
    calc ∑ h ∈ Icc 1 Z, ((1 + a * h).divisors.card : ℝ) * (1 + b * h).divisors.card
        ≤ ∑ h ∈ Icc 1 Z, ((((1 + a * h).divisors.card : ℕ) : ℝ) ^ 2 +
            (((1 + b * h).divisors.card : ℕ) : ℝ) ^ 2) / 2 :=
          sum_le_sum fun h _ => by
            nlinarith [sq_nonneg (((1 + a * h).divisors.card : ℝ) - (1 + b * h).divisors.card)]
      _ = (∑ h ∈ Icc 1 Z, (((1 + a * h).divisors.card : ℕ) : ℝ) ^ 2 +
            ∑ h ∈ Icc 1 Z, (((1 + b * h).divisors.card : ℕ) : ℝ) ^ 2) / 2 := by
          rw [← sum_add_distrib, sum_div]
      _ ≤ (160 * (d.X / Y) * L ^ 3 + 160 * (d.X / Y) * L ^ 3) / 2 := by
          gcongr
          exacts [hprog a ha4, hprog b hb4]
      _ = 160 * (d.X / Y) * L ^ 3 := by ring
  refine (norm_pairError_le A₀ hL0 hα hβ hHm hHn hY ha hb).trans ?_
  have hLA : 0 ≤ L ^ (3 * A₀) := Real.rpow_nonneg hL0.le _
  calc L ^ (4 * C) * (∑ h ∈ Icc 1 Z, ((1 + a * h).divisors.card : ℝ) *
          (1 + b * h).divisors.card +
        4 * L ^ (3 * A₀) / Y * (11 * ∑ k ∈ Icc 1 M, (k.divisors.card : ℝ) ^ 2))
      ≤ L ^ (4 * C) * (160 * (d.X / Y) * L ^ 3 +
          4 * L ^ (3 * A₀) / Y * (11 * (32 * d.X * L ^ 3))) := by
        gcongr
    _ = d.X / Y * L ^ (4 * C) * L ^ 3 * (160 + 1408 * L ^ (3 * A₀)) := by
        field_simp
        ring

end Erdos408.OneSided
