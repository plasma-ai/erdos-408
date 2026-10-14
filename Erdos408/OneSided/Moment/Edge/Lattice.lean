import Erdos408.OneSided.Moment.Edge.Gram
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# The lattice shape

PD `mem:lattice-shape` (M5 of `blueprint/one_sided_type_ii.md` §5.5), in integer coordinates.
The relevant vectors of a lattice block have coordinates `(h, l)` with `|l| ≤ cY` and
`|h + l α| ≤ c`, where `α = D τ(w_z)/τ(z)` at a good source. Test (i) says
`‖l α‖ > Y^{-0.7}` for `1 ≤ l ≤ Y^{0.2}`.

The image of `ℤ²` under `(h, l) ↦ (h + l α, l / Y)` has covolume `1/Y`. Its shortest vector
has length `λ ∈ [Y^{-0.8}, √5 Y^{-1/2}]`: the lower bound is test (i), the upper bound is
Dirichlet's approximation with denominators at most `⌈√Y⌉`. Completing a shortest vector to a
reduced basis of determinant one puts all relevant vectors into the box `|m₁| ≤ A'`,
`|m₂| ≤ B'` with `A' ≍ c/λ`, `B' ≍ c Y λ`.

* `exists_lattice_box`: there are integers `h₁, l₁, h₂, l₂` with `h₁ l₂ - l₁ h₂ = 1` and box
  sides `A', B'` with `A' B' ≤ 6 c² Y` and `A', B' ≤ Y^{0.9}` such that every relevant
  `(h, l)` has new coordinates `m₁ = h l₂ - l h₂`, `m₂ = h₁ l - l₁ h` in the box. Since the
  change of basis has determinant one, `h l' - l h' = m₁ m₂' - m₂ m₁'`.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real

/-- The squared length `(h + l α)² + (l/Y)²` of the image of `(h, l)`. -/
private def latQ (α Y : ℝ) (h l : ℤ) : ℝ := (h + l * α) ^ 2 + (l / Y) ^ 2

/-- A nonzero integer vector has positive image length. -/
private theorem latQ_pos {α Y : ℝ} (hY : 0 < Y) {h l : ℤ} (hne : (h, l) ≠ (0, 0)) :
    0 < latQ α Y h l := by
  unfold latQ
  by_cases hl : l = 0
  · have hh : h ≠ 0 := fun hh => hne (by rw [hh, hl])
    subst hl
    have : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    simp only [Int.cast_zero, zero_mul, add_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    positivity
  · have : (l : ℝ) / Y ≠ 0 := div_ne_zero (by exact_mod_cast hl) hY.ne'
    positivity

/-- A shortest nonzero vector exists. -/
private theorem exists_latQ_min (α : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ∃ v : ℤ × ℤ, v ≠ (0, 0) ∧ ∀ w : ℤ × ℤ, w ≠ (0, 0) → latQ α Y v.1 v.2 ≤ latQ α Y w.1 w.2 := by
  set H : ℕ := ⌈1 + Y * |α|⌉₊
  set Lb : ℕ := ⌈Y⌉₊
  set S := ((Icc (-(H : ℤ)) H) ×ˢ (Icc (-(Lb : ℤ)) Lb)).erase (0, 0)
  have h10 : ((1 : ℤ), (0 : ℤ)) ∈ S := by
    refine mem_erase.2 ⟨by decide, mem_product.2 ⟨mem_Icc.2 ⟨by omega, ?_⟩, mem_Icc.2 ⟨by omega,
      by omega⟩⟩⟩
    have : (1 : ℕ) ≤ H := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
    show (1 : ℤ) ≤ H
    exact_mod_cast this
  obtain ⟨v, hv, hmin⟩ := S.exists_min_image (fun w => latQ α Y w.1 w.2) ⟨_, h10⟩
  refine ⟨v, (mem_erase.1 hv).1, fun w hw => ?_⟩
  by_cases hwS : w ∈ S
  · exact hmin w hwS
  · -- outside the search box the length exceeds `latQ(1, 0) = 1`
    have h1 : latQ α Y 1 0 = 1 := by simp [latQ]
    refine (hmin _ h10).trans (h1.symm ▸ ?_)
    by_contra hlt
    push Not at hlt
    apply hwS
    refine mem_erase.2 ⟨hw, mem_product.2 ⟨?_, ?_⟩⟩
    · have hx : (w.1 + w.2 * α) ^ 2 ≤ 1 := by
        have := sq_nonneg ((w.2 : ℝ) / Y)
        unfold latQ at hlt
        linarith
      have hy : ((w.2 : ℝ) / Y) ^ 2 ≤ 1 := by
        have := sq_nonneg ((w.1 : ℝ) + w.2 * α)
        unfold latQ at hlt
        linarith
      have hx' := sq_le_one_iff_abs_le_one _ |>.1 hx
      have hy' : |(w.2 : ℝ)| ≤ Y := by
        have := sq_le_one_iff_abs_le_one _ |>.1 hy
        rw [abs_le] at this ⊢
        constructor
        · have := (le_div_iff₀ hY).1 this.1
          linarith
        · exact (div_le_iff₀ hY).1 this.2 |>.trans (by linarith)
      have hw1 : |(w.1 : ℝ)| ≤ 1 + Y * |α| := by
        calc |(w.1 : ℝ)| = |(w.1 + w.2 * α) - w.2 * α| := by ring_nf
          _ ≤ |(w.1 : ℝ) + w.2 * α| + |(w.2 : ℝ) * α| := abs_sub _ _
          _ ≤ 1 + Y * |α| := by
              rw [abs_mul]
              have := mul_le_mul_of_nonneg_right hy' (abs_nonneg α)
              linarith
      have hH := Nat.le_ceil (1 + Y * |α|)
      have : |(w.1 : ℝ)| ≤ H := hw1.trans hH
      rw [abs_le] at this
      rw [mem_Icc]
      constructor <;> [exact_mod_cast (by linarith : -(H : ℝ) ≤ w.1);
        exact_mod_cast (by linarith : (w.1 : ℝ) ≤ H)]
    · have hy : ((w.2 : ℝ) / Y) ^ 2 ≤ 1 := by
        have := sq_nonneg ((w.1 : ℝ) + w.2 * α)
        unfold latQ at hlt
        linarith
      have hy' : |(w.2 : ℝ)| ≤ Y := by
        have := sq_le_one_iff_abs_le_one _ |>.1 hy
        rw [abs_le] at this ⊢
        constructor
        · have := (le_div_iff₀ hY).1 this.1
          linarith
        · exact (div_le_iff₀ hY).1 this.2 |>.trans (by linarith)
      have : |(w.2 : ℝ)| ≤ Lb := hy'.trans (Nat.le_ceil Y)
      rw [abs_le] at this
      rw [mem_Icc]
      constructor <;> [exact_mod_cast (by linarith : -(Lb : ℝ) ≤ w.2);
        exact_mod_cast (by linarith : (w.2 : ℝ) ≤ Lb)]

/-- An integer of absolute value at most `r` is at most `⌊r⌋₊` in absolute value. -/
private theorem int_abs_le_floor {m : ℤ} {r : ℝ} (h : |(m : ℝ)| ≤ r) : |m| ≤ (⌊r⌋₊ : ℤ) := by
  have h1 : ((m.natAbs : ℕ) : ℝ) ≤ r := by rwa [Nat.cast_natAbs, Int.cast_abs]
  have h2 : m.natAbs ≤ ⌊r⌋₊ := Nat.le_floor h1
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h2

/-- `(ad - bc)² ≤ (a² + b²)(c² + d²)`. -/
private theorem sq_det_le (a b c d : ℝ) : (a * d - b * c) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a * c + b * d)]

set_option maxHeartbeats 1000000 in
/-- **The lattice shape** (PD `mem:lattice-shape`, M5). Suppose `1 ≤ Y`, `8c ≤ Y^{0.1}` and
`‖l α‖ > Y^{-0.7}` for `1 ≤ l ≤ Y^{0.2}` (test (i)). Then there are integers
`h₁ l₂ - l₁ h₂ = 1` and box sides `A' B' ≤ 6c²Y`, `A', B' ≤ Y^{0.9}` such that every integer
`(h, l)` with `|l| ≤ cY` and `|h + l α| ≤ c` has `|h l₂ - l h₂| ≤ A'` and `|h₁ l - l₁ h| ≤ B'`. -/
theorem exists_lattice_box {α Y c : ℝ} (hY : 1 ≤ Y) (hc : 0 < c)
    (hYc : 8 * c ≤ Y ^ (1 / 10 : ℝ))
    (hgood : ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (1 / 5 : ℝ) →
      Y ^ (-(7 / 10 : ℝ)) < circleDist (l * α)) :
    ∃ h₁ l₁ h₂ l₂ : ℤ, h₁ * l₂ - l₁ * h₂ = 1 ∧ ∃ A' B' : ℕ,
      (A' : ℝ) * B' ≤ 6 * c ^ 2 * Y ∧ (A' : ℝ) ≤ Y ^ (9 / 10 : ℝ) ∧ (B' : ℝ) ≤ Y ^ (9 / 10 : ℝ) ∧
      ∀ h l : ℤ, |(l : ℝ)| ≤ c * Y → |h + l * α| ≤ c →
        |h * l₂ - l * h₂| ≤ A' ∧ |h₁ * l - l₁ * h| ≤ B' := by
  have hY0 : 0 < Y := by linarith
  -- powers of `t = Y^{1/10}`
  set t := Y ^ (1 / 10 : ℝ) with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hY (by norm_num)
  have hpow : ∀ n : ℕ, Y ^ ((n : ℝ) / 10) = t ^ n := by
    intro n
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
    ring_nf
  have hYt : Y = t ^ 10 := by
    rw [← hpow 10]
    norm_num
  have ht2 : Y ^ (1 / 5 : ℝ) = t ^ 2 := by rw [← hpow 2]; norm_num
  have ht9 : Y ^ (9 / 10 : ℝ) = t ^ 9 := by rw [← hpow 9]; norm_num
  have ht7 : Y ^ (-(7 / 10 : ℝ)) = (t ^ 7)⁻¹ := by
    rw [Real.rpow_neg hY0.le, ← hpow 7]
    norm_num
  rw [ht2, ht7] at hgood
  rw [ht9]
  -- a shortest vector `v₁ = (h₁, l₁)`, of squared length `Λ`
  obtain ⟨v, hv0, hmin⟩ := exists_latQ_min α hY0
  set h₁ := v.1
  set l₁ := v.2
  set Λ := latQ α Y h₁ l₁ with hΛ
  have hΛ0 : 0 < Λ := latQ_pos hY0 hv0
  -- `Λ ≤ 5/Y`, by Dirichlet's approximation
  have hΛup : Y * Λ ≤ 5 := by
    set n := ⌈Real.sqrt Y⌉₊
    have hn : 0 < n := Nat.ceil_pos.2 (Real.sqrt_pos.2 hY0)
    obtain ⟨j, k, hk0, hkn, hjk⟩ := Real.exists_int_int_abs_mul_sub_le α hn
    have hne : ((-j : ℤ), k) ≠ (0, 0) := fun h => by
      simp only [Prod.mk.injEq] at h
      omega
    have hle := hmin _ hne
    have hsY : Real.sqrt Y ≤ n := Nat.le_ceil _
    have hn1 : (n : ℝ) ≤ Real.sqrt Y + 1 := (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
    have hsq : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY0.le
    have hs1 : 1 ≤ Real.sqrt Y := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hY
    have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
    -- `(kα - j)² ≤ 1/Y` and `(k/Y)² ≤ 4/Y`
    have h1 : ((-j : ℤ) + k * α) ^ 2 ≤ 1 / Y := by
      have e : ((-j : ℤ) : ℝ) + k * α = k * α - j := by push_cast; ring
      rw [e, ← sq_abs]
      have hb : 1 / ((n : ℝ) + 1) ≤ 1 / Real.sqrt Y :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      calc |(k : ℝ) * α - j| ^ 2 ≤ (1 / Real.sqrt Y) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hjk.trans hb) 2
        _ = 1 / Y := by rw [div_pow, hsq, one_pow]
    have h2 : ((k : ℝ) / Y) ^ 2 ≤ 4 / Y := by
      rw [div_pow, div_le_div_iff₀ (by positivity) hY0]
      have : (k : ℝ) ^ 2 ≤ 4 * Y := by nlinarith
      nlinarith
    have : Λ ≤ 5 / Y := by
      refine hle.trans ?_
      unfold latQ
      have : (5 : ℝ) / Y = 1 / Y + 4 / Y := by ring
      rw [this]
      exact add_le_add h1 h2
    rwa [le_div_iff₀ hY0, mul_comm] at this
  -- `Λ ≥ Y^{-1.6} = t^{-16}`, by test (i)
  have hΛlow : 1 ≤ t ^ 16 * Λ := by
    by_contra hlt
    push Not at hlt
    set x₁ := (h₁ : ℝ) + l₁ * α
    have hΛt : Λ < (t ^ 8)⁻¹ ^ 2 := by
      have e : (t ^ 8)⁻¹ ^ 2 = 1 / t ^ 16 := by rw [inv_pow, ← pow_mul, one_div]
      rw [e, lt_div_iff₀ (by positivity)]
      linarith [mul_comm Λ (t ^ 16)]
    have hx : x₁ ^ 2 < (t ^ 8)⁻¹ ^ 2 := by
      refine lt_of_le_of_lt ?_ hΛt
      have := sq_nonneg ((l₁ : ℝ) / Y)
      simp only [hΛ, latQ, x₁]
      linarith
    have hy : ((l₁ : ℝ) / Y) ^ 2 < (t ^ 8)⁻¹ ^ 2 := by
      refine lt_of_le_of_lt ?_ hΛt
      have := sq_nonneg x₁
      simp only [hΛ, latQ, x₁] at this ⊢
      linarith
    have hx' : |x₁| < (t ^ 8)⁻¹ := abs_lt_of_sq_lt_sq hx (by positivity)
    have hy' : |(l₁ : ℝ) / Y| < (t ^ 8)⁻¹ := abs_lt_of_sq_lt_sq hy (by positivity)
    have hl₁ : |(l₁ : ℝ)| < t ^ 2 := by
      rw [abs_div, abs_of_pos hY0, div_lt_iff₀ hY0, hYt] at hy'
      have : (t ^ 8)⁻¹ * t ^ 10 = t ^ 2 := by
        field_simp
      linarith
    have ht8 : (t ^ 8)⁻¹ ≤ (t ^ 7)⁻¹ := inv_anti₀ (by positivity)
      (pow_le_pow_right₀ ht1 (by norm_num))
    by_cases hl0 : l₁ = 0
    · -- then `|h₁| < 1`, so `v₁ = 0`
      have hh : |(h₁ : ℝ)| < 1 := by
        have : x₁ = h₁ := by simp [x₁, hl0]
        rw [← this]
        exact hx'.trans_le (inv_le_one_of_one_le₀ (one_le_pow₀ ht1))
      have : h₁ = 0 := by
        have : |h₁| < 1 := by exact_mod_cast hh
        exact Int.abs_lt_one_iff.1 this
      exact hv0 (Prod.ext this hl0)
    · -- `l = |l₁|` violates test (i)
      have hl : 1 ≤ l₁.natAbs := Int.natAbs_pos.2 hl0
      have hlr : ((l₁.natAbs : ℕ) : ℝ) = |(l₁ : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      have hg := hgood l₁.natAbs hl (by rw [hlr]; exact hl₁.le)
      have hcd : circleDist ((l₁.natAbs : ℝ) * α) ≤ |x₁| := by
        rcases le_or_gt 0 l₁ with hpos | hneg
        · have : ((l₁.natAbs : ℕ) : ℝ) = l₁ := by
            rw [hlr, abs_of_nonneg (by exact_mod_cast hpos)]
          rw [this]
          calc circleDist (l₁ * α) ≤ |l₁ * α - ((-h₁ : ℤ) : ℝ)| := circleDist_le_abs_sub _ _
            _ = |x₁| := by congr 1; push_cast; simp only [x₁]; ring
        · have : ((l₁.natAbs : ℕ) : ℝ) = -l₁ := by
            rw [hlr, abs_of_neg (by exact_mod_cast hneg)]
          rw [this]
          calc circleDist (-l₁ * α) ≤ |-l₁ * α - ((h₁ : ℤ) : ℝ)| := circleDist_le_abs_sub _ _
            _ = |x₁| := by rw [← abs_neg]; congr 1; simp only [x₁]; ring
      linarith
  -- `v₁` is primitive
  have hprim : Int.gcd h₁ l₁ = 1 := by
    set g := Int.gcd h₁ l₁
    obtain ⟨a, ha⟩ := Int.gcd_dvd_left (a := h₁) (b := l₁)
    obtain ⟨b, hb⟩ := Int.gcd_dvd_right (a := h₁) (b := l₁)
    have hg0 : g ≠ 0 := fun h => hv0 (by
      rw [Int.gcd_eq_zero_iff] at h
      exact Prod.ext h.1 h.2)
    by_contra hg1
    have hg2 : 2 ≤ g := by omega
    have hab : (a, b) ≠ (0, 0) := fun h => by
      simp only [Prod.mk.injEq] at h
      exact hv0 (Prod.ext (by change h₁ = 0; rw [ha, h.1, mul_zero])
        (by change l₁ = 0; rw [hb, h.2, mul_zero]))
    have hle := hmin _ hab
    have hscale : Λ = (g : ℝ) ^ 2 * latQ α Y a b := by
      simp only [hΛ, latQ]
      rw [show (h₁ : ℝ) = g * a by exact_mod_cast ha, show (l₁ : ℝ) = g * b by exact_mod_cast hb]
      ring
    have hpos := latQ_pos hY0 hab (α := α)
    have : (4 : ℝ) ≤ (g : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ g := by exact_mod_cast hg2
      nlinarith
    simp only at hle
    nlinarith
  -- complete `v₁` to a basis of determinant one
  set h₂' := -Int.gcdB h₁ l₁
  set l₂' := Int.gcdA h₁ l₁
  have hdet' : h₁ * l₂' - l₁ * h₂' = 1 := by
    have := Int.gcd_eq_gcd_ab h₁ l₁
    rw [hprim] at this
    simp only [h₂', l₂']
    push_cast at this
    linarith
  set x₁ := (h₁ : ℝ) + l₁ * α with hx₁
  set y₁ := (l₁ : ℝ) / Y with hy₁
  have hΛxy : Λ = x₁ ^ 2 + y₁ ^ 2 := by simp only [hΛ, latQ, x₁, y₁]
  -- reduce the second vector against the first
  set ip := x₁ * ((h₂' : ℝ) + l₂' * α) + y₁ * ((l₂' : ℝ) / Y) with hip
  set k := round (ip / Λ)
  set h₂ := h₂' - k * h₁
  set l₂ := l₂' - k * l₁
  have hdet : h₁ * l₂ - l₁ * h₂ = 1 := by
    simp only [h₂, l₂]
    linear_combination hdet'
  set x₂ := (h₂ : ℝ) + l₂ * α with hx₂
  set y₂ := (l₂ : ℝ) / Y with hy₂
  have hip2 : |x₁ * x₂ + y₁ * y₂| ≤ Λ / 2 := by
    have e : x₁ * x₂ + y₁ * y₂ = Λ * (ip / Λ - k) := by
      rw [mul_sub, mul_div_cancel₀ _ hΛ0.ne', hip, hΛxy]
      simp only [x₂, y₂, h₂, l₂]
      push_cast
      ring
    rw [e, abs_mul, abs_of_pos hΛ0]
    have := abs_sub_round (ip / Λ)
    nlinarith
  have hdetR : x₁ * y₂ - y₁ * x₂ = 1 / Y := by
    have hd : ((h₁ * l₂ - l₁ * h₂ : ℤ) : ℝ) = 1 := by exact_mod_cast hdet
    push_cast at hd
    simp only [x₁, y₁, x₂, y₂]
    field_simp
    linear_combination hd
  -- `Λ |v₂|² ≤ Λ²/4 + 1/Y²` (Lagrange's identity)
  have hv2 : Λ * (x₂ ^ 2 + y₂ ^ 2) ≤ Λ ^ 2 / 4 + 1 / Y ^ 2 := by
    have hL : Λ * (x₂ ^ 2 + y₂ ^ 2) = (x₁ * x₂ + y₁ * y₂) ^ 2 + (x₁ * y₂ - y₁ * x₂) ^ 2 := by
      rw [hΛxy]
      ring
    rw [hL, hdetR, div_pow, one_pow]
    have := sq_abs (x₁ * x₂ + y₁ * y₂)
    have h2 : |x₁ * x₂ + y₁ * y₂| ^ 2 ≤ (Λ / 2) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hip2 2
    nlinarith
  -- the box sides
  set lam := Real.sqrt Λ with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.2 hΛ0
  have hlam2 : lam ^ 2 = Λ := Real.sq_sqrt hΛ0.le
  refine ⟨h₁, l₁, h₂, l₂, hdet, ⌊4 * c / lam⌋₊, ⌊3 / 2 * c * Y * lam⌋₊, ?_, ?_, ?_, ?_⟩
  · -- `A' B' ≤ (4c/λ)(3cYλ/2) = 6c²Y`
    calc (⌊4 * c / lam⌋₊ : ℝ) * ⌊3 / 2 * c * Y * lam⌋₊ ≤ (4 * c / lam) * (3 / 2 * c * Y * lam) :=
          mul_le_mul (Nat.floor_le (by positivity)) (Nat.floor_le (by positivity))
            (Nat.cast_nonneg _) (by positivity)
      _ = 6 * c ^ 2 * Y := by field_simp; ring
  · -- `(4c/λ)² = 16c²/Λ ≤ 16 c² t^16 ≤ t^18`
    have hA : (4 * c / lam) ^ 2 ≤ (t ^ 9) ^ 2 := by
      rw [div_pow, hlam2, div_le_iff₀ hΛ0]
      have h1 : (4 * c) ^ 2 ≤ t ^ 2 / 4 := by nlinarith
      have h2 : t ^ 2 * 1 ≤ t ^ 2 * (t ^ 16 * Λ) :=
        mul_le_mul_of_nonneg_left hΛlow (by positivity)
      have e : (t ^ 9) ^ 2 * Λ = t ^ 2 * (t ^ 16 * Λ) := by ring
      rw [e]
      have : 0 ≤ t ^ 2 := by positivity
      linarith
    exact (Nat.floor_le (by positivity)).trans
      ((pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hA)
  · -- `(3cYλ/2)² = 9c²Y²Λ/4 ≤ 45 c² Y/4 ≤ t^18`
    have hB : (3 / 2 * c * Y * lam) ^ 2 ≤ (t ^ 9) ^ 2 := by
      have e : (3 / 2 * c * Y * lam) ^ 2 = 9 / 4 * c ^ 2 * Y * (Y * Λ) := by
        rw [← hlam2]
        ring
      rw [e]
      have h1 : c ^ 2 ≤ t ^ 2 / 64 := by nlinarith
      have h2 : 9 / 4 * c ^ 2 * Y * (Y * Λ) ≤ 9 / 4 * c ^ 2 * Y * 5 :=
        mul_le_mul_of_nonneg_left hΛup (by positivity)
      have h3 : 9 / 4 * c ^ 2 * Y * 5 ≤ 9 / 4 * (t ^ 2 / 64) * Y * 5 := by
        have : 0 ≤ Y := hY0.le
        nlinarith
      have h4 : t ^ 12 ≤ t ^ 18 := pow_le_pow_right₀ ht1 (by norm_num)
      have e2 : 9 / 4 * (t ^ 2 / 64) * Y * 5 = 45 / 256 * t ^ 12 := by rw [hYt]; ring
      have e3 : (t ^ 9) ^ 2 = t ^ 18 := by ring
      have h5 : 0 ≤ t ^ 12 := by positivity
      rw [e3]
      linarith
    exact (Nat.floor_le (by positivity)).trans
      ((pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hB)
  · -- the relevant vectors lie in the box
    intro h l hl hhl
    set X := (h : ℝ) + l * α
    set Yc := (l : ℝ) / Y
    have hP : X ^ 2 + Yc ^ 2 ≤ 2 * c ^ 2 := by
      have h1 : X ^ 2 ≤ c ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hhl 2
      have h2 : Yc ^ 2 ≤ c ^ 2 := by
        rw [← sq_abs, show |Yc| = |(l : ℝ)| / Y by rw [abs_div, abs_of_pos hY0]]
        exact pow_le_pow_left₀ (by positivity) ((div_le_iff₀ hY0).2 (by linarith)) 2
      linarith
    have hm₁ : ((h * l₂ - l * h₂ : ℤ) : ℝ) = Y * (X * y₂ - Yc * x₂) := by
      push_cast
      simp only [X, Yc, x₂, y₂]
      field_simp
      ring
    have hm₂ : ((h₁ * l - l₁ * h : ℤ) : ℝ) = Y * (x₁ * Yc - y₁ * X) := by
      push_cast
      simp only [X, Yc, x₁, y₁]
      field_simp
      ring
    constructor
    · refine int_abs_le_floor ?_
      rw [hm₁, ← sq_le_sq₀ (abs_nonneg _) (by positivity), sq_abs, div_pow, hlam2,
        le_div_iff₀ hΛ0]
      have hcs := sq_det_le X Yc x₂ y₂
      have hxy : 0 ≤ x₂ ^ 2 + y₂ ^ 2 := by positivity
      calc (Y * (X * y₂ - Yc * x₂)) ^ 2 * Λ = Y ^ 2 * (X * y₂ - Yc * x₂) ^ 2 * Λ := by ring
        _ ≤ Y ^ 2 * ((X ^ 2 + Yc ^ 2) * (x₂ ^ 2 + y₂ ^ 2)) * Λ := by gcongr
        _ ≤ Y ^ 2 * (2 * c ^ 2 * (x₂ ^ 2 + y₂ ^ 2)) * Λ := by gcongr
        _ = 2 * c ^ 2 * Y ^ 2 * (Λ * (x₂ ^ 2 + y₂ ^ 2)) := by ring
        _ ≤ 2 * c ^ 2 * Y ^ 2 * (Λ ^ 2 / 4 + 1 / Y ^ 2) := by gcongr
        _ = 2 * c ^ 2 * ((Y * Λ) ^ 2 / 4 + 1) := by field_simp
        _ ≤ 2 * c ^ 2 * (5 ^ 2 / 4 + 1) := by gcongr
        _ ≤ (4 * c) ^ 2 := by nlinarith
    · refine int_abs_le_floor ?_
      rw [hm₂, ← sq_le_sq₀ (abs_nonneg _) (by positivity), sq_abs]
      have hcs := sq_det_le x₁ y₁ X Yc
      calc (Y * (x₁ * Yc - y₁ * X)) ^ 2 = Y ^ 2 * (x₁ * Yc - y₁ * X) ^ 2 := by ring
        _ ≤ Y ^ 2 * ((x₁ ^ 2 + y₁ ^ 2) * (X ^ 2 + Yc ^ 2)) := by gcongr
        _ ≤ Y ^ 2 * (Λ * (2 * c ^ 2)) := by rw [← hΛxy]; gcongr
        _ ≤ (3 / 2 * c * Y * lam) ^ 2 := by
            rw [show (3 / 2 * c * Y * lam) ^ 2 = 9 / 4 * c ^ 2 * Y ^ 2 * lam ^ 2 by ring, hlam2]
            have h0 : 0 ≤ c ^ 2 * Y ^ 2 * Λ := by positivity
            linarith

end Erdos408.OneSided
