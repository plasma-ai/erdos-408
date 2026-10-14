import Erdos408.Extraction.Sieve
import Erdos408.Mertens
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.NumberTheory.Chebyshev

/-!
# From the smoothed statistic to `RectangleInput`

Unsmoothing (`blueprint/rectangle_input.md` §4; *The normal order of the
number of iterations of Euler's function* (Plasma AI, 2026), §6.4). Bound the
indicator of the dyad `x < p ≤ 2x` above by the smooth cutoff
`Φ(t) = S(W (t - 1) + 2) - S(W (t - 2))` of `(p - 1)/x`, with `S` the smooth
transition and steepness `W = T⁴⁰⁰`. It is `1` on `[1 - 1/W, 2]`, which
contains `(p - 1)/x` for every `p` in the dyad once `W ≤ x`, it vanishes
outside `(1 - 2/W, 2 + 1/W)`, and its derivatives are `O(W^r)`, so it lies in
the cutoff class with `κ = 3` and `C_Φ = 400`. Since the coefficient may be
signed, apply `eventually_smooth_rectangle` to `Φ` and bound the two endpoint
strips `(x - 2x/W, x]` and `(2x, 2x + 2x/W]` directly. With margin `T⁻²⁰`:

* Every slot prime dividing `n ≤ x²` exceeds `x^{T⁻²⁰}`, so `|f_𝔟(n)| ≤ 27 T⁶⁰`,
  and `|C_𝔟| ≤ 8 T³` by Mertens' second theorem.
* The prime number theorem with a power saving (`Erdos408.Analytic.PNT`)
  gives `O(x / (W L) + x^{1-c} / L)` primes in the strips, and
  `Π_x ≥ x / (4L)`.

So the strips lose `O((x / L) T⁶⁰ (1/W + x^{-c})) = O((x / L) T⁻³⁰⁰)`, and
dividing by `Π_x` gives `RectangleInput` with margin constant `1`.
-/

namespace Erdos408

open Filter Real Chebyshev

namespace Unsmooth

/-! ### The upper cutoff -/

/-- Every derivative of the smooth transition is bounded. -/
lemma exists_abs_iteratedDeriv_smoothTransition_le (r : ℕ) :
    ∃ K : ℝ, ∀ y, |iteratedDeriv r smoothTransition y| ≤ K := by
  have hcont : Continuous (iteratedDeriv r smoothTransition) :=
    smoothTransition.contDiff.continuous_iteratedDeriv r (by exact_mod_cast le_top)
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max K 1, fun y => ?_⟩
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · exact (hK y hy).trans (le_max_left _ _)
  refine le_trans ?_ (le_max_right _ _)
  rcases r with _ | r
  · rw [iteratedDeriv_zero, abs_le]
    exact ⟨by linarith [smoothTransition.nonneg y], smoothTransition.le_one y⟩
  -- off `[0, 1]` the transition is locally constant
  have hloc : ∃ c : ℝ, smoothTransition =ᶠ[nhds y] fun _ => c := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hy
    rcases hy with h | h
    · exact ⟨0, by filter_upwards [Iio_mem_nhds h] with z hz using
        smoothTransition.zero_of_nonpos hz.le⟩
    · exact ⟨1, by filter_upwards [Ioi_mem_nhds h] with z hz using
        smoothTransition.one_of_one_le hz.le⟩
  obtain ⟨c, hc⟩ := hloc
  rw [hc.iteratedDeriv_eq, iteratedDeriv_const]
  simp

/-- A bound `K_r` for the `r`-th derivative of the smooth transition. -/
noncomputable def transitionBound (r : ℕ) : ℝ :=
  (exists_abs_iteratedDeriv_smoothTransition_le r).choose

/-- The `r`-th derivative of the smooth transition is at most `K_r`. -/
lemma abs_iteratedDeriv_smoothTransition_le (r : ℕ) (y : ℝ) :
    |iteratedDeriv r smoothTransition y| ≤ transitionBound r :=
  (exists_abs_iteratedDeriv_smoothTransition_le r).choose_spec y

/-- The `r`-th derivative of `t ↦ S(W t + a)` is `W^r S^{(r)}(W t + a)`. -/
lemma iteratedDeriv_smoothTransition_affine (r : ℕ) (W a : ℝ) :
    iteratedDeriv r (fun t => smoothTransition (W * t + a)) =
      fun t => W ^ r * iteratedDeriv r smoothTransition (W * t + a) := by
  rw [iteratedDeriv_comp_const_mul (f := fun z => smoothTransition (z + a))
    (smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)) W]
  funext t
  rw [iteratedDeriv_comp_add_const]

/-- The upper cutoff `Φ_W(t) = S(W (t - 1) + 2) - S(W (t - 2))` of the dyad `(1, 2]`. -/
noncomputable def upperCutoff (W t : ℝ) : ℝ :=
  smoothTransition (W * (t - 1) + 2) - smoothTransition (W * (t - 2))

/-- The upper cutoff in affine form. -/
lemma upperCutoff_eq (W : ℝ) :
    upperCutoff W =
      (fun t => smoothTransition (W * t + (2 - W))) -
        fun t => smoothTransition (W * t + -(2 * W)) := by
  funext t
  simp only [upperCutoff, Pi.sub_apply]
  ring_nf

/-- The upper cutoff is smooth. -/
lemma contDiff_upperCutoff (W : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (upperCutoff W) := by
  unfold upperCutoff
  fun_prop

/-- The upper cutoff is `1` on `[1 - 1/W, 2]`. -/
lemma upperCutoff_eq_one {W t : ℝ} (hW : 0 < W) (h₁ : 1 - 1 / W ≤ t) (h₂ : t ≤ 2) :
    upperCutoff W t = 1 := by
  have hW' : W * (1 / W) = 1 := by field_simp
  have h₁' := mul_le_mul_of_nonneg_left h₁ hW.le
  rw [upperCutoff, smoothTransition.one_of_one_le (by nlinarith),
    smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hW.le (by linarith))]
  norm_num

/-- The upper cutoff takes values in `[0, 1]`. -/
lemma upperCutoff_mem_Icc {W : ℝ} (hW : 0 < W) (t : ℝ) :
    0 ≤ upperCutoff W t ∧ upperCutoff W t ≤ 1 := by
  rcases le_or_gt t 2 with ht | ht
  · rw [upperCutoff,
      smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hW.le (by linarith)),
      sub_zero]
    exact ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  · rw [upperCutoff, smoothTransition.one_of_one_le (by nlinarith)]
    constructor <;> linarith [smoothTransition.nonneg (W * (t - 2)),
      smoothTransition.le_one (W * (t - 2))]

/-- The upper cutoff vanishes outside `(1 - 2/W, 2 + 1/W)`. -/
lemma mem_Ioo_of_upperCutoff_ne_zero {W t : ℝ} (hW : 0 < W) (h : upperCutoff W t ≠ 0) :
    1 - 2 / W < t ∧ t < 2 + 1 / W := by
  have hW₁ : W * (1 / W) = 1 := by field_simp
  have hW₂ : W * (2 / W) = 2 := by field_simp
  have h2W : 0 < 2 / W := by positivity
  by_contra hc
  rw [not_and_or, not_lt, not_lt] at hc
  apply h
  rcases hc with ht | ht
  · have ht' := mul_le_mul_of_nonneg_left ht hW.le
    rw [upperCutoff, smoothTransition.zero_of_nonpos (by nlinarith),
      smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hW.le (by linarith)),
      sub_zero]
  · have ht' := mul_le_mul_of_nonneg_left ht hW.le
    have h1W : 0 < 1 / W := by positivity
    rw [upperCutoff, smoothTransition.one_of_one_le (by nlinarith),
      smoothTransition.one_of_one_le (by nlinarith), sub_self]

/-- The `r`-th derivative of the upper cutoff is at most `2 K_r W^r`. -/
lemma abs_iteratedDeriv_upperCutoff_le {W : ℝ} (hW : 0 < W) (r : ℕ) (t : ℝ) :
    |iteratedDeriv r (upperCutoff W) t| ≤ 2 * transitionBound r * W ^ r := by
  rw [upperCutoff_eq, iteratedDeriv_sub (by fun_prop) (by fun_prop),
    iteratedDeriv_smoothTransition_affine, iteratedDeriv_smoothTransition_affine, ← mul_sub,
    abs_mul, abs_of_pos (pow_pos hW r)]
  have h₁ := abs_iteratedDeriv_smoothTransition_le r (W * t + (2 - W))
  have h₂ := abs_iteratedDeriv_smoothTransition_le r (W * t + -(2 * W))
  have := abs_sub (iteratedDeriv r smoothTransition (W * t + (2 - W)))
    (iteratedDeriv r smoothTransition (W * t + -(2 * W)))
  nlinarith [pow_pos hW r]

/-- With `W = T⁴⁰⁰`, the upper cutoff lies in the cutoff class with `κ = 3` and
`C_Φ = 400`. -/
lemma isCutoff_upperCutoff {x : ℝ} (hT : 3 ≤ logLog x) :
    IsCutoff 3 400 (fun r => 2 * transitionBound r) x (upperCutoff (logLog x ^ 400)) := by
  have hW : 3 ≤ logLog x ^ 400 :=
    hT.trans (le_self_pow₀ (by linarith) (by norm_num))
  have hW0 : 0 < logLog x ^ 400 := by linarith
  refine ⟨contDiff_upperCutoff _, fun t => (upperCutoff_mem_Icc hW0 t).1, fun t ht => ?_,
    fun r t => ?_⟩
  · obtain ⟨h₁, h₂⟩ := mem_Ioo_of_upperCutoff_ne_zero hW0 ht
    have : 1 / logLog x ^ 400 ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hW
    have h2 : 2 / logLog x ^ 400 = 2 * (1 / logLog x ^ 400) := by ring
    constructor <;> linarith
  · rw [show (400 : ℝ) * r = ((400 * r : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      pow_mul]
    exact abs_iteratedDeriv_upperCutoff_le hW0 r t

/-! ### Primes in short intervals and in the dyad -/

/-- AC0 at the trivial character: `|ψ(y) - y| ≤ C y^{1-c}` with `0 < c ≤ 1`. -/
lemma exists_abs_psi_sub_le : ∃ c > (0 : ℝ), c ≤ 1 ∧ ∃ C ≥ (0 : ℝ), ∀ y : ℝ, 2 ≤ y →
    |ψ y - y| ≤ C * y ^ (1 - c) := by
  obtain ⟨c, hc, C, h⟩ := sum_vonMangoldt_mul_char_sub_le
  refine ⟨min c 1, lt_min hc one_pos, min_le_right _ _, max C 0, le_max_right _ _,
    fun y hy => ?_⟩
  have h₁ := h 1 (1 : DirichletCharacter ℂ 1) y hy
  have hone : ∀ n : ℕ, (1 : DirichletCharacter ℂ 1) n = 1 := fun n =>
    MulChar.one_apply (isUnit_of_subsingleton _)
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) - (y : ℂ) =
      ((ψ y - y : ℝ) : ℂ) := by
    rw [psi, ← Finset.Icc_add_one_left_eq_Ioc]
    push_cast
    simp
  simp only [hone, mul_one, ite_true] at h₁
  rw [hsum, Complex.norm_real, Real.norm_eq_abs, Nat.cast_one, Real.one_rpow, mul_one] at h₁
  calc |ψ y - y| ≤ C * y ^ (1 - c) := h₁
    _ ≤ max C 0 * y ^ (1 - min c 1) :=
      mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le (by linarith)
        (by linarith [min_le_left c 1])) (by positivity) (le_max_right _ _)

/-- `ψ(b) - ψ(a)` is the sum of `Λ` over `(a, b]`. -/
lemma psi_sub_psi {a b : ℝ} (hab : a ≤ b) :
    ψ b - ψ a = ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n := by
  rw [psi, psi, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊a⌋₊) (Nat.floor_le_floor hab)]
  ring

/-- `θ(b) - θ(a)` is the sum of `log p` over the primes of `(a, b]`. -/
lemma theta_sub_theta {a b : ℝ} (hab : a ≤ b) :
    θ b - θ a = ∑ p ∈ primesIoc a b, Real.log p := by
  have h := Finset.sum_Ioc_consecutive (fun p ↦ if p.Prime then Real.log p else 0)
    (Nat.zero_le ⌊a⌋₊) (Nat.floor_le_floor hab)
  simp only [theta, primesIoc, Finset.sum_filter] at *
  linarith

/-- The primes of `(a, b]` have `∑ log p ≤ ψ(b) - ψ(a)`. -/
lemma sum_log_primesIoc_le_psi_sub {a b : ℝ} (hab : a ≤ b) :
    ∑ p ∈ primesIoc a b, Real.log p ≤ ψ b - ψ a := by
  rw [psi_sub_psi hab, primesIoc]
  calc ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log p
      = ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, ArithmeticFunction.vonMangoldt p :=
        Finset.sum_congr rfl fun p hp =>
          (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.1 hp).2).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
        ArithmeticFunction.vonMangoldt_nonneg

/-- An interval `(a, b]` with `1 ≤ a` has `π(b) - π(a) ≤ (ψ(b) - ψ(a)) / log a`. -/
lemma card_primesIoc_mul_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ((primesIoc a b).card : ℝ) * Real.log a ≤ ψ b - ψ a := by
  refine le_trans ?_ (sum_log_primesIoc_le_psi_sub hab)
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun p hp => Real.log_le_log (by linarith) (mem_primesIoc.1 hp).2.1.le

/-- Primes in short intervals: for `4 ≤ x` and `x/2 ≤ a ≤ b ≤ 3x`, the interval `(a, b]`
contains at most `(2 / L) ((b - a) + C x^{1-c})` primes. -/
lemma exists_card_primesIoc_le : ∃ c > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ x : ℝ, 4 ≤ x → ∀ a b : ℝ,
    x / 2 ≤ a → a ≤ b → b ≤ 3 * x →
      ((primesIoc a b).card : ℝ) ≤ 2 / Real.log x * ((b - a) + C * x ^ (1 - c)) := by
  obtain ⟨c, hc, hc₁, C, hC, hψ⟩ := exists_abs_psi_sub_le
  refine ⟨c, hc, 6 * C, by positivity, fun x hx a b ha hab hb => ?_⟩
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  -- `log a ≥ log (x / 2) ≥ L / 2`
  have hla : Real.log x / 2 ≤ Real.log a := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have := Real.log_le_log (by norm_num) hx
    have := Real.log_le_log (by linarith) ha
    rw [Real.log_div (by linarith) (by norm_num)] at this
    linarith
  -- `y^{1-c} ≤ (3x)^{1-c} ≤ 3 x^{1-c}` for `y ≤ 3x`
  have h3 : ∀ y : ℝ, 0 ≤ y → y ≤ 3 * x → y ^ (1 - c) ≤ 3 * x ^ (1 - c) := by
    intro y hy0 hy
    calc y ^ (1 - c) ≤ (3 * x) ^ (1 - c) := Real.rpow_le_rpow hy0 hy (by linarith)
      _ = 3 ^ (1 - c) * x ^ (1 - c) := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 3 * x ^ (1 - c) := by
        gcongr
        calc (3 : ℝ) ^ (1 - c) ≤ 3 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 3 := Real.rpow_one 3
  have hψb := abs_le.1 (hψ b (by linarith))
  have hψa := abs_le.1 (hψ a (by linarith))
  have hb' := h3 b (by linarith) hb
  have ha' := h3 a (by linarith) (by linarith)
  have hcard := card_primesIoc_mul_log_le (by linarith) hab
  have hN : ((primesIoc a b).card : ℝ) * (Real.log x / 2) ≤ (b - a) + 6 * C * x ^ (1 - c) := by
    have := mul_le_mul_of_nonneg_left hla (Nat.cast_nonneg (primesIoc a b).card)
    nlinarith
  calc ((primesIoc a b).card : ℝ) = (primesIoc a b).card * (Real.log x / 2) * (2 / Real.log x) := by
        field_simp
    _ ≤ ((b - a) + 6 * C * x ^ (1 - c)) * (2 / Real.log x) := by gcongr
    _ = _ := by ring

/-- The dyad `(x, 2x]` contains at least `x / (4L)` primes for large `x`. -/
lemma eventually_card_dyadicPrimes_ge :
    ∀ᶠ x : ℝ in atTop, x / (4 * Real.log x) ≤ (dyadicPrimes x).card := by
  obtain ⟨c, hc, hc₁, C, hC, hψ⟩ := exists_abs_psi_sub_le
  have h₁ : ∀ᶠ x : ℝ in atTop, 12 * C ≤ x ^ c := (tendsto_rpow_atTop hc).eventually_ge_atTop _
  have h₂ : ∀ᶠ x : ℝ in atTop, Real.log x ≤ 1 / 32 * x ^ (1 / 2 : ℝ) := by
    filter_upwards [(isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound
      (c := 1 / 32) (by norm_num), eventually_ge_atTop 1] with x hx hx1
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (by positivity)] at hx
  filter_upwards [h₁, h₂, eventually_ge_atTop 4] with x h₁ h₂ hx
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
  have hl2x : Real.log (2 * x) = Real.log 2 + Real.log x :=
    Real.log_mul (by norm_num) hx0.ne'
  -- the power saving: `3 C x^{1-c} ≤ x / 4`
  have hpow : x ^ (1 - c) * x ^ c = x := by
    rw [← Real.rpow_add hx0, sub_add_cancel, Real.rpow_one]
  have hsave : 12 * C * x ^ (1 - c) ≤ x := by
    calc 12 * C * x ^ (1 - c) ≤ x ^ c * x ^ (1 - c) :=
          mul_le_mul_of_nonneg_right h₁ (by positivity)
      _ = x := by rw [mul_comm, hpow]
  have h2x : (2 * x) ^ (1 - c) ≤ 2 * x ^ (1 - c) := by
    rw [Real.mul_rpow (by norm_num) hx0.le]
    gcongr
    calc (2 : ℝ) ^ (1 - c) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  -- the prime powers: `2 √(2x) log (2x) ≤ 8 √x L ≤ x / 4`
  have hsq : √x * √x = x := Real.mul_self_sqrt hx0.le
  have hs2 : √2 ≤ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hs2x : √(2 * x) = √2 * √x := Real.sqrt_mul (by norm_num) x
  rw [← Real.sqrt_eq_rpow] at h₂
  have hpp : 2 * √(2 * x) * Real.log (2 * x) ≤ x / 4 := by
    rw [hs2x, hl2x]
    calc 2 * (√2 * √x) * (Real.log 2 + Real.log x) ≤ 2 * (2 * √x) * (2 * Real.log x) := by
          gcongr
          linarith
      _ = 8 * (√x * Real.log x) := by ring
      _ ≤ 8 * (√x * (1 / 32 * √x)) := by gcongr
      _ = x / 4 := by linear_combination (1 / 4) * hsq
  -- `θ(2x) - θ(x) ≥ x / 2`
  have hψ₂ := abs_le.1 (hψ (2 * x) (by linarith))
  have hψ₁ := abs_le.1 (hψ x (by linarith))
  have hθ₂ := psi_sub_theta_le (x := 2 * x) (by linarith)
  have hθ₁ := theta_le_psi x
  have hθ : x / 2 ≤ θ (2 * x) - θ x := by nlinarith
  -- `θ(2x) - θ(x) ≤ π_x log (2x)`
  have hsum : θ (2 * x) - θ x ≤ (dyadicPrimes x).card * Real.log (2 * x) := by
    rw [theta_sub_theta (by linarith), dyadicPrimes_eq_primesIoc, ← nsmul_eq_mul,
      ← Finset.sum_const]
    exact Finset.sum_le_sum fun p hp =>
      Real.log_le_log (by exact_mod_cast (mem_primesIoc.1 hp).1.pos) (mem_primesIoc.1 hp).2.2
  rw [div_le_iff₀ (by positivity)]
  have := Nat.cast_nonneg (α := ℝ) (dyadicPrimes x).card
  nlinarith

/-! ### Size of the slot statistic -/

/-- An integer `0 < n ≤ x²` is divisible by at most `(2/ε + 1)³` slot tuples whose primes all
exceed `x^ε`, so the slot count is at most that in modulus. -/
lemma abs_slotCount_le {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) {k : ℕ} (hk : k ≤ 2)
    {u v : Fin (k + 1) → ℝ} (hu : ∀ i, ε ≤ u i) {B : (Fin k → ℕ) → ℝ} (hB : ∀ Q, |B Q| ≤ 1)
    {n : ℕ} (hn₀ : n ≠ 0) (hn : (n : ℝ) ≤ x ^ 2) :
    |slotCount x u v B n| ≤ (2 / ε + 1) ^ 3 := by
  set D := n.primeFactors.filter fun q : ℕ => x ^ ε < (q : ℝ)
  -- the tuples dividing `n` have their primes in `D`
  have hsub : (slotTuples x u v).filter (fun Q => ∏ i, Q i ∣ n) ⊆
      Fintype.piFinset fun _ => D := by
    intro Q hQ
    obtain ⟨hQ, hdvd⟩ := Finset.mem_filter.1 hQ
    rw [slotTuples, Finset.mem_filter, Fintype.mem_piFinset] at hQ
    rw [Fintype.mem_piFinset]
    intro i
    obtain ⟨-, hp, hlt⟩ := Finset.mem_filter.1 (hQ.1 i)
    refine Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp,
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans hdvd, hn₀⟩, ?_⟩
    exact (Real.rpow_le_rpow_of_exponent_le hx.le (hu i)).trans_lt hlt
  -- `x^{ε |D|} ≤ ∏_D q ≤ n ≤ x²`, so `|D| ≤ 2 / ε`
  have hD : (D.card : ℝ) ≤ 2 / ε := by
    have hprod : ∏ q ∈ D, (q : ℝ) ≤ n := by
      have hdvd : ∏ q ∈ D, q ∣ n :=
        (Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)).trans
          (Nat.prod_primeFactors_dvd n)
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn₀) hdvd
    have hpow : (x ^ ε) ^ D.card ≤ ∏ q ∈ D, (q : ℝ) := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => by positivity) fun q hq =>
        (Finset.mem_filter.1 hq).2.le
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)] at hpow
    have h2 : x ^ (ε * D.card) ≤ x ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      linarith
    rw [Real.rpow_le_rpow_left_iff hx] at h2
    rw [le_div_iff₀ hε]
    linarith
  calc |slotCount x u v B n|
      ≤ ∑ Q ∈ (slotTuples x u v).filter (fun Q => ∏ i, Q i ∣ n), |B (Fin.init Q)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ Q ∈ (slotTuples x u v).filter (fun Q => ∏ i, Q i ∣ n), (1 : ℝ) :=
        Finset.sum_le_sum fun Q _ => hB _
    _ ≤ ((Fintype.piFinset fun _ : Fin (k + 1) => D).card : ℝ) := by
        rw [Finset.sum_const, nsmul_one]
        exact_mod_cast Finset.card_le_card hsub
    _ = (D.card : ℝ) ^ (k + 1) := by
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        push_cast
        rfl
    _ ≤ (2 / ε + 1) ^ (k + 1) := by gcongr; linarith
    _ ≤ (2 / ε + 1) ^ 3 :=
        pow_le_pow_right₀ (by linarith [show 0 < 2 / ε by positivity]) (by omega)

/-- The slot primes are at most `x`, so `|C_𝔟| ≤ (∑_{p ≤ x} 1/p)^{k+1}`. -/
lemma abs_slotMean_le {x : ℝ} (hx : 1 < x) {k : ℕ} {u v : Fin (k + 1) → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hv : ∑ i, v i ≤ 1) {B : (Fin k → ℕ) → ℝ} (hB : ∀ Q, |B Q| ≤ 1) :
    |slotMean x u v B| ≤ (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ (k + 1) := by
  -- every slot tuple has its primes in `(1, x]`
  have hsub : slotTuples x u v ⊆ Fintype.piFinset fun _ => primesIoc 1 x := by
    intro Q hQ
    rw [slotTuples, Finset.mem_filter, Fintype.mem_piFinset] at hQ
    rw [Fintype.mem_piFinset]
    -- each slot is nonempty, so `u i < v i` and hence `0 < v i ≤ 1`
    have hle : ∀ i, (Q i : ℝ) ≤ x ^ v i ∧ x ^ u i < Q i := fun i => by
      obtain ⟨hQi, -, hlt⟩ := Finset.mem_filter.1 (hQ.1 i)
      exact ⟨(Nat.le_floor_iff (by positivity)).1 (Finset.mem_Iic.1 hQi), hlt⟩
    have hv₀ : ∀ i, 0 ≤ v i := fun i => by
      by_contra h
      have := Real.rpow_le_rpow_of_exponent_le hx.le ((not_le.1 h).le.trans (hu i))
      linarith [hle i]
    intro i
    obtain ⟨hQi, hp, -⟩ := Finset.mem_filter.1 (hQ.1 i)
    refine mem_primesIoc_one.2 ⟨hp, (hle i).1.trans ?_⟩
    calc x ^ v i ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le
          ((Finset.single_le_sum (fun j _ => hv₀ j) (Finset.mem_univ i)).trans hv)
      _ = x := Real.rpow_one x
  have hpos : ∀ Q ∈ Fintype.piFinset (fun _ : Fin (k + 1) => primesIoc 1 x),
      0 < ∏ i, (Q i : ℝ) := fun Q hQ => Finset.prod_pos fun i _ => by
    exact_mod_cast (mem_primesIoc.1 (Fintype.mem_piFinset.1 hQ i)).1.pos
  calc |slotMean x u v B|
      ≤ ∑ Q ∈ slotTuples x u v, |B (Fin.init Q) / ∏ i, (Q i : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ Q ∈ slotTuples x u v, 1 / ∏ i, (Q i : ℝ) := by
        refine Finset.sum_le_sum fun Q hQ => ?_
        have := hpos Q (hsub hQ)
        rw [abs_div, abs_of_pos this]
        exact div_le_div_of_nonneg_right (hB _) this.le
    _ ≤ ∑ Q ∈ Fintype.piFinset (fun _ : Fin (k + 1) => primesIoc 1 x),
          1 / ∏ i, (Q i : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun Q hQ _ => (one_div_pos.2 (hpos Q hQ)).le
    _ = (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ (k + 1) := by
        rw [← Fin.prod_const, Finset.prod_univ_sum]
        refine Finset.sum_congr rfl fun Q _ => ?_
        rw [one_div, ← Finset.prod_inv_distrib]
        simp only [one_div]

/-- Mertens' second theorem: `∑_{p ≤ x} 1/p ≤ T + E`. -/
lemma exists_sum_primesIoc_one_inv_le : ∃ E : ℝ, ∀ x : ℝ, 2 ≤ x →
    ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p ≤ logLog x + E := by
  obtain ⟨E, -, hE⟩ := mertens_second
  refine ⟨1 / 2 - Real.log (Real.log 2) + E / Real.log 2, fun x hx => ?_⟩
  have h2 : primesIoc 1 2 = {2} := by
    ext p
    rw [mem_primesIoc, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, -, h⟩
      have : p ≤ 2 := by exact_mod_cast h
      have := hp.two_le
      omega
    · rintro rfl
      exact ⟨Nat.prime_two, by norm_num, by norm_num⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have h := (abs_le.1 (hE 2 x le_rfl hx)).2
  rw [Real.log_div hlogx.ne' hlog2.ne'] at h
  rw [← sum_primesIoc_add _ (by norm_num : (1 : ℝ) ≤ 2) hx, h2, Finset.sum_singleton, logLog]
  push_cast
  linarith

/-- `T = log log x` tends to infinity. -/
lemma tendsto_logLog_atTop : Tendsto logLog atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

/-- For admissible slots with margin `T⁻²⁰` and `0 < n ≤ x²`, `|f_𝔟(n) - C_𝔟| ≤ 35 T⁶⁰`. -/
lemma eventually_abs_slotCount_sub_slotMean_le : ∀ᶠ x : ℝ in atTop,
    ∀ k ≤ 2, ∀ (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ),
      AdmissibleSlots 1 x u v → (∀ Q, |B Q| ≤ 1) → ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ x ^ 2 →
        |slotCount x u v B n - slotMean x u v B| ≤ 35 * logLog x ^ 60 := by
  obtain ⟨E, hE⟩ := exists_sum_primesIoc_one_inv_le
  filter_upwards [tendsto_logLog_atTop.eventually_ge_atTop (max 1 E), eventually_ge_atTop 2]
    with x hT hx k hk u v B ⟨hu, hv⟩ hB n hn₀ hn
  have hT₁ : 1 ≤ logLog x := (le_max_left _ _).trans hT
  have hTE : E ≤ logLog x := (le_max_right _ _).trans hT
  have hT20 : 1 ≤ logLog x ^ 20 := one_le_pow₀ hT₁
  have hε : 0 < 1 / logLog x ^ 20 := by positivity
  -- the slot count: `(2 T²⁰ + 1)³ ≤ 27 T⁶⁰`
  have h₁ := abs_slotCount_le (v := v) (by linarith) hε hk hu hB hn₀ hn
  have h₁' : (2 / (1 / logLog x ^ 20) + 1) ^ 3 ≤ 27 * logLog x ^ 60 := by
    rw [div_div_eq_mul_div, div_one]
    calc (2 * logLog x ^ 20 + 1) ^ 3 ≤ (3 * logLog x ^ 20) ^ 3 := by gcongr; linarith
      _ = 27 * logLog x ^ 60 := by ring
  -- the harmonic model: `(T + E)^{k+1} ≤ (2T)³ ≤ 8 T⁶⁰`
  have hv₁ : ∑ i, v i ≤ 1 := by linarith
  have h₂ := abs_slotMean_le (x := x) (by linarith) (fun i => hε.le.trans (hu i)) hv₁ hB
  have hH₀ : 0 ≤ ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p :=
    Finset.sum_nonneg fun _ _ => by positivity
  have h₂' : (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ (k + 1) ≤ 8 * logLog x ^ 60 := by
    calc (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ (k + 1) ≤ (2 * logLog x) ^ (k + 1) := by
          gcongr
          linarith [hE x hx]
      _ ≤ (2 * logLog x) ^ 3 := pow_le_pow_right₀ (by linarith) (by omega)
      _ = 8 * logLog x ^ 3 := by ring
      _ ≤ 8 * logLog x ^ 60 := by gcongr; norm_num
  calc |slotCount x u v B n - slotMean x u v B|
      ≤ |slotCount x u v B n| + |slotMean x u v B| := abs_sub _ _
    _ ≤ 27 * logLog x ^ 60 + 8 * logLog x ^ 60 := add_le_add (h₁.trans h₁') (h₂.trans h₂')
    _ = 35 * logLog x ^ 60 := by ring

/-! ### The endpoint strips -/

/-- `T^n ≤ x^c` for large `x`. -/
lemma eventually_logLog_pow_le_rpow (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, logLog x ^ n ≤ x ^ c := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop (n : ℝ) hc).bound one_pos,
    tendsto_logLog_atTop.eventually_ge_atTop 0, eventually_ge_atTop 1] with x hx hT hx₁
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx₁
  rw [Real.rpow_natCast, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), one_mul] at hx
  exact (pow_le_pow_left₀ hT (Real.log_le_self hL) n).trans hx

/-- Off the strips `(x - 2x/W, x]` and `(2x, 2x + 2x/W]`, the upper cutoff at `(p - 1)/x`
agrees with the indicator of the dyad. -/
lemma abs_upperCutoff_sub_indicator_le {x W : ℝ} (hW : 4 ≤ W) (hWx : W ≤ x) {p : ℕ}
    (hp : p.Prime) :
    |upperCutoff W (((p : ℝ) - 1) / x) - if p ∈ dyadicPrimes x then 1 else 0| ≤
      (if p ∈ primesIoc (x - 2 * x / W) x then 1 else 0) +
        if p ∈ primesIoc (2 * x) (2 * x + 2 * x / W) then 1 else 0 := by
  have hW0 : 0 < W := by linarith
  have hx0 : 0 < x := by linarith
  have hxW : 1 ≤ x / W := (one_le_div hW0).2 hWx
  have hS : 0 ≤ (if p ∈ primesIoc (x - 2 * x / W) x then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hS' : 0 ≤ (if p ∈ primesIoc (2 * x) (2 * x + 2 * x / W) then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  by_cases hd : p ∈ dyadicPrimes x
  · -- on the dyad the cutoff is `1`
    obtain ⟨-, hlt, hle⟩ := mem_primesIoc.1 ((dyadicPrimes_eq_primesIoc x) ▸ hd)
    rw [ite_eq_left hd, upperCutoff_eq_one hW0, sub_self, abs_zero]
    · positivity
    · rw [le_div_iff₀ hx0]
      have : (1 - 1 / W) * x = x - x / W := by ring
      linarith
    · rw [div_le_iff₀ hx0]
      linarith
  rw [ite_eq_right hd, sub_zero, abs_of_nonneg (upperCutoff_mem_Icc hW0 _).1]
  by_cases h0 : upperCutoff W (((p : ℝ) - 1) / x) = 0
  · rw [h0]
    positivity
  obtain ⟨h₁, h₂⟩ := mem_Ioo_of_upperCutoff_ne_zero hW0 h0
  rw [lt_div_iff₀ hx0] at h₁
  rw [div_lt_iff₀ hx0] at h₂
  have h₁' : (1 - 2 / W) * x = x - 2 * x / W := by ring
  have h₂' : (2 + 1 / W) * x = 2 * x + x / W := by ring
  have hle := (upperCutoff_mem_Icc hW0 (((p : ℝ) - 1) / x)).2
  rw [dyadicPrimes_eq_primesIoc, mem_primesIoc] at hd
  rcases le_or_gt (p : ℝ) x with hpx | hpx
  · -- the lower strip
    rw [ite_eq_left (mem_primesIoc.2 ⟨hp, by linarith, hpx⟩)]
    linarith
  · -- the upper strip
    have h2x : 2 * x < p := by
      by_contra h
      exact hd ⟨hp, hpx, not_lt.1 h⟩
    have h2W : 2 * x / W = 2 * (x / W) := by ring
    rw [ite_eq_left (mem_primesIoc.2 ⟨hp, h2x, by linarith⟩)]
    linarith

/-- A sum of indicators over `A` of membership in `S` is at most `|S|`. -/
lemma sum_indicator_le_card (A S : Finset ℕ) :
    ∑ p ∈ A, (if p ∈ S then (1 : ℝ) else 0) ≤ S.card := by
  rw [Finset.sum_boole]
  exact_mod_cast Finset.card_le_card fun p hp => (Finset.mem_filter.1 hp).2

end Unsmooth

open Unsmooth

/-- The two graph hypotheses imply the rectangle statistic. -/
theorem rectangleInput_of_hypotheses (h₁ : OneSidedTypeII) (h₂ : TwoSidedCorrelation) :
    RectangleInput := by
  obtain ⟨C₀, hC₀⟩ := eventually_smooth_rectangle h₁ h₂ 1 3 400
    (fun r => 2 * transitionBound r) one_pos (by norm_num)
  obtain ⟨c, hc, C, hC, hπ⟩ := exists_card_primesIoc_le
  refine ⟨1, one_pos, 4 * (C₀ + 140 * (2 + C)), ?_⟩
  filter_upwards [hC₀, eventually_abs_slotCount_sub_slotMean_le, eventually_card_dyadicPrimes_ge,
    tendsto_logLog_atTop.eventually_ge_atTop 4, eventually_logLog_pow_le_rpow 400 one_pos,
    eventually_logLog_pow_le_rpow 360 hc, eventually_ge_atTop 4]
    with x hsmooth hslot hdyad hT hWx hsave hx k hk u v hu hv B hB
  have hadm : AdmissibleSlots 1 x u v := ⟨hu, hv⟩
  set T := logLog x with hTdef
  set L := Real.log x with hLdef
  set W := T ^ 400 with hWdef
  set A := primesIcc 2 (3 * x + 1)
  set g : ℕ → ℝ := fun p => slotCount x u v B (p - 1) - slotMean x u v B with hg
  set τ := (T ^ 300)⁻¹ with hτ
  rw [Real.rpow_one] at hWx
  have hx0 : 0 < x := by linarith
  have hL : 0 < L := Real.log_pos (by linarith)
  have hT0 : 0 < T := by linarith
  have hW : 4 ≤ W := hT.trans (le_self_pow₀ (by linarith) (by norm_num))
  have hτ0 : 0 < τ := by positivity
  -- the smoothed statistic
  have hΦ : |∑ p ∈ A, upperCutoff W (((p : ℝ) - 1) / x) * g p| ≤ x / L * (C₀ * τ) := by
    have h := hsmooth k hk u v B (upperCutoff W) hadm hB (isCutoff_upperCutoff (by linarith))
    rw [Real.rpow_neg hT0.le, Real.rpow_ofNat] at h
    calc _ = x / L * (L / x * |∑ p ∈ A, upperCutoff W (((p : ℝ) - 1) / x) * g p|) := by
          field_simp
      _ ≤ x / L * (C₀ * τ) := by gcongr
  -- the endpoint strips
  have hg₀ : ∀ p ∈ A, |g p| ≤ 35 * T ^ 60 := by
    intro p hp
    obtain ⟨hpI, hp⟩ := Finset.mem_filter.1 hp
    have hp3 : (p : ℝ) ≤ 3 * x + 1 :=
      (Nat.le_floor_iff (by linarith)).1 (Finset.mem_Icc.1 hpI).2
    have hp1 : ((p - 1 : ℕ) : ℝ) = p - 1 := by
      rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    refine hslot k hk u v B hadm hB (p - 1) (by have := hp.two_le; omega) ?_
    rw [hp1]
    nlinarith
  have hstrip : |∑ p ∈ A, (upperCutoff W (((p : ℝ) - 1) / x) -
      if p ∈ dyadicPrimes x then 1 else 0) * g p| ≤
      35 * T ^ 60 * ((primesIoc (x - 2 * x / W) x).card +
        (primesIoc (2 * x) (2 * x + 2 * x / W)).card) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ p ∈ A, |(upperCutoff W (((p : ℝ) - 1) / x) -
          if p ∈ dyadicPrimes x then 1 else 0) * g p|
        ≤ ∑ p ∈ A, ((if p ∈ primesIoc (x - 2 * x / W) x then 1 else 0) +
            (if p ∈ primesIoc (2 * x) (2 * x + 2 * x / W) then 1 else 0)) *
              (35 * T ^ 60) := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [abs_mul]
          exact mul_le_mul (abs_upperCutoff_sub_indicator_le hW hWx (Finset.mem_filter.1 hp).2)
            (hg₀ p hp) (abs_nonneg _) (by split_ifs <;> norm_num)
      _ = 35 * T ^ 60 * (∑ p ∈ A, (if p ∈ primesIoc (x - 2 * x / W) x then (1 : ℝ) else 0) +
            ∑ p ∈ A, if p ∈ primesIoc (2 * x) (2 * x + 2 * x / W) then (1 : ℝ) else 0) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ _ := by
          gcongr
          · exact sum_indicator_le_card _ _
          · exact sum_indicator_le_card _ _
  -- the primes in the strips
  have h2xW : 2 * x / W ≤ x / 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h2xW₀ : 0 ≤ 2 * x / W := by positivity
  have hS₁ := hπ x hx (x - 2 * x / W) x (by linarith) (by linarith) (by linarith)
  have hS₂ := hπ x hx (2 * x) (2 * x + 2 * x / W) (by linarith) (by linarith) (by linarith)
  have hA : T ^ 60 * (2 * x / W) ≤ 2 * x * τ := by
    have : T ^ 60 * (2 * x / W) = 2 * x * (T ^ 340)⁻¹ := by
      rw [hWdef]
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left
      (inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by norm_num))) (by positivity)
  have hB' : T ^ 60 * (C * x ^ (1 - c)) ≤ C * x * τ := by
    have hpow : x ^ c * x ^ (1 - c) = x := by
      rw [← Real.rpow_add hx0, add_sub_cancel, Real.rpow_one]
    have h360 : T ^ 360 * x ^ (1 - c) ≤ x :=
      (mul_le_mul_of_nonneg_right hsave (by positivity)).trans_eq hpow
    have : T ^ 60 * (C * x ^ (1 - c)) = C * (T ^ 360 * x ^ (1 - c)) * τ := by
      rw [hτ]
      field_simp
    rw [this]
    gcongr
  have hstrip' : 35 * T ^ 60 * ((primesIoc (x - 2 * x / W) x).card +
      (primesIoc (2 * x) (2 * x + 2 * x / W)).card) ≤ x / L * (140 * (2 + C) * τ) := by
    have h := add_le_add hS₁ hS₂
    rw [show x - (x - 2 * x / W) = 2 * x / W by ring,
      show 2 * x + 2 * x / W - 2 * x = 2 * x / W by ring] at h
    calc 35 * T ^ 60 * ((primesIoc (x - 2 * x / W) x).card +
          (primesIoc (2 * x) (2 * x + 2 * x / W)).card)
        ≤ 35 * T ^ 60 * (2 / L * (2 * x / W + C * x ^ (1 - c)) +
            2 / L * (2 * x / W + C * x ^ (1 - c))) := by gcongr
      _ = 140 / L * (T ^ 60 * (2 * x / W) + T ^ 60 * (C * x ^ (1 - c))) := by ring
      _ ≤ 140 / L * (2 * x * τ + C * x * τ) := by gcongr
      _ = x / L * (140 * (2 + C) * τ) := by ring
  -- unsmoothing
  have hsub : dyadicPrimes x ⊆ A := by
    intro p hp
    obtain ⟨hp, hlt, hle⟩ := mem_primesIoc.1 ((dyadicPrimes_eq_primesIoc x) ▸ hp)
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, Nat.le_floor (by linarith)⟩, hp⟩
    rw [Nat.ceil_le]
    exact_mod_cast hp.two_le
  have hsplit : ∑ p ∈ dyadicPrimes x, g p =
      ∑ p ∈ A, upperCutoff W (((p : ℝ) - 1) / x) * g p -
        ∑ p ∈ A, (upperCutoff W (((p : ℝ) - 1) / x) -
          if p ∈ dyadicPrimes x then 1 else 0) * g p := by
    rw [← Finset.sum_sub_distrib]
    simp only [sub_mul, sub_sub_cancel, ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hsub]
  have hbound : |∑ p ∈ dyadicPrimes x, g p| ≤ x / L * ((C₀ + 140 * (2 + C)) * τ) := by
    rw [hsplit]
    refine (abs_sub _ _).trans ?_
    calc _ ≤ x / L * (C₀ * τ) + x / L * (140 * (2 + C) * τ) :=
          add_le_add hΦ (hstrip.trans hstrip')
      _ = _ := by ring
  -- normalizing by `π_x ≥ x / (4L)`
  have hN : 0 < ((dyadicPrimes x).card : ℝ) := lt_of_lt_of_le (by positivity) hdyad
  have heq : (∑ p ∈ dyadicPrimes x, slotCount x u v B (p - 1)) / (dyadicPrimes x).card -
      slotMean x u v B = (∑ p ∈ dyadicPrimes x, g p) / (dyadicPrimes x).card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp
  change |(∑ p ∈ dyadicPrimes x, slotCount x u v B (p - 1)) / (dyadicPrimes x).card -
    slotMean x u v B| ≤ _
  rw [heq, abs_div, Nat.abs_cast]
  have hK : 0 ≤ x / L * ((C₀ + 140 * (2 + C)) * τ) := (abs_nonneg _).trans hbound
  calc |∑ p ∈ dyadicPrimes x, g p| / (dyadicPrimes x).card
      ≤ x / L * ((C₀ + 140 * (2 + C)) * τ) / (dyadicPrimes x).card := by gcongr
    _ ≤ x / L * ((C₀ + 140 * (2 + C)) * τ) / (x / (4 * L)) :=
        div_le_div_of_nonneg_left hK (by positivity) hdyad
    _ = 4 * (C₀ + 140 * (2 + C)) / T ^ 300 := by
        rw [hτ]
        field_simp

end Erdos408
