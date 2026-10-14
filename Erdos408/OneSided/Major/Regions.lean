import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The two regions of one arc term

`blueprint/one_sided_type_ii.md` §6.4, "One arc term". After the Mellin separation, one arc
term is at most a multiple of `∫∫ k₁(τ) k₂(τ + σ) g(τ) g(-σ) dτ dσ`, where
`k₁(τ) = (1 + |τ|/X)^{-2}` and `k₂(u) = (1 + |u|)^{-2}` come from the kernel bound and `g` is
the size of the separated polynomial. Here `g²` has mean value at most `M (1 + |I|/X)` on
every interval `I`, and energy at most `E` on `[-T, T]`.

* `integral_compl_Icc_mul_le`: the `τ`-tail `∫_{|τ| > T} k₁ f ≤ 8 M X / T` for `T ≥ X`, by
  the dyadic intervals `[2^j T, 2^{j+1} T)`, on each of which `k₁ ≤ (X / 2^j T)²`.
* `integral_kernel_mul_le`: substitute `s = τ + σ` and integrate in `s` last, against
  `∫ k₂ ≤ π`. For fixed `s`, split `τ` at `±T`. On `[-T, T]` use `k₁ ≤ 1` and
  `2 g g' ≤ ε g² + ε⁻¹ g'²`, then the energy and the mean value on an interval of length
  `2T`. On `|τ| > T` use `2 g g' ≤ g² + g'²` and the `τ`-tail twice.

Only `τ` is split. The bound on `[-T, T]` is uniform in `s`, so no separate `s`-tail is
needed.
-/

namespace Erdos408.OneSided

open MeasureTheory Real

/-- `(1 + |τ|/X)^{-2}` is integrable for `X > 0`. -/
private theorem integrable_inv_one_add_abs_div_sq {X : ℝ} (hX : 0 < X) :
    Integrable fun τ : ℝ => ((1 + |τ| / X) ^ 2)⁻¹ := by
  refine (integrable_inv_one_add_sq.comp_div hX.ne').mono' ?_
    (Filter.Eventually.of_forall fun τ => ?_)
  · exact (Continuous.inv₀ (by fun_prop) fun τ => by positivity).aestronglyMeasurable
  · have ha : 0 ≤ |τ| / X := by positivity
    have hsq : (τ / X) ^ 2 = (|τ| / X) ^ 2 := by rw [div_pow, div_pow, sq_abs]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine inv_anti₀ (by positivity) ?_
    rw [hsq]
    nlinarith

/-- `(1 + |u|)^{-2}` is integrable. -/
private theorem integrable_inv_one_add_abs_sq :
    Integrable fun u : ℝ => ((1 + |u|) ^ 2)⁻¹ := by
  simpa using integrable_inv_one_add_abs_div_sq one_pos

/-- `∫ (1 + |u|)^{-2} ≤ π`. -/
private theorem integral_inv_one_add_abs_sq_le : ∫ u : ℝ, ((1 + |u|) ^ 2)⁻¹ ≤ π := by
  rw [← integral_univ_inv_one_add_sq]
  refine integral_mono integrable_inv_one_add_abs_sq integrable_inv_one_add_sq fun u => ?_
  refine inv_anti₀ (by positivity) ?_
  rw [← sq_abs u]
  nlinarith [abs_nonneg u]

/-- On `[-T, T]` a continuous set integral is the interval integral. -/
private theorem integral_Icc_eq_intervalIntegral (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ τ in Set.Icc (-T) T, f τ = ∫ τ in (-T)..T, f τ := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]

/-! ### The `τ`-tail -/

/-- The right `τ`-tail: if `f ≥ 0` has `∫_a^b f ≤ M (1 + (b - a)/X)` on every interval, then
`∫_{τ > T} (1 + |τ|/X)^{-2} f ≤ 4 M X / T` for `T ≥ X`. -/
theorem integral_Ioi_mul_le {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ τ, 0 ≤ f τ) {F₀ : ℝ}
    (hfF : ∀ τ, f τ ≤ F₀) {X T M : ℝ} (hX : 0 < X) (hXT : X ≤ T)
    (hM : ∀ a b, a ≤ b → ∫ τ in a..b, f τ ≤ M * (1 + (b - a) / X)) :
    ∫ τ in Set.Ioi T, ((1 + |τ| / X) ^ 2)⁻¹ * f τ ≤ 4 * M * X / T := by
  have hT : 0 < T := hX.trans_le hXT
  have hM0 : 0 ≤ M := by
    have h := hM T T le_rfl
    rw [intervalIntegral.integral_same, sub_self, zero_div, add_zero, mul_one] at h
    exact h
  set g : ℝ → ℝ := fun τ => ((1 + |τ| / X) ^ 2)⁻¹ * f τ with hg
  have hgc : Continuous g := (Continuous.inv₀ (by fun_prop) fun τ => by positivity).mul hf
  have hgi : Integrable g := by
    refine ((integrable_inv_one_add_abs_div_sq hX).mul_const F₀).mono'
      hgc.aestronglyMeasurable (Filter.Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hf0 τ))]
    exact mul_le_mul_of_nonneg_left (hfF τ) (by positivity)
  -- the dyadic intervals `[2^j T, 2^{j+1} T)` partition `[T, ∞)`
  set s : ℕ → Set ℝ := fun j => Set.Ico (2 ^ j * T) (2 ^ (j + 1) * T) with hs
  have hcover : (⋃ j, s j) = Set.Ici T := by
    ext τ
    simp only [Set.mem_iUnion, Set.mem_Ico, Set.mem_Ici, hs]
    constructor
    · rintro ⟨j, hj, -⟩
      exact (le_mul_of_one_le_left hT.le (one_le_pow₀ one_le_two)).trans hj
    · intro hτ
      obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near ((one_le_div hT).2 hτ) one_lt_two
      exact ⟨j, (le_div_iff₀ hT).1 hj, (div_lt_iff₀ hT).1 hj'⟩
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    have hle : ∀ i j : ℕ, i < j → (2 : ℝ) ^ (i + 1) * T ≤ 2 ^ j * T := fun i j hij =>
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) hT.le
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro τ hi hj
    rcases lt_or_gt_of_ne hij with h | h
    · linarith [hle i j h, hi.2, hj.1]
    · linarith [hle j i h, hi.1, hj.2]
  have hsum := hasSum_integral_iUnion (fun j => measurableSet_Ico) hdisj
    (by rw [hcover]; exact hgi.integrableOn)
  rw [hcover, integral_Ici_eq_integral_Ioi] at hsum
  refine hasSum_le (fun j => ?_) hsum (hasSum_geometric_two' (4 * M * X / T))
  -- on `[P, 2P)`, `P = 2^j T`, `(1 + |τ|/X)^{-2} ≤ (X / P)²`
  set P : ℝ := 2 ^ j * T with hP
  have hP0 : 0 < P := by positivity
  have hXP : X ≤ P := hXT.trans (le_mul_of_one_le_left hT.le (one_le_pow₀ one_le_two))
  have hlen : 2 ^ (j + 1) * T - P = P := by rw [hP, pow_succ]; ring
  have hpt : ∀ τ ∈ s j, g τ ≤ (X / P) ^ 2 * f τ := by
    intro τ hτ
    have h1 : P / X ≤ 1 + |τ| / X := by
      rw [abs_of_pos (hP0.trans_le hτ.1)]
      have := div_le_div_of_nonneg_right hτ.1 hX.le
      linarith
    refine mul_le_mul_of_nonneg_right ?_ (hf0 τ)
    calc ((1 + |τ| / X) ^ 2)⁻¹ ≤ ((P / X) ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 2)
      _ = (X / P) ^ 2 := by rw [← inv_pow, inv_div]
  calc ∫ τ in s j, g τ ≤ ∫ τ in s j, (X / P) ^ 2 * f τ :=
        setIntegral_mono_on hgi.integrableOn
          ((hf.const_mul _).integrableOn_Icc.mono_set Set.Ico_subset_Icc_self) measurableSet_Ico
          hpt
    _ = (X / P) ^ 2 * ∫ τ in P..(2 ^ (j + 1) * T), f τ := by
        rw [integral_const_mul, integral_Ico_eq_integral_Ioc,
          intervalIntegral.integral_of_le (by linarith)]
    _ ≤ (X / P) ^ 2 * (M * (1 + P / X)) := by
        gcongr
        have h := hM P (2 ^ (j + 1) * T) (by linarith)
        rwa [hlen] at h
    _ ≤ (X / P) ^ 2 * (M * (2 * P / X)) := by
        gcongr
        have h1 : 1 ≤ P / X := (one_le_div hX).2 hXP
        have h2 : 2 * P / X = P / X + P / X := by ring
        linarith
    _ = 4 * M * X / T / 2 / 2 ^ j := by
        rw [hP]
        field_simp
        ring

/-- The two-sided `τ`-tail: `∫_{|τ| > T} (1 + |τ|/X)^{-2} f ≤ 8 M X / T` for `T ≥ X`. The left
tail is the right tail of `τ ↦ f(-τ)`. -/
theorem integral_compl_Icc_mul_le {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ τ, 0 ≤ f τ)
    {F₀ : ℝ} (hfF : ∀ τ, f τ ≤ F₀) {X T M : ℝ} (hX : 0 < X) (hXT : X ≤ T)
    (hM : ∀ a b, a ≤ b → ∫ τ in a..b, f τ ≤ M * (1 + (b - a) / X)) :
    ∫ τ in (Set.Icc (-T) T)ᶜ, ((1 + |τ| / X) ^ 2)⁻¹ * f τ ≤ 8 * M * X / T := by
  have hgi : Integrable fun τ => ((1 + |τ| / X) ^ 2)⁻¹ * f τ := by
    refine ((integrable_inv_one_add_abs_div_sq hX).mul_const F₀).mono'
      ((Continuous.inv₀ (by fun_prop) fun τ => by positivity).mul hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hf0 τ))]
    exact mul_le_mul_of_nonneg_left (hfF τ) (by positivity)
  have hcompl : (Set.Icc (-T) T)ᶜ = Set.Iio (-T) ∪ Set.Ioi T := by
    ext τ
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
      not_and_or, not_le]
  have hdisj : Disjoint (Set.Iio (-T)) (Set.Ioi T) := by
    rw [Set.disjoint_left]
    intro τ h₁ h₂
    rw [Set.mem_Iio] at h₁
    rw [Set.mem_Ioi] at h₂
    linarith [hX.trans_le hXT]
  rw [hcompl, setIntegral_union hdisj measurableSet_Ioi hgi.integrableOn hgi.integrableOn]
  -- reflect the left tail
  have hl : ∫ τ in Set.Iio (-T), ((1 + |τ| / X) ^ 2)⁻¹ * f τ =
      ∫ τ in Set.Ioi T, ((1 + |τ| / X) ^ 2)⁻¹ * f (-τ) := by
    rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi]
    simp only [abs_neg]
  have hM' : ∀ a b, a ≤ b → ∫ τ in a..b, f (-τ) ≤ M * (1 + (b - a) / X) := by
    intro a b hab
    rw [intervalIntegral.integral_comp_neg]
    calc ∫ τ in -b..-a, f τ ≤ M * (1 + (-a - -b) / X) := hM _ _ (by linarith)
      _ = M * (1 + (b - a) / X) := by ring
  rw [hl]
  have h₁ := integral_Ioi_mul_le (f := fun τ => f (-τ)) (hf.comp continuous_neg)
    (fun τ => hf0 _) (fun τ => hfF _) hX hXT hM'
  have h₂ := integral_Ioi_mul_le hf hf0 hfF hX hXT hM
  refine (add_le_add h₁ h₂).trans (le_of_eq ?_)
  ring

/-! ### The two regions -/

/-- For fixed `s`:
`∫ (1 + |τ|/X)^{-2} g(τ) g(τ - s) dτ ≤ (ε E + ε⁻¹ M (1 + 2T/X))/2 + 8 M X / T`. -/
theorem integral_mul_shift_le {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ τ, 0 ≤ g τ) {B₀ : ℝ}
    (hgB : ∀ τ, g τ ≤ B₀) {X T M E ε : ℝ} (hX : 0 < X) (hXT : X ≤ T) (hε : 0 < ε)
    (hE : ∫ τ in (-T)..T, g τ ^ 2 ≤ E)
    (hM : ∀ a b, a ≤ b → ∫ τ in a..b, g τ ^ 2 ≤ M * (1 + (b - a) / X)) (s : ℝ) :
    ∫ τ, ((1 + |τ| / X) ^ 2)⁻¹ * (g τ * g (τ - s)) ≤
      (ε * E + ε⁻¹ * (M * (1 + 2 * T / X))) / 2 + 8 * M * X / T := by
  have hT : 0 ≤ T := hX.le.trans hXT
  have hB₀ : 0 ≤ B₀ := (hg0 0).trans (hgB 0)
  set k : ℝ → ℝ := fun τ => ((1 + |τ| / X) ^ 2)⁻¹ with hk
  have hkc : Continuous k := Continuous.inv₀ (by fun_prop) fun τ => by positivity
  have hk0 : ∀ τ, 0 ≤ k τ := fun τ => by positivity
  have hk1 : ∀ τ, k τ ≤ 1 := fun τ =>
    inv_le_one_of_one_le₀ (one_le_pow₀ (le_add_of_nonneg_right (by positivity)))
  have hki := integrable_inv_one_add_abs_div_sq hX
  -- the shifted function `g(τ - s)` has the same mean values
  set gs : ℝ → ℝ := fun τ => g (τ - s) with hgs
  have hgsc : Continuous gs := hg.comp (continuous_id.sub continuous_const)
  have hMs : ∀ a b, a ≤ b → ∫ τ in a..b, gs τ ^ 2 ≤ M * (1 + (b - a) / X) := by
    intro a b hab
    rw [intervalIntegral.integral_comp_sub_right (fun τ => g τ ^ 2)]
    calc ∫ τ in (a - s)..(b - s), g τ ^ 2 ≤ M * (1 + (b - s - (a - s)) / X) :=
          hM _ _ (by linarith)
      _ = M * (1 + (b - a) / X) := by ring
  -- integrability of everything in sight
  have hdom : ∀ φ : ℝ → ℝ, Continuous φ → (∀ τ, 0 ≤ φ τ) → (∀ τ, φ τ ≤ B₀ ^ 2) →
      Integrable fun τ => k τ * φ τ := by
    intro φ hφ hφ0 hφB
    refine (hki.mul_const (B₀ ^ 2)).mono' (hkc.mul hφ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk0 τ) (hφ0 τ))]
    exact mul_le_mul_of_nonneg_left (hφB τ) (hk0 τ)
  have hsqB : ∀ τ, g τ ^ 2 ≤ B₀ ^ 2 := fun τ => pow_le_pow_left₀ (hg0 τ) (hgB τ) 2
  have hhi : Integrable fun τ => k τ * (g τ * gs τ) :=
    hdom _ (hg.mul hgsc) (fun τ => mul_nonneg (hg0 _) (hg0 _)) fun τ => by
      rw [sq]; exact mul_le_mul (hgB _) (hgB _) (hg0 _) hB₀
  have hi₁ : Integrable fun τ => k τ * g τ ^ 2 :=
    hdom _ (hg.pow 2) (fun τ => sq_nonneg _) hsqB
  have hi₂ : Integrable fun τ => k τ * gs τ ^ 2 :=
    hdom _ (hgsc.pow 2) (fun τ => sq_nonneg _) fun τ => hsqB _
  rw [← integral_add_compl measurableSet_Icc hhi]
  -- on `[-T, T]`: `k ≤ 1` and `2 g g' ≤ ε g² + ε⁻¹ g'²`
  have hmain : ∫ τ in Set.Icc (-T) T, k τ * (g τ * gs τ) ≤
      (ε * E + ε⁻¹ * (M * (1 + 2 * T / X))) / 2 := by
    have hpt : ∀ τ ∈ Set.Icc (-T) T, k τ * (g τ * gs τ) ≤
        ε / 2 * g τ ^ 2 + ε⁻¹ / 2 * gs τ ^ 2 := by
      intro τ _
      have hgg := mul_nonneg (hg0 τ) (hg0 (τ - s))
      have key : ε * g τ ^ 2 + ε⁻¹ * gs τ ^ 2 - 2 * (g τ * gs τ) =
          ε⁻¹ * (ε * g τ - gs τ) ^ 2 := by
        field_simp
        ring
      have := mul_nonneg (inv_nonneg.2 hε.le) (sq_nonneg (ε * g τ - gs τ))
      calc k τ * (g τ * gs τ) ≤ 1 * (g τ * gs τ) := mul_le_mul_of_nonneg_right (hk1 τ) hgg
        _ ≤ ε / 2 * g τ ^ 2 + ε⁻¹ / 2 * gs τ ^ 2 := by linarith
    have hc₁ : Continuous fun τ => g τ ^ 2 := hg.pow 2
    have hc₂ : Continuous fun τ => gs τ ^ 2 := hgsc.pow 2
    calc ∫ τ in Set.Icc (-T) T, k τ * (g τ * gs τ)
        ≤ ∫ τ in Set.Icc (-T) T, (ε / 2 * g τ ^ 2 + ε⁻¹ / 2 * gs τ ^ 2) :=
          setIntegral_mono_on hhi.integrableOn
            ((hc₁.const_mul _).add (hc₂.const_mul _)).integrableOn_Icc measurableSet_Icc hpt
      _ = ε / 2 * (∫ τ in (-T)..T, g τ ^ 2) + ε⁻¹ / 2 * ∫ τ in (-T)..T, gs τ ^ 2 := by
          rw [integral_add (hc₁.const_mul _).integrableOn_Icc (hc₂.const_mul _).integrableOn_Icc,
            integral_const_mul, integral_const_mul, integral_Icc_eq_intervalIntegral _ hT,
            integral_Icc_eq_intervalIntegral _ hT]
      _ ≤ ε / 2 * E + ε⁻¹ / 2 * (M * (1 + (T - -T) / X)) :=
          add_le_add (mul_le_mul_of_nonneg_left hE (by positivity))
            (mul_le_mul_of_nonneg_left (hMs _ _ (by linarith)) (by positivity))
      _ = (ε * E + ε⁻¹ * (M * (1 + 2 * T / X))) / 2 := by ring
  -- on `|τ| > T`: `2 g g' ≤ g² + g'²` and the tail twice
  have htail : ∫ τ in (Set.Icc (-T) T)ᶜ, k τ * (g τ * gs τ) ≤ 8 * M * X / T := by
    have hpt : ∀ τ ∈ (Set.Icc (-T) T)ᶜ, k τ * (g τ * gs τ) ≤
        k τ * g τ ^ 2 / 2 + k τ * gs τ ^ 2 / 2 := by
      intro τ _
      have h := mul_le_mul_of_nonneg_left (two_mul_le_add_sq (g τ) (gs τ)) (hk0 τ)
      linarith
    have h₁ : ∫ τ in (Set.Icc (-T) T)ᶜ, k τ * g τ ^ 2 ≤ 8 * M * X / T :=
      integral_compl_Icc_mul_le (hg.pow 2) (fun τ => sq_nonneg _) hsqB hX hXT hM
    have h₂ : ∫ τ in (Set.Icc (-T) T)ᶜ, k τ * gs τ ^ 2 ≤ 8 * M * X / T :=
      integral_compl_Icc_mul_le (hgsc.pow 2) (fun τ => sq_nonneg _) (fun τ => hsqB _) hX hXT hMs
    calc ∫ τ in (Set.Icc (-T) T)ᶜ, k τ * (g τ * gs τ)
        ≤ ∫ τ in (Set.Icc (-T) T)ᶜ, (k τ * g τ ^ 2 / 2 + k τ * gs τ ^ 2 / 2) :=
          setIntegral_mono_on hhi.integrableOn
            ((hi₁.div_const 2).add (hi₂.div_const 2)).integrableOn measurableSet_Icc.compl hpt
      _ = (∫ τ in (Set.Icc (-T) T)ᶜ, k τ * g τ ^ 2) / 2 +
          (∫ τ in (Set.Icc (-T) T)ᶜ, k τ * gs τ ^ 2) / 2 := by
          rw [integral_add (hi₁.div_const 2).integrableOn (hi₂.div_const 2).integrableOn,
            integral_div, integral_div]
      _ ≤ 8 * M * X / T / 2 + 8 * M * X / T / 2 := by gcongr
      _ = 8 * M * X / T := by ring
  exact add_le_add hmain htail

/-- The arc-term integral: for `g ≥ 0` with energy `E` on `[-T, T]` and mean values
`M (1 + |I|/X)`,
`∫∫ (1 + |τ|/X)^{-2} (1 + |τ + σ|)^{-2} g(τ) g(-σ) ≤ π ((ε E + ε⁻¹ M (1 + 2T/X))/2 + 8MX/T)`,
and the integrand is integrable. -/
theorem integral_kernel_mul_le {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ τ, 0 ≤ g τ)
    {B₀ : ℝ} (hgB : ∀ τ, g τ ≤ B₀) {X T M E ε : ℝ} (hX : 0 < X) (hXT : X ≤ T) (hε : 0 < ε)
    (hE : ∫ τ in (-T)..T, g τ ^ 2 ≤ E)
    (hM : ∀ a b, a ≤ b → ∫ τ in a..b, g τ ^ 2 ≤ M * (1 + (b - a) / X)) :
    Integrable (fun q : ℝ × ℝ =>
        ((1 + |q.1| / X) ^ 2)⁻¹ * ((1 + |q.1 + q.2|) ^ 2)⁻¹ * (g q.1 * g (-q.2))) ∧
      ∫ q : ℝ × ℝ, ((1 + |q.1| / X) ^ 2)⁻¹ * ((1 + |q.1 + q.2|) ^ 2)⁻¹ * (g q.1 * g (-q.2)) ≤
        π * ((ε * E + ε⁻¹ * (M * (1 + 2 * T / X))) / 2 + 8 * M * X / T) := by
  have hT : 0 ≤ T := hX.le.trans hXT
  have hB₀ : 0 ≤ B₀ := (hg0 0).trans (hgB 0)
  have hM0 : 0 ≤ M := by
    have h := hM T T le_rfl
    rw [intervalIntegral.integral_same, sub_self, zero_div, add_zero, mul_one] at h
    exact h
  have hE0 : 0 ≤ E :=
    (intervalIntegral.integral_nonneg (by linarith) fun τ _ => sq_nonneg (g τ)).trans hE
  set k₁ : ℝ → ℝ := fun τ => ((1 + |τ| / X) ^ 2)⁻¹ with hk₁
  set k₂ : ℝ → ℝ := fun u => ((1 + |u|) ^ 2)⁻¹ with hk₂
  have hk₁c : Continuous k₁ := Continuous.inv₀ (by fun_prop) fun τ => by positivity
  have hk₂c : Continuous k₂ := Continuous.inv₀ (by fun_prop) fun u => by positivity
  have hk₁i := integrable_inv_one_add_abs_div_sq hX
  have hk₂i := integrable_inv_one_add_abs_sq
  have hgg : ∀ a b, g a * g b ≤ B₀ ^ 2 := fun a b => by
    rw [sq]; exact mul_le_mul (hgB a) (hgB b) (hg0 b) hB₀
  -- the integrand is dominated by `B₀² k₁(τ) k₂(τ + σ)`, integrable after the shear
  set F : ℝ × ℝ → ℝ := fun q => k₁ q.1 * k₂ (q.1 + q.2) * (g q.1 * g (-q.2)) with hF
  have hFc : Continuous F := by
    refine (hk₁c.comp continuous_fst).mul (hk₂c.comp (continuous_fst.add continuous_snd)) |>.mul
      ((hg.comp continuous_fst).mul (hg.comp (continuous_snd.neg)))
  have hDi : Integrable (fun q : ℝ × ℝ => k₁ q.1 * k₂ (q.1 + q.2)) (volume.prod volume) := by
    have hPc : Continuous fun q : ℝ × ℝ => k₁ q.1 * k₂ q.2 :=
      (hk₁c.comp continuous_fst).mul (hk₂c.comp continuous_snd)
    exact ((measurePreserving_prod_add volume volume).integrable_comp
      hPc.aestronglyMeasurable).2 (hk₁i.mul_prod hk₂i)
  have hFi : Integrable F (volume.prod volume) := by
    refine (hDi.mul_const (B₀ ^ 2)).mono' hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    have h0 : 0 ≤ k₁ q.1 * k₂ (q.1 + q.2) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (mul_nonneg (hg0 _) (hg0 _)))]
    exact mul_le_mul_of_nonneg_left (hgg _ _) h0
  rw [Measure.volume_eq_prod]
  refine ⟨hFi, ?_⟩
  -- substitute `σ = s - τ`, then integrate in `τ` first
  set H : ℝ → ℝ → ℝ := fun τ s => k₂ s * (k₁ τ * (g τ * g (τ - s))) with hH
  have hinner : ∀ τ, ∫ σ, F (τ, σ) = ∫ s, H τ s := fun τ => by
    rw [← integral_sub_right_eq_self (fun σ => F (τ, σ)) τ]
    congr 1 with s
    simp only [hF, hH, add_sub_cancel, neg_sub]
    ring
  have hHi : Integrable (Function.uncurry H) (volume.prod volume) := by
    have hHc : Continuous (Function.uncurry H) :=
      (hk₂c.comp continuous_snd).mul ((hk₁c.comp continuous_fst).mul
        ((hg.comp continuous_fst).mul (hg.comp (continuous_fst.sub continuous_snd))))
    refine ((hk₁i.mul_prod hk₂i).mul_const (B₀ ^ 2)).mono' hHc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    have h0 : 0 ≤ k₁ q.1 * k₂ q.2 := by positivity
    simp only [Function.uncurry, hH]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [hg0 q.1, hg0 (q.1 - q.2)])]
    calc k₂ q.2 * (k₁ q.1 * (g q.1 * g (q.1 - q.2))) =
        (k₁ q.1 * k₂ q.2) * (g q.1 * g (q.1 - q.2)) := by ring
      _ ≤ (k₁ q.1 * k₂ q.2) * B₀ ^ 2 := mul_le_mul_of_nonneg_left (hgg _ _) h0
  rw [integral_prod F hFi]
  simp only [hinner]
  rw [integral_integral_swap hHi]
  -- the inner integral is bounded uniformly in `s`
  set Bnd : ℝ := (ε * E + ε⁻¹ * (M * (1 + 2 * T / X))) / 2 + 8 * M * X / T with hBnd
  have hBnd0 : 0 ≤ Bnd := by positivity
  have hJ : ∀ s, ∫ τ, H τ s = k₂ s * ∫ τ, k₁ τ * (g τ * g (τ - s)) := fun s =>
    integral_const_mul _ _
  simp only [hJ]
  calc ∫ s, k₂ s * ∫ τ, k₁ τ * (g τ * g (τ - s)) ≤ ∫ s, k₂ s * Bnd := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => ?_)
          (hk₂i.mul_const Bnd) (Filter.Eventually.of_forall fun s => ?_)
        · exact mul_nonneg (by positivity) (integral_nonneg fun τ => by
            positivity [hg0 τ, hg0 (τ - s)])
        · exact mul_le_mul_of_nonneg_left
            (integral_mul_shift_le hg hg0 hgB hX hXT hε hE hM s) (by positivity)
    _ = (∫ s, k₂ s) * Bnd := integral_mul_const _ _
    _ ≤ π * Bnd := mul_le_mul_of_nonneg_right integral_inv_one_add_abs_sq_le hBnd0

end Erdos408.OneSided
