module

public import Erdos408.TwoSided.Endpoint.Tuple.Box

/-!
# The ordinary and exceptional times of one box (tuple part)

S15–S18 of `blueprint/two_sided_correlation.md` §§6.3–6.6 for one box (PD (6.35)–(6.38)). On
an interval of times `L^E ≤ |τ| ≤ 2T₀ - 2`:

* where `|P_s(τ)| ≤ L^{-A_s}`, E7 with the mean value of `Q` (`boxMeanValue_le'`);
* elsewhere `τ` lies in a unit interval `[j, j + 1)` of the exceptional set `𝒥` of S16
  (rescaled by `min(1, v₋)/V`), with `#𝒥 ≤ exp(L^{0.95})`. There
  `|G|² ≤ (2/v₋)² (PNR/Y)² |N⁻¹ P_l|² |R⁻¹ R|² ≤ (2/v₋)² · 4 (4κ' L^{-A'})² s_j` by E9, and
  `∑_j s_j ≤ 9(1 + |κ'|) L^{2C_U + 4}` by E8.
-/

@[expose] public section

namespace Erdos408.TwoSided.TupleHigh

open Filter Finset MeasureTheory

/-- Eventually `exp(K (L^{0.36} + L^{0.73} log L)) exp(-L^{0.95}) ≤ 1`. -/
theorem eventually_exp_card_exceptional_le (K : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (K * (Real.log x ^ (0.36 : ℝ) +
        Real.log x ^ (0.73 : ℝ) * Real.log (Real.log x))) *
          Real.exp (-Real.log x ^ (0.95 : ℝ)) ≤ 1 := by
  filter_upwards [Real.tendsto_log_atTop.eventually
      (TypeII.eventually_mul_log_rpow_le (2 * |K|) 1 _ (by norm_num : (0 : ℝ) < 0.22)),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with x h₁ hL
  set L := Real.log x
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) hL
  have hL0 : 0 < L := by linarith
  have hT1 : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hL
  rw [Real.rpow_one] at h₁
  have h36 : L ^ (0.36 : ℝ) ≤ L ^ (0.73 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have h73 : 0 ≤ L ^ (0.73 : ℝ) := by positivity
  have hsum : L ^ (0.36 : ℝ) + L ^ (0.73 : ℝ) * Real.log L ≤ 2 * L ^ (0.73 : ℝ) * Real.log L := by
    nlinarith
  have h95 : L ^ (0.73 : ℝ) * L ^ (0.22 : ℝ) = L ^ (0.95 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hK : K * (L ^ (0.36 : ℝ) + L ^ (0.73 : ℝ) * Real.log L) ≤ L ^ (0.95 : ℝ) := by
    have hpos : 0 ≤ L ^ (0.36 : ℝ) + L ^ (0.73 : ℝ) * Real.log L := by positivity
    calc K * (L ^ (0.36 : ℝ) + L ^ (0.73 : ℝ) * Real.log L)
        ≤ |K| * (L ^ (0.36 : ℝ) + L ^ (0.73 : ℝ) * Real.log L) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) hpos
      _ ≤ |K| * (2 * L ^ (0.73 : ℝ) * Real.log L) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg K)
      _ = L ^ (0.73 : ℝ) * (2 * |K| * Real.log L) := by ring
      _ ≤ L ^ (0.73 : ℝ) * L ^ (0.22 : ℝ) := mul_le_mul_of_nonneg_left h₁ h73
      _ = L ^ (0.95 : ℝ) := h95
  rw [← Real.exp_add, ← Real.exp_zero]
  exact Real.exp_le_exp.2 (by linarith)

/-- `L^{-a}` squared is `L^{-2a}`. -/
theorem rpow_neg_sq {L a : ℝ} (hL : 0 ≤ L) : (L ^ (-a)) ^ 2 = L ^ (-(2 * a)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
  ring_nf

/-- `⌊t⌋ ∈ [-⌈T⌉ - 1, ⌈T⌉]` for `|t| ≤ T`. -/
theorem floor_mem_Icc_of_abs_le {t T : ℝ} (h : |t| ≤ T) : ⌊t⌋ ∈ Icc (-⌈T⌉ - 1) ⌈T⌉ := by
  rw [mem_Icc]
  have h₁ := (abs_le.1 h).1
  have h₂ := (abs_le.1 h).2
  constructor
  · have h₃ : (-(⌈T⌉ : ℝ)) ≤ t := by linarith [Int.le_ceil T]
    have h₄ : t < ⌊t⌋ + 1 := Int.lt_floor_add_one t
    have : ((-⌈T⌉ - 1 : ℤ) : ℝ) < ⌊t⌋ + 1 := by push_cast; linarith
    have : (-⌈T⌉ - 1 : ℤ) < ⌊t⌋ + 1 := by exact_mod_cast this
    omega
  · exact (Int.floor_le_floor h₂).trans (Int.floor_le_ceil T)

/-- `L^{-(A + 1)} < m |z|` if `L^{-A} < |z|` and `m L ≥ 1`, `m > 0`. -/
theorem rpow_neg_add_one_lt {L A m z : ℝ} (hL : 0 < L) (hm : 0 < m) (hmL : 1 ≤ m * L)
    (hz : L ^ (-A) < z) : L ^ (-(A + 1)) < m * z := by
  have hsplit : L ^ (-(A + 1)) = L ^ (-A) / L := by
    rw [neg_add, Real.rpow_add hL, Real.rpow_neg_one, div_eq_mul_inv]
  rw [hsplit, div_lt_iff₀ hL]
  have hθ0 : 0 < L ^ (-A) := by positivity
  calc L ^ (-A) ≤ L ^ (-A) * (m * L) := le_mul_of_one_le_right hθ0.le hmL
    _ < z * (m * L) := mul_lt_mul_of_pos_right hz (by positivity)
    _ = m * z * L := by ring

/-- A nonnegative continuous `f` on `(τ₁, τ₂] \ S`, covered by the unit intervals
`[j, j + 1)`, `j ∈ 𝒥`, on each of which `f ≤ b_j`: `∫ f ≤ ∑_{j ∈ 𝒥} b_j`. -/
theorem integral_sdiff_le_of_cover {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    {τ₁ τ₂ : ℝ} {S : Set ℝ} (𝒥 : Finset ℤ) {b : ℤ → ℝ} (hb0 : ∀ j ∈ 𝒥, 0 ≤ b j)
    (hcover : Set.Ioc τ₁ τ₂ \ S ⊆ ⋃ j ∈ 𝒥, Set.Ioc τ₁ τ₂ ∩ Set.Ico (j : ℝ) (j + 1))
    (hpt : ∀ j ∈ 𝒥, ∀ t ∈ Set.Ioc τ₁ τ₂ ∩ Set.Ico (j : ℝ) (j + 1), f t ≤ b j) :
    ∫ t in Set.Ioc τ₁ τ₂ \ S, f t ≤ ∑ j ∈ 𝒥, b j := by
  have hint : IntegrableOn f (Set.Ioc τ₁ τ₂) :=
    hf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hmeasA : ∀ j ∈ 𝒥, MeasurableSet (Set.Ioc τ₁ τ₂ ∩ Set.Ico (j : ℝ) (j + 1)) :=
    fun j _ => measurableSet_Ioc.inter measurableSet_Ico
  have hdisj : Set.Pairwise (↑𝒥 : Set ℤ)
      (Function.onFun Disjoint fun j : ℤ => Set.Ioc τ₁ τ₂ ∩ Set.Ico (j : ℝ) (j + 1)) := by
    intro j _ j' _ hjj'
    refine Set.disjoint_left.2 fun t ht ht' => hjj' ?_
    have h₁ : ⌊t⌋ = j := Int.floor_eq_iff.2 ⟨ht.2.1, ht.2.2⟩
    have h₂ : ⌊t⌋ = j' := Int.floor_eq_iff.2 ⟨ht'.2.1, ht'.2.2⟩
    rw [← h₁, ← h₂]
  have hunion : ⋃ j ∈ 𝒥, Set.Ioc τ₁ τ₂ ∩ Set.Ico (j : ℝ) (j + 1) ⊆ Set.Ioc τ₁ τ₂ :=
    Set.iUnion₂_subset fun j _ => Set.inter_subset_left
  have hpiece : ∀ j ∈ 𝒥, ∫ t in Set.Ioc τ₁ τ₂ ∩ Set.Ico (j : ℝ) (j + 1), f t ≤ b j := by
    intro j hj
    calc ∫ t in Set.Ioc τ₁ τ₂ ∩ Set.Ico (j : ℝ) (j + 1), f t
        ≤ ∫ _t in Set.Ioc τ₁ τ₂ ∩ Set.Ico (j : ℝ) (j + 1), b j :=
          setIntegral_mono_on (hint.mono_set Set.inter_subset_left)
            (integrableOn_const (measure_ne_top_of_subset Set.inter_subset_right
              measure_Ico_lt_top.ne)) (hmeasA j hj) (hpt j hj)
      _ = volume.real (Set.Ioc τ₁ τ₂ ∩ Set.Ico (j : ℝ) (j + 1)) * b j := by
          rw [setIntegral_const, smul_eq_mul]
      _ ≤ 1 * b j := by
          refine mul_le_mul_of_nonneg_right ?_ (hb0 j hj)
          calc volume.real (Set.Ioc τ₁ τ₂ ∩ Set.Ico (j : ℝ) (j + 1))
              ≤ volume.real (Set.Ico (j : ℝ) (j + 1)) :=
                measureReal_mono Set.inter_subset_right measure_Ico_lt_top.ne
            _ = 1 := by rw [Real.volume_real_Ico_of_le (by linarith)]; ring
      _ = b j := one_mul _
  calc ∫ t in Set.Ioc τ₁ τ₂ \ S, f t
      ≤ ∫ t in ⋃ j ∈ 𝒥, Set.Ioc τ₁ τ₂ ∩ Set.Ico (j : ℝ) (j + 1), f t :=
        setIntegral_mono_set (hint.mono_set hunion) (Filter.Eventually.of_forall hf0)
          (Filter.Eventually.of_forall hcover)
    _ = ∑ j ∈ 𝒥, ∫ t in Set.Ioc τ₁ τ₂ ∩ Set.Ico (j : ℝ) (j + 1), f t :=
        integral_biUnion_finset 𝒥 hmeasA hdisj fun j _ => hint.mono_set Set.inter_subset_left
    _ ≤ ∑ j ∈ 𝒥, b j := sum_le_sum hpiece

/-- `P ≥ 1` for `P ≥ e^{L^{0.27}}/2` and `L ≥ 1`. -/
theorem one_le_of_exp_div_two_le {x P : ℝ} (hL : 1 ≤ Real.log x)
    (hP : Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ P) : 1 ≤ P := by
  have h := Real.add_one_le_exp (Real.log x ^ (0.27 : ℝ))
  have : 1 ≤ Real.log x ^ (0.27 : ℝ) := Real.one_le_rpow hL (by norm_num)
  linarith

/-- **The exceptional times, pointwise.** For the data of one box, under AP1, at a time
`L^E ≤ |t| ≤ x³` with `|R⁻¹ R(t)|² ≤ s`:
`|G(t)|² ≤ (2/v₋)² · 4 (4κ' L^{-A'})² s`, by `|P_s| ≤ 2/v₋`, E9 and `PNR ≤ 2Y`. -/
theorem norm_boxPoly_sq_le_of_twist {x Cm CU vlo Y P N R V lo hi : ℝ} {sP uR : Finset ℕ}
    {k : ℕ} {c : ℕ → ℂ} (hvlo : 0 < vlo) (hd : BoxData x Cm CU vlo Y P N R V lo hi sP uR k c)
    (hx : 0 < x) (hL : 1 ≤ Real.log x) (χ : DirichletCharacter ℂ k) {A' E κ' : ℝ}
    (hAP1 : PrimeTwistBound x A' E Cm κ') {t : ℝ} (htE : Real.log x ^ E ≤ |t|)
    (htx : |t| ≤ x ^ 3) {s : ℝ}
    (hR : ‖(R : ℂ)⁻¹ * ∑ u ∈ uR, c u * (u : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤ s) :
    ‖boxPoly Y P V sP ((Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) uR χ c t‖ ^ 2 ≤
      (2 / vlo) ^ 2 * 4 * (4 * κ' * Real.log x ^ (-A')) ^ 2 * s := by
  have hP1 : 1 ≤ P := one_le_of_exp_div_two_le hL hd.hP₁
  have hP0 : 0 < P := by linarith
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hd.hY₁
  have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos _) hd.hN₁
  have hR0 : 0 < R := lt_of_lt_of_le (Real.exp_pos _) hd.hR₁
  set B := 4 * κ' * Real.log x ^ (-A')
  set Pl := ∑ p ∈ (Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime, χ p * (p : ℂ) ^ ((t : ℂ) * Complex.I)
  set Rr := ∑ u ∈ uR, c u * (u : ℂ) ^ ((t : ℂ) * Complex.I)
  -- E9 for `P_l`
  have hPl : ‖Pl‖ ≤ N * B := by
    have h := norm_primeTwistPoly_le hAP1 hd.hN₁ hd.hN₂ hd.hlo hd.hhi hd.hk₁ hd.hk₂ χ htE htx
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hN0.le] at h
    have : ‖Pl‖ = N * (N⁻¹ * ‖Pl‖) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h hN0.le
  have hB0 : 0 ≤ B := (mul_nonneg_iff_of_pos_left hN0).1 ((norm_nonneg _).trans hPl)
  have hs0 : 0 ≤ s := le_trans (sq_nonneg _) hR
  -- E8's bound for `R`
  have hR' : ‖Rr‖ ^ 2 ≤ R ^ 2 * s := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR0.le, mul_pow] at hR
    have : ‖Rr‖ ^ 2 = R ^ 2 * ((R⁻¹) ^ 2 * ‖Rr‖ ^ 2) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hR (by positivity)
  have hPs := norm_smallPoly_le hP1 hvlo hd.hV hd.hsP t
  have hPNRY : P / Y * N * R ≤ 2 := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hY0]
    linarith [hd.hPNR]
  have hPNRY0 : 0 ≤ P / Y * N * R := by positivity
  have hG : ‖boxPoly Y P V sP ((Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) uR χ c t‖ ^ 2 =
      ‖∑ p ∈ sP, (((P * V)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 *
        ((P / Y) ^ 2 * (‖Pl‖ ^ 2 * ‖Rr‖ ^ 2)) := by
    rw [boxPoly, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    ring
  have h₁ : ‖∑ p ∈ sP, (((P * V)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      (2 / vlo) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hPs 2
  have h₂ : ‖Pl‖ ^ 2 ≤ (N * B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hPl 2
  have h₃ : ‖Pl‖ ^ 2 * ‖Rr‖ ^ 2 ≤ (N * B) ^ 2 * (R ^ 2 * s) :=
    mul_le_mul h₂ hR' (by positivity) (by positivity)
  have h₄ : (P / Y) ^ 2 * ((N * B) ^ 2 * (R ^ 2 * s)) = (P / Y * N * R) ^ 2 * (B ^ 2 * s) := by
    ring
  have h₅ : (P / Y * N * R) ^ 2 ≤ 4 := by nlinarith
  rw [hG]
  calc ‖∑ p ∈ sP, (((P * V)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 *
        ((P / Y) ^ 2 * (‖Pl‖ ^ 2 * ‖Rr‖ ^ 2))
      ≤ (2 / vlo) ^ 2 * ((P / Y * N * R) ^ 2 * (B ^ 2 * s)) := by
        rw [← h₄]
        exact mul_le_mul h₁ (mul_le_mul_of_nonneg_left h₃ (by positivity)) (by positivity)
          (by positivity)
    _ ≤ (2 / vlo) ^ 2 * (4 * (B ^ 2 * s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h₅ (by positivity))
          (by positivity)
    _ = (2 / vlo) ^ 2 * 4 * B ^ 2 * s := by ring

/-- **The exceptional times.** For the data of one box, under AP1, on a range of times with
`L^E ≤ |τ|`, `|τ| + 2 ≤ 2T₀`: if every time of `(τ₁, τ₂]` with `|P_s| > θ` lies in `[j, j + 1)`
for some `j ∈ 𝒥`, and `s_j` bound `|R⁻¹ R|²` on `[j, j + 1]` with
`∑ s_j ≤ 9(1 + |κ'|) L^{2C_U + 4}`, then the mean square of `G` over these times is at most
`(2/v₋)² · 4 (4κ' L^{-A'})² · 9(1 + |κ'|) L^{2C_U + 4}`. -/
theorem integral_exceptional_le {x Cm CU vlo Y P N R V lo hi : ℝ} {sP uR : Finset ℕ} {k : ℕ}
    {c : ℕ → ℂ} (hvlo : 0 < vlo) (hd : BoxData x Cm CU vlo Y P N R V lo hi sP uR k c)
    (hx : 0 < x) (hL : 1 ≤ Real.log x) (χ : DirichletCharacter ℂ k) {A' E κ' : ℝ}
    (hAP1 : PrimeTwistBound x A' E Cm κ') {τ₁ τ₂ : ℝ}
    (hrange : ∀ τ ∈ Set.Icc τ₁ τ₂, Real.log x ^ E ≤ |τ| ∧ |τ| ≤ x ^ 3) {θ : ℝ}
    (𝒥 : Finset ℤ)
    (h𝒥 : ∀ t ∈ Set.Ioc τ₁ τ₂, θ < ‖∑ p ∈ sP, (((P * V)⁻¹ : ℝ) : ℂ) *
      (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ → ⌊t⌋ ∈ 𝒥)
    (s : ℤ → ℝ) (hs₁ : ∀ j ∈ 𝒥, ∀ t ∈ Set.Icc (j : ℝ) (j + 1),
      ‖(R : ℂ)⁻¹ * ∑ u ∈ uR, c u * (u : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤ s j)
    (hs₂ : ∑ j ∈ 𝒥, s j ≤ 9 * (1 + |κ'|) * Real.log x ^ (2 * CU + 4)) :
    ∫ t in Set.Ioc τ₁ τ₂ \ {t | ‖∑ p ∈ sP, (((P * V)⁻¹ : ℝ) : ℂ) *
        (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ θ},
      ‖boxPoly Y P V sP ((Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) uR χ c t‖ ^ 2 ≤
      (2 / vlo) ^ 2 * 4 * (4 * κ' * Real.log x ^ (-A')) ^ 2 *
        (9 * (1 + |κ'|) * Real.log x ^ (2 * CU + 4)) := by
  have hs0 : ∀ j ∈ 𝒥, 0 ≤ s j := fun j hj =>
    le_trans (sq_nonneg _) (hs₁ j hj j ⟨le_rfl, by linarith⟩)
  have hC0 : 0 ≤ (2 / vlo) ^ 2 * 4 * (4 * κ' * Real.log x ^ (-A')) ^ 2 := by positivity
  have hcont := (continuous_boxPoly (Y := Y) (P := P) (V := V)
    (spN := (Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) (fun p hp => (hd.hsP p hp).1.pos)
    (fun p hp => (mem_filter.1 hp).2.pos)
    (fun u hu => by have := hd.huR hu; rw [mem_Ioc] at this; omega) χ c).norm.pow 2
  refine (integral_sdiff_le_of_cover hcont (fun t => pow_nonneg (norm_nonneg _) 2) 𝒥
    (fun j hj => mul_nonneg hC0 (hs0 j hj)) ?_ ?_).trans ?_
  · intro t ht
    obtain ⟨htI, htθ⟩ := ht
    simp only [Set.mem_ofPred_eq, not_le] at htθ
    exact Set.mem_biUnion (x := ⌊t⌋) (h𝒥 t htI htθ)
      ⟨htI, Int.floor_le t, Int.lt_floor_add_one t⟩
  · intro j hj t ht
    obtain ⟨htE, htx⟩ := hrange t (Set.Ioc_subset_Icc_self ht.1)
    exact norm_boxPoly_sq_le_of_twist hvlo hd hx hL χ hAP1 htE htx
      (hs₁ j hj t ⟨ht.2.1, ht.2.2.le⟩)
  · rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left hs₂ hC0

/-- `P⁻¹ ∑_{p ∈ s} (m/V) p^{it} = m P_s(t)`. -/
theorem smallPoly_rescale (P V m : ℝ) (hP : P ≠ 0) (sP : Finset ℕ) (t : ℝ) :
    (P : ℂ)⁻¹ * ∑ p ∈ sP, ((m / V : ℝ) : ℂ) * (p : ℂ) ^ ((t : ℂ) * Complex.I) =
      (m : ℂ) * ∑ p ∈ sP, (((P * V)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ ((t : ℂ) * Complex.I) := by
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  have : (P : ℂ) ≠ 0 := by exact_mod_cast hP
  push_cast
  field_simp

/-- **S15–S18 for one box.** Eventually, for the data of one box, under AP1 and AP2, on an
interval of times with `L^E ≤ |τ|` and `|τ| + 2 ≤ 2T₀`: the mean square of `G` is at most
`L^{-2A_s} L^{2C_U + 5} + (2/v₋)² · 4 (4κ' L^{-A'})² · 9(1 + |κ'|) L^{2C_U + 4}`. -/
theorem eventually_integral_boxPoly_le_of_twist (Cm CU vlo As : ℝ) (hvlo : 0 < vlo)
    (hCm : 0 ≤ Cm) (hAs : 0 < As) :
    ∀ᶠ x : ℝ in atTop, ∀ (Y P N R V lo hi : ℝ) (sP uR : Finset ℕ) (k : ℕ)
      (χ : DirichletCharacter ℂ k) (c : ℕ → ℂ),
      BoxData x Cm CU vlo Y P N R V lo hi sP uR k c →
      ∀ A' E κ' : ℝ, PrimeTwistBound x A' E Cm κ' → IntegerKernelBound x Cm κ' →
      ∀ τ₁ τ₂ : ℝ, τ₁ ≤ τ₂ →
        (∀ τ ∈ Set.Icc τ₁ τ₂, Real.log x ^ E ≤ |τ| ∧
          |τ| + 2 ≤ 2 * (x * Real.log x ^ (Cm + 2))) →
        ∫ τ in τ₁..τ₂, ‖boxPoly Y P V sP ((Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) uR χ c τ‖ ^ 2 ≤
          Real.log x ^ (-(2 * As)) * Real.log x ^ (2 * CU + 5) +
            (2 / vlo) ^ 2 * 4 * (4 * κ' * Real.log x ^ (-A')) ^ 2 *
              (9 * (1 + |κ'|) * Real.log x ^ (2 * CU + 4)) := by
  obtain ⟨KJ, -, hS⟩ := exists_card_exceptional_le (As + 1) (by linarith)
  filter_upwards [hS, eventually_sum_sup_normSq_le Cm CU hCm,
    eventually_exp_card_exceptional_le KJ, eventually_boxScales Cm,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 / min 1 vlo)] with x hS hE8 hJ hs hLm
  intro Y P N R V lo hi sP uR k χ c hd A' E κ' hAP1 hAP2 τ₁ τ₂ h₁₂ hrange
  classical
  obtain ⟨hT₀1, -, hT₀x, hYx, -⟩ := boxScales_of hCm hd hs
  have hL : 160 ≤ Real.log x := hs.1
  have hL0 : 0 < Real.log x := by linarith
  have hx0 : 0 < x := by linarith [hs.2.1]
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hd.hP₁
  have hV0 : 0 < V := lt_of_lt_of_le hvlo hd.hV
  have hrange' : ∀ τ ∈ Set.Icc τ₁ τ₂, Real.log x ^ E ≤ |τ| ∧ |τ| ≤ x ^ 3 := fun τ hτ =>
    ⟨(hrange τ hτ).1, by linarith [(hrange τ hτ).2]⟩
  have hlen : τ₂ - τ₁ ≤ 4 * (x * Real.log x ^ (Cm + 2)) := by
    have h₁ := (hrange τ₁ ⟨le_rfl, h₁₂⟩).2
    have h₂ := (hrange τ₂ ⟨h₁₂, le_rfl⟩).2
    have := le_abs_self τ₂
    have := neg_abs_le τ₁
    linarith
  set Ps : ℝ → ℂ := fun τ => ∑ p ∈ sP, (((P * V)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ ((τ : ℂ) * Complex.I)
    with hPs
  have hint : IntegrableOn (fun τ =>
      ‖boxPoly Y P V sP ((Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) uR χ c τ‖ ^ 2) (Set.Ioc τ₁ τ₂) :=
    ((continuous_boxPoly (fun p hp => (hd.hsP p hp).1.pos) (fun p hp => (mem_filter.1 hp).2.pos)
      (fun u hu => by have := hd.huR hu; rw [mem_Ioc] at this; omega) χ c).norm.pow
        2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hPsm : Measurable fun τ => ‖Ps τ‖ := (measurable_dirichletSum sP _).norm
  rw [intervalIntegral.integral_of_le h₁₂, ← integral_inter_add_sdiff
    (measurableSet_le hPsm measurable_const) hint (t := {t | ‖Ps t‖ ≤ Real.log x ^ (-As)})]
  refine add_le_add ?_ ?_
  · -- the ordinary times: E7
    have h := setIntegral_ordinary_le sP (fun _ => (((P * V)⁻¹ : ℝ) : ℂ)) (⌊hi⌋₊ * ⌊2 * R⌋₊)
      (boxCoeff Y P ((Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) uR χ c) h₁₂
      (θ := Real.log x ^ (-As))
    simp only [← boxPoly_eq hd χ] at h
    refine h.trans ?_
    rw [rpow_neg_sq hL0.le]
    exact mul_le_mul_of_nonneg_left (boxMeanValue_le' hCm hd hs χ h₁₂ hlen) (by positivity)
  · -- the exceptional set `𝒥` of S16, with `coeff = min(1, v₋)/V`
    set m := min 1 vlo with hm
    have hm0 : 0 < m := lt_min one_pos hvlo
    have hmV : m ≤ V := (min_le_right _ _).trans hd.hV
    have hmL : 1 ≤ m * Real.log x := by
      rw [div_le_iff₀ hm0] at hLm
      linarith
    set Tmax := 2 * (x * Real.log x ^ (Cm + 2)) - 2 with hTmax
    have hY₁ : x ^ (1 / 2 : ℝ) ≤ Y := by
      have : x ^ (1 / 2 : ℝ) ≤ x := Real.rpow_le_self_of_one_le (by linarith [hs.2.1])
        (by norm_num)
      have : x ≤ x * Real.exp (Real.log x ^ (0.38 : ℝ)) :=
        le_mul_of_one_le_right hx0.le (Real.one_le_exp (by positivity))
      linarith [hd.hY₁]
    have hTY : Tmax ≤ Y := by
      have h4 := (boxScales_of hCm hd hs).2.1
      have hP1 : 1 ≤ P := one_le_of_exp_div_two_le (by linarith) hd.hP₁
      have : x * Real.log x ^ (Cm + 2) ≤ x * Real.log x ^ (Cm + 2) * P :=
        le_mul_of_one_le_right (by linarith) hP1
      linarith
    have hcardJ := hS Y P Tmax sP (fun _ => ((m / V : ℝ) : ℂ)) hY₁ hYx (by linarith) hTY
      hd.hP₁ hd.hP₂ (fun p hp => ⟨(hd.hsP p hp).1, (hd.hsP p hp).2.1.le, (hd.hsP p hp).2.2⟩)
      (fun p _ => by
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        exact (div_le_one hV0).2 hmV)
    set 𝒥 := (Icc (-⌈Tmax⌉ - 1) ⌈Tmax⌉).filter fun j : ℤ =>
      ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ j + 1 ∧ |t| ≤ Tmax ∧
        Real.log x ^ (-(As + 1)) <
          ‖(P : ℂ)⁻¹ * ∑ p ∈ sP, ((m / V : ℝ) : ℂ) * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖
      with h𝒥
    have h𝒥card : (#𝒥 : ℝ) * Real.exp (-Real.log x ^ (0.95 : ℝ)) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right hcardJ (Real.exp_pos _).le) hJ
    have h𝒥T : ∀ j ∈ 𝒥, |(j : ℝ)| ≤ 2 * (x * Real.log x ^ (Cm + 2)) := by
      intro j hj
      have h := (mem_Icc.1 (mem_filter.1 hj).1)
      have hc₁ : (⌈Tmax⌉ : ℝ) < Tmax + 1 := Int.ceil_lt_add_one Tmax
      have h₁ : ((-⌈Tmax⌉ - 1 : ℤ) : ℝ) ≤ j := by exact_mod_cast h.1
      have h₂ : (j : ℝ) ≤ ⌈Tmax⌉ := by exact_mod_cast h.2
      push_cast at h₁
      rw [abs_le]
      constructor <;> linarith
    -- E8 for the coefficients of `R`
    obtain ⟨s, hs₁, hs₂⟩ := hE8 κ' hAP2 R (fun u => if u ∈ uR then c u else 0) 𝒥 hd.hR₁
      hd.hR₂ (fun u => by
        by_cases hu : u ∈ uR
        · simp only [hu, ite_true]
          exact hd.hc u hu
        · simp only [hu, ite_false, norm_zero]
          positivity) h𝒥card h𝒥T
    have hRr : ∀ t : ℝ, ∑ u ∈ Ioc ⌊R⌋₊ ⌊2 * R⌋₊,
        (if u ∈ uR then c u else 0) * (u : ℂ) ^ ((t : ℂ) * Complex.I) =
          ∑ u ∈ uR, c u * (u : ℂ) ^ ((t : ℂ) * Complex.I) := by
      intro t
      simp only [ite_mul, zero_mul]
      rw [sum_ite_mem, inter_eq_right.2 hd.huR]
    refine integral_exceptional_le hvlo hd hx0 (by linarith) χ hAP1 hrange' 𝒥 ?_ s
      (fun j hj t ht => by rw [← hRr t]; exact hs₁ j hj t ht) hs₂
    intro t ht htθ
    obtain ⟨-, htT⟩ := hrange t (Set.Ioc_subset_Icc_self ht)
    have htT' : |t| ≤ Tmax := by linarith
    rw [h𝒥, mem_filter]
    refine ⟨floor_mem_Icc_of_abs_le htT', t, Int.floor_le t, (Int.lt_floor_add_one t).le, htT',
      ?_⟩
    rw [smallPoly_rescale P V m hP0.ne' sP t, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hm0.le]
    exact rpow_neg_add_one_lt hL0 hm0 hmL htθ

end Erdos408.TwoSided.TupleHigh
