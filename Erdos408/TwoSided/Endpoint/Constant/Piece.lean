import Erdos408.TwoSided.Endpoint.Constant.Glue

/-!
# One box of the constant part

The time integral of one box `A(t) (B₀(t) + B₁(t))` of S19
(`blueprint/two_sided_correlation.md` §6.6, E10): `A` is the small-prime polynomial, `B₀` the
model part and `B₁` the model error of the constant residual. On the ordinary times
`|A| ≤ θ` the bound is the hypothesis `hord` (E7); elsewhere `|A| ≤ A_max`, the model error
is bounded in mean square (E10.1), and the model part pointwise,
`|B₀(t)| ≤ Λ (24/|t| + ε)` (E10.2): integrated as `t^{-2}` on the medium range `|t| ≤ X`
(E10.3), and on the high range only over the exceptional unit intervals `𝒥` (E10.4).
-/

namespace Erdos408.TwoSided.ConstHigh

open MeasureTheory

/-- **One box of E10.** For `a ≤ b` with `|t| ≥ c > 0` on `[a, b]`, continuous `A, B₀, B₁` with
`|A| ≤ A_max` and `|B₀(t)| ≤ Λ (24/|t| + ε)` on `[a, b]`, if the ordinary part is at most `Ord`,
the times `|t| > X` with `|A(t)| > θ` lie in the unit intervals `[j, j + 1]`, `j ∈ 𝒥`, and
`∫_a^b |B₁|² ≤ M_E`, then
`∫_a^b |A (B₀ + B₁)|² ≤ Ord + 2 A_max² (Λ² (2304/c + 4ε²X) + #𝒥 (Λ (24/X + ε))² + M_E)`. -/
theorem integral_piece_le {a b c θ X Λ ε Amax Ord ME : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hca : ∀ t ∈ Set.Icc a b, c ≤ |t|) (hX : 0 < X) (hΛ : 0 ≤ Λ)
    {A B₀ B₁ : ℝ → ℂ} (hA : Continuous A) (hB₀ : Continuous B₀) (hB₁ : Continuous B₁)
    (hAmax : ∀ t, ‖A t‖ ≤ Amax) (hB₀pt : ∀ t ∈ Set.Icc a b, ‖B₀ t‖ ≤ Λ * (24 / |t| + ε))
    (hord : ∫ t in {t ∈ Set.Ioc a b | ‖A t‖ ≤ θ}, ‖A t * (B₀ t + B₁ t)‖ ^ 2 ≤ Ord)
    (𝒥 : Finset ℤ)
    (hbad : ∀ t ∈ Set.Ioc a b, θ < ‖A t‖ → X < |t| → ∃ j ∈ 𝒥, (j : ℝ) ≤ t ∧ t ≤ j + 1)
    (hME : ∫ t in a..b, ‖B₁ t‖ ^ 2 ≤ ME) :
    ∫ t in a..b, ‖A t * (B₀ t + B₁ t)‖ ^ 2 ≤
      Ord + 2 * Amax ^ 2 * (Λ ^ 2 * (2304 / c + 4 * ε ^ 2 * X) +
        𝒥.card * (Λ * (24 / X + ε)) ^ 2 + ME) := by
  set f : ℝ → ℝ := fun t => ‖A t * (B₀ t + B₁ t)‖ ^ 2 with hfdef
  set O : Set ℝ := {t | ‖A t‖ ≤ θ} with hOdef
  set Ms : Set ℝ := {t | |t| ≤ X} with hMsdef
  set BH : Set ℝ := {t | θ < ‖A t‖} ∩ {t | X < |t|} with hBHdef
  set G : ℝ := (Λ * (24 / X + ε)) ^ 2 with hGdef
  have hfc : Continuous f := (hA.mul (hB₀.add hB₁)).norm.pow 2
  have hOm : MeasurableSet O := measurableSet_le hA.norm.measurable measurable_const
  have hMm : MeasurableSet Ms := measurableSet_le continuous_abs.measurable measurable_const
  have hBHm : MeasurableSet BH := (measurableSet_lt measurable_const hA.norm.measurable).inter
    (measurableSet_lt measurable_const continuous_abs.measurable)
  have hAm0 : 0 ≤ Amax := (norm_nonneg _).trans (hAmax 0)
  have hne : ∀ t ∈ Set.Icc a b, t ≠ 0 := fun t ht h0 => by
    have := hca t ht
    rw [h0, abs_zero] at this
    linarith
  -- the pointwise bound
  have hpt : ∀ t ∈ Set.Ioc a b, f t ≤ O.indicator f t + 2 * Amax ^ 2 *
      (1152 * Λ ^ 2 * (t ^ 2)⁻¹ + Ms.indicator (fun _ => 2 * Λ ^ 2 * ε ^ 2) t +
        BH.indicator (fun _ => G) t + ‖B₁ t‖ ^ 2) := by
    intro t ht
    have htI : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self ht
    have ht0 := hne t htI
    have hct := hca t htI
    have hat : 0 < |t| := abs_pos.2 ht0
    have hsq : (t ^ 2)⁻¹ = (|t|⁻¹) ^ 2 := by rw [inv_pow, sq_abs]
    have hi1 : 0 ≤ Ms.indicator (fun _ => 2 * Λ ^ 2 * ε ^ 2) t :=
      Set.indicator_nonneg (fun _ _ => by positivity) t
    have hi2 : 0 ≤ BH.indicator (fun _ => G) t := Set.indicator_nonneg (fun _ _ => by positivity) t
    have hB1 : 0 ≤ ‖B₁ t‖ ^ 2 := by positivity
    have ht2 : 0 ≤ (t ^ 2)⁻¹ := by positivity
    by_cases hO : t ∈ O
    · rw [Set.indicator_of_mem hO]
      have : 0 ≤ 2 * Amax ^ 2 * (1152 * Λ ^ 2 * (t ^ 2)⁻¹ +
          Ms.indicator (fun _ => 2 * Λ ^ 2 * ε ^ 2) t + BH.indicator (fun _ => G) t +
          ‖B₁ t‖ ^ 2) := by positivity
      linarith
    rw [Set.indicator_of_notMem hO, zero_add]
    have hAθ : θ < ‖A t‖ := lt_of_not_ge hO
    -- `|B₀|² ≤ 1152 Λ² t^{-2} + 1_{|t| ≤ X} 2Λ²ε² + 1_{BH} G`
    have hB0 : ‖B₀ t‖ ^ 2 ≤ 1152 * Λ ^ 2 * (t ^ 2)⁻¹ +
        Ms.indicator (fun _ => 2 * Λ ^ 2 * ε ^ 2) t + BH.indicator (fun _ => G) t := by
      have hb := hB₀pt t htI
      by_cases hM : t ∈ Ms
      · rw [Set.indicator_of_mem hM]
        have hsq' : ‖B₀ t‖ ^ 2 ≤ (Λ * (24 / |t| + ε)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
        have h24 : (Λ * (24 / |t| + ε)) ^ 2 ≤ 1152 * Λ ^ 2 * (t ^ 2)⁻¹ + 2 * Λ ^ 2 * ε ^ 2 := by
          rw [hsq, div_eq_mul_inv]
          nlinarith [sq_nonneg (24 * |t|⁻¹ - ε), sq_nonneg Λ]
        linarith
      · have hXt : X < |t| := lt_of_not_ge hM
        rw [Set.indicator_of_mem (show t ∈ BH from ⟨hAθ, hXt⟩)]
        have h1 : Λ * (24 / |t| + ε) ≤ Λ * (24 / X + ε) := by
          gcongr
        have hsq' : ‖B₀ t‖ ^ 2 ≤ G := pow_le_pow_left₀ (norm_nonneg _) (hb.trans h1) 2
        have : 0 ≤ 1152 * Λ ^ 2 * (t ^ 2)⁻¹ := by positivity
        linarith
    have hA2 : ‖A t‖ ^ 2 ≤ Amax ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hAmax t) 2
    have hadd : ‖B₀ t + B₁ t‖ ^ 2 ≤ 2 * (‖B₀ t‖ ^ 2 + ‖B₁ t‖ ^ 2) := by
      have := norm_add_le (B₀ t) (B₁ t)
      nlinarith [sq_nonneg (‖B₀ t‖ - ‖B₁ t‖), norm_nonneg (B₀ t + B₁ t),
        pow_le_pow_left₀ (norm_nonneg _) this 2]
    calc f t = ‖A t‖ ^ 2 * ‖B₀ t + B₁ t‖ ^ 2 := by rw [hfdef]; simp only; rw [norm_mul, mul_pow]
      _ ≤ Amax ^ 2 * (2 * (‖B₀ t‖ ^ 2 + ‖B₁ t‖ ^ 2)) :=
          mul_le_mul hA2 hadd (by positivity) (by positivity)
      _ ≤ 2 * Amax ^ 2 * (1152 * Λ ^ 2 * (t ^ 2)⁻¹ +
          Ms.indicator (fun _ => 2 * Λ ^ 2 * ε ^ 2) t + BH.indicator (fun _ => G) t +
          ‖B₁ t‖ ^ 2) := by nlinarith [sq_nonneg Amax]
  -- integrability on `(a, b]`
  have hIoc : MeasurableSet (Set.Ioc a b) := measurableSet_Ioc
  have hint : ∀ g : ℝ → ℝ, Continuous g → IntegrableOn g (Set.Ioc a b) :=
    fun g hg => (hg.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have h1 : IntegrableOn (O.indicator f) (Set.Ioc a b) := (hint f hfc).indicator hOm
  have h2 : IntegrableOn (fun t : ℝ => 1152 * Λ ^ 2 * (t ^ 2)⁻¹) (Set.Ioc a b) := by
    refine (ContinuousOn.integrableOn_Icc fun t ht => ?_).mono_set Set.Ioc_subset_Icc_self
    exact (continuousAt_const.mul ((continuous_pow 2).continuousAt.inv₀
      (pow_ne_zero 2 (hne t ht)))).continuousWithinAt
  have h3 : IntegrableOn (Ms.indicator fun _ => 2 * Λ ^ 2 * ε ^ 2) (Set.Ioc a b) :=
    (hint _ continuous_const).indicator hMm
  have h4 : IntegrableOn (BH.indicator fun _ => G) (Set.Ioc a b) :=
    (hint _ continuous_const).indicator hBHm
  have h5 : IntegrableOn (fun t => ‖B₁ t‖ ^ 2) (Set.Ioc a b) := hint _ (hB₁.norm.pow 2)
  have h23 : IntegrableOn (fun t : ℝ => 1152 * Λ ^ 2 * (t ^ 2)⁻¹ +
      Ms.indicator (fun _ => 2 * Λ ^ 2 * ε ^ 2) t) (Set.Ioc a b) := h2.add h3
  have h234 : IntegrableOn (fun t : ℝ => 1152 * Λ ^ 2 * (t ^ 2)⁻¹ +
      Ms.indicator (fun _ => 2 * Λ ^ 2 * ε ^ 2) t + BH.indicator (fun _ => G) t)
      (Set.Ioc a b) := h23.add h4
  have h2345 : IntegrableOn (fun t : ℝ => 1152 * Λ ^ 2 * (t ^ 2)⁻¹ +
      Ms.indicator (fun _ => 2 * Λ ^ 2 * ε ^ 2) t + BH.indicator (fun _ => G) t +
      ‖B₁ t‖ ^ 2) (Set.Ioc a b) := h234.add h5
  have hg : IntegrableOn (fun t : ℝ => 2 * Amax ^ 2 * (1152 * Λ ^ 2 * (t ^ 2)⁻¹ +
      Ms.indicator (fun _ => 2 * Λ ^ 2 * ε ^ 2) t + BH.indicator (fun _ => G) t +
      ‖B₁ t‖ ^ 2)) (Set.Ioc a b) := h2345.const_mul _
  have hmono : ∫ t in Set.Ioc a b, f t ≤ ∫ t in Set.Ioc a b, (O.indicator f t + 2 * Amax ^ 2 *
      (1152 * Λ ^ 2 * (t ^ 2)⁻¹ + Ms.indicator (fun _ => 2 * Λ ^ 2 * ε ^ 2) t +
        BH.indicator (fun _ => G) t + ‖B₁ t‖ ^ 2)) :=
    setIntegral_mono_on (hint f hfc) (h1.add hg) hIoc hpt
  rw [integral_add h1 hg, integral_const_mul, integral_add h234 h5, integral_add h23 h4,
    integral_add h2 h3, setIntegral_indicator hOm, setIntegral_indicator hMm,
    setIntegral_indicator hBHm, setIntegral_const, setIntegral_const, integral_const_mul]
    at hmono
  rw [intervalIntegral.integral_of_le hab]
  -- the four parts
  have hO' : ∫ t in Set.Ioc a b ∩ O, f t ≤ Ord := hord
  have hinv : ∫ t in Set.Ioc a b, (t ^ 2)⁻¹ ≤ 2 / c := by
    rw [← intervalIntegral.integral_of_le hab]
    exact integral_inv_sq_le hab hc hca
  have hMvol : volume.real (Set.Ioc a b ∩ Ms) ≤ 2 * X := by
    calc volume.real (Set.Ioc a b ∩ Ms) ≤ volume.real (Set.Icc (-X) X) :=
          measureReal_mono (fun t ht => abs_le.1 ht.2)
            (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      _ = 2 * X := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hBHvol : volume.real (Set.Ioc a b ∩ BH) ≤ 𝒥.card := by
    have hsub : Set.Ioc a b ∩ BH ⊆ ⋃ j ∈ 𝒥, Set.Icc (j : ℝ) (j + 1) := by
      intro t ⟨ht, hθ, hXt⟩
      obtain ⟨j, hj, h1, h2⟩ := hbad t ht hθ hXt
      exact Set.mem_biUnion hj ⟨h1, h2⟩
    have hle : volume (Set.Ioc a b ∩ BH) ≤ 𝒥.card := by
      calc volume (Set.Ioc a b ∩ BH) ≤ volume (⋃ j ∈ 𝒥, Set.Icc (j : ℝ) (j + 1)) :=
            measure_mono hsub
        _ ≤ ∑ j ∈ 𝒥, volume (Set.Icc (j : ℝ) (j + 1)) := measure_biUnion_finset_le _ _
        _ = 𝒥.card := by simp [Real.volume_Icc]
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (by simpa using hle)
  have hB1' : ∫ t in Set.Ioc a b, ‖B₁ t‖ ^ 2 ≤ ME := by
    rw [← intervalIntegral.integral_of_le hab]
    exact hME
  have hG0 : 0 ≤ G := by positivity
  have hm1 : 0 ≤ 2 * Λ ^ 2 * ε ^ 2 := by positivity
  have hm2 : 0 ≤ 1152 * Λ ^ 2 := by positivity
  have hA2 : 0 ≤ 2 * Amax ^ 2 := by positivity
  simp only [smul_eq_mul] at hmono
  refine hmono.trans ?_
  have key : 1152 * Λ ^ 2 * (∫ t in Set.Ioc a b, (t ^ 2)⁻¹) +
      volume.real (Set.Ioc a b ∩ Ms) * (2 * Λ ^ 2 * ε ^ 2) +
      volume.real (Set.Ioc a b ∩ BH) * G + ∫ t in Set.Ioc a b, ‖B₁ t‖ ^ 2 ≤
      Λ ^ 2 * (2304 / c + 4 * ε ^ 2 * X) + 𝒥.card * G + ME := by
    have e1 : 1152 * Λ ^ 2 * (∫ t in Set.Ioc a b, (t ^ 2)⁻¹) ≤ 1152 * Λ ^ 2 * (2 / c) :=
      mul_le_mul_of_nonneg_left hinv hm2
    have e2 : volume.real (Set.Ioc a b ∩ Ms) * (2 * Λ ^ 2 * ε ^ 2) ≤
        2 * X * (2 * Λ ^ 2 * ε ^ 2) := mul_le_mul_of_nonneg_right hMvol hm1
    have e3 : volume.real (Set.Ioc a b ∩ BH) * G ≤ 𝒥.card * G :=
      mul_le_mul_of_nonneg_right hBHvol hG0
    have e4 : 1152 * Λ ^ 2 * (2 / c) + 2 * X * (2 * Λ ^ 2 * ε ^ 2) =
        Λ ^ 2 * (2304 / c + 4 * ε ^ 2 * X) := by ring
    linarith
  have := mul_le_mul_of_nonneg_left key hA2
  linarith

end Erdos408.TwoSided.ConstHigh
