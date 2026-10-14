import Mathlib

/-! The weighted energy of a finite sum of Mellin-separated box polynomials:
Cauchy--Schwarz in the separation variable and Tonelli. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos821.P5Marked

theorem sq_le_of_forall_amgm {x A B : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ l : ℝ, 0 < l → x ≤ (l * A + B / l) / 2) : x ^ 2 ≤ A * B := by
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · rw [← hx0]; simp; positivity
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · exfalso
    have hl : 0 < B / x + 1 := by positivity
    have h1 := h _ hl
    rw [← hA0, mul_zero, zero_add] at h1
    have : B / (B / x + 1) / 2 < x := by
      rw [div_div, div_lt_iff₀ (by positivity)]
      have : B / x * x = B := by field_simp
      nlinarith
    linarith
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · exfalso
    have hl : 0 < x / (A + 1) := by positivity
    have h1 := h _ hl
    rw [← hB0, zero_div, add_zero] at h1
    have : x / (A + 1) * A / 2 < x := by
      rw [div_mul_eq_mul_div, div_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hl : 0 < Real.sqrt (B / A) := Real.sqrt_pos.mpr (by positivity)
  have h1 := h _ hl
  have e1 : Real.sqrt (B / A) * A = Real.sqrt (A * B) := by
    rw [show A * B = (B / A) * A ^ 2 by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hA]
  have e2 : B / Real.sqrt (B / A) = Real.sqrt (A * B) := by
    rw [div_eq_iff hl.ne', show A * B = (B / A) * A ^ 2 by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hA, mul_comm, ← mul_assoc, Real.mul_self_sqrt (by positivity)]
    field_simp
  rw [e1, e2] at h1
  have h2 : x ≤ Real.sqrt (A * B) := by linarith
  calc x ^ 2 ≤ Real.sqrt (A * B) ^ 2 := pow_le_pow_left₀ hx h2 2
    _ = A * B := Real.sq_sqrt (by positivity)

/-- Cauchy--Schwarz against a finite measure `‖f‖`. -/
theorem norm_integral_mul_sq_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f g : X → ℂ) (hf : Integrable f μ) (hg : AEStronglyMeasurable g μ) (M : ℝ)
    (hgM : ∀ x, ‖g x‖ ≤ M) :
    ‖∫ x, f x * g x ∂μ‖ ^ 2 ≤ (∫ x, ‖f x‖ ∂μ) * ∫ x, ‖f x‖ * ‖g x‖ ^ 2 ∂μ := by
  have hfn := hf.norm
  have hmeas1 : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
    hf.aestronglyMeasurable.norm.mul hg.norm
  have hmeas2 : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖ ^ 2) μ :=
    hf.aestronglyMeasurable.norm.mul (hg.norm.pow 2)
  have hI1 : Integrable (fun x => ‖f x‖ * ‖g x‖) μ := by
    refine (hfn.mul_const M).mono' hmeas1 (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hgM x) (norm_nonneg _)
  have hI2 : Integrable (fun x => ‖f x‖ * ‖g x‖ ^ 2) μ := by
    refine (hfn.mul_const (M ^ 2)).mono' hmeas2 (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hgM x) 2) (norm_nonneg _)
  have hx : ‖∫ x, f x * g x ∂μ‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp only [norm_mul]
  apply sq_le_of_forall_amgm (norm_nonneg _) (integral_nonneg fun x => norm_nonneg _)
    (integral_nonneg fun x => by positivity)
  intro l hl
  refine hx.trans ?_
  have hpt : ∀ x, ‖f x‖ * ‖g x‖ ≤ (l * ‖f x‖ + ‖f x‖ * ‖g x‖ ^ 2 / l) / 2 := by
    intro x
    have h0 : 0 ≤ ‖f x‖ * (l - ‖g x‖) ^ 2 / l := by positivity
    have e : (l * ‖f x‖ + ‖f x‖ * ‖g x‖ ^ 2 / l) / 2 - ‖f x‖ * ‖g x‖ =
        ‖f x‖ * (l - ‖g x‖) ^ 2 / l / 2 := by field_simp; ring
    linarith
  calc ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤ ∫ x, (l * ‖f x‖ + ‖f x‖ * ‖g x‖ ^ 2 / l) / 2 ∂μ :=
        integral_mono hI1 (((hfn.const_mul l).add (hI2.div_const l)).div_const 2) hpt
    _ = (l * ∫ x, ‖f x‖ ∂μ + (∫ x, ‖f x‖ * ‖g x‖ ^ 2 ∂μ) / l) / 2 := by
        rw [integral_div, integral_add (hfn.const_mul l) (hI2.div_const l), integral_const_mul,
          integral_div]

theorem norm_sum_sq_le_card {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  calc ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := sq_sum_le_card_mul_sum_sq

/-- Energy of a finite sum of Mellin-separated box polynomials. -/
theorem mellin_box_energy {ι : Type*} (Rel : Finset ι) (b : (Fin 1 → ℝ) → ℂ)
    (hb : Integrable b) (Pb : ι → ℝ → ℂ) (hPc : ∀ β, Continuous (Pb β)) (Mb : ι → ℝ)
    (hPb : ∀ β t, ‖Pb β t‖ ≤ Mb β)
    (w : ℝ → ℝ) (hw : Integrable w) (hwc : Continuous w) (hwnn : ∀ t, 0 ≤ w t)
    (c R A1 εt : ℝ) (Jm Ja : ι → ℝ) (hJm0 : ∀ β, 0 ≤ Jm β) (hJa0 : ∀ β, 0 ≤ Ja β)
    (hA1 : ∫ ξ, ‖b ξ‖ ≤ A1) (htail : ∫ ξ in {ξ : Fin 1 → ℝ | R < ‖ξ‖}, ‖b ξ‖ ≤ εt)
    (hJm : ∀ β ∈ Rel, ∀ ξ : Fin 1 → ℝ, ‖ξ‖ ≤ R →
      ∫ t, w t * ‖Pb β (t + c + 2 * Real.pi * ξ 0)‖ ^ 2 ≤ Jm β)
    (hJa : ∀ β ∈ Rel, ∀ ξ : Fin 1 → ℝ,
      ∫ t, w t * ‖Pb β (t + c + 2 * Real.pi * ξ 0)‖ ^ 2 ≤ Ja β)
    (D : ℝ → ℂ)
    (hD : ∀ t, D t = ∑ β ∈ Rel, ∫ ξ, b ξ * Pb β (t + c + 2 * Real.pi * ξ 0)) :
    ∫ t, w t * ‖D t‖ ^ 2 ≤ Rel.card * A1 * ∑ β ∈ Rel, (A1 * Jm β + εt * Ja β) := by
  have hA1nn : 0 ≤ A1 := (integral_nonneg fun ξ => norm_nonneg (b ξ)).trans hA1
  -- the integrand on the product
  let arg : ℝ → (Fin 1 → ℝ) → ℝ := fun t ξ => t + c + 2 * Real.pi * ξ 0
  have harg : Continuous (fun z : ℝ × (Fin 1 → ℝ) => arg z.1 z.2) := by
    simp only [arg]; fun_prop
  let F : ι → ℝ → (Fin 1 → ℝ) → ℝ := fun β t ξ => w t * (‖b ξ‖ * ‖Pb β (arg t ξ)‖ ^ 2)
  have hFint : ∀ β, Integrable (Function.uncurry (F β)) (volume.prod volume) := by
    intro β
    have hdom : Integrable (fun z : ℝ × (Fin 1 → ℝ) => (Mb β) ^ 2 * (w z.1 * ‖b z.2‖))
        (volume.prod volume) := (hw.mul_prod hb.norm).const_mul _
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have h1 : AEStronglyMeasurable (fun z : ℝ × (Fin 1 → ℝ) => w z.1) (volume.prod volume) :=
        hwc.aestronglyMeasurable.comp_fst
      have h2 : AEStronglyMeasurable (fun z : ℝ × (Fin 1 → ℝ) => ‖b z.2‖) (volume.prod volume) :=
        hb.aestronglyMeasurable.norm.comp_snd
      have h3 : AEStronglyMeasurable (fun z : ℝ × (Fin 1 → ℝ) => ‖Pb β (arg z.1 z.2)‖ ^ 2)
          (volume.prod volume) :=
        (((hPc β).comp harg).norm.pow 2).aestronglyMeasurable
      exact h1.mul (h2.mul h3)
    · simp only [Function.uncurry, F]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwnn _) (by positivity))]
      have hP2 : ‖Pb β (arg z.1 z.2)‖ ^ 2 ≤ Mb β ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hPb _ _) 2
      calc w z.1 * (‖b z.2‖ * ‖Pb β (arg z.1 z.2)‖ ^ 2)
          ≤ w z.1 * (‖b z.2‖ * Mb β ^ 2) := by gcongr; exact hwnn _
        _ = Mb β ^ 2 * (w z.1 * ‖b z.2‖) := by ring
  have hFi' : ∀ β, Integrable (fun t => ∫ ξ, F β t ξ) := fun β => (hFint β).integral_prod_left
  -- pointwise bound
  let RHS : ℝ → ℝ := fun t => Rel.card * A1 * ∑ β ∈ Rel, ∫ ξ, F β t ξ
  have hRHSint : Integrable RHS := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro β _
    exact hFi' β
  have hpt : ∀ t, w t * ‖D t‖ ^ 2 ≤ RHS t := by
    intro t
    have hG : ∀ β, ‖∫ ξ, b ξ * Pb β (arg t ξ)‖ ^ 2 ≤ A1 * ∫ ξ, ‖b ξ‖ * ‖Pb β (arg t ξ)‖ ^ 2 := by
      intro β
      have hcs := norm_integral_mul_sq_le b (fun ξ => Pb β (arg t ξ)) hb
        (((hPc β).comp (by simp only [arg]; fun_prop)).aestronglyMeasurable) (Mb β)
        (fun ξ => hPb _ _)
      refine hcs.trans (mul_le_mul_of_nonneg_right hA1 (integral_nonneg fun ξ => by positivity))
    have hDt : ‖D t‖ ^ 2 ≤ Rel.card * ∑ β ∈ Rel, A1 * ∫ ξ, ‖b ξ‖ * ‖Pb β (arg t ξ)‖ ^ 2 := by
      rw [hD t]
      refine (norm_sum_sq_le_card Rel _).trans ?_
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun β _ => hG β
    calc w t * ‖D t‖ ^ 2
        ≤ w t * (Rel.card * ∑ β ∈ Rel, A1 * ∫ ξ, ‖b ξ‖ * ‖Pb β (arg t ξ)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hDt (hwnn t)
      _ = RHS t := by
          simp only [RHS, F, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro β _
          rw [integral_const_mul]
          ring
  have hint : ∫ t, w t * ‖D t‖ ^ 2 ≤ ∫ t, RHS t :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => mul_nonneg (hwnn t)
      (by positivity)) hRHSint (Filter.Eventually.of_forall hpt)
  refine hint.trans ?_
  simp only [RHS]
  rw [integral_const_mul, integral_finsetSum _ (fun β _ => hFi' β)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro β hβ
  rw [integral_integral_swap (hFint β)]
  -- inner integral in t
  have hinner : ∀ ξ, ∫ t, F β t ξ ≤ Jm β * ‖b ξ‖ +
      Ja β * ({ξ : Fin 1 → ℝ | R < ‖ξ‖}.indicator (fun ξ => ‖b ξ‖) ξ) := by
    intro ξ
    have e : ∫ t, F β t ξ = ‖b ξ‖ * ∫ t, w t * ‖Pb β (arg t ξ)‖ ^ 2 := by
      simp only [F]
      rw [← integral_const_mul]
      congr 1; funext t; ring
    rw [e]
    by_cases hR : ‖ξ‖ ≤ R
    · have := hJm β hβ ξ hR
      have hind : 0 ≤ Ja β * ({ξ : Fin 1 → ℝ | R < ‖ξ‖}.indicator (fun ξ => ‖b ξ‖) ξ) := by
        apply mul_nonneg (hJa0 β)
        simp only [Set.indicator]; split_ifs <;> positivity
      have : ‖b ξ‖ * ∫ t, w t * ‖Pb β (arg t ξ)‖ ^ 2 ≤ Jm β * ‖b ξ‖ := by
        rw [mul_comm (Jm β)]
        exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
      linarith
    · rw [not_le] at hR
      have hmem : ξ ∈ {ξ : Fin 1 → ℝ | R < ‖ξ‖} := hR
      rw [Set.indicator_of_mem hmem]
      have := hJa β hβ ξ
      have : ‖b ξ‖ * ∫ t, w t * ‖Pb β (arg t ξ)‖ ^ 2 ≤ Ja β * ‖b ξ‖ := by
        rw [mul_comm (Ja β)]
        exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
      have : 0 ≤ Jm β * ‖b ξ‖ := mul_nonneg (hJm0 β) (norm_nonneg _)
      linarith
  have hmeasS : MeasurableSet {ξ : Fin 1 → ℝ | R < ‖ξ‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hindint : Integrable ({ξ : Fin 1 → ℝ | R < ‖ξ‖}.indicator (fun ξ => ‖b ξ‖)) :=
    hb.norm.indicator hmeasS
  calc ∫ ξ, ∫ t, F β t ξ
      ≤ ∫ ξ, (Jm β * ‖b ξ‖ + Ja β * ({ξ : Fin 1 → ℝ | R < ‖ξ‖}.indicator (fun ξ => ‖b ξ‖) ξ)) :=
        integral_mono (hFint β).integral_prod_right
          ((hb.norm.const_mul _).add (hindint.const_mul _)) hinner
    _ = Jm β * (∫ ξ, ‖b ξ‖) + Ja β * ∫ ξ, {ξ : Fin 1 → ℝ | R < ‖ξ‖}.indicator (fun ξ => ‖b ξ‖) ξ := by
        rw [integral_add (hb.norm.const_mul _) (hindint.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ Jm β * A1 + Ja β * εt := by
        have htail' := htail
        rw [← integral_indicator hmeasS] at htail'
        exact add_le_add (mul_le_mul_of_nonneg_left hA1 (hJm0 β))
          (mul_le_mul_of_nonneg_left htail' (hJa0 β))
    _ = A1 * Jm β + εt * Ja β := by ring

end Erdos821.P5Marked
