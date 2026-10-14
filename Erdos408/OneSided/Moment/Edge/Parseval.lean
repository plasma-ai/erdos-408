module

public import Erdos408.OneSided.Moment.Edge.Minor

/-!
# Fourier in the product variable and in the cutoff

The two Fourier steps of PD §4 for the clean edge, as kernel bounds.

* `kerLe_parseval` (PD: "Fourier transformation in the unrestricted integer product variable
  diagonalizes its convolution"): a kernel `G(p, p') F(T(p, p') - β x + β' x')` with
  `F(n) = ∫_{lo}^{lo+1} w(θ) e(θ n) dθ`, `|w| ≤ 1` and `β` injective, has norm at most the
  supremum over `θ` with `w(θ) ≠ 0` of the norms of the fibers `G(p, p') e(θ T(p, p'))`.
  The proof is Parseval's identity for `∑_x c_x e(θ β x)` over one period.
* `exists_kerLe_cutoff` (PD `mem:cutoff-fourier`): writing `ψ(t/Y) = ∫ ψ̂(ξ) e(ξ t/Y) dξ`, a
  kernel `H(p, p') ψ(T/Y) e(θ T)` has norm at most `C (n_min + n_triv/U)/2` if the twisted
  kernels `H e((θ + ξ/Y) T)` have norm at most `n_min` for `|ξ| ≤ U` and `n_triv` always.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open MeasureTheory Finset Real

/-- A measurable function bounded by `M` is integrable on every interval. -/
private theorem intervalIntegrable_of_norm_le {F : ℝ → ℂ} (hF : AEStronglyMeasurable F volume)
    {M : ℝ} (hb : ∀ θ, ‖F θ‖ ≤ M) (a b : ℝ) : IntervalIntegrable F volume a b :=
  (intervalIntegrable_const (c := M)).mono_fun' hF.restrict (ae_of_all _ hb)

/-- `e(θ t)` is continuous in `θ`. -/
theorem continuous_ephase_mul (t : ℝ) : Continuous fun θ : ℝ => ephase (θ * t) := by
  unfold ephase
  fun_prop

/-- **Parseval's identity**: for `β` injective on `X`,
`∫_{lo}^{lo+1} |∑_{x ∈ X} c_x e(θ β x)|² dθ = ∑_x |c_x|²`. -/
theorem integral_norm_sq_sum_ephase {κ : Type*} (X : Finset κ) {β : κ → ℤ} (hβ : Set.InjOn β X)
    (c : κ → ℂ) (lo : ℝ) :
    ∫ θ in lo..lo + 1, ‖∑ x ∈ X, ephase (θ * β x) * c x‖ ^ 2 = ∑ x ∈ X, ‖c x‖ ^ 2 := by
  classical
  have hcont : ∀ x x' : κ, Continuous fun θ : ℝ =>
      ephase (θ * β x) * c x * star (ephase (θ * β x') * c x') := fun x x' => by
    have h1 := continuous_ephase_mul (β x)
    have h2 := continuous_ephase_mul (β x')
    exact (h1.mul continuous_const).mul ((h2.mul continuous_const).star)
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have e1 : ∀ θ : ℝ, ((‖∑ x ∈ X, ephase (θ * β x) * c x‖ ^ 2 : ℝ) : ℂ) =
      ∑ x ∈ X, ∑ x' ∈ X, ephase (θ * β x) * c x * star (ephase (θ * β x') * c x') := by
    intro θ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def, star_sum, sum_mul_sum]
  simp_rw [e1]
  rw [intervalIntegral.integral_finsetSum fun x _ =>
    (continuous_finsetSum _ fun x' _ => hcont x x').intervalIntegrable _ _]
  refine (sum_congr rfl fun x _ => intervalIntegral.integral_finsetSum fun x' _ =>
    (hcont x x').intervalIntegrable _ _).trans ?_
  -- only the diagonal survives
  have e2 : ∀ x x' : κ, ∫ θ in lo..lo + 1, ephase (θ * β x) * c x * star (ephase (θ * β x') * c x') =
      c x * star (c x') * (if β x - β x' = 0 then 1 else 0) := by
    intro x x'
    rw [← integral_ephase_period lo (β x - β x'), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [star_mul', star_ephase]
    rw [show ephase (θ * ((β x - β x' : ℤ) : ℝ)) = ephase (θ * β x) * ephase (-(θ * β x')) by
      rw [← ephase_add]; congr 1; push_cast; ring]
    ring
  simp_rw [e2]
  push_cast
  refine sum_congr rfl fun x hx => ?_
  rw [sum_eq_single_of_mem x hx fun x' hx' hne => by
    have : β x - β x' ≠ 0 := fun h => hne (hβ hx' hx (by linarith))
    simp only [this, ↓reduceIte, mul_zero]]
  simp only [sub_self, ↓reduceIte, mul_one]
  rw [← Complex.mul_conj', Complex.star_def]

/-- If `m ≤ (t A + B/t)/2` for every `t > 0`, then `m ≤ √A √B`. -/
private theorem le_sqrt_mul_sqrt_of_amgm {m A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → m ≤ (t * A + B / t) / 2) : m ≤ Real.sqrt A * Real.sqrt B := by
  rcases hA.eq_or_lt with hA0 | hApos
  · -- `A = 0`: `m ≤ B/(2t)` for all `t`
    rw [← hA0, Real.sqrt_zero, zero_mul]
    by_contra hm
    push Not at hm
    have h1 := h (B / m + 1) (by positivity)
    rw [← hA0, mul_zero, zero_add] at h1
    have : B / (B / m + 1) / 2 < m := by
      rw [div_div, div_lt_iff₀ (by positivity)]
      field_simp
      nlinarith
    linarith
  rcases hB.eq_or_lt with hB0 | hBpos
  · -- `B = 0`: `m ≤ t A / 2` for all `t`
    rw [← hB0, Real.sqrt_zero, mul_zero]
    by_contra hm
    push Not at hm
    have h1 := h (m / A) (by positivity)
    rw [← hB0, zero_div, add_zero] at h1
    have : m / A * A / 2 < m := by
      rw [div_mul_cancel₀ _ hApos.ne']
      linarith
    linarith
  · -- `t = √B / √A`
    have hsA := Real.sqrt_pos.2 hApos
    have hsB := Real.sqrt_pos.2 hBpos
    have h1 := h (Real.sqrt B / Real.sqrt A) (by positivity)
    have e : (Real.sqrt B / Real.sqrt A * A + B / (Real.sqrt B / Real.sqrt A)) / 2 =
        Real.sqrt A * Real.sqrt B := by
      have hA' : A = Real.sqrt A ^ 2 := (Real.sq_sqrt hA).symm
      have hB' : B = Real.sqrt B ^ 2 := (Real.sq_sqrt hB).symm
      rw [hA', hB']
      field_simp
      rw [Real.sqrt_sq hsA.le, Real.sqrt_sq hsB.le]
      ring
    linarith

/-- **Fourier in the product variable** (PD §4): a kernel
`G(p, p') ∫_{lo}^{lo+1} w(θ) e(θ (T(p, p') - β x + β x')) dθ` with `|w| ≤ 1` and `β` injective
on `X` has norm at most `ε` if every fiber `G(p, p') e(θ T(p, p'))` with `w(θ) ≠ 0` does. -/
theorem kerLe_parseval {γ κ : Type*} (P : Finset γ) (X : Finset κ) {β : κ → ℤ}
    (hβ : Set.InjOn β X) (G : γ → γ → ℂ) (T : γ → γ → ℤ) {w : ℝ → ℝ} (hwm : Measurable w)
    (hw : ∀ θ, |w θ| ≤ 1) (lo : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hfib : ∀ θ ∈ Set.Ioc lo (lo + 1), w θ ≠ 0 →
      KerLe P P (fun p p' => G p p' * ephase (θ * T p p')) ε) :
    KerLe (P ×ˢ X) (P ×ˢ X) (fun q q' => G q.1 q'.1 *
      ∫ θ in lo..lo + 1, (w θ : ℂ) * ephase (θ * ((T q.1 q'.1 - β q.2 + β q'.2 : ℤ) : ℝ))) ε := by
  classical
  refine kerLe_of_bilinear hε fun f g => ?_
  -- the transforms in the product variable
  set gT : ℝ → γ → ℂ := fun θ p => ∑ x ∈ X, ephase (θ * β x) * g (p, x) with hgT
  set fT : ℝ → γ → ℂ := fun θ p => ∑ x ∈ X, ephase (θ * β x) * f (p, x) with hfT
  set Φ : ℝ → ℂ := fun θ =>
    ∑ p ∈ P, star (gT θ p) * ∑ p' ∈ P, G p p' * ephase (θ * T p p') * fT θ p' with hΦ
  have hgTc : ∀ p, Continuous fun θ => gT θ p := fun p =>
    continuous_finsetSum _ fun x _ => (continuous_ephase_mul _).mul continuous_const
  have hfTc : ∀ p, Continuous fun θ => fT θ p := fun p =>
    continuous_finsetSum _ fun x _ => (continuous_ephase_mul _).mul continuous_const
  have hwc : Measurable fun θ => (w θ : ℂ) := Complex.measurable_ofReal.comp hwm
  -- the integrand of one pair `(q, q')`
  set I : (γ × κ) → (γ × κ) → ℝ → ℂ := fun q q' θ => star (g q) * (G q.1 q'.1 *
    ((w θ : ℂ) * ephase (θ * ((T q.1 q'.1 - β q.2 + β q'.2 : ℤ) : ℝ))) * f q') with hI
  have hIi : ∀ q q', IntervalIntegrable (I q q') volume lo (lo + 1) := by
    intro q q'
    refine intervalIntegrable_of_norm_le ?_ (M := ‖g q‖ * ‖G q.1 q'.1‖ * ‖f q'‖) (fun θ => ?_) _ _
    · exact (measurable_const.mul ((measurable_const.mul (hwc.mul
        (continuous_ephase_mul _).measurable)).mul measurable_const)).aestronglyMeasurable
    · simp only [hI, norm_mul, norm_star, norm_ephase, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      have := hw θ
      have h0 : 0 ≤ ‖g q‖ * ‖G q.1 q'.1‖ * ‖f q'‖ := by positivity
      nlinarith [norm_nonneg (g q), norm_nonneg (G q.1 q'.1), norm_nonneg (f q'), abs_nonneg (w θ),
        mul_nonneg (mul_nonneg (norm_nonneg (g q)) (norm_nonneg (G q.1 q'.1))) (norm_nonneg (f q'))]
  -- the bilinear form is `∫ w Φ`
  have hsum : ∀ θ, ∑ q ∈ P ×ˢ X, ∑ q' ∈ P ×ˢ X, I q q' θ = (w θ : ℂ) * Φ θ := by
    intro θ
    have he : ∀ a b c : ℤ, ephase (θ * ((a - b + c : ℤ) : ℝ)) =
        ephase (θ * a) * ephase (-(θ * b)) * ephase (θ * c) := by
      intro a b c
      rw [← ephase_add, ← ephase_add]
      congr 1
      push_cast
      ring
    simp only [hI, hΦ, hgT, hfT, he, sum_product, star_sum, star_mul', star_ephase, mul_sum, sum_mul]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun p' _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun x' _ => sum_congr rfl fun x _ => ?_
    ring
  have hbil : ∑ q ∈ P ×ˢ X, star (g q) * ∑ q' ∈ P ×ˢ X, G q.1 q'.1 *
      (∫ θ in lo..lo + 1, (w θ : ℂ) * ephase (θ * ((T q.1 q'.1 - β q.2 + β q'.2 : ℤ) : ℝ))) * f q' =
      ∫ θ in lo..lo + 1, (w θ : ℂ) * Φ θ := by
    have e1 : ∀ q q', star (g q) * (G q.1 q'.1 *
        (∫ θ in lo..lo + 1, (w θ : ℂ) * ephase (θ * ((T q.1 q'.1 - β q.2 + β q'.2 : ℤ) : ℝ))) *
          f q') = ∫ θ in lo..lo + 1, I q q' θ := by
      intro q q'
      simp only [hI]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const_mul]
    simp_rw [mul_sum, e1]
    have hsumi : ∀ q, IntervalIntegrable (fun θ => ∑ q' ∈ P ×ˢ X, I q q' θ) volume lo (lo + 1) :=
      fun q => by
        have := IntervalIntegrable.sum (P ×ˢ X) fun q' _ => hIi q q'
        rwa [Finset.sum_fn] at this
    simp_rw [← intervalIntegral.integral_finsetSum fun q' _ => hIi _ q']
    rw [← intervalIntegral.integral_finsetSum fun q _ => hsumi q]
    exact intervalIntegral.integral_congr fun θ _ => hsum θ
  rw [hbil]
  -- the fiber bound at each `θ`
  set a : ℝ → ℝ := fun θ => Real.sqrt (∑ p ∈ P, ‖gT θ p‖ ^ 2) with ha
  set b : ℝ → ℝ := fun θ => Real.sqrt (∑ p ∈ P, ‖fT θ p‖ ^ 2) with hb
  have hac : Continuous a := (continuous_finsetSum _ fun p _ => (hgTc p).norm.pow 2).sqrt
  have hbc : Continuous b := (continuous_finsetSum _ fun p _ => (hfTc p).norm.pow 2).sqrt
  have hfibθ : ∀ θ ∈ Set.Ioc lo (lo + 1), ‖(w θ : ℂ) * Φ θ‖ ≤ ε * (a θ * b θ) := by
    intro θ hθ
    by_cases hw0 : w θ = 0
    · rw [hw0, Complex.ofReal_zero, zero_mul, norm_zero]
      exact mul_nonneg hε (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · have h := (hfib θ hθ hw0).bilinear hε (fT θ) (gT θ)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : ‖Φ θ‖ ≤ ε * a θ * b θ := h
      calc |w θ| * ‖Φ θ‖ ≤ 1 * (ε * a θ * b θ) :=
            mul_le_mul (hw θ) h1 (norm_nonneg _) zero_le_one
        _ = ε * (a θ * b θ) := by ring
  refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith) (ae_of_all _ hfibθ)
    ((hac.mul hbc).const_smul ε |>.intervalIntegrable _ _)).trans ?_
  rw [intervalIntegral.integral_const_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hε
  -- Parseval in the product variable
  have hparse : ∀ (F : γ × κ → ℂ) (Fh : ℝ → γ → ℂ),
      (∀ θ p, Fh θ p = ∑ x ∈ X, ephase (θ * β x) * F (p, x)) →
      ∫ θ in lo..lo + 1, Real.sqrt (∑ p ∈ P, ‖Fh θ p‖ ^ 2) ^ 2 = ∑ q ∈ P ×ˢ X, ‖F q‖ ^ 2 := by
    intro F Fh hFh
    have hc : ∀ p, Continuous fun θ => ‖Fh θ p‖ ^ 2 := fun p => by
      simp_rw [hFh]
      exact ((continuous_finsetSum _ fun x _ =>
        (continuous_ephase_mul _).mul continuous_const).norm.pow 2)
    simp_rw [Real.sq_sqrt (sum_nonneg fun p _ => sq_nonneg ‖Fh _ p‖)]
    rw [intervalIntegral.integral_finsetSum fun p _ => (hc p).intervalIntegrable _ _, sum_product]
    refine sum_congr rfl fun p _ => ?_
    simp_rw [hFh]
    exact integral_norm_sq_sum_ephase X hβ (fun x => F (p, x)) lo
  have hA := hparse g gT fun θ p => rfl
  have hB := hparse f fT fun θ p => rfl
  set A := ∑ q ∈ P ×ˢ X, ‖g q‖ ^ 2
  set B := ∑ q ∈ P ×ˢ X, ‖f q‖ ^ 2
  have hA0 : 0 ≤ A := sum_nonneg fun q _ => sq_nonneg _
  have hB0 : 0 ≤ B := sum_nonneg fun q _ => sq_nonneg _
  -- `∫ a b ≤ (t A + B/t)/2` for every `t > 0`
  have hamgm : ∀ t : ℝ, 0 < t → ∫ θ in lo..lo + 1, a θ * b θ ≤ (t * A + B / t) / 2 := by
    intro t ht
    have hle : ∀ θ ∈ Set.Icc lo (lo + 1), a θ * b θ ≤ (t * a θ ^ 2 + b θ ^ 2 / t) / 2 := by
      intro θ _
      have : 0 ≤ (t * a θ - b θ) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
      have e : (t * a θ - b θ) ^ 2 / t = t * a θ ^ 2 + b θ ^ 2 / t - 2 * (a θ * b θ) := by
        field_simp
        ring
      linarith
    have hc1 : Continuous fun θ => t * a θ ^ 2 := continuous_const.mul (hac.pow 2)
    have hc2 : Continuous fun θ => b θ ^ 2 / t := (hbc.pow 2).div_const t
    have hc3 : Continuous fun θ => (t * a θ ^ 2 + b θ ^ 2 / t) / 2 := (hc1.add hc2).div_const 2
    refine (intervalIntegral.integral_mono_on (by linarith) ((hac.mul hbc).intervalIntegrable _ _)
      (hc3.intervalIntegrable _ _) hle).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add
      (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _), intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul]
    simp only [ha, hb]
    rw [hA, hB]
  exact le_sqrt_mul_sqrt_of_amgm hA0 hB0 hamgm

/-- **The cutoff in Fourier space** (PD `mem:cutoff-fourier`): there is a constant `C` such that a
kernel `H(p, p') ψ(T/Y) e(θ T)` has norm at most `C (n_min + n_triv/U)/2`, whenever the twisted
kernels `H(p, p') e((θ + ξ/Y) T)` have norm at most `n_min` for `|ξ| ≤ U` and at most `n_triv`
for all `ξ`. -/
theorem exists_kerLe_cutoff : ∃ C : ℝ, 0 ≤ C ∧ ∀ {γ : Type*} (P : Finset γ) (H : γ → γ → ℂ)
    (T : γ → γ → ℤ) (θ Y U nmin ntriv : ℝ), 0 < Y → 1 ≤ U → 0 ≤ nmin → 0 ≤ ntriv →
    (∀ ξ, |ξ| ≤ U → KerLe P P (fun p p' => H p p' * ephase ((θ + ξ / Y) * T p p')) nmin) →
    (∀ ξ, KerLe P P (fun p p' => H p p' * ephase ((θ + ξ / Y) * T p p')) ntriv) →
    KerLe P P (fun p p' => H p p' * ((plateau (T p p' / Y) : ℂ) * ephase (θ * T p p')))
      (C / 2 * (nmin + ntriv / U)) := by
  obtain ⟨C, hC0, hcont, hdec, htail, hinv⟩ := exists_plateau_fourier
  refine ⟨C, hC0, fun P H T θ Y U nmin ntriv hY hU hmin0 htriv0 hmin htriv => ?_⟩
  have hU0 : 0 < U := by linarith
  refine kerLe_of_bilinear (by positivity) fun f g => ?_
  set ψh := ft fun t => (plateau t : ℂ) with hψh
  have hdecI := integrable_fourierDecay
  -- functions dominated by a multiple of `g` are integrable
  have hint : ∀ {F : ℝ → ℂ}, Continuous F → ∀ M, (∀ ξ, ‖F ξ‖ ≤ M * fourierDecay ξ) →
      Integrable F := fun hF M hb =>
    (hdecI.1.const_mul M).mono' hF.aestronglyMeasurable (ae_of_all _ hb)
  set Bf : ℝ → ℂ := fun ξ =>
    ∑ p ∈ P, star (g p) * ∑ p' ∈ P, H p p' * ephase ((θ + ξ / Y) * T p p') * f p' with hBf
  set E : ℤ → ℝ → ℂ := fun t ξ =>
    Complex.exp (2 * π * Complex.I * ((t / Y : ℝ) : ℂ) * (ξ : ℂ)) with hE
  have hphase : ∀ (t : ℤ) (ξ : ℝ), ephase ((θ + ξ / Y) * t) = ephase (θ * t) * E t ξ := by
    intro t ξ
    rw [show (θ + ξ / Y) * t = θ * t + ξ * t / Y by ring, ephase_add]
    congr 1
    rw [ephase, hE]
    congr 1
    push_cast
    ring
  -- one pair `(p, p')`
  have hterm : ∀ p p', star (g p) * (H p p' * ((plateau (T p p' / Y) : ℂ) * ephase (θ * T p p')) *
      f p') = ∫ ξ, ψh ξ * (star (g p) * (H p p' * ephase ((θ + ξ / Y) * T p p') * f p')) := by
    intro p p'
    have h1 : (plateau (T p p' / Y) : ℂ) = ∫ ξ, E (T p p') ξ * ψh ξ := (hinv _).symm
    calc star (g p) * (H p p' * ((plateau (T p p' / Y) : ℂ) * ephase (θ * T p p')) * f p')
        = (∫ ξ, E (T p p') ξ * ψh ξ) * (star (g p) * H p p' * ephase (θ * T p p') * f p') := by
          rw [h1]
          ring
      _ = ∫ ξ, E (T p p') ξ * ψh ξ * (star (g p) * H p p' * ephase (θ * T p p') * f p') :=
          (integral_mul_const _ _).symm
      _ = _ := integral_congr_ae (ae_of_all _ fun ξ => by
          simp only
          rw [hphase]
          ring)
  have hcontξ : ∀ t : ℤ, Continuous fun ξ : ℝ => ephase ((θ + ξ / Y) * t) := fun t => by
    unfold ephase
    fun_prop
  have htermi : ∀ p p', Integrable fun ξ =>
      ψh ξ * (star (g p) * (H p p' * ephase ((θ + ξ / Y) * T p p') * f p')) := by
    intro p p'
    refine hint (hcont.mul (continuous_const.mul ((continuous_const.mul (hcontξ _)).mul
      continuous_const))) (C * (‖g p‖ * ‖H p p'‖ * ‖f p'‖)) fun ξ => ?_
    have h0 : 0 ≤ ‖g p‖ * ‖H p p'‖ * ‖f p'‖ := by positivity
    refine le_trans (b := C * fourierDecay ξ * (‖g p‖ * ‖H p p'‖ * ‖f p'‖)) ?_ (le_of_eq (by ring))
    rw [norm_mul]
    refine mul_le_mul (hdec ξ) (le_of_eq ?_) (norm_nonneg _)
      (mul_nonneg hC0 (by unfold fourierDecay; positivity))
    rw [norm_mul, norm_mul, norm_mul, norm_star, norm_ephase, mul_one, mul_assoc]
  have hbil : ∑ p ∈ P, star (g p) * ∑ p' ∈ P,
      H p p' * ((plateau (T p p' / Y) : ℂ) * ephase (θ * T p p')) * f p' =
      ∫ ξ, ψh ξ * Bf ξ := by
    simp_rw [mul_sum, hterm]
    refine (sum_congr rfl fun p _ => (integral_finsetSum P fun p' _ => htermi p p').symm).trans ?_
    rw [← integral_finsetSum P fun p _ => integrable_finsetSum P fun p' _ => htermi p p']
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [hBf, mul_sum]
  rw [hbil]
  -- the pointwise bound
  set NG := Real.sqrt (∑ p ∈ P, ‖g p‖ ^ 2)
  set NF := Real.sqrt (∑ p ∈ P, ‖f p‖ ^ 2)
  have hdec0 : ∀ ξ, 0 ≤ fourierDecay ξ := fun ξ => by unfold fourierDecay; positivity
  have hpt : ∀ ξ, ‖ψh ξ * Bf ξ‖ ≤ C * (nmin + ntriv / U) * NG * NF * fourierDecay ξ := by
    intro ξ
    rw [norm_mul]
    have hN : 0 ≤ NG * NF := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    by_cases hξ : |ξ| ≤ U
    · have hB : ‖Bf ξ‖ ≤ nmin * NG * NF := (hmin ξ hξ).bilinear hmin0 f g
      calc ‖ψh ξ‖ * ‖Bf ξ‖ ≤ (C * fourierDecay ξ) * (nmin * NG * NF) :=
            mul_le_mul (hdec ξ) hB (norm_nonneg _) (mul_nonneg hC0 (hdec0 ξ))
        _ ≤ (C * fourierDecay ξ) * ((nmin + ntriv / U) * NG * NF) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 (hdec0 ξ))
            rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hN
        _ = _ := by ring
    · push Not at hξ
      have hB : ‖Bf ξ‖ ≤ ntriv * NG * NF := (htriv ξ).bilinear htriv0 f g
      calc ‖ψh ξ‖ * ‖Bf ξ‖ ≤ (C / U * fourierDecay ξ) * (ntriv * NG * NF) :=
            mul_le_mul (htail U ξ hU hξ) hB (norm_nonneg _)
              (mul_nonneg (div_nonneg hC0 hU0.le) (hdec0 ξ))
        _ = (C * fourierDecay ξ) * ((ntriv / U) * NG * NF) := by ring
        _ ≤ (C * fourierDecay ξ) * ((nmin + ntriv / U) * NG * NF) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 (hdec0 ξ))
            rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hmin0) hN
        _ = _ := by ring
  refine (norm_integral_le_of_norm_le (hdecI.1.const_mul _) (ae_of_all _ hpt)).trans
    (le_of_eq ?_)
  rw [integral_const_mul, hdecI.2]
  ring

end Erdos408.OneSided
