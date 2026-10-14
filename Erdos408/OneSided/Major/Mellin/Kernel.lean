module

public import Erdos408.OneSided.Major.Mellin.Smooth
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The major-arc kernel in logarithmic coordinates

For `w, w' ∈ [1, 16]` put `ζ = X log(w/w')` and `z = log w'`, so that
`X(w - w') = y(ζ, z) = X e^z (e^{ζ/X} - 1)`. The cut-off kernel
`Φ(ζ, z) = φ(y(ζ, z)) ψ(ζ/4) ψ(z/4)` is smooth, supported in the ball of radius `20`, and agrees
with `φ(X(w - w'))` on that range when `φ` vanishes outside `(-5, 5)`.

* `exists_norm_iteratedFDeriv_gapKernel_le`: `‖D^n Φ‖ ≤ B K` for `n ≤ 4`, uniformly in `X ≥ 2`,
  when `‖D^i φ‖ ≤ K` for `i ≤ 4`.
* `gapKernel_log`: `Φ(X log(w/w'), log w') = φ(X(w - w'))`.
-/

@[expose] public section

namespace Erdos408.OneSided.Mellin

open ContDiff Real

/-- `y(ζ, z) = X e^z (e^{ζ/X} - 1)`, so that `y(X log(w/w'), log w') = X(w - w')`. -/
noncomputable def logGap (X : ℝ) (p : ℝ × ℝ) : ℝ := exp p.2 * (X * (exp (p.1 / X) - 1))

/-- The cut-off kernel `Φ(ζ, z) = φ(y(ζ, z)) ψ(ζ/4) ψ(z/4)`. -/
noncomputable def gapKernel (φ : ℝ → ℂ) (X : ℝ) (p : ℝ × ℝ) : ℂ :=
  φ (logGap X p) * ((plateau (p.1 / 4) * plateau (p.2 / 4) : ℝ) : ℂ)

/-- `y` is smooth. -/
theorem contDiff_logGap (X : ℝ) : ContDiff ℝ ∞ (logGap X) :=
  (contDiff_exp.comp contDiff_snd).mul (contDiff_const.mul
    ((contDiff_exp.comp (contDiff_fst.div_const X)).sub contDiff_const))

/-- Composing with a projection does not increase the derivatives. -/
theorem norm_iteratedFDeriv_comp_clm_le {L : ℝ × ℝ →L[ℝ] ℝ} (hL : ‖L‖ ≤ 1) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (j : ℕ) (p : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ j (h ∘ L) p‖ ≤ ‖iteratedDeriv j h (L p)‖ := by
  rw [L.iteratedFDeriv_comp_right hh p (by exact_mod_cast le_top),
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => hL)

/-- `|e^t - 1| ≤ |t| e^{|t|}`. -/
theorem abs_exp_sub_one_le_mul (t : ℝ) : |exp t - 1| ≤ |t| * exp |t| := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_of_nonneg (by linarith [add_one_le_exp t])]
    have h := add_one_le_exp (-t)
    have h' := exp_pos t
    rw [exp_neg] at h
    have : (-t + 1) * exp t ≤ 1 := by
      calc (-t + 1) * exp t ≤ (exp t)⁻¹ * exp t := by gcongr
        _ = 1 := inv_mul_cancel₀ h'.ne'
    nlinarith
  · rw [abs_of_nonpos ht, abs_of_nonpos (by linarith [exp_le_one_iff.2 ht])]
    nlinarith [add_one_le_exp t, one_le_exp (neg_nonneg.2 ht)]

/-- The derivatives of `g(ζ) = X(e^{ζ/X} - 1)` are at most `20 e^{10}` for `|ζ| ≤ 20`. -/
theorem norm_iteratedDeriv_gap_le {X : ℝ} (hX : 2 ≤ X) (j : ℕ) {ζ : ℝ} (hζ : |ζ| ≤ 20) :
    ‖iteratedDeriv j (fun ζ => X * (exp (ζ / X) - 1)) ζ‖ ≤ 20 * exp 10 := by
  have hX0 : 0 < X := by linarith
  have hq : |ζ| / X ≤ 10 := by
    rw [div_le_iff₀ hX0]
    linarith
  cases j with
  | zero =>
    rw [iteratedDeriv_zero, Real.norm_eq_abs, abs_mul, abs_of_pos hX0]
    refine (mul_le_mul_of_nonneg_left (abs_exp_sub_one_le_mul _) hX0.le).trans ?_
    rw [abs_div, abs_of_pos hX0, ← mul_assoc, mul_div_cancel₀ _ hX0.ne']
    gcongr
  | succ m =>
    -- `g' = e^{ζ/X}`
    have hd : deriv (fun ζ => X * (exp (ζ / X) - 1)) = fun ζ => exp (X⁻¹ * ζ) := by
      funext ζ
      have h := (((hasDerivAt_id' ζ).div_const X).exp.sub_const 1).const_mul X
      rw [h.deriv]
      field_simp
    rw [iteratedDeriv_succ', hd, iteratedDeriv_exp_const_mul, Real.norm_eq_abs, abs_mul,
      abs_of_pos (exp_pos _), abs_pow, abs_inv, abs_of_pos hX0]
    have h1 : (X⁻¹) ^ m ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
    have h2 : exp (X⁻¹ * ζ) ≤ exp 10 := by
      refine exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul, abs_inv, abs_of_pos hX0, inv_mul_eq_div]
      exact hq
    calc (X⁻¹) ^ m * exp (X⁻¹ * ζ) ≤ 1 * exp 10 := by gcongr
      _ ≤ 20 * exp 10 := by nlinarith [exp_pos 10]

/-- The derivatives of `y` are at most `A = 16 e^{20} (20 e^{10})` on the ball of radius `20`. -/
theorem norm_iteratedFDeriv_logGap_le {X : ℝ} (hX : 2 ≤ X) {i : ℕ} (hi : i ≤ 4)
    {p : ℝ × ℝ} (hp : ‖p‖ ≤ 20) :
    ‖iteratedFDeriv ℝ i (logGap X) p‖ ≤ 16 * exp 20 * (20 * exp 10) := by
  have h1 : ‖p.1‖ ≤ 20 := (le_max_left _ _).trans hp
  have h2 : ‖p.2‖ ≤ 20 := (le_max_right _ _).trans hp
  have hg : ContDiff ℝ ∞ fun ζ => X * (exp (ζ / X) - 1) :=
    contDiff_const.mul ((contDiff_exp.comp (contDiff_id.div_const X)).sub contDiff_const)
  -- `y = (exp ∘ snd) (g ∘ fst)`
  have hy : logGap X = fun p => (exp ∘ ContinuousLinearMap.snd ℝ ℝ ℝ) p *
      ((fun ζ => X * (exp (ζ / X) - 1)) ∘ ContinuousLinearMap.fst ℝ ℝ ℝ) p := rfl
  rw [hy]
  refine (norm_iteratedFDeriv_mul_le (contDiff_exp.comp (ContinuousLinearMap.snd ℝ ℝ ℝ).contDiff)
    (hg.comp (ContinuousLinearMap.fst ℝ ℝ ℝ).contDiff) p (by exact_mod_cast le_top)).trans ?_
  have hterm : ∀ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
      ‖iteratedFDeriv ℝ j (exp ∘ ContinuousLinearMap.snd ℝ ℝ ℝ) p‖ *
      ‖iteratedFDeriv ℝ (i - j)
        ((fun ζ => X * (exp (ζ / X) - 1)) ∘ ContinuousLinearMap.fst ℝ ℝ ℝ) p‖ ≤
      (i.choose j : ℝ) * (exp 20 * (20 * exp 10)) := by
    intro j _
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_ (norm_nonneg _) (exp_pos _).le)
      (Nat.cast_nonneg _)
    · refine (norm_iteratedFDeriv_comp_clm_le (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
        contDiff_exp j p).trans ?_
      rw [iteratedDeriv_eq_iterate, iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.2 ((le_abs_self _).trans h2)
    · exact (norm_iteratedFDeriv_comp_clm_le (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ) hg _ p).trans
        (norm_iteratedDeriv_gap_le hX _ h1)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
  have h16 : (2 : ℝ) ^ i ≤ 16 := by
    calc (2 : ℝ) ^ i ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hi
      _ = 16 := by norm_num
  push_cast
  rw [mul_assoc 16]
  exact mul_le_mul_of_nonneg_right h16 (by positivity)

/-- `Φ` is smooth when `φ` is. -/
theorem contDiff_gapKernel {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (X : ℝ) :
    ContDiff ℝ ∞ (gapKernel φ X) :=
  (hφ.comp (contDiff_logGap X)).mul (Complex.ofRealCLM.contDiff.comp
    ((contDiff_plateau.comp (contDiff_fst.div_const 4)).mul
      (contDiff_plateau.comp (contDiff_snd.div_const 4))))

/-- `Φ` vanishes outside the ball of radius `20`. -/
theorem gapKernel_eq_zero (φ : ℝ → ℂ) (X : ℝ) {p : ℝ × ℝ} (hp : 20 < ‖p‖) :
    gapKernel φ X p = 0 := by
  rcases lt_max_iff.1 hp with h | h
  · have : 5 ≤ |p.1 / 4| := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), le_div_iff₀ (by norm_num)]
      rw [Real.norm_eq_abs] at h
      linarith
    simp [gapKernel, plateau_eq_zero this]
  · have : 5 ≤ |p.2 / 4| := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), le_div_iff₀ (by norm_num)]
      rw [Real.norm_eq_abs] at h
      linarith
    simp [gapKernel, plateau_eq_zero this]

/-- `‖D^n Φ‖ ≤ B K` for `n ≤ 4`, uniformly in `X ≥ 2`, when `‖D^i φ‖ ≤ K` for `i ≤ 4`. -/
theorem exists_norm_iteratedFDeriv_gapKernel_le : ∃ B : ℝ, 0 ≤ B ∧ ∀ (φ : ℝ → ℂ) (X K : ℝ),
    ContDiff ℝ ∞ φ → 2 ≤ X → (∀ i ≤ 4, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ K) →
      ∀ n ≤ 4, ∀ p, ‖iteratedFDeriv ℝ n (gapKernel φ X) p‖ ≤ B * K := by
  -- the cutoff has bounded derivatives
  set c : ℝ × ℝ → ℂ := fun p => ((plateau (p.1 / 4) * plateau (p.2 / 4) : ℝ) : ℂ) with hc
  have hcd : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp
    ((contDiff_plateau.comp (contDiff_fst.div_const 4)).mul
      (contDiff_plateau.comp (contDiff_snd.div_const 4)))
  have hcs : HasCompactSupport c := by
    refine HasCompactSupport.intro (isCompact_closedBall 0 20) fun p hp => ?_
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hp
    have h := gapKernel_eq_zero (fun _ => 1) 0 hp
    simp only [gapKernel, one_mul] at h
    exact h
  obtain ⟨Q, hQ⟩ := exists_norm_iteratedFDeriv_le hcd hcs 4
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ 0 (Nat.zero_le _) 0)
  set A : ℝ := 16 * exp 20 * (20 * exp 10) with hA
  have hA1 : 1 ≤ A := by
    have h20 := add_one_le_exp 20
    have h10 := add_one_le_exp 10
    calc (1 : ℝ) ≤ 16 * 1 * (20 * 1) := by norm_num
      _ ≤ 16 * exp 20 * (20 * exp 10) := by gcongr <;> linarith
  refine ⟨16 * (24 * A ^ 4) * Q, by positivity, fun φ X K hφ hX hK n hn p => ?_⟩
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (Nat.zero_le _) 0)
  rcases le_or_gt ‖p‖ 20 with hp | hp
  · -- Faà di Bruno for `φ ∘ y`
    have hcomp : ∀ j ≤ 4, ‖iteratedFDeriv ℝ j (φ ∘ logGap X) p‖ ≤ 24 * A ^ 4 * K := by
      intro j hj
      refine (norm_iteratedFDeriv_comp_le hφ (contDiff_logGap X)
        (by exact_mod_cast le_top) p (fun i hi => hK i (hi.trans hj) _)
        fun i hi1 hi => (norm_iteratedFDeriv_logGap_le hX (hi.trans hj) hp).trans
          (le_self_pow₀ hA1 (by omega))).trans ?_
      have hf : (j.factorial : ℝ) ≤ 24 := by
        have : j.factorial ≤ (4 : ℕ).factorial := Nat.factorial_le hj
        exact_mod_cast this
      have hAj : A ^ j ≤ A ^ 4 := pow_le_pow_right₀ hA1 hj
      calc (j.factorial : ℝ) * K * A ^ j ≤ 24 * K * A ^ 4 := by gcongr
        _ = 24 * A ^ 4 * K := by ring
    -- Leibniz for the product with the cutoff
    have hk : gapKernel φ X = fun p => (φ ∘ logGap X) p * c p := rfl
    rw [hk]
    refine (norm_iteratedFDeriv_mul_le (hφ.comp (contDiff_logGap X))
      hcd p (by exact_mod_cast le_top)).trans ?_
    have hterm : ∀ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j (φ ∘ logGap X) p‖ *
        ‖iteratedFDeriv ℝ (n - j) c p‖ ≤ (n.choose j : ℝ) * (24 * A ^ 4 * K * Q) := by
      intro j hj
      have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hcomp j (hj'.trans hn))
        (hQ _ ((Nat.sub_le n j).trans hn) p) (norm_nonneg _) (by positivity)) (Nat.cast_nonneg _)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
    have h16 : (2 : ℝ) ^ n ≤ 16 := by
      calc (2 : ℝ) ^ n ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hn
        _ = 16 := by norm_num
    push_cast
    calc (2 : ℝ) ^ n * (24 * A ^ 4 * K * Q) ≤ 16 * (24 * A ^ 4 * K * Q) :=
          mul_le_mul_of_nonneg_right h16 (by positivity)
      _ = 16 * (24 * A ^ 4) * Q * K := by ring
  · -- outside the ball `Φ` vanishes near `p`
    have h : gapKernel φ X =ᶠ[nhds p] fun _ => 0 :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hp)
        fun q hq => gapKernel_eq_zero φ X hq
    rw [(h.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    positivity

/-- `|log w - log w'| ≤ |w - w'|` for `w, w' ≥ 1`. -/
theorem abs_log_sub_log_le {w w' : ℝ} (hw : 1 ≤ w) (hw' : 1 ≤ w') :
    |log w - log w'| ≤ |w - w'| := by
  have h : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → log a - log b ≤ |a - b| := fun a b ha hb => by
    rw [← log_div (by positivity) (by positivity)]
    refine (log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
    rcases le_total 0 (a - b) with hab | hab
    · rw [abs_of_nonneg hab]
      nlinarith
    · nlinarith [abs_nonneg (a - b)]
  rw [abs_le]
  constructor
  · have := h w' w hw' hw
    rw [abs_sub_comm] at this
    linarith
  · exact h w w' hw hw'

/-- For `w, w' ≥ 1` and `w' ≤ 16`, the cut-off kernel is `φ(X(w - w'))`, when `φ` vanishes
outside `(-5, 5)`. -/
theorem gapKernel_log {φ : ℝ → ℂ} (hφ : ∀ y, 5 ≤ |y| → φ y = 0) {X : ℝ} (hX : 0 < X)
    {w w' : ℝ} (hw : 1 ≤ w) (hw' : 1 ≤ w') (hw'16 : w' ≤ 16) :
    gapKernel φ X (X * (log w - log w'), log w') = φ (X * (w - w')) := by
  -- `y(X log(w/w'), log w') = X(w - w')`
  have hy : logGap X (X * (log w - log w'), log w') = X * (w - w') := by
    simp only [logGap]
    rw [mul_div_cancel_left₀ _ hX.ne', exp_sub, exp_log (by positivity),
      exp_log (by positivity)]
    field_simp
  have hz : plateau (log w' / 4) = 1 := by
    refine plateau_eq_one ?_
    have h0 : 0 ≤ log w' := log_nonneg hw'
    have h1 : log w' ≤ w' - 1 := log_le_sub_one_of_pos (by positivity)
    rw [abs_of_nonneg (by positivity)]
    linarith
  rw [gapKernel, hy, hz, mul_one]
  by_cases h : φ (X * (w - w')) = 0
  · rw [h, zero_mul]
  · -- `|ζ| ≤ X |w - w'| < 5`
    have h5 : |X * (w - w')| < 5 := by
      by_contra h'
      exact h (hφ _ (not_lt.1 h'))
    have hζ : plateau (X * (log w - log w') / 4) = 1 := by
      refine plateau_eq_one ?_
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_mul, abs_of_pos hX]
      rw [abs_mul, abs_of_pos hX] at h5
      have := mul_le_mul_of_nonneg_left (abs_log_sub_log_le hw hw') hX.le
      linarith
    rw [hζ, Complex.ofReal_one, mul_one]

end Erdos408.OneSided.Mellin
