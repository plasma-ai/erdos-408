import Erdos408.Extraction.Sieve.Smooth
import Erdos408.TwoSided.Setup

/-!
# Twisted sums over progressions

Step 3 of Lemma E2 (`blueprint/two_sided_correlation.md` §6.2, (6.29)). For `m` coprime to
`k` and `f(0) = 0`, the twisted sum `∑_{w ≤ N, m ∣ w} f(w) e(hw/k)` is
`κ_{h,k} m⁻¹ ∑_{w ≤ N} f(w)` up to `k` times the total variation of `f`, where
`κ_{h,k} = k⁻¹ ∑_{a < k} e(ha/k)` does not depend on `m`. The main terms therefore cancel
against `C_B` without comparing the full sum with an integral.

* `LowFreq.norm_sum_modEq_sub_le`: the complex form of `Sieve.abs_sum_modEq_sub_le`.
* `LowFreq.norm_sum_dvd_twist_sub_le`: the twisted progression sum.
* `LowFreq.sum_norm_sub_le`: the total variation of `w ↦ ψ₁(w/Y) w^{iτ}` on `[1, N]` is at
  most `N (M₁(1) + |τ| M₁(0)) / Y`.
-/

namespace Erdos408.TwoSided.LowFreq

open Finset

/-- The additive character `e(h w / k)`. -/
noncomputable def addTwist (h : ℤ) (k w : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (h * w / k : ℝ))

/-- The complete average `κ_{h,k} = k⁻¹ ∑_{a < k} e(h a / k)`. -/
noncomputable def twistMean (h : ℤ) (k : ℕ) : ℂ :=
  (k : ℂ)⁻¹ * ∑ a ∈ range k, addTwist h k a

/-- `|e(hw/k)| = 1`. -/
theorem norm_addTwist (h : ℤ) (k w : ℕ) : ‖addTwist h k w‖ = 1 := by
  rw [addTwist, Complex.norm_exp]
  simp

/-- `e(hw/k)` depends only on `w mod k`. -/
theorem addTwist_mod (h : ℤ) {k : ℕ} (hk : 0 < k) (w : ℕ) :
    addTwist h k w = addTwist h k (w % k) := by
  unfold addTwist
  have hw : (w : ℝ) = k * (w / k : ℕ) + (w % k : ℕ) := by
    exact_mod_cast (Nat.div_add_mod w k).symm
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have : (h * w / k : ℝ) = ((h * (w / k : ℕ) : ℤ) : ℝ) + h * (w % k : ℕ) / k := by
    rw [Int.cast_mul, Int.cast_natCast]
    nth_rewrite 1 [hw]
    field_simp
  rw [this, Complex.ofReal_add, mul_add, Complex.exp_add]
  have h1 : Complex.exp (2 * Real.pi * Complex.I * ((h * (w / k : ℕ) : ℤ) : ℝ)) = 1 := by
    rw [← Complex.exp_int_mul_two_pi_mul_I (h * (w / k : ℕ))]
    congr 1
    push_cast
    ring
  rw [h1, one_mul]

/-- `f(u) = ∑_{1 ≤ m ≤ u} (f(m) - f(m-1))` when `f(0) = 0`. -/
theorem eq_sum_Icc_sub {f : ℕ → ℂ} (hf0 : f 0 = 0) (u : ℕ) :
    f u = ∑ m ∈ Icc 1 u, (f m - f (m - 1)) := by
  induction u with
  | zero => simp [hf0]
  | succ u ih => rw [sum_Icc_succ_top (by omega), ← ih, Nat.add_sub_cancel]; ring

/-- A sum over `[1, N]` restricted by a condition, through the increments of `f`. -/
theorem sum_filter_eq_sum_sub {f : ℕ → ℂ} (hf0 : f 0 = 0) (N : ℕ) (p : ℕ → Prop)
    [DecidablePred p] :
    ∑ u ∈ (Icc 1 N).filter p, f u =
      ∑ m ∈ Icc 1 N, (f m - f (m - 1)) * #((Icc m N).filter p) := by
  rw [sum_congr rfl fun u _ => eq_sum_Icc_sub hf0 u]
  rw [sum_comm' (t' := Icc 1 N) (s' := fun m => (Icc m N).filter p)]
  · refine sum_congr rfl fun m _ => ?_
    rw [sum_const, nsmul_eq_mul, mul_comm]
  · intro u m
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩
      exact ⟨⟨⟨h5, h2⟩, h3⟩, h4, h5.trans h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩
      exact ⟨⟨⟨h4.trans h1, h2⟩, h3⟩, h4, h1⟩

/-- A complex sum over a residue class modulo `q` in `[1, N]` is `1/q` of the full sum, up to
the total variation. -/
theorem norm_sum_modEq_sub_le {q : ℕ} (hq : 0 < q) (v N : ℕ) {f : ℕ → ℂ} (hf0 : f 0 = 0) :
    ‖∑ u ∈ (Icc 1 N).filter (· ≡ v [MOD q]), f u - (1 / q : ℂ) * ∑ u ∈ Icc 1 N, f u‖ ≤
      ∑ m ∈ Icc 1 N, ‖f m - f (m - 1)‖ := by
  have hfull : ∑ u ∈ Icc 1 N, f u =
      ∑ m ∈ Icc 1 N, (f m - f (m - 1)) * ((N + 1 - m : ℕ) : ℂ) := by
    have := sum_filter_eq_sum_sub hf0 N (fun _ => True)
    rw [filter_true_of_mem fun _ _ => trivial] at this
    rw [this]
    refine sum_congr rfl fun m _ => ?_
    rw [filter_true_of_mem fun _ _ => trivial, Nat.card_Icc]
  rw [sum_filter_eq_sum_sub hf0, hfull, mul_sum, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
  obtain ⟨hm1, hmN⟩ := mem_Icc.1 hm
  have h := Sieve.abs_card_modEq_sub_le hq v hm1 (by omega : m ≤ N + 1)
  rw [show (f m - f (m - 1)) * (#((Icc m N).filter (· ≡ v [MOD q])) : ℂ) -
      1 / q * ((f m - f (m - 1)) * ((N + 1 - m : ℕ) : ℂ)) =
      (f m - f (m - 1)) * (((#((Icc m N).filter (· ≡ v [MOD q])) : ℝ) -
        ((N + 1 - m : ℕ) : ℝ) / q : ℝ) : ℂ) by push_cast; ring, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _) h

/-- By the Chinese remainder theorem, `m ∣ w ∧ w ≡ a (mod k)` is a residue class modulo
`m k`, for coprime `m, k`. -/
theorem exists_modEq_iff {m k : ℕ} (hmk : Nat.Coprime m k) (a : ℕ) :
    ∃ v, ∀ w, (m ∣ w ∧ w ≡ a [MOD k]) ↔ w ≡ v [MOD m * k] := by
  obtain ⟨v, hv₁, hv₂⟩ := Nat.chineseRemainder hmk 0 a
  refine ⟨v, fun w => ?_⟩
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hmk, ← Nat.modEq_zero_iff_dvd]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁.trans hv₁.symm, h₂.trans hv₂.symm⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁.trans hv₁, h₂.trans hv₂⟩

/-- **The twisted progression sum (6.29).** For `m ≥ 1` coprime to `k ≥ 1` and `f(0) = 0`,
`∑_{w ≤ N, m ∣ w} f(w) e(hw/k) = κ_{h,k} m⁻¹ ∑_{w ≤ N} f(w)` up to `k` times the total
variation of `f`. -/
theorem norm_sum_dvd_twist_sub_le {m k : ℕ} (hm : 0 < m) (hk : 0 < k) (hmk : Nat.Coprime m k)
    (h : ℤ) (N : ℕ) {f : ℕ → ℂ} (hf0 : f 0 = 0) :
    ‖∑ w ∈ (Icc 1 N).filter (m ∣ ·), f w * addTwist h k w -
        twistMean h k * (∑ w ∈ Icc 1 N, f w) / m‖ ≤
      k * ∑ w ∈ Icc 1 N, ‖f w - f (w - 1)‖ := by
  -- split by the residue of `w` modulo `k`
  have hsplit : ∑ w ∈ (Icc 1 N).filter (m ∣ ·), f w * addTwist h k w =
      ∑ a ∈ range k, addTwist h k a *
        ∑ w ∈ ((Icc 1 N).filter (m ∣ ·)).filter (fun w => w % k = a), f w := by
    rw [← sum_fiberwise_of_maps_to (g := (· % k)) (t := range k)
      (fun w _ => mem_range.2 (Nat.mod_lt w hk))]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun w hw => ?_
    rw [addTwist_mod h hk w, (mem_filter.1 hw).2, mul_comm]
  have hclass : ∀ a ∈ range k, ∃ v, ((Icc 1 N).filter (m ∣ ·)).filter (fun w => w % k = a) =
      (Icc 1 N).filter (· ≡ v [MOD m * k]) := by
    intro a ha
    obtain ⟨v, hv⟩ := exists_modEq_iff hmk a
    refine ⟨v, ?_⟩
    rw [filter_filter]
    refine filter_congr fun w _ => ?_
    rw [← hv]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt (mem_range.1 ha)]
  have hmain : twistMean h k * (∑ w ∈ Icc 1 N, f w) / m =
      ∑ a ∈ range k, addTwist h k a * ((1 / ((m * k : ℕ) : ℂ)) * ∑ w ∈ Icc 1 N, f w) := by
    rw [← sum_mul, twistMean]
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast
    field_simp
  rw [hsplit, hmain, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a ∈ range k, ‖addTwist h k a *
        ∑ w ∈ ((Icc 1 N).filter (m ∣ ·)).filter (fun w => w % k = a), f w -
          addTwist h k a * ((1 / ((m * k : ℕ) : ℂ)) * ∑ w ∈ Icc 1 N, f w)‖
      ≤ ∑ _a ∈ range k, ∑ w ∈ Icc 1 N, ‖f w - f (w - 1)‖ := by
        refine sum_le_sum fun a ha => ?_
        obtain ⟨v, hv⟩ := hclass a ha
        rw [← mul_sub, norm_mul, norm_addTwist, one_mul, hv]
        have := norm_sum_modEq_sub_le (Nat.mul_pos hm hk) v N hf0
        push_cast at this ⊢
        exact this
    _ = k * ∑ w ∈ Icc 1 N, ‖f w - f (w - 1)‖ := by
        rw [sum_const, card_range, nsmul_eq_mul]

/-- `|v^{iτ} - u^{iτ}| ≤ |τ| (v - u)/u` for `0 < u ≤ v`. -/
theorem norm_cpow_sub_cpow_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (τ : ℝ) :
    ‖(v : ℂ) ^ ((τ : ℂ) * Complex.I) - (u : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ≤
      |τ| * (v - u) / u := by
  have hv : 0 < v := hu.trans_le huv
  have hcpow : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ ((τ : ℂ) * Complex.I) = Complex.exp (Complex.I * ((τ * Real.log y : ℝ) : ℂ)) := by
    intro y hy
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), ← Complex.ofReal_log hy.le]
    congr 1
    push_cast
    ring
  rw [hcpow v hv, hcpow u hu]
  have hsplit : Complex.exp (Complex.I * ((τ * Real.log v : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((τ * Real.log u : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((τ * Real.log u : ℝ) : ℂ)) *
        (Complex.exp (Complex.I * ((τ * Real.log v - τ * Real.log u : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hsplit, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_self, Real.exp_zero, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
  have hlog : 0 ≤ Real.log v - Real.log u := by
    linarith [Real.log_le_log hu huv]
  have hlog' : Real.log v - Real.log u ≤ (v - u) / u := by
    rw [← Real.log_div hv.ne' hu.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hv hu)).trans_eq ?_
    field_simp
  rw [abs_of_nonneg hlog, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hlog' (abs_nonneg τ)

/-- **The total variation of the smooth weight.** For `ψ₁` differentiable with
`|ψ₁| ≤ M₁(0)`, `|ψ₁'| ≤ M₁(1)` and `ψ₁(y) ≠ 0 → y ≥ 1`, and `Y > 0`, the weight
`w ↦ ψ₁(w/Y) w^{iτ}` has total variation `≤ N (M₁(1) + |τ| M₁(0)) / Y` on `[1, N]`. -/
theorem sum_norm_sub_le {ψ₁ : ℝ → ℂ} (hd : Differentiable ℝ ψ₁) {M₀ M₁ : ℝ}
    (h₀ : ∀ y, ‖ψ₁ y‖ ≤ M₀) (h₁ : ∀ y, ‖deriv ψ₁ y‖ ≤ M₁) (hs : ∀ y, ψ₁ y ≠ 0 → 1 ≤ y)
    {Y : ℝ} (hY : 0 < Y) (τ : ℝ) (N : ℕ) :
    ∑ w ∈ Icc 1 N, ‖ψ₁ (w / Y) * (w : ℂ) ^ ((τ : ℂ) * Complex.I) -
        ψ₁ ((w - 1 : ℕ) / Y) * ((w - 1 : ℕ) : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ≤
      N * ((M₁ + |τ| * M₀) / Y) := by
  have hterm : ∀ w ∈ Icc 1 N, ‖ψ₁ (w / Y) * (w : ℂ) ^ ((τ : ℂ) * Complex.I) -
      ψ₁ ((w - 1 : ℕ) / Y) * ((w - 1 : ℕ) : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ≤
        (M₁ + |τ| * M₀) / Y := by
    intro w hw
    have hw1 := (mem_Icc.1 hw).1
    have hcast : ((w - 1 : ℕ) : ℝ) = w - 1 := by rw [Nat.cast_sub hw1, Nat.cast_one]
    have hw0 : (0 : ℝ) < w := by exact_mod_cast hw1
    have hsplit : ψ₁ (w / Y) * (w : ℂ) ^ ((τ : ℂ) * Complex.I) -
        ψ₁ ((w - 1 : ℕ) / Y) * ((w - 1 : ℕ) : ℂ) ^ ((τ : ℂ) * Complex.I) =
        (ψ₁ (w / Y) - ψ₁ ((w - 1 : ℕ) / Y)) * (w : ℂ) ^ ((τ : ℂ) * Complex.I) +
          ψ₁ ((w - 1 : ℕ) / Y) * ((w : ℂ) ^ ((τ : ℂ) * Complex.I) -
            ((w - 1 : ℕ) : ℂ) ^ ((τ : ℂ) * Complex.I)) := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    -- the change of `ψ₁`
    have hA : ‖(ψ₁ (w / Y) - ψ₁ ((w - 1 : ℕ) / Y)) * (w : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ≤
        M₁ / Y := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hw1]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
        Complex.I_im, mul_one, sub_self, Real.rpow_zero, mul_one]
      have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (fun y _ => hd y)
        (fun y _ => h₁ y) convex_univ (Set.mem_univ (((w - 1 : ℕ) : ℝ) / Y))
        (Set.mem_univ ((w : ℝ) / Y))
      refine this.trans_eq ?_
      rw [hcast, show (w : ℝ) / Y - (w - 1) / Y = 1 / Y by ring, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      ring
    -- the change of `w^{iτ}`
    have hB : ‖ψ₁ ((w - 1 : ℕ) / Y) * ((w : ℂ) ^ ((τ : ℂ) * Complex.I) -
        ((w - 1 : ℕ) : ℂ) ^ ((τ : ℂ) * Complex.I))‖ ≤ |τ| * M₀ / Y := by
      by_cases h0 : ψ₁ ((w - 1 : ℕ) / Y) = 0
      · rw [h0, zero_mul, norm_zero]
        have := (norm_nonneg (ψ₁ 0)).trans (h₀ 0)
        positivity
      · have h1 := hs _ h0
        rw [le_div_iff₀ hY, one_mul] at h1
        have hu : (0 : ℝ) < ((w - 1 : ℕ) : ℝ) := hY.trans_le h1
        have hle : ((w - 1 : ℕ) : ℝ) ≤ w := by rw [hcast]; linarith
        rw [norm_mul]
        have hc := norm_cpow_sub_cpow_le hu hle τ
        rw [Complex.ofReal_natCast, Complex.ofReal_natCast] at hc
        have hdiff : |τ| * ((w : ℝ) - ((w - 1 : ℕ) : ℝ)) / ((w - 1 : ℕ) : ℝ) ≤ |τ| / Y := by
          rw [hcast, sub_sub_cancel, mul_one, ← hcast]
          exact div_le_div_of_nonneg_left (abs_nonneg τ) hY h1
        calc ‖ψ₁ ((w - 1 : ℕ) / Y)‖ * ‖(w : ℂ) ^ ((τ : ℂ) * Complex.I) -
              ((w - 1 : ℕ) : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ≤ M₀ * (|τ| / Y) :=
              mul_le_mul (h₀ _) (hc.trans hdiff) (norm_nonneg _)
                ((norm_nonneg (ψ₁ 0)).trans (h₀ 0))
          _ = |τ| * M₀ / Y := by ring
    calc _ ≤ M₁ / Y + |τ| * M₀ / Y := add_le_add hA hB
      _ = (M₁ + |τ| * M₀) / Y := by ring
  calc _ ≤ ∑ _w ∈ Icc 1 N, (M₁ + |τ| * M₀) / Y := sum_le_sum hterm
    _ = N * ((M₁ + |τ| * M₀) / Y) := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp

end Erdos408.TwoSided.LowFreq
