import Erdos408.TwoSided.Endpoint.Tuple.Assembly

/-!
# The tuple part at high times, for a general coefficient: the statement

S13–S18 of `blueprint/two_sided_correlation.md` §§6.3–6.6 (PD §§6.5–6.6; blueprint §1.3 for
the order of the constants). For the tuple sum with small primes in `[e^{L^{0.27}}, e^{L^{0.36}}]`,
`V ≥ v₋`, spare primes in `(A, B]` with `x^ε ≤ A`, `B ≤ x^{1-ε}`, and `|c| ≤ L^{C_U}` on
`[1, x²]`: there are `A'` and `B_min` such that for every `E, κ'` and `B' ≥ max(B_min,
E + B_min)` there is `C_T`, with the mean square over any interval of times
`L^{B'} ≤ |t| ≤ T₀` at most `C_T L^{-A₀}` under AP1 and AP2. The constants are
`A_s = max((A₀ + D)/2, 1)`, `A' = (A₀ + D - 1)/2` and `A_t = max(A₀ + D - K₁, 1)` with
`D = 6C_m + 2K₁ + 2C_U + 11`, and `B_min = max(C_m, C_sep) + 2`; `A'` does not depend on `E`.
-/

namespace Erdos408.TwoSided.TupleHigh

open Filter Finset MeasureTheory

/-- **The tuple part at high times, for a general coefficient.** -/
theorem exists_integral_tupleSum_high_le (vlo c Cm CU A₀ : ℝ) (hvlo : 0 < vlo) (hc : 0 < c)
    (M₁ : ℕ → ℝ) :
    ∃ A' Bmin : ℝ, ∀ E κ' B' : ℝ, Bmin ≤ B' → E + Bmin ≤ B' → ∃ CT : ℝ, 0 ≤ CT ∧
      ∀ᶠ x : ℝ in atTop,
        PrimeTwistBound x A' E Cm κ' → IntegerKernelBound x Cm κ' →
        ∀ (s : Finset ℕ) (V A B : ℝ) (cf : ℕ → ℂ) (ψ₁ : ℝ → ℂ) (Y σ : ℝ) (k : ℕ) (h : ℤ),
          (∀ p ∈ s, p.Prime ∧ Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ p ∧
            (p : ℝ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ))) →
          vlo ≤ V → Real.exp (c * Real.log x / Real.log (Real.log x) ^ 20) ≤ A →
          B ≤ x * Real.exp (-(c * Real.log x / Real.log (Real.log x) ^ 20)) →
          (∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ x ^ 2 → ‖cf u‖ ≤ Real.log x ^ CU) →
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁ → (∀ y, ψ₁ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) →
          (∀ (j : ℕ) (y : ℝ), ‖iteratedDeriv j ψ₁ y‖ ≤ M₁ j) →
          x * Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ Y →
          Y ≤ x * Real.exp (Real.log x ^ (0.47 : ℝ)) →
          |σ| ≤ Real.log x ^ Cm → 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm →
          ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ →
            (∀ t ∈ Set.Icc t₁ t₂, Real.log x ^ B' ≤ |t| ∧ |t| ≤ x * Real.log x ^ (Cm + 2)) →
            ∫ t in t₁..t₂, ‖twistedPoly Y (fun w => ψ₁ (w / Y) *
                (w : ℂ) ^ ((σ : ℂ) * Complex.I) * ((V⁻¹ : ℝ) : ℂ) *
                ∑ ps ∈ s.filter (· ∣ w), ∑ pl ∈ ((Iic ⌊B⌋₊).filter fun p : ℕ =>
                  p.Prime ∧ A < p).filter (· ∣ w / ps), cf (w / ps / pl)) h k t‖ ^ 2 ≤
              CT * Real.log x ^ (-A₀) := by
  obtain ⟨Cf, K, hCf, hK, hmel⟩ := exists_mellin_piece M₁
  by_cases hCm : 0 ≤ Cm
  swap
  · -- `C_m < 0`: no modulus `k ≥ 1` has `k ≤ L^{C_m}`
    refine ⟨0, 0, fun E κ' B' _ _ => ⟨0, le_rfl, ?_⟩⟩
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 1] with x hL
    intro _ _ s V A B cf ψ₁ Y σ k h _ _ _ _ _ _ _ _ _ _ _ hk₁ hk₂
    have : Real.log x ^ Cm < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL (lt_of_not_ge hCm)
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk₁
    linarith
  set D := 6 * Cm + 6 + 2 * K + 2 * CU + 5 with hD
  set As := max ((A₀ + D) / 2) 1 with hAs
  have hAs0 : 0 < As := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(A₀ + D - 1) / 2, max Cm Cf + 2, fun E κ' B' hB₁ hB₂ => ?_⟩
  set At := max (A₀ + (6 * Cm + 6 + K + 2 * CU + 5)) 1 with hAt
  obtain ⟨KA, hKA, hmelx⟩ := hmel At (lt_of_lt_of_le one_pos (le_max_right _ _))
  refine ⟨4096 * (1 + (2 / vlo) ^ 2 * 4 * 16 * κ' ^ 2 * (9 * (1 + |κ'|)) + (2 / vlo) ^ 2 * KA),
    by positivity, ?_⟩
  filter_upwards [hmelx, eventually_tupleFacts hc Cm,
    eventually_boxTwistBound Cm CU vlo As hvlo hCm hAs0] with x hmelx hf hB2
  intro hAP1 hAP2 s V A B cf ψ₁ Y σ k h hs hV hA hB hcf hψ hψs hψd hY₁ hY₂ hσ hk₁ hk₂ t₁ t₂
    h₁₂ hrange
  obtain ⟨a, hai, ha₁, harep, hat⟩ := hmelx ψ₁ hψ hψs hψd
  set L := Real.log x with hLdef
  have hL : 28 ≤ L := hf.big
  have hL1 : 1 ≤ L := by linarith
  have hx0 : 0 < x := by linarith [hf.box.2.1]
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY₁
  set e := Real.exp (c * L / Real.log L ^ 20) with he
  have hxe : x / e ≤ x := div_le_self hx0.le (Real.one_le_exp (by positivity))
  have hBx : B ≤ x / e := by
    rw [div_eq_mul_inv, he, ← Real.exp_neg]
    exact hB
  set sp := (Iic ⌊B⌋₊).filter fun p : ℕ => p.Prime ∧ A < p with hsp
  have hspP : ∀ p ∈ sp, p.Prime ∧ A < p ∧ (p : ℝ) ≤ B := by
    intro p hp
    obtain ⟨hp₁, hp₂, hp₃⟩ := mem_filter.1 hp
    have hB0 : 0 ≤ B := by
      by_contra hneg
      push Not at hneg
      have h := mem_Iic.1 hp₁
      rw [Nat.floor_of_nonpos hneg.le] at h
      have := hp₂.two_le
      omega
    exact ⟨hp₂, hp₃, (Nat.le_floor_iff hB0).1 (mem_Iic.1 hp₁)⟩
  obtain ⟨hN₀1, hN₀L, hN₀x⟩ := boxCount_facts hx0 hL1
  set N₀ := ⌈3 * L⌉₊ with hN₀
  have hYx : 2 * Y ≤ x ^ 2 := by
    have h := hf.box.2.2.2.1
    have : x * Real.exp (L ^ (0.47 : ℝ)) ≤ x * (x / 16) :=
      mul_le_mul_of_nonneg_left (by linarith) hx0.le
    nlinarith
  have hbox : ∀ p : ℕ, (p : ℝ) ≤ x ^ 2 → boxIndex p < N₀ := fun p hp =>
    boxIndex_lt hN₀1 (by exact_mod_cast hp.trans hN₀x)
  have h36x : Real.exp (L ^ (0.36 : ℝ)) ≤ x / 2 := by
    have h₁ := hf.m36
    have h₂ := hf.m47
    have h₃ : Real.exp (L ^ (0.36 : ℝ)) ≤ Real.exp (L ^ (0.47 : ℝ)) :=
      Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
    have h₄ := hf.box.2.2.2.1
    linarith [Real.exp_pos (L ^ (0.47 : ℝ))]
  have hx2 : x ≤ x ^ 2 := by nlinarith [hf.box.2.1]
  -- the decomposition by boxes, classes and characters
  have hdecomp := twistedPoly_eq_sum_boxTerm (V := V) hY0 s sp
    (fun p hp => (hs p hp).1.pos) (fun p hp => (hspP p hp).1.pos)
    (fun ps hps pl hpl => by
      have h₁ := (hs ps hps).2.2
      have h₂ := (hspP pl hpl).2.2
      have he1 : 2 * Real.exp (L ^ (0.36 : ℝ)) ≤ e := hf.m36
      push_cast
      calc (ps : ℝ) * pl ≤ Real.exp (L ^ (0.36 : ℝ)) * (x / e) :=
            mul_le_mul h₁ (h₂.trans hBx) (Nat.cast_nonneg _) (by positivity)
        _ < x := by
            rw [mul_div_assoc', div_lt_iff₀ (Real.exp_pos _)]
            nlinarith [Real.exp_pos (L ^ (0.36 : ℝ))]
        _ ≤ Y := le_trans (le_mul_of_one_le_right hx0.le (Real.one_le_exp (by positivity)))
            hY₁)
    ψ₁ hψs cf σ hk₁ h
    (fun p hp => hbox p (by linarith [(hs p hp).2.2]))
    (fun p hp => hbox p (by linarith [(hspP p hp).2.2]))
    (fun u hu => hbox u (by
      have := (mem_Ioc.1 hu).2
      have : (u : ℝ) ≤ 2 * Y := (Nat.cast_le.2 this).trans (Nat.floor_le (by linarith))
      linarith))
    (fun p hp => by
      have hpP := (hspP p hp).1
      refine (Nat.Prime.coprime_iff_not_dvd hpP).2 fun hdvd => ?_
      have hpk := Nat.le_of_dvd (by omega) hdvd
      have : (p : ℝ) ≤ k := by exact_mod_cast hpk
      have : 2 * L ^ Cm ≤ e := hf.mCm
      have : 0 < L ^ Cm := by positivity
      linarith [(hspP p hp).2.1])
  simp_rw [hdecomp]
  -- Cauchy–Schwarz over the indices, and each term
  have : NeZero k := ⟨by omega⟩
  have hlen : t₂ - t₁ ≤ 4 * (x * L ^ (Cm + 2)) := by
    have h₁ := (hrange t₁ ⟨le_rfl, h₁₂⟩).2
    have h₂ := (hrange t₂ ⟨h₁₂, le_rfl⟩).2
    have := le_abs_self t₂
    have := neg_abs_le t₁
    have : 0 ≤ x * L ^ (Cm + 2) := by positivity
    linarith
  have hrange' : ∀ t ∈ Set.Icc t₁ t₂, ∀ ξ : ℝ, |ξ| ≤ L ^ Cf →
      L ^ E ≤ |t + (σ + 2 * Real.pi * ξ)| ∧
        |t + (σ + 2 * Real.pi * ξ)| + 2 ≤ 2 * (x * L ^ (Cm + 2)) :=
    fun t ht ξ hξ => shifted_range hL hCf hB₁ hB₂ (hrange t ht).1 (hrange t ht).2 hσ hξ
  refine (integral_norm_sum_sq_le (boxSet N₀ k) _
    (fun m _ => Erdos821.P5Marked.norm_cchi_le k h m.2.2 _) _
    (fun m _ => continuous_boxTerm (fun p hp => (hs p hp).1.pos)
      (fun p hp => (hspP p hp).1.pos) cf ψ₁ σ m) h₁₂).trans ?_
  have hterm := fun m (_ : m ∈ boxSet N₀ k) => integral_boxTerm_le hc hvlo hCm hf hB2 hAP1
    hAP2 hai ha₁ harep hat hs hV hA hB hcf hψs hY₁ hY₂ hk₁ hk₂ h₁₂ hlen hrange' m
  refine (mul_le_mul_of_nonneg_left (sum_le_sum hterm) (Nat.cast_nonneg _)).trans ?_
  rw [sum_const, nsmul_eq_mul]
  -- the number of indices
  have hcard : (#(boxSet N₀ k) : ℝ) ≤ 64 * L ^ (3 * Cm + 3) := by
    have h₁ : (#(boxSet N₀ k) : ℝ) ≤ (N₀ : ℝ) ^ 3 * (k : ℝ) ^ 3 := by
      exact_mod_cast card_boxSet_le N₀ k
    have h₂ : (k : ℝ) ^ 3 ≤ L ^ (3 * Cm) := by
      calc (k : ℝ) ^ 3 ≤ (L ^ Cm) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hk₂ 3
        _ = L ^ (3 * Cm) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
            ring_nf
    have h₃ : (N₀ : ℝ) ^ 3 ≤ (4 * L) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN₀L 3
    have h₄ : (4 * L) ^ 3 * L ^ (3 * Cm) = 64 * L ^ (3 * Cm + 3) := by
      rw [Real.rpow_add (by linarith), mul_pow, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      ring
    calc (#(boxSet N₀ k) : ℝ) ≤ (N₀ : ℝ) ^ 3 * (k : ℝ) ^ 3 := h₁
      _ ≤ (4 * L) ^ 3 * L ^ (3 * Cm) := mul_le_mul h₃ h₂ (by positivity) (by positivity)
      _ = 64 * L ^ (3 * Cm + 3) := h₄
  exact tupleBound_le hL1 hvlo hKA.le (Nat.cast_nonneg _) hcard
    (by rw [hAs]; linarith [le_max_left ((A₀ + D) / 2) 1]) (by rw [hD]; ring)
    (le_max_left _ _)

end Erdos408.TwoSided.TupleHigh
