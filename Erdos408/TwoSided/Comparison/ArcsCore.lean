import Erdos408.TwoSided.Comparison.ArcsBound
import Erdos408.TwoSided.Comparison.ArcsLabels

/-!
# The pieces of the comparison bound

The concrete inputs of S6–S10 in `blueprint/two_sided_correlation.md` §§5.2–5.4 for one
comparison pattern, stated for the objects of `Defs.lean`:

* `sum_norm_endpointCoeff_sq_le`, `sum_norm_second_sq_le`: the endpoint energies (6.19).
* `norm_multiplier_le`: the multiplier off the arcs (C1, C2 on four boxes).
* `energy_le`: the main, tail and additive terms of the arc energy.
* `div_le_of_arcs`: the final count of the Proof of C.
-/

namespace Erdos408.TwoSided.Arcs

open Filter

/-- For `0 ≤ a < b`, eventually `c₁ L^a + c₂ ≤ L^b`. -/
theorem eventually_add_le_rpow {a b : ℝ} (c₁ c₂ : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    ∀ᶠ L : ℝ in atTop, c₁ * L ^ a + c₂ ≤ L ^ b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.2 hab)).eventually_ge_atTop (|c₁| + |c₂|),
    eventually_ge_atTop 1] with L h₁ hL
  have hLa : 1 ≤ L ^ a := Real.one_le_rpow hL ha
  have hsplit : L ^ b = L ^ (b - a) * L ^ a := by
    rw [← Real.rpow_add (by linarith)]
    ring_nf
  rw [hsplit]
  have h₂ : c₁ * L ^ a ≤ |c₁| * L ^ a := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have h₃ : c₂ ≤ |c₂| * L ^ a := (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hLa)
  have h₄ : (|c₁| + |c₂|) * L ^ a ≤ L ^ (b - a) * L ^ a :=
    mul_le_mul_of_nonneg_right h₁ (by linarith)
  linarith

/-- `|n^{-iσ}| ≤ 1`, including `n = 0`. -/
theorem norm_natCast_cpow_neg_le_one (n : ℕ) (σ : ℝ) :
    ‖(n : ℂ) ^ (-((σ : ℂ) * Complex.I))‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · by_cases h : -((σ : ℂ) * Complex.I) = 0
    · simp [h]
    · simp [Complex.zero_cpow h]
  · rw [Complex.norm_natCast_cpow_of_pos hn]
    simp

/-- `∑_t |h|² ≤ |t| b²` when `|h| ≤ b` on `t`. -/
private theorem sum_norm_sq_le_card_mul {t : Finset ℕ} {h : ℕ → ℂ} {b : ℝ}
    (hb : ∀ n ∈ t, ‖h n‖ ≤ b) : ∑ n ∈ t, ‖h n‖ ^ 2 ≤ t.card * b ^ 2 := by
  have := Finset.sum_le_card_nsmul t (fun n => ‖h n‖ ^ 2) (b ^ 2) fun n hn =>
    pow_le_pow_left₀ (norm_nonneg _) (hb n hn) 2
  rwa [nsmul_eq_mul] at this

/-- `√(a + b) ≤ √a + √b`. -/
private theorem sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- `|[⌈Y⌉, ⌊2Y⌋]| ≤ 2Y + 1`. -/
private theorem card_Icc_ceil_floor_le {Y : ℝ} (hY : 0 ≤ Y) :
    ((Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊).card : ℝ) ≤ 2 * Y + 1 := by
  rw [Nat.card_Icc]
  have h₁ : ⌊2 * Y⌋₊ + 1 - ⌈Y⌉₊ ≤ ⌊2 * Y⌋₊ + 1 := Nat.sub_le _ _
  have h₂ : (⌊2 * Y⌋₊ : ℝ) ≤ 2 * Y := Nat.floor_le (by positivity)
  calc ((⌊2 * Y⌋₊ + 1 - ⌈Y⌉₊ : ℕ) : ℝ) ≤ ((⌊2 * Y⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h₁
    _ ≤ 2 * Y + 1 := by push_cast; linarith

/-- **(6.19) for the first endpoint.** `∑_{Y ≤ w ≤ 2Y} |𝒰(w)|² ≤ Y L^{2C_W + 3}` from
`|ψ₁| ≤ M₀`, `|F| ≤ L` (crude U7) and `|W| ≤ L^{C_W}` (U9), once `3M₀² ≤ L`. -/
theorem sum_norm_endpointCoeff_sq_le {x q q₀ : ℝ} {r d : ℕ} (a : Fin r → ℝ)
    (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) {J : ℕ} (C : ι → Finset (Fin J)) (b : (ι → Fin (J + 1) → ℕ) → ℂ)
    (ψ₁ : ℝ → ℂ) {Y σ L CW M0 : ℝ} (hL : 0 < L) (hY : 1 ≤ Y) (hYx : 2 * Y ≤ x ^ 3)
    (hM : 3 * M0 ^ 2 ≤ L) (hψ : ∀ z, ‖ψ₁ z‖ ≤ M0)
    (hF : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ x ^ 3 → |centeredCore x q a u v Bc n| ≤ L)
    (hW : ∀ n, ‖markedListWeight P q₀ (unsharedSlots C) b n‖ ≤ L ^ CW) :
    ∑ w ∈ Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊, ‖endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ w‖ ^ 2 ≤
      Y * L ^ (2 * CW + 3) := by
  have hM0 : 0 ≤ M0 := (norm_nonneg _).trans (hψ 0)
  have hpt : ∀ w ∈ Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊,
      ‖endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ w‖ ≤ M0 * L ^ (1 + CW) := by
    intro w hw
    have hw1 : 1 ≤ w := le_trans (Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne')
      (Finset.mem_Icc.1 hw).1
    have hw2 : (w : ℝ) ≤ x ^ 3 :=
      ((Nat.le_floor_iff (by positivity)).1 (Finset.mem_Icc.1 hw).2).trans (by linarith)
    rw [endpointCoeff, norm_mul, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hw1,
      Complex.norm_real, Real.norm_eq_abs, Real.rpow_add hL, Real.rpow_one]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, Real.rpow_zero, mul_one]
    have := hF w hw1 hw2
    have := hW w
    calc ‖ψ₁ (w / Y)‖ * |centeredCore x q a u v Bc w| *
          ‖markedListWeight P q₀ (unsharedSlots C) b w‖
        ≤ M0 * L * L ^ CW := by gcongr; exact hψ _
      _ = M0 * (L * L ^ CW) := by ring
  refine (sum_norm_sq_le_card_mul hpt).trans ?_
  have hsq : (M0 * L ^ (1 + CW)) ^ 2 = M0 ^ 2 * L ^ (2 * CW + 2) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hL.le]
    push_cast
    ring_nf
  rw [hsq]
  have hcard := card_Icc_ceil_floor_le (show 0 ≤ Y by linarith)
  calc ((Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊).card : ℝ) * (M0 ^ 2 * L ^ (2 * CW + 2))
      ≤ (3 * Y) * (M0 ^ 2 * L ^ (2 * CW + 2)) := by gcongr; linarith
    _ = Y * (3 * M0 ^ 2) * L ^ (2 * CW + 2) := by ring
    _ ≤ Y * L * L ^ (2 * CW + 2) := by gcongr
    _ = Y * L ^ (2 * CW + 3) := by
        rw [show 2 * CW + 3 = 2 * CW + 2 + 1 by ring, Real.rpow_add hL (2 * CW + 2) 1,
          Real.rpow_one]
        ring

/-- **(6.19) for the second endpoint.** `∑_{0 ≤ w ≤ 3Y} |G(w) W(w)|² ≤ Y L^{2B₀ + 2C_W + 1}`
from `0 ≤ G ≤ L^{B₀}` and `|W| ≤ L^{C_W}`, once `4 ≤ L`. -/
theorem sum_norm_second_sq_le {L B₀ CW Y : ℝ} (hL : 4 ≤ L) (hY : 1 ≤ Y) (G : ℕ → ℝ)
    (W : ℕ → ℂ) (hG : ∀ n, 0 ≤ G n ∧ G n ≤ L ^ B₀) (hW : ∀ n, ‖W n‖ ≤ L ^ CW) :
    ∑ w ∈ Finset.Icc 0 ⌊3 * Y⌋₊, ‖(G w : ℂ) * W w‖ ^ 2 ≤ Y * L ^ (2 * B₀ + 2 * CW + 1) := by
  have hL0 : 0 < L := by linarith
  have hpt : ∀ w ∈ Finset.Icc 0 ⌊3 * Y⌋₊, ‖(G w : ℂ) * W w‖ ≤ L ^ (B₀ + CW) := by
    intro w _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hG w).1, Real.rpow_add hL0]
    exact mul_le_mul (hG w).2 (hW w) (norm_nonneg _) (by positivity)
  refine (sum_norm_sq_le_card_mul hpt).trans ?_
  have hsq : (L ^ (B₀ + CW)) ^ 2 = L ^ (2 * B₀ + 2 * CW) := by
    rw [← Real.rpow_mul_natCast hL0.le]
    push_cast
    ring_nf
  rw [hsq, Nat.card_Icc]
  have hcard : ((⌊3 * Y⌋₊ + 1 - 0 : ℕ) : ℝ) ≤ 4 * Y := by
    rw [Nat.sub_zero]
    push_cast
    linarith [Nat.floor_le (show 0 ≤ 3 * Y by linarith)]
  calc ((⌊3 * Y⌋₊ + 1 - 0 : ℕ) : ℝ) * L ^ (2 * B₀ + 2 * CW)
      ≤ (4 * Y) * L ^ (2 * B₀ + 2 * CW) := by gcongr
    _ ≤ (L * Y) * L ^ (2 * B₀ + 2 * CW) := by gcongr
    _ = Y * L ^ (2 * B₀ + 2 * CW + 1) := by
        rw [Real.rpow_add hL0 (2 * B₀ + 2 * CW) 1, Real.rpow_one]
        ring

/-- `√(Y L^c) = √Y L^{c/2}`. -/
private theorem sqrt_mul_rpow {Y L : ℝ} (hY : 0 ≤ Y) (hL : 0 < L) (c : ℝ) :
    Real.sqrt (Y * L ^ c) = Real.sqrt Y * L ^ (c / 2) := by
  rw [Real.sqrt_mul hY, Real.sqrt_eq_rpow (L ^ c), ← Real.rpow_mul hL.le]
  ring_nf

/-- **The final count (Proof of C).** From the S8 bound
`𝔅 ≤ ε √(Y L^{C_A}) √(Y L^{C_V}) + 4R² √E √(Y L^{C_V})` with `ε = 4K' L^{-A'}`,
`E ≤ K₃ Y (Ξ₀ + 2L^{-2A_e})`, `R ≤ L^{C_arc}` and `-A' + (C_A + C_V)/2 ≤ -A_m`:
`𝔅/Y ≤ (4K' + 8√K₃) (L^{-A_m} + L^{2C_arc + C_V/2} (√Ξ₀ + L^{-A_e}))`. -/
theorem div_le_of_arcs {N Y L Kmin K₃ Am Am' A₀ CA CB Carc Ξ₀ E : ℝ} {R : ℕ} (hY : 0 < Y)
    (hL : 1 ≤ L) (hKmin : 0 ≤ Kmin) (hK₃ : 0 ≤ K₃) (hΞ : 0 ≤ Ξ₀)
    (hN : N ≤ 4 * (Kmin * L ^ (-Am')) * Real.sqrt (Y * L ^ CA) * Real.sqrt (Y * L ^ CB) +
      4 * (R : ℝ) ^ 2 * Real.sqrt E * Real.sqrt (Y * L ^ CB))
    (hE : E ≤ K₃ * (Y * (Ξ₀ + 2 * L ^ (-(2 * A₀))))) (hR : (R : ℝ) ≤ L ^ Carc)
    (hAm : -Am' + (CA + CB) / 2 ≤ -Am) :
    N / Y ≤ (4 * Kmin + 8 * Real.sqrt K₃) *
      (L ^ (-Am) + L ^ (2 * Carc + CB / 2) * (Real.sqrt Ξ₀ + L ^ (-A₀))) := by
  have hL0 : 0 < L := by linarith
  have hsY0 := Real.sqrt_nonneg Y
  -- the minor arcs
  have h₁ : 4 * (Kmin * L ^ (-Am')) * Real.sqrt (Y * L ^ CA) * Real.sqrt (Y * L ^ CB) ≤
      Y * (4 * Kmin * L ^ (-Am)) := by
    rw [sqrt_mul_rpow hY.le hL0, sqrt_mul_rpow hY.le hL0]
    have he : L ^ (-Am') * (L ^ (CA / 2) * L ^ (CB / 2)) = L ^ (-Am' + (CA + CB) / 2) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
      ring_nf
    have hle : L ^ (-Am' + (CA + CB) / 2) ≤ L ^ (-Am) :=
      Real.rpow_le_rpow_of_exponent_le hL hAm
    calc 4 * (Kmin * L ^ (-Am')) * (Real.sqrt Y * L ^ (CA / 2)) *
          (Real.sqrt Y * L ^ (CB / 2))
        = (Real.sqrt Y * Real.sqrt Y) *
            (4 * Kmin * (L ^ (-Am') * (L ^ (CA / 2) * L ^ (CB / 2)))) := by ring
      _ = Y * (4 * Kmin * (L ^ (-Am') * (L ^ (CA / 2) * L ^ (CB / 2)))) := by
          rw [Real.mul_self_sqrt hY.le]
      _ ≤ Y * (4 * Kmin * L ^ (-Am)) := by
          rw [he]
          gcongr
  -- the arcs
  have hA0 : 0 ≤ L ^ (-A₀) := by positivity
  have hsE : Real.sqrt E ≤ Real.sqrt K₃ * Real.sqrt Y * (Real.sqrt Ξ₀ + 2 * L ^ (-A₀)) := by
    refine (Real.sqrt_le_sqrt hE).trans ?_
    rw [Real.sqrt_mul hK₃, Real.sqrt_mul hY.le, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hsY0) (Real.sqrt_nonneg _)
    refine (sqrt_add_le hΞ (by positivity)).trans (add_le_add le_rfl ?_)
    rw [Real.sqrt_mul (by norm_num), show -(2 * A₀) = -A₀ * 2 by ring, Real.rpow_mul hL0.le,
      Real.rpow_two, Real.sqrt_sq hA0]
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    exact mul_le_mul_of_nonneg_right this hA0
  have hR2 : (R : ℝ) ^ 2 ≤ L ^ (2 * Carc) := by
    rw [mul_comm, Real.rpow_mul hL0.le, Real.rpow_two]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hR 2
  have h₂ : 4 * (R : ℝ) ^ 2 * Real.sqrt E * Real.sqrt (Y * L ^ CB) ≤
      Y * (8 * Real.sqrt K₃ * (L ^ (2 * Carc + CB / 2) * (Real.sqrt Ξ₀ + L ^ (-A₀)))) := by
    rw [sqrt_mul_rpow hY.le hL0]
    have hK := Real.sqrt_nonneg K₃
    have hΞs := Real.sqrt_nonneg Ξ₀
    calc 4 * (R : ℝ) ^ 2 * Real.sqrt E * (Real.sqrt Y * L ^ (CB / 2))
        ≤ 4 * L ^ (2 * Carc) * (Real.sqrt K₃ * Real.sqrt Y * (Real.sqrt Ξ₀ + 2 * L ^ (-A₀))) *
            (Real.sqrt Y * L ^ (CB / 2)) := by gcongr
      _ = (Real.sqrt Y * Real.sqrt Y) * (4 * Real.sqrt K₃ * ((L ^ (2 * Carc) * L ^ (CB / 2)) *
            (Real.sqrt Ξ₀ + 2 * L ^ (-A₀)))) := by ring
      _ = Y * (4 * Real.sqrt K₃ * ((L ^ (2 * Carc) * L ^ (CB / 2)) *
            (Real.sqrt Ξ₀ + 2 * L ^ (-A₀)))) := by rw [Real.mul_self_sqrt hY.le]
      _ ≤ Y * (8 * Real.sqrt K₃ * (L ^ (2 * Carc + CB / 2) * (Real.sqrt Ξ₀ + L ^ (-A₀)))) := by
          rw [← Real.rpow_add hL0]
          have hp : 0 ≤ L ^ (2 * Carc + CB / 2) := by positivity
          refine mul_le_mul_of_nonneg_left ?_ hY.le
          nlinarith [mul_nonneg hK hp, mul_nonneg (mul_nonneg hK hp) hΞs,
            mul_nonneg (mul_nonneg hK hp) hA0]
  rw [div_le_iff₀ hY]
  have hm0 : 0 ≤ L ^ (-Am) := by positivity
  have hp0 : 0 ≤ L ^ (2 * Carc + CB / 2) * (Real.sqrt Ξ₀ + L ^ (-A₀)) := by positivity
  have hK := Real.sqrt_nonneg K₃
  calc N ≤ Y * (4 * Kmin * L ^ (-Am)) +
        Y * (8 * Real.sqrt K₃ * (L ^ (2 * Carc + CB / 2) * (Real.sqrt Ξ₀ + L ^ (-A₀)))) :=
        hN.trans (add_le_add h₁ h₂)
    _ ≤ _ := by
        have h₃ := mul_nonneg (mul_nonneg hY.le hKmin) hp0
        have h₄ := mul_nonneg (mul_nonneg hY.le hK) hm0
        nlinarith

/-- **The weighted tail.** If `L ≤ T`, `0 ≤ Q ≤ L²` and `C_A + 2A_e + 2 ≤ m`, then
`(1 + T)^{-m} Q L^{C_A} ≤ L^{-2A_e}`. -/
private theorem inv_pow_mul_le {L T Q CA A₀ : ℝ} {m : ℕ} (hL : 1 ≤ L) (hT : L ≤ T) (hQ : 0 ≤ Q)
    (hQL : Q ≤ L ^ 2) (hm : CA + 2 * A₀ + 2 ≤ m) :
    ((1 + T) ^ m)⁻¹ * Q * L ^ CA ≤ L ^ (-(2 * A₀)) := by
  have hL0 : 0 < L := by linarith
  have h₁ : ((1 + T) ^ m)⁻¹ ≤ L ^ (-(m : ℝ)) := by
    rw [Real.rpow_neg hL0.le, Real.rpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hL0.le (by linarith) m)
  calc ((1 + T) ^ m)⁻¹ * Q * L ^ CA ≤ L ^ (-(m : ℝ)) * L ^ (2 : ℝ) * L ^ CA := by
        rw [Real.rpow_two]
        gcongr
    _ = L ^ (-(m : ℝ) + 2 + CA) := by rw [Real.rpow_add hL0, Real.rpow_add hL0]
    _ ≤ L ^ (-(2 * A₀)) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)

/-- **The additive term.** If `0 ≤ H/Y ≤ 4κ/x`, `16κ² ≤ x` and `L^{C_A + 2A_e} ≤ x`, then
`(H/Y)² L^{C_A} ≤ L^{-2A_e}`. -/
private theorem sq_mul_rpow_le {H Y x κ L CA A₀ : ℝ} (hx : 0 < x) (hL : 0 < L) (hHY : 0 ≤ H / Y)
    (hHY' : H / Y ≤ 4 * κ / x) (hκx : 16 * κ ^ 2 ≤ x) (hLx : L ^ (CA + 2 * A₀) ≤ x) :
    (H / Y) ^ 2 * L ^ CA ≤ L ^ (-(2 * A₀)) := by
  have hsplit : L ^ CA = L ^ (CA + 2 * A₀) * L ^ (-(2 * A₀)) := by
    rw [← Real.rpow_add hL]
    ring_nf
  have hsq : (H / Y) ^ 2 ≤ 16 * κ ^ 2 / x ^ 2 := by
    calc (H / Y) ^ 2 ≤ (4 * κ / x) ^ 2 := pow_le_pow_left₀ hHY hHY' 2
      _ = 16 * κ ^ 2 / x ^ 2 := by ring
  have hp : 0 ≤ L ^ (-(2 * A₀)) := by positivity
  calc (H / Y) ^ 2 * L ^ CA ≤ 16 * κ ^ 2 / x ^ 2 * (L ^ (CA + 2 * A₀) * L ^ (-(2 * A₀))) := by
        rw [hsplit]
        gcongr
    _ ≤ x / x ^ 2 * (x * L ^ (-(2 * A₀))) := by gcongr
    _ = L ^ (-(2 * A₀)) := by field_simp

/-- **The minor arcs (S6–S7).** Off the arcs of radius `L^{C_arc}/(UU')` around the centres
`u/r`, `r ≤ R`, `-R ≤ u ≤ 2R`, the multiplier `∑_a μ(a) b₁(D_A) b₂(D_B) e(-θ D_A D_B)` is at
most `4K' L^{-A'}`: the four boxes of C2, each `≤ K' L^{-A'}`, with the atoms of C1. -/
theorem norm_multiplier_le {ι : Type} [Fintype ι] [DecidableEq ι] {c₀ C₀ vlo vhi x : ℝ}
    {P : ι → Finset ℕ} {big : Finset ι} (hadm : GroupAdmissible c₀ C₀ vlo vhi x P big)
    (hvlo : 0 < vlo) {J : ℕ} {A B : ι → Finset (Fin J)} (hAB : ∀ g, Disjoint (A g) (B g))
    (φ φ' : ℕ → ℂ) (σ U U' θ C₇ C Carc Am' Kmin : ℝ) (R : ℕ)
    (hφ : ∀ n, ‖φ n‖ ≤ 1) (hφ' : ∀ n, ‖φ' n‖ ≤ 1)
    (hsφ : ∀ n, φ n ≠ 0 → U ≤ n ∧ (n : ℝ) ≤ Real.exp 1 * U)
    (hsφ' : ∀ n, φ' n ≠ 0 → U' ≤ n ∧ (n : ℝ) ≤ Real.exp 1 * U')
    (hρA : ∀ n : ℕ, 1 ≤ n →
      ∑ l ∈ (auxLabels P A).filter (fun l => slotProduct A l = n), labelMass P A l ≤
        Real.log x ^ C₇ / n)
    (hρB : ∀ n : ℕ, 1 ≤ n →
      ∑ l ∈ (auxLabels P B).filter (fun l => slotProduct B l = n), labelMass P B l ≤
        Real.log x ^ C₇ / n)
    (hC2x : ∀ (U V θ : ℝ) (k : ℤ) (s t : Finset ℤ) (a b : ℤ → ℂ),
        Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ U → Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ V →
        U * V ≤ x ^ 2 → k ≠ 0 → |(k : ℝ)| ≤ Real.log x ^ C →
        (∀ n ∈ s, U ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * U) → (∀ n ∈ t, V ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * V) →
        ∑ n ∈ s, ‖a n‖ ^ 2 ≤ Real.log x ^ C / U → ∑ n ∈ t, ‖b n‖ ^ 2 ≤ Real.log x ^ C / V →
        (∀ (r : ℕ) (u : ℤ), 1 ≤ r → (r : ℝ) ≤ Real.log x ^ Carc →
          Real.log x ^ Carc / (U * V) < |θ - u / r|) →
        ‖∑ n ∈ s, ∑ v ∈ t, a n * b v *
            Complex.exp (2 * Real.pi * (-(k : ℝ) * θ * n * v : ℝ) * Complex.I)‖ ≤
          Kmin * Real.log x ^ (-Am'))
    (hU38 : Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ U)
    (hU'38 : Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ U') (hUUx : 4 * (U * U') ≤ x ^ 2)
    (hL : 1 ≤ Real.log x) (hC₇C : Real.log x ^ C₇ ≤ Real.log x ^ C)
    (hLC : 1 ≤ Real.log x ^ C)
    (hR : ∀ r : ℕ, (r : ℝ) ≤ Real.log x ^ Carc → r ≤ R)
    (hLCarc : Real.log x ^ Carc ≤ U * U') (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (harc : ∀ (r : ℕ) (u : ℤ), 1 ≤ r → r ≤ R → -(R : ℤ) ≤ u → u ≤ 2 * R →
      Real.log x ^ Carc / (U * U') < |θ - u / r|) :
    ‖∑ l ∈ auxLabels P (fun g => A g ∪ B g),
        (labelMass P (fun g => A g ∪ B g) l : ℂ) *
          (φ (slotProduct A l) * (slotProduct A l : ℂ) ^ (-((σ : ℂ) * Complex.I))) *
          (φ' (slotProduct B l) * (slotProduct B l : ℂ) ^ (-((σ : ℂ) * Complex.I))) *
          Erdos821.Blueprint.Analytic.e (-θ * (slotProduct (fun g => A g ∪ B g) l : ℕ))‖ ≤
      4 * (Kmin * Real.log x ^ (-Am')) := by
  set b₁ : ℕ → ℂ := fun n => φ n * (n : ℂ) ^ (-((σ : ℂ) * Complex.I)) with hb₁
  set b₂ : ℕ → ℂ := fun n => φ' n * (n : ℂ) ^ (-((σ : ℂ) * Complex.I)) with hb₂
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos _) hU38
  have hU'0 : 0 < U' := lt_of_lt_of_le (Real.exp_pos _) hU'38
  have he4 : Real.exp 1 ≤ 4 := (Real.exp_one_lt_d9).le.trans (by norm_num)
  have hV : ∀ g, harmonicMass (P g) ≠ 0 := fun g =>
    (lt_of_lt_of_le hvlo (hadm.2.2.2.2.2.1 g).1).ne'
  have hμ : ∀ (S : ι → Finset (Fin J)) (l : ι → Fin J → ℕ), 0 ≤ labelMass P S l :=
    labelMass_nonneg P
  -- the multiplier as a double sum over the labels of `A` and of `B`
  have hbil : ∑ l ∈ auxLabels P (fun g => A g ∪ B g),
      (labelMass P (fun g => A g ∪ B g) l : ℂ) * b₁ (slotProduct A l) * b₂ (slotProduct B l) *
        Erdos821.Blueprint.Analytic.e (-θ * (slotProduct (fun g => A g ∪ B g) l : ℕ)) =
      ∑ l₁ ∈ auxLabels P A, ∑ l₂ ∈ auxLabels P B,
        (labelMass P A l₁ : ℂ) * (labelMass P B l₂ : ℂ) *
          (b₁ (slotProduct A l₁) * b₂ (slotProduct B l₂) *
            bilinearPhase θ (slotProduct A l₁) (slotProduct B l₂)) := by
    rw [← sum_auxLabels_union P hAB (fun n v => b₁ n * b₂ v * bilinearPhase θ n v)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [slotProduct_union hAB]
    simp only [Erdos821.Blueprint.Analytic.e, bilinearPhase]
    push_cast
    ring_nf
  refine (le_of_eq (congrArg norm hbil)).trans ?_
  have hb : ∀ (f : ℕ → ℂ) (n : ℕ), ‖f n‖ ≤ 1 →
      ‖f n * (n : ℂ) ^ (-((σ : ℂ) * Complex.I))‖ ≤ 1 := fun f n h => by
    rw [norm_mul]
    exact (mul_le_mul h (norm_natCast_cpow_neg_le_one n σ) (norm_nonneg _) zero_le_one).trans
      (by norm_num)
  refine norm_sum_bilinear_le (auxLabels P A) (auxLabels P B) (labelMass P A)
    (labelMass P B) (slotProduct A) (slotProduct B) b₁ b₂ U U' (Real.log x ^ C₇)
    (Kmin * Real.log x ^ (-Am')) θ hU0 hU'0 (Real.rpow_nonneg (by linarith) _) (fun l _ => hμ A l)
    (fun l _ => hμ B l) (sum_labelMass hV A) (sum_labelMass hV B)
    (fun n => hb φ n (hφ n)) (fun n => hb φ' n (hφ' n)) ?_ ?_ hρA hρB ?_
  · intro n hn
    have h := hsφ n fun h0 => hn (by rw [hb₁]; simp [h0])
    exact ⟨h.1, h.2.trans (by nlinarith)⟩
  · intro n hn
    have h := hsφ' n fun h0 => hn (by rw [hb₂]; simp [h0])
    exact ⟨h.1, h.2.trans (by nlinarith)⟩
  -- each box is a minor-arc sum of C2
  intro U₀ V₀ s t α β hU₀ hV₀ hs ht hα hβ
  have hU₀l : U ≤ U₀ := by rcases hU₀ with rfl | rfl <;> linarith
  have hV₀l : U' ≤ V₀ := by rcases hV₀ with rfl | rfl <;> linarith
  have hU₀u : U₀ ≤ 2 * U := by rcases hU₀ with rfl | rfl <;> linarith
  have hV₀u : V₀ ≤ 2 * U' := by rcases hV₀ with rfl | rfl <;> linarith
  have hUV : U * U' ≤ U₀ * V₀ := mul_le_mul hU₀l hV₀l hU'0.le (by linarith)
  have hUV0 : 0 < U * U' := mul_pos hU0 hU'0
  have hrad : Real.log x ^ Carc / (U₀ * V₀) ≤ Real.log x ^ Carc / (U * U') :=
    div_le_div_of_nonneg_left (Real.rpow_nonneg (by linarith) _) hUV0 hUV
  have hrad1 : Real.log x ^ Carc / (U * U') ≤ 1 := (div_le_one hUV0).2 hLCarc
  refine hC2x U₀ V₀ θ 1 s t α β (hU38.trans hU₀l) (hU'38.trans hV₀l) ?_ one_ne_zero
    (by simpa using hLC) hs ht (hα.trans (div_le_div_of_nonneg_right hC₇C (by linarith)))
    (hβ.trans (div_le_div_of_nonneg_right hC₇C (by linarith))) ?_
  · calc U₀ * V₀ ≤ (2 * U) * (2 * U') := mul_le_mul hU₀u hV₀u (by linarith) (by linarith)
      _ = 4 * (U * U') := by ring
      _ ≤ x ^ 2 := hUUx
  · intro r u hr₁ hr₂
    have hrR := hR r hr₂
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr₁
    refine lt_of_le_of_lt hrad ?_
    by_cases hu₁ : -(R : ℤ) ≤ u
    · by_cases hu₂ : u ≤ 2 * R
      · exact harc r u hr₁ hrR hu₁ hu₂
      · -- `u/r > 2`, so `|θ - u/r| > 1`
        have h₁ : (2 * r + 1 : ℝ) ≤ u := by
          have : (2 * (r : ℤ) + 1) ≤ u := by omega
          exact_mod_cast this
        have h₂ : 2 < (u : ℝ) / r := by rw [lt_div_iff₀ hr0]; linarith
        refine lt_of_le_of_lt hrad1 ?_
        rw [abs_sub_comm, abs_of_pos (by linarith [hθ.2])]
        linarith [hθ.2]
    · -- `u/r < -1`, so `|θ - u/r| > 1`
      have h₁ : (u : ℝ) ≤ -(r : ℝ) - 1 := by
        have : u ≤ -(r : ℤ) - 1 := by omega
        exact_mod_cast this
      have h₂ : (u : ℝ) / r < -1 := by rw [div_lt_iff₀ hr0]; linarith
      refine lt_of_le_of_lt hrad1 ?_
      rw [abs_of_pos (by linarith [hθ.1])]
      linarith [hθ.1]

/-- **The arc energy (S10).** With `H ≥ 1`, `2YL ≤ T₀H`, `Y ≤ x exp(L^{0.47})`,
`H/Y ≤ 4κ/x` and `j - 4 ≥ C_A + 2A_e + 2`, the energy of S8–S10 is
`E ≤ K₃ Y (Ξ₀ + 2L^{-2A_e})`: the main term `K₃ Y Ξ₀`, the weighted tail and the additive
term `(H/Y)² A`. -/
theorem energy_le {x L Y H T₀ κ K₃ Ξ₀ CA A₀ : ℝ} {j : ℕ} (hx0 : 0 < x) (hLx : Real.log x = L)
    (hL7 : 7 ≤ L) (hY1 : 1 ≤ Y) (hY_hi : Y ≤ x * Real.exp (L ^ (0.47 : ℝ))) (hH1 : 1 ≤ H)
    (hT₀H : 2 * Y * L ≤ T₀ * H) (hm : CA + 2 * A₀ + 2 ≤ ((j - 4 : ℕ) : ℝ))
    (hHY4 : H / Y ≤ 4 * κ / x) (hκx : 16 * κ ^ 2 ≤ x) (hLx' : L ^ (CA + 2 * A₀) ≤ x)
    (hK₃ : 0 ≤ K₃) :
    K₃ * (Y * Ξ₀ + ((1 + T₀ * H / (2 * Y)) ^ (j - 4))⁻¹ *
      (1 / H + 2 * Real.log (4 * Y)) * (Y * L ^ CA) + (H / Y) ^ 2 * (Y * L ^ CA)) ≤
      K₃ * (Y * (Ξ₀ + 2 * L ^ (-(2 * A₀)))) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hY0 : 0 < Y := by linarith
  have hlog4Y : Real.log (4 * Y) ≤ 3 * L := by
    have h₁ : Real.log Y ≤ L + L ^ (0.47 : ℝ) := by
      calc Real.log Y ≤ Real.log (x * Real.exp (L ^ (0.47 : ℝ))) :=
            Real.log_le_log hY0 hY_hi
        _ = L + L ^ (0.47 : ℝ) := by
            rw [Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp, hLx]
    have h₂ : L ^ (0.47 : ℝ) ≤ L := by
      simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (0.47 : ℝ) ≤ 1 by norm_num)
    have h₃ : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      linarith
    rw [Real.log_mul (by norm_num) hY0.ne']
    linarith
  have hQ0 : 0 ≤ 1 / H + 2 * Real.log (4 * Y) :=
    add_nonneg (by positivity) (mul_nonneg zero_le_two (Real.log_nonneg (by linarith)))
  have hQL : 1 / H + 2 * Real.log (4 * Y) ≤ L ^ 2 := by
    have h₁ : 1 / H ≤ 1 := by rw [div_le_one (by linarith)]; exact hH1
    have h₂ : 7 * L ≤ L ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right hL7 hL0.le
    linarith
  have hTL : L ≤ T₀ * H / (2 * Y) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hZ := inv_pow_mul_le hL1 hTL hQ0 hQL hm
  have hHq := sq_mul_rpow_le hx0 hL0 (div_nonneg (by linarith) hY0.le) hHY4 hκx hLx'
  refine mul_le_mul_of_nonneg_left ?_ hK₃
  have e₁ : ((1 + T₀ * H / (2 * Y)) ^ (j - 4))⁻¹ * (1 / H + 2 * Real.log (4 * Y)) *
      (Y * L ^ CA) = Y * (((1 + T₀ * H / (2 * Y)) ^ (j - 4))⁻¹ *
        (1 / H + 2 * Real.log (4 * Y)) * L ^ CA) := by ring
  have e₂ : (H / Y) ^ 2 * (Y * L ^ CA) = Y * ((H / Y) ^ 2 * L ^ CA) := by ring
  rw [e₁, e₂]
  have h₁ := mul_le_mul_of_nonneg_left hZ hY0.le
  have h₂ := mul_le_mul_of_nonneg_left hHq hY0.le
  linarith

end Erdos408.TwoSided.Arcs
