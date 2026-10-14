import Erdos408.Extraction.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The cutoff `Ψ(y) = y Φ(y)`

`TwoSidedCorrelation` weights `w` by `Ψ(w/x) / w`, so the proxy sum's
weight `Φ(w/x)` corresponds to `Ψ(y) = y Φ(y)`, up to the factor `x`. By
Leibniz, `Ψ^{(r+1)} = y Φ^{(r+1)} + (r + 1) Φ^{(r)}`. Since `Φ` vanishes off
`[κ⁻¹, κ]`, so do its derivatives, and `|y Φ^{(r)}(y)| ≤ κ |Φ^{(r)}(y)|`.
Hence `Ψ` lies in the cutoff class with `M'_r = κ M_r + r M_{r-1}` and
`C_Ψ = max C_Φ 0`.
-/

namespace Erdos408

open Filter Real Topology

/-- Leibniz for `y Φ(y)`: `(y Φ)^{(r+1)} = y Φ^{(r+1)} + (r + 1) Φ^{(r)}`. -/
lemma iteratedDeriv_succ_mul_id {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (r : ℕ) : iteratedDeriv (r + 1) (fun y => y * Φ y) =
      fun y => y * iteratedDeriv (r + 1) Φ y + (r + 1) * iteratedDeriv r Φ y := by
  have hd : ∀ k, Differentiable ℝ (iteratedDeriv k Φ) := fun k =>
    hΦ.differentiable_iteratedDeriv k (by exact_mod_cast WithTop.coe_lt_top _)
  induction r with
  | zero =>
    rw [iteratedDeriv_one, iteratedDeriv_zero, iteratedDeriv_one]
    funext y
    have h : HasDerivAt (fun y => y * Φ y) (1 * Φ y + y * deriv Φ y) y :=
      (hasDerivAt_id' y).mul (hΦ.differentiable (by simp) y).hasDerivAt
    rw [h.deriv]
    push_cast
    ring
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h : HasDerivAt (fun y => y * iteratedDeriv (r + 1) Φ y + (r + 1) * iteratedDeriv r Φ y)
        (1 * iteratedDeriv (r + 1) Φ y + y * deriv (iteratedDeriv (r + 1) Φ) y +
          (r + 1) * deriv (iteratedDeriv r Φ) y) y :=
      ((hasDerivAt_id' y).mul ((hd (r + 1)) y).hasDerivAt).add
        (((hd r) y).hasDerivAt.const_mul ((r : ℝ) + 1))
    rw [h.deriv, ← iteratedDeriv_succ, ← iteratedDeriv_succ]
    push_cast
    ring

/-- The derivatives of a function vanishing off `[κ⁻¹, κ]` vanish at `|y| > κ`. -/
lemma iteratedDeriv_eq_zero_of_lt {Φ : ℝ → ℝ} {κ : ℝ} (hκ : 1 < κ)
    (hsupp : ∀ y, Φ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) (r : ℕ) {y : ℝ} (hy : κ < |y|) :
    iteratedDeriv r Φ y = 0 := by
  have hκ0 : 0 < κ⁻¹ := inv_pos.2 (by linarith)
  have hopen : IsOpen {z : ℝ | κ < |z|} := isOpen_lt continuous_const continuous_abs
  have hzero : Φ =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    by_contra h
    obtain ⟨h1, h2⟩ := hsupp z h
    have : |z| = z := abs_of_pos (by linarith)
    linarith
  rw [(hzero.iteratedDeriv r).eq_of_nhds]
  simp

/-- `|y Φ^{(r)}(y)| ≤ κ |Φ^{(r)}(y)|`. -/
lemma abs_mul_iteratedDeriv_le {Φ : ℝ → ℝ} {κ : ℝ} (hκ : 1 < κ)
    (hsupp : ∀ y, Φ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) (r : ℕ) (y : ℝ) :
    |y * iteratedDeriv r Φ y| ≤ κ * |iteratedDeriv r Φ y| := by
  rcases le_or_gt |y| κ with h | h
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
  · rw [iteratedDeriv_eq_zero_of_lt hκ hsupp r h]
    simp

/-- `Ψ(y) = y Φ(y)` is in the cutoff class of `TwoSidedCorrelation` with
`M'_r = κ M_r + r M_{r-1}` and `C_Ψ = max C_Φ 0`. -/
theorem isCutoff_mul_id {κ CΦ : ℝ} {M : ℕ → ℝ} {x : ℝ} {Φ : ℝ → ℝ} (hκ : 1 < κ)
    (hT : 1 ≤ logLog x) (hΦ : IsCutoff κ CΦ M x Φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => y * Φ y) ∧
      (∀ y, y * Φ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) ∧
      ∀ (r : ℕ) (y : ℝ), |iteratedDeriv r (fun y => y * Φ y) y| ≤
        (κ * M r + r * M (r - 1)) * Real.log (Real.log x) ^ (max CΦ 0 * r) := by
  obtain ⟨hsmooth, -, hsupp, hder⟩ := hΦ
  have hM : ∀ r, 0 ≤ M r := fun r => by
    have h := (abs_nonneg _).trans (hder r 0)
    exact nonneg_of_mul_nonneg_left h (rpow_pos_of_pos (by linarith) _)
  have hT' : 1 ≤ Real.log (Real.log x) := hT
  have hexp : ∀ (r : ℕ) (a : ℝ), a ≤ max CΦ 0 * r →
      Real.log (Real.log x) ^ a ≤ Real.log (Real.log x) ^ (max CΦ 0 * r) :=
    fun r a h => rpow_le_rpow_of_exponent_le hT' h
  refine ⟨contDiff_id.mul hsmooth, fun y hy => hsupp y (right_ne_zero_of_mul hy), ?_⟩
  intro r y
  cases r with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.cast_zero, zero_mul, add_zero, mul_zero, rpow_zero,
      mul_one]
    have h := abs_mul_iteratedDeriv_le hκ hsupp 0 y
    have h0 := hder 0 y
    simp only [iteratedDeriv_zero, Nat.cast_zero, mul_zero, rpow_zero, mul_one] at h h0
    nlinarith
  | succ r =>
    rw [iteratedDeriv_succ_mul_id hsmooth r]
    have h1 := abs_mul_iteratedDeriv_le hκ hsupp (r + 1) y
    have h2 := hder (r + 1) y
    have h3 := hder r y
    have e1 := hexp (r + 1) (CΦ * ↑(r + 1)) (by gcongr; exact le_max_left _ _)
    have e2 := hexp (r + 1) (CΦ * r) (by
      push_cast
      have : CΦ * r ≤ max CΦ 0 * r := by gcongr; exact le_max_left _ _
      have : 0 ≤ max CΦ 0 := le_max_right _ _
      nlinarith)
    have hκ0 : 0 ≤ κ := by linarith
    have hr : (0 : ℝ) ≤ r + 1 := by positivity
    calc |y * iteratedDeriv (r + 1) Φ y + (↑r + 1) * iteratedDeriv r Φ y|
        ≤ |y * iteratedDeriv (r + 1) Φ y| + (r + 1) * |iteratedDeriv r Φ y| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul ((r : ℝ) + 1), abs_of_nonneg hr]
      _ ≤ κ * (M (r + 1) * Real.log (Real.log x) ^ (CΦ * ↑(r + 1))) +
            (r + 1) * (M r * Real.log (Real.log x) ^ (CΦ * r)) := by
          gcongr
          · exact h1.trans (mul_le_mul_of_nonneg_left h2 hκ0)
          · exact h3
      _ ≤ κ * (M (r + 1) * Real.log (Real.log x) ^ (max CΦ 0 * ↑(r + 1))) +
            (r + 1) * (M r * Real.log (Real.log x) ^ (max CΦ 0 * ↑(r + 1))) := by
          gcongr
          · exact hM _
          · exact hM _
      _ = _ := by
          simp only [Nat.add_sub_cancel]
          push_cast
          ring

end Erdos408
