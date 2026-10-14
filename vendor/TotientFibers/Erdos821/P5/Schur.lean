import Erdos821.P5.Basic

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Erdos821.P5Core

/-- The elementary real Schur estimate for a symmetric nonnegative finite kernel. -/
theorem symmetric_row_quadratic_bound {ι : Type*} (s : Finset ι)
    (w : ι → ι → ℝ) (a : ι → ℝ) (R : ℝ)
    (hw : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ w i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, w i j = w j i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, w i j ≤ R) :
    ∑ i ∈ s, ∑ j ∈ s, w i j * a i * a j ≤ R * ∑ i ∈ s, a i ^ 2 := by
  have hswap : ∑ i ∈ s, ∑ j ∈ s, w i j * a j ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, w i j * a i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
  calc
    _ ≤ (∑ i ∈ s, ∑ j ∈ s, w i j * (a i ^ 2 + a j ^ 2)) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro j hj
      have hab : a i * a j ≤ (a i ^ 2 + a j ^ 2) / 2 := by
        nlinarith only [sq_nonneg (a i - a j)]
      have h := mul_le_mul_of_nonneg_left hab (hw i hi j hj)
      nlinarith only [h]
    _ = ∑ i ∈ s, (∑ j ∈ s, w i j) * a i ^ 2 := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [hswap]
      simp_rw [← Finset.sum_mul]
      ring
    _ ≤ ∑ i ∈ s, R * a i ^ 2 := Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg _))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- A Gram row bound controls every finite linear combination. -/
theorem norm_linear_combination_sq_le {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (s : Finset ι) (f : ι → H) (a : ι → ℂ) (R : ℝ)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, ‖⟪f i, f j⟫_ℂ‖ ≤ R) :
    ‖∑ i ∈ s, a i • f i‖ ^ 2 ≤ R * ∑ i ∈ s, ‖a i‖ ^ 2 := by
  have hexpand : ‖∑ i ∈ s, a i • f i‖ ^ 2 =
      (∑ i ∈ s, ∑ j ∈ s, star (a i) * a j * ⟪f i, f j⟫_ℂ).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, mul_assoc]
    rfl
  have hschur := symmetric_row_quadratic_bound s (fun i j => ‖⟪f i, f j⟫_ℂ‖)
    (fun i => ‖a i‖) R (fun _ _ _ _ => norm_nonneg _)
    (fun i _ j _ => norm_inner_symm _ _) hrow
  calc
    _ = _ := hexpand
    _ ≤ ‖∑ i ∈ s, ∑ j ∈ s, star (a i) * a j * ⟪f i, f j⟫_ℂ‖ := Complex.re_le_norm _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖star (a i) * a j * ⟪f i, f j⟫_ℂ‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ = ∑ i ∈ s, ∑ j ∈ s, ‖⟪f i, f j⟫_ℂ‖ * ‖a i‖ * ‖a j‖ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [norm_mul, norm_star]
      ring
    _ ≤ _ := hschur

/-- Duality turns the Gram row estimate into a bound for all sampled inner products. -/
theorem gram_bessel_bound {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (s : Finset ι) (f : ι → H) (x : H) (R : ℝ)
    (hR : 0 ≤ R) (hrow : ∀ i ∈ s, ∑ j ∈ s, ‖⟪f i, f j⟫_ℂ‖ ≤ R) :
    ∑ i ∈ s, ‖⟪f i, x⟫_ℂ‖ ^ 2 ≤ R * ‖x‖ ^ 2 := by
  let a := fun i => ⟪f i, x⟫_ℂ
  let g := ∑ i ∈ s, a i • f i
  let S := ∑ i ∈ s, ‖a i‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsquare (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
    have h : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      simpa only [Complex.star_def, mul_comm, Complex.ofReal_pow] using Complex.mul_conj' z
    rw [h, Complex.ofReal_re]
  have hinner : (⟪g, x⟫_ℂ).re = S := by
    simp only [g, S, sum_inner, inner_smul_left]
    change (∑ i ∈ s, star (a i) * a i).re = ∑ i ∈ s, ‖a i‖ ^ 2
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun i _ => hsquare (a i))
  have hnorm : ‖g‖ ^ 2 ≤ R * S := norm_linear_combination_sq_le s f a R hrow
  have hcs : S ≤ ‖g‖ * ‖x‖ := by
    rw [← hinner]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hcs2 : S ^ 2 ≤ ‖g‖ ^ 2 * ‖x‖ ^ 2 := by
    have h := pow_le_pow_left₀ hS hcs 2
    simpa only [mul_pow] using h
  have hsq : S ^ 2 ≤ (R * S) * ‖x‖ ^ 2 := hcs2.trans
    (mul_le_mul_of_nonneg_right hnorm (sq_nonneg _))
  by_cases hzero : S = 0
  · change S ≤ R * ‖x‖ ^ 2
    rw [hzero]
    positivity
  · have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
    change S ≤ R * ‖x‖ ^ 2
    nlinarith only [hsq, hpos]

end Erdos821.P5Core
