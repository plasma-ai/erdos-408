module

public import Erdos408.OneSided.Analysis.Divisor

/-!
# The mean value of a product of two Dirichlet polynomials

PD `maj:product-mean` (`blueprint/one_sided_type_ii.md` §6.3 step 3). The product of
`∑_{m ∈ I₁} u_m m^{it}` and `∑_{n ∈ I₂} v_n n^{it}`, with `I₁ ⊆ [1, N₁]` and `I₂ ⊆ [1, N₂]`,
is the Dirichlet polynomial of length `N = N₁ N₂` with coefficients
`c_l = ∑_{mn = l} u_m v_n`. If `|u_m| ≤ U` and `|v_n| ≤ V`, then `|c_l| ≤ U V τ(l)`, and PD
Lemma 2.2 gives `∫_a^b |·|² ≤ (b - a + 8N(1 + log N)) U² V² N (1 + log N)³`.
-/

@[expose] public section

namespace Erdos408.OneSided

open Finset

/-- The coefficient `c_l = ∑_{mn = l} u_m v_n` of a product of Dirichlet polynomials. -/
noncomputable def mulCoeff (I₁ I₂ : Finset ℕ) (u v : ℕ → ℂ) (l : ℕ) : ℂ :=
  ∑ mn ∈ I₁ ×ˢ I₂ with mn.1 * mn.2 = l, u mn.1 * v mn.2

/-- The product of two Dirichlet polynomials supported in `[1, N₁]` and `[1, N₂]` is the
Dirichlet polynomial of length `N₁ N₂` with coefficients `mulCoeff`. -/
theorem sum_mul_sum_eq {I₁ I₂ : Finset ℕ} {N₁ N₂ : ℕ} (hI₁ : ∀ m ∈ I₁, 1 ≤ m ∧ m ≤ N₁)
    (hI₂ : ∀ n ∈ I₂, 1 ≤ n ∧ n ≤ N₂) (u v : ℕ → ℂ) (t : ℝ) :
    (∑ m ∈ I₁, u m * (m : ℂ) ^ ((t : ℂ) * Complex.I)) *
        (∑ n ∈ I₂, v n * (n : ℂ) ^ ((t : ℂ) * Complex.I)) =
      ∑ l ∈ Icc 1 (N₁ * N₂), mulCoeff I₁ I₂ u v l * (l : ℂ) ^ ((t : ℂ) * Complex.I) := by
  rw [sum_mul_sum, ← sum_product', ← sum_fiberwise_of_maps_to
    (g := fun mn : ℕ × ℕ => mn.1 * mn.2) (t := Icc 1 (N₁ * N₂)) fun mn hmn => ?_]
  · refine sum_congr rfl fun l _ => ?_
    rw [mulCoeff, sum_mul]
    refine sum_congr rfl fun mn hmn => ?_
    rw [mem_filter] at hmn
    -- `m^{it} n^{it} = (mn)^{it}`
    rw [← hmn.2, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  · rw [mem_product] at hmn
    obtain ⟨hm₁, hm₂⟩ := hI₁ _ hmn.1
    obtain ⟨hn₁, hn₂⟩ := hI₂ _ hmn.2
    exact mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)),
      Nat.mul_le_mul hm₂ hn₂⟩

/-- At most `τ(l)` pairs `(m, n)` with `m ≥ 1` have `mn = l ≠ 0`: `m` is a divisor of `l`,
and it determines `n`. -/
theorem card_filter_mul_eq_le {I₁ I₂ : Finset ℕ} (hI₁ : ∀ m ∈ I₁, 1 ≤ m) {l : ℕ} (hl : l ≠ 0) :
    #{mn ∈ I₁ ×ˢ I₂ | mn.1 * mn.2 = l} ≤ #l.divisors := by
  refine card_le_card_of_injOn Prod.fst (fun mn hmn => ?_) fun mn hmn mn' hmn' h => ?_
  · rw [mem_coe, mem_filter] at hmn
    exact Nat.mem_divisors.2 ⟨⟨mn.2, hmn.2.symm⟩, hl⟩
  · rw [mem_coe, mem_filter, mem_product] at hmn hmn'
    have h₁ : 0 < mn.1 := hI₁ _ hmn.1.1
    have h₂ : mn.1 * mn.2 = mn.1 * mn'.2 := by rw [hmn.2, h, hmn'.2]
    exact Prod.ext h (Nat.eq_of_mul_eq_mul_left h₁ h₂)

/-- `|c_l| ≤ U V τ(l)` for `l ≠ 0`. -/
theorem norm_mulCoeff_le {I₁ I₂ : Finset ℕ} (hI₁ : ∀ m ∈ I₁, 1 ≤ m) {u v : ℕ → ℂ} {U V : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hu : ∀ m ∈ I₁, ‖u m‖ ≤ U) (hv : ∀ n ∈ I₂, ‖v n‖ ≤ V) {l : ℕ}
    (hl : l ≠ 0) :
    ‖mulCoeff I₁ I₂ u v l‖ ≤ U * V * #l.divisors := by
  unfold mulCoeff
  refine (norm_sum_le _ _).trans ?_
  calc ∑ mn ∈ I₁ ×ˢ I₂ with mn.1 * mn.2 = l, ‖u mn.1 * v mn.2‖
      ≤ ∑ mn ∈ I₁ ×ˢ I₂ with mn.1 * mn.2 = l, U * V := by
        refine sum_le_sum fun mn hmn => ?_
        rw [mem_filter, mem_product] at hmn
        rw [norm_mul]
        exact mul_le_mul (hu _ hmn.1.1) (hv _ hmn.1.2) (norm_nonneg _) hU
    _ = #{mn ∈ I₁ ×ˢ I₂ | mn.1 * mn.2 = l} * (U * V) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ #l.divisors * (U * V) := by
        gcongr
        exact card_filter_mul_eq_le hI₁ hl
    _ = U * V * #l.divisors := by ring

/-- PD `maj:product-mean`: for Dirichlet polynomials supported in `[1, N₁]` and `[1, N₂]` with
coefficients at most `U` and `V`, and `N = N₁ N₂`,
`∫_a^b |∑ u_m m^{it}|² |∑ v_n n^{it}|² ≤ (b - a + 8N(1 + log N)) U² V² N (1 + log N)³`. -/
theorem integral_norm_sum_mul_sum_sq_le {I₁ I₂ : Finset ℕ} {N₁ N₂ : ℕ}
    (hI₁ : ∀ m ∈ I₁, 1 ≤ m ∧ m ≤ N₁) (hI₂ : ∀ n ∈ I₂, 1 ≤ n ∧ n ≤ N₂) {u v : ℕ → ℂ} {U V : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hu : ∀ m ∈ I₁, ‖u m‖ ≤ U) (hv : ∀ n ∈ I₂, ‖v n‖ ≤ V) {a b : ℝ}
    (hab : a ≤ b) :
    ∫ t in a..b, ‖(∑ m ∈ I₁, u m * (m : ℂ) ^ ((t : ℂ) * Complex.I)) *
        (∑ n ∈ I₂, v n * (n : ℂ) ^ ((t : ℂ) * Complex.I))‖ ^ 2 ≤
      (b - a + 8 * (N₁ * N₂ : ℕ) * (1 + Real.log (N₁ * N₂ : ℕ))) *
        (U ^ 2 * V ^ 2 * ((N₁ * N₂ : ℕ) * (1 + Real.log (N₁ * N₂ : ℕ)) ^ 3)) := by
  simp_rw [sum_mul_sum_eq hI₁ hI₂ u v]
  refine (integral_norm_dirichlet_sq_le _ _ a b).trans ?_
  have hlog := Real.log_natCast_nonneg (N₁ * N₂)
  have hab' := sub_nonneg.2 hab
  gcongr
  -- `∑ |c_l|² ≤ U² V² ∑ τ(l)²`
  calc ∑ l ∈ Icc 1 (N₁ * N₂), ‖mulCoeff I₁ I₂ u v l‖ ^ 2
      ≤ ∑ l ∈ Icc 1 (N₁ * N₂), (U * V * #l.divisors) ^ 2 := by
        refine sum_le_sum fun l hl => ?_
        have hl0 : l ≠ 0 := by rw [mem_Icc] at hl; omega
        exact pow_le_pow_left₀ (norm_nonneg _)
          (norm_mulCoeff_le (fun m hm => (hI₁ m hm).1) hU hV hu hv hl0) 2
    _ = U ^ 2 * V ^ 2 * ∑ l ∈ Icc 1 (N₁ * N₂), ((#l.divisors : ℕ) : ℝ) ^ 2 := by
        rw [mul_sum]
        exact sum_congr rfl fun l _ => by ring
    _ ≤ U ^ 2 * V ^ 2 * ((N₁ * N₂ : ℕ) * (1 + Real.log (N₁ * N₂ : ℕ)) ^ 3) := by
        gcongr
        exact sum_card_divisors_sq_le _

end Erdos408.OneSided
