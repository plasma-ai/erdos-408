import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic

/-!
# The primewise identity

PD §4 (`mem:prime-factor`, `mem:orphan-identity`, `mem:prefix`, `mem:suffix`;
`blueprint/one_sided_type_ii.md` §5.5, M1). Fix a prime `p` and a path of visits
`j = 0, …, N` with lines `L_j ∈ {0, …, p}` (the lines `[z_j]_p`), damping defects
`η'_j = 1 - q_j`, and the set `A` of visits where `p` is active. Averaged over a uniform
line `ℓ ∈ {0, …, p}`, the factor of `p` is
`E = (p + 1)⁻¹ ∑_ℓ ∏_{j ∈ A} [ℓ = L_j] ∏_{j ∉ A} (1 - η'_j [ℓ = L_j])`.

* `primeFactor_eq_orphan`: with `A = ∅`,
  `E = b' + (p + 1)⁻¹ ∑_{a < c} η'_a η'_c [L_a = L_c] ∏_{a < j < c} (1 - η'_j [L_j = L_a])`,
  where `b' = 1 - (p + 1)⁻¹ ∑_j η'_j`. Expand the product over subsets. The empty and
  singleton subsets give `b'`. A larger subset is grouped by its first and last element
  `a < c`, and summing its internal part gives the product.
* `primeFactor_eq_active`: with `A ≠ ∅` and all active lines equal to `L*`,
  `E = (p + 1)⁻¹ ∏_{j ∉ A} (1 - η'_j [L_j = L*])`. If two active lines differ, `E = 0`.
* `prod_one_sub_eq_prefix`: the finite telescoping identity
  `∏_{j < a} (1 - x_j) = 1 - ∑_{h < a} x_h ∏_{h < j < a} (1 - x_j)`, which attaches at most
  one ghost to each end of an active interval.
-/

namespace Erdos408.OneSided

open Finset

/-- The averaged factor of one prime: `(p + 1)⁻¹ ∑_ℓ ∏_{j ∈ A} [ℓ = L_j] ∏_{j ∉ A}
(1 - η'_j [ℓ = L_j])`, over visits `j ∈ range (N + 1)`. -/
noncomputable def primeFactor (p N : ℕ) (L : ℕ → ℕ) (η' : ℕ → ℝ) (A : Finset ℕ) : ℝ :=
  ((p : ℝ) + 1)⁻¹ * ∑ ℓ ∈ range (p + 1),
    (∏ j ∈ A, if ℓ = L j then (1 : ℝ) else 0) *
      ∏ j ∈ (range (N + 1)).filter (· ∉ A), (1 - η' j * if ℓ = L j then 1 else 0)

/-- PD `mem:orphan-identity`: for a never-active prime, the averaged factor is the baseline
`b' = 1 - (p + 1)⁻¹ ∑_j η'_j` plus the ghost lifespans `a < c`. -/
theorem primeFactor_eq_orphan (p N : ℕ) (L : ℕ → ℕ) (η' : ℕ → ℝ)
    (hL : ∀ j ≤ N, L j ≤ p) :
    primeFactor p N L η' ∅ =
      (1 - ((p : ℝ) + 1)⁻¹ * ∑ j ∈ range (N + 1), η' j) +
        ((p : ℝ) + 1)⁻¹ * ∑ a ∈ range (N + 1), ∑ c ∈ range (N + 1),
          if a < c ∧ L a = L c then
            η' a * η' c * ∏ j ∈ Ioo a c, (1 - η' j * if L j = L a then 1 else 0)
          else 0 := by
  -- step: for each line, expand the product into singletons and ghost pairs `a < c`
  have hline : ∀ y : ℕ → ℝ, ∏ j ∈ range (N + 1), (1 - y j) =
      1 - ∑ c ∈ range (N + 1), y c + ∑ a ∈ range (N + 1), ∑ c ∈ range (N + 1),
        if a < c then y a * y c * ∏ j ∈ Ioo a c, (1 - y j) else 0 := by
    intro y
    have hpre : ∀ c ∈ range (N + 1), (range (N + 1)).filter (· < c) = range c := by
      intro c hc
      ext j
      simp only [mem_filter, mem_range] at hc ⊢
      omega
    have hpair : ∀ c ∈ range (N + 1),
        y c * ∏ j ∈ range (N + 1) with j < c, (1 - y j) =
          y c - ∑ a ∈ range (N + 1), if a < c then y a * y c * ∏ j ∈ Ioo a c, (1 - y j)
            else 0 := by
      intro c hc
      rw [hpre c hc, ← sum_filter, hpre c hc, prod_one_sub_ordered', mul_sub, mul_one,
        mul_sum]
      congr 1
      refine sum_congr rfl fun a _ => ?_
      have hIoo : (range c).filter (a < ·) = Ioo a c := by
        ext j
        simp only [mem_filter, mem_range, mem_Ioo]
        omega
      rw [hIoo]
      ring
    rw [prod_one_sub_ordered, sum_congr rfl hpair, sum_sub_distrib, sum_comm]
    ring
  -- step: average each piece over the lines `ℓ`
  have hone : ∀ c ∈ range (N + 1),
      ∑ ℓ ∈ range (p + 1), η' c * (if ℓ = L c then (1 : ℝ) else 0) = η' c := by
    intro c hc
    rw [← mul_sum, sum_ite_eq', ite_eq_left (mem_range.2 (Nat.lt_succ_of_le
      (hL c (Nat.lt_succ_iff.1 (mem_range.1 hc))))), mul_one]
  have htwo : ∀ a c, c ∈ range (N + 1) →
      ∑ ℓ ∈ range (p + 1), (if a < c then (η' a * if ℓ = L a then (1 : ℝ) else 0) *
          (η' c * if ℓ = L c then 1 else 0) *
            ∏ j ∈ Ioo a c, (1 - η' j * if ℓ = L j then 1 else 0) else 0) =
        if a < c ∧ L a = L c then
          η' a * η' c * ∏ j ∈ Ioo a c, (1 - η' j * if L j = L a then 1 else 0)
        else 0 := by
    intro a c hc
    have hLc : L c ∈ range (p + 1) :=
      mem_range.2 (Nat.lt_succ_of_le (hL c (Nat.lt_succ_iff.1 (mem_range.1 hc))))
    -- only the line `ℓ = L c` survives
    rw [sum_eq_single_of_mem (L c) hLc]
    · by_cases hac : a < c ∧ L a = L c
      · rw [ite_eq_left hac.1, ite_eq_left hac, hac.2]
        simp only [ite_true, mul_one]
        exact congrArg _ (prod_congr rfl fun j _ => by simp only [eq_comm])
      · rw [ite_eq_right hac]
        by_cases hlt : a < c
        · have hne : L c ≠ L a := fun h => hac ⟨hlt, h.symm⟩
          rw [ite_eq_left hlt, ite_eq_right hne]
          ring
        · rw [ite_eq_right hlt]
    · intro ℓ _ hℓ
      split_ifs <;> simp_all
  -- step: collect
  have hp : ((p : ℝ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero p
  simp only [primeFactor, prod_empty, notMem_empty, not_false_eq_true, filter_true, one_mul]
  rw [sum_congr rfl fun ℓ _ => hline _, sum_add_distrib, sum_sub_distrib, sum_const, card_range,
    sum_comm (s := range (p + 1)), sum_congr rfl hone, sum_comm (s := range (p + 1))]
  simp only [sum_comm (s := range (p + 1)) (t := range (N + 1))]
  rw [sum_congr rfl fun a _ => sum_congr rfl fun c hc => htwo a c hc]
  rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one, mul_add, mul_sub, inv_mul_cancel₀ hp]

/-- For an active prime whose active lines all equal `L*`, the averaged factor is
`(p + 1)⁻¹ ∏_{j ∉ A} (1 - η'_j [L_j = L*])`. -/
theorem primeFactor_eq_active (p N : ℕ) (L : ℕ → ℕ) (η' : ℕ → ℝ) (A : Finset ℕ)
    (Lstar : ℕ) (hLstar : Lstar ≤ p) (hne : A.Nonempty) (hagree : ∀ j ∈ A, L j = Lstar) :
    primeFactor p N L η' A =
      ((p : ℝ) + 1)⁻¹ * ∏ j ∈ (range (N + 1)).filter (· ∉ A),
        (1 - η' j * if L j = Lstar then 1 else 0) := by
  -- step: the active product is the indicator of `ℓ = L*`
  have hind : ∀ ℓ, (∏ j ∈ A, if ℓ = L j then (1 : ℝ) else 0) = if ℓ = Lstar then 1 else 0 := by
    intro ℓ
    by_cases hℓ : ℓ = Lstar
    · rw [ite_eq_left hℓ]
      exact prod_eq_one fun j hj => by rw [hagree j hj, ite_eq_left hℓ]
    · obtain ⟨j₀, hj₀⟩ := hne
      rw [ite_eq_right hℓ]
      exact prod_eq_zero hj₀ (by rw [hagree j₀ hj₀, ite_eq_right hℓ])
  -- step: only the line `ℓ = L*` survives
  rw [primeFactor]
  simp only [hind, ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq', ite_eq_left (mem_range.2 (Nat.lt_succ_of_le hLstar))]
  exact congrArg _ (prod_congr rfl fun j _ => by simp only [eq_comm])

/-- If two active lines differ, the averaged factor vanishes. -/
theorem primeFactor_eq_zero (p N : ℕ) (L : ℕ → ℕ) (η' : ℕ → ℝ) (A : Finset ℕ)
    {j₁ j₂ : ℕ} (h₁ : j₁ ∈ A) (h₂ : j₂ ∈ A) (hne : L j₁ ≠ L j₂) :
    primeFactor p N L η' A = 0 := by
  -- step: every line `ℓ` misses one of the two active lines
  rw [primeFactor]
  refine mul_eq_zero_of_right _ (sum_eq_zero fun ℓ _ => mul_eq_zero_of_left ?_ _)
  by_cases hℓ : ℓ = L j₁
  · exact prod_eq_zero h₂ (ite_eq_right fun h => hne (hℓ.symm.trans h))
  · exact prod_eq_zero h₁ (ite_eq_right hℓ)

/-- PD `mem:prefix`: `∏_{j < a} (1 - x_j) = 1 - ∑_{h < a} x_h ∏_{h < j < a} (1 - x_j)`. -/
theorem prod_one_sub_eq_prefix (x : ℕ → ℝ) (a : ℕ) :
    ∏ j ∈ range a, (1 - x j) = 1 - ∑ h ∈ range a, x h * ∏ j ∈ Ioo h a, (1 - x j) := by
  rw [prod_one_sub_ordered']
  refine congrArg (1 - ·) (sum_congr rfl fun h hh => ?_)
  have hIoo : (range a).filter (h < ·) = Ioo h a := by
    ext j
    simp only [mem_filter, mem_range, mem_Ioo] at hh ⊢
    omega
  rw [hIoo]

/-- PD `mem:suffix`: `∏_{c < j ≤ N} (1 - x_j) = 1 - ∑_{c < h ≤ N} x_h ∏_{c < j < h} (1 - x_j)`. -/
theorem prod_one_sub_eq_suffix (x : ℕ → ℝ) (c N : ℕ) :
    ∏ j ∈ Ioc c N, (1 - x j) = 1 - ∑ h ∈ Ioc c N, x h * ∏ j ∈ Ioo c h, (1 - x j) := by
  rw [prod_one_sub_ordered]
  refine congrArg (1 - ·) (sum_congr rfl fun h hh => ?_)
  have hIoo : (Ioc c N).filter (· < h) = Ioo c h := by
    ext j
    simp only [mem_filter, mem_Ioc, mem_Ioo] at hh ⊢
    omega
  rw [hIoo]

end Erdos408.OneSided
