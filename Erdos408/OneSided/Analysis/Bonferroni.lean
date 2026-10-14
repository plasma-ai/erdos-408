module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Basic.Real.Basic

/-!
# Bonferroni truncation

The pointwise sandwich of PD Lemma 3.4 (`blueprint/one_sided_type_ii.md` §5.4 and §15). For
`x_i ∈ [0, 1]`, truncating the inclusion–exclusion expansion
`∏_i (1 - x_i) = ∑_I (-1)^{|I|} ∏_{i ∈ I} x_i` below degree `T` errs by at most the degree-`T`
elementary symmetric polynomial `e_T(x)`. On `{0, 1}^n` this is Bonferroni's inequality; both
one-sided inequalities are multilinear, so they extend from the vertices to the cube. The
elementary symmetric polynomial is at most `(∑ x_i)^T / T!`.
-/

@[expose] public section

namespace Erdos408.OneSided

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- The elementary symmetric polynomial satisfies the Pascal recurrence when a variable is
inserted. -/
private lemma sum_powersetCard_succ_insert (s : Finset ι) (a : ι) (ha : a ∉ s) (x : ι → ℝ)
    (T : ℕ) :
    ∑ I ∈ (insert a s).powersetCard (T + 1), ∏ i ∈ I, x i =
      ∑ I ∈ s.powersetCard (T + 1), ∏ i ∈ I, x i + x a * ∑ I ∈ s.powersetCard T, ∏ i ∈ I, x i := by
  rw [powersetCard_succ_insert ha, sum_union, sum_image, mul_sum]
  · refine congrArg _ (sum_congr rfl fun I hI => ?_)
    rw [prod_insert fun h => ha ((mem_powersetCard.1 hI).1 h)]
  · intro I hI J hJ h
    have hI' : a ∉ I := fun h => ha ((mem_powersetCard.1 hI).1 h)
    have hJ' : a ∉ J := fun h => ha ((mem_powersetCard.1 hJ).1 h)
    rw [← erase_insert hI', ← erase_insert hJ']
    exact congrArg (·.erase a) h
  · refine disjoint_left.2 fun I hI hI' => ?_
    obtain ⟨J, -, rfl⟩ := mem_image.1 hI'
    exact ha ((mem_powersetCard.1 hI).1 (mem_insert_self a J))

omit [DecidableEq ι] in
/-- Summing over subsets of size `< T` is summing over the sizes `k < T` of the sum over subsets
of size `k`. -/
private lemma sum_powerset_filter_card_lt (s : Finset ι) (f : Finset ι → ℝ) (T : ℕ) :
    ∑ I ∈ s.powerset with #I < T, f I = ∑ k ∈ range T, ∑ I ∈ s.powersetCard k, f I := by
  rw [← sum_fiberwise_of_maps_to (g := card) (t := range T)
    (fun I hI => mem_range.2 (mem_filter.1 hI).2)]
  refine sum_congr rfl fun k hk => ?_
  rw [powersetCard_eq_filter, filter_filter]
  refine sum_congr (filter_congr fun I hI => ?_) fun _ _ => rfl
  have := mem_range.1 hk
  omega

/-- The signed Bonferroni sandwich in terms of the elementary symmetric polynomials
`e_k(x) = ∑_{|I| = k} ∏_{i ∈ I} x_i`: the error `(-1)^T (∏_i (1 - x_i) - ∑_{k < T} (-1)^k e_k)`
lies in `[0, e_T]`. -/
private lemma signed_bonferroni (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1)
    (T : ℕ) :
    0 ≤ (-1) ^ T * (∏ i ∈ s, (1 - x i) -
        ∑ k ∈ range T, (-1) ^ k * ∑ I ∈ s.powersetCard k, ∏ i ∈ I, x i) ∧
      (-1) ^ T * (∏ i ∈ s, (1 - x i) -
        ∑ k ∈ range T, (-1) ^ k * ∑ I ∈ s.powersetCard k, ∏ i ∈ I, x i) ≤
      ∑ I ∈ s.powersetCard T, ∏ i ∈ I, x i := by
  induction s using Finset.induction_on generalizing T with
  | empty =>
    cases T with
    | zero => simp
    | succ T =>
      have h : ∀ k, (∅ : Finset ι).powersetCard (k + 1) = ∅ := fun k =>
        powersetCard_eq_empty.2 (by simp)
      simp [sum_range_succ', powersetCard_zero, h]
  | insert a s ha ih =>
    have hx' : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1 := fun i hi => hx i (mem_insert_of_mem hi)
    obtain ⟨hxa0, hxa1⟩ := hx a (mem_insert_self a s)
    cases T with
    | zero =>
      obtain ⟨h0, h1⟩ := ih hx' 0
      simp only [powersetCard_zero, sum_singleton, prod_empty, range_zero, sum_empty, sub_zero,
        pow_zero, one_mul, prod_insert ha] at h0 h1 ⊢
      exact ⟨mul_nonneg (sub_nonneg.2 hxa1) h0,
        by simpa using mul_le_mul (by linarith) h1 h0 zero_le_one⟩
    | succ T =>
      obtain ⟨h1, h1'⟩ := ih hx' (T + 1)
      obtain ⟨h0, h0'⟩ := ih hx' T
      have hS : ∑ k ∈ range (T + 1), (-1 : ℝ) ^ k *
            ∑ I ∈ (insert a s).powersetCard k, ∏ i ∈ I, x i =
          ∑ k ∈ range (T + 1), (-1 : ℝ) ^ k * ∑ I ∈ s.powersetCard k, ∏ i ∈ I, x i -
            x a * ∑ k ∈ range T, (-1 : ℝ) ^ k * ∑ I ∈ s.powersetCard k, ∏ i ∈ I, x i := by
        have key : ∑ k ∈ range T, (-1 : ℝ) ^ (k + 1) * (∑ I ∈ s.powersetCard (k + 1), ∏ i ∈ I, x i +
              x a * ∑ I ∈ s.powersetCard k, ∏ i ∈ I, x i) =
            ∑ k ∈ range T, (-1 : ℝ) ^ (k + 1) * ∑ I ∈ s.powersetCard (k + 1), ∏ i ∈ I, x i -
              x a * ∑ k ∈ range T, (-1 : ℝ) ^ k * ∑ I ∈ s.powersetCard k, ∏ i ∈ I, x i := by
          rw [mul_sum, ← sum_sub_distrib]
          exact sum_congr rfl fun k _ => by ring
        rw [sum_range_succ', sum_range_succ' (fun k => (-1 : ℝ) ^ k * ∑ I ∈ s.powersetCard k,
          ∏ i ∈ I, x i)]
        simp only [sum_powersetCard_succ_insert s a ha, key, powersetCard_zero, sum_singleton,
          prod_empty, pow_zero, one_mul]
        ring
      rw [hS, prod_insert ha, sum_powersetCard_succ_insert s a ha]
      generalize ∏ i ∈ s, (1 - x i) = P at *
      generalize ∑ k ∈ range (T + 1), (-1 : ℝ) ^ k * ∑ I ∈ s.powersetCard k, ∏ i ∈ I, x i = S1
        at *
      generalize ∑ k ∈ range T, (-1 : ℝ) ^ k * ∑ I ∈ s.powersetCard k, ∏ i ∈ I, x i = S0 at *
      have hid : (-1 : ℝ) ^ (T + 1) * ((1 - x a) * P - (S1 - x a * S0)) =
          (-1) ^ (T + 1) * (P - S1) + x a * ((-1) ^ T * (P - S0)) := by
        rw [pow_succ]
        ring
      rw [hid]
      exact ⟨add_nonneg h1 (mul_nonneg hxa0 h0),
        add_le_add h1' (mul_le_mul_of_nonneg_left h0' hxa0)⟩

/-- **Bonferroni**: for `x_i ∈ [0, 1]`,
`|∏_i (1 - x_i) - ∑_{|I| < T} (-1)^{|I|} ∏_{i ∈ I} x_i| ≤ ∑_{|I| = T} ∏_{i ∈ I} x_i`. -/
theorem abs_prod_one_sub_sub_le (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1)
    (T : ℕ) :
    |∏ i ∈ s, (1 - x i) -
        ∑ I ∈ s.powerset with #I < T, (-1) ^ #I * ∏ i ∈ I, x i| ≤
      ∑ I ∈ s.powersetCard T, ∏ i ∈ I, x i := by
  have hS : ∑ I ∈ s.powerset with #I < T, (-1 : ℝ) ^ #I * ∏ i ∈ I, x i =
      ∑ k ∈ range T, (-1) ^ k * ∑ I ∈ s.powersetCard k, ∏ i ∈ I, x i := by
    rw [sum_powerset_filter_card_lt s (fun I => (-1 : ℝ) ^ #I * ∏ i ∈ I, x i)]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun I hI => by rw [(mem_powersetCard.1 hI).2]
  obtain ⟨h0, h1⟩ := signed_bonferroni s x hx T
  rw [hS]
  calc _ = |(-1 : ℝ) ^ T * (∏ i ∈ s, (1 - x i) -
          ∑ k ∈ range T, (-1) ^ k * ∑ I ∈ s.powersetCard k, ∏ i ∈ I, x i)| := by
        simp [abs_mul]
    _ = _ := abs_of_nonneg h0
    _ ≤ _ := h1

omit [DecidableEq ι] in
/-- The first two terms of the binomial expansion bound `(σ + y)^(n+1)` from below. -/
private lemma pow_succ_add_mul_le_add_pow (σ y : ℝ) (hσ : 0 ≤ σ) (hy : 0 ≤ y) (n : ℕ) :
    σ ^ (n + 1) + (n + 1) * σ ^ n * y ≤ (σ + y) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hσn : 0 ≤ σ ^ n := pow_nonneg hσ n
    calc σ ^ (n + 1 + 1) + ((n + 1 : ℕ) + 1) * σ ^ (n + 1) * y
        ≤ (σ + y) * (σ ^ (n + 1) + (n + 1) * σ ^ n * y) := by
          have : 0 ≤ (n + 1) * σ ^ n * y * y := by positivity
          have hexp : (σ + y) * (σ ^ (n + 1) + (n + 1) * σ ^ n * y) =
              σ ^ (n + 1 + 1) + (n + 1 + 1) * σ ^ (n + 1) * y + (n + 1) * σ ^ n * y * y := by
            ring
          push_cast
          linarith
      _ ≤ (σ + y) * (σ + y) ^ (n + 1) :=
          mul_le_mul_of_nonneg_left ih (add_nonneg hσ hy)
      _ = (σ + y) ^ (n + 1 + 1) := (pow_succ' _ _).symm

/-- The elementary symmetric polynomial is at most `(∑ x_i)^T / T!` for `x_i ≥ 0`. -/
theorem sum_powersetCard_prod_le (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) (T : ℕ) :
    ∑ I ∈ s.powersetCard T, ∏ i ∈ I, x i ≤ (∑ i ∈ s, x i) ^ T / T.factorial := by
  induction s using Finset.induction_on generalizing T with
  | empty =>
    cases T with
    | zero => simp
    | succ T =>
      simp [powersetCard_eq_empty.2 (show #(∅ : Finset ι) < T + 1 by simp)]
  | insert a s ha ih =>
    have hx' : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (mem_insert_of_mem hi)
    have hxa : 0 ≤ x a := hx a (mem_insert_self a s)
    have hσ : 0 ≤ ∑ i ∈ s, x i := sum_nonneg hx'
    rw [sum_insert ha, add_comm]
    cases T with
    | zero => simp [powersetCard_zero]
    | succ T =>
      rw [sum_powersetCard_succ_insert s a ha]
      have h1 := (le_div_iff₀ (by positivity : (0 : ℝ) < (T + 1).factorial)).1 (ih hx' (T + 1))
      have h0 := (le_div_iff₀ (by positivity : (0 : ℝ) < T.factorial)).1 (ih hx' T)
      have hf : ((T + 1).factorial : ℝ) = (T + 1) * T.factorial := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hy : 0 ≤ x a * (T + 1) := by positivity
      generalize ∑ i ∈ s, x i = σ at *
      generalize ∑ I ∈ s.powersetCard (T + 1), ∏ i ∈ I, x i = e1 at *
      generalize ∑ I ∈ s.powersetCard T, ∏ i ∈ I, x i = e0 at *
      rw [le_div_iff₀ (by positivity)]
      calc (e1 + x a * e0) * ((T + 1).factorial : ℝ)
          = e1 * (T + 1).factorial + x a * (T + 1) * (e0 * T.factorial) := by
            rw [hf]
            ring
        _ ≤ σ ^ (T + 1) + x a * (T + 1) * σ ^ T :=
            add_le_add h1 (mul_le_mul_of_nonneg_left h0 hy)
        _ = σ ^ (T + 1) + (T + 1) * σ ^ T * x a := by ring
        _ ≤ (σ + x a) ^ (T + 1) := pow_succ_add_mul_le_add_pow σ (x a) hσ hxa T

end Erdos408.OneSided
