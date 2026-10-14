import Erdos821.P5.Basic

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

def tupleProduct {s : Finset ℕ} {j : ℕ} (z : Fin j → ↥s) : ℕ :=
  ∏ i, (z i).val

def primePowerCoefficient (s : Finset ℕ) (b : ℕ → ℂ) (j n : ℕ) : ℂ :=
  ∑ z : Fin j → ↥s, if tupleProduct z = n then
    ∏ i, b (z i).val / ((z i).val : ℂ) else 0

theorem tupleProduct_pos {s : Finset ℕ} {j : ℕ} (z : Fin j → ↥s)
    (hprime : ∀ p ∈ s, p.Prime) : 0 < tupleProduct z := by
  exact Finset.prod_pos (fun i _ => (hprime _ (z i).property).pos)

theorem tupleProduct_le {s : Finset ℕ} {j : ℕ} (z : Fin j → ↥s) :
    tupleProduct z ≤ (s.sup id) ^ j := by
  calc
    tupleProduct z ≤ ∏ _i : Fin j, s.sup id :=
      Finset.prod_le_prod (fun i _ => Finset.le_sup (f := id) (z i).property)
    _ = _ := by simp

/-- Expanding the power retains repeated primes and all ordered tuples. -/
theorem prime_polynomial_power (s : Finset ℕ) (b : ℕ → ℂ) (j : ℕ)
    (hprime : ∀ p ∈ s, p.Prime) (t : ℝ) :
    dp (Finset.Icc 1 ((s.sup id) ^ j)) (primePowerCoefficient s b j) t =
      (primePolynomial s b t) ^ j := by
  classical
  let w := fun z : Fin j → ↥s => ∏ i, b (z i).val / ((z i).val : ℂ)
  have hsupport (z : Fin j → ↥s) : tupleProduct z ∈ Finset.Icc 1 ((s.sup id) ^ j) :=
    Finset.mem_Icc.mpr ⟨tupleProduct_pos z hprime, tupleProduct_le z⟩
  have hfiber (n : ℕ) : primePowerCoefficient s b j n * mellin n t =
      ∑ z ∈ (Finset.univ : Finset (Fin j → ↥s)).filter
        (fun z => tupleProduct z = n), w z * mellin (tupleProduct z) t := by
    rw [primePowerCoefficient, Finset.sum_mul, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : tupleProduct z = n
    · simp only [h, ite_true]
      rfl
    · simp only [h, ite_false, zero_mul]
  have hmellin (z : Fin j → ↥s) :
      mellin (tupleProduct z) t = ∏ i, mellin (z i).val t := by
    rw [tupleProduct, Nat.cast_prod]
    exact mellin_prod _ _ t (fun i _ => by exact_mod_cast (hprime _ (z i).property).pos)
  calc
    _ = ∑ n ∈ Finset.Icc 1 ((s.sup id) ^ j),
        ∑ z ∈ (Finset.univ : Finset (Fin j → ↥s)).filter
          (fun z => tupleProduct z = n), w z * mellin (tupleProduct z) t := by
      unfold dp
      exact Finset.sum_congr rfl (fun n _ => hfiber n)
    _ = ∑ z : Fin j → ↥s, w z * mellin (tupleProduct z) t :=
      Finset.sum_fiberwise_of_maps_to (fun z _ => hsupport z) _
    _ = (∑ p : ↥s, b p.val / (p.val : ℂ) * mellin p.val t) ^ j := by
      simp_rw [hmellin, w, ← Finset.prod_mul_distrib]
      exact (Fintype.sum_pow
        (fun p : ↥s => b p.val / (p.val : ℂ) * mellin p.val t) j).symm
    _ = _ := by
      congr 1
      exact (Finset.sum_subtype s (by simp)
        (fun p => b p / (p : ℂ) * mellin p t)).symm

/-- Unique factorization bounds ordered prime-product fibers, including repeated primes. -/
theorem prime_product_fiber_card (s : Finset ℕ) (j n : ℕ)
    (hprime : ∀ p ∈ s, p.Prime) :
    ((Finset.univ : Finset (Fin j → ↥s)).filter
      (fun z => tupleProduct z = n)).card ≤ Nat.factorial j := by
  classical
  let fiber := (Finset.univ : Finset (Fin j → ↥s)).filter (fun z => tupleProduct z = n)
  by_cases h : fiber.Nonempty
  · obtain ⟨z₀, hz₀⟩ := h
    let listOf := fun z : Fin j → ↥s => List.ofFn (fun i => (z i).val)
    have h₀ : tupleProduct z₀ = n := (Finset.mem_filter.mp hz₀).2
    have hcard : fiber.card ≤ (listOf z₀).permutations.toFinset.card := by
      apply Finset.card_le_card_of_injOn listOf
      · intro z hz
        apply List.mem_toFinset.mpr
        apply List.mem_permutations.mpr
        apply perm_of_prod_eq_prod
        · simpa [listOf, List.prod_ofFn, tupleProduct] using
            ((Finset.mem_filter.mp hz).2.trans h₀.symm)
        · intro p hp
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
          exact (hprime _ (z i).property).prime
        · intro p hp
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
          exact (hprime _ (z₀ i).property).prime
      · intro z _ w _ hzw
        have hv := List.ofFn_injective hzw
        funext i
        exact Subtype.ext (congrFun hv i)
    exact hcard.trans (by simpa only [listOf, List.length_permutations, List.length_ofFn] using
      (listOf z₀).permutations.toFinset_card_le)
  · have : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simpa [fiber, this] using Nat.zero_le (Nat.factorial j)

/-- A finite fiber Cauchy bound, independent of the prime-polynomial application. -/
theorem norm_sum_sq_le_card_mul_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ n ∈ s, f n‖ ^ 2 ≤ (s.card : ℝ) * ∑ n ∈ s, ‖f n‖ ^ 2 := by
  calc
    ‖∑ n ∈ s, f n‖ ^ 2 ≤ (∑ n ∈ s, ‖f n‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := sq_sum_le_card_mul_sum_sq

/-- The growing-power moment has exactly the factorial cost, for any finite index set. -/
theorem prime_polynomial_moment (s : Finset ℕ) (b : ℕ → ℂ) (j : ℕ)
    (hprime : ∀ p ∈ s, p.Prime) (r : Finset ℕ) :
    (∑ n ∈ r, ‖primePowerCoefficient s b j n‖ ^ 2) ≤
      Nat.factorial j * (∑ p ∈ s, ‖b p‖ ^ 2 / (p : ℝ) ^ 2) ^ j := by
  classical
  let w := fun z : Fin j → ↥s => ∏ i, b (z i).val / ((z i).val : ℂ)
  have hlocal (n : ℕ) : ‖primePowerCoefficient s b j n‖ ^ 2 ≤
      (Nat.factorial j : ℝ) *
        ∑ z ∈ (Finset.univ : Finset (Fin j → ↥s)).filter
          (fun z => tupleProduct z = n), ‖w z‖ ^ 2 := by
    rw [primePowerCoefficient, ← Finset.sum_filter]
    calc
      _ ≤ _ := norm_sum_sq_le_card_mul_sum _ w
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast prime_product_fiber_card s j n hprime) (by positivity)
  calc
    _ ≤ (Nat.factorial j : ℝ) *
        ∑ n ∈ r, ∑ z ∈ (Finset.univ : Finset (Fin j → ↥s)).filter
          (fun z => tupleProduct z = n), ‖w z‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun n _ => hlocal n)
    _ ≤ (Nat.factorial j : ℝ) * ∑ z : Fin j → ↥s, ‖w z‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.sum_fiberwise_eq_sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro z _ _
      positivity
    _ = _ := by
      congr 1
      simp only [w, norm_prod, norm_div, Complex.norm_natCast, ← Finset.prod_pow]
      simp only [div_pow]
      rw [← Fintype.sum_pow (fun p : ↥s => ‖b p.val‖ ^ 2 / (p.val : ℝ) ^ 2) j]
      congr 1
      exact (Finset.sum_subtype s (by simp) (fun p => ‖b p‖ ^ 2 / (p : ℝ) ^ 2)).symm

end Erdos821.P5Core
