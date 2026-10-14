module

public import Erdos408.Extraction.Allocation.Groups
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.SmoothNumbers

/-!
# Reciprocal sums over factored numbers

Elementary Euler-product bounds used for the mean square of the core.

* The reciprocals of the `S`-factored numbers in a finite set sum to at most
  `∏_{p ∈ S} (1 - 1/p)⁻¹ ≤ exp(2 ∑_{p ∈ S} 1/p)`.
* `∏_{p ≤ Y} (1 - 1/p) ≥ C₁ / log Y` (Mertens' product theorem, lower
  bound), from `log(1 - t) ≥ -t - 2t²` on `[0, 1/2]` and Mertens' second
  theorem.
-/

@[expose] public section

namespace Erdos408

open Finset Real

/-- The reciprocals of finitely many `S`-factored numbers sum to at most
`∏_{p ∈ S} (1 - 1/p)⁻¹`. -/
lemma sum_inv_le_prod_of_factored (S : Finset ℕ) (F : Finset ℕ)
    (hF : ∀ n ∈ F, n ∈ Nat.factoredNumbers S) :
    ∑ n ∈ F, (1 : ℝ) / n ≤ ∏ p ∈ S with p.Prime, (1 - (1 : ℝ) / p)⁻¹ := by
  -- the Euler product for `n ↦ 1/n`
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → (1 : ℝ) / (m * n : ℕ) = 1 / m * (1 / n) := by
    intro m n _
    push_cast
    rw [one_div_mul_one_div]
  have hsum : ∀ {p : ℕ}, p.Prime → Summable fun n : ℕ => ‖(1 : ℝ) / (p ^ n : ℕ)‖ := by
    intro p hp
    have h1 : (1 : ℝ) / p < 1 := by
      rw [div_lt_one (by exact_mod_cast hp.pos)]
      exact_mod_cast hp.one_lt
    refine (summable_geometric_of_lt_one (by positivity) h1).congr fun n => ?_
    rw [norm_of_nonneg (by positivity)]
    push_cast
    rw [one_div_pow]
  obtain ⟨-, hhas⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (1 : ℝ) / n) (by simp) hmul hsum S
  have hgeom : ∀ p ∈ S.filter Nat.Prime, ∑' n : ℕ, (1 : ℝ) / (p ^ n : ℕ) = (1 - (1 : ℝ) / p)⁻¹ := by
    intro p hp
    have hp := (mem_filter.1 hp).2
    have h1 : (1 : ℝ) / p < 1 := by
      rw [div_lt_one (by exact_mod_cast hp.pos)]
      exact_mod_cast hp.one_lt
    rw [← tsum_geometric_of_lt_one (by positivity) h1]
    exact tsum_congr fun n => by push_cast; rw [one_div_pow]
  rw [prod_congr rfl hgeom] at hhas
  have hle := sum_le_hasSum (F.subtype (· ∈ Nat.factoredNumbers S))
    (fun i _ => by positivity) hhas
  rw [Finset.sum_subtype_eq_sum_filter (f := fun n : ℕ => (1 : ℝ) / n),
    filter_true_of_mem hF] at hle
  exact hle

/-- `(1 - 1/p)⁻¹ ≤ exp(2/p)` for `p ≥ 2`. -/
lemma inv_one_sub_le_exp {p : ℝ} (hp : 2 ≤ p) : (1 - 1 / p)⁻¹ ≤ Real.exp (2 / p) := by
  have ht : 1 / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp
  have ht0 : 0 < 1 / p := by positivity
  rw [inv_le_comm₀ (by linarith) (exp_pos _), ← exp_neg]
  -- `exp(-2t) ≤ 1 / (1 + 2t) ≤ 1 - t` for `0 ≤ t ≤ 1/2`
  have h1 : Real.exp (-(2 / p)) ≤ 1 / (1 + 2 / p) := by
    rw [exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [add_one_le_exp (2 / p)])
  have h2 : 1 / (1 + 2 / p) ≤ 1 - 1 / p := by
    rw [div_le_iff₀ (by positivity)]
    have : 2 / p = 2 * (1 / p) := by ring
    rw [this]
    nlinarith
  linarith

/-- `∏_{p ∈ S} (1 - 1/p)⁻¹ ≤ exp(2 ∑_{p ∈ S} 1/p)` over primes. -/
lemma prod_inv_one_sub_le_exp (S : Finset ℕ) :
    ∏ p ∈ S with p.Prime, (1 - (1 : ℝ) / p)⁻¹ ≤
      Real.exp (2 * ∑ p ∈ S with p.Prime, (1 : ℝ) / p) := by
  rw [mul_sum, exp_sum]
  refine prod_le_prod₀ (fun p hp => ?_) fun p hp => ?_
  · have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    exact (inv_pos.2 (by linarith)).le
  · have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.1 hp).2.two_le
    rw [mul_one_div]
    exact inv_one_sub_le_exp h2

/-- Mertens' product theorem, lower bound: `∏_{p ≤ Y} (1 - 1/p) ≥ C₁ / log Y`. -/
lemma exists_prod_one_sub_ge : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ Y : ℝ, 2 ≤ Y →
    C₁ / Real.log Y ≤ ∏ p ∈ primesIcc 2 Y, (1 - (1 : ℝ) / p) := by
  obtain ⟨E, hE, hM⟩ := mertens_second
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 * Real.exp (-(5 / 2 + E / Real.log 2)), by positivity, fun Y hY => ?_⟩
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hp2 : ∀ p ∈ primesIcc 2 Y, (2 : ℝ) ≤ p := fun p hp => by
    have := (mem_filter.1 hp).1
    rw [mem_Icc, Nat.ceil_le] at this
    exact this.1
  have hpos : ∀ p ∈ primesIcc 2 Y, 0 < 1 - (1 : ℝ) / p := fun p hp => by
    have := hp2 p hp
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  -- `log(1 - 1/p) ≥ -1/p - 2/p²`
  have hlog : ∀ p ∈ primesIcc 2 Y, -(1 : ℝ) / p - 2 * ((p : ℝ) ^ 2)⁻¹ ≤ Real.log (1 - 1 / p) := by
    intro p hp
    have h2 := hp2 p hp
    have ht : |(1 : ℝ) / p| < 1 := by
      rw [abs_of_pos (by positivity), div_lt_one (by linarith)]
      linarith
    have h := abs_le.1 (Real.abs_log_sub_add_sum_range_le ht 1)
    simp only [range_one, sum_singleton, pow_one, Nat.cast_zero, zero_add, div_one] at h
    have hq : |(1 : ℝ) / p| ^ (1 + 1) / (1 - |(1 : ℝ) / p|) ≤ 2 * ((p : ℝ) ^ 2)⁻¹ := by
      set t := (1 : ℝ) / p with htdef
      have ht0 : 0 < t := by positivity
      have ht2 : t ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
      have hpt : ((p : ℝ) ^ 2)⁻¹ = t ^ 2 := by rw [htdef, one_div_pow, one_div]
      rw [abs_of_pos ht0, hpt, div_le_iff₀ (by linarith), show t ^ (1 + 1) = t ^ 2 by norm_num]
      nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 1 - 2 * t by linarith)]
    have : -(1 : ℝ) / p = -(1 / p) := by ring
    linarith [h.1]
  -- the reciprocal sums
  have hsum1 : ∑ p ∈ primesIcc 2 Y, (1 : ℝ) / p ≤ 1 / 2 + Real.log (Real.log Y / Real.log 2) +
      E / Real.log 2 := by
    have hsplit : primesIcc 2 Y ⊆ insert 2 (primesIoc 2 Y) := by
      intro p hp
      obtain ⟨hpr, h1, h2⟩ := (mem_primesIcc.1 hp)
      rcases eq_or_lt_of_le (show (2 : ℝ) ≤ p from h1) with h | h
      · rw [show p = 2 by exact_mod_cast h.symm]
        exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_primesIoc.2 ⟨hpr, h, h2⟩)
    calc ∑ p ∈ primesIcc 2 Y, (1 : ℝ) / p ≤ ∑ p ∈ insert 2 (primesIoc 2 Y), (1 : ℝ) / p :=
          sum_le_sum_of_subset_of_nonneg hsplit fun _ _ _ => by positivity
      _ = 1 / 2 + ∑ p ∈ primesIoc 2 Y, (1 : ℝ) / p := by
          rw [sum_insert (by simp [mem_primesIoc])]
          norm_num
      _ ≤ _ := by
          have := (abs_le.1 (hM 2 Y le_rfl hY)).2
          linarith
  have hsum2 : ∑ p ∈ primesIcc 2 Y, ((p : ℝ) ^ 2)⁻¹ ≤ 1 := by
    have hsub : primesIcc 2 Y ⊆ Ioo 1 (⌊Y⌋₊ + 1) := by
      intro p hp
      obtain ⟨hpr, -, h2⟩ := mem_primesIcc.1 hp
      exact mem_Ioo.2 ⟨hpr.one_lt, Nat.lt_succ_of_le (Nat.le_floor h2)⟩
    calc ∑ p ∈ primesIcc 2 Y, ((p : ℝ) ^ 2)⁻¹ ≤ ∑ i ∈ Ioo 1 (⌊Y⌋₊ + 1), ((i : ℝ) ^ 2)⁻¹ :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ ≤ 2 / ((1 : ℕ) + 1 : ℝ) := sum_Ioo_inv_sq_le 1 _
      _ = 1 := by norm_num
  have hprod_pos : 0 < ∏ p ∈ primesIcc 2 Y, (1 - (1 : ℝ) / p) := prod_pos hpos
  have hlogprod : -(5 / 2 + E / Real.log 2) - Real.log (Real.log Y / Real.log 2) ≤
      Real.log (∏ p ∈ primesIcc 2 Y, (1 - (1 : ℝ) / p)) := by
    rw [Real.log_prod fun p hp => (hpos p hp).ne']
    calc -(5 / 2 + E / Real.log 2) - Real.log (Real.log Y / Real.log 2)
        ≤ ∑ p ∈ primesIcc 2 Y, (-(1 : ℝ) / p - 2 * ((p : ℝ) ^ 2)⁻¹) := by
          rw [sum_sub_distrib, ← mul_sum]
          simp only [neg_div, sum_neg_distrib]
          linarith
      _ ≤ _ := sum_le_sum hlog
  rw [← exp_log hprod_pos]
  calc Real.log 2 * Real.exp (-(5 / 2 + E / Real.log 2)) / Real.log Y
      = Real.exp (-(5 / 2 + E / Real.log 2) - Real.log (Real.log Y / Real.log 2)) := by
        rw [exp_sub, exp_log (div_pos hlY hl2)]
        field_simp
    _ ≤ _ := exp_le_exp.2 hlogprod

end Erdos408
