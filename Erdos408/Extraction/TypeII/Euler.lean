module

public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Euler products for completely multiplicative weights

For a weight `loc` on the primes, `cmul loc` is the completely multiplicative
function `n ↦ ∏_{p^e ∥ n} loc(p)^e`. If `0 ≤ loc p < 1` at every prime, its
sum over `[1, N]` is at most `∏_{p ≤ N} (1 - loc p)⁻¹`, by the Euler product
over the `N`-factored numbers. The product is at most `exp(2 ∑ loc p)` when
every `loc p ≤ 1/2`.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real

/-- The completely multiplicative function `n ↦ ∏_{p^e ∥ n} loc(p)^e`, with
value `0` at `0`. -/
noncomputable def cmul (loc : ℕ → ℝ) : ℕ →* ℝ where
  toFun n := if n = 0 then 0 else n.factorization.prod fun p e => loc p ^ e
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [mul_eq_zero, hm, hn, or_self, ite_false, Nat.factorization_mul hm hn]
    exact Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _

theorem cmul_apply {loc : ℕ → ℝ} {n : ℕ} (hn : n ≠ 0) :
    cmul loc n = n.factorization.prod fun p e => loc p ^ e := by
  simp [cmul, hn]

theorem cmul_prime_pow (loc : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    cmul loc (p ^ e) = loc p ^ e := by
  rw [cmul_apply (pow_ne_zero _ hp.ne_zero), hp.factorization_pow]
  exact Finsupp.prod_single_index (pow_zero _)

theorem cmul_prime (loc : ℕ → ℝ) {p : ℕ} (hp : p.Prime) : cmul loc p = loc p := by
  simpa using cmul_prime_pow loc hp 1

/-- `cmul loc` is nonnegative when `loc` is nonnegative at the primes. -/
theorem cmul_nonneg {loc : ℕ → ℝ} (h0 : ∀ p, p.Prime → 0 ≤ loc p) (n : ℕ) :
    0 ≤ cmul loc n := by
  by_cases hn : n = 0
  · simp [cmul, hn]
  rw [cmul_apply hn]
  exact Finset.prod_nonneg fun p hp =>
    pow_nonneg (h0 p (Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp))) _

/-- `cmul` is monotone in the prime weights. -/
theorem cmul_le_cmul {loc loc' : ℕ → ℝ} (h0 : ∀ p, p.Prime → 0 ≤ loc p)
    (h : ∀ p, p.Prime → loc p ≤ loc' p) (n : ℕ) : cmul loc n ≤ cmul loc' n := by
  by_cases hn : n = 0
  · simp [cmul, hn]
  rw [cmul_apply hn, cmul_apply hn]
  refine Finset.prod_le_prod₀ (fun p hp => pow_nonneg (h0 p ?_) _) fun p hp =>
    pow_le_pow_left₀ (h0 p ?_) (h p ?_) _ <;>
    exact Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)

/-- `cmul` of a pointwise product of prime weights is the product. -/
theorem cmul_mul_loc (loc loc' : ℕ → ℝ) (n : ℕ) :
    cmul (fun p => loc p * loc' p) n = cmul loc n * cmul loc' n := by
  by_cases hn : n = 0
  · simp [cmul, hn]
  rw [cmul_apply hn, cmul_apply hn, cmul_apply hn, ← Finsupp.prod_mul]
  exact Finsupp.prod_congr fun p _ => mul_pow _ _ _

/-- `n = ∏_{p^e ∥ n} p^e` in `ℝ`. -/
theorem natCast_eq_factorization_prod {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) = n.factorization.prod fun p e => (p : ℝ) ^ e := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Finsupp.prod, Nat.cast_prod]
  push_cast
  rfl

/-- `n^θ` is completely multiplicative: `cmul (p ↦ p^θ) n = n^θ`. -/
theorem cmul_rpow (θ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    cmul (fun p => (p : ℝ) ^ θ) n = (n : ℝ) ^ θ := by
  rw [cmul_apply hn, natCast_eq_factorization_prod hn, Finsupp.prod, Finsupp.prod,
    ← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
  exact prod_congr rfl fun p _ => (Real.rpow_pow_comm (Nat.cast_nonneg p) θ _)

/-- `1/n` is completely multiplicative. -/
theorem cmul_inv {n : ℕ} (hn : n ≠ 0) : cmul (fun p => (p : ℝ)⁻¹) n = (n : ℝ)⁻¹ := by
  have h := cmul_rpow (-1) hn
  simp only [Real.rpow_neg_one] at h
  exact h

/-- `f(n) / n` for a completely multiplicative `f`. -/
theorem cmul_div {loc : ℕ → ℝ} {n : ℕ} (hn : n ≠ 0) :
    cmul loc n / n = cmul (fun p => loc p / p) n := by
  rw [div_eq_mul_inv, ← cmul_inv hn, ← cmul_mul_loc]
  rfl

/-- `cmul loc n` only depends on `loc` at the prime factors of `n`. -/
theorem cmul_congr {loc loc' : ℕ → ℝ} {n : ℕ} (h : ∀ p ∈ n.primeFactors, loc p = loc' p) :
    cmul loc n = cmul loc' n := by
  by_cases hn : n = 0
  · simp [cmul, hn]
  rw [cmul_apply hn, cmul_apply hn]
  exact Finsupp.prod_congr fun p hp => by
    rw [h p (Nat.support_factorization n ▸ hp)]

/-- `cmul loc n ≤ 1` when `0 ≤ loc ≤ 1` at the primes. -/
theorem cmul_le_one {loc : ℕ → ℝ} (h0 : ∀ p, p.Prime → 0 ≤ loc p)
    (h1 : ∀ p, p.Prime → loc p ≤ 1) (n : ℕ) : cmul loc n ≤ 1 := by
  by_cases hn : n = 0
  · simp [cmul, hn]
  rw [cmul_apply hn]
  refine Finset.prod_le_one₀ (fun p hp => pow_nonneg (h0 p ?_) _) fun p hp =>
    pow_le_one₀ (h0 p ?_) (h1 p ?_) <;>
    exact Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)

/-- `cmul loc n = 0` when `loc` vanishes at a prime factor of `n`. -/
theorem cmul_eq_zero {loc : ℕ → ℝ} {n p : ℕ} (hp : p ∈ n.primeFactors) (h : loc p = 0) :
    cmul loc n = 0 := by
  have hn : n ≠ 0 := (Nat.mem_primeFactors.1 hp).2.2
  rw [cmul_apply hn, Finsupp.prod]
  refine Finset.prod_eq_zero (Nat.support_factorization n ▸ hp) ?_
  rw [h, zero_pow]
  exact ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn
    (Nat.dvd_of_mem_primeFactors hp)).ne'

/-- The Euler-product bound `∑_{m ≤ N} cmul loc m ≤ ∏_{p ≤ N} (1 - loc p)⁻¹`. -/
theorem sum_cmul_le_prod {loc : ℕ → ℝ} (h0 : ∀ p, p.Prime → 0 ≤ loc p)
    (h1 : ∀ p, p.Prime → loc p < 1) (N : ℕ) :
    ∑ m ∈ Icc 1 N, cmul loc m ≤ ∏ p ∈ (range (N + 1)).filter Nat.Prime, (1 - loc p)⁻¹ := by
  have hnorm : ∀ {p : ℕ}, p.Prime → ‖cmul loc p‖ < 1 := fun {p} hp => by
    rw [cmul_prime loc hp, Real.norm_of_nonneg (h0 p hp)]
    exact h1 p hp
  have hsum := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    hnorm (range (N + 1))).2
  have hprod : ∏ p ∈ (range (N + 1)).filter Nat.Prime, (1 - cmul loc p)⁻¹ =
      ∏ p ∈ (range (N + 1)).filter Nat.Prime, (1 - loc p)⁻¹ :=
    prod_congr rfl fun p hp => by rw [cmul_prime loc (mem_filter.1 hp).2]
  rw [hprod] at hsum
  have hmem : ∀ m ∈ Icc 1 N, m ∈ Nat.factoredNumbers (range (N + 1)) := by
    intro m hm
    obtain ⟨h1m, hmN⟩ := mem_Icc.1 hm
    refine ⟨by omega, fun p hp => mem_range.2 ?_⟩
    have := Nat.le_of_mem_primeFactorsList hp
    omega
  let s : Finset (Nat.factoredNumbers (range (N + 1))) :=
    (Icc 1 N).attach.map ⟨fun m => ⟨m.1, hmem m.1 m.2⟩, fun a b h => by
      exact Subtype.ext (congrArg Subtype.val h :)⟩
  have hs : ∑ m ∈ Icc 1 N, cmul loc m = ∑ m ∈ s, cmul loc m := by
    rw [sum_map, ← sum_attach]
    rfl
  rw [hs]
  exact sum_le_hasSum s (fun m _ => cmul_nonneg h0 m) hsum

/-- `∏ (1 - y_p)⁻¹ ≤ exp(2 ∑ y_p)` when `0 ≤ y_p ≤ 1/2`. -/
theorem prod_inv_one_sub_le_exp {ι : Type*} (S : Finset ι) (y : ι → ℝ)
    (h0 : ∀ i ∈ S, 0 ≤ y i) (h1 : ∀ i ∈ S, y i ≤ 1 / 2) :
    ∏ i ∈ S, (1 - y i)⁻¹ ≤ Real.exp (2 * ∑ i ∈ S, y i) := by
  rw [mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun i hi => inv_nonneg.2 (by linarith [h1 i hi])) fun i hi => ?_
  have hy0 := h0 i hi
  have hy1 := h1 i hi
  have hpos : 0 < 1 - y i := by linarith
  calc (1 - y i)⁻¹ ≤ 1 + 2 * y i := by
        rw [inv_le_iff_one_le_mul₀ hpos]
        nlinarith
    _ ≤ Real.exp (2 * y i) := by linarith [Real.add_one_le_exp (2 * y i)]

end Erdos408.TypeII
