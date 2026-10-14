import Erdos408.Extraction.TypeII.Strip

/-!
# The composite and proxy sums as telescoping sums

`Comp_j`, the unstripped proxy sum `Prox_j^0` and `Prox_j` are sums over `m ∈ [1, M]^j` of
`Ψ(∏ m) ∏ w(m_i)` with `w` the prime weight, `a_j^0` and `a_j`. Telescoping one factor at a
time turns `Comp_j - Prox_j^0` into `j` steps with coefficient `[prime, > x^γ] - a_j^0`, and
`Prox_j^0 - Prox_j` into `j` steps with coefficient `a_j^0 - a_j`.
-/

namespace Erdos408.TypeII

open Finset Real

/-- The composite sum as a tuple sum over `[1, M]^j` with prime weights. -/
theorem compositeSum_eq (q cw : ℝ) (K : ℕ) (CN x γ κ : ℝ) (j : ℕ)
    (Φ : ℝ → ℝ) {k : ℕ} (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) :
    compositeSum q cw K CN x γ κ j Φ u v B =
      ∑ m ∈ Fintype.piFinset (fun _ : Fin j => Icc 1 ⌊κ * x + 1⌋₊),
        cutPsi Φ (endpoint q cw K CN x u v B) x (∏ i, m i) * ∏ i, primeWeight x γ (m i) := by
  unfold compositeSum
  have hsub : Fintype.piFinset (fun _ : Fin j => primesIcc (x ^ γ) (κ * x + 1)) ⊆
      Fintype.piFinset (fun _ : Fin j => Icc 1 ⌊κ * x + 1⌋₊) := by
    refine Fintype.piFinset_subset _ _ fun i p hp => ?_
    obtain ⟨hpp, hlo, hhi⟩ := mem_primesIcc.1 hp
    exact mem_Icc.2 ⟨hpp.one_lt.le, hhi⟩
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun p hp => ?_
    have hpr : ∀ i, (p i).Prime := fun i =>
      (mem_primesIcc.1 (Fintype.mem_piFinset.1 hp i)).1
    unfold cutPsi primeWeight
    split_ifs with h
    · have h1 : ∏ i, (if (p i).Prime ∧ x ^ γ < p i then (1 : ℝ) else 0) = 1 :=
        prod_eq_one fun i _ => by simp only [hpr i, h i, and_self, ↓reduceIte]
      rw [h1, mul_one]
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have h0 : ∏ i, (if (p i).Prime ∧ x ^ γ < p i then (1 : ℝ) else 0) = 0 :=
        prod_eq_zero (mem_univ i) (by
          simp only [not_lt.2 hi, and_false, ↓reduceIte])
      rw [h0, mul_zero]
  · intro m hm hmp
    rw [mul_eq_zero]
    right
    rw [Fintype.mem_piFinset] at hmp
    push Not at hmp
    obtain ⟨i, hi⟩ := hmp
    refine prod_eq_zero (mem_univ i) ?_
    unfold primeWeight
    refine ite_eq_right_iff.2 fun h => ?_
    obtain ⟨hp, hlt⟩ := h
    exfalso
    apply hi
    have hmi := (mem_Icc.1 (Fintype.mem_piFinset.1 hm i)).2
    exact mem_primesIcc.2 ⟨hp, Nat.ceil_le.2 hlt.le, hmi⟩

/-- The proxy sum as a tuple sum. -/
theorem proxySum_eq (q cw : ℝ) (K : ℕ) (CN x γ κ : ℝ) (j : ℕ) (Φ : ℝ → ℝ) {k : ℕ}
    (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) :
    proxySum q cw K CN x γ κ j Φ u v B =
      ∑ m ∈ Fintype.piFinset (fun _ : Fin j => Icc 1 ⌊κ * x + 1⌋₊),
        cutPsi Φ (endpoint q cw K CN x u v B) x (∏ i, m i) * ∏ i, strippedProxy x γ j (m i) := by
  unfold proxySum cutPsi
  push_cast
  rfl

/-- Telescoping a difference of tuple sums. -/
theorem sum_sub_sum_eq_steps (S : Finset ℕ) (Ψ : ℕ → ℝ) (A B : ℕ → ℝ) (r : ℕ) :
    ∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 1) => S), Ψ (∏ i, m i) * ∏ i, A (m i) -
      ∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 1) => S), Ψ (∏ i, m i) * ∏ i, B (m i) =
      ∑ i : Fin (r + 1), ∑ m₀ ∈ S, ∑ m' ∈ Fintype.piFinset (fun _ : Fin r => S),
        Ψ (m₀ * ∏ k, m' k) * (A m₀ - B m₀) *
          ∏ k, (if i.succAbove k < i then B else A) (m' k) := by
  rw [← sum_prod_sub_prod_eq, ← sum_sub_distrib]
  exact sum_congr rfl fun m _ => (mul_sub _ _ _).symm

theorem primeWeight_sub_unstripped (x γ : ℝ) (j m : ℕ) :
    primeWeight x γ m - unstrippedProxy x γ j m = primeProxyDiff x γ j m := rfl

end Erdos408.TypeII
