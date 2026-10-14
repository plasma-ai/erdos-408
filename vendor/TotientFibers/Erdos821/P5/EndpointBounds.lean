import Erdos821.P5.Basic

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P5Core
open Blueprint.Analytic

def factorTriples (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 N).product ((Finset.Icc 1 N).product (Finset.Icc 1 N))).filter
    (fun u => u.1 * u.2.1 * u.2.2 = N)

theorem factorTriples_info (N : ℕ) (u : ℕ × ℕ × ℕ) (hu : u ∈ factorTriples N) :
    0 < u.1 ∧ 0 < u.2.1 ∧ 0 < u.2.2 ∧ u.1 * u.2.1 * u.2.2 = N := by
  obtain ⟨huI, hfact⟩ := Finset.mem_filter.mp hu
  obtain ⟨hm, hpr⟩ := Finset.mem_product.mp huI
  obtain ⟨hp, hr⟩ := Finset.mem_product.mp hpr
  exact ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hp).1,
    (Finset.mem_Icc.mp hr).1, hfact⟩

/-- The residual factor is determined by its divisor pair. -/
theorem factorTriples_card_le (N : ℕ) : (factorTriples N).card ≤ N.divisors.card ^ 2 := by
  classical
  have hmap (u : ℕ × ℕ × ℕ) (hu : u ∈ factorTriples N) :
      (u.1, u.2.1) ∈ N.divisors.product N.divisors := by
    obtain ⟨hm, hp, hr, hfact⟩ := factorTriples_info N u hu
    have hN : N ≠ 0 := by
      have h : 0 < N := by rw [← hfact]; positivity
      omega
    apply Finset.mem_product.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨⟨u.2.1 * u.2.2, by rw [← hfact]; ring⟩, hN⟩
    · exact Nat.mem_divisors.mpr ⟨⟨u.1 * u.2.2, by rw [← hfact]; ring⟩, hN⟩
  have hinj : (factorTriples N : Set (ℕ × ℕ × ℕ)).InjOn (fun u => (u.1, u.2.1)) := by
    intro u hu v hv heq
    obtain ⟨hm, hp, _hr, hfact⟩ := factorTriples_info N u hu
    have hfactv := (factorTriples_info N v hv).2.2.2
    have hmEq : u.1 = v.1 := congrArg (fun w : ℕ × ℕ => w.1) heq
    have hpEq : u.2.1 = v.2.1 := congrArg (fun w : ℕ × ℕ => w.2) heq
    have hfactv' : u.1 * u.2.1 * v.2.2 = N := by simpa only [hmEq, hpEq] using hfactv
    have hrEq := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hm hp) (hfact.trans hfactv'.symm)
    exact Prod.ext hmEq (Prod.ext hpEq hrEq)
  have hcard := Finset.card_le_card_of_injOn (fun u : ℕ × ℕ × ℕ => (u.1, u.2.1)) hmap hinj
  simpa only [Finset.product_eq_sprod, Finset.card_product, pow_two] using hcard

theorem endpoint_factorization (G : PrimeGroups) (x : ℝ) (E : Endpoint) (n : ℕ) :
    endpoint G x E n = ∑ u ∈ factorTriples (groupFreePart G n),
      if E.lo ≤ (u.2.1 : ℝ) ∧ (u.2.1 : ℝ) ≤ E.hi ∧ rough (W x) u.2.1 then
        E.alpha u.1 * E.chi (u.1 : ZMod E.modulus) * mellin u.1 E.sigma₀ *
          mellin u.2.1 E.sigma₁ * E.residual u.2.2 else 0 := by
  simp only [endpoint, factorTriples, Finset.sum_filter, Finset.product_eq_sprod,
    Finset.sum_product, ite_and]

/-- §4 endpoint bound independent of the graph depth and probe count. -/
theorem endpoint_norm_le (G : PrimeGroups) (x C τ η : ℝ) (E : Endpoint)
    (hL : 1 ≤ L x) (hE : EndpointBound x C τ η E) (n : ℕ) :
    ‖endpoint G x E n‖ ≤ L x ^ (2 * C) * ((groupFreePart G n).divisors.card : ℝ) ^ 2 := by
  classical
  have hLpos : 0 < L x := by linarith
  have hcoeff := hE.2.2.2.1
  have hterm (m p r : ℕ) :
      ‖E.alpha m * E.chi (m : ZMod E.modulus) * mellin m E.sigma₀ *
        mellin p E.sigma₁ * E.residual r‖ ≤ L x ^ (2 * C) := by
    simp only [norm_mul, norm_mellin, mul_one]
    calc
      _ ≤ L x ^ C * 1 * L x ^ C :=
        mul_le_mul (mul_le_mul (hcoeff m).1 (E.chi.norm_le_one _) (norm_nonneg _)
          (Real.rpow_nonneg hLpos.le C)) (hcoeff r).2 (norm_nonneg _) (by positivity)
      _ = _ := by simp only [mul_one]; rw [← Real.rpow_add hLpos]; congr 1; ring
  rw [endpoint_factorization]
  calc
    _ ≤ ∑ u ∈ factorTriples (groupFreePart G n),
        ‖if E.lo ≤ (u.2.1 : ℝ) ∧ (u.2.1 : ℝ) ≤ E.hi ∧ rough (W x) u.2.1 then
          E.alpha u.1 * E.chi (u.1 : ZMod E.modulus) * mellin u.1 E.sigma₀ *
            mellin u.2.1 E.sigma₁ * E.residual u.2.2 else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ factorTriples (groupFreePart G n), L x ^ (2 * C) := by
      apply Finset.sum_le_sum
      intro u hu
      split_ifs
      · exact hterm _ _ _
      · simp only [norm_zero]; positivity
    _ = ((factorTriples (groupFreePart G n)).card : ℝ) * L x ^ (2 * C) := by simp
    _ ≤ ((groupFreePart G n).divisors.card : ℝ) ^ 2 * L x ^ (2 * C) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLpos.le _)
      exact_mod_cast factorTriples_card_le (groupFreePart G n)
    _ = _ := mul_comm _ _

theorem endpoint_norm_sq_le (G : PrimeGroups) (x C τ η : ℝ) (E : Endpoint)
    (hL : 1 ≤ L x) (hE : EndpointBound x C τ η E) (n : ℕ) :
    ‖endpoint G x E n‖ ^ 2 ≤ L x ^ (4 * C) * ((groupFreePart G n).divisors.card : ℝ) ^ 4 := by
  have hLpos : 0 < L x := by linarith
  have hbound := endpoint_norm_le G x C τ η E hL hE n
  have hsq := mul_self_le_mul_self (norm_nonneg _) hbound
  have hpow : (L x ^ (2 * C)) ^ 2 = L x ^ (4 * C) := by
    rw [pow_two, ← Real.rpow_add hLpos]
    congr 1
    ring
  calc
    _ ≤ (L x ^ (2 * C) * ((groupFreePart G n).divisors.card : ℝ) ^ 2) ^ 2 := by
      simpa only [pow_two] using hsq
    _ = _ := by rw [mul_pow, hpow]; ring

end Erdos821.P5Core
