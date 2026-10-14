import Erdos821.P5.EndpointBounds
import Erdos821.P5.RoughDivisorTask
import Erdos821.P5Div.Basic

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem roughDivisorCountTask_proof : RoughDivisorCountTask := by
  exact Erdos821.P5Div.RoughDivisorCountTask_proof

def roughFactorTriples (y : ℝ) (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (factorTriples N).filter (fun u => rough y u.1 ∧ rough y u.2.1)

theorem roughFactorTriples_card_le (y : ℝ) (N : ℕ) :
    (roughFactorTriples y N).card ≤ (N.divisors.filter (rough y)).card ^ 2 := by
  classical
  let s := N.divisors.filter (rough y)
  have hmap (u : ℕ × ℕ × ℕ) (hu : u ∈ roughFactorTriples y N) :
      (u.1, u.2.1) ∈ s.product s := by
    obtain ⟨huT, hrough⟩ := Finset.mem_filter.mp hu
    obtain ⟨hm, hp, hr, hfact⟩ := factorTriples_info N u huT
    have hN : N ≠ 0 := by
      have h : 0 < N := by rw [← hfact]; positivity
      omega
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨⟨u.2.1 * u.2.2, by rw [← hfact]; ring⟩, hN⟩, hrough.1⟩
    · exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨⟨u.1 * u.2.2, by rw [← hfact]; ring⟩, hN⟩, hrough.2⟩
  have hinj : (roughFactorTriples y N : Set (ℕ × ℕ × ℕ)).InjOn (fun u => (u.1, u.2.1)) := by
    intro u hu v hv heq
    obtain ⟨hm, hp, hr, hfact⟩ := factorTriples_info N u (Finset.mem_filter.mp hu).1
    have hfactv := (factorTriples_info N v (Finset.mem_filter.mp hv).1).2.2.2
    have hmEq : u.1 = v.1 := congrArg (fun w : ℕ × ℕ => w.1) heq
    have hpEq : u.2.1 = v.2.1 := congrArg (fun w : ℕ × ℕ => w.2) heq
    have hfactv' : u.1 * u.2.1 * v.2.2 = N := by simpa only [hmEq, hpEq] using hfactv
    have hrEq := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hm hp) (hfact.trans hfactv'.symm)
    exact Prod.ext hmEq (Prod.ext hpEq hrEq)
  have hcard := Finset.card_le_card_of_injOn (fun u : ℕ × ℕ × ℕ => (u.1, u.2.1)) hmap hinj
  simpa only [Finset.product_eq_sprod, Finset.card_product, pow_two] using hcard

theorem endpoint_rough_factorization (G : PrimeGroups) (x C τ η : ℝ) (E : Endpoint)
    (hE : EndpointBound x C τ η E) (n : ℕ) :
    endpoint G x E n = ∑ u ∈ roughFactorTriples (W x) (groupFreePart G n),
      if E.lo ≤ (u.2.1 : ℝ) ∧ (u.2.1 : ℝ) ≤ E.hi then
        E.alpha u.1 * E.chi (u.1 : ZMod E.modulus) * mellin u.1 E.sigma₀ *
          mellin u.2.1 E.sigma₁ * E.residual u.2.2 else 0 := by
  rw [endpoint_factorization]
  simp only [roughFactorTriples, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hα : E.alpha u.1 = 0
  · simp [hα]
  · have hm := hE.2.2.2.2.1 u.1 hα
    by_cases hp : rough (W x) u.2.1 <;> simp [hm, hp]

theorem endpoint_term_norm_le (x C τ η : ℝ) (E : Endpoint)
    (hL : 1 ≤ L x) (hE : EndpointBound x C τ η E) (m p r : ℕ) :
    ‖E.alpha m * E.chi (m : ZMod E.modulus) * mellin m E.sigma₀ *
      mellin p E.sigma₁ * E.residual r‖ ≤ L x ^ (2 * C) := by
  have hLpos : 0 < L x := by linarith
  have hcoeff := hE.2.2.2.1
  simp only [norm_mul, norm_mellin, mul_one]
  calc
    _ ≤ L x ^ C * 1 * L x ^ C :=
      mul_le_mul (mul_le_mul (hcoeff m).1 (E.chi.norm_le_one _) (norm_nonneg _)
        (Real.rpow_nonneg hLpos.le C)) (hcoeff r).2 (norm_nonneg _) (by positivity)
    _ = _ := by simp only [mul_one]; rw [← Real.rpow_add hLpos]; congr 1; ring

/-- Count only the rough m,p pairs; the unrestricted divisor count does not give
the exponential-in-sqrt(log x) bound required by transference. -/
theorem endpoint_norm_rough_divisors_le (G : PrimeGroups) (x C τ η : ℝ) (E : Endpoint)
    (hL : 1 ≤ L x) (hE : EndpointBound x C τ η E) (n : ℕ) :
    ‖endpoint G x E n‖ ≤ L x ^ (2 * C) *
      (((groupFreePart G n).divisors.filter (rough (W x))).card : ℝ) ^ 2 := by
  classical
  rw [endpoint_rough_factorization G x C τ η E hE]
  calc
    _ ≤ ∑ u ∈ roughFactorTriples (W x) (groupFreePart G n),
        ‖if E.lo ≤ (u.2.1 : ℝ) ∧ (u.2.1 : ℝ) ≤ E.hi then
          E.alpha u.1 * E.chi (u.1 : ZMod E.modulus) * mellin u.1 E.sigma₀ *
            mellin u.2.1 E.sigma₁ * E.residual u.2.2 else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ roughFactorTriples (W x) (groupFreePart G n), L x ^ (2 * C) := by
      apply Finset.sum_le_sum
      intro u hu
      split_ifs
      · exact endpoint_term_norm_le x C τ η E hL hE _ _ _
      · simp only [norm_zero]; positivity
    _ = ((roughFactorTriples (W x) (groupFreePart G n)).card : ℝ) * L x ^ (2 * C) := by simp
    _ ≤ (((groupFreePart G n).divisors.filter (rough (W x))).card : ℝ) ^ 2 * L x ^ (2 * C) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith : 0 ≤ L x) _)
      exact_mod_cast roughFactorTriples_card_le (W x) (groupFreePart G n)
    _ = _ := mul_comm _ _

end Erdos821.P5Core
