import Erdos408.OneSided.Moment.Lines

/-!
# Averages of products over independent lines

The lines at distinct band primes are independent and uniform, so the line average of a
product over the band primes of functions of `ℓ p` is the product of the averages over
`{0, …, p}` (`blueprint/one_sided_type_ii.md` §12, S1).
-/

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

/-- The line average of `∏_p φ_p(ℓ p)` over the band primes is
`∏_p (p + 1)⁻¹ ∑_{l ≤ p} φ_p(l)`. -/
theorem lineAverage_prod (x : ℝ) (d : Data K) (φ : ℕ → ℕ → ℂ) :
    lineAverage x d (fun ℓ => ∏ p ∈ bandPrimes x d, φ p (ℓ p)) =
      ∏ p ∈ bandPrimes x d, (((p : ℂ) + 1)⁻¹ * ∑ l ∈ range (p + 1), φ p l) := by
  classical
  -- step: the line assignments are an injective image of the pi set
  have hinj : Set.InjOn (fun (f : ∀ p ∈ bandPrimes x d, ℕ) p =>
      if h : p ∈ bandPrimes x d then f p h else 0)
      ((bandPrimes x d).pi fun p => range (p + 1)) := by
    intro f _ f' _ h
    funext p hp
    simpa only [hp, dite_true] using congrFun h p
  have hcard : ((lineAssignments x d).card : ℂ) = ∏ p ∈ bandPrimes x d, ((p : ℂ) + 1) := by
    rw [lineAssignments, card_image_of_injOn (by convert hinj), card_pi]
    push_cast [card_range]
    rfl
  rw [lineAverage, hcard, prod_mul_distrib, prod_inv_distrib, prod_sum, lineAssignments,
    sum_image (by convert hinj)]
  congr 1
  refine sum_congr rfl fun f _ => ?_
  rw [← prod_attach]
  exact prod_congr rfl fun p _ => by simp only [p.2, dite_true]
