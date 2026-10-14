import Mathlib
import PrimeNumberTheoremAnd.Erdos970.MertensClassical

/-!
# Classical prime estimates I: Mertens (paper §1, `eq:mertens`)

The paper uses Mertens' estimates (citing Tao):
`∑_{p ≤ y} 1/p = log log y + O(1)` and
`∏_{p ≤ y} (1 - 1/p) ∼ e^{-γ_E} / log y`.

Both are already formalized in `PrimeNumberTheoremAnd.Erdos970.MertensClassical`
(Apache-2.0; also reused by OAI's `TwoPointCorrelations.primeReciprocalInput`):
* second theorem `Erdos970.Mertens.sum_prime_div_eq_log_log`;
* third theorem `Erdos970.Mertens.E₃.bound''` (with rate `E₃.bound'''`
  and identity `prod_one_minus_div_prime_eq`).

This file restates them in the paper's quantifiers and derives the two
consequences later sections need:
* one-sided reciprocal-sum bounds;
* the crude product bound `∏_{p ≤ y}(1 + 1/p) ≪ log y` used by the
  rough-sieve harmonic estimate (`eq:rough-sieve-harmonic`);
* two-sided product bounds `≍ 1/log` used by the sieve main terms (§6:
  `eq:proxy-denominator`, `eq:presieve-mass`).
-/

namespace Erdos821
namespace Prelim
namespace Mertens

open Finset Filter Asymptotics

/-- Prime reciprocal sum `∑_{p ≤ x} 1/p` (PNT/OAI convention). -/
noncomputable def primeRecipSum (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / (p : ℝ)

/-- Mertens product `∏_{p ≤ x}(1 - 1/p)` (PNT convention). -/
noncomputable def primeProd (x : ℝ) : ℝ :=
  ∏ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / (p : ℝ))

/-- Mertens' second theorem (paper `eq:mertens`, sum part), from PNT. -/
theorem mertens_second :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |primeRecipSum x - Real.log (Real.log x)| ≤ C := by
  obtain ⟨C, hC⟩ := Erdos970.Mertens.sum_prime_div_eq_log_log
  refine ⟨C, fun x hx => ?_⟩
  unfold primeRecipSum
  exact hC x hx

/-- Upper half of the reciprocal-sum estimate. -/
theorem mertens_upper :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      primeRecipSum x ≤ Real.log (Real.log x) + C := by
  obtain ⟨C, hC⟩ := mertens_second
  refine ⟨C, fun x hx => ?_⟩
  have h := (abs_le.mp (hC x hx)).2
  linarith

/-- Lower half of the reciprocal-sum estimate. -/
theorem mertens_lower :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      Real.log (Real.log x) - C ≤ primeRecipSum x := by
  obtain ⟨C, hC⟩ := mertens_second
  refine ⟨C, fun x hx => ?_⟩
  have h := (abs_le.mp (hC x hx)).1
  linarith

/-- Mertens' third theorem (paper `eq:mertens`, product part), from PNT:
`∏_{p ≤ x}(1 - 1/p) ∼ e^{-γ} / log x`. -/
theorem mertens_third :
    (fun x : ℝ => primeProd x) ~[atTop]
      (fun x : ℝ => Real.exp (-Real.eulerMascheroniConstant) / Real.log x) :=
  Erdos970.Mertens.E₃.bound''

/-- Two-sided product bounds `≍ e^{-γ}/log` for large `x`, from PNT's
`E₃.abs_le` and `prod_one_minus_div_prime_eq`. Later sections evaluate
sieve main terms `V(W)`, `V(x^{b₁})` from this. -/
theorem mertens_product_bounds :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      Real.exp (-Real.eulerMascheroniConstant) / Real.exp 1 / Real.log x ≤
        primeProd x ∧
      primeProd x ≤
        Real.exp (-Real.eulerMascheroniConstant) * Real.exp 1 / Real.log x := by
  obtain ⟨C, hC⟩ := Erdos970.Mertens.E₃.abs_le
  -- Threshold where `C / log x ≤ 1`, so `|E₃ x| ≤ 1`.
  refine ⟨max 2 (Real.exp C), fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hexpC : Real.exp C ≤ x := le_trans (le_max_right _ _) hx
  have hlogx : (0 : ℝ) < Real.log x :=
    Real.log_pos (lt_of_lt_of_le one_lt_two hx2)
  have hE : |Erdos970.Mertens.E₃ x| ≤ 1 := by
    have h1 := hC x hx2
    have h2 : C / Real.log x ≤ 1 := by
      rw [div_le_one hlogx]
      have hll := Real.log_le_log (Real.exp_pos C) hexpC
      rwa [Real.log_exp] at hll
    exact le_trans h1 h2
  have hlo : (-1 : ℝ) ≤ Erdos970.Mertens.E₃ x := (abs_le.mp hE).1
  have hhi : Erdos970.Mertens.E₃ x ≤ 1 := (abs_le.mp hE).2
  have hexp_lo : Real.exp (-1 : ℝ) ≤ Real.exp (Erdos970.Mertens.E₃ x) :=
    Real.exp_le_exp.mpr hlo
  have hexp_hi : Real.exp (Erdos970.Mertens.E₃ x) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr hhi
  have hident :=
    Erdos970.Mertens.prod_one_minus_div_prime_eq (show (1 : ℝ) < x by linarith)
  have hprod : primeProd x = Real.exp (-Real.eulerMascheroniConstant) *
      Real.exp (Erdos970.Mertens.E₃ x) / Real.log x := by
    simp only [primeProd]
    exact hident
  rw [hprod]
  have hγ : (0 : ℝ) < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
  have hexp1 : (0 : ℝ) < Real.exp (1 : ℝ) := Real.exp_pos _
  have hem1 : Real.exp (-1 : ℝ) = 1 / Real.exp 1 := by
    rw [Real.exp_neg, one_div]
  have h1div : (1 : ℝ) / Real.exp 1 ≤ Real.exp (Erdos970.Mertens.E₃ x) := by
    rw [← hem1]
    exact hexp_lo
  have hnum_lo : Real.exp (-Real.eulerMascheroniConstant) / Real.exp 1 ≤
      Real.exp (-Real.eulerMascheroniConstant) *
        Real.exp (Erdos970.Mertens.E₃ x) := by
    have h := mul_le_mul_of_nonneg_left h1div hγ.le
    rwa [mul_one_div] at h
  have hnum_hi : Real.exp (-Real.eulerMascheroniConstant) *
        Real.exp (Erdos970.Mertens.E₃ x) ≤
      Real.exp (-Real.eulerMascheroniConstant) * Real.exp 1 :=
    mul_le_mul_of_nonneg_left hexp_hi hγ.le
  have hLnn : (0 : ℝ) ≤ (Real.log x)⁻¹ := inv_nonneg.mpr hlogx.le
  have e1 : Real.exp (-Real.eulerMascheroniConstant) / Real.exp 1 /
      Real.log x =
      (Real.exp (-Real.eulerMascheroniConstant) / Real.exp 1) *
        (Real.log x)⁻¹ := div_eq_mul_inv _ _
  have e2 : Real.exp (-Real.eulerMascheroniConstant) *
      Real.exp (Erdos970.Mertens.E₃ x) / Real.log x =
      (Real.exp (-Real.eulerMascheroniConstant) *
        Real.exp (Erdos970.Mertens.E₃ x)) * (Real.log x)⁻¹ :=
    div_eq_mul_inv _ _
  have e3 : Real.exp (-Real.eulerMascheroniConstant) * Real.exp 1 /
      Real.log x =
      (Real.exp (-Real.eulerMascheroniConstant) * Real.exp 1) *
        (Real.log x)⁻¹ := div_eq_mul_inv _ _
  constructor
  · rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hnum_lo hLnn
  · rw [e2, e3]
    exact mul_le_mul_of_nonneg_right hnum_hi hLnn

/-- Elementary step: `∏(1 + 1/p) ≤ exp(∑ 1/p)`, from `1 + t ≤ e^t`. -/
theorem one_add_product_le_exp (P : Finset ℕ) :
    ∏ p ∈ P, (1 + 1 / (p : ℝ)) ≤ Real.exp (∑ p ∈ P, 1 / (p : ℝ)) := by
  calc ∏ p ∈ P, (1 + 1 / (p : ℝ))
      ≤ ∏ p ∈ P, Real.exp (1 / (p : ℝ)) := by
        apply Finset.prod_le_prod₀
        · intro p _
          have hnn : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
          linarith
        · intro p _
          have h := Real.add_one_le_exp (1 / (p : ℝ))
          linarith
    _ = Real.exp (∑ p ∈ P, 1 / (p : ℝ)) := (Real.exp_sum _ _).symm

/-- Crude product bound `∏_{p ≤ y}(1 + 1/p) ≤ C' log y`, for the
rough-sieve harmonic estimate (`eq:rough-sieve-harmonic`). -/
theorem mertens_one_add_upper :
    ∃ C' : ℝ, 0 < C' ∧ ∀ y : ℝ, 2 ≤ y →
      ∏ p ∈ Finset.Ioc 0 ⌊y⌋₊ with p.Prime, (1 + 1 / (p : ℝ)) ≤
        C' * Real.log y := by
  obtain ⟨C, hC⟩ := Erdos970.Mertens.sum_prime_div_eq_log_log
  refine ⟨Real.exp C, Real.exp_pos _, fun y hy => ?_⟩
  have h1y : (1 : ℝ) < y := by linarith
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos h1y
  have hsum : ∑ p ∈ Finset.Ioc 0 ⌊y⌋₊ with p.Prime, (1 : ℝ) / (p : ℝ) ≤
      Real.log (Real.log y) + C := by
    have h := (abs_le.mp (hC y hy)).2
    linarith
  calc ∏ p ∈ Finset.Ioc 0 ⌊y⌋₊ with p.Prime, (1 + 1 / (p : ℝ))
      ≤ Real.exp (∑ p ∈ Finset.Ioc 0 ⌊y⌋₊ with p.Prime, (1 : ℝ) / (p : ℝ)) :=
        one_add_product_le_exp _
    _ ≤ Real.exp (Real.log (Real.log y) + C) := Real.exp_le_exp.mpr hsum
    _ = Real.exp C * Real.log y := by
        rw [Real.exp_add, Real.exp_log hlog, mul_comm]

end Mertens
end Prelim
end Erdos821
