module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Weighted `ℓ²` bounds for choice operators

The operators of PD §4 all have the same shape. Each input state makes finitely many
choices; each choice has a coefficient, and it leads to one output state. In the row
convention the operator is `(T f)(i) = ∑_c a(i, c) f(out(i, c))`. Its norm is controlled by
the weighted Schur test (PD §4, `mem:schur-weight`). With positive weights `h`, suppose
the absolute row sums against `h` are at most `R h`, and the absolute column sums against
the input measure are at most `C` times the output measure times `h`. Then the norm from
`ℓ²(ν)` to `ℓ²(μ)` is at most `√(R C)`.

Norms are recorded by the predicate `NormLe μ ν T c`, which says `‖T f‖_μ ≤ c ‖f‖_ν` for
every `f`.
-/

@[expose] public section

namespace Erdos408.OneSided

open Finset

variable {ι κ γ : Type*} [Fintype ι] [Fintype κ]

/-- The weighted square norm `∑_i μ(i) |f(i)|²`. -/
noncomputable def wnormSq (μ : ι → ℝ) (f : ι → ℂ) : ℝ := ∑ i, μ i * ‖f i‖ ^ 2

/-- `‖T f‖_μ ≤ c ‖f‖_ν` for every `f`. -/
def NormLe (μ : ι → ℝ) (ν : κ → ℝ) (T : (κ → ℂ) → ι → ℂ) (c : ℝ) : Prop :=
  ∀ f, wnormSq μ (T f) ≤ c ^ 2 * wnormSq ν f

/-- The choice operator `(T f)(i) = ∑_{c ∈ cs} a(i, c) f(out(i, c))`. -/
def choiceOp (cs : Finset γ) (a : ι → γ → ℂ) (out : ι → γ → κ) (f : κ → ℂ) : ι → ℂ :=
  fun i => ∑ c ∈ cs, a i c * f (out i c)

omit [Fintype ι] [Fintype κ] in
/-- Choice operators compose by pairing their choices: `(S ∘ T) f (i)` sums over the choice
`c` of `S` at `i` and then the choice `c'` of `T` at `out(i, c)`. Iterating this expands a
product of operators as a sum over histories, which is how PD §4 reads the moment. -/
theorem choiceOp_comp {ρ γ' : Type*} (cs : Finset γ) (a : ι → γ → ℂ) (out : ι → γ → κ)
    (cs' : Finset γ') (a' : κ → γ' → ℂ) (out' : κ → γ' → ρ) (f : ρ → ℂ) :
    choiceOp cs a out (choiceOp cs' a' out' f) =
      choiceOp (cs ×ˢ cs') (fun i c => a i c.1 * a' (out i c.1) c.2)
        (fun i c => out' (out i c.1) c.2) f := by
  funext i
  simp only [choiceOp, sum_product, mul_sum, mul_assoc]

theorem NormLe.comp {ρ : Type*} [Fintype ρ] {μ : ι → ℝ} {ν : κ → ℝ} {σ : ρ → ℝ}
    {S : (κ → ℂ) → ι → ℂ} {T : (ρ → ℂ) → κ → ℂ} {a b : ℝ} (hS : NormLe μ ν S a)
    (hT : NormLe ν σ T b) : NormLe μ σ (S ∘ T) (a * b) := fun f => by
  calc wnormSq μ (S (T f)) ≤ a ^ 2 * wnormSq ν (T f) := hS _
    _ ≤ a ^ 2 * (b ^ 2 * wnormSq σ f) := by gcongr; exact hT f
    _ = (a * b) ^ 2 * wnormSq σ f := by ring

/-- **The weighted Schur test** for a choice operator. If, for weights `h` and `h' > 0`,
`∑_c |a(i, c)| h'(out(i, c)) ≤ R h(i)` for every input `i`, and
`∑_{i, c : out(i, c) = j} μ(i) |a(i, c)| h(i) ≤ C ν(j) h'(j)` for every output `j`, then the
operator has norm at most `√(R C)` from `ℓ²(ν)` to `ℓ²(μ)`. -/
theorem normLe_choiceOp [DecidableEq κ] {cs : Finset γ} {a : ι → γ → ℂ} {out : ι → γ → κ} {μ : ι → ℝ}
    {ν : κ → ℝ} {h : ι → ℝ} {h' : κ → ℝ} {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hμ : ∀ i, 0 ≤ μ i) (hh' : ∀ j, 0 < h' j)
    (hrow : ∀ i, ∑ c ∈ cs, ‖a i c‖ * h' (out i c) ≤ R * h i)
    (hcol : ∀ j, ∑ i, ∑ c ∈ cs with out i c = j, μ i * ‖a i c‖ * h i ≤ C * (ν j * h' j)) :
    NormLe μ ν (choiceOp cs a out) (Real.sqrt (R * C)) := by
  intro f
  rw [Real.sq_sqrt (mul_nonneg hR hC)]
  -- Cauchy–Schwarz at each input: `|T f(i)|² ≤ R h(i) ∑_c |a| |f(out)|² / h'(out)`
  have hpt : ∀ i, ‖choiceOp cs a out f i‖ ^ 2 ≤
      R * h i * ∑ c ∈ cs, ‖a i c‖ * ‖f (out i c)‖ ^ 2 / h' (out i c) := by
    intro i
    have h1 : ‖choiceOp cs a out f i‖ ≤ ∑ c ∈ cs, ‖a i c‖ * ‖f (out i c)‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact sum_congr rfl fun c _ => norm_mul _ _
    have h2 : (∑ c ∈ cs, ‖a i c‖ * ‖f (out i c)‖) ^ 2 ≤
        (∑ c ∈ cs, ‖a i c‖ * h' (out i c)) *
          ∑ c ∈ cs, ‖a i c‖ * ‖f (out i c)‖ ^ 2 / h' (out i c) := by
      refine sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun c _ => ?_) (fun c _ => ?_)
        (fun c _ => ?_)
      · exact mul_nonneg (norm_nonneg _) (hh' _).le
      · exact div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (hh' _).le
      · rw [show ‖a i c‖ * h' (out i c) * (‖a i c‖ * ‖f (out i c)‖ ^ 2 / h' (out i c)) =
            (‖a i c‖ * ‖f (out i c)‖) ^ 2 by field_simp [(hh' (out i c)).ne']]
    have h3 : 0 ≤ ∑ c ∈ cs, ‖a i c‖ * ‖f (out i c)‖ ^ 2 / h' (out i c) :=
      sum_nonneg fun c _ => div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (hh' _).le
    calc ‖choiceOp cs a out f i‖ ^ 2 ≤ (∑ c ∈ cs, ‖a i c‖ * ‖f (out i c)‖) ^ 2 := by
          gcongr
      _ ≤ _ := h2
      _ ≤ R * h i * ∑ c ∈ cs, ‖a i c‖ * ‖f (out i c)‖ ^ 2 / h' (out i c) := by
          gcongr; exact hrow i
  -- regroup the choices by their output
  calc wnormSq μ (choiceOp cs a out f)
      ≤ ∑ i, μ i * (R * h i * ∑ c ∈ cs, ‖a i c‖ * ‖f (out i c)‖ ^ 2 / h' (out i c)) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpt i) (hμ i)
    _ = R * ∑ i, ∑ c ∈ cs, μ i * ‖a i c‖ * h i * (‖f (out i c)‖ ^ 2 / h' (out i c)) := by
        rw [Finset.mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine sum_congr rfl fun c _ => ?_
        ring
    _ = R * ∑ j, ‖f j‖ ^ 2 / h' j *
          ∑ i, ∑ c ∈ cs with out i c = j, μ i * ‖a i c‖ * h i := by
        congr 1
        simp_rw [Finset.mul_sum]
        conv_rhs => rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [← sum_fiberwise cs (out i)
          (fun c => μ i * ‖a i c‖ * h i * (‖f (out i c)‖ ^ 2 / h' (out i c)))]
        refine sum_congr rfl fun j _ => sum_congr rfl fun c hc => ?_
        rw [(mem_filter.1 hc).2]
        ring
    _ ≤ R * ∑ j, ‖f j‖ ^ 2 / h' j * (C * (ν j * h' j)) := by
        gcongr with j
        · exact div_nonneg (sq_nonneg _) (hh' j).le
        · exact hcol j
    _ = R * C * wnormSq ν f := by
        rw [wnormSq, mul_sum, mul_sum]
        refine sum_congr rfl fun j _ => ?_
        field_simp [(hh' j).ne']

end Erdos408.OneSided
