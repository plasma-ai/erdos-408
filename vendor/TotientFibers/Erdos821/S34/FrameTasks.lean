import Mathlib

set_option autoImplicit false

open scoped BigOperators Classical

namespace Erdos821.S34Core

noncomputable section

def frameCellMass {α κ : Type*} [Fintype α] [DecidableEq κ]
    (w : α → ℝ) (cell : α → κ) (j : κ) : ℝ :=
  ∑ x, if cell x = j then w x else 0

def frameCellKernel {α κ γ : Type*} [Fintype α] [Fintype γ] [DecidableEq κ]
    (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (ξ : ℝ) (D X : α) : ℂ :=
  if cell D = cell X ∧ ξ ≤ frameCellMass w cell (cell X) then
    (frameCellMass w cell (cell X) : ℂ)⁻¹ * ∑ c, star (χ c D) * χ c X
  else 0

def frameCellApply {α κ γ : Type*} [Fintype α] [Fintype γ] [DecidableEq κ]
    (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (ξ : ℝ)
    (f : α → ℂ) (X : α) : ℂ :=
  ∑ D, (w D : ℂ) * frameCellKernel w cell χ ξ D X * f D

def weightedFrameNorm {α : Type*} [Fintype α] (w : α → ℝ) (f : α → ℂ) : ℝ :=
  Real.sqrt (∑ x, w x * ‖f x‖ ^ 2)

/-- §3 conditional frame estimate. Weights need not have total mass one.
There is no cell-count cost: distinct cells are orthogonal blocks.
Suggested route: weighted vectors sqrt(w x) χ(c,x) / sqrt(cell mass),
then OAI.LargePrimeGaps.norm_sum_smul_sq_le_gram and gram_large_sieve
(OAI.NumberTheory.PrimeGaps.AdditiveSieve, prebuilt). -/
def CellFrameTask : Prop :=
  ∀ (α κ γ : Type) [Fintype α] [Fintype κ] [Fintype γ] [DecidableEq κ]
    (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (ξ δ : ℝ),
    (∀ x, 0 ≤ w x) → (∀ c x, ‖χ c x‖ ≤ 1) → 0 < ξ → 0 ≤ δ →
    (∀ j : κ, ξ ≤ frameCellMass w cell j → ∀ c d : γ, c ≠ d →
      ‖∑ x, if cell x = j then (w x : ℂ) * star (χ c x) * χ d x else 0‖ ≤ δ) →
    ∀ f : α → ℂ,
      weightedFrameNorm w (frameCellApply w cell χ ξ f) ≤
        (1 + (Fintype.card γ : ℝ) * δ / ξ) * weightedFrameNorm w f

end
end Erdos821.S34Core
