import Erdos821.Blueprint.Graph

/-! The literal finite-choice ghost kernel on multiset memory states. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups}

/-- Particle indices retain their multiplicity when numerical particles coincide. -/
def memoryEntry {g : P.Group} (z : P.Memory g) (i : Fin z.card) : P.Particle g :=
  z.toList.get ⟨i.val, by simpa using i.isLt⟩

def zeroMemoryIndices {g : P.Group} (z : P.Memory g) : Finset (Fin z.card) :=
  Finset.univ.filter (fun i => (memoryEntry z i).2 = 0)

def deleteMemoryIndices {g : P.Group} (z : P.Memory g) (A : Finset (Fin z.card)) : P.Memory g :=
  ((Finset.univ \ A).toList.map (memoryEntry z) : List (P.Particle g))

def zeroBirthBatch {g : P.Group} {b : ℕ} (p : Fin b → P.Prime g) : P.Memory g :=
  (List.ofFn (fun i => (⟨p i, 0⟩ : P.Particle g)) : List (P.Particle g))

/-- A matrix entry only needs batches no longer than its target memory. -/
abbrev GhostChoice {M : ℕ} (s t : P.MemoryState M) :=
  ((g : P.BigGroup) → Finset (Fin (s.2.2 g).card)) ×
    ((b : (g : P.BigGroup) → Fin ((t.2.2 g).card + 1)) ×
      ((g : P.BigGroup) → Fin (b g).val → P.Prime g.val))

def ghostChoiceValid {M : ℕ} {s t : P.MemoryState M} (c : GhostChoice s t) : Prop :=
  ∀ g : P.BigGroup,
    c.1 g ⊆ zeroMemoryIndices (s.2.2 g) ∧
    deleteMemoryIndices (s.2.2 g) (c.1 g) + zeroBirthBatch (c.2.2 g) = t.2.2 g

/-- The source paper's coefficient, with all divisions performed in ℝ. -/
def ghostChoiceWeight (F : FixedData) (n : ℕ) (rho : ℝ) (i : Fin (n + 1))
    {M : ℕ} {s t : P.MemoryState M} (c : GhostChoice s t) : ℝ :=
  ∏ g : P.BigGroup,
    (-eta F n i / rho) ^ (c.1 g).card *
    (visitQ F.q n i / rho ^ (2 : ℕ)) ^
      ((zeroMemoryIndices (s.2.2 g)).card - (c.1 g).card) *
    ((c.2.1 g).val.factorial : ℝ)⁻¹ *
    (-eta F n i * P.V g.val / rho) ^ (c.2.1 g).val *
    ∏ h : Fin (c.2.1 g).val, tiltedMu F P n g.val (c.2.2 g h)

/-- Local multipliers are inserted before any signed choices are combined. -/
def memoryGhostKernel (F : FixedData) (J n : ℕ) (rho : ℝ) (i : Fin (n + 1))
    (phi : (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℂ)
    (s t : P.MemoryState (J + F.ell)) : ℂ :=
  if s.1 = t.1 ∧ s.2.1 = t.2.1 then
    ∑ c : GhostChoice s t,
      if ghostChoiceValid c then (ghostChoiceWeight F n rho i c : ℂ) * phi s t c else 0
  else 0

def absoluteMemoryGhostKernel (F : FixedData) (J n : ℕ) (rho : ℝ) (i : Fin (n + 1))
    (s t : P.MemoryState (J + F.ell)) : ℝ :=
  if s.1 = t.1 ∧ s.2.1 = t.2.1 then
    ∑ c : GhostChoice s t, if ghostChoiceValid c then |ghostChoiceWeight F n rho i c| else 0
  else 0

def ghostBirthCount {M : ℕ} {s t : P.MemoryState M} (c : GhostChoice s t) : ℕ :=
  ∑ g : P.BigGroup, (c.2.1 g).val

/-- A scale d multiplies each original ghost birth by d; d=2 is used for tails. -/
def absoluteScaledMemoryGhostKernel (F : FixedData) (J n : ℕ) (rho d : ℝ)
    (i : Fin (n + 1)) (s t : P.MemoryState (J + F.ell)) : ℝ :=
  if s.1 = t.1 ∧ s.2.1 = t.2.1 then
    ∑ c : GhostChoice s t,
      if ghostChoiceValid c then |ghostChoiceWeight F n rho i c| * d ^ ghostBirthCount c else 0
  else 0

/-- The factorial adjoint swaps birth and termination normalizations. -/
def ghostReversalFactor (d : ℝ) {M : ℕ} (s t : P.MemoryState M) : ℝ :=
  ∏ g : P.BigGroup, (d * P.V g.val) ^
    (((s.2.2 g).card : ℤ) - ((t.2.2 g).card : ℤ))

/-- Modulus-one birth phases or performed-address indicators are dominated
by the absolute choices, including on numerical memory diagonals. -/
theorem memoryGhostKernel_norm_le (F : FixedData) (J n : ℕ) (rho : ℝ) (i : Fin (n + 1))
    (phi : (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℂ)
    (hphi : ∀ s t c, ‖phi s t c‖ ≤ 1) (s t : P.MemoryState (J + F.ell)) :
    ‖memoryGhostKernel F J n rho i phi s t‖ ≤ absoluteMemoryGhostKernel F J n rho i s t := by
  by_cases h : s.1 = t.1 ∧ s.2.1 = t.2.1
  · simp only [memoryGhostKernel, absoluteMemoryGhostKernel, if_pos h]
    calc
      _ ≤ ∑ c : GhostChoice s t,
          ‖if ghostChoiceValid c then (ghostChoiceWeight F n rho i c : ℂ) * phi s t c else 0‖ :=
        norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro c _
        by_cases hc : ghostChoiceValid c
        · simp only [if_pos hc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (hphi s t c) (abs_nonneg (ghostChoiceWeight F n rho i c))
        · simp only [if_neg hc, norm_zero, le_refl]
  · simp only [memoryGhostKernel, absoluteMemoryGhostKernel, if_neg h, norm_zero, le_refl]


end Erdos821.S2Core
