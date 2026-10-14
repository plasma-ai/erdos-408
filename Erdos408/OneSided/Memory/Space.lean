module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-!
# The memory space

PD §4 stores pending primes as *memory particles* and uses symmetric functions of the
`k_i` particles of each group with the measure `λ^{⊗k_i} / k_i!` (`mem:hilbert-space`).
A symmetric function of `k` particles is a function of their multiset. On multisets the
measure becomes `∏_x λ(x)^{S(x)} / S(x)!`, where `S(x)` is the multiplicity of the particle
`x`. Indeed, a multiset with multiplicities `S` has `k! / ∏_x S(x)!` orderings, each of
measure `∏_x λ(x)^{S(x)} / k!`.

So the memory space is `ℓ²` of the multiplicity functions `S : X → ℕ`, weighted by
`memWeight`. The cap `Π_B` of PD (`mem:truncation-error`) restricts to total size at most
`B`, which makes the space finite.

Particles of all groups share one type `X`; the group of a particle is determined by its
prime, since the bands are disjoint.
-/

@[expose] public section

namespace Erdos408.OneSided

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The size `∑_x S(x)` of a memory state. -/
def memSize (S : X → ℕ) : ℕ := ∑ x, S x

/-- The memory states of size at most `B`, as multiplicity functions. -/
def memStates (B : ℕ) : Finset (X → ℕ) :=
  (Fintype.piFinset fun _ => range (B + 1)).filter fun S => memSize S ≤ B

omit [DecidableEq X] in
theorem le_memSize (S : X → ℕ) (x : X) : S x ≤ memSize S :=
  single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ x)

theorem mem_memStates {B : ℕ} {S : X → ℕ} : S ∈ memStates B ↔ memSize S ≤ B := by
  simp only [memStates, mem_filter, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  intro h x
  have := le_memSize S x
  omega

/-- The memory space with the cap `B`. -/
abbrev MemState (X : Type*) [Fintype X] [DecidableEq X] (B : ℕ) := ↥(memStates (X := X) B)

/-- The symmetric weight `∏_x ν(x)^{S(x)} / S(x)!`. -/
noncomputable def memWeight (ν : X → ℝ) (S : X → ℕ) : ℝ := ∏ x, ν x ^ S x / (S x).factorial

omit [DecidableEq X] in
theorem memWeight_nonneg {ν : X → ℝ} (hν : ∀ x, 0 ≤ ν x) (S : X → ℕ) : 0 ≤ memWeight ν S :=
  prod_nonneg fun x _ => div_nonneg (pow_nonneg (hν x) _) (Nat.cast_nonneg _)

end Erdos408.OneSided
