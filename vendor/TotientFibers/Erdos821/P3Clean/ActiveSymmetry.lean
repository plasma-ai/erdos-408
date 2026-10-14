import Erdos821.P3Clean.Symmetry
import Erdos821.P3Clean.Structure

/-! Active-list permutations preserve the literal memory measure. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {P : PrimeGroups}

def activePermutationEquiv {M : ℕ} (π : P.Permutations M) :
    P.MemoryState M ≃ P.MemoryState M where
  toFun := permuteActive π
  invFun := permuteActive (fun g => (π g).symm)
  left_inv := by
    intro s
    rcases s with ⟨y, a, z⟩
    have h : P.act (fun g => (π g).symm) (P.act π a) = a := by
      funext g i
      change a g (π g ((π g).symm i)) = a g i
      rw [Equiv.apply_symm_apply]
    change (y, P.act (fun g => (π g).symm) (P.act π a), z) = (y, a, z)
    rw [h]
  right_inv := by
    intro s
    rcases s with ⟨y, a, z⟩
    have h : P.act π (P.act (fun g => (π g).symm) a) = a := by
      funext g i
      change a g ((π g).symm (π g i)) = a g i
      rw [Equiv.symm_apply_apply]
    change (y, P.act π (P.act (fun g => (π g).symm) a), z) = (y, a, z)
    rw [h]

theorem smallPhysical_act {M : ℕ} (π : P.Permutations M)
    (y : P.SmallResidues) (a : P.Labels M) :
    P.smallPhysical y (P.act π a) ↔ P.smallPhysical y a := by
  constructor
  · intro h g
    refine ⟨?_, ?_⟩
    · intro i j hij
      have hh : P.act π a g.val ((π g.val).symm i) =
          P.act π a g.val ((π g.val).symm j) := by
        simpa only [PrimeGroups.act, Equiv.apply_symm_apply] using hij
      have hi := congrArg (π g.val) ((h g).1 hh)
      simpa only [Equiv.apply_symm_apply] using hi
    · intro i
      obtain ⟨j, rfl⟩ := (π g.val).surjective i
      exact (h g).2 j
  · intro h g
    refine ⟨?_, ?_⟩
    · intro i j hij
      exact (π g.val).injective ((h g).1 hij)
    · intro i
      exact (h g).2 (π g.val i)

theorem memoryMass_permuteActive (F : FixedData) (J n : ℕ)
    (π : P.Permutations (J + F.ell)) (s : P.MemoryState (J + F.ell)) :
    P.memoryMass F J n (permuteActive π s) = P.memoryMass F J n s := by
  classical
  have ha : (∏ g : P.BigGroup, ∏ i : Fin (J + F.ell),
      tiltedMu F P n g.val ((P.act π s.2.1) g.val i)) =
      ∏ g : P.BigGroup, ∏ i : Fin (J + F.ell), tiltedMu F P n g.val (s.2.1 g.val i) := by
    apply Finset.prod_congr rfl
    intro g _
    exact Equiv.prod_comp (π g.val) (fun i => tiltedMu F P n g.val (s.2.1 g.val i))
  simp only [PrimeGroups.memoryMass, permuteActive, smallPhysical_act, ha]

theorem normBound_active_symmetry {F : FixedData} {J n : ℕ} {C : ℝ}
    (K : P.MemoryState (J + F.ell) → P.MemoryState (J + F.ell) → ℂ)
    (hK : NormBound (P.memoryMass F J n) K C)
    (π τ : P.Permutations (J + F.ell)) :
    NormBound (P.memoryMass F J n)
      (fun s t => K (permuteActive π s) (permuteActive τ t)) C := by
  exact normBound_relabel _ K C hK (activePermutationEquiv π) (activePermutationEquiv τ)
    (memoryMass_permuteActive F J n π) (memoryMass_permuteActive F J n τ)


end Erdos821.P3Clean
