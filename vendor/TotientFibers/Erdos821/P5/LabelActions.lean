import Erdos821.Blueprint.Transference

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Graph

def labelsActionEquiv (P : PrimeGroups) {M : ℕ} (π : P.Permutations M) :
    P.Labels M ≃ P.Labels M where
  toFun := P.act π
  invFun := P.act (fun g => (π g).symm)
  left_inv a := by funext g i; simp [PrimeGroups.act]
  right_inv a := by funext g i; simp [PrimeGroups.act]

theorem physical_act_iff (P : PrimeGroups) {M : ℕ} (π : P.Permutations M)
    (n : ℤ) (a : P.Labels M) : P.physical M n (P.act π a) ↔ P.physical M n a := by
  constructor
  · intro ha g
    refine ⟨?_, ?_⟩
    · intro i j hij
      have h : (P.act π a) g ((π g).symm i) = (P.act π a) g ((π g).symm j) := by
        simpa only [PrimeGroups.act, Equiv.apply_symm_apply] using hij
      exact (π g).symm.injective ((ha g).1 h)
    · intro i
      simpa only [PrimeGroups.act, Equiv.apply_symm_apply] using (ha g).2 ((π g).symm i)
  · intro ha g
    exact ⟨(ha g).1.comp (π g).injective, fun i => (ha g).2 (π g i)⟩

theorem stateMass_act {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (π : P.Permutations (J + F.ell)) (n : ℤ) (a : A.Labels) :
    A.stateMass (n, P.act π a) = A.stateMass (n, a) := by
  unfold Model.stateMass
  rw [physical_act_iff]

theorem sum_labels_act (P : PrimeGroups) {M : ℕ} (π : P.Permutations M)
    {R : Type*} [AddCommMonoid R] (f : P.Labels M → R) :
    (∑ a : P.Labels M, f (P.act π a)) = ∑ a : P.Labels M, f a :=
  (labelsActionEquiv P π).sum_comp f

theorem sum_four_swap_blocks {α β γ δ R : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Fintype δ] [AddCommMonoid R] (f : α → β → γ → δ → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h := Finset.sum_comm (s := (Finset.univ : Finset (α × β)))
    (t := (Finset.univ : Finset (γ × δ))) (f := fun ab cd => f ab.1 ab.2 cd.1 cd.2)
  simpa only [Fintype.sum_prod_type] using h

theorem stateMass_mul_physicalRaw {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (absolute : Bool) (z z' : A.State) :
    (A.stateMass z : ℂ) * A.physicalRaw absolute z z' =
      (P.markMass (J + F.ell) : ℂ) * A.physicalRaw absolute z z' := by
  by_cases hz : P.physical (J + F.ell) z.1 z.2
  · simp only [Model.stateMass, hz, if_true]
  · have hraw : A.physicalRaw absolute z z' = 0 := by
      simp only [Model.physicalRaw, hz, false_and, if_false]
    rw [hraw, mul_zero, mul_zero]

end Erdos821.P5Core
