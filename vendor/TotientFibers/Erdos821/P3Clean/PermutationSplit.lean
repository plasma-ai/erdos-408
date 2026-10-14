import Erdos821.P3Clean.ConditionedKernel

/-! Separate the two small and two big endpoint permutation averages. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

abbrev SmallPermutations (P : PrimeGroups) (M : ℕ) := P.SmallGroup → Equiv.Perm (Fin M)

def joinPermutations {P : PrimeGroups} {M : ℕ} (s : SmallPermutations P M)
    (b : P.BigPermutations M) : P.Permutations M :=
  fun g => if hg : P.big g = true then b ⟨g, hg⟩ else s ⟨g, by cases h : P.big g <;> simp_all⟩

theorem joinPermutations_small {P : PrimeGroups} {M : ℕ} (s : SmallPermutations P M)
    (b : P.BigPermutations M) (g : P.SmallGroup) : joinPermutations s b g.val = s g := by
  simp [joinPermutations, g.property]

theorem joinPermutations_big {P : PrimeGroups} {M : ℕ} (s : SmallPermutations P M)
    (b : P.BigPermutations M) (g : P.BigGroup) : joinPermutations s b g.val = b g := by
  simp [joinPermutations, g.property]

def splitPermutations (P : PrimeGroups) (M : ℕ) :
    P.Permutations M ≃ SmallPermutations P M × P.BigPermutations M where
  toFun p := (fun g => p g.val, fun g => p g.val)
  invFun p := joinPermutations p.1 p.2
  left_inv := by
    intro p
    funext g
    simp only [joinPermutations]
    split_ifs <;> rfl
  right_inv := by
    intro p
    apply Prod.ext
    · funext g
      exact joinPermutations_small p.1 p.2 g
    · funext g
      exact joinPermutations_big p.1 p.2 g

theorem permutations_card (P : PrimeGroups) (M : ℕ) :
    Fintype.card (P.Permutations M) =
      Fintype.card (SmallPermutations P M) * Fintype.card (P.BigPermutations M) := by
  rw [Fintype.card_congr (splitPermutations P M), Fintype.card_prod]

def smallSymmetryFactor (P : PrimeGroups) (M : ℕ) : ℂ :=
  ((Fintype.card (SmallPermutations P M) : ℂ) ^ (2 : ℕ))⁻¹

def bigSymmetryFactor (P : PrimeGroups) (M : ℕ) : ℂ :=
  ((Fintype.card (P.BigPermutations M) : ℂ) ^ (2 : ℕ))⁻¹

theorem edgeSymmetryFactor_split (P : PrimeGroups) (M : ℕ) :
    (edgeSymmetryFactor P M : ℂ) = smallSymmetryFactor P M * bigSymmetryFactor P M := by
  unfold edgeSymmetryFactor smallSymmetryFactor bigSymmetryFactor
  rw [permutations_card]
  simp only [Nat.cast_mul, mul_pow, mul_inv_rev, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_natCast]
  ring

theorem sum_permutations_split {P : PrimeGroups} {M : ℕ} (f : P.Permutations M → ℂ) :
    (∑ p : P.Permutations M, f p) =
      ∑ s : SmallPermutations P M, ∑ b : P.BigPermutations M, f (joinPermutations s b) := by
  have h := Equiv.sum_comp (splitPermutations P M).symm f
  change (∑ p : SmallPermutations P M × P.BigPermutations M,
    f (joinPermutations p.1 p.2)) = ∑ p : P.Permutations M, f p at h
  rw [Fintype.sum_prod_type] at h
  exact h.symm


end Erdos821.P3Clean
