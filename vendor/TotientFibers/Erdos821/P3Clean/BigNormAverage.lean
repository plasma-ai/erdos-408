import Erdos821.P3Clean.PermutationSplit
import Erdos821.P3Clean.Symmetry

/-! Big endpoint permutation averages are contractions in an invariant measure. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups} {M : ℕ}

def bigPermutationEquiv (p : P.BigPermutations M) : P.BigLabels M ≃ P.BigLabels M where
  toFun := P.actBig p
  invFun := P.actBig (fun g => (p g).symm)
  left_inv := by intro a; funext g i; simp [PrimeGroups.actBig]
  right_inv := by intro a; funext g i; simp [PrimeGroups.actBig]

def averageBigKernel (K : P.BigLabels M → P.BigLabels M → ℂ) (a b : P.BigLabels M) : ℂ :=
  bigSymmetryFactor P M * ∑ p : P.BigPermutations M, ∑ q : P.BigPermutations M,
    K (P.actBig p a) (P.actBig q b)

theorem normBound_averageBigKernel (mass : P.BigLabels M → ℝ)
    (K : P.BigLabels M → P.BigLabels M → ℂ) (C : ℝ)
    (hm : ∀ p : P.BigPermutations M, ∀ a, mass (P.actBig p a) = mass a)
    (hK : NormBound mass K C) : NormBound mass (averageBigKernel K) C := by
  let T := P.BigPermutations M × P.BigPermutations M
  let w : T → ℝ := fun _ => (Fintype.card T : ℝ)⁻¹
  have hn : 0 < (Fintype.card T : ℝ) := by exact_mod_cast Fintype.card_pos
  have hw : ∀ t, 0 ≤ w t := fun _ => inv_nonneg.mpr hn.le
  have hw1 : (∑ t : T, w t) = 1 := by
    simp only [w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn.ne'
  have hrel (t : T) : NormBound mass (fun a b => K (P.actBig t.1 a) (P.actBig t.2 b)) C :=
    normBound_relabel mass K C hK (bigPermutationEquiv t.1) (bigPermutationEquiv t.2)
      (hm t.1) (hm t.2)
  have h := normBound_convex_sum mass
    (fun t : T => fun a b => K (P.actBig t.1 a) (P.actBig t.2 b)) w C hw hw1 hrel
  have he : (fun a b => ∑ t : T, (w t : ℂ) * K (P.actBig t.1 a) (P.actBig t.2 b)) =
      averageBigKernel K := by
    funext a b
    simp only [w, T, Fintype.card_prod, Nat.cast_mul, Complex.ofReal_inv,
      Complex.ofReal_mul, Complex.ofReal_natCast, Fintype.sum_prod_type,
      averageBigKernel, bigSymmetryFactor, pow_two, Finset.mul_sum]
  rw [he] at h
  exact h


end Erdos821.P3Clean
