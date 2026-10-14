import Erdos821.P3Edge.SmallZeros

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

lemma smallDamping_le_one {P : PrimeGroups} {F : FixedData} {J : ℕ}
    (y : P.SmallResidues) (a : P.Labels (J + F.ell))
    (hphys : P.smallPhysical y a) :
    smallDamping F J y ≤ 1 := by
  classical
  unfold smallDamping
  -- Exponent in definition is ((omega:ℝ) - (↑J+↑ell)*↑card)/2 (with separate casts, as elaborated for ℝ ops)
  -- Prove it nonneg.
  have hexp_nonneg : (0:ℝ) ≤ (((smallOmega y : ℝ) - ((J : ℝ) + (F.ell : ℝ)) * (Fintype.card P.SmallGroup : ℝ)) / 2) := by
    have hge : (((J : ℝ) + (F.ell : ℝ)) * (Fintype.card P.SmallGroup : ℝ) ≤ (smallOmega y : ℝ)) := by
      have h1 : ∀ g : P.SmallGroup, (((J : ℝ) + (F.ell : ℝ))) ≤
          ((Finset.univ.filter (fun p : P.Prime g.val => y g p = 0)).card : ℝ) := by
        intro g
        have hle : J + F.ell ≤ (Finset.univ.filter (fun p : P.Prime g.val => y g p = 0)).card :=
          small_zeros_ge P y a hphys g
        have hcast : (((J + F.ell : ℕ)) : ℝ) = ((J : ℝ) + (F.ell : ℝ)) := by
          push_cast
          ring_nf
        rw [← hcast]
        exact Nat.cast_le.mpr hle
      have hsum : ∑ _g : P.SmallGroup, (((J : ℝ) + (F.ell : ℝ))) ≤ ∑ g : P.SmallGroup,
          ((Finset.univ.filter (fun p : P.Prime g.val => y g p = 0)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro g _
        exact h1 g
      have lhs_eq : ∑ _g : P.SmallGroup, (((J : ℝ) + (F.ell : ℝ)))
          = (((J : ℝ) + (F.ell : ℝ))) * (Fintype.card P.SmallGroup : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
      have rhs_eq : ∑ g : P.SmallGroup,
          ((Finset.univ.filter (fun p : P.Prime g.val => y g p = 0)).card : ℝ)
          = (smallOmega y : ℝ) := by
        unfold smallOmega
        rw [Nat.cast_sum]
      rw [lhs_eq, rhs_eq] at hsum
      exact hsum
    linarith
  have hq0 : (0:ℝ) ≤ F.q := F.q_pos.le
  have hq1 : F.q ≤ 1 := F.q_lt.le
  -- Need to match exponent form in goal (which uses separate casts as in definition, same as hexp_nonneg)
  -- smallDamping unfolds to F.q ^ (((omega:ℝ) - (↑J+↑ell)*↑card)/2) (with separate casts), same as hexp_nonneg. Good!
  exact Real.rpow_le_one hq0 hq1 hexp_nonneg

end Erdos821.P3Edge
