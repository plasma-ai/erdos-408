import Erdos821.P3Clean.BigAverage
import Erdos821.P3Clean.ActiveSymmetry
import Erdos821.P3Clean.NormTransport

/-! Recover the full clean endpoint symmetrization after small conditioning. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def actSmall {M : ℕ} (p : SmallPermutations P M) (a : SmallLabels P M) : SmallLabels P M :=
  fun g i => a g (p g i)

theorem act_joinPermutations {M : ℕ} (p : SmallPermutations P M) (q : P.BigPermutations M)
    (a : SmallLabels P M) (b : P.BigLabels M) :
    P.act (joinPermutations p q) (joinLabels a b) = joinLabels (actSmall p a) (P.actBig q b) := by
  funext g i
  unfold PrimeGroups.act joinPermutations joinLabels actSmall PrimeGroups.actBig
  split_ifs <;> rfl

def smallCoordinatePermEquiv {M B : ℕ} (p : SmallPermutations P M) :
    CoordinateState P M B ≃ CoordinateState P M B where
  toFun a := (actSmall p a.1, a.2)
  invFun a := (actSmall (fun g => (p g).symm) a.1, a.2)
  left_inv := by
    intro a
    apply Prod.ext
    · funext g i; simp [actSmall]
    · rfl
  right_inv := by
    intro a
    apply Prod.ext
    · funext g i; simp [actSmall]
    · rfl

theorem smallArrayStates_actSmall {M : ℕ} (p : SmallPermutations P M)
    (y : P.SmallResidues) (a : SmallLabels P M) (b : P.BigLabels M) :
    actSmall p a ∈ smallArrayStates P M y ↔ a ∈ smallArrayStates P M y := by
  have h := smallPhysical_act (joinPermutations p (fun _ => Equiv.refl _)) y (joinLabels a b)
  rw [act_joinPermutations] at h
  simpa only [smallPhysical_join] using h

theorem coordinateMass_actSmall (F : FixedData) (J n B : ℕ)
    (p : SmallPermutations P (J + F.ell)) (a : CoordinateState P (J + F.ell) B) :
    coordinateMass F J n B (smallCoordinatePermEquiv p a) = coordinateMass F J n B a := by
  rw [coordinateMass_eq_memoryMass, coordinateMass_eq_memoryMass]
  change P.memoryMass F J n (a.2.2.val.1, joinLabels (actSmall p a.1) a.2.1, a.2.2.val.2) =
    P.memoryMass F J n (a.2.2.val.1, joinLabels a.1 a.2.1, a.2.2.val.2)
  have h := memoryMass_permuteActive F J n
    (joinPermutations p (fun _ => Equiv.refl _))
    (a.2.2.val.1, joinLabels a.1 a.2.1, a.2.2.val.2)
  simp only [permuteActive, act_joinPermutations] at h
  exact h

def averageSmallCoordinateKernel {M B : ℕ}
    (K : CoordinateState P M B → CoordinateState P M B → ℂ) (a b : CoordinateState P M B) : ℂ :=
  smallSymmetryFactor P M * ∑ p : SmallPermutations P M, ∑ q : SmallPermutations P M,
    K (smallCoordinatePermEquiv p a) (smallCoordinatePermEquiv q b)

theorem normBound_averageSmallCoordinateKernel (F : FixedData) (J n B : ℕ)
    (K : CoordinateState P (J + F.ell) B → CoordinateState P (J + F.ell) B → ℂ)
    (C : ℝ) (hK : NormBound (coordinateMass F J n B) K C) :
    NormBound (coordinateMass F J n B) (averageSmallCoordinateKernel K) C := by
  let T := SmallPermutations P (J + F.ell) × SmallPermutations P (J + F.ell)
  let w : T → ℝ := fun _ => (Fintype.card T : ℝ)⁻¹
  have hn : 0 < (Fintype.card T : ℝ) := by exact_mod_cast Fintype.card_pos
  have hw : ∀ t, 0 ≤ w t := fun _ => inv_nonneg.mpr hn.le
  have hw1 : (∑ t : T, w t) = 1 := by
    simp only [w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn.ne'
  have hrel (t : T) : NormBound (coordinateMass F J n B)
      (fun a b => K (smallCoordinatePermEquiv t.1 a) (smallCoordinatePermEquiv t.2 b)) C :=
    normBound_relabel _ K C hK (smallCoordinatePermEquiv t.1) (smallCoordinatePermEquiv t.2)
      (coordinateMass_actSmall F J n B t.1) (coordinateMass_actSmall F J n B t.2)
  have h := normBound_convex_sum (coordinateMass F J n B)
    (fun t : T => fun a b => K (smallCoordinatePermEquiv t.1 a) (smallCoordinatePermEquiv t.2 b))
    w C hw hw1 hrel
  have he : (fun a b => ∑ t : T, (w t : ℂ) *
      K (smallCoordinatePermEquiv t.1 a) (smallCoordinatePermEquiv t.2 b)) =
      averageSmallCoordinateKernel K := by
    funext a b
    simp only [w, T, Fintype.card_prod, Nat.cast_mul, Complex.ofReal_inv,
      Complex.ofReal_mul, Complex.ofReal_natCast, Fintype.sum_prod_type,
      averageSmallCoordinateKernel, smallSymmetryFactor, pow_two, Finset.mul_sum]
  rw [he] at h
  exact h

theorem averageSmallCoordinateKernel_clean (A : Model F P J m) (n : ℕ) (theta : ℝ) (i : Fin n)
    {B : ℕ} (a b : CoordinateState P (J + F.ell) B) :
    averageSmallCoordinateKernel (bigAveragedRawKernel A n theta (edgeForward i) (B := B)) a b =
      cleanEdgeKernel A n 1 theta i ((cutoffStateCoordinates P (J + F.ell) B).symm a).val
        ((cutoffStateCoordinates P (J + F.ell) B).symm b).val := by
  change _ = cleanEdgeKernel A n 1 theta i
    (a.2.2.val.1, joinLabels a.1 a.2.1, a.2.2.val.2)
    (b.2.2.val.1, joinLabels b.1 b.2.1, b.2.2.val.2)
  rw [cleanEdgeKernel_one, edgeSymmetryFactor_split]
  simp_rw [sum_permutations_split]
  have he (p q : SmallPermutations P (J + F.ell)) (r s : P.BigPermutations (J + F.ell)) :
      rawCleanKernel A n theta (edgeForward i)
        (permuteActive (joinPermutations p r) (a.2.2.val.1, joinLabels a.1 a.2.1, a.2.2.val.2))
        (permuteActive (joinPermutations q s) (b.2.2.val.1, joinLabels b.1 b.2.1, b.2.2.val.2)) =
      coordinateRawKernel A n theta (edgeForward i)
        (permuteCoordinateBig r (smallCoordinatePermEquiv p a))
        (permuteCoordinateBig s (smallCoordinatePermEquiv q b)) := by
    simp only [permuteActive, act_joinPermutations]
    rfl
  simp only [he, averageSmallCoordinateKernel, bigAveragedRawKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring


end Erdos821.P3Clean
