import Erdos821.P4Bridge.Properties
import Erdos821.P4Bridge.FiniteComparison

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos821.P4Bridge
open Blueprint.Graph P4Probe
noncomputable section
variable {P : PrimeGroups} {J ell m : ℕ}

lemma sum_labels {R : Type*} [AddCommMonoid R] (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (H : P.BigLabels (J + ell) → R) :
    (∑ a, H a) = ∑ s : SharedRows ν, ∑ x : SideTuple ν block false,
      ∑ y : SideTuple ν block true, ∑ t : P.BigLabels ell, H (labelJoin ν block s x y t) := by
  calc
    _ = ∑ z, H ((labelSplit ν block).symm z) := by
      apply Fintype.sum_equiv (labelSplit ν block)
      intro a
      simp only [Equiv.symm_apply_apply]
    _ = _ := by simp only [Fintype.sum_prod_type]; rfl

lemma sum_prefix {R : Type*} [AddCommMonoid R] (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (H : P.BigLabels J → R) :
    (∑ a, H a) = ∑ s : SharedRows ν, ∑ x : SideTuple ν block false,
      ∑ y : SideTuple ν block true, H ((prefixSplit ν block).symm (s, x, y)) := by
  calc
    _ = ∑ z, H ((prefixSplit ν block).symm z) := by
      apply Fintype.sum_equiv (prefixSplit ν block)
      intro a
      simp only [Equiv.symm_apply_apply]
    _ = _ := by simp only [Fintype.sum_prod_type]

def conditionalF (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (f : P.BigLabels (J + ell) → ℂ) (s : SharedRows ν) (y : SideTuple ν block true) : ℂ :=
  ∑ x : SideTuple ν block false, ∑ t : P.BigLabels ell,
    ((Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false) x *
      P.idealMass t : ℝ) : ℂ) * f (labelJoin ν block s x y t)

def conditionalG (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (g : P.BigLabels (J + ell) → ℂ) (s : SharedRows ν) (x : SideTuple ν block false) : ℂ :=
  ∑ y : SideTuple ν block true, ∑ t : P.BigLabels ell,
    ((Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true) y *
      P.idealMass t : ℝ) : ℂ) * g (labelJoin ν block s x y t)

lemma conditionalF_energy_le (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (hV : ∀ g, 0 < P.V g) (f : P.BigLabels (J + ell) → ℂ) :
    (∑ s, rowWeight (sharedRows ν) s *
      ∑ y, Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true) y *
        ‖conditionalF ν block f s y‖ ^ 2) ≤ ∑ a, P.idealMass a * ‖f a‖ ^ 2 := by
  let wx := Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false)
  let wy := Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true)
  have hmean (s : SharedRows ν) (y : SideTuple ν block true) :
      ‖conditionalF ν block f s y‖ ^ 2 ≤
        ∑ x, ∑ t : P.BigLabels ell, wx x * P.idealMass t * ‖f (labelJoin ν block s x y t)‖ ^ 2 :=
    mean_product_sq_le wx (P.idealMass (M := ell))
      (fun x => (sideWeight_pos hV _ x).le) (fun t => (idealMass_pos P ell hV t).le)
      (sideWeight_sum hV _) (idealMass_sum P ell hV) (fun x t => f (labelJoin ν block s x y t))
  calc
    _ ≤ ∑ s, rowWeight (sharedRows ν) s * ∑ y, wy y *
        (∑ x, ∑ t : P.BigLabels ell, wx x * P.idealMass t * ‖f (labelJoin ν block s x y t)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ (rowWeight_pos hV _ s).le
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hmean s y) (sideWeight_pos hV _ y).le
    _ = ∑ a, P.idealMass a * ‖f a‖ ^ 2 := by
      rw [sum_labels ν block]
      simp only [idealMass_labelJoin]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro t _
      dsimp only [wx, wy]
      ring

lemma conditionalG_energy_le (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (hV : ∀ g, 0 < P.V g) (g : P.BigLabels (J + ell) → ℂ) :
    (∑ s, rowWeight (sharedRows ν) s *
      ∑ x, Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false) x *
        ‖conditionalG ν block g s x‖ ^ 2) ≤ ∑ a, P.idealMass a * ‖g a‖ ^ 2 := by
  let wx := Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false)
  let wy := Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true)
  have hmean (s : SharedRows ν) (x : SideTuple ν block false) :
      ‖conditionalG ν block g s x‖ ^ 2 ≤
        ∑ y, ∑ t : P.BigLabels ell, wy y * P.idealMass t * ‖g (labelJoin ν block s x y t)‖ ^ 2 :=
    mean_product_sq_le wy (P.idealMass (M := ell))
      (fun y => (sideWeight_pos hV _ y).le) (fun t => (idealMass_pos P ell hV t).le)
      (sideWeight_sum hV _) (idealMass_sum P ell hV) (fun y t => g (labelJoin ν block s x y t))
  calc
    _ ≤ ∑ s, rowWeight (sharedRows ν) s * ∑ x, wx x *
        (∑ y, ∑ t : P.BigLabels ell, wy y * P.idealMass t * ‖g (labelJoin ν block s x y t)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ (rowWeight_pos hV _ s).le
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (hmean s x) (sideWeight_pos hV _ x).le
    _ = ∑ a, P.idealMass a * ‖g a‖ ^ 2 := by
      rw [sum_labels ν block]
      simp only [idealMass_labelJoin]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro t _
      dsimp only [wx, wy]
      ring

end
end Erdos821.P4Bridge
