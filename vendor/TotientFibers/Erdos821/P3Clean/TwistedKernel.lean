import Erdos821.P3Clean.CycleDisplacement
import Erdos821.P3Clean.RawNormAssembly

/-! The regular cyclic lift of the literal conditioned kernel. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem ite_fintype_sum_zero {α : Type*} [Fintype α] (p : Prop) [Decidable p] (f : α → ℂ) :
    (if p then ∑ a, f a else 0) = ∑ a, if p then f a else 0 := by
  classical
  by_cases h : p <;> simp [h]

instance pendingCycleFintype (P : PrimeGroups) (B : ℕ) [Fintype (CutPendingState P B)] :
    Fintype (PendingCycle P B) := Fintype.ofFinite _

def regularCycleKernel (A : Model F P J m) (n B : ℕ) [Fintype (CutPendingState P B)]
    (theta : ℝ) (forward : Bool) (d : SmallLabels P J)
    (a b : P.BigLabels (J + F.ell)) (r : PendingCycle P B) : ℂ :=
  ∑ v : Fin A.patternCount, ∑ u : P.BigAux J,
    if (A.pattern v).matchesBig a b ∧ bigBan (A.pattern v) a b u ∧
        r = cycleDisplacement A B (A.pattern v) forward d a u then
      bigCleanCoefficient A n theta forward (A.pattern v) d a b u else 0

theorem regularCycleKernel_fibre (A : Model F P J m) (n B : ℕ)
    [Fintype (CutPendingState P B)] (theta : ℝ) (forward : Bool) (d : SmallLabels P J)
    (psi : AddChar (PendingCycle P B) ℂ) (a b : P.BigLabels (J + F.ell)) :
    fourierFibre (regularCycleKernel A n B theta forward d) psi a b =
      ∑ v : Fin A.patternCount, ∑ u : P.BigAux J,
        if (A.pattern v).matchesBig a b ∧ bigBan (A.pattern v) a b u then
          bigCleanCoefficient A n theta forward (A.pattern v) d a b u *
            psi (cycleDisplacement A B (A.pattern v) forward d a u) else 0 := by
  classical
  simp only [fourierFibre, regularCycleKernel, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : (A.pattern v).matchesBig a b ∧ bigBan (A.pattern v) a b u
  · simp [h, and_assoc, ite_mul]
  · have hf (r : PendingCycle P B) :
        ¬ ((A.pattern v).matchesBig a b ∧ bigBan (A.pattern v) a b u ∧
          r = cycleDisplacement A B (A.pattern v) forward d a u) := by tauto
    simp only [if_neg h, if_neg (hf _), zero_mul, Finset.sum_const_zero]

theorem cutoffConditionedKernel_cycle (A : Model F P J m) (n B : ℕ)
    [Fintype (CutPendingState P B)] (theta : ℝ) (forward : Bool) (d : SmallLabels P J)
    (a b : BetweenState P (J + F.ell) B) :
    cutoffConditionedKernel A n theta forward d a b =
      ∑ r : PendingCycle P B,
        if cycleAct (pendingTranslationEquiv (P := P) B 1) r a.2 = b.2 then
          regularCycleKernel A n B theta forward d a.1 b.1 r else 0 := by
  classical
  unfold cutoffConditionedKernel conditionedKernel conditionedPatternEntry
  simp only [regularCycleKernel]
  simp_rw [ite_fintype_sum_zero]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  have he : cycleAct (pendingTranslationEquiv (P := P) B 1)
      (cycleDisplacement A B (A.pattern v) forward d a.1 u) a.2 = b.2 ↔
      b.2.val = translatePending (bigStep A (A.pattern v) forward d a.1 u) a.2.val := by
    rw [cycleDisplacement_act]
    change pendingTranslationEquiv B (bigStep A (A.pattern v) forward d a.1 u) a.2 = b.2 ↔ _
    rw [Subtype.ext_iff]
    exact eq_comm
  by_cases h : (A.pattern v).matchesBig a.1 b.1 ∧ bigBan (A.pattern v) a.1 b.1 u
  · simp only [bigCleanGate, h.1, h.2, true_and]
    symm
    rw [Finset.sum_eq_single (cycleDisplacement A B (A.pattern v) forward d a.1 u)]
    · simp only [if_pos rfl]
      by_cases ht : b.2.val = translatePending (bigStep A (A.pattern v) forward d a.1 u) a.2.val
      · simp only [if_pos ht, if_pos (he.mpr ht), ite_true]
      · simp only [if_neg ht, if_neg (fun hh => ht (he.mp hh)), ite_true]
    · intro r _ hr
      by_cases ha : cycleAct (pendingTranslationEquiv (P := P) B 1) r a.2 = b.2
      · simp only [if_pos ha, if_neg hr]
      · simp only [if_neg ha]
    · simp
  · have hf (r : PendingCycle P B) :
        ¬ ((A.pattern v).matchesBig a.1 b.1 ∧ bigBan (A.pattern v) a.1 b.1 u ∧
          r = cycleDisplacement A B (A.pattern v) forward d a.1 u) := by tauto
    have hg : ¬ bigCleanGate A (A.pattern v) forward d a.1 b.1 u a.2.val b.2.val := by
      unfold bigCleanGate
      tauto
    simp only [if_neg hg, if_neg (hf _), ite_self, Finset.sum_const_zero]


end Erdos821.P3Clean
