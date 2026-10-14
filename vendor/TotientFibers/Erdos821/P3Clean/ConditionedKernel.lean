import Erdos821.P3Clean.CleanCoefficients

/-! The exact conditioned signed kernel, retaining every big auxiliary draw. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def smallCleanGate (J ell : ℕ) (a c : SmallLabels P (J + ell)) (s t : PendingState P) : Prop :=
  a ∈ smallArrayStates P (J + ell) s.1 ∧ c ∈ smallArrayStates P (J + ell) t.1 ∧
    smallArrayPrefix J ell a = smallArrayPrefix J ell c

def bigCleanGate (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (d0 : SmallLabels P J) (a b : P.BigLabels (J + F.ell)) (u : P.BigAux J)
    (s t : PendingState P) : Prop :=
  ν.matchesBig a b ∧ bigBan ν a b u ∧ t = translatePending (bigStep A ν forward d0 a u) s

def bigCleanCoefficient (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool)
    (ν : Pattern P J F.ell m) (d0 : SmallLabels P J)
    (a b : P.BigLabels (J + F.ell)) (u : P.BigAux J) : ℂ :=
  (ν.bigAuxMass u * tiltedFreshMass F n ν b : ℝ) *
    smallSignedCoefficient A forward d0 * bigSignedCoefficient A ν forward a b u *
    phase (theta * (bigStep A ν forward d0 a u : ℝ))

def conditionedPatternEntry (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool)
    (ν : Pattern P J F.ell m) (d0 : SmallLabels P J)
    (a b : P.BigLabels (J + F.ell)) (s t : PendingState P) : ℂ :=
  ∑ u : P.BigAux J, if bigCleanGate A ν forward d0 a b u s t then
    bigCleanCoefficient A n theta forward ν d0 a b u else 0

def conditionedKernel (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool)
    (d0 : SmallLabels P J)
    (a b : P.BigLabels (J + F.ell) × PendingState P) : ℂ :=
  ∑ v : Fin A.patternCount, conditionedPatternEntry A n theta forward (A.pattern v) d0
    a.1 b.1 a.2 b.2

theorem rawEdgeValid_split (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (a c : SmallLabels P (J + F.ell)) (b d : P.BigLabels (J + F.ell))
    (v : SmallLabels P J) (u : P.BigAux J) (s t : PendingState P) :
    rawEdgeValid A ν forward (joinLabels v u)
      (s.1, joinLabels a b, s.2) (t.1, joinLabels c d, t.2)
      (emptyTransfer (s.1, joinLabels a b, s.2)) ↔
      smallCleanGate J F.ell a c s t ∧
        bigCleanGate A ν forward (smallArrayPrefix J F.ell a) b d u s t := by
  rw [rawEdgeValid_empty_join]
  unfold smallCleanGate bigCleanGate
  tauto

theorem rawClean_summand_split (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool)
    (ν : Pattern P J F.ell m) (a c : SmallLabels P (J + F.ell))
    (b d : P.BigLabels (J + F.ell)) (v : SmallLabels P J) (u : P.BigAux J)
    (s t : PendingState P) (hV : ∀ g : P.SmallGroup, 0 ≤ P.V g.val) :
    (smallMarkMass P (J + F.ell) : ℂ) *
      (if rawEdgeValid A ν forward (joinLabels v u)
          (s.1, joinLabels a b, s.2) (t.1, joinLabels c d, t.2)
          (emptyTransfer (s.1, joinLabels a b, s.2)) then
        rawCleanCoefficient A n theta forward ν (joinLabels v u)
          (s.1, joinLabels a b, s.2) (t.1, joinLabels c d, t.2) else 0) =
      if smallCleanGate J F.ell a c s t then
        (smallAuxMass v : ℂ) *
          (star (physicalSmallCoefficient F P J s.1) * physicalSmallCoefficient F P J t.1) *
          (if bigCleanGate A ν forward (smallArrayPrefix J F.ell a) b d u s t then
            bigCleanCoefficient A n theta forward ν (smallArrayPrefix J F.ell a) b d u else 0)
      else 0 := by
  have hr := rawEdgeValid_split A ν forward a c b d v u s t
  by_cases hs : smallCleanGate J F.ell a c s t
  · by_cases hb : bigCleanGate A ν forward (smallArrayPrefix J F.ell a) b d u s t
    · have hv := hr.mpr ⟨hs, hb⟩
      rw [if_pos hs, if_pos hb, if_pos hv, rawCleanCoefficient_join A n theta forward ν a c b d v u s t hV]
      unfold bigCleanCoefficient
      ring
    · have hv : ¬ rawEdgeValid A ν forward (joinLabels v u)
          (s.1, joinLabels a b, s.2) (t.1, joinLabels c d, t.2)
          (emptyTransfer (s.1, joinLabels a b, s.2)) := fun h => hb (hr.mp h).2
      simp only [if_pos hs, if_neg hb, if_neg hv, mul_zero]
  · have hv : ¬ rawEdgeValid A ν forward (joinLabels v u)
        (s.1, joinLabels a b, s.2) (t.1, joinLabels c d, t.2)
        (emptyTransfer (s.1, joinLabels a b, s.2)) := fun h => hs (hr.mp h).1
    simp only [if_neg hs, if_neg hv, mul_zero]

theorem sum_aux_split (f : P.Aux J → ℂ) :
    (∑ u : P.Aux J, f u) = ∑ v : SmallLabels P J, ∑ u : P.BigAux J, f (joinLabels v u) := by
  have h := Equiv.sum_comp (splitLabels P J).symm f
  change (∑ w : SmallLabels P J × P.BigAux J, f (joinLabels w.1 w.2)) = ∑ u : P.Aux J, f u at h
  rw [Fintype.sum_prod_type] at h
  exact h.symm

theorem rawCleanPattern_sum_split (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool)
    (ν : Pattern P J F.ell m) (a c : SmallLabels P (J + F.ell))
    (b d : P.BigLabels (J + F.ell)) (s t : PendingState P)
    (hV : ∀ g : P.SmallGroup, 0 < P.V g.val) :
    (smallMarkMass P (J + F.ell) : ℂ) *
      (∑ u : P.Aux J, if rawEdgeValid A ν forward u
          (s.1, joinLabels a b, s.2) (t.1, joinLabels c d, t.2)
          (emptyTransfer (s.1, joinLabels a b, s.2)) then
        rawCleanCoefficient A n theta forward ν u
          (s.1, joinLabels a b, s.2) (t.1, joinLabels c d, t.2) else 0) =
      if smallCleanGate J F.ell a c s t then
        (star (physicalSmallCoefficient F P J s.1) * physicalSmallCoefficient F P J t.1) *
          conditionedPatternEntry A n theta forward ν (smallArrayPrefix J F.ell a) b d s t
      else 0 := by
  rw [Finset.mul_sum, sum_aux_split]
  simp_rw [rawClean_summand_split A n theta forward ν a c b d _ _ s t (fun g => (hV g).le)]
  by_cases hs : smallCleanGate J F.ell a c s t
  · simp only [if_pos hs]
    rw [Finset.sum_comm]
    unfold conditionedPatternEntry
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    have hsmall : (∑ v : SmallLabels P J, (smallAuxMass v : ℂ)) = 1 := by
      exact_mod_cast smallAuxMass_sum J (fun g => (hV g).ne')
    calc
      _ = (∑ v : SmallLabels P J, (smallAuxMass v : ℂ)) *
          ((star (physicalSmallCoefficient F P J s.1) * physicalSmallCoefficient F P J t.1) *
            (if bigCleanGate A ν forward (smallArrayPrefix J F.ell a) b d u s t then
              bigCleanCoefficient A n theta forward ν (smallArrayPrefix J F.ell a) b d u else 0)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by rw [hsmall, one_mul]
  · simp only [if_neg hs, Finset.sum_const_zero]

theorem rawCleanKernel_coordinates (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool)
    (a c : SmallLabels P (J + F.ell)) (b d : P.BigLabels (J + F.ell))
    (s t : PendingState P) (hV : ∀ g : P.SmallGroup, 0 < P.V g.val) :
    (smallMarkMass P (J + F.ell) : ℂ) *
      rawCleanKernel A n theta forward
        (s.1, joinLabels a b, s.2) (t.1, joinLabels c d, t.2) =
      if smallCleanGate J F.ell a c s t then
        (star (physicalSmallCoefficient F P J s.1) * physicalSmallCoefficient F P J t.1) *
          conditionedKernel A n theta forward (smallArrayPrefix J F.ell a) (b, s) (d, t)
      else 0 := by
  unfold rawCleanKernel
  rw [Finset.mul_sum]
  simp_rw [rawCleanPattern_sum_split A n theta forward _ a c b d s t hV]
  by_cases hs : smallCleanGate J F.ell a c s t
  · simp only [if_pos hs]
    rw [← Finset.mul_sum]
    rfl
  · simp only [if_neg hs, Finset.sum_const_zero]


end Erdos821.P3Clean
