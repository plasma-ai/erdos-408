import Erdos821.P3Clean.ConditionedKernel

/-! The big dilation exponent gives a natural power of one fixed cyclic translation. -/

noncomputable section

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

abbrev PendingCycle (P : PrimeGroups) (B : ℕ) :=
  TranslationCycle (pendingTranslationEquiv (P := P) B 1)

def dilationCycleStep (A : Model F P J m) (B : ℕ) (forward : Bool)
    (d : SmallLabels P J) : PendingCycle P B :=
  ((if forward then A.k else -A.k) * (prefixPrimeProduct J d : ℤ)) •
    cycleStep (pendingTranslationEquiv (P := P) B 1)

def cycleDisplacement (A : Model F P J m) (B : ℕ) (ν : Pattern P J F.ell m)
    (forward : Bool) (d : SmallLabels P J) (a : P.BigLabels (J + F.ell)) (u : P.BigAux J) :
    PendingCycle P B :=
  (ν.DBig a u) • dilationCycleStep A B forward d

theorem cycleDisplacement_act (A : Model F P J m) (B : ℕ) (ν : Pattern P J F.ell m)
    (forward : Bool) (d : SmallLabels P J) (a : P.BigLabels (J + F.ell)) (u : P.BigAux J) :
    cycleAct (pendingTranslationEquiv (P := P) B 1)
      (cycleDisplacement A B ν forward d a u) = pendingTranslationEquiv B (bigStep A ν forward d a u) := by
  unfold cycleDisplacement dilationCycleStep
  rw [← natCast_zsmul, ← mul_zsmul]
  rw [cycleAct_step_zsmul]
  have he : (ν.DBig a u : ℤ) *
      ((if forward then A.k else -A.k) * (prefixPrimeProduct J d : ℤ)) =
      bigStep A ν forward d a u := by unfold bigStep; ring
  rw [he]
  exact (pendingTranslationEquiv_zpow B (bigStep A ν forward d a u)).symm

theorem cycleDisplacement_character (A : Model F P J m) (B : ℕ)
    [Fintype (CutPendingState P B)] (forward : Bool) (d : SmallLabels P J)
    (psi : AddChar (PendingCycle P B) ℂ) :
    ∃ theta : ℝ, ∀ (ν : Pattern P J F.ell m) (a : P.BigLabels (J + F.ell)) (u : P.BigAux J),
      psi (cycleDisplacement A B ν forward d a u) = phase (theta * (ν.DBig a u : ℝ)) := by
  obtain ⟨theta, ht⟩ := character_nsmul_phase psi (dilationCycleStep A B forward d)
  exact ⟨theta, fun ν a u => ht (ν.DBig a u)⟩


end Erdos821.P3Clean
