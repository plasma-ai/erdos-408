import Erdos821.S2.LowRankTask
import Erdos821.S2.EdgeTasks
import Erdos821.S2.GhostTasks

/-! Chronological dependent births retain their reciprocal-prime savings. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

def highRankHistoryExpression {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n B : ℕ) (rho theta : ℝ)
    (pi : Finset (Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B))))) : ℝ :=
  ∑' H : MemoryHistory A n,
    if H.Valid ∧ H.Truncated B ∧ birthEvent (H.performedFin B) (H.valueFin B) pi then
      ‖H.Weight rho theta‖ else 0

def HighRankMemoryTask (F : FixedData) (r : MemoryParameters F) : Prop :=
  GhostRowsTask → MemoryEdgeAbsoluteTask F r →
  ∀ (m : ℕ) (C₁ : ℝ), ∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ J : ℕ,
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ P : PrimeGroups,
    P.Admissible F x → ∀ A : Model F P J m, A.patternMass ≤ (L x) ^ C₁ →
    ∀ theta : ℝ,
    ∀ pi : Finset (Finset
      (Fin (Fintype.card (BirthAddress P (J + F.ell) (N x) (memoryCutoff x))))),
      BirthCollection pi →
      highRankHistoryExpression A (N x) (memoryCutoff x) r.rho theta pi ≤
        (L x) ^ (Ch * (N x + 1 : ℕ)) *
          (C / Real.exp ((L x) ^ F.c)) ^ birthRank pi


end Erdos821.S2Core
