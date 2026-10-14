import Erdos821.S2.HighRankTask

/-! Every equality-rank expression at a finite cutoff is genuinely summable. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem rankHistory_hasFiniteSupport {β : Type*} [Zero β]
    (A : Model F P J m) (n B : ℕ)
    (pi : Finset (Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B)))))
    (f : MemoryHistory A n → β) :
    Function.HasFiniteSupport (fun H : MemoryHistory A n =>
      if H.Valid ∧ H.Truncated B ∧ birthEvent (H.performedFin B) (H.valueFin B) pi then
        f H else 0) := by
  have hf : Set.Finite {H : MemoryHistory A n | H.Truncated B} :=
    @Set.toFinite (MemoryHistory A n) {H | H.Truncated B}
      (truncated_history_finite A n B)
  apply hf.subset
  intro H hH
  change (if H.Valid ∧ H.Truncated B ∧ birthEvent (H.performedFin B) (H.valueFin B) pi then
    f H else 0) ≠ 0 at hH
  by_contra hn
  exact hH (ite_eq_right (fun hp => hn hp.2.1))

theorem lowRankHistoryExpression_summable (A : Model F P J m) (n B : ℕ)
    (rho theta : ℝ)
    (pi : Finset (Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B))))) :
    Summable (fun H : MemoryHistory A n =>
      if H.Valid ∧ H.Truncated B ∧ birthEvent (H.performedFin B) (H.valueFin B) pi then
        H.Weight rho theta else 0) :=
  summable_of_hasFiniteSupport (rankHistory_hasFiniteSupport A n B pi (fun H => H.Weight rho theta))

theorem highRankHistoryExpression_summable (A : Model F P J m) (n B : ℕ)
    (rho theta : ℝ)
    (pi : Finset (Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B))))) :
    Summable (fun H : MemoryHistory A n =>
      if H.Valid ∧ H.Truncated B ∧ birthEvent (H.performedFin B) (H.valueFin B) pi then
        ‖H.Weight rho theta‖ else 0) :=
  summable_of_hasFiniteSupport (rankHistory_hasFiniteSupport A n B pi (fun H => ‖H.Weight rho theta‖))

theorem lowRankHistoryExpression_norm_le (A : Model F P J m) (n B : ℕ)
    (rho theta : ℝ)
    (pi : Finset (Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B))))) :
    ‖lowRankHistoryExpression A n B rho theta pi‖ ≤
      highRankHistoryExpression A n B rho theta pi := by
  let f (H : MemoryHistory A n) : ℂ :=
    if H.Valid ∧ H.Truncated B ∧ birthEvent (H.performedFin B) (H.valueFin B) pi then
      H.Weight rho theta else 0
  have he (H : MemoryHistory A n) : ‖f H‖ =
      if H.Valid ∧ H.Truncated B ∧ birthEvent (H.performedFin B) (H.valueFin B) pi then
        ‖H.Weight rho theta‖ else 0 := by
    simp only [f, apply_ite norm, norm_zero]
  have hs : Summable (fun H => ‖f H‖) := by
    simp_rw [he]
    exact highRankHistoryExpression_summable A n B rho theta pi
  simpa only [lowRankHistoryExpression, highRankHistoryExpression, he] using
    norm_tsum_le_tsum_norm hs


end Erdos821.S2Core
