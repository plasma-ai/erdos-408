import Erdos821.S2.RankSummability

/-! The actual truncated history sum admits the finite equality-rank expansion. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def truncatedHistories (A : Model F P J m) (n B : ℕ) : Finset (MemoryHistory A n) :=
  (@Set.toFinite (MemoryHistory A n) {H | H.Truncated B}
    (truncated_history_finite A n B)).toFinset

theorem mem_truncatedHistories (A : Model F P J m) (n B : ℕ) (H : MemoryHistory A n) :
    H ∈ truncatedHistories A n B ↔ H.Truncated B := by
  simp only [truncatedHistories, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

def truncatedDistinctMemoryExpression (A : Model F P J m) (n B : ℕ) (rho theta : ℝ) : ℂ :=
  ∑' H : MemoryHistory A n,
    if H.Valid ∧ H.Truncated B ∧ H.DistinctBirths then H.Weight rho theta else 0

theorem truncatedDistinctMemoryExpression_eq_sum (A : Model F P J m) (n B : ℕ)
    (rho theta : ℝ) :
    truncatedDistinctMemoryExpression A n B rho theta =
      ∑ H ∈ truncatedHistories A n B,
        if H.Valid ∧ H.DistinctBirths then H.Weight rho theta else 0 := by
  unfold truncatedDistinctMemoryExpression
  rw [tsum_eq_sum (s := truncatedHistories A n B) (fun H hH =>
    ite_eq_right (fun hp => hH ((mem_truncatedHistories A n B H).mpr hp.2.1)))]
  apply Finset.sum_congr rfl
  intro H hH
  simp only [(mem_truncatedHistories A n B H).mp hH, true_and]

theorem lowRankHistoryExpression_eq_sum (A : Model F P J m) (n B : ℕ) (rho theta : ℝ)
    (pi : Finset (Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B))))) :
    lowRankHistoryExpression A n B rho theta pi =
      ∑ H ∈ truncatedHistories A n B,
        if H.Valid ∧ birthEvent (H.performedFin B) (H.valueFin B) pi then
          H.Weight rho theta else 0 := by
  unfold lowRankHistoryExpression
  rw [tsum_eq_sum (s := truncatedHistories A n B) (fun H hH =>
    ite_eq_right (fun hp => hH ((mem_truncatedHistories A n B H).mpr hp.2.1)))]
  apply Finset.sum_congr rfl
  intro H hH
  simp only [(mem_truncatedHistories A n B H).mp hH, true_and]

theorem weighted_distinct_expansion {A : Model F P J m} {n : ℕ}
    (H : MemoryHistory A n) (B : ℕ) (hH : H.Truncated B) (w : ℂ) :
    (if H.DistinctBirths then w else 0) =
      ∑ pi ∈ Finset.univ.powerset.powerset.filter BirthCollection,
        (birthMobius pi : ℂ) *
          if birthEvent (H.performedFin B) (H.valueFin B) pi then w else 0 := by
  have he := congrArg (fun z : ℤ => (z : ℂ) * w) (H.distinct_birth_expansion_history B hH)
  simpa only [Int.cast_sum, Int.cast_ite, Int.cast_one, Int.cast_zero, Finset.sum_mul,
    ite_mul, mul_ite, one_mul, zero_mul, mul_zero] using he

theorem truncatedDistinctMemoryExpression_rank_expansion (A : Model F P J m) (n B : ℕ)
    (rho theta : ℝ) :
    truncatedDistinctMemoryExpression A n B rho theta =
      ∑ pi ∈ Finset.univ.powerset.powerset.filter BirthCollection,
        (birthMobius pi : ℂ) * lowRankHistoryExpression A n B rho theta pi := by
  rw [truncatedDistinctMemoryExpression_eq_sum]
  simp_rw [lowRankHistoryExpression_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro H hH
  by_cases hv : H.Valid
  · simp only [hv, true_and]
    exact weighted_distinct_expansion H B ((mem_truncatedHistories A n B H).mp hH)
      (H.Weight rho theta)
  · simp only [hv, false_and, ite_false, mul_zero, Finset.sum_const_zero]


end Erdos821.S2Core
