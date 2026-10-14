import Erdos821.S2High.Baseline

noncomputable section

namespace Erdos821.S2High

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups} {J ell m : ℕ}

def coefficientSup (ν : Pattern P J ell m) : ℝ :=
  sSup (Set.range (fun z : P.BigLabels (J + ell) × P.BigLabels (J + ell) × P.BigAux J =>
    ‖ν.coefficient z.1 z.2.1 z.2.2‖))

theorem coefficientSup_nonneg (ν : Pattern P J ell m) : 0 ≤ coefficientSup ν := by
  classical
  let α := P.BigLabels (J + ell) × P.BigLabels (J + ell) × P.BigAux J
  by_cases hα : Nonempty α
  · obtain ⟨z⟩ := hα
    have hbdd : BddAbove (Set.range (fun z : α => ‖ν.coefficient z.1 z.2.1 z.2.2‖)) :=
      (Set.finite_range _).bddAbove
    have hz : ‖ν.coefficient z.1 z.2.1 z.2.2‖ ∈
        Set.range (fun z : α => ‖ν.coefficient z.1 z.2.1 z.2.2‖) := ⟨z, rfl⟩
    exact (norm_nonneg _).trans (le_csSup hbdd hz)
  · have hRange : Set.range (fun z : α => ‖ν.coefficient z.1 z.2.1 z.2.2‖) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro y hy
      rcases hy with ⟨z, _⟩
      exact hα ⟨z⟩
    unfold coefficientSup
    rw [hRange]
    simp

def majorantPattern (ν : Pattern P J ell m) : Pattern P J ell m :=
  { ν with
    coefficient := fun _ _ _ => (coefficientSup ν : ℂ)
    coefficient_aux_ext := by
      intro a b u v huv
      rfl }

theorem majorantPattern_sup (ν : Pattern P J ell m) :
    sSup (Set.range (fun z : P.BigLabels (J + ell) × P.BigLabels (J + ell) × P.BigAux J =>
      ‖(majorantPattern ν).coefficient z.1 z.2.1 z.2.2‖)) = coefficientSup ν := by
  classical
  let α := P.BigLabels (J + ell) × P.BigLabels (J + ell) × P.BigAux J
  have hnonneg := coefficientSup_nonneg ν
  have hnorm : ‖(coefficientSup ν : ℂ)‖ = coefficientSup ν := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  by_cases hα : Nonempty α
  · letI : Nonempty α := hα
    have hRange : Set.range (fun _ : α => ‖(coefficientSup ν : ℂ)‖) =
        {coefficientSup ν} := by
      apply Set.ext
      intro y
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, rfl⟩
        exact hnorm
      · intro hy
        subst y
        obtain ⟨z⟩ := hα
        exact ⟨z, hnorm⟩
    change sSup (Set.range (fun z : α => ‖(coefficientSup ν : ℂ)‖)) = coefficientSup ν
    rw [hRange]
    simp
  · have hRange : Set.range (fun z : α => ‖ν.coefficient z.1 z.2.1 z.2.2‖) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro y hy
      rcases hy with ⟨z, _⟩
      exact hα ⟨z⟩
    have hMajRange : Set.range (fun z : α => ‖(coefficientSup ν : ℂ)‖) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro y hy
      rcases hy with ⟨z, _⟩
      exact hα ⟨z⟩
    change sSup (Set.range (fun z : α => ‖(coefficientSup ν : ℂ)‖)) =
      sSup (Set.range (fun z : α => ‖ν.coefficient z.1 z.2.1 z.2.2‖))
    rw [hMajRange, hRange]

def majorantModel {F : FixedData} (A : Model F P J m) : Model F P J m :=
  { A with pattern := fun i => majorantPattern (A.pattern i) }

theorem majorantModel_patternMass {F : FixedData} (A : Model F P J m) :
    (majorantModel A).patternMass = A.patternMass := by
  classical
  simp only [Model.patternMass, majorantModel]
  apply Finset.sum_congr rfl
  intro i hi
  exact majorantPattern_sup (A.pattern i)


end Erdos821.S2High
