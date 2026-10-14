import Erdos821.S2.SpanSumTask

/-! Sum independent finite prime lifespans and restore their baseline factors. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

namespace ResiduePath

variable {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
  (Q : ResiduePath A n)

def spanProduct (S : LifespanAssignment P n) : ℝ :=
  ∏ g : P.BigGroup, ∏ p : P.Prime g.val, Q.spanWeight g p (S g p)

def bigResidueExpectation : ℝ :=
  ∏ g : P.BigGroup, ∏ p : P.Prime g.val,
    onePrimeExpectation p.val (n + 1) (eta F n)
      (fun i => (Q.offset i : ZMod p.val)) (Q.activeVisits g p)

theorem spanWeight_zero_of_invalid (g : P.BigGroup) (p : P.Prime g.val)
    (span : PrimeSpan n) (hn : ¬ Q.spanValid g p span) : Q.spanWeight g p span = 0 := by
  cases span with
  | none => exact ite_eq_right hn
  | some be =>
    rcases be with ⟨b, e⟩
    exact ite_eq_right hn

theorem spanProduct_zero_of_invalid (S : LifespanAssignment P n)
    (hn : ¬ Q.lifespanValid S) : Q.spanProduct S = 0 := by
  change ¬ ∀ g p, Q.spanValid g p (S g p) at hn
  obtain ⟨g, hg⟩ := not_forall.mp hn
  obtain ⟨p, hp⟩ := not_forall.mp hg
  apply Finset.prod_eq_zero (Finset.mem_univ g)
  apply Finset.prod_eq_zero (Finset.mem_univ p)
  exact Q.spanWeight_zero_of_invalid g p (S g p) hp

theorem spanProduct_sum :
    (∑ S : LifespanAssignment P n, Q.spanProduct S) =
      ∏ g : P.BigGroup, ∏ p : P.Prime g.val, ∑ span : PrimeSpan n, Q.spanWeight g p span := by
  unfold spanProduct
  have hOuter := Fintype.prod_sum (fun (g : P.BigGroup) (s : P.Prime g.val → PrimeSpan n) =>
    ∏ p : P.Prime g.val, Q.spanWeight g p (s p))
  rw [← hOuter]
  apply Finset.prod_congr rfl
  intro g _
  exact (Fintype.prod_sum (fun (p : P.Prime g.val) (span : PrimeSpan n) =>
    Q.spanWeight g p span)).symm

theorem valid_spanProduct_sum :
    (∑ S : {S : LifespanAssignment P n // Q.lifespanValid S}, Q.spanProduct S.val) =
      ∏ g : P.BigGroup, ∏ p : P.Prime g.val, ∑ span : PrimeSpan n, Q.spanWeight g p span := by
  have hz : (∑ S : {S : LifespanAssignment P n // ¬ Q.lifespanValid S},
      Q.spanProduct S.val) = 0 := by
    apply Finset.sum_eq_zero
    intro S _
    exact Q.spanProduct_zero_of_invalid S.val S.property
  have he := Fintype.sum_subtype_add_sum_subtype (fun S : LifespanAssignment P n => Q.lifespanValid S)
    Q.spanProduct
  rw [hz, add_zero] at he
  exact he.trans Q.spanProduct_sum

theorem valid_spanProduct_sum_normalized (hSpan : SpanSumTask)
    (hbp : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, baselinePrime F n p.val ≠ 0) :
    (∑ S : {S : LifespanAssignment P n // Q.lifespanValid S}, Q.spanProduct S.val) =
      (∏ g : P.BigGroup, ∏ p : P.Prime g.val, (baselinePrime F n p.val)⁻¹) *
        Q.bigResidueExpectation := by
  rw [Q.valid_spanProduct_sum]
  calc
    _ = ∏ g : P.BigGroup, ∏ p : P.Prime g.val,
        (baselinePrime F n p.val)⁻¹ *
          onePrimeExpectation p.val (n + 1) (eta F n)
            (fun i => (Q.offset i : ZMod p.val)) (Q.activeVisits g p) := by
      apply Finset.prod_congr rfl
      intro g _
      apply Finset.prod_congr rfl
      intro p _
      exact hSpan F P J m n A Q g p (hbp g p)
    _ = _ := by simp only [bigResidueExpectation, Finset.prod_mul_distrib]

end ResiduePath

theorem bigBaseline_eq_subtypes (F : FixedData) (P : PrimeGroups) (n : ℕ) :
    bigBaseline F P n = ∏ g : P.BigGroup, ∏ p : P.Prime g.val, baselinePrime F n p.val := by
  unfold bigBaseline
  rw [Finset.prod_subtype (p := fun g : P.Group => P.big g = true)
    P.bigGroups (by simp [PrimeGroups.bigGroups])]
  apply Finset.prod_congr rfl
  intro g _
  exact Finset.prod_subtype (P.primes g.val) (fun _ => Iff.rfl) (baselinePrime F n)

namespace ResiduePath

variable {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
  (Q : ResiduePath A n)

theorem baseline_mul_valid_spanProduct_sum (hSpan : SpanSumTask)
    (hbp : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, baselinePrime F n p.val ≠ 0) :
    bigBaseline F P n *
      (∑ S : {S : LifespanAssignment P n // Q.lifespanValid S}, Q.spanProduct S.val) =
        Q.bigResidueExpectation := by
  rw [Q.valid_spanProduct_sum_normalized hSpan hbp, bigBaseline_eq_subtypes]
  have hc : (∏ g : P.BigGroup, ∏ p : P.Prime g.val, baselinePrime F n p.val) *
      (∏ g : P.BigGroup, ∏ p : P.Prime g.val, (baselinePrime F n p.val)⁻¹) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro g _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p _
    exact mul_inv_cancel₀ (hbp g p)
  rw [← mul_assoc, hc, one_mul]


end ResiduePath


end Erdos821.S2Core
