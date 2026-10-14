import Erdos821.S2.MassDecomposition
import Erdos821.S2.SpanMarkWeightTask

/-! Assemble per-prime lifespan costs across all big groups and operations. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

theorem group_operation_product {G I K R : Type*} [Fintype G] [Fintype I] [Fintype K]
    [CommMonoid R] (f0 : G → R) (f1 : I → G → R) (f2 : K → G → R) :
    (∏ g, f0 g) * (∏ i, ∏ g, f1 i g) * (∏ i, ∏ g, f2 i g) =
      ∏ g, f0 g * (∏ i, f1 i g) * (∏ i, f2 i g) := by
  have h1 : (∏ i, ∏ g, f1 i g) = ∏ g, ∏ i, f1 i g := Finset.prod_comm
  have h2 : (∏ i, ∏ g, f2 i g) = ∏ g, ∏ i, f2 i g := Finset.prod_comm
  rw [h1, h2]
  simp only [Finset.prod_mul_distrib]

namespace ResiduePath

variable {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
  (Q : ResiduePath A n)

def initialBigGroupFactor (g : P.BigGroup) : ℝ :=
  ∏ j : Fin (J + F.ell), tiltedMu F P n g.val (Q.labels 0 g.val j)

def freshBigGroupFactor (S : LifespanAssignment P n) (i : Fin n) (g : P.BigGroup) : ℝ :=
  ∏ j : Fin (J + F.ell),
    if (A.pattern (Q.pattern i)).shared g.val j ∨ j ∈ Q.promotionSlots S i g then 1
    else tiltedMu F P n g.val (Q.target i g.val j)

theorem all_big_group_weights (hMark : SpanMarkWeightTask) (S : LifespanAssignment P n)
    (hQ : Q.Valid) (hS : Q.lifespanValid S)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (hV : ∀ g : P.BigGroup, P.V g.val ≠ 0) :
    (∏ g : P.BigGroup, Q.initialBigGroupFactor g) *
        (∏ i : Fin n, ∏ g : P.BigGroup, Q.freshBigGroupFactor S i g *
          (P.V g.val) ^ (-((Q.promotionSlots S i g).card : ℤ))) *
        (∏ i : Fin (n + 1), ∏ g : P.BigGroup, ∏ p : P.Prime g.val, Q.spanGhostFactor S i g p) =
      (∏ g : P.BigGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) *
        (∏ i : Fin n, ∏ g : P.BigGroup,
          (P.V g.val) ^ (-((A.pattern (Q.pattern i)).t g.val : ℤ))) *
        (∏ g : P.BigGroup, ∏ p : P.Prime g.val, Q.spanWeight g p (S g p)) := by
  rw [group_operation_product]
  calc
    _ = ∏ g : P.BigGroup,
        (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ) *
          (∏ i : Fin n, (P.V g.val) ^ (-((A.pattern (Q.pattern i)).t g.val : ℤ))) *
          ∏ p : P.Prime g.val, Q.spanWeight g p (S g p) := by
      apply Finset.prod_congr rfl
      intro g _
      exact hMark F P J m n A Q S hQ hS hk g (hV g)
    _ = _ := by
      simp only [Finset.prod_mul_distrib]
      have hTarget :
          (∏ g : P.BigGroup, ∏ i : Fin n,
            (P.V g.val) ^ (-((A.pattern (Q.pattern i)).t g.val : ℤ))) =
          ∏ i : Fin n, ∏ g : P.BigGroup,
            (P.V g.val) ^ (-((A.pattern (Q.pattern i)).t g.val : ℤ)) := Finset.prod_comm
      rw [hTarget]


end ResiduePath


end Erdos821.S2Core
