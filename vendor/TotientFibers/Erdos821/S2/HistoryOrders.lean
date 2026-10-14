import Erdos821.S2.BatchOrders

/-! Full histories retain all ghost-batch orderings with the same weight. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

namespace MemoryHistory

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)

abbrev BatchOrders := (i : Fin (n + 1)) →
  (g : P.BigGroup) → Equiv.Perm (Fin ((H.ghost i).2.1 g).val)

def reorderBatches (sigma : H.BatchOrders) : MemoryHistory A n where
  before := H.before
  after := H.after
  ghost := fun i => reorderGhostChoice (H.ghost i) (sigma i)
  edge := H.edge

theorem reorderBatches_valid (sigma : H.BatchOrders) :
    (H.reorderBatches sigma).Valid ↔ H.Valid := by
  simp only [Valid, reorderBatches, reorderGhostChoice_valid]

theorem reorderBatches_weight (rho theta : ℝ) (sigma : H.BatchOrders) :
    (H.reorderBatches sigma).Weight rho theta = H.Weight rho theta := by
  simp only [Weight, reorderBatches, reorderGhostChoice_weight]

theorem reorderBatches_birthValues (sigma : H.BatchOrders) :
    (H.reorderBatches sigma).birthValues = H.birthValues := by
  have hg (i : Fin (n + 1)) :
      (H.reorderBatches sigma).ghostBirthValues i = H.ghostBirthValues i := by
    dsimp only [ghostBirthValues, reorderBatches, reorderGhostChoice]
    apply Finset.sum_congr rfl
    intro g _
    exact Equiv.sum_comp (sigma i g) (fun h => ({((H.ghost i).2.2 g h).val} : Multiset ℕ))
  unfold birthValues
  rw [Finset.sum_congr rfl (fun i _ => hg i)]
  rfl

theorem reorderBatches_distinct (sigma : H.BatchOrders) :
    (H.reorderBatches sigma).DistinctBirths ↔ H.DistinctBirths := by
  unfold DistinctBirths
  rw [H.reorderBatches_birthValues]

theorem reorderBatches_projection (sigma : H.BatchOrders) :
    (H.reorderBatches sigma).toResiduePath = H.toResiduePath := rfl

theorem reorderBatches_injective
    (hp : ∀ i g, Function.Injective ((H.ghost i).2.2 g)) :
    Function.Injective H.reorderBatches := by
  intro sigma tau he
  let pack (K : MemoryHistory A n) :
      Σ b : Fin (n + 1) → P.MemoryState (J + F.ell),
        Σ a : Fin (n + 1) → P.MemoryState (J + F.ell),
          (i : Fin (n + 1)) → GhostChoice (b i) (a i) :=
    ⟨K.before, K.after, K.ghost⟩
  have hpack := congrArg pack he
  have ha := eq_of_heq (Sigma.mk.inj_iff.mp hpack).2
  have hg := eq_of_heq (Sigma.mk.inj_iff.mp ha).2
  funext i
  apply reorderGhostChoice_injective (H.ghost i) (hp i)
  exact congrFun hg i

theorem batchOrders_card :
    Fintype.card H.BatchOrders =
      ∏ i : Fin (n + 1), ∏ g : P.BigGroup, ((H.ghost i).2.1 g).val.factorial := by
  simp [BatchOrders, Fintype.card_pi, Fintype.card_perm]

theorem reorderBatches_weight_sum (rho theta : ℝ) :
    (∑ sigma : H.BatchOrders, (H.reorderBatches sigma).Weight rho theta) =
      ((∏ i : Fin (n + 1), ∏ g : P.BigGroup,
        ((H.ghost i).2.1 g).val.factorial : ℕ) : ℂ) * H.Weight rho theta := by
  simp only [H.reorderBatches_weight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    H.batchOrders_card]


end MemoryHistory
end Erdos821.S2Core
