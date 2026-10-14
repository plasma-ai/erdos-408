import Erdos821.S2.SpanHistory
import Mathlib.Data.List.FinRange

/-! Ordered ghost batches have permutation fibers with invariant coefficients. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups}

theorem zeroBirthBatch_perm {g : P.Group} {b : ℕ} (p : Fin b → P.Prime g)
    (sigma : Equiv.Perm (Fin b)) :
    zeroBirthBatch (fun i => p (sigma i)) = zeroBirthBatch p := by
  unfold zeroBirthBatch
  exact Multiset.coe_eq_coe.mpr (sigma.ofFn_comp_perm (fun i => (⟨p i, 0⟩ : P.Particle g)))

def reorderGhostChoice {M : ℕ} {s t : P.MemoryState M} (c : GhostChoice s t)
    (sigma : (g : P.BigGroup) → Equiv.Perm (Fin (c.2.1 g).val)) : GhostChoice s t :=
  ⟨c.1, c.2.1, fun g i => c.2.2 g (sigma g i)⟩

theorem reorderGhostChoice_valid {M : ℕ} {s t : P.MemoryState M} (c : GhostChoice s t)
    (sigma : (g : P.BigGroup) → Equiv.Perm (Fin (c.2.1 g).val)) :
    ghostChoiceValid (reorderGhostChoice c sigma) ↔ ghostChoiceValid c := by
  unfold ghostChoiceValid reorderGhostChoice
  simp only [zeroBirthBatch_perm]

theorem reorderGhostChoice_weight (F : FixedData) (n : ℕ) (rho : ℝ)
    (i : Fin (n + 1)) {M : ℕ} {s t : P.MemoryState M} (c : GhostChoice s t)
    (sigma : (g : P.BigGroup) → Equiv.Perm (Fin (c.2.1 g).val)) :
    ghostChoiceWeight F n rho i (reorderGhostChoice c sigma) =
      ghostChoiceWeight F n rho i c := by
  unfold ghostChoiceWeight reorderGhostChoice
  apply Finset.prod_congr rfl
  intro g _
  congr 1
  exact Equiv.prod_comp (sigma g) (fun h => tiltedMu F P n g.val (c.2.2 g h))

theorem reorderGhostChoice_injective {M : ℕ} {s t : P.MemoryState M}
    (c : GhostChoice s t) (hp : ∀ g, Function.Injective (c.2.2 g)) :
    Function.Injective (reorderGhostChoice c) := by
  intro sigma tau he
  have hbatch : (fun g i => c.2.2 g (sigma g i)) =
      (fun g i => c.2.2 g (tau g i)) := by
    have hs := (Prod.mk.inj he).2
    exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  funext g
  apply Equiv.ext
  intro i
  exact hp g (congrFun (congrFun hbatch g) i)

theorem ghostOrder_card {M : ℕ} {s t : P.MemoryState M} (c : GhostChoice s t) :
    Fintype.card ((g : P.BigGroup) → Equiv.Perm (Fin (c.2.1 g).val)) =
      ∏ g : P.BigGroup, (c.2.1 g).val.factorial := by
  simp [Fintype.card_pi, Fintype.card_perm]


end Erdos821.S2Core
