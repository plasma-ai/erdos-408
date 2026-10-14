import Erdos821.S2.MemoryEdge
import Mathlib

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

lemma fresh_sum_eq {α : Type*} [Fintype α] [DecidableEq α] (mu : α → ℝ) (k : ℕ) :
    ∑ p : Fin k → α, ∏ i, mu (p i) = (∑ a, mu a) ^ k := by
  classical
  have h1 := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset α))
    (fun _ : Fin k => fun a : α => mu a)
  have lhs : (∏ _i : Fin k, ∑ _j : α, mu _j) = (∑ a, mu a) ^ k := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have rhs : (∑ x ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset α)), ∏ i, mu (x i))
      = ∑ p : Fin k → α, ∏ i, mu (p i) := by
    rw [Fintype.piFinset_univ]
  -- h1 : ∏ i, ∑ j∈univ, mu j = ∑ x∈piFinset, ...
  -- lhs/rhs convert to match h1 (up to ∑ j∈univ vs ∑ j, which are defeq as both sum over univ)
  have h1' : (∏ _i : Fin k, ∑ _j : α, mu _j)
      = (∑ x ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset α)), ∏ i, mu (x i)) := h1
  rw [lhs, rhs] at h1'
  exact h1'.symm

lemma fresh_sum_bound {α : Type*} [Fintype α] [DecidableEq α] (mu : α → ℝ)
    (hmu_nonneg : ∀ a, 0 ≤ mu a) (hmu_sum : ∑ a, mu a ≤ 2) (k : ℕ) :
    ∑ p : Fin k → α, ∏ i, mu (p i) ≤ (2 : ℝ) ^ k := by
  rw [fresh_sum_eq]
  apply pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ => hmu_nonneg a)) hmu_sum k

end Erdos821.P3Edge
