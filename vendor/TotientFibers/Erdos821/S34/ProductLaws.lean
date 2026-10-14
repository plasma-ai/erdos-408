import Erdos821.S34.Probability

set_option autoImplicit false

open scoped BigOperators Classical

namespace Erdos821.S34Core

noncomputable section

theorem group_law_sum (G : S34.Core.PrimeGroups) (g : Fin G.size)
    (hV : 0 < S34.Core.mass G g) :
    (∑ p : S34.Core.Label G g, S34.Core.mu G g p.val) = 1 := by
  simp only [S34.Core.mu, one_div, mul_inv_rev]
  rw [← Finset.sum_mul]
  have hs : (∑ p : S34.Core.Label G g, (p.val : ℝ)⁻¹) = S34.Core.mass G g := by
    change (∑ p : ↥(G.primes g), (p.val : ℝ)⁻¹) = _
    simp [S34.Core.mass, one_div]
    exact Finset.sum_attach (G.primes g) (fun p : ℕ => (p : ℝ)⁻¹)
  rw [hs, mul_inv_cancel₀ hV.ne']

theorem tuple_law_sum (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ)
    (hV : ∀ g, 0 < S34.Core.mass G g) :
    (∑ z : S34.Core.Tuple G k, S34.Core.tupleWeight G k z) = 1 := by
  have hrow (g : Fin G.size) :
      (∑ row : Fin (k g) → S34.Core.Label G g, ∏ j, S34.Core.mu G g (row j).val) = 1 := by
    calc
      _ = ∏ j : Fin (k g), ∑ p : S34.Core.Label G g, S34.Core.mu G g p.val :=
        (Fintype.prod_sum (fun _j : Fin (k g) => fun p : S34.Core.Label G g => S34.Core.mu G g p.val)).symm
      _ = 1 := by simp [group_law_sum G g (hV g)]
  change (∑ z : ∀ g, Fin (k g) → S34.Core.Label G g,
    ∏ g, ∏ j, S34.Core.mu G g (z g j).val) = 1
  calc
    _ = ∏ g, ∑ row : Fin (k g) → S34.Core.Label G g,
        ∏ j, S34.Core.mu G g (row j).val :=
      (Fintype.prod_sum (fun g => fun row : Fin (k g) → S34.Core.Label G g =>
        ∏ j, S34.Core.mu G g (row j).val)).symm
    _ = 1 := by simp only [hrow, Finset.prod_const_one]

end
end Erdos821.S34Core
