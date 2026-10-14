import Erdos821.P3Clean.Structure

/-! Probability normalization of the original auxiliary laws. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups}

theorem V_pos_of_prime (g : P.Group) (p : P.Prime g) : 0 < P.V g := by
  unfold PrimeGroups.V
  apply Finset.sum_pos'
  · intro n hn
    exact inv_nonneg.mpr (Nat.cast_nonneg n)
  · refine ⟨p.val, p.property, ?_⟩
    exact inv_pos.mpr (by exact_mod_cast (P.prime g p.val p.property).pos)

theorem mu_pos (g : P.Group) (p : P.Prime g) : 0 < P.mu g p := by
  unfold PrimeGroups.mu
  exact inv_pos.mpr (mul_pos (V_pos_of_prime g p)
    (by exact_mod_cast (P.prime g p.val p.property).pos))

theorem mu_sum (g : P.Group) (hV : P.V g ≠ 0) : (∑ p : P.Prime g, P.mu g p) = 1 := by
  classical
  have hsum : (∑ p : P.Prime g, (p.val : ℝ)⁻¹) = P.V g := by
    symm
    exact Finset.sum_subtype (P.primes g) (fun _ => Iff.rfl) (fun p => (p : ℝ)⁻¹)
  simp only [PrimeGroups.mu, mul_inv_rev]
  rw [← Finset.sum_mul, hsum, mul_inv_cancel₀ hV]

theorem auxMass_sum {J ell m : ℕ} (ν : Pattern P J ell m)
    (hV : ∀ g, P.V g ≠ 0) : (∑ u : P.Aux J, ν.auxMass u) = 1 := by
  classical
  unfold Pattern.auxMass
  rw [← Fintype.prod_sum (fun g (a : Fin J → P.Prime g) => ∏ i, P.mu g (a i))]
  simp only [← Fintype.prod_sum]
  simp only [mu_sum _ (hV _), Finset.prod_const_one]

theorem bigAuxMass_sum {J ell m : ℕ} (ν : Pattern P J ell m)
    (hV : ∀ g : P.BigGroup, P.V g.val ≠ 0) : (∑ u : P.BigAux J, ν.bigAuxMass u) = 1 := by
  classical
  unfold Pattern.bigAuxMass
  rw [← Fintype.prod_sum (fun (g : P.BigGroup) (a : Fin J → P.Prime g.val) =>
    ∏ i, P.mu g.val (a i))]
  simp only [← Fintype.prod_sum]
  simp only [mu_sum _ (hV _), Finset.prod_const_one]


end Erdos821.P3Clean
