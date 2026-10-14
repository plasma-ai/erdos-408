import Erdos821.P4Probe.Family

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

lemma graph_mu_pos (P : PrimeGroups) (g : P.Group) (hV : 0 < P.V g)
    (p : P.Prime g) : 0 < P.mu g p := by
  have hp : 0 < (p.val : ℝ) := by exact_mod_cast (P.prime g p.val p.property).pos
  exact inv_pos.mpr (mul_pos hV hp)

lemma graph_mu_sum (P : PrimeGroups) (g : P.Group) (hV : 0 < P.V g) :
    ∑ p : P.Prime g, P.mu g p = 1 := by
  have hs : ∑ p : P.Prime g, (p.val : ℝ)⁻¹ = P.V g := by
    change (∑ p ∈ (P.primes g).attach, (p.val : ℝ)⁻¹) =
      ∑ p ∈ P.primes g, (p : ℝ)⁻¹
    exact Finset.sum_attach (P.primes g) (fun p : ℕ => (p : ℝ)⁻¹)
  simp only [PrimeGroups.mu, mul_inv_rev]
  rw [← Finset.sum_mul, hs, mul_inv_cancel₀ hV.ne']

lemma idealMass_pos (P : PrimeGroups) (M : ℕ) (hV : ∀ g, 0 < P.V g)
    (a : P.BigLabels M) : 0 < P.idealMass a := by
  apply Finset.prod_pos
  intro g _
  exact Finset.prod_pos (fun i _ => graph_mu_pos P g.val (hV g.val) (a g i))

lemma idealMass_sum (P : PrimeGroups) (M : ℕ) (hV : ∀ g, 0 < P.V g) :
    ∑ a : P.BigLabels M, P.idealMass a = 1 := by
  unfold PrimeGroups.idealMass
  trans ∏ g : P.BigGroup, ∑ a : Fin M → P.Prime g.val, ∏ i, P.mu g.val (a i)
  · exact (Fintype.prod_sum (fun (g : P.BigGroup) (a : Fin M → P.Prime g.val) =>
      ∏ i, P.mu g.val (a i))).symm
  apply Finset.prod_eq_one
  intro g _
  trans ∏ _i : Fin M, ∑ a : P.Prime g.val, P.mu g.val a
  · exact (Fintype.prod_sum (fun (_i : Fin M) (a : P.Prime g.val) => P.mu g.val a)).symm
  · simp only [graph_mu_sum P g.val (hV g.val), Finset.prod_const_one]

lemma bigAuxMass_sum {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (hV : ∀ g, 0 < P.V g) : ∑ u : P.BigAux J, ν.bigAuxMass u = 1 :=
  idealMass_sum P J hV

lemma idealMass_act (P : PrimeGroups) {M : ℕ} (π : P.BigPermutations M)
    (a : P.BigLabels M) : P.idealMass (P.actBig π a) = P.idealMass a := by
  unfold PrimeGroups.idealMass PrimeGroups.actBig
  apply Finset.prod_congr rfl
  intro g _
  exact Equiv.prod_comp (π g) (fun i => P.mu g.val (a g i))

/-- Weighted Cauchy–Schwarz for conditional L2 norms on shared labels. -/
lemma weighted_sqrt_cauchy {β : Type*} [Fintype β]
    (w a b : β → ℝ) (hw : ∀ z, 0 ≤ w z) (ha : ∀ z, 0 ≤ a z) (hb : ∀ z, 0 ≤ b z) :
    (∑ z, w z * Real.sqrt (a z) * Real.sqrt (b z)) ≤
      Real.sqrt (∑ z, w z * a z) * Real.sqrt (∑ z, w z * b z) := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun z => w z * Real.sqrt (a z) * Real.sqrt (b z))
    (f := fun z => w z * a z) (g := fun z => w z * b z)
    (fun z _ => mul_nonneg (hw z) (ha z))
    (fun z _ => mul_nonneg (hw z) (hb z))
    (fun z _ => le_of_eq (by
      rw [mul_pow, mul_pow, Real.sq_sqrt (ha z), Real.sq_sqrt (hb z)]
      ring))
  have hsa : 0 ≤ ∑ z, w z * a z := Finset.sum_nonneg (fun z _ => mul_nonneg (hw z) (ha z))
  have hsb : 0 ≤ ∑ z, w z * b z := Finset.sum_nonneg (fun z _ => mul_nonneg (hw z) (hb z))
  have hsq : (Real.sqrt (∑ z, w z * a z) * Real.sqrt (∑ z, w z * b z)) ^ 2 =
      (∑ z, w z * a z) * (∑ z, w z * b z) := by
    rw [mul_pow, Real.sq_sqrt hsa, Real.sq_sqrt hsb]
  have hn : 0 ≤ Real.sqrt (∑ z, w z * a z) * Real.sqrt (∑ z, w z * b z) := by positivity
  nlinarith

end
end Erdos821.P4Probe
