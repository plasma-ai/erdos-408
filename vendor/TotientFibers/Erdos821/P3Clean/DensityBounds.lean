import Erdos821.P3Clean.FreshDensityFactor

/-! Uniform bounds for the fresh density factors. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem bigFreshMass_bounds {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (mu : (g : P.BigGroup) → P.Prime g.val → ℝ) (eps : ℝ) (he : 0 ≤ eps)
    (hmu : ∀ g p, 1 ≤ mu g p ∧ mu g p ≤ 1 + eps) (a : P.BigLabels (J + ell)) :
    1 ≤ bigFreshMass ν mu a ∧
      bigFreshMass ν mu a ≤ (1 + eps) ^ ((J + ell) * Fintype.card P.BigGroup) := by
  have hlo (g : P.BigGroup) (i : Fin (J + ell)) :
      1 ≤ (if ν.shared g.val i then (1 : ℝ) else mu g (a g i)) := by
    split_ifs
    · exact le_rfl
    · exact (hmu g _).1
  have hhi (g : P.BigGroup) (i : Fin (J + ell)) :
      (if ν.shared g.val i then (1 : ℝ) else mu g (a g i)) ≤ 1 + eps := by
    split_ifs
    · linarith
    · exact (hmu g _).2
  have hlg (g : P.BigGroup) : 1 ≤
      ∏ i : Fin (J + ell), if ν.shared g.val i then (1 : ℝ) else mu g (a g i) := by
    simpa only [Finset.prod_const_one] using
      (Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin (J + ell) => (1 : ℝ))
        (fun _ _ => zero_le_one) (fun i _ => hlo g i))
  refine ⟨?_, ?_⟩
  · simpa only [Finset.prod_const_one, bigFreshMass] using
      (Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : P.BigGroup => (1 : ℝ))
        (fun _ _ => zero_le_one) (fun g _ => hlg g))
  have hg (g : P.BigGroup) :
      (∏ i : Fin (J + ell), if ν.shared g.val i then (1 : ℝ) else mu g (a g i)) ≤
        (1 + eps) ^ (J + ell) := by
    calc
      _ ≤ ∏ _ : Fin (J + ell), (1 + eps) := Finset.prod_le_prod₀
        (fun i _ => zero_le_one.trans (hlo g i)) (fun i _ => hhi g i)
      _ = _ := by simp
  calc
    _ ≤ ∏ _ : P.BigGroup, (1 + eps) ^ (J + ell) := Finset.prod_le_prod₀
      (fun g _ => Finset.prod_nonneg (fun i _ => zero_le_one.trans (hlo g i))) (fun g _ => hg g)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, ← pow_mul]

theorem freshDensity_bounds (F : FixedData) (P : PrimeGroups) (n : ℕ) {J m : ℕ}
    (ν : Pattern P J F.ell m) (eps : ℝ) (he : 0 ≤ eps)
    (hmu : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      1 ≤ (baselinePrime F n p.val)⁻¹ ∧ (baselinePrime F n p.val)⁻¹ ≤ 1 + eps)
    (a : P.BigLabels (J + F.ell)) :
    1 ≤ freshDensity F n ν a ∧
      freshDensity F n ν a ≤ (1 + eps) ^ ((J + F.ell) * Fintype.card P.BigGroup) :=
  bigFreshMass_bounds ν (fun _ p => (baselinePrime F n p.val)⁻¹) eps he hmu a

theorem freshSqrtFactor_bounds (F : FixedData) (P : PrimeGroups) (n : ℕ) {J m : ℕ}
    (ν : Pattern P J F.ell m) (eps : ℝ) (he : 0 ≤ eps)
    (hmu : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      1 ≤ (baselinePrime F n p.val)⁻¹ ∧ (baselinePrime F n p.val)⁻¹ ≤ 1 + eps)
    (a b : P.BigLabels (J + F.ell)) :
    1 ≤ Real.sqrt (freshDensity F n ν a) * Real.sqrt (freshDensity F n ν b) ∧
      Real.sqrt (freshDensity F n ν a) * Real.sqrt (freshDensity F n ν b) ≤
        (1 + eps) ^ ((J + F.ell) * Fintype.card P.BigGroup) := by
  obtain ⟨ha0, ha1⟩ := freshDensity_bounds F P n ν eps he hmu a
  obtain ⟨hb0, hb1⟩ := freshDensity_bounds F P n ν eps he hmu b
  have hsa : 1 ≤ Real.sqrt (freshDensity F n ν a) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ha0
  have hsb : 1 ≤ Real.sqrt (freshDensity F n ν b) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hb0
  refine ⟨by nlinarith, ?_⟩
  calc
    _ ≤ Real.sqrt ((1 + eps) ^ ((J + F.ell) * Fintype.card P.BigGroup)) *
        Real.sqrt ((1 + eps) ^ ((J + F.ell) * Fintype.card P.BigGroup)) :=
      mul_le_mul (Real.sqrt_le_sqrt ha1) (Real.sqrt_le_sqrt hb1)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (pow_nonneg (by linarith) _)


end Erdos821.P3Clean
