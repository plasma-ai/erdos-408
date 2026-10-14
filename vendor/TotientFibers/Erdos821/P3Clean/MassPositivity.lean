import Erdos821.P3Clean.RawNormAssembly
import Erdos821.P3Clean.Baseline

/-! Positivity of the between-map measure once all big baselines are positive. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem tiltedMu_pos (F : FixedData) (P : PrimeGroups) (n : ℕ) (g : P.Group) (p : P.Prime g)
    (hb : 0 < baselinePrime F n p.val) : 0 < tiltedMu F P n g p := by
  rw [tiltedMu_eq_mu_mul]
  exact mul_pos (mu_pos g p) (inv_pos.mpr hb)

theorem groupMemoryMass_nonneg (F : FixedData) (P : PrimeGroups) (n : ℕ)
    (g : P.Group) (hb : ∀ p : P.Prime g, 0 < baselinePrime F n p.val) (z : P.Memory g) :
    0 ≤ P.groupMemoryMass F n g z := by
  classical
  unfold PrimeGroups.groupMemoryMass
  apply div_nonneg
  · apply Multiset.prod_nonneg
    intro r hr
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hr
    exact (tiltedMu_pos F P n g p.1 (hb p.1)).le
  · positivity

theorem betweenMass_nonneg (F : FixedData) (P : PrimeGroups) (n : ℕ)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    {M B : ℕ} (a : BetweenState P M B) : 0 ≤ betweenMass F n a := by
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro g _
    apply Finset.prod_nonneg
    intro i _
    exact (tiltedMu_pos F P n g.val (a.1 g i) (hb g _)).le
  · unfold pendingMass
    apply mul_nonneg
    · positivity
    · apply Finset.prod_nonneg
      intro g _
      exact groupMemoryMass_nonneg F P n g.val (hb g) (a.2.val.2 g)


end Erdos821.P3Clean
