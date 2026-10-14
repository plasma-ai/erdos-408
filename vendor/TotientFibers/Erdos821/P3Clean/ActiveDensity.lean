import Erdos821.P3Clean.BigRefresh
import Erdos821.P3Clean.DensityIdentification

/-! Density factors for the tilted active labels and their fresh integrations. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def activeDensity (F : FixedData) (n : ℕ) {M : ℕ} (a : P.BigLabels M) : ℝ :=
  bigProductMass (fun g p => (baselinePrime F n p.val)⁻¹) a

def freshDensity (F : FixedData) (n : ℕ) (ν : Pattern P J F.ell m)
    (a : P.BigLabels (J + F.ell)) : ℝ :=
  bigFreshMass ν (fun g p => (baselinePrime F n p.val)⁻¹) a

theorem tiltedIdealMass_density (F : FixedData) (n : ℕ) {M : ℕ} (a : P.BigLabels M) :
    tiltedIdealMass F n a = P.idealMass a * activeDensity F n a := by
  unfold tiltedIdealMass PrimeGroups.idealMass activeDensity bigProductMass
  simp only [tiltedMu_eq_mu_mul, Finset.prod_mul_distrib]

theorem tiltedFreshMass_density (F : FixedData) (n : ℕ) (ν : Pattern P J F.ell m)
    (a : P.BigLabels (J + F.ell)) :
    tiltedFreshMass F n ν a = ν.freshMass a * freshDensity F n ν a := by
  unfold tiltedFreshMass Pattern.freshMass freshDensity bigFreshMass
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : ν.shared g.val i
  · simp only [if_pos hi, one_mul]
  · simp only [if_neg hi, tiltedMu_eq_mu_mul]

theorem activeDensity_pos (F : FixedData) (n : ℕ)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    {M : ℕ} (a : P.BigLabels M) : 0 < activeDensity F n a := by
  unfold activeDensity bigProductMass
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  exact inv_pos.mpr (hb g (a g i))

theorem freshDensity_pos (F : FixedData) (n : ℕ) (ν : Pattern P J F.ell m)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (a : P.BigLabels (J + F.ell)) : 0 < freshDensity F n ν a := by
  unfold freshDensity bigFreshMass
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact zero_lt_one
  · exact inv_pos.mpr (hb g (a g i))

theorem density_reversal (F : FixedData) (n : ℕ) (ν : Pattern P J F.ell m)
    (a b : P.BigLabels (J + F.ell)) (h : ν.matchesBig a b) :
    activeDensity F n a * freshDensity F n ν b =
      activeDensity F n b * freshDensity F n ν a :=
  bigFreshMass_reversal ν (fun g p => (baselinePrime F n p.val)⁻¹) a b h

theorem bigProductMass_actBig {M : ℕ}
    (mu : (g : P.BigGroup) → P.Prime g.val → ℝ) (p : P.BigPermutations M) (a : P.BigLabels M) :
    bigProductMass mu (P.actBig p a) = bigProductMass mu a := by
  apply Finset.prod_congr rfl
  intro g _
  exact Equiv.prod_comp (p g) (fun i => mu g (a g i))

theorem activeDensity_actBig (F : FixedData) (n : ℕ) {M : ℕ}
    (p : P.BigPermutations M) (a : P.BigLabels M) :
    activeDensity F n (P.actBig p a) = activeDensity F n a :=
  bigProductMass_actBig _ p a

theorem tiltedIdealMass_actBig (F : FixedData) (n : ℕ) {M : ℕ}
    (p : P.BigPermutations M) (a : P.BigLabels M) :
    tiltedIdealMass F n (P.actBig p a) = tiltedIdealMass F n a :=
  bigProductMass_actBig (fun g q => tiltedMu F P n g.val q) p a


end Erdos821.P3Clean
