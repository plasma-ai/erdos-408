import Erdos821.P5.ForbiddenProbability
import Erdos821.P5.FreeCollisionTheorem

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Graph

abbrev SharedIndex {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m) :=
  (g : P.Group) × {i : Fin J // i ∈ sharedSlots ν g}

abbrev SharedDraw {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m) :=
  (j : SharedIndex ν) → P.Prime j.1

def sharedDrawLaw {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (z : SharedDraw ν) : ℝ := productLaw (fun j : SharedIndex ν => P.mu j.1) z

def sharedRestriction {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (a : P.Labels (J + ell)) : SharedDraw ν := fun j => a j.1 (ν.slot j.2.val)

theorem sharedDrawLaw_restriction {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (a : P.Labels (J + ell)) : sharedDrawLaw ν (sharedRestriction ν a) = sharedLaw ν a := by
  unfold sharedDrawLaw productLaw sharedRestriction sharedLaw
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro g hg
  exact (Finset.prod_subtype (sharedSlots ν g) (fun i => Iff.rfl)
    (fun i => P.mu g (a g (ν.slot i)))).symm

theorem sharedDrawLaw_sum {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (hV : ∀ g, P.V g ≠ 0) : (∑ z : SharedDraw ν, sharedDrawLaw ν z) = 1 := by
  exact productLaw_sum (fun j : SharedIndex ν => P.mu j.1)
    (fun j => group_law_sum P j.1 (hV j.1))

theorem sharedIndex_card_le {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m) :
    Fintype.card (SharedIndex ν) ≤ J * P.count := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∑ g : P.Group, J := Finset.sum_le_sum (fun g hg => by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ (sharedSlots ν g)))
    _ = _ := by simp; ring

def sharedForbidden {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (n n' D : ℕ) (i : SharedIndex ν)
    (r : ∀ j : {j : SharedIndex ν // j ≠ i}, P.Prime j.val.1) : Finset ℕ :=
  n.primeFactors ∪ n'.primeFactors ∪ D.primeFactors ∪
    Finset.univ.image (fun j : {j : SharedIndex ν // j ≠ i} => (r j).val)

theorem sharedForbidden_card {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (n n' D : ℕ) (i : SharedIndex ν)
    (r : ∀ j : {j : SharedIndex ν // j ≠ i}, P.Prime j.val.1) :
    (sharedForbidden ν n n' D i r).card ≤
      n.primeFactors.card + n'.primeFactors.card + D.primeFactors.card +
        Fintype.card (SharedIndex ν) := by
  have h1 := Finset.card_union_le n.primeFactors n'.primeFactors
  have h2 := Finset.card_union_le (n.primeFactors ∪ n'.primeFactors) D.primeFactors
  have h3 := Finset.card_union_le (n.primeFactors ∪ n'.primeFactors ∪ D.primeFactors)
    (Finset.univ.image (fun j : {j : SharedIndex ν // j ≠ i} => (r j).val))
  have hI : (Finset.univ.image (fun j : {j : SharedIndex ν // j ≠ i} => (r j).val)).card ≤
      Fintype.card (SharedIndex ν) :=
    Finset.card_image_le.trans (by
      simpa only [Finset.card_univ] using
        (Fintype.card_subtype_le (fun j : SharedIndex ν => j ≠ i)))
  unfold sharedForbidden
  omega

/-- Harmonic probability of an endpoint overlap, a free/shared coincidence,
or a repeated shared prime, using the actual selected shared coordinates. -/
theorem shared_draw_exclusion_probability (P : Blueprint.Analytic.Geometry)
    (G : Blueprint.Analytic.PrimeGroups) (x : ℝ) (hL : 1 ≤ Blueprint.Analytic.L x)
    (hG : Blueprint.Analytic.Admissible P x G) {J ell m : ℕ}
    (ν : Pattern G.graph J ell m) (n n' D : ℕ) :
    (∑ z : SharedDraw ν,
      if ∃ i : SharedIndex ν, (z i).val ∈ sharedForbidden ν n n' D i (fun j => z j.val)
      then sharedDrawLaw ν z else 0) ≤
        (Fintype.card (SharedIndex ν) : ℝ) *
          (n.primeFactors.card + n'.primeFactors.card + D.primeFactors.card +
            Fintype.card (SharedIndex ν) : ℕ) *
          (P.vmin⁻¹ * Real.exp (-(Blueprint.Analytic.L x ^ P.a))) := by
  have hV (g : Fin G.size) : 0 < G.graph.V g := by
    rw [Blueprint.Analytic.graph_mass]
    exact P.positive.2.2.1.trans_le (hG.2.2.1 g).1
  apply productLaw_any_forbidden (fun j : SharedIndex ν => G.graph.mu j.1)
    (fun j a => inv_nonneg.mpr (mul_nonneg (hV j.1).le (Nat.cast_nonneg a.val)))
    (fun j => group_law_sum G.graph j.1 (hV j.1).ne')
    (fun j a => a.val) (fun j => Subtype.val_injective)
    (sharedForbidden ν n n' D)
    (n.primeFactors.card + n'.primeFactors.card + D.primeFactors.card + Fintype.card (SharedIndex ν))
    (P.vmin⁻¹ * Real.exp (-(Blueprint.Analytic.L x ^ P.a)))
    (mul_nonneg (inv_nonneg.mpr P.positive.2.2.1.le) (Real.exp_pos _).le)
    (fun j a => admissible_group_atom_le P G x hL hG j.1 a)
    (sharedForbidden_card ν n n' D)

end Erdos821.P5Core
