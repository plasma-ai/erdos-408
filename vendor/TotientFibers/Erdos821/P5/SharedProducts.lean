import Erdos821.P5.EndpointInvariance
import Erdos821.P5.HarmonicLists

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P5Core
open Blueprint.Graph

def sharedSlots {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m) (g : P.Group) :
    Finset (Fin J) := Finset.univ \ ν.changed g

def sharedProduct {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (a : P.Labels (J + ell)) : ℕ :=
  ∏ g, ∏ i ∈ sharedSlots ν g, (a g (ν.slot i)).val

def freeProduct {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (u : P.Aux J) : ℕ := ∏ g, ∏ i ∈ ν.changed g, (u g i).val

def sharedLaw {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (a : P.Labels (J + ell)) : ℝ :=
  ∏ g, ∏ i ∈ sharedSlots ν g, P.mu g (a g (ν.slot i))

theorem shared_slot_count {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (g : P.Group) : J + ell = (sharedSlots ν g).card + ν.t g := by
  have hc : (sharedSlots ν g).card + (ν.changed g).card = J := by
    simpa only [sharedSlots, Finset.card_univ, Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (ν.changed g))
  unfold Pattern.t
  omega

theorem pattern_D_split {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (a : P.Labels (J + ell)) (u : P.Aux J) :
    ν.D a u = sharedProduct ν a * freeProduct ν u := by
  unfold Pattern.D sharedProduct freeProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  have hs : (Finset.univ : Finset (Fin J)).filter (fun i => i ∉ ν.changed g) = sharedSlots ν g := by
    ext i
    simp [sharedSlots]
  calc
    _ = (∏ i ∈ sharedSlots ν g, (a g (ν.slot i)).val) * ∏ i ∈ ν.changed g, (u g i).val := by
      simp only [sharedSlots, Finset.prod_ite, Finset.filter_mem_eq_inter,
        Finset.univ_inter]
      rw [hs]
      exact mul_comm _ _
    _ = _ := rfl

theorem sharedProduct_pos {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (a : P.Labels (J + ell)) : 0 < sharedProduct ν a := by
  apply Finset.prod_pos
  intro g hg
  apply Finset.prod_pos
  intro i hi
  exact (P.prime g _ (a g (ν.slot i)).property).pos

theorem freeProduct_pos {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (u : P.Aux J) : 0 < freeProduct ν u := by
  apply Finset.prod_pos
  intro g hg
  apply Finset.prod_pos
  intro i hi
  exact (P.prime g _ (u g i).property).pos

theorem sharedProduct_primeFactors {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (a : P.Labels (J + ell)) : (sharedProduct ν a).primeFactors ⊆ P.allPrimes := by
  apply primeFactors_prod_supported
  · intro g hg
    exact Finset.prod_pos (fun i hi => (P.prime g _ (a g (ν.slot i)).property).pos)
  · intro g hg
    apply primeFactors_prod_supported
    · intro i hi
      exact (P.prime g _ (a g (ν.slot i)).property).pos
    · intro i hi
      rw [(P.prime g _ (a g (ν.slot i)).property).primeFactors, Finset.singleton_subset_iff]
      exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, (a g (ν.slot i)).property⟩

theorem freeProduct_primeFactors {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (u : P.Aux J) : (freeProduct ν u).primeFactors ⊆ P.allPrimes := by
  apply primeFactors_prod_supported
  · intro g hg
    exact Finset.prod_pos (fun i hi => (P.prime g _ (u g i).property).pos)
  · intro g hg
    apply primeFactors_prod_supported
    · intro i hi
      exact (P.prime g _ (u g i).property).pos
    · intro i hi
      rw [(P.prime g _ (u g i).property).primeFactors, Finset.singleton_subset_iff]
      exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, (u g i).property⟩

theorem shared_slot_injective {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m) :
    Function.Injective ν.slot := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun z : Fin (J + ell) => z.val) hij

theorem sharedProduct_dvd_listProduct {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (a : P.Labels (J + ell)) : sharedProduct ν a ∣ listProduct P a := by
  apply Finset.prod_dvd_prod_of_dvd
  intro g hg
  have heq : (∏ i ∈ sharedSlots ν g, (a g (ν.slot i)).val) =
      ∏ j ∈ (sharedSlots ν g).image ν.slot, (a g j).val := by
    rw [Finset.prod_image (fun i hi j hj hij => shared_slot_injective ν hij)]
  rw [heq]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)

theorem physical_sharedProduct_dvd {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    {n : ℤ} (a : P.Labels (J + ell)) (hn : 0 ≤ n) (ha : P.physical (J + ell) n a) :
    sharedProduct ν a ∣ n.toNat :=
  dvd_trans (sharedProduct_dvd_listProduct ν a) (physical_listProduct_dvd P a hn ha)

theorem endpoint_sharedProduct {G : Blueprint.Analytic.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G.graph J ell m) (a : G.graph.Labels (J + ell))
    (x : ℝ) (E : Blueprint.Analytic.Endpoint) (n : ℕ) :
    Blueprint.Analytic.endpoint G x E (sharedProduct ν a * n) = Blueprint.Analytic.endpoint G x E n :=
  endpoint_mul_supported G x E _ n (sharedProduct_pos ν a).ne' (sharedProduct_primeFactors ν a)

theorem sharedLaw_eq_harmonic {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (a : P.Labels (J + ell)) :
    sharedLaw ν a = (∏ g, P.V g ^ (-((sharedSlots ν g).card : ℤ))) / (sharedProduct ν a : ℝ) := by
  unfold sharedLaw sharedProduct PrimeGroups.mu
  simp only [Nat.cast_prod, mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_const, div_eq_mul_inv, zpow_neg, zpow_natCast, inv_pow]

theorem markMass_shared_split {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (hV : ∀ g, P.V g ≠ 0) :
    P.markMass (J + ell) = (∏ g, P.V g ^ (-((sharedSlots ν g).card : ℤ))) * ν.physicalTargetMass := by
  unfold PrimeGroups.markMass Pattern.physicalTargetMass
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  rw [← zpow_add₀ (hV g)]
  congr 1
  have hc : ((J + ell : ℕ) : ℤ) = ((sharedSlots ν g).card : ℤ) + (ν.t g : ℤ) := by
    exact_mod_cast shared_slot_count ν g
  omega

/-- The harmonic factor from removing the shared product converts its entire
normalization to independent shared draws, leaving one list mass per endpoint. -/
theorem shared_harmonic_normalization {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) (hV : ∀ g, P.V g ≠ 0) :
    P.markMass (J + ell) * ν.physicalTargetMass / (sharedProduct ν a : ℝ) =
      sharedLaw ν a * ν.physicalTargetMass ^ 2 := by
  rw [markMass_shared_split ν hV, sharedLaw_eq_harmonic]
  ring

end Erdos821.P5Core
