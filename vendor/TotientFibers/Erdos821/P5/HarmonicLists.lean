import Erdos821.Blueprint.Adapters

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Graph

/-- All slots, including small groups, enter the physical list product. -/
def listProduct (P : PrimeGroups) {M : ℕ} (a : P.Labels M) : ℕ :=
  ∏ g, ∏ i, (a g i).val

def listLaw (P : PrimeGroups) {M : ℕ} (a : P.Labels M) : ℝ :=
  ∏ g, ∏ i, P.mu g (a g i)

theorem listProduct_pos (P : PrimeGroups) {M : ℕ} (a : P.Labels M) :
    0 < listProduct P a := by
  apply Finset.prod_pos
  intro g hg
  apply Finset.prod_pos
  intro i hi
  exact (P.prime g _ (a g i).property).pos

theorem list_values_injective (P : PrimeGroups) {M : ℕ} (a : P.Labels M)
    (ha : ∀ g, Function.Injective (a g)) :
    Function.Injective (fun j : P.Group × Fin M => (a j.1 j.2).val) := by
  rintro ⟨g, i⟩ ⟨h, j⟩ heq
  have hgh : g = h := by
    by_contra hne
    apply Finset.disjoint_left.mp (P.disjoint g h hne) (a g i).property
    simpa only [heq] using (a h j).property
  subst h
  have hij : i = j := ha g (Subtype.ext heq)
  subst j
  rfl

theorem listProduct_eq_image (P : PrimeGroups) {M : ℕ} (a : P.Labels M)
    (ha : ∀ g, Function.Injective (a g)) :
    listProduct P a = ∏ p ∈ Finset.univ.image (fun j : P.Group × Fin M => (a j.1 j.2).val), p := by
  rw [Finset.prod_image (fun u hu v hv h => list_values_injective P a ha h)]
  exact (Fintype.prod_prod_type (fun j : P.Group × Fin M => (a j.1 j.2).val)).symm

theorem listProduct_primeFactors (P : PrimeGroups) {M : ℕ} (a : P.Labels M)
    (ha : ∀ g, Function.Injective (a g)) :
    (listProduct P a).primeFactors ⊆ P.allPrimes := by
  rw [listProduct_eq_image P a ha, Nat.primeFactors_prod]
  · intro p hp
    obtain ⟨⟨g, i⟩, hi, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, (a g i).property⟩
  · intro p hp
    obtain ⟨⟨g, i⟩, hi, rfl⟩ := Finset.mem_image.mp hp
    exact P.prime g _ (a g i).property

/-- Distinct labels in disjoint prime groups form a square-free divisor of the root. -/
theorem listProduct_dvd (P : PrimeGroups) {M n : ℕ} (a : P.Labels M)
    (ha : ∀ g, Function.Injective (a g)) (hd : ∀ g i, (a g i).val ∣ n) :
    listProduct P a ∣ n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [listProduct_eq_image P a ha]
  apply dvd_trans (Finset.prod_dvd_prod_of_subset _ n.primeFactors id ?_)
    (Nat.prod_primeFactors_dvd n)
  intro p hp
  obtain ⟨⟨g, i⟩, hi, rfl⟩ := Finset.mem_image.mp hp
  exact Nat.mem_primeFactors.mpr ⟨P.prime g _ (a g i).property, hd g i, hn⟩

theorem physical_listProduct_dvd (P : PrimeGroups) {M : ℕ} {n : ℤ} (a : P.Labels M)
    (hn : 0 ≤ n) (ha : P.physical M n a) : listProduct P a ∣ n.toNat := by
  apply listProduct_dvd P a (fun g => (ha g).1)
  intro g i
  apply Int.natCast_dvd_natCast.mp
  simpa only [Int.toNat_of_nonneg hn] using (ha g).2 i

theorem markMass_nonneg (P : PrimeGroups) (M : ℕ) (hV : ∀ g, 0 < P.V g) :
    0 ≤ P.markMass M := by
  unfold PrimeGroups.markMass
  exact Finset.prod_nonneg (fun g hg => zpow_nonneg (hV g).le _)

theorem listLaw_nonneg (P : PrimeGroups) {M : ℕ} (a : P.Labels M)
    (hV : ∀ g, 0 ≤ P.V g) : 0 ≤ listLaw P a := by
  apply Finset.prod_nonneg
  intro g hg
  apply Finset.prod_nonneg
  intro i hi
  exact inv_nonneg.mpr (mul_nonneg (hV g) (Nat.cast_nonneg _))

theorem group_law_sum (P : PrimeGroups) (g : P.Group) (hV : P.V g ≠ 0) :
    (∑ p : P.Prime g, P.mu g p) = 1 := by
  simp only [PrimeGroups.mu, mul_inv_rev]
  rw [← Finset.sum_mul]
  have hs : (∑ p : P.Prime g, (p.val : ℝ)⁻¹) = P.V g := by
    exact Finset.sum_attach (P.primes g) (fun p : ℕ => (p : ℝ)⁻¹)
  rw [hs, mul_inv_cancel₀ hV]

theorem listLaw_sum (P : PrimeGroups) (M : ℕ) (hV : ∀ g, P.V g ≠ 0) :
    (∑ a : P.Labels M, listLaw P a) = 1 := by
  unfold listLaw
  change (∑ a : ∀ g : P.Group, Fin M → P.Prime g, ∏ g, ∏ i, P.mu g (a g i)) = 1
  rw [← Fintype.prod_sum
    (fun g : P.Group => fun a : Fin M → P.Prime g => ∏ i, P.mu g (a i))]
  have hs (g : P.Group) : (∑ a : Fin M → P.Prime g, ∏ i, P.mu g (a i)) = 1 := by
    rw [← Fintype.sum_pow, group_law_sum P g (hV g), one_pow]
  simp_rw [hs]
  exact Finset.prod_const_one

theorem listLaw_eq_harmonic (P : PrimeGroups) {M : ℕ} (a : P.Labels M) :
    listLaw P a = P.markMass M / (listProduct P a : ℝ) := by
  unfold listLaw listProduct PrimeGroups.markMass PrimeGroups.mu
  simp only [Nat.cast_prod, mul_inv, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [div_eq_mul_inv, zpow_neg, zpow_natCast, Finset.prod_inv_distrib]

/-- Restricting the full independent harmonic law to injective lists costs at most one. -/
theorem physical_list_harmonic_mass (P : PrimeGroups) (M : ℕ)
    (hV : ∀ g, 0 < P.V g) :
    (∑ a ∈ (Finset.univ : Finset (P.Labels M)).filter (fun a => ∀ g, Function.Injective (a g)),
      P.markMass M / (listProduct P a : ℝ)) ≤ 1 := by
  simp_rw [← listLaw_eq_harmonic]
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun a ha hnot => listLaw_nonneg P a (fun g => (hV g).le))).trans
  exact (listLaw_sum P M (fun g => (hV g).ne')).le

end Erdos821.P5Core
