import Erdos821.P5.SharedCounts

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P5Core
open Blueprint.Graph

def unsharedSlots {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m) (g : P.Group) :
    Finset (Fin (J + ell)) := Finset.univ \ (sharedSlots ν g).image ν.slot

def unsharedProduct {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (a : P.Labels (J + ell)) : ℕ := ∏ g, ∏ i ∈ unsharedSlots ν g, (a g i).val

theorem mem_unsharedSlots {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (g : P.Group) (i : Fin (J + ell)) : i ∈ unsharedSlots ν g ↔ ¬ν.shared g i := by
  simp [unsharedSlots, sharedSlots, Pattern.shared, and_comm]

theorem unshared_slot_count {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (g : P.Group) : (unsharedSlots ν g).card = ν.t g := by
  have hc := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ ((sharedSlots ν g).image ν.slot))
  have hi : ((sharedSlots ν g).image ν.slot).card = (sharedSlots ν g).card :=
    Finset.card_image_of_injective _ (shared_slot_injective ν)
  rw [hi] at hc
  have hs := shared_slot_count ν g
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  change (unsharedSlots ν g).card + (sharedSlots ν g).card = J + ell at hc
  omega

theorem listProduct_shared_unshared {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) :
    listProduct P a = sharedProduct ν a * unsharedProduct ν a := by
  unfold listProduct sharedProduct unsharedProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  have heq : (∏ i ∈ sharedSlots ν g, (a g (ν.slot i)).val) =
      ∏ i ∈ (sharedSlots ν g).image ν.slot, (a g i).val := by
    rw [Finset.prod_image (fun i hi j hj hij => shared_slot_injective ν hij)]
  rw [heq, mul_comm]
  exact (Finset.prod_sdiff (Finset.subset_univ ((sharedSlots ν g).image ν.slot))).symm

/-- Unshared mark divisors survive stripping even when the endpoint contains
an additional occurrence of a shared prime. -/
theorem unsharedProduct_dvd_strip {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) (n : ℕ)
    (hd : listProduct P a ∣ sharedProduct ν a * n) : unsharedProduct ν a ∣ n := by
  rw [listProduct_shared_unshared] at hd
  exact Nat.dvd_of_mul_dvd_mul_left (sharedProduct_pos ν a) hd

theorem unsharedProduct_dvd_physical_strip {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) (n : ℕ)
    (ha : P.physical (J + ell) ((sharedProduct ν a * n : ℕ) : ℤ) a) :
    unsharedProduct ν a ∣ n := by
  apply unsharedProduct_dvd_strip ν a n
  simpa only [Int.toNat_natCast] using
    physical_listProduct_dvd P a (Int.natCast_nonneg _) ha

theorem unshared_label_dvd_strip {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) (n : ℕ)
    (ha : P.physical (J + ell) ((sharedProduct ν a * n : ℕ) : ℤ) a)
    (g : P.Group) (i : Fin (J + ell)) (hi : ¬ν.shared g i) : (a g i).val ∣ n := by
  apply dvd_trans _ (unsharedProduct_dvd_physical_strip ν a n ha)
  apply dvd_trans (Finset.dvd_prod_of_mem _ ((mem_unsharedSlots ν g i).mpr hi))
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ g)

theorem compatible_sharedProduct {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a b : P.Labels (J + ell)) (hab : ν.compatible a b) :
    sharedProduct ν a = sharedProduct ν b := by
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  have his : ν.shared g (ν.slot i) :=
    ⟨i, rfl, (Finset.mem_sdiff.mp hi).2⟩
  rw [hab g (ν.slot i) his]

theorem free_label_dvd_product {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (u : P.Aux J) (g : P.Group) (i : Fin J)
    (hi : i ∈ ν.changed g) : (u g i).val ∣ freeProduct ν u := by
  apply dvd_trans (Finset.dvd_prod_of_mem _ hi)
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ g)

theorem dvd_shift_iff (p D n n' : ℕ) (k : ℤ) (hD : p ∣ D)
    (hshift : (n' : ℤ) = (n : ℤ) + k * (D : ℤ)) : p ∣ n ↔ p ∣ n' := by
  have hstep : (p : ℤ) ∣ k * (D : ℤ) :=
    dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hD) k
  constructor
  · intro hn
    apply Int.natCast_dvd_natCast.mp
    rw [hshift]
    exact dvd_add (Int.natCast_dvd_natCast.mpr hn) hstep
  · intro hn'
    apply Int.natCast_dvd_natCast.mp
    have hd := dvd_sub (Int.natCast_dvd_natCast.mpr hn') hstep
    simpa only [hshift, add_sub_cancel_right] using hd

/-- After free/shared coincidences are removed, every remaining ban violation
lies among multiples of one free prime at both stripped endpoints. -/
theorem ban_violation_free_divisor {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a b : P.Labels (J + ell)) (u : P.Aux J)
    (n n' : ℕ) (k : ℤ) (hab : ν.compatible a b)
    (ha : P.physical (J + ell) ((sharedProduct ν a * n : ℕ) : ℤ) a)
    (hb : P.physical (J + ell) ((sharedProduct ν a * n' : ℕ) : ℤ) b)
    (hshift : (n' : ℤ) = (n : ℤ) + k * (freeProduct ν u : ℤ))
    (hshared : ∀ g i, i ∈ ν.changed g → ∀ j, ν.shared g j →
      u g i ≠ a g j ∧ u g i ≠ b g j)
    (hban : ¬ν.ban a b u) :
    ∃ g i, i ∈ ν.changed g ∧ (u g i).val ∣ freeProduct ν u ∧
      (u g i).val ∣ n ∧ (u g i).val ∣ n' := by
  unfold Pattern.ban at hban
  push Not at hban
  obtain ⟨g, i, hi, j, heq⟩ := hban
  have heq' : u g i = a g j ∨ u g i = b g j := by
    by_cases he : u g i = a g j
    · exact Or.inl he
    · exact Or.inr (heq he)
  have hD := free_label_dvd_product ν u g i hi
  have hs : ¬ν.shared g j := by
    intro hsj
    obtain ⟨hna, hnb⟩ := hshared g i hi j hsj
    rcases heq' with heq | heq
    · exact hna heq
    · exact hnb heq
  have hb' : P.physical (J + ell) ((sharedProduct ν b * n' : ℕ) : ℤ) b := by
    rwa [compatible_sharedProduct ν a b hab] at hb
  have he : (u g i).val ∣ n ∨ (u g i).val ∣ n' := by
    rcases heq' with heq | heq
    · left
      rw [heq]
      exact unshared_label_dvd_strip ν a n ha g j hs
    · right
      rw [heq]
      exact unshared_label_dvd_strip ν b n' hb' g j hs
  have hd := dvd_shift_iff (u g i).val (freeProduct ν u) n n' k hD hshift
  rcases he with hn | hn'
  · exact ⟨g, i, hi, hD, hn, hd.mp hn⟩
  · exact ⟨g, i, hi, hD, hd.mpr hn', hn'⟩

end Erdos821.P5Core
