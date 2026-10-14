import Erdos821.P5.GroupOmega

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P5Core

theorem prime_dvd_sharedProduct_iff {P : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern P J ell m) (a : P.Labels (J + ell))
    {p : ℕ} (hp : p.Prime) :
    p ∣ sharedProduct ν a ↔ ∃ g i, i ∈ sharedSlots ν g ∧ p = (a g (ν.slot i)).val := by
  unfold sharedProduct
  rw [hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨g, hg, hd⟩
    obtain ⟨i, hi, hpi⟩ := hp.prime.dvd_finsetProd_iff _ |>.mp hd
    refine ⟨g, i, hi, ?_⟩
    exact (Nat.dvd_prime (P.prime g _ (a g (ν.slot i)).property)).mp hpi |>.resolve_left hp.ne_one
  · rintro ⟨g, i, hi, rfl⟩
    exact ⟨g, Finset.mem_univ _, Finset.dvd_prod_of_mem _ hi⟩

/-- Group disjointness identifies every divisor of the shared product with
one of that group's selected shared coordinates, even for repeated labels. -/
theorem sharedProduct_group_filter {P : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern P J ell m) (a : P.Labels (J + ell)) (g : P.Group) :
    (P.primes g).filter (fun p => p ∣ sharedProduct ν a) =
      (sharedSlots ν g).image (fun i => (a g (ν.slot i)).val) := by
  ext p
  constructor
  · intro hp
    obtain ⟨h, i, hi, heq⟩ := (prime_dvd_sharedProduct_iff ν a
      (P.prime g p (Finset.mem_filter.mp hp).1)).mp (Finset.mem_filter.mp hp).2
    have hgh : g = h := by
      by_contra hne
      apply Finset.disjoint_left.mp (P.disjoint g h hne) (Finset.mem_filter.mp hp).1
      simpa only [heq] using (a h (ν.slot i)).property
    subst h
    exact Finset.mem_image.mpr ⟨i, hi, heq.symm⟩
  · intro hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨(a g (ν.slot i)).property,
      (prime_dvd_sharedProduct_iff ν a (P.prime g _ (a g (ν.slot i)).property)).mpr
        ⟨g, i, hi, rfl⟩⟩

theorem omegaGroup_sharedProduct (G : Blueprint.Analytic.PrimeGroups) {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G.graph J ell m) (a : G.graph.Labels (J + ell))
    (ha : ∀ g, Function.Injective (a g)) (g : Fin G.size) :
    Blueprint.Analytic.omegaGroup G g (sharedProduct ν a) = (sharedSlots ν g).card := by
  unfold Blueprint.Analytic.omegaGroup
  rw [show G.primes g = G.graph.primes g from rfl, sharedProduct_group_filter]
  apply Finset.card_image_of_injective
  intro i j hij
  exact shared_slot_injective ν (ha g (Subtype.ext hij))

theorem sharedProduct_coprime_iff {P : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern P J ell m) (a : P.Labels (J + ell)) (n : ℕ) :
    Nat.Coprime (sharedProduct ν a) n ↔
      ∀ g i, i ∈ sharedSlots ν g → ¬(a g (ν.slot i)).val ∣ n := by
  constructor
  · intro h g i hi hd
    have hp := P.prime g _ (a g (ν.slot i)).property
    have hD := (prime_dvd_sharedProduct_iff ν a hp).mpr ⟨g, i, hi, rfl⟩
    have hdiv := Nat.dvd_gcd hD hd
    rw [h.gcd_eq_one] at hdiv
    exact hp.not_dvd_one hdiv
  · intro h
    by_contra hc
    obtain ⟨p, hp, hD, hn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    obtain ⟨g, i, hi, rfl⟩ := (prime_dvd_sharedProduct_iff ν a hp).mp hD
    exact h g i hi hn

theorem damping_sq_strip (P : Blueprint.Analytic.Geometry) (G : Blueprint.Analytic.PrimeGroups)
    (J m : ℕ) (A : Blueprint.Graph.Model P.graph G.graph J m)
    (ν : Blueprint.Graph.Pattern G.graph J P.ell m) (a : G.graph.Labels (J + P.ell))
    (ha : ∀ g, Function.Injective (a g)) (n : ℕ)
    (hn : ∀ g i, i ∈ sharedSlots ν g → ¬(a g (ν.slot i)).val ∣ n) :
    A.damping ((sharedProduct ν a * n : ℕ) : ℤ) ^ 2 =
      P.q ^ ((Blueprint.Analytic.omega G n : ℤ) - ∑ g, (ν.t g : ℤ)) := by
  apply damping_sq_strip_of_counts P G J m A ν
  · exact (sharedProduct_coprime_iff ν a n).mpr hn
  · exact omegaGroup_sharedProduct G ν a ha

/-- The correction counts distinct primes, rather than their valuations. -/
def groupOverlap (G : Blueprint.Analytic.PrimeGroups) (g : Fin G.size) (D n : ℕ) : ℕ :=
  ((G.primes g).filter (fun p => p ∣ D ∧ p ∣ n)).card

def primeOverlap (G : Blueprint.Analytic.PrimeGroups) (D n : ℕ) : ℕ :=
  ∑ g, groupOverlap G g D n

theorem omegaGroup_mul_overlap (G : Blueprint.Analytic.PrimeGroups) (g : Fin G.size)
    (D n : ℕ) :
    Blueprint.Analytic.omegaGroup G g (D * n) + groupOverlap G g D n =
      Blueprint.Analytic.omegaGroup G g D + Blueprint.Analytic.omegaGroup G g n := by
  have hu : (G.primes g).filter (fun p => p ∣ D * n) =
      ((G.primes g).filter (fun p => p ∣ D)) ∪ ((G.primes g).filter (fun p => p ∣ n)) := by
    ext p
    by_cases hp : p ∈ G.primes g
    · simp only [Finset.mem_filter, hp, true_and, Finset.mem_union]
      exact (G.prime g p hp).dvd_mul
    · simp [hp]
  have hi : ((G.primes g).filter (fun p => p ∣ D)) ∩
      ((G.primes g).filter (fun p => p ∣ n)) =
      (G.primes g).filter (fun p => p ∣ D ∧ p ∣ n) := by
    ext p
    simp only [Finset.mem_inter, Finset.mem_filter]
    tauto
  unfold Blueprint.Analytic.omegaGroup groupOverlap
  rw [hu, ← hi]
  exact Finset.card_union_add_card_inter _ _

theorem omega_mul_overlap (G : Blueprint.Analytic.PrimeGroups) (D n : ℕ) :
    Blueprint.Analytic.omega G (D * n) + primeOverlap G D n =
      Blueprint.Analytic.omega G D + Blueprint.Analytic.omega G n := by
  unfold Blueprint.Analytic.omega primeOverlap
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun g hg => omegaGroup_mul_overlap G g D n)

theorem groupOverlap_sharedProduct (G : Blueprint.Analytic.PrimeGroups) {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G.graph J ell m) (a : G.graph.Labels (J + ell))
    (ha : ∀ g, Function.Injective (a g)) (g : Fin G.size) (n : ℕ) :
    groupOverlap G g (sharedProduct ν a) n =
      ((sharedSlots ν g).filter (fun i => (a g (ν.slot i)).val ∣ n)).card := by
  have hf : (G.primes g).filter (fun p => p ∣ sharedProduct ν a ∧ p ∣ n) =
      ((G.graph.primes g).filter (fun p => p ∣ sharedProduct ν a)).filter (fun p => p ∣ n) := by
    ext p
    simp only [Finset.mem_filter]
    tauto
  unfold groupOverlap
  rw [hf, sharedProduct_group_filter, Finset.filter_image]
  apply Finset.card_image_of_injective
  intro i j hij
  exact shared_slot_injective ν (ha g (Subtype.ext hij))

/-- Exact signed-power identity, including the shared endpoint overlaps that
are subsequently discarded in the analytic lift. -/
theorem damping_sq_shared_overlap (P : Blueprint.Analytic.Geometry)
    (G : Blueprint.Analytic.PrimeGroups) (J m : ℕ)
    (A : Blueprint.Graph.Model P.graph G.graph J m)
    (ν : Blueprint.Graph.Pattern G.graph J P.ell m) (a : G.graph.Labels (J + P.ell))
    (ha : ∀ g, Function.Injective (a g)) (n : ℕ) :
    A.damping ((sharedProduct ν a * n : ℕ) : ℤ) ^ 2 =
      P.q ^ ((Blueprint.Analytic.omega G n : ℤ) - ∑ g, (ν.t g : ℤ) -
        (primeOverlap G (sharedProduct ν a) n : ℤ)) := by
  have hN : Blueprint.Analytic.omega G (sharedProduct ν a) + ∑ g, ν.t g =
      (J + P.ell) * G.size := by
    unfold Blueprint.Analytic.omega
    simp_rw [omegaGroup_sharedProduct G ν a ha]
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ g : Fin G.size, (J + P.ell) :=
        Finset.sum_congr rfl (fun g hg => (shared_slot_count ν g).symm)
      _ = _ := by simp; ring
  have hNZ : (Blueprint.Analytic.omega G (sharedProduct ν a) : ℤ) +
      ∑ g, (ν.t g : ℤ) = (((J + P.ell) * G.size : ℕ) : ℤ) := by
    exact_mod_cast hN
  have hMZ : (Blueprint.Analytic.omega G (sharedProduct ν a * n) : ℤ) +
      (primeOverlap G (sharedProduct ν a) n : ℤ) =
      (Blueprint.Analytic.omega G (sharedProduct ν a) : ℤ) +
        (Blueprint.Analytic.omega G n : ℤ) := by
    exact_mod_cast omega_mul_overlap G (sharedProduct ν a) n
  rw [damping_sq_int]
  congr 1
  push_cast at hNZ ⊢
  omega

end Erdos821.P5Core
