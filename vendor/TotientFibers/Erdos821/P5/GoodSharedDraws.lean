import Erdos821.P5.LabelSplit

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Graph

def GoodSharedDraw {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (n n' D : ℕ) (z : SharedDraw ν) : Prop :=
  ∀ i : SharedIndex ν, (z i).val ∉ sharedForbidden ν n n' D i (fun j => z j.val)

def sharedDrawProduct {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (z : SharedDraw ν) : ℕ := ∏ i : SharedIndex ν, (z i).val

theorem sharedDrawProduct_restriction {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) :
    sharedDrawProduct ν (sharedRestriction ν a) = sharedProduct ν a := by
  unfold sharedDrawProduct sharedRestriction sharedProduct
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro g hg
  exact (Finset.prod_subtype (sharedSlots ν g) (fun i => Iff.rfl)
    (fun i => (a g (ν.slot i)).val)).symm

theorem sharedProduct_assemble {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (z : SharedDraw ν) (r : UnsharedDraw ν) :
    sharedProduct ν (assembleLabels ν z r) = sharedDrawProduct ν z := by
  rw [← sharedDrawProduct_restriction, sharedRestriction_assemble]

theorem goodSharedDraw_iff {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (n n' D : ℕ) (hn : n ≠ 0) (hn' : n' ≠ 0) (hD : D ≠ 0)
    (z : SharedDraw ν) :
    GoodSharedDraw ν n n' D z ↔
      (∀ i : SharedIndex ν, ¬(z i).val ∣ n ∧ ¬(z i).val ∣ n' ∧ ¬(z i).val ∣ D) ∧
        Function.Injective (fun i : SharedIndex ν => (z i).val) := by
  have hprime (i : SharedIndex ν) : (z i).val.Prime := P.prime i.1 _ (z i).property
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · intro i
      have hi := hz i
      simp only [sharedForbidden, Finset.mem_union, not_or] at hi
      exact ⟨fun hd => hi.1.1.1 ((hprime i).mem_primeFactors hd hn),
        fun hd => hi.1.1.2 ((hprime i).mem_primeFactors hd hn'),
        fun hd => hi.1.2 ((hprime i).mem_primeFactors hd hD)⟩
    · intro i j hij
      by_contra hne
      apply hz i
      unfold sharedForbidden
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨⟨j, Ne.symm hne⟩, Finset.mem_univ _, hij.symm⟩
  · rintro ⟨hdiv, hinj⟩ i
    simp only [sharedForbidden, Finset.mem_union, not_or]
    refine ⟨⟨⟨fun hp => (hdiv i).1 (Nat.dvd_of_mem_primeFactors hp),
      fun hp => (hdiv i).2.1 (Nat.dvd_of_mem_primeFactors hp)⟩,
      fun hp => (hdiv i).2.2 (Nat.dvd_of_mem_primeFactors hp)⟩, ?_⟩
    rintro hp
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hp
    exact j.property (hinj heq)

theorem sharedDrawProduct_pos {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (z : SharedDraw ν) : 0 < sharedDrawProduct ν z :=
  Finset.prod_pos (fun i hi => (P.prime i.1 _ (z i).property).pos)

theorem sharedDrawProduct_coprime {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (z : SharedDraw ν) (n : ℕ)
    (hn : ∀ i : SharedIndex ν, ¬(z i).val ∣ n) : Nat.Coprime (sharedDrawProduct ν z) n := by
  apply Nat.Coprime.prod_left
  intro i hi
  exact (P.prime i.1 _ (z i).property).coprime_iff_not_dvd.mpr (hn i)

theorem goodSharedDraw_coprime {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (n n' D : ℕ) (hn : n ≠ 0) (hn' : n' ≠ 0) (hD : D ≠ 0)
    (z : SharedDraw ν) (hz : GoodSharedDraw ν n n' D z) :
    Nat.Coprime (sharedDrawProduct ν z) n ∧ Nat.Coprime (sharedDrawProduct ν z) n' ∧
      Nat.Coprime (sharedDrawProduct ν z) D := by
  have h := ((goodSharedDraw_iff ν n n' D hn hn' hD z).mp hz).1
  exact ⟨sharedDrawProduct_coprime ν z n (fun i => (h i).1),
    sharedDrawProduct_coprime ν z n' (fun i => (h i).2.1),
    sharedDrawProduct_coprime ν z D (fun i => (h i).2.2)⟩

theorem sharedProduct_counts_of_draw_injective (G : Blueprint.Analytic.PrimeGroups)
    {J ell m : ℕ} (ν : Pattern G.graph J ell m) (z : SharedDraw ν)
    (hz : Function.Injective (fun i : SharedIndex ν => (z i).val))
    (r : UnsharedDraw ν) (g : Fin G.size) :
    Blueprint.Analytic.omegaGroup G g (sharedDrawProduct ν z) = (sharedSlots ν g).card := by
  rw [← sharedProduct_assemble ν z r]
  unfold Blueprint.Analytic.omegaGroup
  rw [show G.primes g = G.graph.primes g from rfl, sharedProduct_group_filter]
  apply Finset.card_image_of_injOn
  intro i hi j hj hij
  dsimp only at hij
  rw [assembleLabels_shared ν z r g ⟨i, hi⟩,
    assembleLabels_shared ν z r g ⟨j, hj⟩] at hij
  have heq : (z ⟨g, ⟨i, hi⟩⟩).val = (z ⟨g, ⟨j, hj⟩⟩).val := by
    exact hij
  have h := hz heq
  exact congrArg (fun k : SharedIndex ν => k.2.val) h

theorem damping_sq_good_shared (P : Blueprint.Analytic.Geometry)
    (G : Blueprint.Analytic.PrimeGroups) (J m : ℕ)
    (A : Model P.graph G.graph J m) (ν : Pattern G.graph J P.ell m)
    (z : SharedDraw ν) (r : UnsharedDraw ν) (n n' D : ℕ)
    (hn : n ≠ 0) (hn' : n' ≠ 0) (hD : D ≠ 0)
    (hz : GoodSharedDraw ν n n' D z) :
    A.damping ((sharedDrawProduct ν z * n : ℕ) : ℤ) ^ 2 =
      P.q ^ ((Blueprint.Analytic.omega G n : ℤ) - ∑ g, (ν.t g : ℤ)) := by
  have hgood := (goodSharedDraw_iff ν n n' D hn hn' hD z).mp hz
  exact damping_sq_strip_of_counts P G J m A ν _ n
    (sharedDrawProduct_coprime ν z n (fun i => (hgood.1 i).1))
    (sharedProduct_counts_of_draw_injective G ν z hgood.2 r)

end Erdos821.P5Core
