import Erdos821.P5.SharedProbability

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Graph

abbrev FreeIndex {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m) :=
  (g : P.Group) × {i : Fin J // i ∈ ν.changed g}

abbrev FreeDraw {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m) :=
  (j : FreeIndex ν) → P.Prime j.1

def freeDrawLaw {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (u : FreeDraw ν) : ℝ := productLaw (fun j : FreeIndex ν => P.mu j.1) u

def freeRestriction {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (u : P.Aux J) : FreeDraw ν := fun j => u j.1 j.2.val

def assembleAux {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (u : FreeDraw ν) (z : SharedDraw ν) : P.Aux J := fun g i =>
  if hi : i ∈ ν.changed g then u ⟨g, ⟨i, hi⟩⟩
  else z ⟨g, ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩⟩⟩

theorem assembleAux_free {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (u : FreeDraw ν) (z : SharedDraw ν)
    (g : P.Group) (i : {i : Fin J // i ∈ ν.changed g}) :
    assembleAux ν u z g i.val = u ⟨g, i⟩ := by
  rw [assembleAux, dif_pos i.property]

theorem assembleAux_unused {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (u : FreeDraw ν) (z : SharedDraw ν)
    (g : P.Group) (i : {i : Fin J // i ∈ sharedSlots ν g}) :
    assembleAux ν u z g i.val = z ⟨g, i⟩ := by
  rw [assembleAux, dif_neg (Finset.mem_sdiff.mp i.property).2]

def auxSplit {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m) :
    P.Aux J ≃ FreeDraw ν × SharedDraw ν where
  toFun u := (freeRestriction ν u, fun j => u j.1 j.2.val)
  invFun uz := assembleAux ν uz.1 uz.2
  left_inv u := by
    funext g i
    dsimp [assembleAux, freeRestriction]
    split_ifs <;> rfl
  right_inv uz := by
    apply Prod.ext
    · funext j
      exact assembleAux_free ν uz.1 uz.2 j.1 j.2
    · funext j
      exact assembleAux_unused ν uz.1 uz.2 j.1 j.2

theorem freeDrawLaw_sum {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (hV : ∀ g, P.V g ≠ 0) :
    (∑ u : FreeDraw ν, freeDrawLaw ν u) = 1 :=
  productLaw_sum _ (fun j => group_law_sum P j.1 (hV j.1))

theorem freeIndex_card_le {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) : Fintype.card (FreeIndex ν) ≤ m * P.count := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∑ g : P.Group, m := Finset.sum_le_sum (fun g hg => ν.bound g)
    _ = _ := by simp; ring

def freeDrawProduct {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (u : FreeDraw ν) : ℕ := ∏ i : FreeIndex ν, (u i).val

theorem freeDrawProduct_restriction {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (u : P.Aux J) :
    freeDrawProduct ν (freeRestriction ν u) = freeProduct ν u := by
  unfold freeDrawProduct freeRestriction freeProduct
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro g hg
  exact (Finset.prod_subtype (ν.changed g) (fun i => Iff.rfl)
    (fun i => (u g i).val)).symm

theorem freeProduct_assembleAux {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (u : FreeDraw ν) (z : SharedDraw ν) :
    freeProduct ν (assembleAux ν u z) = freeDrawProduct ν u := by
  rw [← freeDrawProduct_restriction]
  congr 1
  funext j
  exact assembleAux_free ν u z j.1 j.2

theorem auxMass_assemble {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (u : FreeDraw ν) (z : SharedDraw ν) :
    ν.auxMass (assembleAux ν u z) = freeDrawLaw ν u * sharedDrawLaw ν z := by
  unfold Pattern.auxMass freeDrawLaw sharedDrawLaw productLaw
  rw [Fintype.prod_sigma, Fintype.prod_sigma, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  have hc : (∏ i ∈ ν.changed g, P.mu g (assembleAux ν u z g i)) =
      ∏ i : {i : Fin J // i ∈ ν.changed g}, P.mu g (u ⟨g, i⟩) := by
    rw [Finset.prod_subtype (ν.changed g) (fun i => Iff.rfl)
      (fun i => P.mu g (assembleAux ν u z g i))]
    apply Finset.prod_congr rfl
    intro i hi
    rw [assembleAux_free]
  have hs : (∏ i ∈ sharedSlots ν g, P.mu g (assembleAux ν u z g i)) =
      ∏ i : {i : Fin J // i ∈ sharedSlots ν g}, P.mu g (z ⟨g, i⟩) := by
    rw [Finset.prod_subtype (sharedSlots ν g) (fun i => Iff.rfl)
      (fun i => P.mu g (assembleAux ν u z g i))]
    apply Finset.prod_congr rfl
    intro i hi
    rw [assembleAux_unused]
  rw [← hc, ← hs, mul_comm]
  exact (Finset.prod_sdiff (Finset.subset_univ (ν.changed g))).symm

/-- Every unused auxiliary label integrates to one. Only the designated
free labels and their harmonic laws remain in the stripped expectation. -/
theorem sum_auxMass_free {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (hV : ∀ g, P.V g ≠ 0) (f : FreeDraw ν → ℂ) :
    (∑ u : P.Aux J, (ν.auxMass u : ℂ) * f (freeRestriction ν u)) =
      ∑ u : FreeDraw ν, (freeDrawLaw ν u : ℂ) * f u := by
  rw [← (auxSplit ν).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u hu
  change (∑ z : SharedDraw ν, (ν.auxMass (assembleAux ν u z) : ℂ) *
    f (freeRestriction ν (assembleAux ν u z))) = _
  have heq (z : SharedDraw ν) : freeRestriction ν (assembleAux ν u z) = u := by
    funext j
    exact assembleAux_free ν u z j.1 j.2
  simp_rw [heq, auxMass_assemble, Complex.ofReal_mul]
  calc
    _ = (∑ z : SharedDraw ν, (sharedDrawLaw ν z : ℂ)) * ((freeDrawLaw ν u : ℂ) * f u) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ = _ := by
      rw [← Complex.ofReal_sum, sharedDrawLaw_sum ν hV, Complex.ofReal_one, one_mul]

theorem coefficient_assembleAux_unused_ext {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a b : P.BigLabels (J + ell))
    (u : FreeDraw ν) (z z' : SharedDraw ν) :
    ν.coefficient a b (fun g => assembleAux ν u z g.val) =
      ν.coefficient a b (fun g => assembleAux ν u z' g.val) := by
  apply ν.coefficient_aux_ext
  intro g i hi
  rw [assembleAux_free ν u z g.val ⟨i, hi⟩, assembleAux_free ν u z' g.val ⟨i, hi⟩]

theorem sum_auxMass_coefficient {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (hV : ∀ g, P.V g ≠ 0)
    (a b : P.BigLabels (J + ell)) (z₀ : SharedDraw ν) :
    (∑ u : P.Aux J, (ν.auxMass u : ℂ) * ν.coefficient a b (fun g => u g.val)) =
      ∑ u : FreeDraw ν, (freeDrawLaw ν u : ℂ) *
        ν.coefficient a b (fun g => assembleAux ν u z₀ g.val) := by
  have hc (u : P.Aux J) : ν.coefficient a b (fun g => u g.val) =
      ν.coefficient a b (fun g => assembleAux ν (freeRestriction ν u) z₀ g.val) := by
    apply ν.coefficient_aux_ext
    intro g i hi
    rw [assembleAux_free ν (freeRestriction ν u) z₀ g.val ⟨i, hi⟩]
    rfl
  calc
    _ = ∑ u : P.Aux J, (ν.auxMass u : ℂ) *
        ν.coefficient a b (fun g => assembleAux ν (freeRestriction ν u) z₀ g.val) :=
      Finset.sum_congr rfl (fun u hu => congrArg (fun c => (ν.auxMass u : ℂ) * c) (hc u))
    _ = _ := sum_auxMass_free ν hV
      (fun u => ν.coefficient a b (fun g => assembleAux ν u z₀ g.val))

end Erdos821.P5Core
