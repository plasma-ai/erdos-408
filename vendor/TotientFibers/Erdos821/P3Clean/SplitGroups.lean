import Erdos821.P3Clean.Structure

/-! Splitting the fixed small labels from the variable big labels. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups}

abbrev SmallLabels (P : PrimeGroups) (M : ℕ) :=
  (g : P.SmallGroup) → Fin M → P.Prime g.val

def restrictSmall {M : ℕ} (a : P.Labels M) : SmallLabels P M := fun g => a g.val

def joinLabels {M : ℕ} (a : SmallLabels P M) (b : P.BigLabels M) : P.Labels M :=
  fun g => if hg : P.big g = true then b ⟨g, hg⟩ else a ⟨g, by
    cases h : P.big g <;> simp_all⟩

theorem joinLabels_small {M : ℕ} (a : SmallLabels P M) (b : P.BigLabels M)
    (g : P.SmallGroup) : joinLabels a b g.val = a g := by
  simp [joinLabels, g.property]

theorem joinLabels_big {M : ℕ} (a : SmallLabels P M) (b : P.BigLabels M)
    (g : P.BigGroup) : joinLabels a b g.val = b g := by
  simp [joinLabels, g.property]

def splitLabels (P : PrimeGroups) (M : ℕ) : P.Labels M ≃ SmallLabels P M × P.BigLabels M where
  toFun a := (restrictSmall a, P.restrictBig a)
  invFun a := joinLabels a.1 a.2
  left_inv := by
    intro a
    funext g
    simp only [joinLabels, restrictSmall, PrimeGroups.restrictBig]
    split_ifs <;> rfl
  right_inv := by
    intro a
    apply Prod.ext
    · funext g
      exact joinLabels_small a.1 a.2 g
    · funext g
      exact joinLabels_big a.1 a.2 g

theorem prod_group_split {R : Type*} [CommMonoid R] (f : P.Group → R) :
    (∏ g : P.Group, f g) =
      (∏ g : P.SmallGroup, f g.val) * ∏ g : P.BigGroup, f g.val := by
  classical
  have h (g : P.Group) : ¬ P.big g = false ↔ P.big g = true := by
    cases P.big g <;> simp
  let e : {g : P.Group // ¬ P.big g = false} ≃ P.BigGroup :=
    Equiv.subtypeEquivRight h
  have he : (∏ g : {g : P.Group // ¬ P.big g = false}, f g.val) =
      ∏ g : P.BigGroup, f g.val := Fintype.prod_equiv e _ _ (fun _ => rfl)
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun g => P.big g = false) f, he]

def smallPrefixProduct {M : ℕ} (J : ℕ) (hJM : J ≤ M) (a : SmallLabels P M) : ℕ :=
  ∏ g : P.SmallGroup, ∏ j : Fin J, (a g ⟨j.val, lt_of_lt_of_le j.isLt hJM⟩).val

theorem D_split {J ell m : ℕ} (ν : Pattern P J ell m)
    (a : P.Labels (J + ell)) (u : P.Aux J) :
    ν.D a u = smallPrefixProduct J (Nat.le_add_right J ell) (restrictSmall a) *
      ν.DBig (P.restrictBig a) (fun g => u g.val) := by
  unfold Pattern.D Pattern.DBig smallPrefixProduct
  rw [prod_group_split]
  congr 1
  apply Finset.prod_congr rfl
  intro g _
  have hs := ν.small g.val g.property
  simp [hs, Pattern.slot, restrictSmall]

theorem compatible_split {J ell m : ℕ} (ν : Pattern P J ell m)
    (a b : P.Labels (J + ell)) :
    ν.compatible a b ↔
      (∀ g : P.SmallGroup, ∀ j : Fin J, a g.val (ν.slot j) = b g.val (ν.slot j)) ∧
        ν.matchesBig (P.restrictBig a) (P.restrictBig b) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro g j
      apply h g.val (ν.slot j)
      exact ⟨j, rfl, by simp [ν.small g.val g.property]⟩
    · intro g i hi
      exact h g.val i hi
  · rintro ⟨hs, hb⟩ g i hi
    by_cases hg : P.big g = true
    · exact hb ⟨g, hg⟩ i hi
    · have hsmall : P.big g = false := by cases h : P.big g <;> simp_all
      obtain ⟨j, rfl, _⟩ := hi
      exact hs ⟨g, hsmall⟩ j

theorem ban_split {J ell m : ℕ} (ν : Pattern P J ell m)
    (a b : P.Labels (J + ell)) (u : P.Aux J) :
    ν.ban a b u ↔ ∀ g : P.BigGroup, ∀ i ∈ ν.changed g.val,
      ∀ j, u g.val i ≠ a g.val j ∧ u g.val i ≠ b g.val j := by
  constructor
  · intro h g i hi j
    exact h g.val i hi j
  · intro h g i hi j
    by_cases hg : P.big g = true
    · exact h ⟨g, hg⟩ i hi j
    · have hsmall : P.big g = false := by cases hh : P.big g <;> simp_all
      rw [ν.small g hsmall] at hi
      exact False.elim (Finset.notMem_empty i hi)

theorem D_eq_of_compatible {J ell m : ℕ} (ν : Pattern P J ell m)
    (a b : P.Labels (J + ell)) (u : P.Aux J) (h : ν.compatible a b) :
    ν.D a u = ν.D b u := by
  unfold Pattern.D
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ ν.changed g
  · simp only [if_pos hi]
  · simp only [if_neg hi, h g (ν.slot i) ⟨i, rfl, hi⟩]

theorem D_aux_ext {J ell m : ℕ} (ν : Pattern P J ell m)
    (a : P.Labels (J + ell)) (u v : P.Aux J)
    (h : ∀ g i, i ∈ ν.changed g → u g i = v g i) : ν.D a u = ν.D a v := by
  unfold Pattern.D
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ ν.changed g
  · simp only [if_pos hi, h g i hi]
  · simp only [if_neg hi]


end Erdos821.P3Clean
