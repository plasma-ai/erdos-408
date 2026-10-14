import Erdos821.Leaves.Arith

/-! Unshared active entries cannot be factors of the dilation step. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups} {J ell m : ℕ}

theorem prime_group_eq {g h : P.Group} (p : P.Prime g) (q : P.Prime h) (he : p.val = q.val) : g = h := by
  by_contra hgh
  exact Finset.disjoint_left.mp (P.disjoint g h hgh) p.property (he.symm ▸ q.property)

theorem source_label_dvd_D_iff (ν : Pattern P J ell m) (a b : P.Labels (J + ell)) (u : P.Aux J)
    (hinj : ∀ g, Function.Injective (a g)) (hban : ν.ban a b u) (g : P.Group) (i : Fin (J + ell)) :
    (a g i).val ∣ ν.D a u ↔ ν.shared g i := by
  constructor
  · intro hd
    have hp := P.prime g (a g i).val (a g i).property
    unfold Pattern.D at hd
    obtain ⟨h, _, hd⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
    obtain ⟨j, _, hd⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
    by_cases hj : j ∈ ν.changed h
    · rw [ite_eq_left hj] at hd
      have he := (Nat.prime_dvd_prime_iff_eq hp (P.prime h _ (u h j).property)).mp hd
      have hg := prime_group_eq (a g i) (u h j) he
      subst h
      exact False.elim ((hban g j hj i).1 (Subtype.ext he.symm))
    · rw [ite_eq_right hj] at hd
      have he := (Nat.prime_dvd_prime_iff_eq hp (P.prime h _ (a h (ν.slot j)).property)).mp hd
      have hg := prime_group_eq (a g i) (a h (ν.slot j)) he
      subst h
      exact ⟨j, (hinj g (Subtype.ext he)).symm, hj⟩
  · rintro ⟨j, hj, hc⟩
    rw [← hj]
    have h1 := Finset.dvd_prod_of_mem
      (fun j : Fin J => if j ∈ ν.changed g then (u g j).val else (a g (ν.slot j)).val)
      (Finset.mem_univ j)
    have h2 := Finset.dvd_prod_of_mem
      (fun h : P.Group => ∏ j : Fin J,
        if j ∈ ν.changed h then (u h j).val else (a h (ν.slot j)).val)
      (Finset.mem_univ g)
    simpa only [ite_eq_right hc, Pattern.D] using h1.trans h2

theorem compatible_D_eq (ν : Pattern P J ell m) (a b : P.Labels (J + ell)) (u : P.Aux J)
    (hc : ν.compatible a b) : ν.D a u = ν.D b u := by
  unfold Pattern.D
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j ∈ ν.changed g
  · simp only [ite_eq_left hj]
  · simp only [ite_eq_right hj]
    exact congrArg Subtype.val (hc g (ν.slot j) ⟨j, rfl, hj⟩)

theorem target_label_dvd_D_iff (ν : Pattern P J ell m) (a b : P.Labels (J + ell)) (u : P.Aux J)
    (hinj : ∀ g, Function.Injective (b g)) (hcompat : ν.compatible a b)
    (hban : ν.ban a b u) (g : P.Group) (i : Fin (J + ell)) :
    (b g i).val ∣ ν.D a u ↔ ν.shared g i := by
  rw [compatible_D_eq ν a b u hcompat]
  apply source_label_dvd_D_iff ν b a u hinj
  intro h j hj i
  exact ⟨(hban h j hj i).2, (hban h j hj i).1⟩

/-- A repeated active prime across one physical step must occupy the same
canonical shared slot. This prevents an immediate new-store promotion. -/
theorem active_both_shared (ν : Pattern P J ell m) (a b : P.Labels (J + ell)) (u : P.Aux J)
    (hinjA : ∀ g, Function.Injective (a g)) (hinjB : ∀ g, Function.Injective (b g))
    (hcompat : ν.compatible a b) (hban : ν.ban a b u)
    (g : P.Group) (i j : Fin (J + ell)) (he : a g i = b g j)
    (n k : ℤ) (hn : ((a g i).val : ℤ) ∣ n)
    (hn' : ((a g i).val : ℤ) ∣ n + k * (ν.D a u : ℤ))
    (hk : ¬ ((a g i).val : ℤ) ∣ k) :
    ν.shared g i ∧ ν.shared g j ∧ i = j := by
  have hp := P.prime g (a g i).val (a g i).property
  have hdZ := active_both_divides_step (a g i).val n k (ν.D a u) hp hn hn' hk
  have hd : (a g i).val ∣ ν.D a u := by exact_mod_cast hdZ
  have hshared := (source_label_dvd_D_iff ν a b u hinjA hban g i).mp hd
  have hij : i = j := hinjB g ((hcompat g i hshared).symm.trans he)
  exact ⟨hshared, hij ▸ hshared, hij⟩


end Erdos821.S2Core
