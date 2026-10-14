import Erdos821.P3Clean.BigRefresh
import Erdos821.P3Clean.IdealMultiplier

/-! Auxiliary-coordinate marginals and a uniform collision union bound. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem productMass_coordinate_sum {I : Type*} [Fintype I] [DecidableEq I]
    {alpha : I → Type*} [∀ i, Fintype (alpha i)] (mu : ∀ i, alpha i → ℝ)
    (hmu : ∀ i, (∑ x, mu i x) = 1) (i : I) (f : alpha i → ℝ) :
    (∑ a : ∀ j, alpha j, productMass mu a * f (a i)) = ∑ x, mu i x * f x := by
  let w (j : I) (x : alpha j) : ℝ := mu j x * if h : j = i then f (h ▸ x) else 1
  have hp (a : ∀ j, alpha j) : productMass mu a * f (a i) = ∏ j, w j (a j) := by
    simp only [w, Finset.prod_mul_distrib]
    congr 1
    symm
    calc
      _ = (if h : i = i then f (h ▸ a i) else 1) := by
        apply Finset.prod_eq_single i
        · intro j _ hji
          simp only [dif_neg hji]
        · intro hi
          exact False.elim (hi (Finset.mem_univ i))
      _ = _ := by simp
  simp only [hp]
  rw [← Fintype.prod_sum w]
  calc
    _ = ∑ x, w i x := by
      apply Finset.prod_eq_single i
      · intro j _ hji
        simp only [w, dif_neg hji, mul_one, hmu]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    _ = _ := by simp [w]

theorem bigAuxMass_marginal {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (hV : ∀ g : P.BigGroup, P.V g.val ≠ 0) (g : P.BigGroup) (i : Fin J)
    (q : P.Prime g.val) :
    (∑ u : P.BigAux J, ν.bigAuxMass u * (if u g i = q then 1 else 0)) = P.mu g.val q := by
  have h := productMass_coordinate_sum
    (fun z : P.BigGroup × Fin J => P.mu z.1.val)
    (fun z => mu_sum z.1.val (hV z.1)) (g, i) (fun p => if p = q then 1 else 0)
  have hs := Equiv.sum_comp (flattenBigLabels P J)
    (fun u => productMass (fun z : P.BigGroup × Fin J => P.mu z.1.val) u *
      (if u (g, i) = q then 1 else 0))
  have hh := hs.trans h
  simp only [productMass, Fintype.prod_prod_type, flattenBigLabels, Equiv.coe_fn_mk] at hh
  change (∑ u : P.BigAux J, ν.bigAuxMass u * (if u g i = q then 1 else 0)) =
    (∑ x : P.Prime g.val, P.mu g.val x * (if x = q then 1 else 0)) at hh
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hh

theorem bigBan_indicator_le {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (a b : P.BigLabels (J + ell)) (u : P.BigAux J) :
    (if bigBan ν a b u then (0 : ℝ) else 1) ≤
      ∑ g : P.BigGroup, ∑ i : Fin J, ∑ j : Fin (J + ell),
        ((if u g i = a g j then (1 : ℝ) else 0) + (if u g i = b g j then 1 else 0)) := by
  have hn (g : P.BigGroup) (i : Fin J) (j : Fin (J + ell)) :
      0 ≤ (if u g i = a g j then (1 : ℝ) else 0) + (if u g i = b g j then 1 else 0) := by
    positivity
  by_cases h : bigBan ν a b u
  · simp only [if_pos h]
    exact Finset.sum_nonneg (fun g _ => Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => hn g i j)))
  · simp only [if_neg h]
    unfold bigBan at h
    push_neg at h
    obtain ⟨g, i, _, j, hbad⟩ := h
    have hs : 1 ≤ (if u g i = a g j then (1 : ℝ) else 0) +
        (if u g i = b g j then 1 else 0) := by
      by_cases ha : u g i = a g j
      · simp only [if_pos ha]
        have hz : 0 ≤ (if u g i = b g j then (1 : ℝ) else 0) := by positivity
        linarith
      · simp only [if_neg ha, if_pos (hbad ha)]; norm_num
    exact hs.trans ((Finset.single_le_sum (fun z _ => hn g i z) (Finset.mem_univ j)).trans
      ((Finset.single_le_sum (fun z _ => Finset.sum_nonneg (fun t _ => hn g z t))
        (Finset.mem_univ i)).trans
        (Finset.single_le_sum (fun z _ => Finset.sum_nonneg (fun t _ =>
          Finset.sum_nonneg (fun s _ => hn z t s))) (Finset.mem_univ g))))

theorem bigAuxMass_ban_probability {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (hV : ∀ g : P.BigGroup, P.V g.val ≠ 0) (atom : ℝ)
    (hatom : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, P.mu g.val p ≤ atom)
    (a b : P.BigLabels (J + ell)) :
    (∑ u : P.BigAux J, ν.bigAuxMass u * (if bigBan ν a b u then 0 else 1)) ≤
      (Fintype.card P.BigGroup : ℝ) * J * (J + ell) * (2 * atom) := by
  have hn (u : P.BigAux J) : 0 ≤ ν.bigAuxMass u := by
    exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => (mu_pos g.val (u g i)).le))
  calc
    _ ≤ ∑ u : P.BigAux J, ν.bigAuxMass u *
        ∑ g : P.BigGroup, ∑ i : Fin J, ∑ j : Fin (J + ell),
          ((if u g i = a g j then (1 : ℝ) else 0) + (if u g i = b g j then 1 else 0)) :=
      Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (bigBan_indicator_le ν a b u)
        (hn u))
    _ = ∑ g : P.BigGroup, ∑ i : Fin J, ∑ j : Fin (J + ell),
        (P.mu g.val (a g j) + P.mu g.val (b g j)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp only [mul_add, Finset.sum_add_distrib]
      rw [bigAuxMass_marginal ν hV, bigAuxMass_marginal ν hV]
    _ ≤ ∑ _ : P.BigGroup, ∑ _ : Fin J, ∑ _ : Fin (J + ell), 2 * atom := by
      apply Finset.sum_le_sum
      intro g _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have ha := hatom g (a g j)
      have hb := hatom g (b g j)
      linarith
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add]; ring


end Erdos821.P3Clean
