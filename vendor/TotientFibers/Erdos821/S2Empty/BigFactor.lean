import Erdos821.S2Empty.SmallFactor

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Empty

open Erdos821.Blueprint.Graph

abbrev BigLabels (P : PrimeGroups) (M : ℕ) :=
  (g : P.BigGroup) → Fin M → P.Prime g.val

set_option maxHeartbeats 2000000 in
theorem big_label_sum_eq_prod (F : FixedData) (P : PrimeGroups) (n M : ℕ) :
    (∑ a : BigLabels P M,
      ∏ g : P.BigGroup, ∏ j : Fin M, tiltedMu F P n g.val (a g j)) =
      ∏ g : P.BigGroup,
        (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ^ M := by
  classical
  let β : P.BigGroup → Type := fun g => Fin M → P.Prime g.val
  let f : ∀ g : P.BigGroup, β g → ℝ := fun g a =>
    ∏ j : Fin M, tiltedMu F P n g.val (a j)
  calc
    _ = ∏ g : P.BigGroup, ∑ a : Fin M → P.Prime g.val,
        ∏ j : Fin M, tiltedMu F P n g.val (a j) := by
      change (∑ a : (g : P.BigGroup) → β g, ∏ g, f g (a g)) = _
      exact sum_pi_prod (ι := P.BigGroup) (β := β) f
    _ = ∏ g : P.BigGroup,
        (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ^ M := by
      apply Finset.prod_congr rfl
      intro g _
      calc
        _ = ∏ j : Fin M, ∑ p : P.Prime g.val, tiltedMu F P n g.val p :=
          sum_pi_prod (ι := Fin M) (β := fun _ => P.Prime g.val)
            (fun _ p => tiltedMu F P n g.val p)
        _ = _ := by simp

/-- Bernoulli's lower bound for a power of `1 - e`. -/
theorem one_sub_pow_lower {e : ℝ} (he : e ≤ 1) (k : ℕ) :
    1 - (k : ℝ) * e ≤ (1 - e) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmul := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr he)
    calc
      1 - ((k + 1 : ℕ) : ℝ) * e ≤ (1 - (k : ℝ) * e) * (1 - e) := by
        push_cast
        nlinarith [mul_nonneg (Nat.cast_nonneg k) (sq_nonneg e)]
      _ ≤ (1 - e) ^ k * (1 - e) := hmul
      _ = (1 - e) ^ (k + 1) := (pow_succ _ _).symm

theorem big_label_product_le_two (P : PrimeGroups) (M : ℕ) (e : ℝ)
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 2)
    (hbudget : (M : ℝ) * (Fintype.card P.BigGroup : ℝ) * e ≤ 1 / 2)
    (S : P.BigGroup → ℝ)
    (hS : ∀ g, 0 ≤ S g ∧ S g ≤ (1 - e)⁻¹) :
    ∏ g : P.BigGroup, (S g) ^ M ≤ 2 := by
  classical
  have hpow :
      (∏ g : P.BigGroup, (S g) ^ M) ≤
        ((1 - e)⁻¹) ^ (M * Fintype.card P.BigGroup) := by
    calc
      _ ≤ ∏ g : P.BigGroup, ((1 - e)⁻¹) ^ M := by
        apply Finset.prod_le_prod₀
        · intro g _
          exact pow_nonneg (hS g).1 _
        · intro g _
          exact pow_le_pow_left₀ (hS g).1 (hS g).2 _
      _ = _ := by simp [pow_mul]
  let K : ℕ := M * Fintype.card P.BigGroup
  have hKe : (K : ℝ) * e ≤ 1 / 2 := by
    dsimp [K]
    rw [Nat.cast_mul]
    nlinarith [hbudget]
  have hbern := one_sub_pow_lower (by linarith [he1] : e ≤ 1) K
  have hden : 1 / 2 ≤ (1 - e) ^ K := by nlinarith [hbern, hKe]
  have hdenpos : 0 < (1 - e) ^ K := by linarith
  have hinv : ((1 - e)⁻¹) ^ K ≤ 2 := by
    rw [inv_pow]
    apply (inv_le_iff_one_le_mul₀ hdenpos).2
    nlinarith [hden]
  exact hpow.trans (by simpa [K] using hinv)


end Erdos821.S2Empty
