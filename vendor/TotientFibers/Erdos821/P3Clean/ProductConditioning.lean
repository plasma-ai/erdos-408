import Erdos821.P3Clean.GroupGain
import Erdos821.P3Clean.SplitGroups

/-! The aggregate conditioning map over all small groups. -/

noncomputable section
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable

namespace Erdos821.P3Clean


open Erdos821.Blueprint.Graph

local instance (priority := 11000) boolEqDecidable (b c : Bool) : Decidable (b = c) :=
  instDecidableEqBool b c

local instance smallLabelsDecidableEq (P : PrimeGroups) (M : ℕ) :
    DecidableEq (SmallLabels P M) := Classical.decEq _

theorem conditioning_pi_normSq_bound {I : Type*} [Fintype I] [DecidableEq I]
    {α β : I → Type*} [∀ i, Fintype (β i)]
    (s : ∀ i, Finset (α i)) (projection : ∀ i, α i → β i) (u : I → ℂ)
    (C : ℝ) (hC : ∀ i d, ‖u i‖ ^ 2 * ((s i |>.filter
      (fun a => projection i a = d)).card : ℝ) ≤ C) (f : (∀ i, α i) → ℂ) :
    (∑ d : ∀ i, β i,
      ‖(∏ i, u i) * ∑ a ∈ (Fintype.piFinset s).filter
        (fun a => (fun i => projection i (a i)) = d), f a‖ ^ 2) ≤
      C ^ Fintype.card I * ∑ a ∈ Fintype.piFinset s, ‖f a‖ ^ 2 := by
  have hfilter (d : ∀ i, β i)
      (dec : DecidablePred (fun (a : ∀ i, α i) => (fun i => projection i (a i)) = d)) :
      @Finset.filter _ (fun (a : ∀ i, α i) => (fun i => projection i (a i)) = d) dec (Fintype.piFinset s) =
        Fintype.piFinset (fun i => (s i).filter (fun a => projection i a = d i)) := by
    ext a
    simp only [Finset.mem_filter, Fintype.mem_piFinset, funext_iff, forall_and]
  apply conditioning_normSq_bound (Fintype.piFinset s)
    (fun a i => projection i (a i)) (fun _ => ∏ i, u i)
  intro d
  rw [hfilter d]
  simp only [norm_prod, ← Finset.prod_pow, Fintype.card_piFinset, Nat.cast_prod]
  rw [← Finset.prod_mul_distrib]
  calc
    _ ≤ ∏ _ : I, C := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
      · intro i _
        exact hC i (d i)
    _ = _ := by simp

def smallArrayStates (P : PrimeGroups) (M : ℕ) (y : P.SmallResidues) :
    Finset (SmallLabels P M) :=
  Fintype.piFinset (fun g => Finset.univ.filter
    (fun a : Fin M → P.Prime g.val => Function.Injective a ∧ ∀ i, y g (a i) = 0))

def smallArrayPrefix {P : PrimeGroups} (J ell : ℕ) (a : SmallLabels P (J + ell)) :
    SmallLabels P J := fun g j => a g (Fin.castAdd ell j)

def smallArrayCoefficient (F : FixedData) (P : PrimeGroups) (J : ℕ) (y : P.SmallResidues) : ℂ :=
  ∏ g : P.SmallGroup, (normalizedSmallCoefficient F J (P.V g.val)
    ((Finset.univ.filter (fun p : P.Prime g.val => y g p = 0)).card) : ℂ)

theorem small_array_conditioning_uniform (F : FixedData) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : PrimeGroups) (J : ℕ) (y : P.SmallResidues),
      (∀ g : P.SmallGroup, F.vMin ≤ P.V g.val) →
      ∀ f : SmallLabels P (J + F.ell) → ℂ,
        (∑ d : SmallLabels P J,
          ‖smallArrayCoefficient F P J y *
            ∑ a ∈ (smallArrayStates P (J + F.ell) y).filter
              (fun a => smallArrayPrefix J F.ell a = d), f a‖ ^ 2) ≤
          C ^ Fintype.card P.SmallGroup *
            ∑ a ∈ smallArrayStates P (J + F.ell) y, ‖f a‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := small_prefix_multiplier_uniform F
  refine ⟨C, hC, ?_⟩
  intro P J y hV f
  unfold smallArrayCoefficient smallArrayStates smallArrayPrefix
  refine conditioning_pi_normSq_bound
    (I := P.SmallGroup)
    (α := fun g => Fin (J + F.ell) → P.Prime g.val)
    (β := fun g => Fin J → P.Prime g.val)
    (fun g : P.SmallGroup => Finset.univ.filter
      (fun a : Fin (J + F.ell) → P.Prime g.val => Function.Injective a ∧ ∀ i, y g (a i) = 0))
    (fun _ a j => a (Fin.castAdd F.ell j))
    (fun g => (normalizedSmallCoefficient F J (P.V g.val)
      ((Finset.univ.filter (fun p : P.Prime g.val => y g p = 0)).card) : ℂ)) C ?_ f
  intro g d
  have hfilter (dec : DecidablePred (fun a : Fin (J + F.ell) → P.Prime g.val =>
      (fun j => a (Fin.castAdd F.ell j)) = d)) :
      @Finset.filter _ (fun a => (fun j => a (Fin.castAdd F.ell j)) = d) dec
        (Finset.univ.filter (fun a => Function.Injective a ∧ ∀ i, y g (a i) = 0)) =
          smallPrefixFibre J F.ell (y g) d := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, smallPrefixFibre, funext_iff]
    tauto
  rw [hfilter]
  have hsq : ‖(normalizedSmallCoefficient F J (P.V g.val)
      ((Finset.univ.filter (fun p : P.Prime g.val => y g p = 0)).card) : ℂ)‖ ^ 2 =
      (P.V g.val) ^ (-(F.ell : ℤ)) * F.q ^
        (((Finset.univ.filter (fun p : P.Prime g.val => y g p = 0)).card : ℝ) -
          ((J + F.ell : ℕ) : ℝ)) := by
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, normalizedSmallCoefficient]
    apply Real.sq_sqrt
    exact mul_nonneg (zpow_nonneg (F.vMin_pos.trans_le (hV g)).le _)
      (Real.rpow_nonneg F.q_pos.le _)
  rw [hsq]
  have hb := hbound P g.val J (y g) d (hV g)
  simp only [mul_assoc, mul_left_comm, mul_comm] at hb ⊢
  convert hb using 1
  congr 6
  ext p
  simp


theorem small_array_conditioning_log_gain (F : FixedData) :
    ∃ Cs : ℝ, ∀ (x : ℝ) (P : PrimeGroups), P.Admissible F x → 0 < L x →
      ∀ (J : ℕ) (y : P.SmallResidues) (f : SmallLabels P (J + F.ell) → ℂ),
        (∑ d : SmallLabels P J,
          ‖smallArrayCoefficient F P J y *
            ∑ a ∈ (smallArrayStates P (J + F.ell) y).filter
              (fun a => smallArrayPrefix J F.ell a = d), f a‖ ^ 2) ≤
          (L x) ^ Cs * ∑ a ∈ smallArrayStates P (J + F.ell) y, ‖f a‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := small_array_conditioning_uniform F
  refine ⟨F.C₀ * Real.log (max 1 C), ?_⟩
  intro x P hP hL J y f
  have hV (g : P.SmallGroup) : F.vMin ≤ P.V g.val := (hP.2.2.2.2.1 g.val).1
  have hpow : C ^ Fintype.card P.SmallGroup ≤ (max 1 C) ^ Fintype.card P.SmallGroup :=
    pow_le_pow_left₀ hC.le (le_max_right _ _) _
  have hg : (max 1 C) ^ Fintype.card P.SmallGroup ≤ (L x) ^ (F.C₀ * Real.log (max 1 C)) := by
    exact small_group_gain F (max 1 C) (le_max_left _ _) x P hP hL
  exact (hbound P J y hV f).trans (mul_le_mul_of_nonneg_right
    (hpow.trans hg)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))


end Erdos821.P3Clean
