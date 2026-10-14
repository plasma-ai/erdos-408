import Erdos821.P3Edge.SmallDamp
import Erdos821.P3Edge.SmallFresh
import Erdos821.P3Edge.TransferBounds

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {g : P.Group}

def smallPrefixFibre (J ell : ℕ) (y : (p : P.Prime g) → ZMod p.val)
    (d : Fin J → P.Prime g) : Finset (Fin (J + ell) → P.Prime g) :=
  Finset.univ.filter (fun a => Function.Injective a ∧ (∀ i, y (a i) = 0) ∧
    ∀ j : Fin J, a (Fin.castAdd ell j) = d j)

theorem smallPrefixFibre_nonempty (J ell : ℕ) (y : (p : P.Prime g) → ZMod p.val)
    (d : Fin J → P.Prime g) (h : (smallPrefixFibre J ell y d).Nonempty) :
    Function.Injective d ∧ (∀ j, y (d j) = 0) ∧
      J + ell ≤ (Finset.univ.filter (fun p : P.Prime g => y p = 0)).card := by
  classical
  obtain ⟨a, ha⟩ := h
  obtain ⟨hinj, hzero, hprefix⟩ := (Finset.mem_filter.mp ha).2
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    have hh := congrArg Fin.val (hinj ((hprefix i).trans (hij.trans (hprefix j).symm)))
    exact hh
  · intro j
    rw [← hprefix j]
    exact hzero _
  · have hcard : (Finset.univ.image a).card = J + ell := by
      rw [Finset.card_image_of_injective _ hinj]
      simp
    rw [← hcard]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero _⟩

theorem smallPrefixFibre_card (J ell : ℕ) (y : (p : P.Prime g) → ZMod p.val)
    (d : Fin J → P.Prime g) (hd : Function.Injective d) (hy : ∀ j, y (d j) = 0) :
    (smallPrefixFibre J ell y d).card ≤
      ((Finset.univ.filter (fun p : P.Prime g => y p = 0)).card - J).descFactorial ell := by
  classical
  let Z := Finset.univ.filter (fun p : P.Prime g => y p = 0)
  let D := Finset.univ.image d
  let B := Z \ D
  have hDZ : D ⊆ Z := by
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy j⟩
  have hD : D.card = J := by
    rw [Finset.card_image_of_injective _ hd]
    simp
  have hB : B.card = Z.card - J := by
    rw [Finset.card_sdiff_of_subset hDZ, hD]
  let suffix : {a // a ∈ smallPrefixFibre J ell y d} → (Fin ell ↪ {p // p ∈ B}) :=
    fun a => {
      toFun := fun i => ⟨a.val (Fin.natAdd J i), by
        obtain ⟨ha, hzero, hprefix⟩ := (Finset.mem_filter.mp a.property).2
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero _⟩, ?_⟩
        intro hp
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp
        have heq : Fin.castAdd ell j = Fin.natAdd J i := ha ((hprefix j).trans hj)
        have hv := congrArg Fin.val heq
        simp only [Fin.coe_castAdd, Fin.coe_natAdd] at hv
        omega⟩
      inj' := by
        intro i j hij
        obtain ⟨ha, _, _⟩ := (Finset.mem_filter.mp a.property).2
        have hh := ha (congrArg Subtype.val hij)
        apply Fin.ext
        have hv := congrArg Fin.val hh
        simp only [Fin.coe_natAdd] at hv
        omega
    }
  have hinj : Function.Injective suffix := by
    intro a b hab
    apply Subtype.ext
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have ha := ((Finset.mem_filter.mp a.property).2).2.2 j
      have hb := ((Finset.mem_filter.mp b.property).2).2.2 j
      exact ha.trans hb.symm
    · exact congrArg Subtype.val (congrArg (fun f : Fin ell ↪ {p // p ∈ B} => f j) hab)
  have hc := Fintype.card_le_of_injective suffix hinj
  simpa only [Fintype.card_coe, Fintype.card_embedding_eq, Fintype.card_fin, hB] using hc

/-- Per-small-group damped weight. -/
def smallGroupWeight (F : FixedData) (J : ℕ) (g : P.SmallGroup)
    (y : (p : P.Prime g.val) → ZMod p.val) : ℝ :=
  (P.V g.val) ^ (-(F.ell : ℤ)) *
    F.q ^ ((((Finset.univ.filter (fun p : P.Prime g.val => y p = 0)).card : ℝ) -
      ((J : ℝ) + (F.ell : ℝ))) / 2)

lemma smallGroupWeight_nonneg (F : FixedData) (J : ℕ) (g : P.SmallGroup)
    (hV : 0 < P.V g.val) (y : (p : P.Prime g.val) → ZMod p.val) :
    0 ≤ smallGroupWeight F J g y := by
  unfold smallGroupWeight
  exact mul_nonneg (zpow_nonneg hV.le _) (Real.rpow_nonneg F.q_pos.le _)

/-- The product of `smallGroupWeight` over all small groups equals
`smallTargetFactor F * smallDamping F J y`. -/
lemma prod_smallGroupWeight_eq (F : FixedData) (J : ℕ) (y : P.SmallResidues) :
    (∏ g : P.SmallGroup, smallGroupWeight F J g (y g)) =
      smallTargetFactor (P := P) F * smallDamping F J y := by
  unfold smallGroupWeight smallTargetFactor smallDamping smallOmega
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos F.q_pos]
  congr 2
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Nat.cast_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- Unconditional bound on the small-group fiber sum for one small group `g`. -/
lemma smallPrefixFibre_sum_le (F : FixedData) (J m : ℕ) (Csmall0 : ℝ)
    (hCsmall0_pos : 0 < Csmall0)
    (hCsmall0 : ∀ Y : ℕ, F.ell ≤ Y →
      (Y : ℝ) ^ F.ell * F.q ^ ((((Y - F.ell : ℕ)) : ℝ) / 2) ≤ Csmall0)
    (g : P.SmallGroup) (hVlo : F.vMin ≤ P.V g.val)
    (y : (p : P.Prime g.val) → ZMod p.val) (d : Fin J → P.Prime g.val) :
    (∑ b : Fin (J + F.ell) → P.Prime g.val,
      if b ∈ smallPrefixFibre J F.ell y d then smallGroupWeight F J g y else 0) ≤
      max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0) := by
  classical
  have hsum : (∑ b : Fin (J + F.ell) → P.Prime g.val,
      if b ∈ smallPrefixFibre J F.ell y d then smallGroupWeight F J g y else 0) =
      ((smallPrefixFibre J F.ell y d).card : ℝ) * smallGroupWeight F J g y := by
    rw [← Finset.sum_filter, Finset.filter_univ_mem, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  rcases Finset.eq_empty_or_nonempty (smallPrefixFibre J F.ell y d) with hemp | hne
  · rw [hemp, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact le_trans zero_le_one (le_max_left _ _)
  · obtain ⟨hd, hy, hZ⟩ := smallPrefixFibre_nonempty J F.ell y d hne
    set Z := (Finset.univ.filter (fun p : P.Prime g.val => y p = 0)).card
    have hcard_R : ((smallPrefixFibre J F.ell y d).card : ℝ) ≤ ((Z - J : ℕ) : ℝ) ^ F.ell :=
      le_trans (Nat.cast_le.mpr (smallPrefixFibre_card J F.ell y d hd hy))
        (descFactorial_le_pow (Z - J) F.ell)
    have hY : F.ell ≤ Z - J := by omega
    have hexp_eq : ((Z : ℝ) - ((J : ℝ) + (F.ell : ℝ))) / 2 =
        ((((Z - J) - F.ell : ℕ) : ℝ) / 2) := by
      have h1 : (Z - J) - F.ell = Z - (J + F.ell) := Nat.sub_sub Z J F.ell
      rw [h1, Nat.cast_sub hZ, Nat.cast_add]
    have hVpos : 0 < P.V g.val := lt_of_lt_of_le F.vMin_pos hVlo
    have hVinv : (P.V g.val) ^ (-(F.ell : ℤ)) ≤ max 1 ((F.vMin⁻¹) ^ (F.ell + m)) :=
      Vinv_pow_le F.vMin_pos (P.V g.val) hVlo F.ell (Nat.le_add_right _ _)
    have hdamp : ((Z - J : ℕ) : ℝ) ^ F.ell *
        F.q ^ ((((Z : ℝ) - ((J : ℝ) + (F.ell : ℝ))) / 2)) ≤ Csmall0 := by
      rw [hexp_eq]
      exact hCsmall0 (Z - J) hY
    have hwg_nn : 0 ≤ smallGroupWeight F J g y := smallGroupWeight_nonneg F J g hVpos y
    calc ((smallPrefixFibre J F.ell y d).card : ℝ) * smallGroupWeight F J g y
        ≤ ((Z - J : ℕ) : ℝ) ^ F.ell * smallGroupWeight F J g y :=
          mul_le_mul_of_nonneg_right hcard_R hwg_nn
      _ = (P.V g.val) ^ (-(F.ell : ℤ)) *
          (((Z - J : ℕ) : ℝ) ^ F.ell *
            F.q ^ (((Z : ℝ) - ((J : ℝ) + (F.ell : ℝ))) / 2)) := by
          unfold smallGroupWeight
          ring
      _ ≤ max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0 := by
          apply mul_le_mul hVinv hdamp
          · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg F.q_pos.le _)
          · exact le_trans zero_le_one (le_max_left _ _)
      _ ≤ max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0) := le_max_right _ _

end Erdos821.P3Edge
