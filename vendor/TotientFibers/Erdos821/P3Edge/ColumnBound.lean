import Erdos821.P3Edge.RowBound
import Erdos821.P3Edge.ColReversal
import Erdos821.P3Edge.ColSummable

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-! ### Invariance and factorization of `memoryMass` and `edgeDelta` -/

lemma smallPhysical_permuteActive_iff {M : ℕ} (π : P.Permutations M)
    (y : P.SmallResidues) (a : P.Labels M) :
    P.smallPhysical y (P.act π a) ↔ P.smallPhysical y a := by
  unfold PrimeGroups.smallPhysical PrimeGroups.act
  refine forall_congr' (fun g => and_congr ?_ ?_)
  · constructor
    · intro h i j hij
      have h' : (π g.val).symm i = (π g.val).symm j := by
        apply h
        dsimp
        rw [(π g.val).apply_symm_apply, (π g.val).apply_symm_apply]
        exact hij
      exact (π g.val).symm.injective h'
    · intro h i j hij
      exact (π g.val).injective (h hij)
  · constructor
    · intro h i
      have h' := h ((π g.val).symm i)
      rwa [(π g.val).apply_symm_apply] at h'
    · intro h i
      exact h (π g.val i)

/-- Small-group baseline factor in `memoryMass`. -/
def smallBaseMass (F : FixedData) (P : PrimeGroups) (J : ℕ) : ℝ :=
  (Fintype.card P.SmallResidues : ℝ)⁻¹ *
    (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ))

lemma smallBaseMass_nonneg (F : FixedData) (P : PrimeGroups) (J : ℕ)
    (hV : ∀ g : P.Group, 0 < P.V g) :
    0 ≤ smallBaseMass F P J := by
  unfold smallBaseMass
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.prod_nonneg (fun g _ => zpow_nonneg (hV g.val).le _)

lemma memoryMass_eq_of_smallPhysical (F : FixedData) (J n : ℕ)
    (π : P.Permutations (J + F.ell)) (z : P.MemoryState (J + F.ell))
    (hphys : P.smallPhysical z.1 (P.act π z.2.1)) :
    P.memoryMass F J n z =
      smallBaseMass F P J *
        ∏ g : P.BigGroup,
          ((∏ idx : Fin (J + F.ell), tiltedMu F P n g.val ((P.act π z.2.1) g.val idx)) *
            P.groupMemoryMass F n g.val (z.2.2 g)) := by
  have hphys0 : P.smallPhysical z.1 z.2.1 :=
    (smallPhysical_permuteActive_iff π z.1 z.2.1).mp hphys
  unfold PrimeGroups.memoryMass smallBaseMass
  rw [if_pos hphys0, Finset.prod_mul_distrib, ← mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro g _
  symm
  exact Equiv.prod_comp (π g.val) (fun idx => tiltedMu F P n g.val (z.2.1 g.val idx))

lemma memoryMass_nonneg (F : FixedData) (J n : ℕ)
    (hV : ∀ g : P.Group, 0 < P.V g)
    (htilted : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (z : P.MemoryState (J + F.ell)) :
    0 ≤ P.memoryMass F J n z := by
  unfold PrimeGroups.memoryMass
  split_ifs
  · apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        exact Finset.prod_nonneg (fun g _ => zpow_nonneg (hV g.val).le _)
      · exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => htilted g _))
    · exact Finset.prod_nonneg (fun g _ => groupMemoryMass_nonneg F n (htilted g) (z.2.2 g))
  · exact le_refl 0

lemma edgeDelta_eq_of_compatible (A : Model F P J m) (ν : Pattern P J F.ell m)
    (forward : Bool) (a b : P.Labels (J + F.ell)) (u : P.Aux J)
    (hcomp : ν.compatible a b) :
    edgeDelta A ν forward a u = edgeDelta A ν forward b u := by
  have hD : ν.D a u = ν.D b u := by
    unfold Pattern.D
    apply Finset.prod_congr rfl
    intro g _
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ ν.changed g
    · simp [hi]
    · have hsh : ν.shared g (ν.slot i) := ⟨i, rfl, hi⟩
      rw [if_neg hi, if_neg hi, hcomp g (ν.slot i) hsh]
  unfold edgeDelta
  rw [hD]

lemma translateSmallResidues_neg_cancel (d : ℤ) (y : P.SmallResidues) :
    translateSmallResidues (-d) (translateSmallResidues d y) = y := by
  funext g p
  unfold translateSmallResidues
  push_cast
  exact add_neg_cancel_right (y g p) (d : ZMod p.val)

lemma edgeChoiceCoefficient_indep_f (A : Model F P J m) (n : ℕ) (rho theta : ℝ)
    (i : Fin n) (s t : P.MemoryState (J + F.ell))
    (π τ : P.Permutations (J + F.ell)) (v : Fin A.patternCount) (u : P.Aux J)
    (B A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)))
    (f₁ f₂ : (g : P.BigGroup) → {idx : Fin (J + F.ell) // idx ∈ A_retr g} → Fin (s.2.2 g).card) :
    edgeChoiceCoefficient A n rho theta i s t (π, τ, v, u, (B, ⟨A_retr, f₁⟩)) =
      edgeChoiceCoefficient A n rho theta i s t (π, τ, v, u, (B, ⟨A_retr, f₂⟩)) := rfl

/-! ### Column fiber definitions and label sum bound -/

/-- Sum over reversed retrieval maps `f'_g` for a single big group in the column bound. -/
def colBigMapSum (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (ν : Pattern P J F.ell m) (delta' : ℤ) (tt : P.MemoryState (J + F.ell))
    (g : P.BigGroup) (B'_g A'_g : Finset (Fin (J + F.ell)))
    (a_g : Fin (J + F.ell) → P.Prime g.val) : ℝ :=
  ∑ f'_g : {idx : Fin (J + F.ell) // idx ∈ A'_g} → Fin (tt.2.2 g).card,
    if bigGroupValid ν delta' g (tt.2.1 g.val) (tt.2.2 g) B'_g A'_g f'_g a_g then
      bigGroupWeight F r n ν delta' g (tt.2.1 g.val) (tt.2.2 g) B'_g A'_g f'_g a_g
    else 0

lemma colBigMapSum_nonneg (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (ν : Pattern P J F.ell m) (delta' : ℤ) (tt : P.MemoryState (J + F.ell))
    (g : P.BigGroup) (hV : 0 < P.V g.val)
    (htilted : ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (B'_g A'_g : Finset (Fin (J + F.ell)))
    (a_g : Fin (J + F.ell) → P.Prime g.val) :
    0 ≤ colBigMapSum F r n ν delta' tt g B'_g A'_g a_g := by
  unfold colBigMapSum
  apply Finset.sum_nonneg
  intro f'_g _
  split_ifs
  · exact bigGroupWeight_nonneg F r n ν delta' g hV htilted _ _ _ _ _ _
  · exact le_refl 0

/-- Product of `colBigMapSum` over big groups and `smallPrefixFibre` indicator over small groups. -/
def colLabelTerm (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (ν : Pattern P J F.ell m) (delta' : ℤ) (tt : P.MemoryState (J + F.ell))
    (B' A' : (g : P.BigGroup) → Finset (Fin (J + F.ell)))
    (a : P.Labels (J + F.ell)) : ℝ :=
  (∏ g : P.BigGroup, colBigMapSum F r n ν delta' tt g (B' g) (A' g) (a g.val)) *
  (∏ g : P.SmallGroup,
    if a g.val ∈ smallPrefixFibre J F.ell
        (translateSmallResidues delta' tt.1 g)
        (fun j => tt.2.1 g.val (Fin.castAdd F.ell j)) then
      smallGroupWeight F J g (translateSmallResidues delta' tt.1 g)
    else 0)

lemma colLabelTerm_nonneg (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (hV : ∀ g : P.Group, 0 < P.V g)
    (htilted : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (ν : Pattern P J F.ell m) (delta' : ℤ) (tt : P.MemoryState (J + F.ell))
    (B' A' : (g : P.BigGroup) → Finset (Fin (J + F.ell)))
    (a : P.Labels (J + F.ell)) :
    0 ≤ colLabelTerm F r n ν delta' tt B' A' a := by
  unfold colLabelTerm
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun g _ =>
      colBigMapSum_nonneg F r n ν delta' tt g (hV g.val) (htilted g) (B' g) (A' g) (a g.val))
  · apply Finset.prod_nonneg (fun g _ => ?_)
    split_ifs
    · exact smallGroupWeight_nonneg F J g (hV g.val) _
    · exact le_refl 0

/-- Summing `colLabelTerm` over `(B, A_retr, a)` is bounded by the product of big and small group constants. -/
lemma sum_colLabelTerm_le (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (Cprom Csmall0 : ℝ) (hCsmall0_pos : 0 < Csmall0)
    (hCprom : ∀ Z' a : ℕ, a ≤ F.ell + m → (Z' : ℝ) ^ a * r.rho ^ (Z' - a) ≤ Cprom)
    (hCsmall0 : ∀ Y : ℕ, F.ell ≤ Y →
      (Y : ℝ) ^ F.ell * F.q ^ ((((Y - F.ell : ℕ)) : ℝ) / 2) ≤ Csmall0)
    (hVlo : ∀ g : P.Group, F.vMin ≤ P.V g)
    (htilted_nn : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (htilted_sum : ∀ g : P.BigGroup, ∑ p : P.Prime g.val, tiltedMu F P n g.val p ≤ 2)
    (ν : Pattern P J F.ell m) (delta' : ℤ) (tt : P.MemoryState (J + F.ell)) :
    (∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
      ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
        ∑ a : P.Labels (J + F.ell),
          colLabelTerm F r n ν delta' tt A_retr B a) ≤
      (bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
        (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^ Fintype.card P.SmallGroup := by
  classical
  have hVpos : ∀ g : P.Group, 0 < P.V g := fun g => lt_of_lt_of_le F.vMin_pos (hVlo g)
  let F_small : (g : P.SmallGroup) → (Fin (J + F.ell) → P.Prime g.val) → ℝ :=
    fun g a_g =>
      if a_g ∈ smallPrefixFibre J F.ell
          (translateSmallResidues delta' tt.1 g)
          (fun j => tt.2.1 g.val (Fin.castAdd F.ell j)) then
        smallGroupWeight F J g (translateSmallResidues delta' tt.1 g)
      else 0
  have hmap_eq : ∀ (g : P.BigGroup) (B'_g A'_g : Finset (Fin (J + F.ell))),
      (∑ a_g : Fin (J + F.ell) → P.Prime g.val,
        colBigMapSum F r n ν delta' tt g B'_g A'_g a_g) =
      bigChoiceMapSum F r n ν delta' tt g B'_g A'_g := by
    intro g B'_g A'_g
    unfold colBigMapSum bigChoiceMapSum bigChoiceLabelSum
    exact Finset.sum_comm
  have ha_sum : ∀ (B A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell))),
      (∑ a : P.Labels (J + F.ell), colLabelTerm F r n ν delta' tt A_retr B a) =
      (∏ g : P.BigGroup, bigChoiceMapSum F r n ν delta' tt g (A_retr g) (B g)) *
      (∏ g : P.SmallGroup, ∑ a_g : Fin (J + F.ell) → P.Prime g.val, F_small g a_g) := by
    intro B A_retr
    unfold colLabelTerm
    rw [sum_labels_split (fun g a_g => colBigMapSum F r n ν delta' tt g (A_retr g) (B g) a_g) F_small]
    congr 1
    apply Finset.prod_congr rfl
    intro g _
    exact hmap_eq g (A_retr g) (B g)
  simp_rw [ha_sum, ← Finset.sum_mul]
  rw [Finset.sum_comm]
  have hB_sum : ∀ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
      (∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
        ∏ g : P.BigGroup, bigChoiceMapSum F r n ν delta' tt g (A_retr g) (B g)) =
      ∏ g : P.BigGroup, bigChoiceRetrSum F r n ν delta' tt g (A_retr g) := by
    intro A_retr
    exact sum_pi_prod (fun g B_g => bigChoiceMapSum F r n ν delta' tt g (A_retr g) B_g)
  have hAB_sum : (∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
      ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
        ∏ g : P.BigGroup, bigChoiceMapSum F r n ν delta' tt g (A_retr g) (B g)) =
      ∏ g : P.BigGroup, ∑ A_g : Finset (Fin (J + F.ell)),
        bigChoiceRetrSum F r n ν delta' tt g A_g := by
    rw [Finset.sum_congr rfl (fun A_retr _ => hB_sum A_retr)]
    exact sum_pi_prod (fun g A_g => bigChoiceRetrSum F r n ν delta' tt g A_g)
  rw [hAB_sum]
  have hbig_prod_le : (∏ g : P.BigGroup,
      ∑ A_g : Finset (Fin (J + F.ell)), bigChoiceRetrSum F r n ν delta' tt g A_g) ≤
      (bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup := by
    apply prod_le_const_pow
    · intro g
      unfold bigChoiceRetrSum bigChoiceMapSum bigChoiceLabelSum
      refine Finset.sum_nonneg (fun B_g _ => Finset.sum_nonneg (fun A_g _ =>
        Finset.sum_nonneg (fun f_g _ => Finset.sum_nonneg (fun b_g _ => ?_))))
      split_ifs
      · exact bigGroupWeight_nonneg F r n ν delta' g (hVpos g.val) (htilted_nn g) _ _ _ _ _ _
      · exact le_refl 0
    · intro g
      unfold bigChoiceRetrSum bigChoiceMapSum bigChoiceLabelSum
      exact bigGroup_sum_le F r n Cprom hCprom ν delta' g (hVlo g.val)
        (htilted_nn g) (htilted_sum g) (tt.2.1 g.val) (tt.2.2 g)
  have hsmall_prod_le : (∏ g : P.SmallGroup,
      ∑ a_g : Fin (J + F.ell) → P.Prime g.val, F_small g a_g) ≤
      (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^ Fintype.card P.SmallGroup := by
    apply prod_le_const_pow
    · intro g
      refine Finset.sum_nonneg (fun a_g _ => ?_)
      dsimp [F_small]
      split_ifs
      · exact smallGroupWeight_nonneg F J g (hVpos g.val) _
      · exact le_refl 0
    · intro g
      exact smallPrefixFibre_sum_le F J m Csmall0 hCsmall0_pos hCsmall0 g (hVlo g.val) _ _
  apply mul_le_mul hbig_prod_le hsmall_prod_le
  · refine Finset.prod_nonneg (fun g _ => Finset.sum_nonneg (fun a_g _ => ?_))
    dsimp [F_small]
    split_ifs
    · exact smallGroupWeight_nonneg F J g (hVpos g.val) _
    · exact le_refl 0
  · exact pow_nonneg (bigGroupConst_pos F r m Cprom).le _

/-! ### Reversal bound at a single source `s` -/

/-- Inner sum over retrieval maps `f` for fixed `(π, τ, v, u, B, A_retr)` and source `s`. -/
def colSourceMapSum (F : FixedData) (r : MemoryParameters F) (n : ℕ) (theta : ℝ)
    (i : Fin n) (A : Model F P J m) (t : P.MemoryState (J + F.ell))
    (π τ : P.Permutations (J + F.ell)) (v : Fin A.patternCount) (u : P.Aux J)
    (B A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)))
    (s : P.MemoryState (J + F.ell)) : ℝ :=
  ∑ f : (g : P.BigGroup) → {idx : Fin (J + F.ell) // idx ∈ A_retr g} → Fin (s.2.2 g).card,
    if edgeChoiceValid A .all i s t (π, τ, v, u, (B, ⟨A_retr, f⟩)) then
      P.memoryMass F J n s *
        ‖edgeChoiceCoefficient A n r.rho theta i s t (π, τ, v, u, (B, ⟨A_retr, f⟩))‖ *
        P.memoryWeight r.v s
    else 0

lemma colSourceMapSum_nonneg (F : FixedData) (r : MemoryParameters F) (n : ℕ) (theta : ℝ)
    (i : Fin n) (A : Model F P J m) (t : P.MemoryState (J + F.ell))
    (hV : ∀ g : P.Group, 0 < P.V g)
    (htilted : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (π τ : P.Permutations (J + F.ell)) (v : Fin A.patternCount) (u : P.Aux J)
    (B A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)))
    (s : P.MemoryState (J + F.ell)) :
    0 ≤ colSourceMapSum F r n theta i A t π τ v u B A_retr s := by
  unfold colSourceMapSum
  apply Finset.sum_nonneg
  intro f _
  split_ifs
  · exact mul_nonneg (mul_nonneg (memoryMass_nonneg F J n hV htilted s) (norm_nonneg _))
      (memoryWeight_nonneg r s)
  · exact le_refl 0

/-- Expands `P.memoryMass * absoluteMemoryEdgeKernel * P.memoryWeight` at a single `s`
into the outer choice sums of `colSourceMapSum`. -/
lemma source_choice_sum_eq_colSourceMapSum (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (theta : ℝ) (i : Fin n) (A : Model F P J m)
    (s t : P.MemoryState (J + F.ell)) :
    P.memoryMass F J n s *
      absoluteMemoryEdgeKernel A n r.rho theta i .all s t *
      P.memoryWeight r.v s =
    edgeSymmetryFactor P (J + F.ell) *
      ∑ π : P.Permutations (J + F.ell),
        ∑ τ : P.Permutations (J + F.ell),
          ∑ v : Fin A.patternCount,
            ∑ u : P.Aux J,
              ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  colSourceMapSum F r n theta i A t π τ v u B A_retr s := by
  classical
  have h1 : P.memoryMass F J n s *
        absoluteMemoryEdgeKernel A n r.rho theta i .all s t *
        P.memoryWeight r.v s =
      edgeSymmetryFactor P (J + F.ell) *
        ∑ c : EdgeChoice A s,
          if edgeChoiceValid A .all i s t c then
            P.memoryMass F J n s *
              ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ *
              P.memoryWeight r.v s
          else 0 := by
    unfold absoluteMemoryEdgeKernel
    rw [mul_left_comm (P.memoryMass F J n s) (edgeSymmetryFactor P (J + F.ell)),
      mul_assoc (edgeSymmetryFactor P (J + F.ell)),
      Finset.mul_sum, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> ring
  rw [h1]
  congr 1
  unfold EdgeChoice TransferChoice colSourceMapSum
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl (fun π _ => ?_)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl (fun u _ => ?_)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl (fun B _ => ?_)
  rw [Fintype.sum_sigma]

/-- Pointwise reversal inequality combining all big and small groups at a valid choice `f₀`. -/
lemma col_rawEdge_reversal_le (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (i : Fin n) (A : Model F P J m)
    (hVlo : ∀ g : P.Group, F.vMin ≤ P.V g)
    (hVhi : ∀ g : P.Group, P.V g ≤ F.vMax)
    (htilted_nn : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (π τ : P.Permutations (J + F.ell)) (v : Fin A.patternCount) (u : P.Aux J)
    (B A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)))
    (s t : P.MemoryState (J + F.ell))
    (f₀ : (g : P.BigGroup) → {idx : Fin (J + F.ell) // idx ∈ A_retr g} → Fin (s.2.2 g).card)
    (hval₀ : edgeChoiceValid A .all i s t (π, τ, v, u, (B, ⟨A_retr, f₀⟩))) :
    let ν := A.pattern v
    let ss := permuteActive π s
    let tt := permuteActive τ t
    let delta := edgeDelta A ν (edgeForward i) tt.2.1 u
    (∏ g : P.BigGroup,
      ((retrievalFibre (s.2.2 g) (A_retr g)
        (fun idx => ⟨tt.2.1 g.val idx, -(delta : ZMod (tt.2.1 g.val idx).val)⟩)).card : ℝ)) *
      (P.memoryMass F J n s *
        |rawEdgeWeight A n r.rho ν u ss tt (B, ⟨A_retr, f₀⟩)| *
        P.memoryWeight r.v s) ≤
    ν.auxMass u * P.memoryMass F J n t * P.memoryWeight r.v t *
      (colRevConst F m ^ Fintype.card P.BigGroup) *
      colLabelTerm F r n ν (-delta) tt A_retr B ss.2.1 := by
  classical
  intro ν ss tt delta
  have hVpos : ∀ g : P.Group, 0 < P.V g := fun g => lt_of_lt_of_le F.vMin_pos (hVlo g)
  obtain ⟨hs_phys, ht_phys, hcomp, _, ht_small_raw, hg_raw⟩ := hval₀.1
  have hdelta_eq : edgeDelta A ν (edgeForward i) ss.2.1 u = delta :=
    edgeDelta_eq_of_compatible A ν (edgeForward i) ss.2.1 tt.2.1 u hcomp
  have ht_small : t.1 = translateSmallResidues delta s.1 := by
    have h1 : t.1 = translateSmallResidues (edgeDelta A ν (edgeForward i) ss.2.1 u) s.1 :=
      ht_small_raw
    rwa [hdelta_eq] at h1
  have hs_small : s.1 = translateSmallResidues (-delta) t.1 := by
    rw [ht_small, translateSmallResidues_neg_cancel]
  have hsg_mem : ∀ g : P.SmallGroup,
      ss.2.1 g.val ∈ smallPrefixFibre J F.ell
        (translateSmallResidues (-delta) t.1 g)
        (fun j => tt.2.1 g.val (Fin.castAdd F.ell j)) := by
    intro g
    simp only [smallPrefixFibre, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(hs_phys g).1, ?_, ?_⟩
    · intro idx
      rw [← hs_small]
      exact (hs_phys g).2 idx
    · intro j
      have hch : j ∉ ν.changed g.val := by
        rw [ν.small g.val g.property]
        exact Finset.notMem_empty j
      exact hcomp g.val (ν.slot j) ⟨j, rfl, hch⟩
  set S_prod := ∏ g : P.SmallGroup,
    if ss.2.1 g.val ∈ smallPrefixFibre J F.ell
        (translateSmallResidues (-delta) tt.1 g)
        (fun j => tt.2.1 g.val (Fin.castAdd F.ell j)) then
      smallGroupWeight F J g (translateSmallResidues (-delta) tt.1 g)
    else 0
  have hsmall_prod : smallTargetFactor (P := P) F * smallDamping F J s.1 = S_prod := by
    have h1 : S_prod = ∏ g : P.SmallGroup, smallGroupWeight F J g (s.1 g) := by
      apply Finset.prod_congr rfl
      intro g _
      change (if ss.2.1 g.val ∈ smallPrefixFibre J F.ell
          (translateSmallResidues (-delta) t.1 g)
          (fun j => tt.2.1 g.val (Fin.castAdd F.ell j)) then
        smallGroupWeight F J g (translateSmallResidues (-delta) t.1 g) else 0) = _
      rw [if_pos (hsg_mem g), ← hs_small]
    rw [h1, prod_smallGroupWeight_eq]
  have hw_eq : P.memoryWeight r.v s =
      P.memoryWeight r.v t * ∏ g : P.BigGroup, (r.v ^ (A_retr g).card / r.v ^ (B g).card) := by
    unfold PrimeGroups.memoryWeight PrimeGroups.memorySize
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro g _
    have hcard := rawEdgeValid_memory_card A ν (edgeForward i) u ss tt (B, ⟨A_retr, f₀⟩) hval₀.1 g
    have hinj : Function.Injective (f₀ g) := (hg_raw g).2.2.1
    have hle : (A_retr g).card ≤ (s.2.2 g).card := by
      have hc := Fintype.card_le_of_injective (f₀ g) hinj
      simpa using hc
    have hvne : r.v ≠ 0 := ne_of_gt (lt_trans zero_lt_one r.v_gt)
    change r.v ^ (s.2.2 g).card =
      r.v ^ (t.2.2 g).card * (r.v ^ (A_retr g).card / r.v ^ (B g).card)
    have hcard' : (t.2.2 g).card = (s.2.2 g).card - (A_retr g).card + (B g).card := hcard
    rw [hcard', pow_add]
    have hsub : r.v ^ ((s.2.2 g).card - (A_retr g).card) =
        r.v ^ (s.2.2 g).card / r.v ^ (A_retr g).card := by
      rw [eq_div_iff (pow_ne_zero _ hvne), ← pow_add, Nat.sub_add_cancel hle]
    have hA_ne : r.v ^ (A_retr g).card ≠ 0 := pow_ne_zero _ hvne
    have hB_ne : r.v ^ (B g).card ≠ 0 := pow_ne_zero _ hvne
    rw [hsub]
    calc r.v ^ (s.2.2 g).card
        = (r.v ^ (s.2.2 g).card / r.v ^ (A_retr g).card * r.v ^ (A_retr g).card) *
            (r.v ^ (B g).card / r.v ^ (B g).card) := by
          rw [div_mul_cancel₀ _ hA_ne, div_self hB_ne, mul_one]
      _ = r.v ^ (s.2.2 g).card / r.v ^ (A_retr g).card * r.v ^ (B g).card *
            (r.v ^ (A_retr g).card / r.v ^ (B g).card) := by ring
  have hmass_s := memoryMass_eq_of_smallPhysical F J n π s hs_phys
  have hmass_t := memoryMass_eq_of_smallPhysical F J n τ t ht_phys
  let LHS_g (g : P.BigGroup) : ℝ :=
    ((retrievalFibre (s.2.2 g) (A_retr g)
      (fun idx => ⟨tt.2.1 g.val idx, -(delta : ZMod (tt.2.1 g.val idx).val)⟩)).card : ℝ) *
    (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (ss.2.1 g.val idx)) *
    P.groupMemoryMass F n g.val (s.2.2 g) *
    (∏ idx : Fin (J + F.ell),
      if ν.shared g.val idx ∨ idx ∈ A_retr g then 1 else tiltedMu F P n g.val (tt.2.1 g.val idx)) *
    (P.V g.val) ^ (-((A_retr g).card : ℤ)) *
    r.rho ^ (zeroMemoryIndices (s.2.2 g)).card *
    (r.v ^ (A_retr g).card / r.v ^ (B g).card)
  let RHS_g (g : P.BigGroup) : ℝ :=
    colRevConst F m *
    (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (tt.2.1 g.val idx)) *
    P.groupMemoryMass F n g.val (t.2.2 g) *
    colBigMapSum F r n ν (-delta) tt g (A_retr g) (B g) (ss.2.1 g.val)
  have hg_le : ∀ g : P.BigGroup, LHS_g g ≤ RHS_g g := by
    intro g
    obtain ⟨hB_g, hA_g, hinj_g, hprom_g, hmem_g⟩ := hg_raw g
    have hret_g : ∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_retr g},
        (memoryEntry (s.2.2 g) (f₀ g idx)).1 = tt.2.1 g.val idx.val ∧
        (memoryEntry (s.2.2 g) (f₀ g idx)).2 +
          (delta : ZMod (memoryEntry (s.2.2 g) (f₀ g idx)).1.val) = 0 := by
      intro idx
      refine ⟨(hprom_g idx).1, ?_⟩
      have h2 : (memoryEntry (s.2.2 g) (f₀ g idx)).2 +
          (edgeDelta A ν (edgeForward i) ss.2.1 u : ZMod (memoryEntry (s.2.2 g) (f₀ g idx)).1.val) = 0 :=
        (hprom_g idx).2.1
      rwa [hdelta_eq] at h2
    have ht_eq_g : t.2.2 g = translateMemory delta
        (deleteMemoryIndices (s.2.2 g) (Finset.univ.image (f₀ g)) +
          storedMemory (ss.2.1 g.val) (B g)) := by
      have hm : t.2.2 g = translateMemory (edgeDelta A ν (edgeForward i) ss.2.1 u)
          (deleteMemoryIndices (s.2.2 g) (Finset.univ.image (f₀ g)) +
            storedMemory (ss.2.1 g.val) (B g)) := hmem_g
      rwa [hdelta_eq] at hm
    exact col_bigGroup_reversal_le F r n ν delta g (hVlo g.val) (hVhi g.val)
      (htilted_nn g) (ss.2.1 g.val) (tt.2.1 g.val) (s.2.2 g) (t.2.2 g)
      (B g) (A_retr g) (f₀ g)
      (fun idx hidx => (hB_g idx hidx).1) hA_g (fun idx hsh => hcomp g.val idx hsh)
      hinj_g hret_g ht_eq_g
  have hLHS_g_nn : ∀ g : P.BigGroup, 0 ≤ LHS_g g := by
    intro g
    dsimp [LHS_g]
    have hvpos : 0 < r.v := lt_trans zero_lt_one r.v_gt
    have hfresh_nn : 0 ≤ ∏ idx : Fin (J + F.ell),
        if ν.shared g.val idx ∨ idx ∈ A_retr g then 1 else tiltedMu F P n g.val (tt.2.1 g.val idx) := by
      apply Finset.prod_nonneg (fun idx _ => ?_)
      split_ifs
      · exact zero_le_one
      · exact htilted_nn g _
    have hact_nn : 0 ≤ ∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (ss.2.1 g.val idx) :=
      Finset.prod_nonneg (fun idx _ => htilted_nn g _)
    have hgm_nn : 0 ≤ P.groupMemoryMass F n g.val (s.2.2 g) :=
      groupMemoryMass_nonneg F n (htilted_nn g) (s.2.2 g)
    have hV_nn : 0 ≤ (P.V g.val) ^ (-((A_retr g).card : ℤ)) := zpow_nonneg (hVpos g.val).le _
    have hrho_nn : 0 ≤ r.rho ^ (zeroMemoryIndices (s.2.2 g)).card := pow_nonneg r.rho_pos.le _
    have hv_nn : 0 ≤ r.v ^ (A_retr g).card / r.v ^ (B g).card :=
      div_nonneg (pow_nonneg hvpos.le _) (pow_nonneg hvpos.le _)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (Nat.cast_nonneg _) hact_nn)
              hgm_nn)
            hfresh_nn)
          hV_nn)
        hrho_nn)
      hv_nn
  have hprod_le : (∏ g : P.BigGroup, LHS_g g) ≤ ∏ g : P.BigGroup, RHS_g g := by
    have hind : ∀ s : Finset P.BigGroup, (∏ g ∈ s, LHS_g g) ≤ ∏ g ∈ s, RHS_g g := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        exact mul_le_mul (hg_le a) ih (Finset.prod_nonneg (fun x _ => hLHS_g_nn x))
          (le_trans (hLHS_g_nn a) (hg_le a))
    exact hind Finset.univ
  have hprod_LHS_eq : (∏ g : P.BigGroup,
      ((retrievalFibre (s.2.2 g) (A_retr g)
        (fun idx => ⟨tt.2.1 g.val idx, -(delta : ZMod (tt.2.1 g.val idx).val)⟩)).card : ℝ)) *
      (∏ g : P.BigGroup,
        ((∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (ss.2.1 g.val idx)) *
          P.groupMemoryMass F n g.val (s.2.2 g))) *
      freshBigFactor F n ν A_retr tt.2.1 *
      (∏ g : P.BigGroup, (P.V g.val) ^ (-((A_retr g).card : ℤ))) *
      r.rho ^ (∑ g : P.BigGroup, (zeroMemoryIndices (s.2.2 g)).card) *
      (∏ g : P.BigGroup, (r.v ^ (A_retr g).card / r.v ^ (B g).card)) =
      ∏ g : P.BigGroup, LHS_g g := by
    unfold freshBigFactor
    rw [← Finset.prod_pow_eq_pow_sum]
    simp only [LHS_g, Finset.prod_mul_distrib]
    ring
  have hprod_RHS_eq : (∏ g : P.BigGroup, RHS_g g) =
      (colRevConst F m ^ Fintype.card P.BigGroup) *
      (∏ g : P.BigGroup,
        ((∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (tt.2.1 g.val idx)) *
          P.groupMemoryMass F n g.val (t.2.2 g))) *
      (∏ g : P.BigGroup, colBigMapSum F r n ν (-delta) tt g (A_retr g) (B g) (ss.2.1 g.val)) := by
    simp only [RHS_g, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    ring
  have hdamp_t : smallDamping F J t.1 *
      r.rho ^ (∑ g : P.BigGroup, (zeroMemoryIndices (t.2.2 g)).card) ≤ 1 :=
    source_damp_le_one F r J t.1 tt.2.1 ht_phys _
  have haux_nn : 0 ≤ ν.auxMass u := by
    unfold Pattern.auxMass
    exact Finset.prod_nonneg (fun g _ =>
      Finset.prod_nonneg (fun j _ => (mu_pos_of_V_pos g (hVpos g) (u g j)).le))
  have hS_nn : 0 ≤ S_prod := by
    apply Finset.prod_nonneg (fun g _ => ?_)
    split_ifs
    · exact smallGroupWeight_nonneg F J g (hVpos g.val) _
    · exact le_refl 0
  have hbase_nn : 0 ≤ smallBaseMass F P J := smallBaseMass_nonneg F P J hVpos
  have hwt_t_nn : 0 ≤ P.memoryWeight r.v t := memoryWeight_nonneg r t
  have hfactor_lhs :
      (∏ g : P.BigGroup,
        ((retrievalFibre (s.2.2 g) (A_retr g)
          (fun idx => ⟨tt.2.1 g.val idx, -(delta : ZMod (tt.2.1 g.val idx).val)⟩)).card : ℝ)) *
        (P.memoryMass F J n s *
          |rawEdgeWeight A n r.rho ν u ss tt (B, ⟨A_retr, f₀⟩)| *
          P.memoryWeight r.v s) =
      (ν.auxMass u * smallBaseMass F P J * P.memoryWeight r.v t * S_prod *
        (∏ g : P.BigGroup, LHS_g g)) *
        (smallDamping F J t.1 *
          r.rho ^ (∑ g : P.BigGroup, (zeroMemoryIndices (t.2.2 g)).card)) := by
    rw [abs_of_nonneg (rawEdgeWeight_nonneg r n A ν u ss tt (B, ⟨A_retr, f₀⟩) hVpos htilted_nn),
      hmass_s, hw_eq]
    unfold rawEdgeWeight
    have htd : smallDamping F J tt.1 = smallDamping F J t.1 := rfl
    have hsd : smallDamping F J ss.1 = smallDamping F J s.1 := rfl
    have htz : (∑ g : P.BigGroup, (zeroMemoryIndices (tt.2.2 g)).card) =
        ∑ g : P.BigGroup, (zeroMemoryIndices (t.2.2 g)).card := rfl
    have hsz : (∑ g : P.BigGroup, (zeroMemoryIndices (ss.2.2 g)).card) =
        ∑ g : P.BigGroup, (zeroMemoryIndices (s.2.2 g)).card := rfl
    rw [htd, hsd, htz, hsz, pow_add, ← hprod_LHS_eq, ← hsmall_prod]
    dsimp [ss, tt, permuteActive]
    ring
  rw [hfactor_lhs]
  calc (ν.auxMass u * smallBaseMass F P J * P.memoryWeight r.v t * S_prod *
          (∏ g : P.BigGroup, LHS_g g)) *
          (smallDamping F J t.1 *
            r.rho ^ (∑ g : P.BigGroup, (zeroMemoryIndices (t.2.2 g)).card))
      ≤ (ν.auxMass u * smallBaseMass F P J * P.memoryWeight r.v t * S_prod *
          (∏ g : P.BigGroup, LHS_g g)) * 1 := by
        apply mul_le_mul_of_nonneg_left hdamp_t
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg haux_nn hbase_nn) hwt_t_nn) hS_nn)
          (Finset.prod_nonneg (fun g _ => hLHS_g_nn g))
    _ = (ν.auxMass u * smallBaseMass F P J * P.memoryWeight r.v t * S_prod) *
          (∏ g : P.BigGroup, LHS_g g) := mul_one _
    _ ≤ (ν.auxMass u * smallBaseMass F P J * P.memoryWeight r.v t * S_prod) *
          (∏ g : P.BigGroup, RHS_g g) := by
        apply mul_le_mul_of_nonneg_left hprod_le
        exact mul_nonneg (mul_nonneg (mul_nonneg haux_nn hbase_nn) hwt_t_nn) hS_nn
    _ = ν.auxMass u * P.memoryMass F J n t * P.memoryWeight r.v t *
          (colRevConst F m ^ Fintype.card P.BigGroup) *
          colLabelTerm F r n ν (-delta) tt A_retr B ss.2.1 := by
        rw [hprod_RHS_eq, hmass_t]
        unfold colLabelTerm
        dsimp [S_prod, tt, ss, permuteActive]
        ring

/-- Pointwise bound on `colSourceMapSum` at a valid source `s`. -/
lemma colSourceMapSum_le_of_valid (F : FixedData) (r : MemoryParameters F) (n : ℕ) (theta : ℝ)
    (i : Fin n) (A : Model F P J m)
    (hVlo : ∀ g : P.Group, F.vMin ≤ P.V g)
    (hVhi : ∀ g : P.Group, P.V g ≤ F.vMax)
    (htilted_nn : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (π τ : P.Permutations (J + F.ell)) (v : Fin A.patternCount) (u : P.Aux J)
    (B A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)))
    (s t : P.MemoryState (J + F.ell))
    (f₀ : (g : P.BigGroup) → {idx : Fin (J + F.ell) // idx ∈ A_retr g} → Fin (s.2.2 g).card)
    (hval₀ : edgeChoiceValid A .all i s t (π, τ, v, u, (B, ⟨A_retr, f₀⟩))) :
    colSourceMapSum F r n theta i A t π τ v u B A_retr s ≤
      patternSup A v * (A.pattern v).auxMass u * P.memoryMass F J n t * P.memoryWeight r.v t *
        (colRevConst F m ^ Fintype.card P.BigGroup) *
        colLabelTerm F r n (A.pattern v)
          (-edgeDelta A (A.pattern v) (edgeForward i) (permuteActive τ t).2.1 u)
          (permuteActive τ t) A_retr B (P.act π s.2.1) := by
  classical
  let ν := A.pattern v
  let ss := permuteActive π s
  let tt := permuteActive τ t
  let delta := edgeDelta A ν (edgeForward i) tt.2.1 u
  have hVpos : ∀ g : P.Group, 0 < P.V g := fun g => lt_of_lt_of_le F.vMin_pos (hVlo g)
  let FibSet : Finset ((g : P.BigGroup) → {idx : Fin (J + F.ell) // idx ∈ A_retr g} → Fin (s.2.2 g).card) :=
    Fintype.piFinset (fun g : P.BigGroup =>
      retrievalFibre (s.2.2 g) (A_retr g)
        (fun idx => ⟨tt.2.1 g.val idx, -(delta : ZMod (tt.2.1 g.val idx).val)⟩))
  have hsub : Finset.univ.filter (fun f => edgeChoiceValid A .all i s t (π, τ, v, u, (B, ⟨A_retr, f⟩))) ⊆
      FibSet := by
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp only [FibSet, Fintype.mem_piFinset]
    intro g
    obtain ⟨_, _, hcomp, _, _, hg⟩ := hf.1
    obtain ⟨_, _, hinj, hprom, hmem⟩ := hg g
    have hdelta_eq : edgeDelta A ν (edgeForward i) ss.2.1 u = delta :=
      edgeDelta_eq_of_compatible A ν (edgeForward i) ss.2.1 tt.2.1 u hcomp
    have hret : ∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_retr g},
        (memoryEntry (s.2.2 g) (f g idx)).1 = tt.2.1 g.val idx.val ∧
        (memoryEntry (s.2.2 g) (f g idx)).2 +
          (delta : ZMod (memoryEntry (s.2.2 g) (f g idx)).1.val) = 0 := by
      intro idx
      refine ⟨(hprom idx).1, ?_⟩
      have h2 : (memoryEntry (s.2.2 g) (f g idx)).2 +
          (edgeDelta A ν (edgeForward i) ss.2.1 u : ZMod (memoryEntry (s.2.2 g) (f g idx)).1.val) = 0 :=
        (hprom idx).2.1
      rwa [hdelta_eq] at h2
    have ht_eq : t.2.2 g = translateMemory delta
        (deleteMemoryIndices (s.2.2 g) (Finset.univ.image (f g)) +
          storedMemory (ss.2.1 g.val) (B g)) := by
      have hm : t.2.2 g = translateMemory (edgeDelta A ν (edgeForward i) ss.2.1 u)
          (deleteMemoryIndices (s.2.2 g) (Finset.univ.image (f g)) +
            storedMemory (ss.2.1 g.val) (B g)) := hmem
      rwa [hdelta_eq] at hm
    exact (valid_bigGroup_decomp delta g (ss.2.1 g.val) (tt.2.1 g.val)
      (s.2.2 g) (t.2.2 g) (B g) (A_retr g) (f g) hinj hret ht_eq).1
  have hcard_le : ((Finset.univ.filter (fun f =>
        edgeChoiceValid A .all i s t (π, τ, v, u, (B, ⟨A_retr, f⟩)))).card : ℝ) ≤
      ∏ g : P.BigGroup,
        ((retrievalFibre (s.2.2 g) (A_retr g)
          (fun idx => ⟨tt.2.1 g.val idx, -(delta : ZMod (tt.2.1 g.val idx).val)⟩)).card : ℝ) := by
    have hc : (Finset.univ.filter (fun f =>
        edgeChoiceValid A .all i s t (π, τ, v, u, (B, ⟨A_retr, f⟩)))).card ≤
        ∏ g : P.BigGroup,
          (retrievalFibre (s.2.2 g) (A_retr g)
            (fun idx => ⟨tt.2.1 g.val idx, -(delta : ZMod (tt.2.1 g.val idx).val)⟩)).card := by
      calc (Finset.univ.filter (fun f =>
            edgeChoiceValid A .all i s t (π, τ, v, u, (B, ⟨A_retr, f⟩)))).card
          ≤ FibSet.card := Finset.card_le_card hsub
        _ = ∏ g : P.BigGroup,
              (retrievalFibre (s.2.2 g) (A_retr g)
                (fun idx => ⟨tt.2.1 g.val idx, -(delta : ZMod (tt.2.1 g.val idx).val)⟩)).card :=
            Fintype.card_piFinset _
    exact_mod_cast hc
  let K₀ : ℝ := P.memoryMass F J n s *
    |rawEdgeWeight A n r.rho ν u ss tt (B, ⟨A_retr, f₀⟩)| *
    P.memoryWeight r.v s
  have hK₀_nn : 0 ≤ K₀ :=
    mul_nonneg (mul_nonneg (memoryMass_nonneg F J n hVpos htilted_nn s) (abs_nonneg _))
      (memoryWeight_nonneg r s)
  have hterm_le : ∀ f ∈ Finset.univ.filter (fun f =>
        edgeChoiceValid A .all i s t (π, τ, v, u, (B, ⟨A_retr, f⟩))),
      P.memoryMass F J n s *
        ‖edgeChoiceCoefficient A n r.rho theta i s t (π, τ, v, u, (B, ⟨A_retr, f⟩))‖ *
        P.memoryWeight r.v s ≤
      patternSup A v * K₀ := by
    intro f _
    rw [edgeChoiceCoefficient_indep_f A n r.rho theta i s t π τ v u B A_retr f f₀]
    have hcoeff := edgeChoiceCoefficient_norm_le_patternSup A n r.rho theta i s t
      (π, τ, v, u, (B, ⟨A_retr, f₀⟩))
    calc P.memoryMass F J n s *
          ‖edgeChoiceCoefficient A n r.rho theta i s t (π, τ, v, u, (B, ⟨A_retr, f₀⟩))‖ *
          P.memoryWeight r.v s
        ≤ P.memoryMass F J n s *
            (patternSup A v * |rawEdgeWeight A n r.rho ν u ss tt (B, ⟨A_retr, f₀⟩)|) *
            P.memoryWeight r.v s := by
          apply mul_le_mul_of_nonneg_right _ (memoryWeight_nonneg r s)
          exact mul_le_mul_of_nonneg_left hcoeff (memoryMass_nonneg F J n hVpos htilted_nn s)
      _ = patternSup A v * K₀ := by
          dsimp [K₀]
          ring
  have hrev := col_rawEdge_reversal_le F r n i A hVlo hVhi htilted_nn π τ v u B A_retr s t f₀ hval₀
  calc colSourceMapSum F r n theta i A t π τ v u B A_retr s
      = ∑ f ∈ Finset.univ.filter (fun f =>
          edgeChoiceValid A .all i s t (π, τ, v, u, (B, ⟨A_retr, f⟩))),
          P.memoryMass F J n s *
            ‖edgeChoiceCoefficient A n r.rho theta i s t (π, τ, v, u, (B, ⟨A_retr, f⟩))‖ *
            P.memoryWeight r.v s := by
        unfold colSourceMapSum
        rw [← Finset.sum_filter]
    _ ≤ ∑ _f ∈ Finset.univ.filter (fun f =>
          edgeChoiceValid A .all i s t (π, τ, v, u, (B, ⟨A_retr, f⟩))),
          (patternSup A v * K₀) :=
        Finset.sum_le_sum hterm_le
    _ = ((Finset.univ.filter (fun f =>
          edgeChoiceValid A .all i s t (π, τ, v, u, (B, ⟨A_retr, f⟩)))).card : ℝ) *
          (patternSup A v * K₀) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∏ g : P.BigGroup,
          ((retrievalFibre (s.2.2 g) (A_retr g)
            (fun idx => ⟨tt.2.1 g.val idx, -(delta : ZMod (tt.2.1 g.val idx).val)⟩)).card : ℝ)) *
          (patternSup A v * K₀) :=
        mul_le_mul_of_nonneg_right hcard_le (mul_nonneg (patternSup_nonneg A v) hK₀_nn)
    _ = patternSup A v *
          ((∏ g : P.BigGroup,
            ((retrievalFibre (s.2.2 g) (A_retr g)
              (fun idx => ⟨tt.2.1 g.val idx, -(delta : ZMod (tt.2.1 g.val idx).val)⟩)).card : ℝ)) *
            K₀) := by ring
    _ ≤ patternSup A v *
          (ν.auxMass u * P.memoryMass F J n t * P.memoryWeight r.v t *
            (colRevConst F m ^ Fintype.card P.BigGroup) *
            colLabelTerm F r n ν (-delta) tt A_retr B ss.2.1) :=
        mul_le_mul_of_nonneg_left hrev (patternSup_nonneg A v)
    _ = patternSup A v * ν.auxMass u * P.memoryMass F J n t * P.memoryWeight r.v t *
          (colRevConst F m ^ Fintype.card P.BigGroup) *
          colLabelTerm F r n ν (-delta) tt A_retr B (P.act π s.2.1) := by
        dsimp [ss, permuteActive]
        ring

/-! ### Source sum bound via injectivity of `s ↦ P.act π s.2.1` -/

lemma valid_source_small_and_mem (A : Model F P J m) {n : ℕ} (i : Fin n)
    (π τ : P.Permutations (J + F.ell)) (v : Fin A.patternCount) (u : P.Aux J)
    (B A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)))
    (s t : P.MemoryState (J + F.ell))
    (f : (g : P.BigGroup) → {idx : Fin (J + F.ell) // idx ∈ A_retr g} → Fin (s.2.2 g).card)
    (hv : edgeChoiceValid A .all i s t (π, τ, v, u, (B, ⟨A_retr, f⟩))) :
    let ν := A.pattern v
    let tt := permuteActive τ t
    let delta := edgeDelta A ν (edgeForward i) tt.2.1 u
    s.1 = translateSmallResidues (-delta) t.1 ∧
    ∀ g : P.BigGroup,
      s.2.2 g = (translateMemory (-delta) (t.2.2 g) - storedMemory ((P.act π s.2.1) g.val) (B g)) +
        (A_retr g).val.map (fun idx => ⟨tt.2.1 g.val idx, -(delta : ZMod (tt.2.1 g.val idx).val)⟩) := by
  intro ν tt delta
  let ss := permuteActive π s
  obtain ⟨_, _, hcomp, _, ht_small_raw, hg⟩ := hv.1
  have hd : edgeDelta A ν (edgeForward i) ss.2.1 u = delta :=
    edgeDelta_eq_of_compatible A ν (edgeForward i) ss.2.1 tt.2.1 u hcomp
  have ht_small : t.1 = translateSmallResidues delta s.1 := by
    have h1 : t.1 = translateSmallResidues (edgeDelta A ν (edgeForward i) ss.2.1 u) s.1 :=
      ht_small_raw
    rwa [hd] at h1
  refine ⟨by rw [ht_small, translateSmallResidues_neg_cancel], fun g => ?_⟩
  obtain ⟨_, _, hinj, hprom, hmem⟩ := hg g
  have hret : ∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_retr g},
      (memoryEntry (s.2.2 g) (f g idx)).1 = tt.2.1 g.val idx.val ∧
      (memoryEntry (s.2.2 g) (f g idx)).2 +
        (delta : ZMod (memoryEntry (s.2.2 g) (f g idx)).1.val) = 0 := by
    intro idx
    refine ⟨(hprom idx).1, ?_⟩
    have h2 : (memoryEntry (s.2.2 g) (f g idx)).2 +
        (edgeDelta A ν (edgeForward i) ss.2.1 u : ZMod (memoryEntry (s.2.2 g) (f g idx)).1.val) = 0 :=
      (hprom idx).2.1
    rwa [hd] at h2
  have ht_eq : t.2.2 g = translateMemory delta
      (deleteMemoryIndices (s.2.2 g) (Finset.univ.image (f g)) +
        storedMemory (ss.2.1 g.val) (B g)) := by
    have hm : t.2.2 g = translateMemory (edgeDelta A ν (edgeForward i) ss.2.1 u)
        (deleteMemoryIndices (s.2.2 g) (Finset.univ.image (f g)) +
          storedMemory (ss.2.1 g.val) (B g)) := hmem
    rwa [hd] at hm
  exact (valid_bigGroup_decomp delta g (ss.2.1 g.val) (tt.2.1 g.val)
    (s.2.2 g) (t.2.2 g) (B g) (A_retr g) (f g) hinj hret ht_eq).2.2.2.2

/-- Summing `colSourceMapSum` over `s ∈ S` is bounded by the sum of `colLabelTerm` over `a : P.Labels (J + F.ell)`. -/
lemma sum_source_colSourceMapSum_le (F : FixedData) (r : MemoryParameters F) (n : ℕ) (theta : ℝ)
    (i : Fin n) (A : Model F P J m)
    (hVlo : ∀ g : P.Group, F.vMin ≤ P.V g)
    (hVhi : ∀ g : P.Group, P.V g ≤ F.vMax)
    (htilted_nn : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (π τ : P.Permutations (J + F.ell)) (v : Fin A.patternCount) (u : P.Aux J)
    (B A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)))
    (t : P.MemoryState (J + F.ell))
    (S : Finset (P.MemoryState (J + F.ell))) :
    (∑ s ∈ S, colSourceMapSum F r n theta i A t π τ v u B A_retr s) ≤
      patternSup A v * (A.pattern v).auxMass u * P.memoryMass F J n t * P.memoryWeight r.v t *
        (colRevConst F m ^ Fintype.card P.BigGroup) *
        ∑ a : P.Labels (J + F.ell),
          colLabelTerm F r n (A.pattern v)
            (-edgeDelta A (A.pattern v) (edgeForward i) (permuteActive τ t).2.1 u)
            (permuteActive τ t) A_retr B a := by
  classical
  set ν := A.pattern v
  set tt := permuteActive τ t
  set delta := edgeDelta A ν (edgeForward i) tt.2.1 u
  have hVpos : ∀ g : P.Group, 0 < P.V g := fun g => lt_of_lt_of_le F.vMin_pos (hVlo g)
  let S_val := S.filter (fun s =>
    ∃ f : (g : P.BigGroup) → {idx : Fin (J + F.ell) // idx ∈ A_retr g} → Fin (s.2.2 g).card,
      edgeChoiceValid A .all i s t (π, τ, v, u, (B, ⟨A_retr, f⟩)))
  have hsum_filter : (∑ s ∈ S, colSourceMapSum F r n theta i A t π τ v u B A_retr s) =
      ∑ s ∈ S_val, colSourceMapSum F r n theta i A t π τ v u B A_retr s := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ S)
    intro s hs hnot
    simp only [S_val, Finset.mem_filter, hs, true_and, not_exists] at hnot
    unfold colSourceMapSum
    apply Finset.sum_eq_zero
    intro f _
    rw [if_neg (hnot f)]
  have hinj : Set.InjOn (fun s : P.MemoryState (J + F.ell) => P.act π s.2.1) S_val := by
    intro s₁ hs₁ s₂ hs₂ heq
    simp only [] at heq
    obtain ⟨f₁, hv₁⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hs₁)).2
    obtain ⟨f₂, hv₂⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hs₂)).2
    obtain ⟨hs₁_sm, hs₁_mem⟩ := valid_source_small_and_mem A i π τ v u B A_retr s₁ t f₁ hv₁
    obtain ⟨hs₂_sm, hs₂_mem⟩ := valid_source_small_and_mem A i π τ v u B A_retr s₂ t f₂ hv₂
    have h1 : s₁.1 = s₂.1 := hs₁_sm.trans hs₂_sm.symm
    have h2 : s₁.2.1 = s₂.2.1 := by
      funext g j
      have hj := congrArg (fun a : P.Labels (J + F.ell) => a g ((π g).symm j)) heq
      simpa [PrimeGroups.act] using hj
    have h3 : s₁.2.2 = s₂.2.2 := by
      funext g
      have hm₁ := hs₁_mem g
      have hm₂ := hs₂_mem g
      rw [heq] at hm₁
      exact hm₁.trans hm₂.symm
    cases s₁ with
    | mk y₁ p₁ =>
      cases p₁ with
      | mk a₁ m₁ =>
        cases s₂ with
        | mk y₂ p₂ =>
          cases p₂ with
          | mk a₂ m₂ =>
            dsimp at h1 h2 h3
            subst h1 h2 h3
            rfl
  let C_pref : ℝ := patternSup A v * ν.auxMass u * P.memoryMass F J n t * P.memoryWeight r.v t *
    (colRevConst F m ^ Fintype.card P.BigGroup)
  have hC_pref_nn : 0 ≤ C_pref := by
    dsimp [C_pref]
    have haux_nn : 0 ≤ ν.auxMass u := by
      unfold Pattern.auxMass
      exact Finset.prod_nonneg (fun g _ =>
        Finset.prod_nonneg (fun j _ => (mu_pos_of_V_pos g (hVpos g) (u g j)).le))
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (patternSup_nonneg A v) haux_nn)
      (memoryMass_nonneg F J n hVpos htilted_nn t)) (memoryWeight_nonneg r t))
      (pow_nonneg (colRevConst_pos F m).le _)
  have hsum_img : (∑ s ∈ S_val, colLabelTerm F r n ν (-delta) tt A_retr B (P.act π s.2.1)) ≤
      ∑ a : P.Labels (J + F.ell), colLabelTerm F r n ν (-delta) tt A_retr B a := by
    rw [← Finset.sum_image hinj]
    exact Finset.sum_le_univ_sum_of_nonneg (colLabelTerm_nonneg F r n hVpos htilted_nn ν (-delta) tt A_retr B)
  rw [hsum_filter]
  calc (∑ s ∈ S_val, colSourceMapSum F r n theta i A t π τ v u B A_retr s)
      ≤ ∑ s ∈ S_val, C_pref * colLabelTerm F r n ν (-delta) tt A_retr B (P.act π s.2.1) := by
        apply Finset.sum_le_sum
        intro s hs
        obtain ⟨f₀, hv₀⟩ := (Finset.mem_filter.mp hs).2
        exact colSourceMapSum_le_of_valid F r n theta i A hVlo hVhi htilted_nn
          π τ v u B A_retr s t f₀ hv₀
    _ = C_pref * ∑ s ∈ S_val, colLabelTerm F r n ν (-delta) tt A_retr B (P.act π s.2.1) := by
        rw [← Finset.mul_sum]
    _ ≤ C_pref * ∑ a : P.Labels (J + F.ell), colLabelTerm F r n ν (-delta) tt A_retr B a :=
        mul_le_mul_of_nonneg_left hsum_img hC_pref_nn

/-! ### Main column bound theorem `col_tsum_le` -/

/-- Column bound: absolute column tsum dominated by `L^Ca` times target mass and weight. -/
theorem col_tsum_le (F : FixedData) (r : MemoryParameters F) (m : ℕ) (C₁ : ℝ) :
    ∃ Ca : ℝ, ∀ J : ℕ, ∃ x₀ : ℝ, ∀ x : ℝ, x ≥ x₀ → ∀ P : PrimeGroups,
      P.Admissible F x → ∀ A : Model F P J m, A.patternMass ≤ (L x) ^ C₁ →
      ∀ (theta : ℝ) (i : Fin (N x)) (t : P.MemoryState (J + F.ell)),
        ∑' s, P.memoryMass F J (N x) s *
          ‖((absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t : ℝ) : ℂ)‖ *
          P.memoryWeight r.v s ≤
          (L x) ^ Ca * P.memoryMass F J (N x) t * P.memoryWeight r.v t := by
  classical
  obtain ⟨Cprom, hCprom_pos, hCprom⟩ :=
    promo_allmaps_bound r.rho r.rho_pos r.rho_lt (F.ell + m)
  obtain ⟨Csmall0, hCsmall0_pos, hCsmall0⟩ :=
    small_count_damp F.q F.q_pos F.q_lt F.ell
  let Cbig := colRevConst F m * bigGroupConst F r m Cprom
  have hCbig_ge : 1 ≤ Cbig := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ colRevConst F m * bigGroupConst F r m Cprom :=
        mul_le_mul (colRevConst_ge_one F m) (bigGroupConst_ge_one F r m Cprom)
          zero_le_one (colRevConst_pos F m).le
  have hCbig_pos : 0 < Cbig := lt_of_lt_of_le zero_lt_one hCbig_ge
  let Csmall := max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)
  have hCsmall_ge : 1 ≤ Csmall := le_max_left _ _
  have hCsmall_pos : 0 < Csmall := lt_of_lt_of_le zero_lt_one hCsmall_ge
  let Kbig : ℝ := F.C₀ * Real.log Cbig
  let Ksmall : ℝ := F.C₀ * Real.log Csmall
  have hKbig_nn : 0 ≤ Kbig := mul_nonneg F.C₀_pos.le (Real.log_nonneg hCbig_ge)
  have hKsmall_nn : 0 ≤ Ksmall := mul_nonneg F.C₀_pos.le (Real.log_nonneg hCsmall_ge)
  refine ⟨C₁ + Kbig + Ksmall, fun J => ?_⟩
  let xfact : ℝ := 10 * ((taylorTerms F).factorial : ℝ)
  refine ⟨max 3 (Real.exp xfact), fun x hx P hP A hA theta i t => ?_⟩
  have hx3 : 3 ≤ x := le_trans (le_max_left _ _) hx
  have hxexp : Real.exp xfact ≤ x := le_trans (le_max_right _ _) hx
  have hL1 : 1 < L x := one_lt_L hx3
  have hLpos : 0 < L x := lt_trans zero_lt_one hL1
  have hLfact : xfact ≤ L x := by
    have hlog := Real.log_le_log (Real.exp_pos _) hxexp
    rwa [Real.log_exp] at hlog
  have hx1 : 1 ≤ L x := hL1.le
  have hL10 : 10 * ((taylorTerms F).factorial : ℝ) ≤ L x := hLfact
  have hVlo : ∀ g : P.Group, F.vMin ≤ P.V g := fun g => (hP.2.2.2.2.1 g).1
  have hVhi : ∀ g : P.Group, P.V g ≤ F.vMax := fun g => (hP.2.2.2.2.1 g).2
  have hVpos : ∀ g : P.Group, 0 < P.V g := fun g => V_pos_of_adm hP g
  have hVne : ∀ g : P.Group, P.V g ≠ 0 := fun g => ne_of_gt (hVpos g)
  have htilted_nn : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P (N x) g.val p :=
    fun g p => (tiltedMu_pos hx1 hP (N x) rfl hL10 g p).le
  have htilted_sum : ∀ g : P.BigGroup, ∑ p : P.Prime g.val, tiltedMu F P (N x) g.val p ≤ 2 :=
    fun g => tiltedMu_sum_le_two hx1 hP (N x) rfl hL10 g
  have hcard_big : ((Fintype.card P.BigGroup : ℕ) : ℝ) ≤ F.C₀ * Real.log (L x) := by
    have hle : (P.bigGroups.card : ℝ) ≤ F.C₀ * T x := hP.2.2.2.1
    have hcard_eq : (Fintype.card P.BigGroup : ℝ) = (P.bigGroups.card : ℝ) := by
      rw [PrimeGroups.bigGroups]
      simp [Fintype.card_subtype]
    rw [hcard_eq]
    exact hle
  have hcard_small : ((Fintype.card P.SmallGroup : ℕ) : ℝ) ≤ F.C₀ * Real.log (L x) := by
    have hle : (P.smallGroups.card : ℝ) ≤ F.C₀ * T x := hP.2.1
    have hcard_eq : (Fintype.card P.SmallGroup : ℝ) = (P.smallGroups.card : ℝ) := by
      rw [PrimeGroups.smallGroups]
      simp [Fintype.card_subtype]
    rw [hcard_eq]
    exact hle
  have hbig_pow : Cbig ^ Fintype.card P.BigGroup ≤ (L x) ^ Kbig :=
    pow_groups_le_rpow Cbig hCbig_pos _ F.C₀ (L x) Kbig
      F.C₀_pos hL1 hKbig_nn (le_refl _) hcard_big
  have hsmall_pow : Csmall ^ Fintype.card P.SmallGroup ≤ (L x) ^ Ksmall :=
    pow_groups_le_rpow Csmall hCsmall_pos _ F.C₀ (L x) Ksmall
      F.C₀_pos hL1 hKsmall_nn (le_refl _) hcard_small
  have hfin : Set.Finite {s : P.MemoryState (J + F.ell) |
      absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t ≠ 0} :=
    col_kernel_set_finite A r.rho theta i t
  have htsum_eq : (∑' s, P.memoryMass F J (N x) s *
        ‖((absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t : ℝ) : ℂ)‖ *
        P.memoryWeight r.v s) =
      ∑ s ∈ hfin.toFinset,
        P.memoryMass F J (N x) s *
          absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t *
          P.memoryWeight r.v s := by
    rw [tsum_eq_sum]
    · apply Finset.sum_congr rfl
      intro s _
      rw [norm_cast_absolute]
    · intro s hs
      have hnot : s ∉ {s : P.MemoryState (J + F.ell) |
          absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t ≠ 0} :=
        fun hcon => hs (hfin.mem_toFinset.mpr hcon)
      simp only [Set.mem_setOf_eq, ne_eq, not_not] at hnot
      rw [norm_cast_absolute, hnot, mul_zero, zero_mul]
  let P_base : ℝ := (bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
    Csmall ^ Fintype.card P.SmallGroup
  let MW_t : ℝ := P.memoryMass F J (N x) t * P.memoryWeight r.v t *
    (colRevConst F m ^ Fintype.card P.BigGroup)
  have hMW_t_nn : 0 ≤ MW_t :=
    mul_nonneg (mul_nonneg (memoryMass_nonneg F J (N x) hVpos htilted_nn t) (memoryWeight_nonneg r t))
      (pow_nonneg (colRevConst_pos F m).le _)
  have hcol_fin_le : ∑ s ∈ hfin.toFinset,
        P.memoryMass F J (N x) s *
          absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t *
          P.memoryWeight r.v s ≤
      A.patternMass * (Cbig ^ Fintype.card P.BigGroup) *
        (Csmall ^ Fintype.card P.SmallGroup) *
        P.memoryMass F J (N x) t * P.memoryWeight r.v t := by
    have hswap : (∑ s ∈ hfin.toFinset,
          P.memoryMass F J (N x) s *
            absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t *
            P.memoryWeight r.v s) =
        edgeSymmetryFactor P (J + F.ell) *
          ∑ π : P.Permutations (J + F.ell),
            ∑ τ : P.Permutations (J + F.ell),
              ∑ v : Fin A.patternCount,
                ∑ u : P.Aux J,
                  ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                    ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                      ∑ s ∈ hfin.toFinset,
                        colSourceMapSum F r (N x) theta i A t π τ v u B A_retr s := by
      simp_rw [source_choice_sum_eq_colSourceMapSum F r (N x) theta i A _ t, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl (fun π _ => ?_)
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl (fun τ _ => ?_)
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl (fun v _ => ?_)
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl (fun B _ => Finset.sum_comm)
    rw [hswap]
    have hBA_le : ∀ (π τ : P.Permutations (J + F.ell)) (v : Fin A.patternCount) (u : P.Aux J),
        (∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
          ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
            ∑ s ∈ hfin.toFinset,
              colSourceMapSum F r (N x) theta i A t π τ v u B A_retr s) ≤
        (patternSup A v * (A.pattern v).auxMass u * MW_t) * P_base := by
      intro π τ v u
      have haux_nn : 0 ≤ (A.pattern v).auxMass u := by
        unfold Pattern.auxMass
        exact Finset.prod_nonneg (fun g _ =>
          Finset.prod_nonneg (fun j _ => (mu_pos_of_V_pos g (hVpos g) (u g j)).le))
      calc (∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
            ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
              ∑ s ∈ hfin.toFinset,
                colSourceMapSum F r (N x) theta i A t π τ v u B A_retr s)
          ≤ ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
              ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                (patternSup A v * (A.pattern v).auxMass u * MW_t) *
                  ∑ a : P.Labels (J + F.ell),
                    colLabelTerm F r (N x) (A.pattern v)
                      (-edgeDelta A (A.pattern v) (edgeForward i) (permuteActive τ t).2.1 u)
                      (permuteActive τ t) A_retr B a := by
            apply Finset.sum_le_sum (fun B _ => Finset.sum_le_sum (fun A_retr _ => ?_))
            have h := sum_source_colSourceMapSum_le F r (N x) theta i A hVlo hVhi htilted_nn
              π τ v u B A_retr t hfin.toFinset
            dsimp [MW_t]
            linarith [h]
        _ = (patternSup A v * (A.pattern v).auxMass u * MW_t) *
              ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  ∑ a : P.Labels (J + F.ell),
                    colLabelTerm F r (N x) (A.pattern v)
                      (-edgeDelta A (A.pattern v) (edgeForward i) (permuteActive τ t).2.1 u)
                      (permuteActive τ t) A_retr B a := by
            simp_rw [← Finset.mul_sum]
        _ ≤ (patternSup A v * (A.pattern v).auxMass u * MW_t) * P_base := by
            apply mul_le_mul_of_nonneg_left
              (sum_colLabelTerm_le F r (N x) Cprom Csmall0 hCsmall0_pos hCprom hCsmall0
                hVlo htilted_nn htilted_sum (A.pattern v)
                (-edgeDelta A (A.pattern v) (edgeForward i) (permuteActive τ t).2.1 u)
                (permuteActive τ t))
            exact mul_nonneg (mul_nonneg (patternSup_nonneg A v) haux_nn) hMW_t_nn
    have hc_sum : (∑ π : P.Permutations (J + F.ell),
          ∑ τ : P.Permutations (J + F.ell),
            ∑ v : Fin A.patternCount,
              ∑ u : P.Aux J,
                ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                    ∑ s ∈ hfin.toFinset,
                      colSourceMapSum F r (N x) theta i A t π τ v u B A_retr s) ≤
        ((Fintype.card (P.Permutations (J + F.ell)) : ℝ) ^ (2 : ℕ)) *
          (A.patternMass * MW_t * P_base) := by
      calc (∑ π : P.Permutations (J + F.ell),
            ∑ τ : P.Permutations (J + F.ell),
              ∑ v : Fin A.patternCount,
                ∑ u : P.Aux J,
                  ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                    ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                      ∑ s ∈ hfin.toFinset,
                        colSourceMapSum F r (N x) theta i A t π τ v u B A_retr s)
          ≤ ∑ _π : P.Permutations (J + F.ell),
              ∑ _τ : P.Permutations (J + F.ell),
                ∑ v : Fin A.patternCount,
                  ∑ u : P.Aux J,
                    (patternSup A v * (A.pattern v).auxMass u * MW_t) * P_base :=
            Finset.sum_le_sum (fun π _ => Finset.sum_le_sum (fun τ _ =>
              Finset.sum_le_sum (fun v _ => Finset.sum_le_sum (fun u _ => hBA_le π τ v u))))
        _ = ((Fintype.card (P.Permutations (J + F.ell)) : ℝ) ^ (2 : ℕ)) *
              (A.patternMass * MW_t * P_base) := by
            have hu : ∀ v : Fin A.patternCount,
                (∑ u : P.Aux J, (patternSup A v * (A.pattern v).auxMass u * MW_t) * P_base) =
                patternSup A v * (MW_t * P_base) := by
              intro v
              have h1 : (∑ u : P.Aux J, (patternSup A v * (A.pattern v).auxMass u * MW_t) * P_base) =
                  patternSup A v * (∑ u : P.Aux J, (A.pattern v).auxMass u) * (MW_t * P_base) := by
                rw [Finset.mul_sum, Finset.sum_mul]
                apply Finset.sum_congr rfl (fun u _ => by ring)
              rw [h1, auxMass_sum_eq_one (A.pattern v) hVne, mul_one]
            simp_rw [hu, ← Finset.sum_mul, sum_patternSup_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
    calc edgeSymmetryFactor P (J + F.ell) *
          ∑ π : P.Permutations (J + F.ell),
            ∑ τ : P.Permutations (J + F.ell),
              ∑ v : Fin A.patternCount,
                ∑ u : P.Aux J,
                  ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                    ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                      ∑ s ∈ hfin.toFinset,
                        colSourceMapSum F r (N x) theta i A t π τ v u B A_retr s
        ≤ edgeSymmetryFactor P (J + F.ell) *
            (((Fintype.card (P.Permutations (J + F.ell)) : ℝ) ^ (2 : ℕ)) *
              (A.patternMass * MW_t * P_base)) :=
          mul_le_mul_of_nonneg_left hc_sum (edgeSymmetryFactor_nonneg P (J + F.ell))
      _ = A.patternMass * (Cbig ^ Fintype.card P.BigGroup) *
            (Csmall ^ Fintype.card P.SmallGroup) *
            P.memoryMass F J (N x) t * P.memoryWeight r.v t := by
          unfold edgeSymmetryFactor
          have hcard_pos : (0 : ℝ) < (Fintype.card (P.Permutations (J + F.ell)) : ℝ) ^ (2 : ℕ) := by
            positivity
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard_pos), one_mul]
          dsimp [MW_t, P_base, Cbig]
          rw [mul_pow]
          ring
  rw [htsum_eq]
  calc ∑ s ∈ hfin.toFinset,
        P.memoryMass F J (N x) s *
          absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t *
          P.memoryWeight r.v s
      ≤ A.patternMass * (Cbig ^ Fintype.card P.BigGroup) *
          (Csmall ^ Fintype.card P.SmallGroup) *
          P.memoryMass F J (N x) t * P.memoryWeight r.v t := hcol_fin_le
    _ ≤ ((L x) ^ C₁) * ((L x) ^ Kbig) * ((L x) ^ Ksmall) *
          P.memoryMass F J (N x) t * P.memoryWeight r.v t := by
        have hCb0 : 0 ≤ Cbig ^ Fintype.card P.BigGroup := pow_nonneg hCbig_pos.le _
        have hCs0 : 0 ≤ Csmall ^ Fintype.card P.SmallGroup := pow_nonneg hCsmall_pos.le _
        have hL10' : 0 ≤ (L x) ^ C₁ := Real.rpow_nonneg hLpos.le _
        have hL20 : 0 ≤ (L x) ^ Kbig := Real.rpow_nonneg hLpos.le _
        have hL30 : 0 ≤ (L x) ^ Ksmall := Real.rpow_nonneg hLpos.le _
        have hmid : A.patternMass * (Cbig ^ Fintype.card P.BigGroup) *
            (Csmall ^ Fintype.card P.SmallGroup) ≤
            ((L x) ^ C₁) * ((L x) ^ Kbig) * ((L x) ^ Ksmall) := by
          apply mul_le_mul _ hsmall_pow hCs0 (mul_nonneg hL10' hL20)
          exact mul_le_mul hA hbig_pow hCb0 hL10'
        have hmw_nn : 0 ≤ P.memoryMass F J (N x) t * P.memoryWeight r.v t :=
          mul_nonneg (memoryMass_nonneg F J (N x) hVpos htilted_nn t) (memoryWeight_nonneg r t)
        have h1 := mul_le_mul_of_nonneg_right hmid hmw_nn
        linarith [h1]
    _ = (L x) ^ (C₁ + Kbig + Ksmall) * P.memoryMass F J (N x) t * P.memoryWeight r.v t := by
        rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos]

end Erdos821.P3Edge
