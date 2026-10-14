import Erdos821.P3High.PerAssignment

/-! A birth event is covered by the prescriptions of block values (one value per block, in
its pivot's group); summing the prescription bounds over the block values gives one tilted
moment per block, hence `(C / Pstar) ^ rank`. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3High

open Erdos821.Blueprint.Graph hiding BirthAddress EdgeChoice GhostChoice MemoryHistory
  TransferChoice TransferMode absoluteMemoryEdgeKernel absoluteMemoryGhostKernel
  absoluteScaledMemoryGhostKernel deleteMemoryIndices distinctMemoryExpression
  edgeChoiceCoefficient edgeChoiceValid edgeDelta edgeForward edgeSymmetryFactor freshBigFactor
  ghostBirthCount ghostChoiceValid ghostChoiceWeight ghostReversalFactor memoryEdgeKernel
  memoryEntry memoryGhostKernel permuteActive rawEdgeValid rawEdgeWeight retrievedIndices
  smallDamping smallOmega smallTargetFactor storedMemory transferModeAccept translateMemory
  translateParticle translateSmallResidues zeroBirthBatch zeroMemoryIndices
open Erdos821.S2Core Erdos821.P3Lowrank Erdos821.S2High

attribute [local instance] bmsFintype ghostChoiceFintype edgeChoiceFintype

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

instance pivotAssignmentFintype {n B : ℕ} (pi : Finset (Finset (AddrIdx P (J + F.ell) n B)))
    (hpi : BirthCollection pi) : Fintype (PivotAssignment pi hpi) := by
  unfold PivotAssignment
  infer_instance

/-- The prescribed value of an address of the collection: its block's value. -/
def blockTarget {n B : ℕ} (pi : Finset (Finset (AddrIdx P (J + F.ell) n B)))
    (hpi : BirthCollection pi) (values : PivotAssignment pi hpi)
    (j : AddrIdx P (J + F.ell) n B) : ℕ :=
  if hj : j ∈ performedAddressSet pi then (values (blockContaining pi hpi j hj)).val else 0

theorem prescribed_of_compatible {A : Model F P J m} {n B : ℕ} (H : MemoryHistory A n)
    (pi : Finset (Finset (AddrIdx P (J + F.ell) n B))) (hpi : BirthCollection pi)
    (values : PivotAssignment pi hpi) (hc : PivotCompatible H pi hpi values) :
    Prescribed B H (performedAddressSet pi) (blockTarget pi hpi values) := by
  intro j hj
  have hmem := blockContaining_mem pi hpi j hj
  have h := hc (blockContaining pi hpi j hj) j hmem
  refine ⟨h.1, ?_⟩
  rw [h.2]
  unfold blockTarget
  rw [dif_pos hj]

/-- The literal high-rank expression is covered by the prescriptions of block values. -/
theorem highRank_le_assign (A : Model F P J m) (n B : ℕ) (rho theta : ℝ)
    (pi : Finset (Finset (AddrIdx P (J + F.ell) n B))) (hpi : BirthCollection pi) :
    highRankHistoryExpression A n B rho theta pi ≤
      ∑ values : PivotAssignment pi hpi, ∑' H : MemoryHistory A n,
        (if H.Valid ∧ H.Truncated B ∧
            Prescribed B H (performedAddressSet pi) (blockTarget pi hpi values)
          then ‖H.Weight rho theta‖ else 0) := by
  unfold highRankHistoryExpression
  rw [tsum_truncR A n B _ (fun H hH => if_neg (fun h => hH h.2.1))]
  have htr : ∀ values : PivotAssignment pi hpi, (∑' H : MemoryHistory A n,
      (if H.Valid ∧ H.Truncated B ∧
          Prescribed B H (performedAddressSet pi) (blockTarget pi hpi values)
        then ‖H.Weight rho theta‖ else 0)) =
      ∑ d : BoundedHistoryData A n B,
        (if (mkH d).Valid ∧ (mkH d).Truncated B ∧
            Prescribed B (mkH d) (performedAddressSet pi) (blockTarget pi hpi values)
          then ‖(mkH d).Weight rho theta‖ else 0) :=
    fun values => tsum_truncR A n B _ (fun H hH => if_neg (fun h => hH h.2.1))
  rw [Finset.sum_congr rfl (fun v _ => htr v), Finset.sum_comm]
  apply Finset.sum_le_sum
  intro d _
  by_cases hc : (mkH d).Valid ∧ (mkH d).Truncated B ∧
      birthEvent ((mkH d).performedFin B) ((mkH d).valueFin B) pi
  · rw [if_pos hc]
    obtain ⟨values, hv⟩ := (birthEvent_iff_exists_pivotAssignment (mkH d) pi hpi).mp hc.2.2
    have hpre := prescribed_of_compatible (mkH d) pi hpi values hv
    calc ‖(mkH d).Weight rho theta‖
        = (if (mkH d).Valid ∧ (mkH d).Truncated B ∧
            Prescribed B (mkH d) (performedAddressSet pi) (blockTarget pi hpi values)
          then ‖(mkH d).Weight rho theta‖ else 0) := by rw [if_pos ⟨hc.1, hc.2.1, hpre⟩]
      _ ≤ _ := Finset.single_le_sum (f := fun values : PivotAssignment pi hpi =>
            if (mkH d).Valid ∧ (mkH d).Truncated B ∧
              Prescribed B (mkH d) (performedAddressSet pi) (blockTarget pi hpi values)
            then ‖(mkH d).Weight rho theta‖ else 0)
          (fun v _ => by split_ifs <;> simp) (Finset.mem_univ values)
  · rw [if_neg hc]
    exact Finset.sum_nonneg fun v _ => by split_ifs <;> simp

theorem muHat_le_block {n B : ℕ} (pi : Finset (Finset (AddrIdx P (J + F.ell) n B)))
    (hpi : BirthCollection pi) (C : {C // C ∈ pi}) (p : P.Prime (blockPivotGroup pi hpi C).val)
    (hμ : ∀ (g : P.BigGroup) (q : P.Prime g.val), 0 < tiltedMu F P n g.val q)
    (j : AddrIdx P (J + F.ell) n B) :
    muHat F P n (birthAddressGroup ((Fintype.equivFin _).symm j)) p.val ≤
      tiltedMu F P n (blockPivotGroup pi hpi C).val p := by
  by_cases hg : birthAddressGroup ((Fintype.equivFin (BirthAddress P (J + F.ell) n B)).symm j) =
      blockPivotGroup pi hpi C
  · rw [hg, muHat_of_mem]
  · have h0 : muHat F P n (birthAddressGroup ((Fintype.equivFin _).symm j)) p.val = 0 := by
      unfold muHat
      rw [dif_neg]
      intro hmem
      exact hg (big_groups_eq_of_common_prime _ _ p.val hmem p.property)
    rw [h0]
    exact (hμ _ _).le

/-- Summing the prescription products over the block values: one tilted moment per block. -/
theorem assign_sum_le {n B : ℕ} (x : ℝ) (hP : P.Admissible F x)
    (hcut : (n + 1 : ℝ) ≤ Real.exp ((L x) ^ F.c) / 2)
    (pi : Finset (Finset (AddrIdx P (J + F.ell) n B))) (hpi : BirthCollection pi) :
    ∑ values : PivotAssignment pi hpi, ∏ j ∈ performedAddressSet pi,
        2 * muHat F P n (birthAddressGroup ((Fintype.equivFin _).symm j))
          (blockTarget pi hpi values j) ≤
      (16 / (F.vMin * Real.exp ((L x) ^ F.c))) ^ birthRank pi := by
  have hmb := tiltedMu_group_mass_bounds F P x n hP hcut
  have hμ : ∀ (g : P.BigGroup) (q : P.Prime g.val), 0 < tiltedMu F P n g.val q :=
    fun g q => ((hmb g).1 q).1
  set X : ℝ := 2 / (F.vMin * Real.exp ((L x) ^ F.c)) with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact div_nonneg (by norm_num) (mul_nonneg F.vMin_pos.le (Real.exp_pos _).le)
  have hY : 16 / (F.vMin * Real.exp ((L x) ^ F.c)) = 8 * X := by rw [hX]; ring
  let H : (C : {C // C ∈ pi}) → P.Prime (blockPivotGroup pi hpi C).val → ℝ := fun C p =>
    ∏ j ∈ C.val, 2 * muHat F P n (birthAddressGroup ((Fintype.equivFin _).symm j)) p.val
  have hstep1 : ∀ values : PivotAssignment pi hpi,
      (∏ j ∈ performedAddressSet pi,
        2 * muHat F P n (birthAddressGroup ((Fintype.equivFin _).symm j))
          (blockTarget pi hpi values j)) = ∏ C : {C // C ∈ pi}, H C (values C) := by
    intro values
    unfold performedAddressSet
    rw [Finset.prod_biUnion (s := pi) (t := id) (by exact hpi.2), ← Finset.prod_coe_sort pi]
    apply Finset.prod_congr rfl
    intro C _
    apply Finset.prod_congr rfl
    intro j hj
    have hjU : j ∈ performedAddressSet pi := Finset.mem_biUnion.2 ⟨C.val, C.property, hj⟩
    have hb : blockTarget pi hpi values j = (values C).val := by
      unfold blockTarget
      rw [dif_pos hjU, blockContaining_eq pi hpi j hjU C.val C.property hj]
    rw [hb]
  rw [Finset.sum_congr rfl (fun v _ => hstep1 v)]
  have hstep2 : (∑ values : PivotAssignment pi hpi, ∏ C : {C // C ∈ pi}, H C (values C)) =
      ∏ C : {C // C ∈ pi}, ∑ p : P.Prime (blockPivotGroup pi hpi C).val, H C p := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rfl
  rw [hstep2, hY]
  have hblock : ∀ C : {C // C ∈ pi},
      (∑ p : P.Prime (blockPivotGroup pi hpi C).val, H C p) ≤ (8 * X) ^ (C.val.card - 1) := by
    intro C
    have hk : 2 ≤ C.val.card := hpi.1 C.val C.property
    have hle : ∀ p, H C p ≤ (2 * tiltedMu F P n (blockPivotGroup pi hpi C).val p) ^ C.val.card := by
      intro p
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod₀
      · intro j _
        exact mul_nonneg two_pos.le (muHat_nonneg F P n hμ _ _)
      · intro j _
        exact mul_le_mul_of_nonneg_left (muHat_le_block pi hpi C p hμ j) two_pos.le
    have hmom := tiltedMu_power_sum_bound F P x n hP hcut (blockPivotGroup pi hpi C)
      C.val.card (by omega)
    obtain ⟨r, hr⟩ : ∃ r, C.val.card = r + 1 := ⟨C.val.card - 1, by omega⟩
    have hr1 : 1 ≤ r := by omega
    calc (∑ p : P.Prime (blockPivotGroup pi hpi C).val, H C p)
        ≤ ∑ p : P.Prime (blockPivotGroup pi hpi C).val,
            (2 * tiltedMu F P n (blockPivotGroup pi hpi C).val p) ^ C.val.card :=
          Finset.sum_le_sum fun p _ => hle p
      _ = 2 ^ C.val.card * ∑ p : P.Prime (blockPivotGroup pi hpi C).val,
            (tiltedMu F P n (blockPivotGroup pi hpi C).val p) ^ C.val.card := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => mul_pow _ _ _
      _ ≤ 2 ^ C.val.card * (2 * X ^ (C.val.card - 1)) :=
          mul_le_mul_of_nonneg_left hmom (by positivity)
      _ = 4 * (2 * X) ^ r := by rw [hr, Nat.add_sub_cancel, pow_succ, mul_pow]; ring
      _ ≤ 4 ^ r * (2 * X) ^ r := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
          calc (4 : ℝ) = 4 ^ 1 := (pow_one 4).symm
            _ ≤ 4 ^ r := pow_le_pow_right₀ (by norm_num) hr1
      _ = (8 * X) ^ (C.val.card - 1) := by rw [hr, Nat.add_sub_cancel, ← mul_pow]; ring
  calc (∏ C : {C // C ∈ pi}, ∑ p : P.Prime (blockPivotGroup pi hpi C).val, H C p)
      ≤ ∏ C : {C // C ∈ pi}, (8 * X) ^ (C.val.card - 1) :=
        Finset.prod_le_prod₀ (fun C _ => Finset.sum_nonneg fun p _ =>
          Finset.prod_nonneg fun j _ => mul_nonneg two_pos.le (muHat_nonneg F P n hμ _ _))
          (fun C _ => hblock C)
    _ = (8 * X) ^ birthRank pi := by
        rw [Finset.prod_pow_eq_pow_sum, birthRank]
        congr 1
        exact Finset.sum_coe_sort pi (fun C => C.card - 1)

end Erdos821.P3High
