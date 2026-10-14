import Erdos821.P3High.Initial
import Erdos821.S2High.MarkedAddresses

/-! Prescribing the values of a finite set `U` of potential birth addresses: the literal
truncated absolute history sum is controlled by the per-operation conditional rows, with one
tilted point mass for every prescribed address. -/

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

section Slots

variable (F) (J) {n B : ℕ}

abbrev AddrIdx (P : PrimeGroups) (M n B : ℕ) := Fin (Fintype.card (BirthAddress P M n B))

def aIdx (a : BirthAddress P (J + F.ell) n B) : AddrIdx P (J + F.ell) n B :=
  Fintype.equivFin _ a

def slI (U : Finset (AddrIdx P (J + F.ell) n B)) : Finset (P.BigGroup × Fin (J + F.ell)) :=
  Finset.univ.filter (fun x => aIdx F J (n := n) (B := B) (.inl x) ∈ U)

def valsI (tgt : AddrIdx P (J + F.ell) n B → ℕ) (x : P.BigGroup × Fin (J + F.ell)) : ℕ :=
  tgt (aIdx F J (n := n) (B := B) (.inl x))

def slE (U : Finset (AddrIdx P (J + F.ell) n B)) (i : Fin n) :
    Finset (P.BigGroup × Fin (J + F.ell)) :=
  Finset.univ.filter (fun x => aIdx F J (n := n) (B := B) (.inr (.inl (i, x.1, x.2))) ∈ U)

def valsE (tgt : AddrIdx P (J + F.ell) n B → ℕ) (i : Fin n)
    (x : P.BigGroup × Fin (J + F.ell)) : ℕ :=
  tgt (aIdx F J (n := n) (B := B) (.inr (.inl (i, x.1, x.2))))

def slG (U : Finset (AddrIdx P (J + F.ell) n B)) (i : Fin (n + 1)) :
    Finset (P.BigGroup × Fin B) :=
  Finset.univ.filter (fun x => aIdx F J (n := n) (B := B) (.inr (.inr (i, x.1, x.2))) ∈ U)

def valsG (tgt : AddrIdx P (J + F.ell) n B → ℕ) (i : Fin (n + 1))
    (x : P.BigGroup × Fin B) : ℕ :=
  tgt (aIdx F J (n := n) (B := B) (.inr (.inr (i, x.1, x.2))))

end Slots

/-- Every address of `U` is performed with its prescribed value. -/
def Prescribed {A : Model F P J m} {n : ℕ} (B : ℕ) (H : MemoryHistory A n)
    (U : Finset (AddrIdx P (J + F.ell) n B)) (tgt : AddrIdx P (J + F.ell) n B → ℕ) : Prop :=
  ∀ j ∈ U, H.addressPerformed B ((Fintype.equivFin _).symm j) ∧
    H.addressValue B ((Fintype.equivFin _).symm j) = tgt j

def initMult {n B : ℕ} (U : Finset (AddrIdx P (J + F.ell) n B)) (tgt : AddrIdx P (J + F.ell) n B → ℕ)
    (s : P.MemoryState (J + F.ell)) : ℝ :=
  if ∀ x ∈ slI F J U, (s.2.1 x.1.val x.2).val = valsI F J tgt x then 1 else 0

theorem prescribed_local {A : Model F P J m} {n B : ℕ} (H : MemoryHistory A n)
    (U : Finset (AddrIdx P (J + F.ell) n B)) (tgt : AddrIdx P (J + F.ell) n B → ℕ)
    (hH : Prescribed B H U tgt) :
    localFactorR A n (initMult U tgt) (fun i => ghostMult (slG F J U i) (valsG F J tgt i))
      (fun i => edgeMult A (slE F J U i) (valsE F J tgt i)) H = 1 := by
  have hI : initMult U tgt (H.before 0) = 1 := by
    unfold initMult
    rw [if_pos]
    intro x hx
    have hj := hH _ (Finset.mem_filter.1 hx).2
    simp only [aIdx, Equiv.symm_apply_apply] at hj
    exact hj.2
  have hG : ∀ i, ghostMult (slG F J U i) (valsG F J tgt i) (H.before i) (H.after i)
      (H.ghost i) = 1 := by
    intro i
    unfold ghostMult
    rw [if_pos]
    intro x hx
    have hj := hH _ (Finset.mem_filter.1 hx).2
    simp only [aIdx, Equiv.symm_apply_apply] at hj
    exact ⟨hj.1, hj.2⟩
  have hE : ∀ i, edgeMult A (slE F J U i) (valsE F J tgt i) (H.after i.castSucc)
      (H.before i.succ) (H.edge i) = 1 := by
    intro i
    unfold edgeMult
    rw [if_pos]
    intro x hx
    have hj := hH _ (Finset.mem_filter.1 hx).2
    simp only [aIdx, Equiv.symm_apply_apply] at hj
    obtain ⟨h1, h2⟩ := hj
    have h1' : x.2 ∈ H.freshTargetSlots i x.1 := h1
    simp only [S2Core.MemoryHistory.freshTargetSlots, Finset.mem_filter, Finset.mem_univ,
      true_and] at h1'
    exact ⟨h1', h2⟩
  unfold localFactorR
  rw [hI, Finset.prod_eq_one (fun i _ => hG i), Finset.prod_eq_one (fun i _ => hE i)]
  ring

theorem localFactor_nonneg {A : Model F P J m} {n B : ℕ} (H : MemoryHistory A n)
    (U : Finset (AddrIdx P (J + F.ell) n B)) (tgt : AddrIdx P (J + F.ell) n B → ℕ) :
    0 ≤ localFactorR A n (initMult U tgt) (fun i => ghostMult (slG F J U i) (valsG F J tgt i))
      (fun i => edgeMult A (slE F J U i) (valsE F J tgt i)) H := by
  unfold localFactorR initMult ghostMult edgeMult
  apply mul_nonneg (mul_nonneg _ _) _
  · split_ifs <;> norm_num
  · exact Finset.prod_nonneg fun i _ => by dsimp only; split_ifs <;> norm_num
  · exact Finset.prod_nonneg fun i _ => by dsimp only; split_ifs <;> norm_num

theorem bms_sum_le_tsum {M B : ℕ} (f : P.MemoryState M → ℝ) (hf : ∀ t, 0 ≤ f t)
    (hs : Summable f) :
    ∑ t : BoundedMemoryState P M B, f t.val ≤ ∑' t, f t := by
  have h1 : ∑ t : BoundedMemoryState P M B, f t.val =
      ∑ x ∈ (Finset.univ : Finset (BoundedMemoryState P M B)).map
        (Function.Embedding.subtype _), f x := by
    rw [Finset.sum_map]
    rfl
  rw [h1]
  exact hs.sum_le_tsum _ (fun t _ => hf t)

theorem prod_slots_le (n B : ℕ) (U : Finset (AddrIdx P (J + F.ell) n B))
    (tgt : AddrIdx P (J + F.ell) n B → ℕ)
    (hμ : ∀ (g : P.BigGroup) (p : P.Prime g.val), 0 < tiltedMu F P n g.val p) :
    (∏ x ∈ slI F J U, muHat F P n x.1 (valsI F J tgt x)) *
      (∏ i : Fin (n + 1), ∏ x ∈ slG F J U i, muHat F P n x.1 (valsG F J tgt i x)) *
      (∏ i : Fin n, ∏ x ∈ slE F J U i, 2 * muHat F P n x.1 (valsE F J tgt i x)) ≤
    ∏ j ∈ U, 2 * muHat F P n (birthAddressGroup ((Fintype.equivFin _).symm j)) (tgt j) := by
  have h0 := muHat_nonneg F P n hμ
  let ψ : BirthAddress P (J + F.ell) n B → ℝ := fun a =>
    if aIdx F J a ∈ U then 2 * muHat F P n (birthAddressGroup a) (tgt (aIdx F J a)) else 1
  have hU : (∏ j ∈ U, 2 * muHat F P n (birthAddressGroup ((Fintype.equivFin _).symm j))
      (tgt j)) = ∏ a, ψ a := by
    rw [← Finset.univ_inter U, ← Finset.prod_ite_mem,
      ← (Fintype.equivFin (BirthAddress P (J + F.ell) n B)).prod_comp]
    apply Finset.prod_congr rfl
    intro a _
    rw [Equiv.symm_apply_apply]
    rfl
  have hI : (∏ x : P.BigGroup × Fin (J + F.ell), ψ (.inl x)) =
      ∏ x ∈ slI F J U, 2 * muHat F P n x.1 (valsI F J tgt x) := by
    unfold slI
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro x _
    rcases x with ⟨g, h⟩
    rfl
  have hG : ∀ i : Fin (n + 1), (∏ x : P.BigGroup × Fin B, ψ (.inr (.inr (i, x)))) =
      ∏ x ∈ slG F J U i, 2 * muHat F P n x.1 (valsG F J tgt i x) := by
    intro i
    unfold slG
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro x _
    rcases x with ⟨g, h⟩
    rfl
  have hE : ∀ i : Fin n, (∏ x : P.BigGroup × Fin (J + F.ell), ψ (.inr (.inl (i, x)))) =
      ∏ x ∈ slE F J U i, 2 * muHat F P n x.1 (valsE F J tgt i x) := by
    intro i
    unfold slE
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro x _
    rcases x with ⟨g, h⟩
    rfl
  have hsplit : (∏ a, ψ a) =
      (∏ x : P.BigGroup × Fin (J + F.ell), ψ (.inl x)) *
        ((∏ i : Fin n, ∏ x : P.BigGroup × Fin (J + F.ell), ψ (.inr (.inl (i, x)))) *
          ∏ i : Fin (n + 1), ∏ x : P.BigGroup × Fin B, ψ (.inr (.inr (i, x)))) := by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    congr 2
    · exact Fintype.prod_prod_type (fun y => ψ (.inr (.inl y)))
    · exact Fintype.prod_prod_type (fun z => ψ (.inr (.inr z)))
  rw [hU, hsplit, hI]
  simp only [hG, hE]
  have hle1 : (∏ x ∈ slI F J U, muHat F P n x.1 (valsI F J tgt x)) ≤
      ∏ x ∈ slI F J U, 2 * muHat F P n x.1 (valsI F J tgt x) :=
    Finset.prod_le_prod₀ (fun x _ => h0 _ _) (fun x _ => by linarith [h0 x.1 (valsI F J tgt x)])
  have hle2 : (∏ i : Fin (n + 1), ∏ x ∈ slG F J U i, muHat F P n x.1 (valsG F J tgt i x)) ≤
      ∏ i : Fin (n + 1), ∏ x ∈ slG F J U i, 2 * muHat F P n x.1 (valsG F J tgt i x) :=
    Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun x _ => h0 _ _)
      (fun i _ => Finset.prod_le_prod₀ (fun x _ => h0 _ _)
        (fun x _ => by linarith [h0 x.1 (valsG F J tgt i x)]))
  have hn1 : 0 ≤ ∏ x ∈ slI F J U, muHat F P n x.1 (valsI F J tgt x) :=
    Finset.prod_nonneg fun x _ => h0 _ _
  have hn2 : 0 ≤ ∏ i : Fin (n + 1), ∏ x ∈ slG F J U i, muHat F P n x.1 (valsG F J tgt i x) :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun x _ => h0 _ _
  have hn3 : 0 ≤ ∏ i : Fin n, ∏ x ∈ slE F J U i, 2 * muHat F P n x.1 (valsE F J tgt i x) :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun x _ =>
      mul_nonneg two_pos.le (h0 _ _)
  have hn1' : 0 ≤ ∏ x ∈ slI F J U, 2 * muHat F P n x.1 (valsI F J tgt x) := hn1.trans hle1
  calc _ ≤ (∏ x ∈ slI F J U, 2 * muHat F P n x.1 (valsI F J tgt x)) *
        (∏ i : Fin (n + 1), ∏ x ∈ slG F J U i, 2 * muHat F P n x.1 (valsG F J tgt i x)) *
        (∏ i : Fin n, ∏ x ∈ slE F J U i, 2 * muHat F P n x.1 (valsE F J tgt i x)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hle1 hle2 hn2 hn1') hn3
    _ = _ := by ring

/-- The prescribed truncated absolute history sum, for fixed prescribed values. -/
theorem prescribed_sum_le (A : Model F P J m) (n B : ℕ) (rho theta v CG CE : ℝ)
    (hv : 1 ≤ v) (hCG : 0 ≤ CG) (hCE : 0 ≤ CE)
    (hμ : ∀ (g : P.BigGroup) (p : P.Prime g.val), 0 < tiltedMu F P n g.val p)
    (hmass1 : ∀ g : P.BigGroup, 1 ≤ ∑ p : P.Prime g.val, tiltedMu F P n g.val p)
    (hmassJ : ∀ (g : P.BigGroup) (forb : Finset (P.Prime g.val)), forb.card ≤ J →
      (1 / 2 : ℝ) ≤ ∑ p ∈ Finset.univ.filter (fun p => p ∉ forb), tiltedMu F P n g.val p)
    (hG : ∀ (i : Fin (n + 1)) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteScaledMemoryGhostKernel F J n rho 1 i s t *
        P.memoryWeight v t) ∧
      (∑' t, absoluteScaledMemoryGhostKernel F J n rho 1 i s t * P.memoryWeight v t) ≤
        CG * P.memoryWeight v s)
    (hE : ∀ (i : Fin n) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteMemoryEdgeKernel (majorantModel A) n rho theta i .all s t *
        P.memoryWeight v t) ∧
      (∑' t, absoluteMemoryEdgeKernel (majorantModel A) n rho theta i .all s t *
        P.memoryWeight v t) ≤ CE * P.memoryWeight v s)
    (U : Finset (AddrIdx P (J + F.ell) n B)) (tgt : AddrIdx P (J + F.ell) n B → ℕ) :
    ∑' H : MemoryHistory A n,
        (if H.Valid ∧ H.Truncated B ∧ Prescribed B H U tgt then ‖H.Weight rho theta‖ else 0) ≤
      CG ^ (n + 1) * CE ^ n * initialMemoryBoundaryMass A n *
        ∏ j ∈ U, 2 * muHat F P n (birthAddressGroup ((Fintype.equivFin _).symm j)) (tgt j) := by
  have hv0 : 0 ≤ v := le_trans zero_le_one hv
  have hw0 : ∀ t : P.MemoryState (J + F.ell), 0 ≤ P.memoryWeight v t := fun t => pow_nonneg hv0 _
  have hw1 : ∀ t : P.MemoryState (J + F.ell), 1 ≤ P.memoryWeight v t := fun t => one_le_pow₀ hv
  have h0 := muHat_nonneg F P n hμ
  let Φ0 := initMult (F := F) (J := J) U tgt
  let φG : Fin (n + 1) → (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℝ :=
    fun i => ghostMult (slG F J U i) (valsG F J tgt i)
  let φE : Fin n → (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℝ :=
    fun i => edgeMult A (slE F J U i) (valsE F J tgt i)
  let cG : Fin (n + 1) → ℝ := fun i =>
    (∏ x ∈ slG F J U i, muHat F P n x.1 (valsG F J tgt i x)) * CG
  let cE : Fin n → ℝ := fun i =>
    (∏ x ∈ slE F J U i, 2 * muHat F P n x.1 (valsE F J tgt i x)) * CE
  have hcG : ∀ i, 0 ≤ cG i := fun i =>
    mul_nonneg (Finset.prod_nonneg fun x _ => h0 _ _) hCG
  have hcE : ∀ i, 0 ≤ cE i := fun i =>
    mul_nonneg (Finset.prod_nonneg fun x _ => mul_nonneg two_pos.le (h0 _ _)) hCE
  have step1 : ∑' H : MemoryHistory A n,
      (if H.Valid ∧ H.Truncated B ∧ Prescribed B H U tgt then ‖H.Weight rho theta‖ else 0) ≤
      ∑ d : BoundedHistoryData A n B,
        (if (mkH d).Valid then ‖(mkH d).Weight rho theta‖ * localFactorR A n Φ0 φG φE (mkH d)
          else 0) := by
    rw [tsum_truncR A n B _ (fun H hH => if_neg (fun h => hH h.2.1))]
    apply Finset.sum_le_sum
    intro d _
    by_cases hc : (mkH d).Valid ∧ (mkH d).Truncated B ∧ Prescribed B (mkH d) U tgt
    · rw [if_pos hc, if_pos hc.1, prescribed_local (mkH d) U tgt hc.2.2, mul_one]
    · rw [if_neg hc]
      split_ifs
      · exact mul_nonneg (norm_nonneg _) (localFactor_nonneg (mkH d) U tgt)
      · exact le_rfl
  rw [history_sum_eq] at step1
  have hrowG : ∀ (i : Fin (n + 1)) (s : BoundedMemoryState P (J + F.ell) B),
      ∑ t : BoundedMemoryState P (J + F.ell) B,
        ghostK F J n rho i (φG i) s.val t.val * P.memoryWeight v t.val ≤
          cG i * P.memoryWeight v s.val := by
    intro i s
    have h1 := ghost_row_constrained F J n rho i B v hv0 hμ hmass1 (slG F J U i)
      (valsG F J tgt i) s.val
    have h2 := bms_sum_le_tsum (B := B)
      (fun t => absoluteScaledMemoryGhostKernel F J n rho 1 i s.val t * P.memoryWeight v t)
      (fun t => mul_nonneg (by
        unfold absoluteScaledMemoryGhostKernel
        split_ifs
        · exact Finset.sum_nonneg fun c _ => by split_ifs <;> positivity
        · exact le_rfl) (hw0 t)) (hG i s.val).1
    have hP : 0 ≤ ∏ x ∈ slG F J U i, muHat F P n x.1 (valsG F J tgt i x) :=
      Finset.prod_nonneg fun x _ => h0 _ _
    calc _ ≤ _ := h1
      _ ≤ (∏ x ∈ slG F J U i, muHat F P n x.1 (valsG F J tgt i x)) *
            (CG * P.memoryWeight v s.val) :=
          mul_le_mul_of_nonneg_left (h2.trans (hG i s.val).2) hP
      _ = _ := by simp only [cG]; ring
  have hrowE : ∀ (i : Fin n) (s : BoundedMemoryState P (J + F.ell) B),
      ∑ t : BoundedMemoryState P (J + F.ell) B,
        edgeK A n rho theta i (φE i) s.val t.val * P.memoryWeight v t.val ≤
          cE i * P.memoryWeight v s.val := by
    intro i s
    have h1 := edge_row_constrained A n rho theta i B v hv0 hμ hmassJ (slE F J U i)
      (valsE F J tgt i) s.val
    have h2 := bms_sum_le_tsum (B := B)
      (fun t => absoluteMemoryEdgeKernel (majorantModel A) n rho theta i .all s.val t *
        P.memoryWeight v t)
      (fun t => mul_nonneg (Erdos821.P3Tail.edgeKernel_nonneg _ n rho theta i _ _) (hw0 t))
      (hE i s.val).1
    have hP : 0 ≤ ∏ x ∈ slE F J U i, 2 * muHat F P n x.1 (valsE F J tgt i x) :=
      Finset.prod_nonneg fun x _ => mul_nonneg two_pos.le (h0 _ _)
    calc _ ≤ _ := h1
      _ ≤ (∏ x ∈ slE F J U i, 2 * muHat F P n x.1 (valsE F J tgt i x)) *
            (CE * P.memoryWeight v s.val) :=
          mul_le_mul_of_nonneg_left (h2.trans (hE i s.val).2) hP
      _ = _ := by simp only [cE]; ring
  have hpath := pathSumR_le (fun s : BoundedMemoryState P (J + F.ell) B => P.memoryWeight v s.val)
    (fun s => hw0 s.val) n
    (fun i (s t : BoundedMemoryState P (J + F.ell) B) => ghostK F J n rho i (φG i) s.val t.val)
    (fun i (s t : BoundedMemoryState P (J + F.ell) B) => edgeK A n rho theta i (φE i) s.val t.val)
    cG cE
    (fun i s t => ghostK_nonneg F J n rho i _ (fun s t c => by
      simp only [φG, ghostMult]; split_ifs <;> norm_num) _ _)
    (fun i s t => edgeK_nonneg A n rho theta i _ (fun s t c => by
      simp only [φE, edgeMult]; split_ifs <;> norm_num) _ _)
    hcG hcE hrowG hrowE
    (fun s => if ∀ g, s.val.2.2 g = 0 then |P.memoryMass F J n s.val| * Φ0 s.val else 0)
    (fun s => if ∀ g, s.val.2.2 g = 0 then 1 else 0)
    (fun s => by
      split_ifs
      · exact mul_nonneg (abs_nonneg _) (by simp only [Φ0, initMult]; split_ifs <;> norm_num)
      · exact le_rfl)
    (fun s => by split_ifs <;> norm_num)
    (fun s => by
      split_ifs
      · exact hw1 s.val
      · exact hw0 s.val)
  have hstart : ∑ s : BoundedMemoryState P (J + F.ell) B,
      (if ∀ g, s.val.2.2 g = 0 then |P.memoryMass F J n s.val| * Φ0 s.val else 0) *
        P.memoryWeight v s.val ≤
      (∏ x ∈ slI F J U, muHat F P n x.1 (valsI F J tgt x)) * initialMemoryBoundaryMass A n := by
    have hrw : ∀ s : BoundedMemoryState P (J + F.ell) B,
        (if ∀ g, s.val.2.2 g = 0 then |P.memoryMass F J n s.val| * Φ0 s.val else 0) *
          P.memoryWeight v s.val =
        (if ∀ x ∈ slI F J U, (s.val.2.1 x.1.val x.2).val = valsI F J tgt x
          then initTerm F J n s.val else 0) := by
      intro s
      by_cases hem : ∀ g, s.val.2.2 g = 0
      · have hsz : P.memorySize s.val = 0 := by
          simp [PrimeGroups.memorySize, hem]
        have hw : P.memoryWeight v s.val = 1 := by
          simp [PrimeGroups.memoryWeight, hsz]
        rw [if_pos hem, hw, mul_one]
        simp only [Φ0, initMult, initTerm, if_pos hem]
        split_ifs <;> ring
      · rw [if_neg hem, zero_mul]
        simp only [initTerm, if_neg hem]
        split_ifs <;> rfl
    rw [Finset.sum_congr rfl (fun s _ => hrw s)]
    have hI0 : 0 ≤ ∏ x ∈ slI F J U, muHat F P n x.1 (valsI F J tgt x) :=
      Finset.prod_nonneg fun x _ => h0 _ _
    exact (init_slots F J n B hμ hmass1 (valsI F J tgt) (slI F J U)).trans
      (mul_le_mul_of_nonneg_left (initTerm_sum_le A n B) hI0)
  have hIBM : 0 ≤ initialMemoryBoundaryMass A n :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hprodG : (∏ i, cG i) = (∏ i : Fin (n + 1),
      ∏ x ∈ slG F J U i, muHat F P n x.1 (valsG F J tgt i x)) * CG ^ (n + 1) := by
    simp only [cG, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hprodE : (∏ i, cE i) = (∏ i : Fin n,
      ∏ x ∈ slE F J U i, 2 * muHat F P n x.1 (valsE F J tgt i x)) * CE ^ n := by
    simp only [cE, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hslots := prod_slots_le n B U tgt hμ
  have hK : 0 ≤ CG ^ (n + 1) * CE ^ n * initialMemoryBoundaryMass A n :=
    mul_nonneg (mul_nonneg (pow_nonneg hCG _) (pow_nonneg hCE _)) hIBM
  have hn2 : 0 ≤ ∏ i : Fin (n + 1), ∏ x ∈ slG F J U i, muHat F P n x.1 (valsG F J tgt i x) :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun x _ => h0 _ _
  have hn3 : 0 ≤ ∏ i : Fin n, ∏ x ∈ slE F J U i, 2 * muHat F P n x.1 (valsE F J tgt i x) :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun x _ =>
      mul_nonneg two_pos.le (h0 _ _)
  have hcGE : 0 ≤ (∏ i, cG i) * (∏ i, cE i) :=
    mul_nonneg (Finset.prod_nonneg fun i _ => hcG i) (Finset.prod_nonneg fun i _ => hcE i)
  calc _ ≤ _ := step1
    _ ≤ _ := hpath
    _ ≤ (∏ i, cG i) * (∏ i, cE i) *
          ((∏ x ∈ slI F J U, muHat F P n x.1 (valsI F J tgt x)) *
            initialMemoryBoundaryMass A n) := mul_le_mul_of_nonneg_left hstart hcGE
    _ = (CG ^ (n + 1) * CE ^ n * initialMemoryBoundaryMass A n) *
          ((∏ x ∈ slI F J U, muHat F P n x.1 (valsI F J tgt x)) *
            (∏ i : Fin (n + 1), ∏ x ∈ slG F J U i, muHat F P n x.1 (valsG F J tgt i x)) *
            (∏ i : Fin n, ∏ x ∈ slE F J U i, 2 * muHat F P n x.1 (valsE F J tgt i x))) := by
        rw [hprodG, hprodE]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hslots hK

end Erdos821.P3High
