import Erdos821.S2.HighRankTask
import Erdos821.P3LowRank.LowRank
import Erdos821.P3High.PathSum

/-! Absolute truncated history sums with real local multipliers are finite real path sums. -/

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
open Erdos821.S2Core Erdos821.P3Lowrank

attribute [local instance] bmsFintype ghostChoiceFintype edgeChoiceFintype

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- Absolute ghost kernel with a real multiplier on each local choice. -/
def ghostK (F : FixedData) (J n : ℕ) (rho : ℝ) (i : Fin (n + 1))
    (φ : (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℝ)
    (s t : P.MemoryState (J + F.ell)) : ℝ :=
  if s.1 = t.1 ∧ s.2.1 = t.2.1 then
    ∑ c : GhostChoice s t, if ghostChoiceValid c then |ghostChoiceWeight F n rho i c| * φ s t c
      else 0
  else 0

/-- Absolute edge kernel with a real multiplier on each local choice. -/
def edgeK (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (φ : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℝ)
    (s t : P.MemoryState (J + F.ell)) : ℝ :=
  edgeSymmetryFactor P (J + F.ell) * ∑ c : EdgeChoice A s,
    if edgeChoiceValid A .all i s t c then
      ‖edgeChoiceCoefficient A n rho theta i s t c‖ * φ s t c else 0

def localFactorR (A : Model F P J m) (n : ℕ)
    (Φ0 : P.MemoryState (J + F.ell) → ℝ)
    (φG : Fin (n + 1) → (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℝ)
    (φE : Fin n → (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℝ)
    (H : MemoryHistory A n) : ℝ :=
  Φ0 (H.before 0) * (∏ i, φG i (H.before i) (H.after i) (H.ghost i)) *
    ∏ i, φE i (H.after i.castSucc) (H.before i.succ) (H.edge i)

theorem norm_weight_eq {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n) (rho theta : ℝ) :
    ‖H.Weight rho theta‖ = |P.memoryMass F J n (H.before 0)| *
      (∏ i, |ghostChoiceWeight F n rho i (H.ghost i)|) *
      ∏ i, (edgeSymmetryFactor P (J + F.ell) *
        ‖edgeChoiceCoefficient A n rho theta i (H.after i.castSucc) (H.before i.succ)
          (H.edge i)‖) := by
  simp only [S2Core.MemoryHistory.Weight, norm_mul, norm_prod, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (edgeSymmetryFactor_nonneg P (J + F.ell))]

/-- Exact absolute choice expansion for one fixed state path. -/
theorem abs_choice_sum (A : Model F P J m) (n : ℕ) (rho theta : ℝ)
    (Φ0 : P.MemoryState (J + F.ell) → ℝ)
    (φG : Fin (n + 1) → (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℝ)
    (φE : Fin n → (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℝ)
    (bf af : Fin (n + 1) → P.MemoryState (J + F.ell)) :
    ∑ c1 : (i : Fin (n + 1)) → GhostChoice (bf i) (af i),
      ∑ c2 : (i : Fin n) → EdgeChoice A (af i.castSucc),
        (if (⟨bf, af, c1, c2⟩ : MemoryHistory A n).Valid then
          ‖(⟨bf, af, c1, c2⟩ : MemoryHistory A n).Weight rho theta‖ *
            localFactorR A n Φ0 φG φE ⟨bf, af, c1, c2⟩ else 0) =
      (if ∀ g, (bf 0).2.2 g = 0 then |P.memoryMass F J n (bf 0)| * Φ0 (bf 0) else 0) *
        (∏ i, ghostK F J n rho i (φG i) (bf i) (af i)) *
        (∏ i : Fin n, edgeK A n rho theta i (φE i) (af i.castSucc) (bf i.succ)) *
        (if ∀ g, (af (Fin.last n)).2.2 g = 0 then (1 : ℝ) else 0) := by
  set X0 : ℝ := if ∀ g, (bf 0).2.2 g = 0 then |P.memoryMass F J n (bf 0)| * Φ0 (bf 0) else 0
    with hX0
  set Y0 : ℝ := if ∀ g, (af (Fin.last n)).2.2 g = 0 then (1 : ℝ) else 0 with hY0
  let gT : (i : Fin (n + 1)) → GhostChoice (bf i) (af i) → ℝ := fun i c =>
    if (bf i).1 = (af i).1 ∧ (bf i).2.1 = (af i).2.1 ∧ ghostChoiceValid c then
      |ghostChoiceWeight F n rho i c| * φG i (bf i) (af i) c else 0
  let eT : (i : Fin n) → EdgeChoice A (af i.castSucc) → ℝ := fun i c =>
    if edgeChoiceValid A .all i (af i.castSucc) (bf i.succ) c then
      edgeSymmetryFactor P (J + F.ell) *
        ‖edgeChoiceCoefficient A n rho theta i (af i.castSucc) (bf i.succ) c‖ *
          φE i (af i.castSucc) (bf i.succ) c else 0
  have hpt : ∀ (c1 : (i : Fin (n + 1)) → GhostChoice (bf i) (af i))
      (c2 : (i : Fin n) → EdgeChoice A (af i.castSucc)),
      (if (⟨bf, af, c1, c2⟩ : MemoryHistory A n).Valid then
          ‖(⟨bf, af, c1, c2⟩ : MemoryHistory A n).Weight rho theta‖ *
            localFactorR A n Φ0 φG φE ⟨bf, af, c1, c2⟩ else 0) =
        X0 * (∏ i, gT i (c1 i)) * (∏ i, eT i (c2 i)) * Y0 := by
    intro c1 c2
    by_cases h0 : ∀ g, (bf 0).2.2 g = 0
    · by_cases hn : ∀ g, (af (Fin.last n)).2.2 g = 0
      · by_cases hg : ∀ i, (bf i).1 = (af i).1 ∧ (bf i).2.1 = (af i).2.1 ∧
            ghostChoiceValid (c1 i)
        · by_cases he : ∀ i, edgeChoiceValid A .all i (af i.castSucc) (bf i.succ) (c2 i)
          · have hV : (⟨bf, af, c1, c2⟩ : MemoryHistory A n).Valid := ⟨h0, hn, hg, he⟩
            rw [if_pos hV, hX0, hY0, if_pos h0, if_pos hn]
            have hgT : ∀ i, gT i (c1 i) =
                |ghostChoiceWeight F n rho i (c1 i)| * φG i (bf i) (af i) (c1 i) :=
              fun i => if_pos (hg i)
            have heT : ∀ i, eT i (c2 i) = edgeSymmetryFactor P (J + F.ell) *
                ‖edgeChoiceCoefficient A n rho theta i (af i.castSucc) (bf i.succ) (c2 i)‖ *
                  φE i (af i.castSucc) (bf i.succ) (c2 i) :=
              fun i => if_pos (he i)
            rw [norm_weight_eq]
            simp only [hgT, heT, localFactorR, Finset.prod_mul_distrib]
            ring
          · have hV : ¬ (⟨bf, af, c1, c2⟩ : MemoryHistory A n).Valid := fun hV => he hV.2.2.2
            obtain ⟨i, hi⟩ := not_forall.mp he
            rw [if_neg hV, Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)]
            ring
        · have hV : ¬ (⟨bf, af, c1, c2⟩ : MemoryHistory A n).Valid := fun hV => hg hV.2.2.1
          obtain ⟨i, hi⟩ := not_forall.mp hg
          rw [if_neg hV, Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)]
          ring
      · have hV : ¬ (⟨bf, af, c1, c2⟩ : MemoryHistory A n).Valid := fun hV => hn hV.2.1
        rw [if_neg hV, hY0, if_neg hn]
        ring
    · have hV : ¬ (⟨bf, af, c1, c2⟩ : MemoryHistory A n).Valid := fun hV => h0 hV.1
      rw [if_neg hV, hX0, if_neg h0]
      ring
  have hG : ∀ i, ∑ c, gT i c = ghostK F J n rho i (φG i) (bf i) (af i) := by
    intro i
    unfold ghostK
    by_cases hag : (bf i).1 = (af i).1 ∧ (bf i).2.1 = (af i).2.1
    · rw [if_pos hag]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : ghostChoiceValid c
      · rw [if_pos hc]
        exact if_pos ⟨hag.1, hag.2, hc⟩
      · rw [if_neg hc]
        exact if_neg (fun h => hc h.2.2)
    · rw [if_neg hag]
      apply Finset.sum_eq_zero
      intro c _
      exact if_neg (fun h => hag ⟨h.1, h.2.1⟩)
  have hE : ∀ i, ∑ c, eT i c = edgeK A n rho theta i (φE i) (af i.castSucc) (bf i.succ) := by
    intro i
    unfold edgeK
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : edgeChoiceValid A .all i (af i.castSucc) (bf i.succ) c
    · rw [if_pos hc]
      simp only [eT, if_pos hc]
      ring
    · rw [if_neg hc]
      simp only [eT, if_neg hc, mul_zero]
  have hsplit : ∀ c1 : (i : Fin (n + 1)) → GhostChoice (bf i) (af i),
      ∑ c2 : (i : Fin n) → EdgeChoice A (af i.castSucc),
        X0 * (∏ i, gT i (c1 i)) * (∏ i, eT i (c2 i)) * Y0 =
      (X0 * (∏ i, gT i (c1 i)) * Y0) * ∑ c2 : (i : Fin n) → EdgeChoice A (af i.castSucc),
        ∏ i, eT i (c2 i) := by
    intro c1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c2 _
    ring
  simp only [hpt, hsplit]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Fintype.prod_sum gT,
    ← Fintype.prod_sum eT]
  simp only [hG, hE]
  ring

theorem tsum_truncR (A : Model F P J m) (n B : ℕ) (f : MemoryHistory A n → ℝ)
    (hf : ∀ H, ¬ H.Truncated B → f H = 0) :
    ∑' H, f H = ∑ d : BoundedHistoryData A n B, f (mkH d) := by
  have hs : Function.support f ⊆ {H : MemoryHistory A n | H.Truncated B} := by
    intro H hH
    by_contra h
    exact hH (hf H h)
  rw [← tsum_subtype_eq_of_support_subset hs, ← (truncEquiv A n B).tsum_eq, tsum_fintype]
  rfl

/-- The bounded history sum is the real path sum of the multiplied absolute kernels. -/
theorem history_sum_eq (A : Model F P J m) (n B : ℕ) (rho theta : ℝ)
    (Φ0 : P.MemoryState (J + F.ell) → ℝ)
    (φG : Fin (n + 1) → (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℝ)
    (φE : Fin n → (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℝ) :
    (∑ d : BoundedHistoryData A n B,
      (if (mkH d).Valid then ‖(mkH d).Weight rho theta‖ * localFactorR A n Φ0 φG φE (mkH d)
        else 0)) =
      pathSumR n (fun i (s t : BoundedMemoryState P (J + F.ell) B) =>
          ghostK F J n rho i (φG i) s.val t.val)
        (fun i (s t : BoundedMemoryState P (J + F.ell) B) =>
          edgeK A n rho theta i (φE i) s.val t.val)
        (fun s => if ∀ g, s.val.2.2 g = 0 then |P.memoryMass F J n s.val| * Φ0 s.val else 0)
        (fun s => if ∀ g, s.val.2.2 g = 0 then 1 else 0) := by
  unfold pathSumR
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type]
  exact abs_choice_sum A n rho theta Φ0 φG φE (fun i => (b i).val) (fun i => (a i).val)

theorem ghostK_nonneg (F : FixedData) (J n : ℕ) (rho : ℝ) (i : Fin (n + 1))
    (φ : (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℝ)
    (hφ : ∀ s t c, 0 ≤ φ s t c) (s t : P.MemoryState (J + F.ell)) :
    0 ≤ ghostK F J n rho i φ s t := by
  unfold ghostK
  split_ifs
  · exact Finset.sum_nonneg fun c _ => by
      split_ifs
      · exact mul_nonneg (abs_nonneg _) (hφ s t c)
      · exact le_rfl
  · exact le_rfl

theorem edgeK_nonneg (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (φ : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℝ)
    (hφ : ∀ s t c, 0 ≤ φ s t c) (s t : P.MemoryState (J + F.ell)) :
    0 ≤ edgeK A n rho theta i φ s t := by
  unfold edgeK
  apply mul_nonneg (edgeSymmetryFactor_nonneg P (J + F.ell))
  exact Finset.sum_nonneg fun c _ => by
    split_ifs
    · exact mul_nonneg (norm_nonneg _) (hφ s t c)
    · exact le_rfl

end Erdos821.P3High
