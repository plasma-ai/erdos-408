import Erdos821.S2.LowRankTask
import Erdos821.P3Tail.MemoryTail
import Erdos821.P3LowRank.ChainBound

/-! Truncated valid histories with local multipliers form an exact finite kernel chain.

Fixing the bounded state path, the local ghost and edge choices factor into the literal
memory kernels with the inserted multipliers; the state paths then form a path sum on the
finite bounded state type, which the finite operator-norm composition controls. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Lowrank

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- The finite bounded state type. -/
abbrev bmsFintype (P : PrimeGroups) (M B : ℕ) : Fintype (BoundedMemoryState P M B) :=
  @Fintype.ofFinite _ (bounded_memoryState_finite P M B)

abbrev ghostChoiceFintype {M : ℕ} (s t : P.MemoryState M) : Fintype (GhostChoice s t) :=
  inferInstance

abbrev edgeChoiceFintype (A : Model F P J m) (s : P.MemoryState (J + F.ell)) :
    Fintype (EdgeChoice A s) :=
  inferInstance

attribute [local instance] bmsFintype ghostChoiceFintype edgeChoiceFintype

/-- The history determined by bounded states and local choices. -/
def mkH {A : Model F P J m} {n B : ℕ} (d : BoundedHistoryData A n B) : MemoryHistory A n :=
  ⟨fun i => (d.1 i).val, fun i => (d.2.1 i).val, d.2.2.1, d.2.2.2⟩

theorem mkH_truncated {A : Model F P J m} {n B : ℕ} (d : BoundedHistoryData A n B) :
    (mkH d).Truncated B := fun i => ⟨(d.1 i).property, (d.2.1 i).property⟩

def truncEquiv (A : Model F P J m) (n B : ℕ) :
    BoundedHistoryData A n B ≃ ↥{H : MemoryHistory A n | H.Truncated B} where
  toFun d := ⟨mkH d, mkH_truncated d⟩
  invFun H := ⟨fun i => ⟨H.val.before i, ((show H.val.Truncated B from H.property) i).1⟩,
    fun i => ⟨H.val.after i, ((show H.val.Truncated B from H.property) i).2⟩,
    H.val.ghost, H.val.edge⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tsum_trunc (A : Model F P J m) (n B : ℕ) (f : MemoryHistory A n → ℂ)
    (hf : ∀ H, ¬ H.Truncated B → f H = 0) :
    ∑' H, f H = ∑ d : BoundedHistoryData A n B, f (mkH d) := by
  have hs : Function.support f ⊆ {H : MemoryHistory A n | H.Truncated B} := by
    intro H hH
    by_contra h
    exact hH (hf H h)
  rw [← tsum_subtype_eq_of_support_subset hs, ← (truncEquiv A n B).tsum_eq, tsum_fintype]
  rfl

/-- Product of the local multipliers along a history. -/
def localFactor (A : Model F P J m) (n : ℕ)
    (Φ0 : P.MemoryState (J + F.ell) → ℂ)
    (φG : Fin (n + 1) → (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℂ)
    (φE : Fin n → (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ)
    (H : MemoryHistory A n) : ℂ :=
  Φ0 (H.before 0) * (∏ i, φG i (H.before i) (H.after i) (H.ghost i)) *
    ∏ i, φE i (H.after i.castSucc) (H.before i.succ) (H.edge i)

/-- Exact choice expansion for one fixed state path. -/
theorem choice_sum (A : Model F P J m) (n : ℕ) (rho theta : ℝ)
    (Φ0 : P.MemoryState (J + F.ell) → ℂ)
    (φG : Fin (n + 1) → (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℂ)
    (φE : Fin n → (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ)
    (bf af : Fin (n + 1) → P.MemoryState (J + F.ell)) :
    ∑ c1 : (i : Fin (n + 1)) → GhostChoice (bf i) (af i),
      ∑ c2 : (i : Fin n) → EdgeChoice A (af i.castSucc),
        (if (⟨bf, af, c1, c2⟩ : MemoryHistory A n).Valid then
          (⟨bf, af, c1, c2⟩ : MemoryHistory A n).Weight rho theta *
            localFactor A n Φ0 φG φE ⟨bf, af, c1, c2⟩ else 0) =
      (if ∀ g, (bf 0).2.2 g = 0 then (P.memoryMass F J n (bf 0) : ℂ) * Φ0 (bf 0) else 0) *
        (∏ i, memoryGhostKernel F J n rho i (φG i) (bf i) (af i)) *
        (∏ i : Fin n, memoryEdgeKernel A n rho theta i .all (φE i) (af i.castSucc) (bf i.succ)) *
        (if ∀ g, (af (Fin.last n)).2.2 g = 0 then (1 : ℂ) else 0) := by
  set X0 : ℂ := if ∀ g, (bf 0).2.2 g = 0 then (P.memoryMass F J n (bf 0) : ℂ) * Φ0 (bf 0) else 0
    with hX0
  set Y0 : ℂ := if ∀ g, (af (Fin.last n)).2.2 g = 0 then (1 : ℂ) else 0 with hY0
  let gT : (i : Fin (n + 1)) → GhostChoice (bf i) (af i) → ℂ := fun i c =>
    if (bf i).1 = (af i).1 ∧ (bf i).2.1 = (af i).2.1 ∧ ghostChoiceValid c then
      (ghostChoiceWeight F n rho i c : ℂ) * φG i (bf i) (af i) c else 0
  let eT : (i : Fin n) → EdgeChoice A (af i.castSucc) → ℂ := fun i c =>
    if edgeChoiceValid A .all i (af i.castSucc) (bf i.succ) c then
      (edgeSymmetryFactor P (J + F.ell) : ℂ) *
        edgeChoiceCoefficient A n rho theta i (af i.castSucc) (bf i.succ) c *
          φE i (af i.castSucc) (bf i.succ) c else 0
  have hpt : ∀ (c1 : (i : Fin (n + 1)) → GhostChoice (bf i) (af i))
      (c2 : (i : Fin n) → EdgeChoice A (af i.castSucc)),
      (if (⟨bf, af, c1, c2⟩ : MemoryHistory A n).Valid then
          (⟨bf, af, c1, c2⟩ : MemoryHistory A n).Weight rho theta *
            localFactor A n Φ0 φG φE ⟨bf, af, c1, c2⟩ else 0) =
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
                (ghostChoiceWeight F n rho i (c1 i) : ℂ) * φG i (bf i) (af i) (c1 i) :=
              fun i => if_pos (hg i)
            have heT : ∀ i, eT i (c2 i) = (edgeSymmetryFactor P (J + F.ell) : ℂ) *
                edgeChoiceCoefficient A n rho theta i (af i.castSucc) (bf i.succ) (c2 i) *
                  φE i (af i.castSucc) (bf i.succ) (c2 i) :=
              fun i => if_pos (he i)
            simp only [hgT, heT, MemoryHistory.Weight, localFactor, Finset.prod_mul_distrib]
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
  have hG : ∀ i, ∑ c, gT i c = memoryGhostKernel F J n rho i (φG i) (bf i) (af i) := by
    intro i
    unfold memoryGhostKernel
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
  have hE : ∀ i, ∑ c, eT i c =
      memoryEdgeKernel A n rho theta i .all (φE i) (af i.castSucc) (bf i.succ) := by
    intro i
    unfold memoryEdgeKernel
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

/-- Bilinear bounds on the full state type restrict to the finite kept subtype. -/
theorem finNormBound_of_normBound {α : Type*} (keep : α → Prop) [Fintype {x // keep x}]
    (mass : α → ℝ) (K : α → α → ℂ) (C : ℝ) (h : NormBound mass (projectKernel keep K) C) :
    FinNormBound (fun s : {x // keep x} => mass s.val) (fun s t => K s.val t.val) C := by
  intro f g
  let S : Finset α := Finset.univ.map (Function.Embedding.subtype keep)
  let f' : α → ℂ := fun x => if hx : keep x then f ⟨x, hx⟩ else 0
  let g' : α → ℂ := fun x => if hx : keep x then g ⟨x, hx⟩ else 0
  have h1 := h S S f' g'
  have hf' : ∀ s : {x // keep x}, f' s.val = f s := fun s => dif_pos s.property
  have hg' : ∀ s : {x // keep x}, g' s.val = g s := fun s => dif_pos s.property
  have hp : ∀ s t : {x // keep x}, projectKernel keep K s.val t.val = K s.val t.val :=
    fun s t => if_pos ⟨s.property, t.property⟩
  simp only [S, Finset.sum_map, Function.Embedding.coe_subtype, hf', hg', hp] at h1
  exact h1

theorem boundary_sum_le (A : Model F P J m) (n B : ℕ) :
    ∑ s : BoundedMemoryState P (J + F.ell) B,
      (if ∀ g, s.val.2.2 g = 0 then P.memoryMass F J n s.val else 0) ≤
        initialMemoryBoundaryMass A n := by
  rw [← Finset.sum_filter]
  let T := (Finset.univ.filter (fun s : BoundedMemoryState P (J + F.ell) B =>
    ∀ g, s.val.2.2 g = 0)).map (Function.Embedding.subtype _)
  calc ∑ s ∈ Finset.univ.filter (fun s : BoundedMemoryState P (J + F.ell) B =>
        ∀ g, s.val.2.2 g = 0), P.memoryMass F J n s.val
      = ∑ x ∈ T, P.memoryMass F J n x := by
        simp only [T, Finset.sum_map, Function.Embedding.coe_subtype]
    _ ≤ ∑ x ∈ T, |P.memoryMass F J n x| := Finset.sum_le_sum fun x _ => le_abs_self _
    _ ≤ _ := by
        apply Erdos821.P3Tail.start_sum_le A n T
        intro x hx
        simp only [T, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coe_subtype] at hx
        obtain ⟨s, hs, rfl⟩ := hx
        exact hs

theorem star_ite_mul (p : Prop) [Decidable p] (x : ℝ) (z : ℂ) :
    (x : ℂ) * star (if p then star z else 0) = if p then (x : ℂ) * z else 0 := by
  split_ifs <;> simp

/-- The literal truncated-history sum with arbitrary local multipliers. -/
theorem local_history_bound (A : Model F P J m) (n B : ℕ) (rho theta CG : ℝ) (c : Fin n → ℝ)
    (Φ0 : P.MemoryState (J + F.ell) → ℂ)
    (φG : Fin (n + 1) → (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℂ)
    (φE : Fin n → (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ)
    (hmass : ∀ s, 0 ≤ P.memoryMass F J n s) (hCG : 0 ≤ CG) (hc : ∀ i, 0 ≤ c i)
    (hΦ0 : ∀ s, ‖Φ0 s‖ ≤ 1)
    (hG : ∀ i, NormBound (P.memoryMass F J n)
      (projectKernel (fun s => P.memorySize s ≤ B) (memoryGhostKernel F J n rho i (φG i))) CG)
    (hE : ∀ i, NormBound (P.memoryMass F J n)
      (projectKernel (fun s => P.memorySize s ≤ B)
        (memoryEdgeKernel A n rho theta i .all (φE i))) (c i)) :
    ‖∑ d : BoundedHistoryData A n B,
        (if (mkH d).Valid then (mkH d).Weight rho theta * localFactor A n Φ0 φG φE (mkH d)
          else 0)‖ ≤
      initialMemoryBoundaryMass A n * CG ^ (n + 1) * ∏ i, c i := by
  let mass' : BoundedMemoryState P (J + F.ell) B → ℝ := fun s => P.memoryMass F J n s.val
  let Gk : Fin (n + 1) → BoundedMemoryState P (J + F.ell) B →
      BoundedMemoryState P (J + F.ell) B → ℂ :=
    fun i s t => memoryGhostKernel F J n rho i (φG i) s.val t.val
  let Ek : Fin n → BoundedMemoryState P (J + F.ell) B →
      BoundedMemoryState P (J + F.ell) B → ℂ :=
    fun i s t => memoryEdgeKernel A n rho theta i .all (φE i) s.val t.val
  let f : BoundedMemoryState P (J + F.ell) B → ℂ :=
    fun s => if ∀ g, s.val.2.2 g = 0 then star (Φ0 s.val) else 0
  let v : BoundedMemoryState P (J + F.ell) B → ℂ :=
    fun s => if ∀ g, s.val.2.2 g = 0 then 1 else 0
  have hsum : (∑ d : BoundedHistoryData A n B,
      (if (mkH d).Valid then (mkH d).Weight rho theta * localFactor A n Φ0 φG φE (mkH d)
        else 0)) = pathSum n Gk Ek (fun s => (mass' s : ℂ) * star (f s)) v := by
    unfold pathSum
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro b _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro a _
    rw [Fintype.sum_prod_type]
    refine (choice_sum A n rho theta Φ0 φG φE (fun i => (b i).val) (fun i => (a i).val)).trans ?_
    simp only [mass', f, star_ite_mul]
    rfl
  rw [hsum]
  have hmass' : ∀ s, 0 ≤ mass' s := fun s => hmass s.val
  have hfin := pathSum_bound mass' hmass' CG hCG n Gk Ek c hc
    (fun i => finNormBound_of_normBound (fun s => P.memorySize s ≤ B) _ _ CG (hG i))
    (fun i => finNormBound_of_normBound (fun s => P.memorySize s ≤ B) _ _ (c i) (hE i)) f v
  set M := initialMemoryBoundaryMass A n with hMdef
  have hbd := boundary_sum_le A n B
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hf : wnorm mass' f ≤ Real.sqrt M := by
    apply Real.sqrt_le_sqrt
    refine le_trans (Finset.sum_le_sum fun s _ => ?_) hbd
    show mass' s * ‖f s‖ ^ 2 ≤ if ∀ g, s.val.2.2 g = 0 then P.memoryMass F J n s.val else 0
    by_cases hs : ∀ g, s.val.2.2 g = 0
    · simp only [f, if_pos hs, norm_star]
      have h1 : ‖Φ0 s.val‖ ^ 2 ≤ 1 := by
        have := hΦ0 s.val
        have h0 := norm_nonneg (Φ0 s.val)
        nlinarith
      calc mass' s * ‖Φ0 s.val‖ ^ 2 ≤ mass' s * 1 := mul_le_mul_of_nonneg_left h1 (hmass' s)
        _ = _ := mul_one _
    · simp only [f, if_neg hs, norm_zero]
      simp
  have hv : wnorm mass' v ≤ Real.sqrt M := by
    apply Real.sqrt_le_sqrt
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun s _ => ?_)) hbd
    by_cases hs : ∀ g, s.val.2.2 g = 0
    · simp only [v, if_pos hs, norm_one]
      simp [mass']
    · simp only [v, if_neg hs, norm_zero]
      simp
  have hK : 0 ≤ CG ^ (n + 1) * ∏ i, c i :=
    mul_nonneg (pow_nonneg hCG _) (Finset.prod_nonneg fun i _ => hc i)
  calc _ ≤ CG ^ (n + 1) * (∏ i, c i) * wnorm mass' f * wnorm mass' v := hfin
    _ ≤ CG ^ (n + 1) * (∏ i, c i) * Real.sqrt M * Real.sqrt M := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hf hK) hv (wnorm_nonneg _ _)
        exact mul_nonneg hK (Real.sqrt_nonneg _)
    _ = M * CG ^ (n + 1) * ∏ i, c i := by
        rw [mul_assoc (CG ^ (n + 1) * ∏ i, c i), Real.mul_self_sqrt hM]
        ring

end Erdos821.P3Lowrank
