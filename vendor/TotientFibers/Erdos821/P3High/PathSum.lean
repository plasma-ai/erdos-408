import Mathlib

/-! Real nonnegative alternating path sums controlled by per-operation weighted row bounds. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Erdos821.P3High

variable {β : Type*} [Fintype β]

/-- Ghost kernels on `(b i, a i)`, edges on `(a i, b (i+1))`. -/
def pathSumR (n : ℕ) (G : Fin (n + 1) → β → β → ℝ) (E : Fin n → β → β → ℝ)
    (u v : β → ℝ) : ℝ :=
  ∑ b : Fin (n + 1) → β, ∑ a : Fin (n + 1) → β,
    u (b 0) * (∏ i, G i (b i) (a i)) * (∏ i : Fin n, E i (a i.castSucc) (b i.succ)) *
      v (a (Fin.last n))

def applyR (K : β → β → ℝ) (h : β → ℝ) : β → ℝ := fun s => ∑ t, K s t * h t

/-- The function produced by everything after the first ghost kernel. -/
def tailR : (n : ℕ) → (Fin (n + 1) → β → β → ℝ) → (Fin n → β → β → ℝ) → (β → ℝ) → β → ℝ
  | 0, _, _, v => v
  | n + 1, G, E, v =>
      applyR (E 0) (applyR (G (Fin.succ 0)) (tailR n (fun i => G i.succ) (fun i => E i.succ) v))

theorem sum_fin_consR {M : Type*} [AddCommMonoid M] (n : ℕ) (f : (Fin (n + 1) → β) → M) :
    ∑ b : Fin (n + 1) → β, f b = ∑ b0 : β, ∑ b' : Fin n → β, f (Fin.cons b0 b') := by
  rw [← (Fin.consEquiv fun _ => β).sum_comp, Fintype.sum_prod_type]
  rfl

theorem pathSumR_eq : ∀ (n : ℕ) (G : Fin (n + 1) → β → β → ℝ) (E : Fin n → β → β → ℝ)
    (u v : β → ℝ), pathSumR n G E u v = ∑ s, ∑ t, u s * G 0 s t * tailR n G E v t := by
  intro n
  induction n with
  | zero =>
      intro G E u v
      unfold pathSumR
      rw [sum_fin_consR]
      apply Finset.sum_congr rfl
      intro s _
      rw [Fintype.sum_unique]
      rw [sum_fin_consR]
      apply Finset.sum_congr rfl
      intro t _
      rw [Fintype.sum_unique]
      simp [tailR, Fin.last]
  | succ n ih =>
      intro G E u v
      unfold pathSumR
      rw [sum_fin_consR]
      apply Finset.sum_congr rfl
      intro s _
      simp_rw [sum_fin_consR (n := n + 1)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      have hih := ih (fun i => G i.succ) (fun i => E i.succ) (E 0 t) v
      simp only [pathSumR] at hih
      have hc : ∀ i : Fin n, (i.succ.castSucc : Fin (n + 2)) = i.castSucc.succ :=
        fun i => Fin.ext rfl
      have hrw : ∀ (b' a' : Fin (n + 1) → β),
          u ((Fin.cons s b' : Fin (n + 2) → β) 0) *
            (∏ i, G i ((Fin.cons s b' : Fin (n + 2) → β) i)
              ((Fin.cons t a' : Fin (n + 2) → β) i)) *
            (∏ i : Fin (n + 1), E i ((Fin.cons t a' : Fin (n + 2) → β) i.castSucc)
              ((Fin.cons s b' : Fin (n + 2) → β) i.succ)) *
            v ((Fin.cons t a' : Fin (n + 2) → β) (Fin.last (n + 1))) =
          u s * G 0 s t * (E 0 t (b' 0) * (∏ i, G i.succ (b' i) (a' i)) *
            (∏ i : Fin n, E i.succ (a' i.castSucc) (b' i.succ)) * v (a' (Fin.last n))) := by
        intro b' a'
        rw [Fin.prod_univ_succ (n := n), Fin.prod_univ_succ (n := n + 1)]
        simp only [Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero, hc]
        rw [← Fin.succ_last, Fin.cons_succ]
        ring
      simp_rw [hrw, ← Finset.mul_sum]
      rw [hih]
      congr 1
      simp only [tailR, applyR, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s' _
      apply Finset.sum_congr rfl
      intro t' _
      ring

theorem tailR_bound (w : β → ℝ) (hw : ∀ t, 0 ≤ w t) :
    ∀ (n : ℕ) (G : Fin (n + 1) → β → β → ℝ) (E : Fin n → β → β → ℝ)
      (cG : Fin (n + 1) → ℝ) (cE : Fin n → ℝ),
      (∀ i s t, 0 ≤ G i s t) → (∀ i s t, 0 ≤ E i s t) →
      (∀ i, 0 ≤ cG i) → (∀ i, 0 ≤ cE i) →
      (∀ i s, ∑ t, G i s t * w t ≤ cG i * w s) →
      (∀ i s, ∑ t, E i s t * w t ≤ cE i * w s) →
      ∀ v : β → ℝ, (∀ t, 0 ≤ v t) → (∀ t, v t ≤ w t) →
      ∀ t, 0 ≤ tailR n G E v t ∧
        tailR n G E v t ≤ (∏ i : Fin n, cG i.succ) * (∏ i, cE i) * w t := by
  intro n
  induction n with
  | zero =>
      intro G E cG cE _ _ _ _ _ _ v hv0 hvw t
      simpa [tailR] using And.intro (hv0 t) (hvw t)
  | succ n ih =>
      intro G E cG cE hG hE hcG hcE hGr hEr v hv0 hvw
      have IH := ih (fun i => G i.succ) (fun i => E i.succ) (fun i => cG i.succ)
        (fun i => cE i.succ) (fun i => hG i.succ) (fun i => hE i.succ)
        (fun i => hcG i.succ) (fun i => hcE i.succ) (fun i => hGr i.succ)
        (fun i => hEr i.succ) v hv0 hvw
      set T := tailR n (fun i => G i.succ) (fun i => E i.succ) v with hT
      set K : ℝ := (∏ i : Fin n, cG i.succ.succ) * (∏ i : Fin n, cE i.succ) with hK
      have hK0 : 0 ≤ K := mul_nonneg (Finset.prod_nonneg fun i _ => hcG _)
        (Finset.prod_nonneg fun i _ => hcE _)
      have hinner : ∀ t', 0 ≤ applyR (G (Fin.succ 0)) T t' ∧
          applyR (G (Fin.succ 0)) T t' ≤ K * cG (Fin.succ 0) * w t' := by
        intro t'
        constructor
        · exact Finset.sum_nonneg fun t'' _ => mul_nonneg (hG _ _ _) (IH t'').1
        · calc applyR (G (Fin.succ 0)) T t' = ∑ t'', G (Fin.succ 0) t' t'' * T t'' := rfl
            _ ≤ ∑ t'', G (Fin.succ 0) t' t'' * (K * w t'') :=
                Finset.sum_le_sum fun t'' _ => mul_le_mul_of_nonneg_left (IH t'').2 (hG _ _ _)
            _ = K * ∑ t'', G (Fin.succ 0) t' t'' * w t'' := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun _ _ => by ring
            _ ≤ K * (cG (Fin.succ 0) * w t') := mul_le_mul_of_nonneg_left (hGr _ t') hK0
            _ = K * cG (Fin.succ 0) * w t' := by ring
      intro t
      have hprod : (∏ i : Fin (n + 1), cG i.succ) * (∏ i, cE i) =
          K * cG (Fin.succ 0) * cE 0 := by
        rw [Fin.prod_univ_succ (f := fun i : Fin (n + 1) => cG i.succ),
          Fin.prod_univ_succ (f := cE)]
        simp only [hK]
        ring
      have hKc : 0 ≤ K * cG (Fin.succ 0) := mul_nonneg hK0 (hcG _)
      constructor
      · exact Finset.sum_nonneg fun t' _ => mul_nonneg (hE _ _ _) (hinner t').1
      · change ∑ t', E 0 t t' * applyR (G (Fin.succ 0)) T t' ≤ _
        rw [hprod]
        calc ∑ t', E 0 t t' * applyR (G (Fin.succ 0)) T t'
            ≤ ∑ t', E 0 t t' * (K * cG (Fin.succ 0) * w t') :=
              Finset.sum_le_sum fun t' _ => mul_le_mul_of_nonneg_left (hinner t').2 (hE _ _ _)
          _ = K * cG (Fin.succ 0) * ∑ t', E 0 t t' * w t' := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ => by ring
          _ ≤ K * cG (Fin.succ 0) * (cE 0 * w t) := mul_le_mul_of_nonneg_left (hEr 0 t) hKc
          _ = K * cG (Fin.succ 0) * cE 0 * w t := by ring

/-- The path sum is at most the product of the row constants times the weighted start mass. -/
theorem pathSumR_le (w : β → ℝ) (hw : ∀ t, 0 ≤ w t) (n : ℕ)
    (G : Fin (n + 1) → β → β → ℝ) (E : Fin n → β → β → ℝ)
    (cG : Fin (n + 1) → ℝ) (cE : Fin n → ℝ)
    (hG : ∀ i s t, 0 ≤ G i s t) (hE : ∀ i s t, 0 ≤ E i s t)
    (hcG : ∀ i, 0 ≤ cG i) (hcE : ∀ i, 0 ≤ cE i)
    (hGr : ∀ i s, ∑ t, G i s t * w t ≤ cG i * w s)
    (hEr : ∀ i s, ∑ t, E i s t * w t ≤ cE i * w s)
    (u v : β → ℝ) (hu : ∀ s, 0 ≤ u s) (hv0 : ∀ t, 0 ≤ v t) (hvw : ∀ t, v t ≤ w t) :
    pathSumR n G E u v ≤ (∏ i, cG i) * (∏ i, cE i) * ∑ s, u s * w s := by
  rw [pathSumR_eq]
  have hT := tailR_bound w hw n G E cG cE hG hE hcG hcE hGr hEr v hv0 hvw
  set K : ℝ := (∏ i : Fin n, cG i.succ) * (∏ i, cE i) with hK
  have hK0 : 0 ≤ K := mul_nonneg (Finset.prod_nonneg fun i _ => hcG _)
    (Finset.prod_nonneg fun i _ => hcE _)
  have hprod : (∏ i, cG i) * (∏ i, cE i) = cG 0 * K := by
    rw [Fin.prod_univ_succ (f := cG)]
    simp only [hK]
    ring
  rw [hprod, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc ∑ t, u s * G 0 s t * tailR n G E v t
      ≤ ∑ t, u s * G 0 s t * (K * w t) :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hT t).2
          (mul_nonneg (hu s) (hG _ _ _))
    _ = u s * K * ∑ t, G 0 s t * w t := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ u s * K * (cG 0 * w s) := mul_le_mul_of_nonneg_left (hGr 0 s) (mul_nonneg (hu s) hK0)
    _ = cG 0 * K * (u s * w s) := by ring

end Erdos821.P3High
