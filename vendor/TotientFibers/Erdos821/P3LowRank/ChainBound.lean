import Mathlib

/-! Finite alternating kernel chains: path sums and weighted operator-norm composition. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Lowrank

variable {β : Type*} [Fintype β]

/-- Weighted `ℓ²` norm on a finite type. -/
def wnorm (mass : β → ℝ) (h : β → ℂ) : ℝ := Real.sqrt (∑ s, mass s * ‖h s‖ ^ 2)

/-- Kernel application; the kernel already contains the target integration. -/
def applyK (K : β → β → ℂ) (h : β → ℂ) : β → ℂ := fun s => ∑ t, K s t * h t

/-- Bilinear operator-norm bound on the whole finite type. -/
def FinNormBound (mass : β → ℝ) (K : β → β → ℂ) (C : ℝ) : Prop :=
  ∀ f g : β → ℂ, ‖∑ a, ∑ b, (mass a : ℂ) * star (f a) * K a b * g b‖ ≤
    C * wnorm mass f * wnorm mass g

theorem wnorm_nonneg (mass : β → ℝ) (h : β → ℂ) : 0 ≤ wnorm mass h := Real.sqrt_nonneg _

theorem wnorm_sq (mass : β → ℝ) (hm : ∀ s, 0 ≤ mass s) (h : β → ℂ) :
    wnorm mass h ^ 2 = ∑ s, mass s * ‖h s‖ ^ 2 := by
  unfold wnorm
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun s _ => mul_nonneg (hm s) (sq_nonneg _)

theorem applyK_bound (mass : β → ℝ) (hm : ∀ s, 0 ≤ mass s) (K : β → β → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hK : FinNormBound mass K C) (h : β → ℂ) :
    wnorm mass (applyK K h) ≤ C * wnorm mass h := by
  set x := applyK K h with hx
  have heq : ((∑ s, mass s * ‖x s‖ ^ 2 : ℝ) : ℂ) =
      ∑ a, ∑ b, (mass a : ℂ) * star (x a) * K a b * h b := by
    push_cast
    apply Finset.sum_congr rfl
    intro a _
    have hxa : x a = ∑ b, K a b * h b := rfl
    calc (mass a : ℂ) * (‖x a‖ : ℂ) ^ 2 = (mass a : ℂ) * star (x a) * x a := by
          rw [mul_assoc, Complex.star_def, Complex.conj_mul']
      _ = _ := by
          rw [hxa, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          rw [← hxa]
          ring
  have hle : wnorm mass x ^ 2 ≤ C * wnorm mass x * wnorm mass h := by
    rw [wnorm_sq mass hm x]
    have hnn : 0 ≤ ∑ s, mass s * ‖x s‖ ^ 2 :=
      Finset.sum_nonneg fun s _ => mul_nonneg (hm s) (sq_nonneg _)
    calc ∑ s, mass s * ‖x s‖ ^ 2 = ‖((∑ s, mass s * ‖x s‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ = _ := by rw [heq]
      _ ≤ _ := hK x h
  have hw := wnorm_nonneg mass x
  have hh := wnorm_nonneg mass h
  rcases hw.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg hC hh
  · have : wnorm mass x * wnorm mass x ≤ wnorm mass x * (C * wnorm mass h) := by
      nlinarith
    exact le_of_mul_le_mul_left this hpos

/-- Sum over alternating state paths: ghost kernels on `(b i, a i)`, edges on `(a i, b (i+1))`. -/
def pathSum (n : ℕ) (G : Fin (n + 1) → β → β → ℂ) (E : Fin n → β → β → ℂ) (u v : β → ℂ) : ℂ :=
  ∑ b : Fin (n + 1) → β, ∑ a : Fin (n + 1) → β,
    u (b 0) * (∏ i, G i (b i) (a i)) * (∏ i : Fin n, E i (a i.castSucc) (b i.succ)) *
      v (a (Fin.last n))

/-- The vector produced by everything after the first ghost kernel. -/
def tailVec : (n : ℕ) → (Fin (n + 1) → β → β → ℂ) → (Fin n → β → β → ℂ) → (β → ℂ) → β → ℂ
  | 0, _, _, v => v
  | n + 1, G, E, v =>
      applyK (E 0) (applyK (G (Fin.succ 0)) (tailVec n (fun i => G i.succ) (fun i => E i.succ) v))

theorem sum_fin_cons {M : Type*} [AddCommMonoid M] (n : ℕ) (f : (Fin (n + 1) → β) → M) :
    ∑ b : Fin (n + 1) → β, f b = ∑ b0 : β, ∑ b' : Fin n → β, f (Fin.cons b0 b') := by
  rw [← (Fin.consEquiv fun _ => β).sum_comp, Fintype.sum_prod_type]
  rfl

theorem pathSum_eq : ∀ (n : ℕ) (G : Fin (n + 1) → β → β → ℂ) (E : Fin n → β → β → ℂ)
    (u v : β → ℂ), pathSum n G E u v = ∑ s, ∑ t, u s * G 0 s t * tailVec n G E v t := by
  intro n
  induction n with
  | zero =>
      intro G E u v
      unfold pathSum
      rw [sum_fin_cons]
      apply Finset.sum_congr rfl
      intro s _
      rw [Fintype.sum_unique]
      rw [sum_fin_cons]
      apply Finset.sum_congr rfl
      intro t _
      rw [Fintype.sum_unique]
      simp [tailVec, Fin.last]
  | succ n ih =>
      intro G E u v
      unfold pathSum
      rw [sum_fin_cons]
      apply Finset.sum_congr rfl
      intro s _
      simp_rw [sum_fin_cons (n := n + 1)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      have hih := ih (fun i => G i.succ) (fun i => E i.succ) (E 0 t) v
      simp only [pathSum] at hih
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
      simp only [tailVec, applyK, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s' _
      apply Finset.sum_congr rfl
      intro t' _
      ring

theorem tailVec_bound (mass : β → ℝ) (hm : ∀ s, 0 ≤ mass s) (CG : ℝ) (hCG : 0 ≤ CG) :
    ∀ (n : ℕ) (G : Fin (n + 1) → β → β → ℂ) (E : Fin n → β → β → ℂ) (c : Fin n → ℝ),
      (∀ i, 0 ≤ c i) → (∀ i, FinNormBound mass (G i) CG) →
      (∀ i, FinNormBound mass (E i) (c i)) → ∀ v : β → ℂ,
      wnorm mass (tailVec n G E v) ≤ CG ^ n * (∏ i, c i) * wnorm mass v := by
  intro n
  induction n with
  | zero =>
      intro G E c _ _ _ v
      simp [tailVec]
  | succ n ih =>
      intro G E c hc hG hE v
      have h1 := ih (fun i => G i.succ) (fun i => E i.succ) (fun i => c i.succ)
        (fun i => hc i.succ) (fun i => hG i.succ) (fun i => hE i.succ) v
      set w := tailVec n (fun i => G i.succ) (fun i => E i.succ) v
      have h2 := applyK_bound mass hm (G (Fin.succ 0)) CG hCG (hG _) w
      have h3 := applyK_bound mass hm (E 0) (c 0) (hc 0) (hE 0) (applyK (G (Fin.succ 0)) w)
      have hprod : 0 ≤ ∏ i : Fin n, c i.succ := Finset.prod_nonneg fun i _ => hc i.succ
      change wnorm mass (applyK (E 0) (applyK (G (Fin.succ 0)) w)) ≤ _
      rw [Fin.prod_univ_succ]
      calc wnorm mass (applyK (E 0) (applyK (G (Fin.succ 0)) w))
          ≤ c 0 * wnorm mass (applyK (G (Fin.succ 0)) w) := h3
        _ ≤ c 0 * (CG * wnorm mass w) := mul_le_mul_of_nonneg_left h2 (hc 0)
        _ ≤ c 0 * (CG * (CG ^ n * (∏ i : Fin n, c i.succ) * wnorm mass v)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hCG) (hc 0)
        _ = _ := by ring

theorem pathSum_bound (mass : β → ℝ) (hm : ∀ s, 0 ≤ mass s) (CG : ℝ) (hCG : 0 ≤ CG)
    (n : ℕ) (G : Fin (n + 1) → β → β → ℂ) (E : Fin n → β → β → ℂ) (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hG : ∀ i, FinNormBound mass (G i) CG)
    (hE : ∀ i, FinNormBound mass (E i) (c i)) (f v : β → ℂ) :
    ‖pathSum n G E (fun s => (mass s : ℂ) * star (f s)) v‖ ≤
      CG ^ (n + 1) * (∏ i, c i) * wnorm mass f * wnorm mass v := by
  rw [pathSum_eq]
  have h1 := hG 0 f (tailVec n G E v)
  have h2 := tailVec_bound mass hm CG hCG n G E c hc hG hE v
  have hf := wnorm_nonneg mass f
  calc _ ≤ CG * wnorm mass f * wnorm mass (tailVec n G E v) := h1
    _ ≤ CG * wnorm mass f * (CG ^ n * (∏ i, c i) * wnorm mass v) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hCG hf)
    _ = _ := by ring

end Erdos821.P3Lowrank
