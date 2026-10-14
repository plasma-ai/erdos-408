import Erdos821.Blueprint.Graph

/-! Schur bounds on arbitrary state spaces, proved on finite supports. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

theorem finite_support_schur {α : Type*} (mass w : α → ℝ) (K : α → α → ℂ) (R C : ℝ)
    (hm : ∀ a, 0 ≤ mass a) (hw : ∀ a, 0 < w a) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ a (t : Finset α), ∑ b ∈ t, ‖K a b‖ * w b ≤ R * w a)
    (hcol : ∀ b (s : Finset α), ∑ a ∈ s, mass a * ‖K a b‖ * w a ≤ C * mass b * w b) :
    NormBound mass K (Real.sqrt (R * C)) := by
  classical
  have hK (a b : α) : 0 ≤ ‖K a b‖ := norm_nonneg _
  intro s t f g
  let U : ℝ := ∑ a ∈ s, mass a * ‖f a‖ ^ 2
  let V : ℝ := ∑ b ∈ t, mass b * ‖g b‖ ^ 2
  let S : Finset (α × α) := s.product t
  let rho (u : α × α) : ℝ := mass u.1 * ‖K u.1 u.2‖ * ‖f u.1‖ * ‖g u.2‖
  let F (u : α × α) : ℝ := mass u.1 * ‖K u.1 u.2‖ * w u.2 / w u.1 * ‖f u.1‖ ^ 2
  let G (u : α × α) : ℝ := mass u.1 * ‖K u.1 u.2‖ * w u.1 / w u.2 * ‖g u.2‖ ^ 2
  have hU : 0 ≤ U := Finset.sum_nonneg (fun a _ => mul_nonneg (hm a) (sq_nonneg _))
  have hV : 0 ≤ V := Finset.sum_nonneg (fun b _ => mul_nonneg (hm b) (sq_nonneg _))
  have hF (u : α × α) : 0 ≤ F u :=
    mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (hm u.1) (hK u.1 u.2))
      (hw u.2).le) (hw u.1).le) (sq_nonneg _)
  have hG (u : α × α) : 0 ≤ G u :=
    mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (hm u.1) (hK u.1 u.2))
      (hw u.1).le) (hw u.2).le) (sq_nonneg _)
  have hsq (u : α × α) : rho u ^ 2 = F u * G u := by
    dsimp only [rho, F, G]
    field_simp [ne_of_gt (hw u.1), ne_of_gt (hw u.2)]
  have hrowT (a : α) : (∑ b ∈ t, ‖K a b‖ * w b) ≤ R * w a := hrow a t
  have hcolS (b : α) : (∑ a ∈ s, mass a * ‖K a b‖ * w a) ≤ C * mass b * w b := hcol b s
  have hFs : (∑ u ∈ S, F u) ≤ R * U := by
    calc
      (∑ u ∈ S, F u) = ∑ a ∈ s, ∑ b ∈ t, F (a, b) := Finset.sum_product s t F
      _ ≤ ∑ a ∈ s, R * (mass a * ‖f a‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro a _
        have ha : 0 ≤ mass a * ‖f a‖ ^ 2 / w a :=
          div_nonneg (mul_nonneg (hm a) (sq_nonneg _)) (hw a).le
        calc
          _ = (mass a * ‖f a‖ ^ 2 / w a) * (∑ b ∈ t, ‖K a b‖ * w b) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            dsimp only [F]
            simp only [div_eq_mul_inv]
            ring
          _ ≤ (mass a * ‖f a‖ ^ 2 / w a) * (R * w a) :=
            mul_le_mul_of_nonneg_left (hrowT a) ha
          _ = R * (mass a * ‖f a‖ ^ 2) := by
            field_simp [ne_of_gt (hw a)]
      _ = R * U := (Finset.mul_sum s (fun a => mass a * ‖f a‖ ^ 2) R).symm
  have hGs : (∑ u ∈ S, G u) ≤ C * V := by
    calc
      (∑ u ∈ S, G u) = ∑ a ∈ s, ∑ b ∈ t, G (a, b) := Finset.sum_product s t G
      _ = ∑ b ∈ t, ∑ a ∈ s, G (a, b) := Finset.sum_comm
      _ ≤ ∑ b ∈ t, C * (mass b * ‖g b‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro b _
        have hb : 0 ≤ ‖g b‖ ^ 2 / w b := div_nonneg (sq_nonneg _) (hw b).le
        calc
          _ = (‖g b‖ ^ 2 / w b) * (∑ a ∈ s, mass a * ‖K a b‖ * w a) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            dsimp only [G]
            simp only [div_eq_mul_inv]
            ring
          _ ≤ (‖g b‖ ^ 2 / w b) * (C * mass b * w b) :=
            mul_le_mul_of_nonneg_left (hcolS b) hb
          _ = C * (mass b * ‖g b‖ ^ 2) := by
            field_simp [ne_of_gt (hw b)]
      _ = C * V := (Finset.mul_sum t (fun b => mass b * ‖g b‖ ^ 2) C).symm
  have hcs : (∑ u ∈ S, rho u) ^ 2 ≤ (∑ u ∈ S, F u) * (∑ u ∈ S, G u) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
      (fun u _ => hF u) (fun u _ => hG u) (fun u _ => (hsq u).le)
  have hnormEntry (a b : α) :
      ‖(mass a : ℂ) * star (f a) * K a b * g b‖ = rho (a, b) := by
    simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hm a)]
    dsimp only [rho]
    ring
  have hnorm :
      ‖∑ a ∈ s, ∑ b ∈ t, (mass a : ℂ) * star (f a) * K a b * g b‖ ≤
        ∑ u ∈ S, rho u := by
    calc
      _ ≤ ∑ a ∈ s, ‖∑ b ∈ t, (mass a : ℂ) * star (f a) * K a b * g b‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ s, ∑ b ∈ t, ‖(mass a : ℂ) * star (f a) * K a b * g b‖ :=
        Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
      _ = ∑ a ∈ s, ∑ b ∈ t, rho (a, b) := by simp only [hnormEntry]
      _ = ∑ u ∈ S, rho u := (Finset.sum_product s t rho).symm
  have hpos : 0 ≤ ∑ u ∈ S, rho u := Finset.sum_nonneg (fun u _ =>
    mul_nonneg (mul_nonneg (mul_nonneg (hm u.1) (hK u.1 u.2)) (norm_nonneg _)) (norm_nonneg _))
  let B : ℝ := Real.sqrt (R * C) * Real.sqrt U * Real.sqrt V
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)
  have hBsq : B ^ 2 = (R * U) * (C * V) := by
    dsimp only [B]
    simp only [mul_pow, Real.sq_sqrt (mul_nonneg hR hC), Real.sq_sqrt hU, Real.sq_sqrt hV]
    ring
  have hfinal :
      ‖∑ a ∈ s, ∑ b ∈ t, (mass a : ℂ) * star (f a) * K a b * g b‖ ^ 2 ≤ B ^ 2 := by
    calc
      _ ≤ (∑ u ∈ S, rho u) ^ 2 := (sq_le_sq₀ (norm_nonneg _) hpos).mpr hnorm
      _ ≤ (∑ u ∈ S, F u) * (∑ u ∈ S, G u) := hcs
      _ ≤ (R * U) * (C * V) := mul_le_mul hFs hGs
        (Finset.sum_nonneg (fun u _ => hG u)) (mul_nonneg hR hU)
      _ = B ^ 2 := hBsq.symm
  exact (sq_le_sq₀ (norm_nonneg _) hB).mp hfinal

/-- A countable Schur certificate also controls arbitrary local restrictions
and phases that are dominated by the original absolute matrix entries. -/
theorem weightedBounds_domination {α : Type*} (mass w : α → ℝ)
    (K H : α → α → ℂ) (C : ℝ) (hm : ∀ a, 0 ≤ mass a) (hw : ∀ a, 0 < w a)
    (hC : 0 ≤ C) (hH : WeightedBounds mass w H C)
    (hKH : ∀ a b, ‖K a b‖ ≤ ‖H a b‖) : NormBound mass K C := by
  have hb := finite_support_schur mass w K C C hm hw hC hC
  have hrow (a : α) (t : Finset α) : ∑ b ∈ t, ‖K a b‖ * w b ≤ C * w a := by
    calc
      _ ≤ ∑ b ∈ t, ‖H a b‖ * w b := Finset.sum_le_sum
        (fun b _ => mul_le_mul_of_nonneg_right (hKH a b) (hw b).le)
      _ ≤ ∑' b, ‖H a b‖ * w b := (hH.1 a).1.sum_le_tsum t
        (fun b _ => mul_nonneg (norm_nonneg _) (hw b).le)
      _ ≤ _ := (hH.1 a).2
  have hcol (b : α) (s : Finset α) : ∑ a ∈ s, mass a * ‖K a b‖ * w a ≤ C * mass b * w b := by
    calc
      _ ≤ ∑ a ∈ s, mass a * ‖H a b‖ * w a := Finset.sum_le_sum
        (fun a _ => mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hKH a b) (hm a)) (hw a).le)
      _ ≤ ∑' a, mass a * ‖H a b‖ * w a := (hH.2 b).1.sum_le_tsum s
        (fun a _ => mul_nonneg (mul_nonneg (hm a) (norm_nonneg _)) (hw a).le)
      _ ≤ _ := (hH.2 b).2
  simpa only [Real.sqrt_mul_self hC] using hb hrow hcol

theorem normBound_add {α : Type*} (mass : α → ℝ) (K H : α → α → ℂ) (C D : ℝ)
    (hK : NormBound mass K C) (hH : NormBound mass H D) :
    NormBound mass (fun a b => K a b + H a b) (C + D) := by
  intro s t f g
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add (hK s t f g) (hH s t f g)
    _ = _ := by ring


end Erdos821.S2Core
