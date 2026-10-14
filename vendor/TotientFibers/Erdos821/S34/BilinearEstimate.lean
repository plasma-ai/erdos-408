import Erdos821.S34.BilinearBlocks
import Erdos821.S34.Core

set_option autoImplicit false

open scoped BigOperators Classical
open OAI.LargePrimeGaps

namespace Erdos821.S34.Proofs

theorem e_eq_bvExp (t : ℝ) : Core.e t = bvExp t := by
  unfold Core.e bvExp
  congr 1
  push_cast
  ring

private theorem interval_from_real_bounds (s : Finset ℤ) (X H : ℝ) (hH : 0 ≤ H)
    (hs : ∀ n ∈ s, X ≤ (n : ℝ) ∧ (n : ℝ) ≤ X + H) :
    ∀ n ∈ s, ⌈X⌉ ≤ n ∧ n < ⌈X⌉ + (⌊H⌋₊ + 1 : ℕ) := by
  intro n hn
  have hlo : ⌈X⌉ ≤ n := Int.ceil_le.mpr (hs n hn).1
  have hceil : X ≤ (⌈X⌉ : ℝ) := Int.le_ceil X
  have hoff : ((n - ⌈X⌉).toNat : ℝ) = (n : ℝ) - ⌈X⌉ := by
    exact_mod_cast (show ((n - ⌈X⌉).toNat : ℤ) = n - ⌈X⌉ by omega)
  have hnat : (n - ⌈X⌉).toNat ≤ ⌊H⌋₊ := Nat.le_floor (by rw [hoff]; linarith [(hs n hn).2])
  exact ⟨hlo, by omega⟩

/-- §3 integer bilinear estimate, including intervals with arbitrary origins
and coefficients with arbitrary holes in their support. -/
theorem integer_bilinear (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (U V N M α β : ℝ) (u : ℤ) (r : ℕ)
      (s t : Finset ℤ) (a b : ℤ → ℂ),
      1 ≤ U → 1 ≤ V → 1 ≤ r → Nat.Coprime u.natAbs r →
      α = (u : ℝ) / r + β → |β| ≤ (r : ℝ) ^ (-2 : ℤ) →
      (∀ n ∈ s, N ≤ (n : ℝ) ∧ (n : ℝ) ≤ N + C * U) →
      (∀ v ∈ t, M ≤ (v : ℝ) ∧ (v : ℝ) ≤ M + C * V) →
      ‖∑ n ∈ s, ∑ v ∈ t, a n * b v * Core.e (α * n * v)‖ ≤
        K * Real.sqrt (∑ n ∈ s, ‖a n‖ ^ 2) * Real.sqrt (∑ v ∈ t, ‖b v‖ ^ 2) *
          Real.sqrt (U + (1 + V / r) * (U + r * Real.log (2 * r))) := by
  let B : ℝ := max (C + 1) (2 * (1 + (Real.log 2)⁻¹))
  let K₂ : ℝ := (2 * C + 1) * B
  have hB₁ : C + 1 ≤ B := le_max_left _ _
  have hB₂ : 2 * (1 + (Real.log 2)⁻¹) ≤ B := le_max_right _ _
  have hBpos : 0 < B := lt_of_lt_of_le (by linarith) hB₁
  have hKpos : 0 < K₂ := mul_pos (by linarith) hBpos
  refine ⟨Real.sqrt K₂, Real.sqrt_pos.mpr hKpos, ?_⟩
  intro U V N M α β u r s t a b hU hV hr hu hα hβ hs ht
  have hUpos : 0 < U := by linarith
  have hVpos : 0 < V := by linarith
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hr₁ : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hβ' : |β| ≤ 1 / (r : ℝ) ^ 2 := by
    simpa only [zpow_neg, zpow_ofNat, one_div] using hβ
  have hti : ∀ v ∈ t, ⌈M⌉ ≤ v ∧ (v : ℝ) - ⌈M⌉ ≤ C * V := by
    intro v hv
    exact ⟨Int.ceil_le.mpr (ht v hv).1, by linarith [(ht v hv).2, Int.le_ceil M]⟩
  have hsi := interval_from_real_bounds s N (C * U) (by positivity) hs
  let Ea : ℝ := ∑ n ∈ s, ‖a n‖ ^ 2
  let Eb : ℝ := ∑ v ∈ t, ‖b v‖ ^ 2
  let F : ℝ := U + (1 + V / r) * (U + r * Real.log (2 * r))
  have hEa : 0 ≤ Ea := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hEb : 0 ≤ Eb := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (2 * (r : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogpos : 0 < Real.log (2 * (r : ℝ)) := hlog₂.trans_le hlog
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hcount : 2 * (C * V) / r + 1 ≤ (2 * C + 1) * (1 + V / r) := by
    have hvr : 0 ≤ V / (r : ℝ) := by positivity
    rw [show 2 * (C * V) / (r : ℝ) = 2 * C * (V / r) by ring]
    nlinarith
  have hlen : ((⌊C * U⌋₊ + 1 : ℕ) : ℝ) ≤ B * U := by
    have hf := Nat.floor_le (show 0 ≤ C * U by positivity)
    have hcu : (C + 1) * U ≤ B * U := mul_le_mul_of_nonneg_right hB₁ hUpos.le
    push_cast
    linarith
  have hH : (harmonic (2 * r) : ℝ) ≤ 1 + Real.log (2 * (r : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using harmonic_le_one_add_log (2 * r)
  have hlogcost : 1 + Real.log (2 * (r : ℝ)) ≤
      (1 + (Real.log 2)⁻¹) * Real.log (2 * (r : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hlog₂.le)
    rw [inv_mul_cancel₀ (ne_of_gt hlog₂)] at hh
    nlinarith
  have hHbound : 2 * (r : ℝ) * (harmonic (2 * r) : ℝ) ≤
      B * ((r : ℝ) * Real.log (2 * (r : ℝ))) := by
    have hh := mul_le_mul_of_nonneg_left (hH.trans hlogcost) (show 0 ≤ 2 * (r : ℝ) by positivity)
    have hb := mul_le_mul_of_nonneg_right hB₂
      (show 0 ≤ (r : ℝ) * Real.log (2 * (r : ℝ)) by positivity)
    nlinarith
  have hkernel : ((⌊C * U⌋₊ + 1 : ℕ) : ℝ) + 2 * r * (harmonic (2 * r) : ℝ) ≤
      B * (U + r * Real.log (2 * r)) := by
    nlinarith [hlen, hHbound]
  have henergy : (∑ v ∈ t, ‖∑ n ∈ s, a n * bvExp (α * n * v)‖ ^ 2) ≤ K₂ * F * Ea := by
    have he := rational_block_large_sieve α β u r hr hu hα hβ' t ⌈M⌉ (C * V)
      (by positivity) hti s ⌈N⌉ (⌊C * U⌋₊ + 1) a hsi
    calc
      _ ≤ (2 * (C * V) / r + 1) *
          (((⌊C * U⌋₊ + 1 : ℕ) : ℝ) + 2 * r * (harmonic (2 * r) : ℝ)) * Ea := he
      _ ≤ (2 * (C * V) / r + 1) * (B * (U + r * Real.log (2 * r))) * Ea := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hkernel (by positivity)) hEa
      _ ≤ ((2 * C + 1) * (1 + V / r)) * (B * (U + r * Real.log (2 * r))) * Ea := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcount (by positivity)) hEa
      _ = K₂ * ((1 + V / r) * (U + r * Real.log (2 * r))) * Ea := by dsimp [K₂]; ring
      _ ≤ K₂ * F * Ea := by
        apply mul_le_mul_of_nonneg_right _ hEa
        apply mul_le_mul_of_nonneg_left _ hKpos.le
        dsimp [F]
        linarith
  have heq : (∑ n ∈ s, ∑ v ∈ t, a n * b v * Core.e (α * n * v)) =
      ∑ v ∈ t, b v * (∑ n ∈ s, a n * bvExp (α * n * v)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [e_eq_bvExp]
    ring
  have hsq : ‖∑ n ∈ s, ∑ v ∈ t, a n * b v * Core.e (α * n * v)‖ ^ 2 ≤ K₂ * Ea * Eb * F := by
    rw [heq]
    have hc := norm_sum_mul_sq t b (fun v => ∑ n ∈ s, a n * bvExp (α * n * v))
    have he := mul_le_mul_of_nonneg_left henergy hEb
    have hh := hc.trans he
    convert hh using 1 <;> dsimp [Eb] <;> ring
  have hrhs : 0 ≤ Real.sqrt K₂ * Real.sqrt Ea * Real.sqrt Eb * Real.sqrt F := by positivity
  have hrhssq : (Real.sqrt K₂ * Real.sqrt Ea * Real.sqrt Eb * Real.sqrt F) ^ 2 = K₂ * Ea * Eb * F := by
    simp only [mul_pow, Real.sq_sqrt hKpos.le, Real.sq_sqrt hEa, Real.sq_sqrt hEb, Real.sq_sqrt hF]
  change ‖∑ n ∈ s, ∑ v ∈ t, a n * b v * Core.e (α * n * v)‖ ≤
    Real.sqrt K₂ * Real.sqrt Ea * Real.sqrt Eb * Real.sqrt F
  apply (sq_le_sq₀ (norm_nonneg _) hrhs).mp
  simpa only [hrhssq] using hsq

end Erdos821.S34.Proofs
