import Mathlib

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

lemma pow_groups_le_rpow (C : ℝ) (hC : 0 < C) (cardGroups : ℕ) (C0 L K : ℝ)
    (_hC0 : 0 < C0) (hL1 : 1 < L) (hK0 : 0 ≤ K) (hK : C0 * Real.log C ≤ K)
    (hcard : (cardGroups : ℝ) ≤ C0 * Real.log L) :
    C ^ cardGroups ≤ L ^ K := by
  classical
  have hLpos : 0 < L := lt_trans zero_lt_one hL1
  have hlogL_nonneg : 0 ≤ Real.log L := le_of_lt (Real.log_pos hL1)
  by_cases hC1 : 1 ≤ C
  · -- C ≥ 1, log C ≥ 0, use exp monotonic with card bound (preserves direction since log C ≥ 0)
    have hlogC_nonneg : 0 ≤ Real.log C := Real.log_nonneg hC1
    have hCpow_eq : C ^ cardGroups = Real.exp (Real.log C * (cardGroups : ℝ)) := by
      have h1 : C ^ ((cardGroups : ℝ)) = Real.exp (Real.log C * (cardGroups : ℝ)) :=
        (Real.rpow_def_of_pos hC _).symm ▸ rfl
      -- Actually rpow_def: C^(card:ℝ) (rpow) = exp(log C * card). And rpow_natCast: C^(card:ℝ) (rpow) = C^card (Nat pow). Good!
      have h2 : C ^ ((cardGroups : ℝ)) = C ^ cardGroups := Real.rpow_natCast C cardGroups
      rw [h2] at h1
      -- h1 : C^card (Nat) = exp(...)? Wait h1 after rw? Let's be careful:
      -- h1 originally: C^(card:ℝ) (rpow) = exp(...). h2: C^(card:ℝ) (rpow) = C^card (Nat). So rw h2 at h1 replaces LHS rpow with Nat pow? Actually h1 LHS is rpow, h2 LHS is rpow, RHS Nat pow. rw h2 at h1 replaces rpow in h1 with Nat pow, giving Nat pow = exp. Good!
      exact h1
    have hLpow_eq : L ^ K = Real.exp (K * Real.log L) := by
      have h1 : L ^ K = Real.exp (Real.log L * K) := Real.rpow_def_of_pos hLpos K
      rw [mul_comm] at h1
      exact h1
      -- Actually rpow_def: L^K = exp(log L * K). Need K*log L vs log L*K? Same via mul_comm. Good!
    rw [hCpow_eq, hLpow_eq]
    apply Real.exp_le_exp.mpr
    -- Need log C * card ≤ K * log L
    have h1 : Real.log C * (cardGroups : ℝ) ≤ Real.log C * (C0 * Real.log L) := by
      apply mul_le_mul_of_nonneg_left hcard hlogC_nonneg
    have h2 : Real.log C * (C0 * Real.log L) = (C0 * Real.log C) * Real.log L := by
      ring_nf
    have h3 : (C0 * Real.log C) * Real.log L ≤ K * Real.log L := by
      apply mul_le_mul_of_nonneg_right hK hlogL_nonneg
    linarith
  · -- C < 1 (with 0<C<1), bound LHS ≤1 ≤ RHS (since K≥0, L>1 ⇒ L^K ≥1)
    push Not at hC1
    have hC_le_one : C ≤ 1 := le_of_lt hC1
    have hLHS_le_one : C ^ cardGroups ≤ (1:ℝ) := pow_le_one₀ hC.le hC_le_one
    have hRHS_ge_one : (1:ℝ) ≤ L ^ K := by
      -- 1^K =1 ≤ L^K since 1≤L and 0≤K (rpow monotonic in base? Need Real.one_le_rpow?)
      have h1 : (1:ℝ) ^ K = 1 := Real.one_rpow K
      have h2 : (1:ℝ) ^ K ≤ L ^ K := Real.rpow_le_rpow zero_le_one hL1.le hK0
      rwa [h1] at h2
    linarith

end Erdos821.P3Edge
