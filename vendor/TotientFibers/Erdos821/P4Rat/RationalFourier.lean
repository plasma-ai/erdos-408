import Erdos821.Blueprint.Analytic
import OAI.NumberTheory.PrimeGaps.MultiplicativeSieve

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators Classical ComplexConjugate

namespace Erdos821.P4Rat

open Blueprint.Analytic

/-- §3 rational Fourier expansion, on the group of reduced residue classes.
Suggested proof: coefficient = normalized character transform of the unit
phase; reconstruct by DirichletCharacter.sum_char_inv_mul_char_eq, and use
OAI.LargePrimeGaps.character_transform_bound for the L1 estimate. -/
def RationalFourierTask : Prop :=
  ∀ (r : ℕ) (u : ℤ), 1 ≤ r →
    ∃ c : DirichletCharacter ℂ r → ℂ,
      (∑ ψ, ‖c ψ‖) ≤ Real.sqrt (r.totient : ℝ) ∧
      ∀ n : ℕ, Nat.Coprime n r →
        e ((u : ℝ) * n / r) = ∑ ψ, c ψ * ψ (n : ZMod r)

lemma rf_e_norm (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  have h : (2 * Real.pi * t * Complex.I : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

lemma rf_e_add_int (t : ℝ) (k : ℤ) : e (t + (k : ℝ)) = e t := by
  have hcast : (((t + (k : ℝ)) : ℝ) : ℂ) = ((t : ℝ) : ℂ) + ((k : ℤ) : ℂ) := by
    push_cast
    ring
  have harg : (2 * (Real.pi : ℂ) * (((t + (k : ℝ)) : ℝ) : ℂ) * Complex.I : ℂ)
      = 2 * (Real.pi : ℂ) * ((t : ℝ) : ℂ) * Complex.I
        + ((k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hcast]
    ring
  have h1 : Complex.exp (((k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I k
  unfold e
  rw [harg, Complex.exp_add, h1, mul_one]

lemma rf_e_nat_mod (r : ℕ) (hr : 0 < r) (u : ℤ) (n : ℕ) :
    e ((u : ℝ) * (n : ℝ) / (r : ℝ)) = e ((u : ℝ) * ((n % r : ℕ) : ℝ) / (r : ℝ)) := by
  have hr_ne : (r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  have hdivmod : n / r * r + n % r = n := by
    rw [mul_comm]
    exact Nat.div_add_mod n r
  have hcast : (n : ℝ) = ((n / r : ℕ) : ℝ) * (r : ℝ) + ((n % r : ℕ) : ℝ) := by
    exact_mod_cast hdivmod.symm
  have hk : (((u * ((n / r : ℕ) : ℤ) : ℤ)) : ℝ) = (u : ℝ) * ((n / r : ℕ) : ℝ) := by
    rw [Int.cast_mul, Int.cast_natCast]
  have hsplit : (u : ℝ) * (n : ℝ) / (r : ℝ)
      = (u : ℝ) * ((n % r : ℕ) : ℝ) / (r : ℝ) + ((u * ((n / r : ℕ) : ℤ) : ℤ) : ℝ) := by
    rw [hk, hcast]
    field_simp
    ring
  rw [hsplit]
  exact rf_e_add_int _ _

noncomputable def rf_unitPhase (r : ℕ) (u : ℤ) (v : (ZMod r)ˣ) : ℂ :=
  e ((u : ℝ) * ((v.val.val : ℕ) : ℝ) / (r : ℝ))

lemma rf_unitPhase_norm (r : ℕ) (u : ℤ) (v : (ZMod r)ˣ) : ‖rf_unitPhase r u v‖ = 1 :=
  rf_e_norm _

noncomputable def rf_coeff (r : ℕ) [NeZero r] (u : ℤ) (ψ : DirichletCharacter ℂ r) : ℂ :=
  ((r.totient : ℂ))⁻¹ * ∑ v : (ZMod r)ˣ, rf_unitPhase r u v * star (ψ (v.val : ZMod r))

lemma rf_star_eq (r : ℕ) [NeZero r] (ψ : DirichletCharacter ℂ r) (v : (ZMod r)ˣ) :
    star (ψ (v.val : ZMod r)) = ψ ((v.val : ZMod r)⁻¹) := by
  simpa [RCLike.star_def] using OAI.LargePrimeGaps.conj_character_unit (q := r) ψ v

theorem RationalFourierTask_proof : RationalFourierTask := by
  intro r u hr
  have hr_pos : 0 < r := by omega
  have hNe : NeZero r := ⟨by omega⟩
  have hphi_pos : 0 < r.totient := Nat.totient_pos.mpr hr_pos
  have hphi_posR : (0 : ℝ) < (r.totient : ℝ) := by exact_mod_cast hphi_pos
  have hphi_nonnegR : (0 : ℝ) ≤ (r.totient : ℝ) := le_of_lt hphi_posR
  have hphi_neC : ((r.totient : ℕ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hphi_pos
  have hexp_ne : Monoid.exponent ((ZMod r)ˣ) ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have hNeExp : NeZero ((Monoid.exponent ((ZMod r)ˣ) : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr hexp_ne⟩
  refine ⟨rf_coeff r u, ?_, ?_⟩
  · -- L1 bound
    have hnorm_c : ∀ ψ, ‖rf_coeff r u ψ‖
        = (r.totient : ℝ)⁻¹ * ‖∑ v : (ZMod r)ˣ, rf_unitPhase r u v * star (ψ (v.val : ZMod r))‖ := by
      intro ψ
      unfold rf_coeff
      rw [norm_mul]
      have hnorm_inv : ‖((r.totient : ℂ))⁻¹‖ = (r.totient : ℝ)⁻¹ := by
        rw [norm_inv, Complex.norm_natCast]
      rw [hnorm_inv]
    have hsum_f : (∑ v : (ZMod r)ˣ, ‖rf_unitPhase r u v‖ ^ 2) = (r.totient : ℝ) := by
      have h1 : ∀ v : (ZMod r)ˣ, ‖rf_unitPhase r u v‖ ^ 2 = (1 : ℝ) := by
        intro v
        rw [rf_unitPhase_norm, one_pow]
      simp [h1, ZMod.card_units_eq_totient]
    have hbound := OAI.LargePrimeGaps.character_transform_bound
      (q := r) (fun v => rf_unitPhase r u v)
    rw [hsum_f] at hbound
    have hstar_inv : ∀ (ψ : DirichletCharacter ℂ r) (v : (ZMod r)ˣ),
        rf_unitPhase r u v * star (ψ (v.val : ZMod r))
          = rf_unitPhase r u v * ψ⁻¹ (v.val : ZMod r) := by
      intro ψ v
      rw [MulChar.star_apply']
    have hS_eq : (∑ ψ : DirichletCharacter ℂ r,
          ‖∑ v : (ZMod r)ˣ, rf_unitPhase r u v * star (ψ (v.val : ZMod r))‖ ^ 2)
        = ∑ ψ : DirichletCharacter ℂ r,
          ‖∑ v : (ZMod r)ˣ, rf_unitPhase r u v * ψ⁻¹ (v.val : ZMod r)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro ψ _
      have hInner : (∑ v : (ZMod r)ˣ, rf_unitPhase r u v * star (ψ (v.val : ZMod r)))
          = ∑ v : (ZMod r)ˣ, rf_unitPhase r u v * ψ⁻¹ (v.val : ZMod r) :=
        Finset.sum_congr rfl (fun v _ => hstar_inv ψ v)
      rw [hInner]
    have hBij : (∑ ψ : DirichletCharacter ℂ r,
          ‖∑ v : (ZMod r)ˣ, rf_unitPhase r u v * ψ⁻¹ (v.val : ZMod r)‖ ^ 2)
        = ∑ ψ : DirichletCharacter ℂ r,
          ‖∑ v : (ZMod r)ˣ, rf_unitPhase r u v * ψ (v.val : ZMod r)‖ ^ 2 :=
      Fintype.sum_bijective (fun ψ : DirichletCharacter ℂ r => ψ⁻¹)
        inv_involutive.bijective _ _ (fun _ => rfl)
    have hS_le : (∑ ψ : DirichletCharacter ℂ r,
          ‖∑ v : (ZMod r)ˣ, rf_unitPhase r u v * star (ψ (v.val : ZMod r))‖ ^ 2)
        ≤ (r.totient : ℝ) * (r.totient : ℝ) := by
      rw [hS_eq, hBij]
      exact hbound
    have hcard : Fintype.card (DirichletCharacter ℂ r) = r.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r
    have hCS : (∑ ψ : DirichletCharacter ℂ r, ‖rf_coeff r u ψ‖) ^ 2
        ≤ (Fintype.card (DirichletCharacter ℂ r) : ℝ)
          * ∑ ψ : DirichletCharacter ℂ r, ‖rf_coeff r u ψ‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    rw [hcard] at hCS
    have hsum_c_sq : (∑ ψ : DirichletCharacter ℂ r, ‖rf_coeff r u ψ‖ ^ 2)
        = ((r.totient : ℝ))⁻¹ ^ 2 * ∑ ψ : DirichletCharacter ℂ r,
          ‖∑ v : (ZMod r)ˣ, rf_unitPhase r u v * star (ψ (v.val : ZMod r))‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ψ _
      rw [hnorm_c ψ, mul_pow]
    have hsum_c_le1 : (∑ ψ : DirichletCharacter ℂ r, ‖rf_coeff r u ψ‖ ^ 2) ≤ 1 := by
      rw [hsum_c_sq]
      have hle : ((r.totient : ℝ))⁻¹ ^ 2 * ∑ ψ : DirichletCharacter ℂ r,
          ‖∑ v : (ZMod r)ˣ, rf_unitPhase r u v * star (ψ (v.val : ZMod r))‖ ^ 2
          ≤ ((r.totient : ℝ))⁻¹ ^ 2 * ((r.totient : ℝ) * (r.totient : ℝ)) :=
        mul_le_mul_of_nonneg_left hS_le (sq_nonneg _)
      have heq : ((r.totient : ℝ))⁻¹ ^ 2 * ((r.totient : ℝ) * (r.totient : ℝ)) = 1 := by
        field_simp
      rw [heq] at hle
      exact hle
    have hSq_le : (∑ ψ : DirichletCharacter ℂ r, ‖rf_coeff r u ψ‖) ^ 2 ≤ (r.totient : ℝ) := by
      calc (∑ ψ, ‖rf_coeff r u ψ‖) ^ 2
          ≤ (r.totient : ℝ) * ∑ ψ, ‖rf_coeff r u ψ‖ ^ 2 := hCS
        _ ≤ (r.totient : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hsum_c_le1 hphi_nonnegR
        _ = (r.totient : ℝ) := mul_one _
    have hnn : 0 ≤ ∑ ψ : DirichletCharacter ℂ r, ‖rf_coeff r u ψ‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    exact (Real.le_sqrt hnn hphi_nonnegR).mpr hSq_le
  · -- reconstruction
    intro n hn
    have hUnit : IsUnit ((n : ℕ) : ZMod r) := (ZMod.isUnit_iff_coprime n r).mpr hn
    let un : (ZMod r)ˣ := hUnit.unit
    have hun : ((un.val : ZMod r)) = ((n : ℕ) : ZMod r) := IsUnit.unit_spec _
    have hInner : ∀ v : (ZMod r)ˣ,
        (∑ ψ : DirichletCharacter ℂ r, star (ψ (v.val : ZMod r)) * ψ (un.val : ZMod r))
          = if v.val = un.val then ((r.totient : ℕ) : ℂ) else 0 := by
      intro v
      have h1 : ∀ ψ : DirichletCharacter ℂ r,
          star (ψ (v.val : ZMod r)) * ψ (un.val : ZMod r)
            = ψ ((v.val : ZMod r)⁻¹) * ψ (un.val : ZMod r) := by
        intro ψ
        rw [rf_star_eq r ψ v]
      simp_rw [h1]
      exact DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ)
        (a := (v.val : ZMod r)) v.isUnit (un.val : ZMod r)
    have hf_un : rf_unitPhase r u un = e ((u : ℝ) * (n : ℝ) / (r : ℝ)) := by
      unfold rf_unitPhase
      have hval : ((un.val.val : ℕ)) = n % r := by
        rw [hun]
        exact ZMod.val_natCast r n
      rw [hval]
      exact (rf_e_nat_mod r hr_pos u n).symm
    have hRHS : (∑ ψ : DirichletCharacter ℂ r, rf_coeff r u ψ * ψ ((n : ℕ) : ZMod r))
        = ∑ ψ : DirichletCharacter ℂ r, rf_coeff r u ψ * ψ (un.val : ZMod r) := by
      apply Finset.sum_congr rfl
      intro ψ _
      rw [← hun]
    rw [hRHS]
    have hswap : (∑ ψ : DirichletCharacter ℂ r, rf_coeff r u ψ * ψ (un.val : ZMod r))
        = ((r.totient : ℕ) : ℂ)⁻¹ * ∑ v : (ZMod r)ˣ, rf_unitPhase r u v *
          (∑ ψ : DirichletCharacter ℂ r, star (ψ (v.val : ZMod r)) * ψ (un.val : ZMod r)) := by
      have h1 : ∀ ψ : DirichletCharacter ℂ r,
          rf_coeff r u ψ * ψ (un.val : ZMod r)
            = ((r.totient : ℕ) : ℂ)⁻¹
              * ((∑ v : (ZMod r)ˣ, rf_unitPhase r u v * star (ψ (v.val : ZMod r)))
                * ψ (un.val : ZMod r)) := by
        intro ψ
        unfold rf_coeff
        ring
      simp_rw [h1, ← Finset.mul_sum]
      have h2 : ∀ ψ : DirichletCharacter ℂ r,
          (∑ v : (ZMod r)ˣ, rf_unitPhase r u v * star (ψ (v.val : ZMod r))) * ψ (un.val : ZMod r)
            = ∑ v : (ZMod r)ˣ, rf_unitPhase r u v * star (ψ (v.val : ZMod r)) * ψ (un.val : ZMod r) := by
        intro ψ
        exact Finset.sum_mul _ _ _
      simp_rw [h2]
      rw [Finset.sum_comm]
      apply congrArg
      apply Finset.sum_congr rfl
      intro v _
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
    rw [hswap]
    simp_rw [hInner]
    have hcollapse : (∑ v : (ZMod r)ˣ,
          rf_unitPhase r u v * (if v.val = un.val then ((r.totient : ℕ) : ℂ) else 0))
        = rf_unitPhase r u un * ((r.totient : ℕ) : ℂ) := by
      have h1 : ∀ v : (ZMod r)ˣ, v ≠ un →
          rf_unitPhase r u v * (if v.val = un.val then ((r.totient : ℕ) : ℂ) else 0) = 0 := by
        intro v hv
        have hne : ¬ (v.val = un.val) := fun heq => hv (Units.ext heq)
        rw [if_neg hne, mul_zero]
      have h2 : rf_unitPhase r u un * (if un.val = un.val then ((r.totient : ℕ) : ℂ) else 0)
          = rf_unitPhase r u un * ((r.totient : ℕ) : ℂ) := by
        rw [if_pos rfl]
      have hEq := Finset.sum_eq_single un (fun v _ hv => h1 v hv) (fun hmem => absurd (Finset.mem_univ un) hmem)
      rw [h2] at hEq
      exact hEq
    have hfin : ((r.totient : ℕ) : ℂ)⁻¹ * (rf_unitPhase r u un * ((r.totient : ℕ) : ℂ))
        = rf_unitPhase r u un := by
      have h : ((r.totient : ℕ) : ℂ)⁻¹ * ((r.totient : ℕ) : ℂ) = 1 :=
        inv_mul_cancel₀ hphi_neC
      calc ((r.totient : ℕ) : ℂ)⁻¹ * (rf_unitPhase r u un * ((r.totient : ℕ) : ℂ))
          = rf_unitPhase r u un * (((r.totient : ℕ) : ℂ)⁻¹ * ((r.totient : ℕ) : ℂ)) := by ring
        _ = rf_unitPhase r u un * 1 := by rw [h]
        _ = rf_unitPhase r u un := mul_one _
    -- goal after rw [hswap] + simp_rw [hInner] is e = φ⁻¹ * ∑_v ...
    rw [hcollapse, hfin]
    exact hf_un.symm

example : RationalFourierTask := RationalFourierTask_proof

end Erdos821.P4Rat
