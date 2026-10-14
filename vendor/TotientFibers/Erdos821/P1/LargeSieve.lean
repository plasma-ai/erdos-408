import Erdos821.Blueprint.Classical
import OAI.NumberTheory.PrimeGaps.Main

open scoped BigOperators

namespace Erdos821.P1

private theorem sum_Icc_eq_fin {α : Type} [AddCommMonoid α] (N : ℕ) (f : ℕ → α) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ i : Fin N, f (i.val + 1) := by
  classical
  let i (n : ℕ) (hn : n ∈ Finset.Icc 1 N) : Fin N :=
    ⟨n - 1, by
      have hn' := Finset.mem_Icc.mp hn
      omega⟩
  refine Finset.sum_bij i ?_ ?_ ?_ ?_
  · intro n hn
    simp
  · intro n hn m hm hij
    have hval := congrArg Fin.val hij
    have hn' := Finset.mem_Icc.mp hn
    have hm' := Finset.mem_Icc.mp hm
    dsimp [i] at hval
    omega
  · intro b hb
    refine ⟨b.val + 1, Finset.mem_Icc.mpr ⟨by omega, by have := b.isLt; omega⟩, ?_⟩
    apply Fin.ext
    simp [i]
  · intro n hn
    have hn' := Finset.mem_Icc.mp hn
    simp [i, Nat.sub_add_cancel hn'.1]

private noncomputable def sieveK : ℝ := 3 + (Real.log 2)⁻¹

private theorem harmonic_log_bound (R : ℕ) :
    (harmonic (R ^ 2) : ℝ) ≤ sieveK * Real.log (2 * (R : ℝ)) := by
  by_cases hR : R = 0
  · simp [hR, sieveK]
  have hRpos : (0 : ℝ) < R := by exact_mod_cast Nat.pos_of_ne_zero hR
  have hRone : (1 : ℝ) ≤ R := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hR
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : (0 : ℝ) < Real.log (2 * (R : ℝ)) :=
    Real.log_pos (by nlinarith)
  have hlog2_le : Real.log 2 ≤ Real.log (2 * (R : ℝ)) := by
    apply Real.log_le_log (by norm_num) (by nlinarith)
  have hlogR_le : Real.log (R : ℝ) ≤ Real.log (2 * (R : ℝ)) := by
    exact Real.log_le_log hRpos (by nlinarith)
  have hharm := harmonic_le_one_add_log (R ^ 2)
  have hpow : Real.log ((R ^ 2 : ℕ) : ℝ) = 2 * Real.log (R : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hpow] at hharm
  have hone : (1 : ℝ) ≤ (Real.log 2)⁻¹ * Real.log (2 * (R : ℝ)) := by
    calc
      (1 : ℝ) ≤ Real.log (2 * (R : ℝ)) / Real.log 2 :=
        (le_div_iff₀ hlog2).2 (by simpa using hlog2_le)
      _ = (Real.log 2)⁻¹ * Real.log (2 * (R : ℝ)) := by ring
  have hsmall : 1 + 2 * Real.log (R : ℝ) ≤
      ((Real.log 2)⁻¹ + 2) * Real.log (2 * (R : ℝ)) := by
    nlinarith [hlogR_le]
  have hK : (Real.log 2)⁻¹ + 2 ≤ sieveK := by
    dsimp [sieveK]
    nlinarith
  calc
    (harmonic (R ^ 2) : ℝ) ≤ 1 + 2 * Real.log (R : ℝ) := hharm
    _ ≤ ((Real.log 2)⁻¹ + 2) * Real.log (2 * (R : ℝ)) := hsmall
    _ ≤ sieveK * Real.log (2 * (R : ℝ)) :=
      mul_le_mul_of_nonneg_right hK hlogx.le

theorem multiplicative_large_sieve_proof :
    Erdos821.Blueprint.MultiplicativeLargeSieve := by
  classical
  refine ⟨sieveK, ?_, ?_⟩
  · have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hinv : (0 : ℝ) < (Real.log 2)⁻¹ := inv_pos.mpr hlog2
    dsimp [sieveK]
    positivity
  · intro N R a
    let b : Fin (N + 1) → ℂ := fun i => if 0 < i.val then a i.val else 0
    have hchar (q : ℕ) (χ : DirichletCharacter ℂ q) :
        (∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod q)) =
          OAI.LargePrimeGaps.sequenceCharacterSum b χ := by
      have hseq : OAI.LargePrimeGaps.sequenceCharacterSum b χ =
          ∑ i : Fin N, a (i.val + 1) * χ ((i.val + 1 : ℕ) : ZMod q) := by
        unfold OAI.LargePrimeGaps.sequenceCharacterSum
        rw [Fin.sum_univ_succ]
        simp [b, Fin.val_succ]
      rw [sum_Icc_eq_fin N (fun n => a n * χ (n : ZMod q)), hseq.symm]
    have hnorm : (∑ i : Fin (N + 1), ‖b i‖ ^ 2) =
        Erdos821.Blueprint.Analytic.sqNorm (Finset.Icc 1 N) a := by
      calc
        _ = ‖b 0‖ ^ 2 + ∑ i : Fin N, ‖b i.succ‖ ^ 2 := Fin.sum_univ_succ _
        _ = ∑ i : Fin N, ‖a (i.val + 1)‖ ^ 2 := by simp [b, Fin.val_succ]
        _ = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
          (sum_Icc_eq_fin N (fun n => ‖a n‖ ^ 2)).symm
        _ = Erdos821.Blueprint.Analytic.sqNorm (Finset.Icc 1 N) a := rfl
    have hleft :
        (∑ r : Fin R, ((r.val + 1 : ℕ) : ℝ) / Nat.totient (r.val + 1) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (r.val + 1))).filter
            DirichletCharacter.IsPrimitive,
            ‖∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod (r.val + 1))‖ ^ 2) =
        ∑ r : Fin R, ((r.val + 1 : ℕ) : ℝ) / Nat.totient (r.val + 1) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (r.val + 1))).filter
            DirichletCharacter.IsPrimitive,
            ‖OAI.LargePrimeGaps.sequenceCharacterSum b χ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      apply congrArg (fun t : ℝ =>
        ((r.val + 1 : ℕ) : ℝ) / Nat.totient (r.val + 1) * t)
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [hchar]
    have hOAI := OAI.LargePrimeGaps.multiplicative_large_sieve R (N + 1) b
    have hS : 0 ≤ ∑ i : Fin (N + 1), ‖b i‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg ‖b i‖
    have hR2 : (0 : ℝ) ≤ (R : ℝ) ^ 2 := sq_nonneg _
    have hH := harmonic_log_bound R
    have hRterm : (R : ℝ) ^ 2 * (harmonic (R ^ 2) : ℝ) ≤
        sieveK * ((R : ℝ) ^ 2 * Real.log (2 * (R : ℝ))) := by
      calc
        _ ≤ (R : ℝ) ^ 2 * (sieveK * Real.log (2 * (R : ℝ))) :=
          mul_le_mul_of_nonneg_left hH hR2
        _ = _ := by ring
    have hcoef : ((N + 1 : ℕ) : ℝ) + (R : ℝ) ^ 2 * (harmonic (R ^ 2) : ℝ) ≤
        sieveK * ((N : ℝ) + 1 + (R : ℝ) ^ 2 * Real.log (2 * (R : ℝ))) := by
      have hk1 : (1 : ℝ) ≤ sieveK := by
        have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        have hinv : (0 : ℝ) < (Real.log 2)⁻¹ := inv_pos.mpr hlog2
        dsimp [sieveK]
        nlinarith
      have hbase : (N : ℝ) + 1 ≤ sieveK * ((N : ℝ) + 1) := by
        nlinarith
      have hterm := add_le_add hbase hRterm
      calc
        ((N + 1 : ℕ) : ℝ) + (R : ℝ) ^ 2 * (harmonic (R ^ 2) : ℝ) ≤
            sieveK * ((N : ℝ) + 1) + sieveK * ((R : ℝ) ^ 2 * Real.log (2 * (R : ℝ))) := by
          simpa only [Nat.cast_add, Nat.cast_one] using hterm
        _ = sieveK * ((N : ℝ) + 1 + (R : ℝ) ^ 2 * Real.log (2 * (R : ℝ))) := by ring
    have hmain := hOAI.trans (mul_le_mul_of_nonneg_right hcoef hS)
    rw [hleft]
    calc
      _ ≤ (sieveK * ((N : ℝ) + 1 + (R : ℝ) ^ 2 * Real.log (2 * (R : ℝ)))) *
          (∑ i : Fin (N + 1), ‖b i‖ ^ 2) := hmain
      _ = sieveK * ((N : ℝ) + 1 + (R : ℝ) ^ 2 * Real.log (2 * (R : ℝ))) *
          Erdos821.Blueprint.Analytic.sqNorm (Finset.Icc 1 N) a := by rw [hnorm]

example : Erdos821.Blueprint.MultiplicativeLargeSieve := multiplicative_large_sieve_proof


end Erdos821.P1
