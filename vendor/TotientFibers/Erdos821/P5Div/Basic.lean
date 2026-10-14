import Erdos821.Blueprint.Analytic

set_option autoImplicit false

open scoped BigOperators

namespace Erdos821.P5Div

open Erdos821.Blueprint.Analytic

noncomputable section

attribute [local instance] Classical.propDecidable

/-- §4 pointwise rough-divisor count for the physical endpoint sup bound.
A rough divisor chooses exponents only at prime factors of N exceeding y.
Its count is the product of (e_p+1) over those primes, at most 2^(sum e_p).
Their prime-power product is at most N, while each prime is greater than y,
so sum e_p ≤ log(N)/log(y). All logs and divisions are real.
This is an elementary finite-factorization task and needs no P1 interface. -/
def RoughDivisorCountTask : Prop :=
  ∀ (y : ℝ) (N : ℕ), 1 < y → 0 < N →
    (((N.divisors.filter (rough y)).card : ℕ) : ℝ) ≤
      Real.exp (Real.log 2 * Real.log (N : ℝ) / Real.log y)

/-- Every `e + 1 ≤ 2 ^ e`. -/
lemma succ_le_two_pow (e : ℕ) : e + 1 ≤ 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hpos : (0 : ℕ) < 2 ^ e := pow_pos (by norm_num) e
    have h1 : (1 : ℕ) ≤ 2 ^ e := by omega
    calc e + 1 + 1 ≤ 2 ^ e + 1 := Nat.add_le_add_right ih 1
      _ ≤ 2 ^ e + 2 ^ e := Nat.add_le_add_left h1 _
      _ = 2 ^ (e + 1) := by ring

theorem RoughDivisorCountTask_proof : RoughDivisorCountTask := by
  intro y N hy1 hNpos
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos hy1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hNposR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
  -- The large prime factors of N and the total exponent.
  set P : Finset ℕ := N.primeFactors.filter (fun p => y < (p : ℝ)) with hPdef
  set E : ℕ := ∑ p ∈ P, N.factorization p with hEdef
  set s : Finset ℕ := N.divisors.filter (rough y) with hsdef
  -- Divisibility facts for members of s.
  have hmem_dvd : ∀ d ∈ s, d ∣ N := by
    intro d hd
    have hdiv : d ∈ N.divisors := Finset.mem_of_mem_filter d hd
    exact (Nat.mem_divisors.mp hdiv).1
  have hmem_pos : ∀ d ∈ s, 0 < d := by
    intro d hd
    exact Nat.pos_of_dvd_of_pos (hmem_dvd d hd) hNpos
  have hmem_ne : ∀ d ∈ s, d ≠ 0 := by
    intro d hd h
    exact absurd h (ne_of_gt (hmem_pos d hd))
  have hfact_le : ∀ d ∈ s, ∀ p : ℕ, d.factorization p ≤ N.factorization p := by
    intro d hd p
    have hd0 : d ≠ 0 := hmem_ne d hd
    have hle : d.factorization ≤ N.factorization :=
      (Nat.factorization_le_iff_dvd hd0 hNne).mpr (hmem_dvd d hd)
    exact Finsupp.le_def.mp hle p
  -- Members of s are supported on P.
  have hzero_of_not_mem : ∀ d ∈ s, ∀ p : ℕ, p ∉ P → d.factorization p = 0 := by
    intro d hd p hpNot
    by_contra hNe
    have hmemSup : p ∈ d.factorization.support :=
      Finsupp.mem_support_iff.mpr hNe
    rw [Nat.support_factorization] at hmemSup
    obtain ⟨hprime, hdvdD, _⟩ := Nat.mem_primeFactors.mp hmemSup
    obtain ⟨_, hAll⟩ := (Finset.mem_filter.mp hd).2
    have hlt : y < (p : ℝ) := hAll p hprime hdvdD
    have hdvdN : p ∣ N := dvd_trans hdvdD (hmem_dvd d hd)
    have hNmem : p ∈ N.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hprime, hdvdN, hNne⟩
    have hPmem : p ∈ P := Finset.mem_filter.mpr ⟨hNmem, hlt⟩
    exact hpNot hPmem
  -- Exponent map into the box; `%` makes it total.
  let phi : ℕ → (∀ _p : ↥P, Fin (N.factorization _p.val + 1)) :=
    fun d p => ⟨d.factorization p.val % (N.factorization p.val + 1),
      Nat.mod_lt _ (Nat.succ_pos _)⟩
  have hphi_eq : ∀ d ∈ s, ∀ p : ↥P,
      ((phi d p).val = d.factorization p.val) := by
    intro d hd p
    show d.factorization p.val % (N.factorization p.val + 1) = _
    apply Nat.mod_eq_of_lt
    exact Nat.lt_succ_of_le (hfact_le d hd p.val)
  have hMaps : Set.MapsTo phi (↑s : Set ℕ)
      (↑(Fintype.piFinset (fun _p : ↥P =>
        (Finset.univ : Finset (Fin (N.factorization _p.val + 1)))))) := by
    intro d hd
    simp only [Finset.mem_coe] at hd ⊢
    rw [Fintype.mem_piFinset]
    intro _
    exact Finset.mem_univ _
  have hInj : Set.InjOn phi (↑s : Set ℕ) := by
    intro d1 hd1 d2 hd2 heq
    simp only [Finset.mem_coe] at hd1 hd2
    have hd1ne := hmem_ne d1 hd1
    have hd2ne := hmem_ne d2 hd2
    apply Nat.eq_of_factorization_eq hd1ne hd2ne
    intro p
    by_cases hp : p ∈ P
    · have hcongr := congrArg (fun f => (f (⟨p, hp⟩ : ↥P)).val) heq
      simp only at hcongr
      rw [hphi_eq d1 hd1 ⟨p, hp⟩, hphi_eq d2 hd2 ⟨p, hp⟩] at hcongr
      exact hcongr
    · rw [hzero_of_not_mem d1 hd1 p hp, hzero_of_not_mem d2 hd2 p hp]
  have hCardPi : (Fintype.piFinset (fun _p : ↥P =>
      (Finset.univ : Finset (Fin (N.factorization _p.val + 1))))).card
      = ∏ p ∈ P, (N.factorization p + 1) := by
    rw [Fintype.card_piFinset]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact Finset.prod_coe_sort P (fun p => N.factorization p + 1)
  have hCardLePi : s.card ≤ ∏ p ∈ P, (N.factorization p + 1) := by
    calc s.card
        ≤ (Fintype.piFinset (fun _p : ↥P =>
            (Finset.univ : Finset (Fin (N.factorization _p.val + 1))))).card :=
          Finset.card_le_card_of_injOn phi hMaps hInj
      _ = ∏ p ∈ P, (N.factorization p + 1) := hCardPi
  have hProdLe : ∏ p ∈ P, (N.factorization p + 1) ≤ 2 ^ E := by
    have hEach : ∀ p ∈ P, N.factorization p + 1 ≤ 2 ^ N.factorization p :=
      fun p _ => succ_le_two_pow _
    have hStep : ∏ p ∈ P, (N.factorization p + 1)
        ≤ ∏ p ∈ P, 2 ^ N.factorization p :=
      Finset.prod_le_prod (fun p hp => hEach p hp)
    have hPowEq : ∏ p ∈ P, (2 : ℕ) ^ N.factorization p
        = 2 ^ (∑ p ∈ P, N.factorization p) :=
      Finset.prod_pow_eq_pow_sum P (fun p => N.factorization p) 2
    rw [hPowEq] at hStep
    simpa [hEdef] using hStep
  have hCardNat : s.card ≤ 2 ^ E := hCardLePi.trans hProdLe
  -- The subproduct over P divides N.
  have hSub : P ⊆ N.primeFactors := by
    rw [hPdef]
    exact Finset.filter_subset _ _
  have hDvdSub : (∏ p ∈ P, p ^ N.factorization p) ∣ N := by
    calc (∏ p ∈ P, p ^ N.factorization p)
        ∣ ∏ p ∈ N.primeFactors, p ^ N.factorization p :=
          Finset.prod_dvd_prod_of_subset P N.primeFactors _ hSub
      _ = N := (Nat.prod_primeFactors_pow_factorization hNne).symm
  have hPowLeNat : ∏ p ∈ P, p ^ N.factorization p ≤ N :=
    Nat.le_of_dvd hNpos hDvdSub
  -- Real version: `y ^ E ≤ N`.
  have hPowLeR : (y : ℝ) ^ E ≤ (N : ℝ) := by
    have hEachR : ∀ p ∈ P,
        y ^ N.factorization p ≤ ((p : ℕ) : ℝ) ^ N.factorization p := by
      intro p hp
      have hp2 : p ∈ N.primeFactors.filter (fun q => y < ((q : ℕ) : ℝ)) := hPdef ▸ hp
      have hlt : y < ((p : ℕ) : ℝ) := (Finset.mem_filter.mp hp2).2
      exact pow_le_pow_left₀ hy0.le (le_of_lt hlt) _
    have hProdR : ∏ p ∈ P, y ^ N.factorization p
        ≤ ∏ p ∈ P, ((p : ℕ) : ℝ) ^ N.factorization p :=
      Finset.prod_le_prod₀
        (fun p _ => pow_nonneg hy0.le _)
        (fun p hp => hEachR p hp)
    have hEqL : ∏ p ∈ P, y ^ N.factorization p = y ^ E := by
      rw [hEdef]
      exact Finset.prod_pow_eq_pow_sum P (fun p => N.factorization p) y
    have hEqR : ((∏ p ∈ P, p ^ N.factorization p : ℕ) : ℝ)
        = ∏ p ∈ P, ((p : ℕ) : ℝ) ^ N.factorization p := by
      push_cast
      rfl
    calc y ^ E = ∏ p ∈ P, y ^ N.factorization p := hEqL.symm
      _ ≤ ∏ p ∈ P, ((p : ℕ) : ℝ) ^ N.factorization p := hProdR
      _ = ((∏ p ∈ P, p ^ N.factorization p : ℕ) : ℝ) := hEqR.symm
      _ ≤ (N : ℝ) := Nat.cast_le.mpr hPowLeNat
  -- Take logs.
  have hPowPos : (0 : ℝ) < y ^ E := pow_pos hy0 E
  have hLogLe : (E : ℝ) * Real.log y ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_log hPowPos hPowLeR
    rwa [Real.log_pow] at h
  have hExpLe : (E : ℝ) * Real.log 2
      ≤ Real.log 2 * Real.log (N : ℝ) / Real.log y := by
    rw [le_div_iff₀ hlogy]
    calc ((E : ℝ) * Real.log 2) * Real.log y
        = Real.log 2 * ((E : ℝ) * Real.log y) := by ring
      _ ≤ Real.log 2 * Real.log (N : ℝ) :=
          mul_le_mul_of_nonneg_left hLogLe (le_of_lt hlog2)
  -- Cast the counting bound and rewrite the power as `exp`.
  have hCardR : ((s.card : ℕ) : ℝ) ≤ ((2 ^ E : ℕ) : ℝ) := by
    exact_mod_cast hCardNat
  have hCast2 : ((2 ^ E : ℕ) : ℝ) = (2 : ℝ) ^ E := by norm_cast
  have hExpEq : (2 : ℝ) ^ E = Real.exp ((E : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hExpMono : Real.exp ((E : ℝ) * Real.log 2)
      ≤ Real.exp (Real.log 2 * Real.log (N : ℝ) / Real.log y) :=
    Real.exp_monotone hExpLe
  calc ((s.card : ℕ) : ℝ) ≤ ((2 ^ E : ℕ) : ℝ) := hCardR
    _ = (2 : ℝ) ^ E := hCast2
    _ = Real.exp ((E : ℝ) * Real.log 2) := hExpEq
    _ ≤ Real.exp (Real.log 2 * Real.log (N : ℝ) / Real.log y) := hExpMono

example : RoughDivisorCountTask := RoughDivisorCountTask_proof


end

end Erdos821.P5Div
