import Mathlib


namespace Erdos821
namespace Prelim
namespace Notation

open Finset Nat

/-- Largest prime factor, with `Pplus 1 = 1` (paper §1). For `0` we also
return `1`; the paper only uses positive integers. -/
noncomputable def Pplus (n : ℕ) : ℕ :=
  n.primeFactors.max.unbotD 1

/-- Least prime factor, with `Pminus 1 = ∞` (paper §1), represented as
`⊤ : WithTop ℕ`. For `0` we also return `⊤`. -/
noncomputable def Pminus (n : ℕ) : WithTop ℕ :=
  n.primeFactors.min

theorem Pplus_one : Pplus 1 = 1 := by
  simp [Pplus]

theorem Pminus_one : Pminus 1 = ⊤ := by
  simp [Pminus]

/-- The `max` behind `Pplus` is a genuine prime factor when `1 < n`. -/
theorem Pplus_max_eq {n : ℕ} (h1 : 1 < n) :
    ∃ b : ℕ, b ∈ n.primeFactors ∧ n.primeFactors.max = (↑b : WithBot ℕ) ∧
      Pplus n = b := by
  have h : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr h1
  obtain ⟨b, hb⟩ := Finset.max_of_nonempty h
  have hmem : b ∈ n.primeFactors := Finset.mem_of_max hb
  refine ⟨b, hmem, hb, ?_⟩
  simp [Pplus, hb]

theorem Pplus_mem {n : ℕ} (h1 : 1 < n) : Pplus n ∈ n.primeFactors := by
  obtain ⟨b, hmem, _, rfl⟩ := Pplus_max_eq h1
  exact hmem

theorem Pplus_prime {n : ℕ} (h1 : 1 < n) : Nat.Prime (Pplus n) :=
  Nat.prime_of_mem_primeFactors (Pplus_mem h1)

theorem Pplus_dvd {n : ℕ} (h1 : 1 < n) : Pplus n ∣ n :=
  Nat.dvd_of_mem_primeFactors (Pplus_mem h1)

theorem Pplus_max_coe {n : ℕ} (h1 : 1 < n) :
    (↑(Pplus n) : WithBot ℕ) = n.primeFactors.max := by
  obtain ⟨b, _, hb, hPb⟩ := Pplus_max_eq h1
  rw [hPb]
  exact hb.symm

theorem Pplus_ge_of_mem {n p : ℕ} (h1 : 1 < n) (hp : p ∈ n.primeFactors) :
    p ≤ Pplus n := by
  have hle : (↑p : WithBot ℕ) ≤ n.primeFactors.max := Finset.le_max hp
  rw [← Pplus_max_coe h1] at hle
  exact WithBot.coe_le_coe.mp hle

theorem Pplus_le_self {n : ℕ} (h1 : 1 < n) : Pplus n ≤ n :=
  Nat.le_of_mem_primeFactors (Pplus_mem h1)

theorem Pplus_prime_self {p : ℕ} (hp : p.Prime) : Pplus p = p := by
  have hset : p.primeFactors = {p} := hp.primeFactors
  simp [Pplus, hset]

theorem Pminus_prime_self {p : ℕ} (hp : p.Prime) :
    Pminus p = ((p : ℕ) : WithTop ℕ) := by
  have hset : p.primeFactors = {p} := hp.primeFactors
  simp [Pminus, hset]

theorem Pminus_min_eq {n : ℕ} (h1 : 1 < n) :
    ∃ m : ℕ, m ∈ n.primeFactors ∧ Pminus n = ((m : ℕ) : WithTop ℕ) := by
  have h : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr h1
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty h
  exact ⟨m, Finset.mem_of_min hm, hm⟩

theorem Pminus_le_of_mem {n p : ℕ} (_h1 : 1 < n) (hp : p ∈ n.primeFactors) :
    Pminus n ≤ ((p : ℕ) : WithTop ℕ) := by
  simp only [Pminus]
  exact Finset.min_le hp

theorem Pminus_lt_top {n : ℕ} (h1 : 1 < n) : Pminus n < ⊤ := by
  obtain ⟨m, _, hm⟩ := Pminus_min_eq h1
  rw [hm]
  exact WithTop.coe_lt_top _

/-- `y`-smooth (paper §1): every prime divisor is at most `y`. `1` is
vacuously smooth; this matches `Pplus(n) ≤ y` for `n > 1`. -/
def IsSmooth (y : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ y

/-- Rough above `y` (paper §1): every prime divisor exceeds `y`. `1` is
vacuously rough; this matches `Pminus(n) > y` for `n > 1` with
`Pminus(1) = ∞`. -/
def IsRoughAbove (y : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → y < (p : ℝ)

theorem isSmooth_one (y : ℝ) : IsSmooth y 1 := by
  intro p hp hdvd
  have hle : p ≤ 1 := Nat.le_of_dvd one_pos hdvd
  have heq : p = 1 := Nat.le_antisymm hle (Nat.Prime.one_le hp)
  rw [heq] at hp
  exact absurd hp Nat.not_prime_one

theorem isRoughAbove_one (y : ℝ) : IsRoughAbove y 1 := by
  intro p hp hdvd
  have hle : p ≤ 1 := Nat.le_of_dvd one_pos hdvd
  have heq : p = 1 := Nat.le_antisymm hle (Nat.Prime.one_le hp)
  rw [heq] at hp
  exact absurd hp Nat.not_prime_one

theorem isSmooth_iff_forall_mem {y : ℝ} {n : ℕ} (hn : n ≠ 0) :
    IsSmooth y n ↔ ∀ p ∈ n.primeFactors, (p : ℝ) ≤ y := by
  constructor
  · intro h p hp
    exact h p (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  · intro h p hp hdvd
    exact h p (hp.mem_primeFactors hdvd hn)

theorem isRoughAbove_iff_forall_mem {y : ℝ} {n : ℕ} (hn : n ≠ 0) :
    IsRoughAbove y n ↔ ∀ p ∈ n.primeFactors, y < (p : ℝ) := by
  constructor
  · intro h p hp
    exact h p (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  · intro h p hp hdvd
    exact h p (hp.mem_primeFactors hdvd hn)

theorem isSmooth_iff_Pplus_le {y : ℝ} {n : ℕ} (h1 : 1 < n) :
    IsSmooth y n ↔ ((Pplus n : ℕ) : ℝ) ≤ y := by
  constructor
  · intro h
    exact h _ (Pplus_prime h1) (Pplus_dvd h1)
  · intro h p hp hdvd
    have hn : n ≠ 0 := by omega
    have hm : p ∈ n.primeFactors := hp.mem_primeFactors hdvd hn
    calc (p : ℝ) ≤ ((Pplus n : ℕ) : ℝ) :=
            by exact_mod_cast Pplus_ge_of_mem h1 hm
      _ ≤ y := h

theorem isRoughAbove_of_forall_mem {y : ℝ} {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, y < (p : ℝ)) : IsRoughAbove y n :=
  (isRoughAbove_iff_forall_mem hn).mpr h

theorem forall_mem_of_isRoughAbove {y : ℝ} {n : ℕ} (hn : n ≠ 0)
    (h : IsRoughAbove y n) : ∀ p ∈ n.primeFactors, y < (p : ℝ) :=
  (isRoughAbove_iff_forall_mem hn).mp h

/-- Logarithmic scales (paper (eq:scales)): `L = log x`. -/
noncomputable def L (x : ℝ) : ℝ := Real.log x

/-- `T = log L` (paper (eq:scales)). -/
noncomputable def T (x : ℝ) : ℝ := Real.log (Real.log x)

/-- `W = exp √L` (paper (eq:scales)), the roughness cutoff. -/
noncomputable def W (x : ℝ) : ℝ := Real.exp (Real.sqrt (Real.log x))

theorem L_pos_of_one_lt {x : ℝ} (hx : 1 < x) : 0 < L x :=
  Real.log_pos hx

theorem L_gt_one_of_exp_one_lt {x : ℝ} (hx : Real.exp 1 < x) : 1 < L x := by
  have := Real.log_lt_log (Real.exp_pos 1) hx
  rwa [Real.log_exp] at this

theorem T_pos_of_exp_one_lt {x : ℝ} (hx : Real.exp 1 < x) : 0 < T x := by
  unfold T
  exact Real.log_pos (L_gt_one_of_exp_one_lt hx)

theorem W_pos (x : ℝ) : 0 < W x := Real.exp_pos _

theorem one_le_W_of_nonneg_log {x : ℝ} (hx : 0 ≤ Real.log x) : 1 ≤ W x := by
  unfold W
  have h : (0 : ℝ) ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have := Real.exp_le_exp.mpr h
  rwa [Real.exp_zero] at this

/-- Dyad of naturals `[Y, 2Y)` (paper §1). -/
def dyadNat (Y : ℕ) : Finset ℕ := Finset.Ico Y (2 * Y)

theorem mem_dyadNat {Y n : ℕ} : n ∈ dyadNat Y ↔ Y ≤ n ∧ n < 2 * Y := by
  simp [dyadNat]

/-- Dyad of reals `[Y, 2Y)` (paper §1). -/
def dyadReal (Y : ℝ) : Set ℝ := Set.Ico Y (2 * Y)

theorem mem_dyadReal {Y n : ℝ} : n ∈ dyadReal Y ↔ Y ≤ n ∧ n < 2 * Y := by
  rfl

/-- `n ≍ Y` (paper §1): bounded above and below by fixed positive multiples. -/
def IsAsymp (n Y : ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ c₁ * Y ≤ n ∧ n ≤ c₂ * Y

theorem isAsymp_refl_of_nonneg {n : ℝ} (_hn : 0 ≤ n) : IsAsymp n n :=
  ⟨1, 1, one_pos, one_pos, by rw [one_mul], by rw [one_mul]⟩

theorem isAsymp_symm_of_pos {n Y : ℝ} (hn : 0 < n)
    (h : IsAsymp n Y) : IsAsymp Y n := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hlo, hhi⟩ := h
  refine ⟨1 / c₂, 1 / c₁, by positivity, by positivity, ?_, ?_⟩
  · have h1 : n / c₂ ≤ Y := by
      rw [div_le_iff₀ hc₂]
      calc n ≤ c₂ * Y := hhi
        _ = Y * c₂ := by ring
    calc 1 / c₂ * n = n / c₂ := by ring
      _ ≤ Y := h1
  · have h2 : Y ≤ n / c₁ := by
      rw [le_div_iff₀ hc₁]
      calc Y * c₁ = c₁ * Y := by ring
        _ ≤ n := hlo
    calc Y ≤ n / c₁ := h2
      _ = 1 / c₁ * n := by ring

theorem isAsymp_trans {n Y Z : ℝ}
    (h1 : IsAsymp n Y) (h2 : IsAsymp Y Z) : IsAsymp n Z := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hlo1, hhi1⟩ := h1
  obtain ⟨d₁, d₂, hd₁, hd₂, hlo2, hhi2⟩ := h2
  refine ⟨c₁ * d₁, c₂ * d₂, mul_pos hc₁ hd₁, mul_pos hc₂ hd₂, ?_, ?_⟩
  · calc c₁ * d₁ * Z = c₁ * (d₁ * Z) := by ring
      _ ≤ c₁ * Y := by
          apply mul_le_mul_of_nonneg_left hlo2 hc₁.le
      _ ≤ n := hlo1
  · calc n ≤ c₂ * Y := hhi1
      _ ≤ c₂ * (d₂ * Z) := by
          apply mul_le_mul_of_nonneg_left hhi2 hc₂.le
      _ = c₂ * d₂ * Z := by ring

/-- `e(t) = exp(2π i t)` (paper §1). -/
noncomputable def addChar (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))

theorem addChar_zero : addChar 0 = 1 := by
  simp [addChar]

theorem addChar_add (s t : ℝ) : addChar (s + t) = addChar s * addChar t := by
  simp only [addChar, Complex.ofReal_add, mul_add]
  rw [Complex.exp_add]

theorem addChar_ne_zero (t : ℝ) : addChar t ≠ 0 :=
  Complex.exp_ne_zero _

/-- Falling factorial `(z)_j = z(z-1)⋯(z-j+1)` with `(z)_0 = 1` (paper §1). -/
noncomputable def fallingFactorialℂ (z : ℂ) : ℕ → ℂ
  | 0 => 1
  | j + 1 => fallingFactorialℂ z j * (z - (j : ℂ))

theorem fallingFactorialℂ_zero (z : ℂ) : fallingFactorialℂ z 0 = 1 := rfl

theorem fallingFactorialℂ_succ (z : ℂ) (j : ℕ) :
    fallingFactorialℂ z (j + 1) = fallingFactorialℂ z j * (z - (j : ℂ)) := rfl

/-- `ω(n)`: number of distinct prime factors (paper §1; group counts in §2
are built from `Nat.primeFactors`). Multiplicities do not increase it. -/
noncomputable def omega (n : ℕ) : ℕ := n.primeFactors.card

theorem omega_one : omega 1 = 0 := by
  simp [omega]

theorem omega_prime {p : ℕ} (hp : p.Prime) : omega p = 1 := by
  simp [omega, hp.primeFactors]

theorem omega_eq_zero_iff {n : ℕ} : omega n = 0 ↔ n = 0 ∨ n = 1 := by
  simp [omega, Nat.primeFactors_eq_empty]

/-- `τ(n)`: divisor function (paper §1). -/
noncomputable def tau (n : ℕ) : ℕ := n.divisors.card

theorem tau_one : tau 1 = 1 := by
  simp [tau]

theorem tau_zero : tau 0 = 0 := by
  simp [tau, Nat.divisors_zero]

/-- `φ` is Mathlib's `Nat.totient` (paper §1); record the alias. -/
theorem phi_def (n : ℕ) : Nat.totient n = Nat.totient n := rfl

/-- `μ` vanishes on non-squarefree `n` (paper §1); Mathlib's
`ArithmeticFunction.moebius`. -/
theorem mu_eq_zero_of_not_squarefree {n : ℕ} (h : ¬Squarefree n) :
    ArithmeticFunction.moebius n = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree h

end Notation
end Prelim
end Erdos821
