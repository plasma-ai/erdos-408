import Erdos821.P3Edge.AuxSum
import Erdos821.P3Edge.Analytic

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {x : ℝ}

/-- Logarithmic scale exceeds one from `x ≥ 3`. -/
lemma one_lt_L (hx : 3 ≤ x) : 1 < L x := by
  unfold L
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h1 : (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
  calc (1 : ℝ) = Real.log (Real.exp 1) := h1
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
    _ ≤ Real.log x := Real.log_le_log (by norm_num) hx

lemma V_pos_of_adm {x : ℝ} (hP : P.Admissible F x) (g : P.Group) : 0 < P.V g :=
  lt_of_lt_of_le F.vMin_pos ((hP.2.2.2.2.1 g).1)

lemma V_le_of_adm {x : ℝ} (hP : P.Admissible F x) (g : P.Group) : P.V g ≤ F.vMax :=
  ((hP.2.2.2.2.1 g).2)

/-- Big primes are large: from admissibility. -/
lemma big_prime_ge {x : ℝ} (hP : P.Admissible F x)
    (g : P.BigGroup) (p : P.Prime g.val) : Real.exp ((L x) ^ F.c) ≤ (p.val : ℝ) := by
  have h := hP.2.2.2.2.2 g.val p.val p.property
  -- hP.2.2.2 : ∀ g p, p ∈ primes g → if big g then ... ; g.val has big = true
  have hb : P.big g.val = true := g.property
  rw [hb] at h
  simpa using h.1

/-- `N x + 1` grows at most linearly in `L x` once `1 ≤ L x`. -/
lemma Nx_add_one_le (hx : 1 ≤ L x) : ((N x + 1 : ℕ) : ℝ) ≤ 5 * L x := by
  have hL0 : 0 ≤ L x := le_trans zero_le_one hx
  have hrpow52 : (L x) ^ ((52 : ℝ) / 100) ≤ L x := by
    have h1 : ((52 : ℝ) / 100) ≤ 1 := by norm_num
    calc (L x) ^ ((52 : ℝ) / 100) ≤ (L x) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx h1
      _ = L x := Real.rpow_one _
  have hR : ((R x : ℕ) : ℝ) ≤ (L x) ^ ((52 : ℝ) / 100) + 1 := by
    have h := Nat.ceil_lt_add_one (a := (L x) ^ ((52 : ℝ) / 100))
      (Real.rpow_nonneg hL0 ((52 : ℝ) / 100))
    -- h : ↑⌈(Lx)^0.52⌉₊ < (Lx)^0.52 + 1 ; R x is exactly that ceil
    simpa [R] using le_of_lt h
  have hN : ((N x : ℕ) : ℝ) ≤ 4 * L x := by
    have : ((N x : ℕ) : ℝ) = 2 * ((R x : ℕ) : ℝ) := by simp [N]
    rw [this]
    calc 2 * ((R x : ℕ) : ℝ) ≤ 2 * ((L x) ^ ((52 : ℝ) / 100) + 1) := by
            apply mul_le_mul_of_nonneg_left hR (by norm_num)
      _ ≤ 2 * (L x + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            linarith [hrpow52]
      _ ≤ 4 * L x := by linarith [hx]
  push_cast
  linarith [hN, hx]

/-- Exponential of a positive power dominates: single Taylor term. -/
lemma exp_ge_pow_div (y : ℝ) (hy : 0 ≤ y) (k : ℕ) :
    y ^ k / (k.factorial : ℝ) ≤ Real.exp y := by
  have hnn : ∀ i ∈ Finset.range (k + 1), (0:ℝ) ≤ y ^ i / (i.factorial : ℝ) := by
    intro i _
    apply div_nonneg (pow_nonneg hy _)
    positivity
  calc y ^ k / (k.factorial : ℝ)
      ≤ ∑ i ∈ Finset.range (k + 1), y ^ i / (i.factorial : ℝ) :=
        Finset.single_le_sum hnn (Finset.mem_range.mpr (Nat.lt_succ_self k))
    _ ≤ Real.exp y := Real.sum_le_exp_of_nonneg hy (k + 1)

/-- Fixed-data constant: how many Taylor terms dominate `L x`. -/
def taylorTerms (F : FixedData) : ℕ := ⌈2 / F.c⌉₊ + 1

lemma taylorTerms_pos_c (F : FixedData) : 0 < F.c :=
  lt_trans (lt_trans F.a_pos F.ab) F.bc

lemma taylorTerms_mul (F : FixedData) :
    2 ≤ F.c * (taylorTerms F : ℝ) := by
  have hc : 0 < F.c := taylorTerms_pos_c F
  unfold taylorTerms
  have h1 : (2 / F.c : ℝ) ≤ ((⌈2 / F.c⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ((⌈2 / F.c⌉₊ : ℕ) : ℝ) ≤ ((⌈2 / F.c⌉₊ + 1 : ℕ) : ℝ) := by
    apply Nat.cast_le.mpr
    omega
  have h3 : F.c * (2 / F.c) = 2 := by field_simp
  calc (2:ℝ) = F.c * (2 / F.c) := h3.symm
    _ ≤ F.c * ((⌈2 / F.c⌉₊ + 1 : ℕ) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hc)
        calc (2 / F.c : ℝ) ≤ ((⌈2 / F.c⌉₊ : ℕ) : ℝ) := h1
          _ ≤ ((⌈2 / F.c⌉₊ + 1 : ℕ) : ℝ) := h2

/-- For large `L x`, primes exceed twice the auxiliary sum. -/
lemma exp_pow_ge_ten_mul (hx : 1 ≤ L x)
    (hL : 10 * ((taylorTerms F).factorial : ℝ) ≤ L x) :
    10 * L x ≤ Real.exp ((L x) ^ F.c) := by
  have hc : 0 < F.c := taylorTerms_pos_c F
  set k := taylorTerms F with hk
  have hy0 : (0:ℝ) ≤ (L x) ^ F.c := Real.rpow_nonneg (le_trans zero_le_one hx) _
  have hterm := exp_ge_pow_div ((L x) ^ F.c) hy0 k
  -- ((Lx)^c)^k = (Lx)^(c*k), and c*k ≥ 2 so (Lx)^(c*k) ≥ (Lx)^2
  have hpow : ((L x) ^ F.c) ^ k = (L x) ^ (F.c * (k : ℝ)) := by
    rw [← Real.rpow_natCast _ k, ← Real.rpow_mul (le_trans zero_le_one hx)]
  have hck : (2:ℝ) ≤ F.c * k := taylorTerms_mul F
  have hL2 : (L x) ^ (2:ℝ) ≤ (L x) ^ (F.c * k) :=
    Real.rpow_le_rpow_of_exponent_le hx hck
  have hL2eq : (L x) ^ (2:ℝ) = (L x) * L x := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, pow_two]
  have hkpos : (0:ℝ) < (k.factorial : ℝ) := by positivity
  have hLx_pos : 0 < L x := lt_of_lt_of_le zero_lt_one hx
  have hterm2 : (L x) ^ (F.c * k) / (k.factorial : ℝ) ≤ Real.exp ((L x) ^ F.c) := by
    have h2 : ((L x) ^ F.c) ^ k / (k.factorial : ℝ) ≤ Real.exp ((L x) ^ F.c) := by
      have h3 := exp_ge_pow_div ((L x) ^ F.c)
        (Real.rpow_nonneg (le_of_lt hLx_pos) _) k
      linarith [h3]
    rwa [hpow] at h2
  have hstep : (L x) ^ (2:ℝ) / (k.factorial : ℝ) ≤ Real.exp ((L x) ^ F.c) := by
    have hdiv : (L x) ^ (2:ℝ) / (k.factorial : ℝ)
        ≤ (L x) ^ (F.c * k) / (k.factorial : ℝ) := by
      gcongr
    exact le_trans hdiv hterm2
  have hfin : 10 * L x ≤ (L x) * L x / (k.factorial : ℝ) := by
    rw [le_div_iff₀ hkpos]
    have hmul := mul_le_mul_of_nonneg_right hL (le_of_lt hLx_pos)
    nlinarith [hmul]
  calc 10 * L x ≤ (L x) * L x / (k.factorial : ℝ) := hfin
    _ = (L x) ^ (2:ℝ) / (k.factorial : ℝ) := by rw [hL2eq]
    _ ≤ Real.exp ((L x) ^ F.c) := hstep

/-- Auxiliary sum is at most `n+1`. -/
lemma eta_sum_le (n : ℕ) : ∑ i : Fin (n + 1), eta F n i ≤ ((n + 1 : ℕ) : ℝ) := by
  have h := Finset.sum_le_card_nsmul Finset.univ (fun i => eta F n i) (1:ℝ)
    (fun i _ => le_of_lt (eta_lt_one F n i))
  simpa [Finset.card_univ] using h

/-- Baseline is at least one half for large `x`. -/
lemma baseline_ge_half {x : ℝ} (hx1 : 1 ≤ L x)
    (hP : P.Admissible F x) (n : ℕ) (hn : n = N x)
    (hL : 10 * ((taylorTerms F).factorial : ℝ) ≤ L x)
    (g : P.BigGroup) (p : P.Prime g.val) :
    (1:ℝ)/2 ≤ baselinePrime F n p.val := by
  have hc : 0 < F.c := lt_trans (lt_trans F.a_pos F.ab) F.bc
  have hS : ∑ i : Fin (n + 1), eta F n i ≤ 5 * L x := by
    have h1 : ∑ i : Fin (n + 1), eta F n i ≤ ((n + 1 : ℕ) : ℝ) := eta_sum_le n
    have h2 : ((n + 1 : ℕ) : ℝ) ≤ 5 * L x := by
      rw [hn]; exact Nx_add_one_le hx1
    linarith
  have hpge := big_prime_ge hP g p
  have hexp := exp_pow_ge_ten_mul hx1 hL
  have hppos : 0 < (p.val : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos _) hpge
  have h2S : 2 * (∑ i : Fin (n + 1), eta F n i) ≤ (p.val : ℝ) := by linarith
  have hSp : (∑ i : Fin (n + 1), eta F n i) / (p.val : ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ hppos]
    linarith
  have hdiv : ((p.val : ℝ))⁻¹ * (∑ i : Fin (n + 1), eta F n i)
      = (∑ i : Fin (n + 1), eta F n i) / (p.val : ℝ) := by
    rw [div_eq_mul_inv, mul_comm]
  have h2 : (1:ℝ) - 1/2 = 1/2 := by norm_num
  rw [← h2]
  unfold baselinePrime
  rw [hdiv]
  exact sub_le_sub_left hSp 1

/-- Tilted densities are positive for large `x`. -/
lemma tiltedMu_pos {x : ℝ} (hx1 : 1 ≤ L x)
    (hP : P.Admissible F x) (n : ℕ) (hn : n = N x)
    (hL : 10 * ((taylorTerms F).factorial : ℝ) ≤ L x)
    (g : P.BigGroup) (p : P.Prime g.val) : 0 < tiltedMu F P n g.val p := by
  unfold tiltedMu
  apply inv_pos.mpr
  apply mul_pos
  · apply mul_pos
    · exact V_pos_of_adm hP g.val
    · have h := (P.prime g.val p.val p.property).pos
      exact_mod_cast h
  · have hb := baseline_ge_half hx1 hP n hn hL g p
    linarith

/-- Fresh tilted mass per big group is at most two for large `x`. -/
lemma tiltedMu_sum_le_two {x : ℝ} (hx1 : 1 ≤ L x)
    (hP : P.Admissible F x) (n : ℕ) (hn : n = N x)
    (hL : 10 * ((taylorTerms F).factorial : ℝ) ≤ L x)
    (g : P.BigGroup) : ∑ p : P.Prime g.val, tiltedMu F P n g.val p ≤ 2 := by
  have hb : ∀ p : P.Prime g.val, (1:ℝ)/2 ≤ baselinePrime F n p.val :=
    fun p => baseline_ge_half hx1 hP n hn hL g p
  have hinv : ∀ p : P.Prime g.val, (baselinePrime F n p.val)⁻¹ ≤ 2 := by
    intro p
    have hbp : 0 < baselinePrime F n p.val := lt_of_lt_of_le (by norm_num) (hb p)
    have h2 : (2:ℝ) = (1/2)⁻¹ := by norm_num
    rw [h2]
    exact (inv_le_inv₀ hbp (by norm_num)).mpr (hb p)
  calc ∑ p : P.Prime g.val, tiltedMu F P n g.val p
      = ∑ p : P.Prime g.val, P.mu g.val p * (baselinePrime F n p.val)⁻¹ := by
        apply Finset.sum_congr rfl
        intro p _
        unfold tiltedMu PrimeGroups.mu
        rw [mul_inv]
    _ ≤ ∑ _p : P.Prime g.val, P.mu g.val _p * 2 := by
        apply Finset.sum_le_sum
        intro p _
        apply mul_le_mul_of_nonneg_left (hinv p)
        exact (mu_pos_of_V_pos g.val (V_pos_of_adm hP g.val) p).le
    _ = 2 := by
        rw [← Finset.sum_mul, mu_sum_eq_one g.val (ne_of_gt (V_pos_of_adm hP g.val)),
          one_mul]

end Erdos821.P3Edge
