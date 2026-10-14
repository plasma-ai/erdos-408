import Mathlib
import OAI.NumberTheory.PrimeGaps.OrthantIntegrals
import Erdos821.Blueprint.Classical

open scoped BigOperators

namespace Erdos821.Classical

/-- The divisor count is submultiplicative. -/
theorem divisors_card_mul_le (a b : ℕ) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  let S := a.primeFactors ∪ b.primeFactors
  have hS : (a * b).primeFactors = S := by
    simp [S, Nat.primeFactors_mul ha hb]
  rw [Nat.card_divisors (mul_ne_zero ha hb), Nat.card_divisors ha,
    Nat.card_divisors hb, hS]
  have hA : ∏ p ∈ S, (a.factorization p + 1) =
      ∏ p ∈ a.primeFactors, (a.factorization p + 1) := by
    symm
    apply Finset.prod_subset (Finset.subset_union_left)
    intro p hp hpA
    have hpz : a.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      simpa only [Nat.support_factorization] using hpA
    simp [hpz]
  have hB : ∏ p ∈ S, (b.factorization p + 1) =
      ∏ p ∈ b.primeFactors, (b.factorization p + 1) := by
    symm
    apply Finset.prod_subset (Finset.subset_union_right)
    intro p hp hpB
    have hpz : b.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      simpa only [Nat.support_factorization] using hpB
    simp [hpz]
  have hprod : ∀ p ∈ S,
      a.factorization p + b.factorization p + 1 ≤
        (a.factorization p + 1) * (b.factorization p + 1) := by
    intro p hp
    nlinarith [Nat.zero_le (a.factorization p * b.factorization p)]
  calc
    _ = ∏ p ∈ S, (a.factorization p + b.factorization p + 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_mul ha hb]
      rfl
    _ ≤ ∏ p ∈ S, ((a.factorization p + 1) * (b.factorization p + 1)) := by
      apply Finset.prod_le_prod
      intro p hp
      exact hprod p hp
    _ = _ := by rw [Finset.prod_mul_distrib, hA, hB]


/-- The generalized divisor function of order `2^k` majorizes the `k`-th
power of the ordinary divisor count. -/
theorem divisorMultiplicity_pow_lower (k n : ℕ) (hn : 0 < n) :
    n.divisors.card ^ k ≤ OAI.LargePrimeGaps.divisorMultiplicity (2 ^ k) n := by
  induction k generalizing n with
  | zero =>
      simp [OAI.LargePrimeGaps.divisorMultiplicity, hn.ne']
  | succ k ih =>
      let q := 2 ^ k
      have hpow : 2 ^ (k + 1) = q + q := by
        dsimp [q]
        rw [pow_succ, Nat.mul_two]
      rw [hpow]
      have hrep (m : ℕ) :
          OAI.LargePrimeGaps.divisorMultiplicity (q + q) m =
            ∑ d ∈ m.divisors,
              OAI.LargePrimeGaps.divisorMultiplicity q d *
                OAI.LargePrimeGaps.divisorMultiplicity q (m / d) := by
        rw [OAI.LargePrimeGaps.divisorMultiplicity, pow_add,
          ArithmeticFunction.mul_apply]
        rw [Nat.sum_divisorsAntidiagonal
          (fun a b => (ArithmeticFunction.zeta ^ q) a * (ArithmeticFunction.zeta ^ q) b)]
        rfl
      calc
        n.divisors.card ^ (k + 1) = n.divisors.card ^ k * n.divisors.card := by
          rw [pow_succ]
        _ = ∑ d ∈ n.divisors, n.divisors.card ^ k := by simp [mul_comm]
        _ ≤ ∑ d ∈ n.divisors,
            OAI.LargePrimeGaps.divisorMultiplicity q d *
              OAI.LargePrimeGaps.divisorMultiplicity q (n / d) := by
          apply Finset.sum_le_sum
          intro d hd
          have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
          have hdp : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
          have hqp : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdvd) hdp
          have hfac : d * (n / d) = n := Nat.mul_div_cancel' hdvd
          have hcount : n.divisors.card ≤ d.divisors.card * (n / d).divisors.card := by
            calc
              n.divisors.card = (d * (n / d)).divisors.card := by rw [hfac]
              _ ≤ d.divisors.card * (n / d).divisors.card := divisors_card_mul_le d (n / d)
          calc
            n.divisors.card ^ k ≤
                (d.divisors.card * (n / d).divisors.card) ^ k :=
              Nat.pow_le_pow_left hcount k
            _ = d.divisors.card ^ k * (n / d).divisors.card ^ k := by rw [Nat.mul_pow]
            _ ≤ OAI.LargePrimeGaps.divisorMultiplicity q d *
                OAI.LargePrimeGaps.divisorMultiplicity q (n / d) :=
              Nat.mul_le_mul (ih d hdp) (ih (n / d) hqp)
        _ = OAI.LargePrimeGaps.divisorMultiplicity (q + q) n := (hrep n).symm


/-- The fixed divisor moments have logarithmic reciprocal and counting bounds. -/
def DivisorMoments : Prop :=
  ∀ k : ℕ, ∃ C K : ℝ, 0 < K ∧ ∀ Y : ℝ, 1 ≤ Y →
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k / n) ≤
      K * Real.log (2 * Y) ^ C ∧
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k) ≤
      K * Y * Real.log (2 * Y) ^ C

theorem divisorMoments : DivisorMoments := by
  intro k
  let D : ℕ := 2 ^ k
  let c : ℝ := 1 + (Real.log 2)⁻¹
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨(D : ℝ), c ^ D, by positivity, ?_⟩
  intro Y hY
  let N : ℕ := ⌊Y⌋₊
  have hN : 1 ≤ N :=
    (Nat.le_floor_iff (le_trans (by norm_num) hY)).2 (by exact_mod_cast hY)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNY : (N : ℝ) ≤ Y := Nat.floor_le (le_trans (by norm_num) hY)
  have hN2Y : (N : ℝ) ≤ 2 * Y := by nlinarith [hNY, hY]
  have hlogY : Real.log (N : ℝ) ≤ Real.log (2 * Y) :=
    Real.log_le_log hNpos (by nlinarith [hN2Y])
  have hlog2Y : Real.log 2 ≤ Real.log (2 * Y) :=
    Real.log_le_log (by norm_num) (by nlinarith [hY])
  have hlogpos : 0 < Real.log (2 * Y) :=
    Real.log_pos (by nlinarith [hY])
  have hharm : (harmonic N : ℝ) ≤ c * Real.log (2 * Y) := by
    calc
      (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
      _ ≤ 1 + Real.log (2 * Y) := by simpa [add_comm] using add_le_add_left hlogY 1
      _ ≤ c * Real.log (2 * Y) := by
        have hprod : 1 ≤ (Real.log 2)⁻¹ * Real.log (2 * Y) := by
          calc
            1 = (Real.log 2)⁻¹ * Real.log 2 := by field_simp [hlog2.ne']
            _ ≤ (Real.log 2)⁻¹ * Real.log (2 * Y) :=
              mul_le_mul_of_nonneg_left hlog2Y (inv_nonneg.mpr hlog2.le)
        dsimp [c]
        nlinarith [hprod]
  have hrec :
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / n) ≤
        (harmonic N : ℝ) ^ D := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N,
          (OAI.LargePrimeGaps.divisorMultiplicity D n : ℝ) / (n : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnp : 0 < n := by
          have hn' := Finset.mem_Icc.mp hn
          omega
        have hmaj : (n.divisors.card : ℝ) ^ k ≤
            (OAI.LargePrimeGaps.divisorMultiplicity D n : ℝ) := by
          exact_mod_cast divisorMultiplicity_pow_lower k n hnp
        exact div_le_div_of_nonneg_right hmaj (by positivity)
      _ ≤ (harmonic N : ℝ) ^ D :=
        OAI.LargePrimeGaps.sum_divisorMultiplicity_reciprocal_le D N
  have hrecBound :
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / n) ≤
        c ^ D * Real.log (2 * Y) ^ (D : ℝ) := by
    calc
      _ ≤ (harmonic N : ℝ) ^ D := hrec
      _ ≤ (c * Real.log (2 * Y)) ^ D := by
        have hHnonneg : (0 : ℝ) ≤ (harmonic N : ℝ) := by
          rw [harmonic_eq_sum_Icc]
          simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
          apply Finset.sum_nonneg
          intro i hi
          positivity
        exact pow_le_pow_left₀ hHnonneg hharm D
      _ = c ^ D * Real.log (2 * Y) ^ D := by rw [mul_pow]
      _ = c ^ D * Real.log (2 * Y) ^ (D : ℝ) := by simp [Real.rpow_natCast]
  have hunweighted :
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k) ≤
        Y * (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / n) := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N, Y * ((n.divisors.card : ℝ) ^ k / n) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnI := Finset.mem_Icc.mp hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hnY : (n : ℝ) ≤ Y := by
          exact (Nat.cast_le.mpr hnI.2).trans hNY
        have hfactor :
            (n.divisors.card : ℝ) ^ k =
              ((n.divisors.card : ℝ) ^ k / n) * (n : ℝ) := by
          field_simp [hnpos.ne']
        calc
          (n.divisors.card : ℝ) ^ k =
              ((n.divisors.card : ℝ) ^ k / n) * (n : ℝ) := hfactor
          _ ≤ ((n.divisors.card : ℝ) ^ k / n) * Y :=
            mul_le_mul_of_nonneg_left hnY
              (div_nonneg (by positivity) hnpos.le)
          _ = Y * ((n.divisors.card : ℝ) ^ k / n) := by ring
      _ = Y * (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / n) := by
        rw [Finset.mul_sum]
  refine ⟨?_, ?_⟩
  · simpa only [N] using hrecBound
  · calc
      _ ≤ Y * (c ^ D * Real.log (2 * Y) ^ (D : ℝ)) := by
        exact hunweighted.trans (mul_le_mul_of_nonneg_left hrecBound (by positivity))
      _ = c ^ D * Y * Real.log (2 * Y) ^ (D : ℝ) := by ring


/-- The order-`m` generalized divisor function is at most `τ(n)^(m-1)`. -/
theorem divisorMultiplicity_order_le (m n : ℕ) (hn : 0 < n) :
    OAI.LargePrimeGaps.divisorMultiplicity (m + 1) n ≤ n.divisors.card ^ m := by
  induction m generalizing n with
  | zero =>
      simp [OAI.LargePrimeGaps.divisorMultiplicity, hn.ne']
  | succ m ih =>
      rw [show m + 1 + 1 = (m + 1) + 1 by omega,
        OAI.LargePrimeGaps.divisorMultiplicity_succ]
      calc
        (∑ d ∈ n.divisors,
            OAI.LargePrimeGaps.divisorMultiplicity (m + 1) d) ≤
            ∑ d ∈ n.divisors, n.divisors.card ^ m := by
          apply Finset.sum_le_sum
          intro d hd
          have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
          have hdp : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
          have hsub : d.divisors ⊆ n.divisors := by
            intro e he
            exact Nat.mem_divisors.mpr
              ⟨(Nat.mem_divisors.mp he).1.trans hdvd, hn.ne'⟩
          have hcard : d.divisors.card ≤ n.divisors.card := Finset.card_le_card hsub
          exact (ih d hdp).trans (Nat.pow_le_pow_left hcard m)
        _ = n.divisors.card ^ m * n.divisors.card := by simp [mul_comm]
        _ = n.divisors.card ^ (m + 1) := by rw [pow_succ]


/-- Iterated Dirichlet convolution of a nonempty list of sequences. -/
noncomputable def dirichletConvList : List (ℕ → ℂ) → ℕ → ℂ
  | [], _ => 0
  | [f], n => f n
  | f :: g :: fs, n =>
      ∑ d ∈ n.divisors, f d * dirichletConvList (g :: fs) (n / d)

/-- A convolution coefficient is bounded by the factorization count times
one coefficient bound for each input sequence. -/
theorem dirichletConvList_norm_le (R : ℝ) (hR : 0 ≤ R) :
    ∀ fs : List (ℕ → ℂ), fs ≠ [] →
      (∀ f ∈ fs, ∀ n, 0 < n → ‖f n‖ ≤ R) →
      ∀ n, 0 < n →
        ‖dirichletConvList fs n‖ ≤
          R ^ fs.length * (n.divisors.card : ℝ) ^ fs.length := by
  intro fs
  induction fs with
  | nil =>
      simp
  | cons f tail ih =>
      intro hne hb n hn
      cases tail with
      | nil =>
          have hcard : 1 ≤ n.divisors.card := by
            have h1 : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn.ne'
            have hp := Finset.card_pos.mpr ⟨1, h1⟩
            omega
          have hbase : ‖f n‖ ≤ R * (n.divisors.card : ℝ) := by
            calc
              ‖f n‖ ≤ R := hb f (by simp) n hn
              _ = R * 1 := by ring
              _ ≤ R * (n.divisors.card : ℝ) := by
                have hcardR : (1 : ℝ) ≤ (n.divisors.card : ℝ) := by exact_mod_cast hcard
                exact mul_le_mul_of_nonneg_left hcardR hR
          simpa [dirichletConvList] using hbase
      | cons g rest =>
          have hbTail : ∀ a ∈ g :: rest, ∀ m, 0 < m → ‖a m‖ ≤ R := by
            intro a ha m hm
            have hmem : a ∈ f :: g :: rest := by
              simpa only [List.mem_cons] using (Or.inr ha : a = f ∨ a ∈ g :: rest)
            exact hb a hmem m hm
          have hneTail : g :: rest ≠ [] := by simp
          let ℓ : ℕ := (g :: rest).length
          have hlen : (f :: g :: rest).length = ℓ + 1 := by
            simp [ℓ]
          rw [dirichletConvList]
          rw [hlen]
          calc
            ‖∑ d ∈ n.divisors, f d * dirichletConvList (g :: rest) (n / d)‖ ≤
                ∑ d ∈ n.divisors,
                  ‖f d * dirichletConvList (g :: rest) (n / d)‖ := norm_sum_le _ _
            _ ≤ ∑ d ∈ n.divisors,
                  R * (R ^ ℓ * (n.divisors.card : ℝ) ^ ℓ) := by
              apply Finset.sum_le_sum
              intro d hd
              have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
              have hdp : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
              have hqp : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdvd) hdp
              have hqdiv : n / d ∣ n := Nat.div_dvd_of_dvd hdvd
              have hsub : (n / d).divisors ⊆ n.divisors := by
                intro e he
                exact Nat.mem_divisors.mpr
                  ⟨(Nat.mem_divisors.mp he).1.trans hqdiv, hn.ne'⟩
              have hcard : (n / d).divisors.card ≤ n.divisors.card :=
                Finset.card_le_card hsub
              have hconv := ih hneTail hbTail (n / d) hqp
              calc
                ‖f d * dirichletConvList (g :: rest) (n / d)‖ =
                    ‖f d‖ * ‖dirichletConvList (g :: rest) (n / d)‖ := norm_mul _ _
                _ ≤ R * (R ^ ℓ * ((n / d).divisors.card : ℝ) ^ ℓ) :=
                  mul_le_mul (hb f (by simp) d hdp) hconv
                    (norm_nonneg _) hR
                _ ≤ R * (R ^ ℓ * (n.divisors.card : ℝ) ^ ℓ) := by
                  gcongr
            _ = (n.divisors.card : ℝ) *
                  (R * (R ^ ℓ * (n.divisors.card : ℝ) ^ ℓ)) := by simp
            _ = R ^ (ℓ + 1) * (n.divisors.card : ℝ) ^ (ℓ + 1) := by
              rw [pow_succ, pow_succ]
              ring


/-- The squared coefficients of a fixed iterated convolution have a
logarithmic-power bound on each dyadic interval. -/
theorem dirichletConvList_square_sum_dyad (R : ℝ) (hR : 0 ≤ R)
    (fs : List (ℕ → ℂ)) (hfs : fs ≠ [])
    (hb : ∀ f ∈ fs, ∀ n, 0 < n → ‖f n‖ ≤ R)
    (U : ℕ) (hU : 1 ≤ U) :
    ∃ C K : ℝ, 0 < K ∧
      (∑ n ∈ Finset.Icc U (2 * U),
        ‖dirichletConvList fs n‖ ^ 2) ≤
        R ^ (2 * fs.length) * K * (2 * (U : ℝ)) *
          Real.log (2 * (2 * (U : ℝ))) ^ C := by
  let k : ℕ := 2 * fs.length
  obtain ⟨C, K, hK, hm⟩ := divisorMoments k
  let Y : ℝ := 2 * (U : ℝ)
  have hY : 1 ≤ Y := by
    dsimp [Y]
    exact_mod_cast (show 1 ≤ 2 * U by omega)
  have hfloor : ⌊Y⌋₊ = 2 * U := by
    dsimp [Y]
    rw [show (2 : ℝ) * (U : ℝ) = ((2 * U : ℕ) : ℝ) by norm_num]
    exact Nat.floor_natCast _
  have hm' :
      (∑ n ∈ Finset.Icc 1 (2 * U), (n.divisors.card : ℝ) ^ k) ≤
        K * (2 * (U : ℝ)) * Real.log (2 * (2 * (U : ℝ))) ^ C := by
    simpa [Y, hfloor] using (hm Y hY).2
  have hsub : Finset.Icc U (2 * U) ⊆ Finset.Icc 1 (2 * U) := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hnU, hn2⟩
    exact Finset.mem_Icc.mpr ⟨by omega, hn2⟩
  have htausum :
      (∑ n ∈ Finset.Icc U (2 * U), (n.divisors.card : ℝ) ^ k) ≤
        (∑ n ∈ Finset.Icc 1 (2 * U), (n.divisors.card : ℝ) ^ k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn hnot
    positivity
  have hterms (n : ℕ) (hn : n ∈ Finset.Icc U (2 * U)) :
      ‖dirichletConvList fs n‖ ^ 2 ≤
        R ^ (2 * fs.length) * (n.divisors.card : ℝ) ^ k := by
    have hnpos : 0 < n := by
      have h := (Finset.mem_Icc.mp hn).1
      omega
    have hcoeff := dirichletConvList_norm_le R hR fs hfs hb n hnpos
    have hcoeff_nonneg :
        0 ≤ R ^ fs.length * (n.divisors.card : ℝ) ^ fs.length := by
      positivity
    calc
      ‖dirichletConvList fs n‖ ^ 2 ≤
          (R ^ fs.length * (n.divisors.card : ℝ) ^ fs.length) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hcoeff_nonneg).2 hcoeff
      _ = R ^ (2 * fs.length) * (n.divisors.card : ℝ) ^ k := by
        calc
          _ = R ^ (fs.length * 2) *
              (n.divisors.card : ℝ) ^ (fs.length * 2) := by
            rw [mul_pow, ← pow_mul, ← pow_mul]
          _ = R ^ (2 * fs.length) * (n.divisors.card : ℝ) ^ k := by
            simp [k, Nat.mul_comm]
  refine ⟨C, K, hK, ?_⟩
  calc
    (∑ n ∈ Finset.Icc U (2 * U),
        ‖dirichletConvList fs n‖ ^ 2) ≤
        ∑ n ∈ Finset.Icc U (2 * U),
          R ^ (2 * fs.length) * (n.divisors.card : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro n hn
      exact hterms n hn
    _ = R ^ (2 * fs.length) *
        (∑ n ∈ Finset.Icc U (2 * U), (n.divisors.card : ℝ) ^ k) := by
      rw [← Finset.mul_sum]
    _ ≤ R ^ (2 * fs.length) *
        (∑ n ∈ Finset.Icc 1 (2 * U), (n.divisors.card : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left htausum (by positivity)
    _ ≤ R ^ (2 * fs.length) *
        (K * (2 * (U : ℝ)) * Real.log (2 * (2 * (U : ℝ))) ^ C) :=
      mul_le_mul_of_nonneg_left hm' (by positivity)
    _ = R ^ (2 * fs.length) * K * (2 * (U : ℝ)) *
        Real.log (2 * (2 * (U : ℝ))) ^ C := by ring

end Erdos821.Classical







namespace Erdos821.DivisorHarmonic

open Erdos821.Classical

/-- If each convolution factor is bounded by `R/n`, its coefficient at `n`
is bounded by the divisor majorant with the same reciprocal index. -/
theorem dirichletConvList_norm_le_recip (R : ℝ) (hR : 0 ≤ R)
    (fs : List (ℕ → ℂ)) (hfs : fs ≠ [])
    (hb : ∀ f ∈ fs, ∀ n, 0 < n → ‖f n‖ ≤ R / (n : ℝ))
    (n : ℕ) (hn : 0 < n) :
    ‖dirichletConvList fs n‖ ≤
      R ^ fs.length * (n.divisors.card : ℝ) ^ fs.length / n := by
  have hmul (fs : List (ℕ → ℂ)) (n : ℕ) :
      dirichletConvList (fs.map (fun f m => (m : ℂ) * f m)) n =
        (n : ℂ) * dirichletConvList fs n := by
    induction fs generalizing n with
    | nil => simp [dirichletConvList]
    | cons f tail ih =>
        cases tail with
        | nil => simp [dirichletConvList]
        | cons g rest =>
            change (∑ d ∈ n.divisors,
                ((d : ℂ) * f d) *
                  dirichletConvList ((g :: rest).map (fun a m => (m : ℂ) * a m)) (n / d)) =
              (n : ℂ) *
                (∑ d ∈ n.divisors,
                  f d * dirichletConvList (g :: rest) (n / d))
            calc
              (∑ d ∈ n.divisors,
                  ((d : ℂ) * f d) *
                    dirichletConvList ((g :: rest).map (fun a m => (m : ℂ) * a m)) (n / d)) =
                  ∑ d ∈ n.divisors,
                    ((d : ℂ) * f d) * (((n / d : ℕ) : ℂ) * dirichletConvList (g :: rest) (n / d)) := by
                      apply Finset.sum_congr rfl
                      intro d hd
                      rw [ih]
              _ = ∑ d ∈ n.divisors,
                  (n : ℂ) * (f d * dirichletConvList (g :: rest) (n / d)) := by
                      apply Finset.sum_congr rfl
                      intro d hd
                      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
                      have hfac : (d : ℂ) * ((n / d : ℕ) : ℂ) = (n : ℂ) := by
                        exact_mod_cast Nat.mul_div_cancel' hdvd
                      rw [← hfac]
                      ring
              _ = (n : ℂ) *
                  (∑ d ∈ n.divisors,
                    f d * dirichletConvList (g :: rest) (n / d)) := by
                      rw [Finset.mul_sum]
  let w : (ℕ → ℂ) → ℕ → ℂ := fun f m => (m : ℂ) * f m
  have hmapne : fs.map w ≠ [] := by simpa using hfs
  have hwb : ∀ g ∈ fs.map w, ∀ m, 0 < m → ‖g m‖ ≤ R := by
    intro g hg m hm
    rcases List.mem_map.mp hg with ⟨f, hf, hfg⟩
    subst g
    dsimp [w]
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    calc
      ‖(m : ℂ) * f m‖ = (m : ℝ) * ‖f m‖ := by simp
      _ ≤ (m : ℝ) * (R / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left (hb f hf m hm) hmR.le
      _ = R := by field_simp
  have hconv := dirichletConvList_norm_le R hR (fs.map w) hmapne hwb n hn
  have hscaled :
      (n : ℝ) * ‖dirichletConvList fs n‖ ≤
        R ^ fs.length * (n.divisors.card : ℝ) ^ fs.length := by
    calc
      (n : ℝ) * ‖dirichletConvList fs n‖ =
          ‖(n : ℂ) * dirichletConvList fs n‖ := by simp
      _ = ‖dirichletConvList (fs.map w) n‖ := by
        rw [hmul]
      _ ≤ R ^ (fs.map w).length * (n.divisors.card : ℝ) ^ (fs.map w).length := hconv
      _ = R ^ fs.length * (n.divisors.card : ℝ) ^ fs.length := by simp
  apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).2
  nlinarith [hscaled]

/-- The squared coefficients of a reciprocal-index convolution have a
logarithmic-power bound divided by the dyadic scale. -/
theorem dirichletConvList_recip_square_sum_dyad (R : ℝ) (hR : 0 ≤ R)
    (fs : List (ℕ → ℂ)) (hfs : fs ≠ [])
    (hb : ∀ f ∈ fs, ∀ n, 0 < n → ‖f n‖ ≤ R / (n : ℝ))
    (U : ℕ) (hU : 1 ≤ U) :
    ∃ C K : ℝ, 0 < K ∧
      (∑ n ∈ Finset.Icc U (2 * U),
        ‖dirichletConvList fs n‖ ^ 2) ≤
        R ^ (2 * fs.length) * K *
          Real.log (2 * (2 * (U : ℝ))) ^ C / U := by
  let k : ℕ := 2 * fs.length
  obtain ⟨C, K, hK, hm⟩ := divisorMoments k
  let Y : ℝ := 2 * (U : ℝ)
  have hY : 1 ≤ Y := by
    dsimp [Y]
    exact_mod_cast (show 1 ≤ 2 * U by omega)
  have hfloor : ⌊Y⌋₊ = 2 * U := by
    dsimp [Y]
    rw [show (2 : ℝ) * (U : ℝ) = ((2 * U : ℕ) : ℝ) by norm_num]
    exact Nat.floor_natCast _
  have hm' :
      (∑ n ∈ Finset.Icc 1 (2 * U), (n.divisors.card : ℝ) ^ k / n) ≤
        K * Real.log (2 * (2 * (U : ℝ))) ^ C := by
    simpa [Y, hfloor] using (hm Y hY).1
  have hsub : Finset.Icc U (2 * U) ⊆ Finset.Icc 1 (2 * U) := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hnU, hn2⟩
    exact Finset.mem_Icc.mpr ⟨by omega, hn2⟩
  have hrecSum :
      (∑ n ∈ Finset.Icc U (2 * U), (n.divisors.card : ℝ) ^ k / n) ≤
        (∑ n ∈ Finset.Icc 1 (2 * U), (n.divisors.card : ℝ) ^ k / n) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn hnot
    positivity
  have hterms (n : ℕ) (hnmem : n ∈ Finset.Icc U (2 * U)) :
      ‖dirichletConvList fs n‖ ^ 2 ≤
        (R ^ (2 * fs.length) / (U : ℝ)) *
          ((n.divisors.card : ℝ) ^ k / n) := by
    have hnU : U ≤ n := (Finset.mem_Icc.mp hnmem).1
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hUR : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (by omega : 0 < U)
    have hnUreal : (U : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnU
    have hden : (n : ℝ) * U ≤ (n : ℝ) ^ 2 := by nlinarith
    have hinv : 1 / (n : ℝ) ^ 2 ≤ 1 / ((n : ℝ) * U) :=
      one_div_le_one_div_of_le (mul_pos hnR hUR) hden
    have hfrac :
        (n.divisors.card : ℝ) ^ k / (n : ℝ) ^ 2 ≤
          (n.divisors.card : ℝ) ^ k / (n : ℝ) / U := by
      calc
        _ = (n.divisors.card : ℝ) ^ k * (1 / (n : ℝ) ^ 2) := by ring
        _ ≤ (n.divisors.card : ℝ) ^ k * (1 / ((n : ℝ) * U)) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = (n.divisors.card : ℝ) ^ k / (n : ℝ) / U := by
          field_simp [hnR.ne', hUR.ne']
    have hcoef := dirichletConvList_norm_le_recip R hR fs hfs hb n hnpos
    calc
      ‖dirichletConvList fs n‖ ^ 2 ≤
          (R ^ fs.length * (n.divisors.card : ℝ) ^ fs.length / n) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hcoef
      _ = R ^ (2 * fs.length) *
          ((n.divisors.card : ℝ) ^ k / (n : ℝ) ^ 2) := by
        calc
          _ = (R ^ fs.length * (n.divisors.card : ℝ) ^ fs.length) ^ 2 /
                (n : ℝ) ^ 2 := by rw [div_pow]
          _ = R ^ (fs.length * 2) *
                (n.divisors.card : ℝ) ^ (fs.length * 2) / (n : ℝ) ^ 2 := by
              rw [mul_pow, ← pow_mul, ← pow_mul]
          _ = R ^ (2 * fs.length) *
                ((n.divisors.card : ℝ) ^ k / (n : ℝ) ^ 2) := by
              simp [k, Nat.mul_comm]
              ring
      _ ≤ R ^ (2 * fs.length) *
          ((n.divisors.card : ℝ) ^ k / (n : ℝ) / U) :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = (R ^ (2 * fs.length) / (U : ℝ)) *
          ((n.divisors.card : ℝ) ^ k / n) := by ring
  have hQ : 0 ≤ R ^ (2 * fs.length) / (U : ℝ) := by positivity
  refine ⟨C, K, hK, ?_⟩
  calc
    (∑ n ∈ Finset.Icc U (2 * U),
        ‖dirichletConvList fs n‖ ^ 2) ≤
        ∑ n ∈ Finset.Icc U (2 * U),
          (R ^ (2 * fs.length) / (U : ℝ)) *
            ((n.divisors.card : ℝ) ^ k / n) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hterms n hn
    _ = (R ^ (2 * fs.length) / (U : ℝ)) *
        (∑ n ∈ Finset.Icc U (2 * U),
          (n.divisors.card : ℝ) ^ k / n) := by
      rw [← Finset.mul_sum]
    _ ≤ (R ^ (2 * fs.length) / (U : ℝ)) *
        (∑ n ∈ Finset.Icc 1 (2 * U),
          (n.divisors.card : ℝ) ^ k / n) :=
      mul_le_mul_of_nonneg_left hrecSum hQ
    _ ≤ (R ^ (2 * fs.length) / (U : ℝ)) *
        (K * Real.log (2 * (2 * (U : ℝ))) ^ C) :=
      mul_le_mul_of_nonneg_left hm' hQ
    _ = R ^ (2 * fs.length) * K *
        Real.log (2 * (2 * (U : ℝ))) ^ C / U := by ring

end Erdos821.DivisorHarmonic



theorem Erdos821.Blueprint.DivisorMoments_proof :
    Erdos821.Blueprint.DivisorMoments := Erdos821.Classical.divisorMoments

example : type_of% @Erdos821.Blueprint.DivisorMoments_proof =
    Erdos821.Blueprint.DivisorMoments := rfl

