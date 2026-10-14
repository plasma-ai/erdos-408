module

public import Erdos408.Extraction.TypeII.Proxy
public import Erdos408.Extraction.TypeII.Rough
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Sums of the damped weight

Write `Π_P(u) = ∏_{p ∈ P} (1 - u/p)⁻¹` and `Π_{(Y,N]}(u) = ∏_{Y < p ≤ N} (1 - u/p)⁻¹`, so
that `D_j = ∏_{p ≤ Y} (1 - 1/p) · Π_P(1/j)`.

* Log densities, by the Euler product: `∑_{m ≤ N} g(m)/m ≤ Π_P(t) Π_{(Y,N]}(1)` and
  `∑_{m ≤ N} g(m)² r^{Ω(m)}/m ≤ Π_P(r t²) Π_{(Y,N]}(r)`.
* The candidate logarithm: `∑_{m ≤ N} g(m) log(m/m̄)/m ≤ 2t (∑_P log p/p) ∑_{m ≤ N} g(m)/m`,
  from `g(p^a m) = t^a g(m)`.
* The rough-count bound `∑_{m ≤ W} g(m) ≤ (A W / log Y) Π_P(t) + W^θ ∏_P (1 - p^{-θ})⁻¹`:
  split `m = m̄ · m_P`, count the rough `m̄ ≤ W / m_P` by `roughCount_le`, and bound the
  number of `P`-numbers by Rankin's trick.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real

/-- Candidate primes lie below `Y` when `exp(L^{0.45}) < Y`. -/
theorem candidate_lt_cutoff {x : ℝ} (hL : 1 ≤ Real.log x)
    (hYP : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x) {p : ℕ}
    (hp : p ∈ candidatePrimes x) : (p : ℝ) < proxyCutoff x :=
  lt_of_le_of_lt (mem_candidatePrimes hL hp).2.2 hYP

/-- The Euler product over the primes up to `N` splits into the candidate primes and the
primes in `(Y, N]` when the weight vanishes on the other primes up to `Y`. -/
theorem prod_primes_split {x : ℝ} (hL : 1 ≤ Real.log x)
    (hYP : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x) {N : ℕ}
    (hYN : proxyCutoff x ≤ N) (loc : ℕ → ℝ)
    (hloc : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ proxyCutoff x → p ∉ candidatePrimes x → loc p = 0) :
    ∏ p ∈ (range (N + 1)).filter Nat.Prime, (1 - loc p)⁻¹ =
      (∏ p ∈ candidatePrimes x, (1 - loc p)⁻¹) *
        ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - loc p)⁻¹ := by
  have hdisj : Disjoint (candidatePrimes x) (primesIoc (proxyCutoff x) N) := by
    refine disjoint_left.2 fun p hp hp' => ?_
    have := (mem_primesIoc.1 hp').2.1
    linarith [candidate_lt_cutoff hL hYP hp]
  rw [← prod_union hdisj]
  symm
  refine prod_subset (fun p hp => ?_) fun p hp hnot => ?_
  · rw [mem_filter, mem_range]
    rcases mem_union.1 hp with h | h
    · obtain ⟨hpp, -, hle⟩ := mem_candidatePrimes hL h
      have : (p : ℝ) ≤ N := (candidate_lt_cutoff hL hYP h).le.trans hYN
      exact ⟨by exact_mod_cast (show (p : ℝ) < N + 1 by linarith), hpp⟩
    · obtain ⟨hpp, -, hle⟩ := mem_primesIoc.1 h
      exact ⟨by exact_mod_cast (show (p : ℝ) < N + 1 by linarith), hpp⟩
  · rw [mem_filter, mem_range] at hp
    rw [mem_union, not_or] at hnot
    have hpY : (p : ℝ) ≤ proxyCutoff x := by
      by_contra h
      push Not at h
      exact hnot.2 (mem_primesIoc.2 ⟨hp.2, h, by exact_mod_cast (by omega : p ≤ N)⟩)
    rw [hloc p hp.2 hpY hnot.1, sub_zero, inv_one]

theorem proxyLoc_nonneg (x : ℝ) (j p : ℕ) : 0 ≤ proxyLoc x j p := by
  unfold proxyLoc; split_ifs <;> positivity

theorem proxyLoc_le_one (x : ℝ) {j : ℕ} (hj : 1 ≤ j) (p : ℕ) : proxyLoc x j p ≤ 1 := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  unfold proxyLoc; split_ifs
  · exact inv_le_one_of_one_le₀ hj'
  · exact zero_le_one
  · exact le_rfl

theorem proxyLoc_of_candidate {x : ℝ} {j p : ℕ} (hp : p ∈ candidatePrimes x) :
    proxyLoc x j p = (j : ℝ)⁻¹ := by simp [proxyLoc, hp]

theorem proxyLoc_of_gt {x : ℝ} (hL : 1 ≤ Real.log x)
    (hYP : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x) {j p : ℕ}
    (hp : proxyCutoff x < p) : proxyLoc x j p = 1 := by
  have hP : p ∉ candidatePrimes x := fun h => by linarith [candidate_lt_cutoff hL hYP h]
  simp [proxyLoc, hP, not_le.2 hp]

theorem proxyLoc_of_le {x : ℝ} {j p : ℕ} (hpY : (p : ℝ) ≤ proxyCutoff x)
    (hP : p ∉ candidatePrimes x) : proxyLoc x j p = 0 := by
  simp [proxyLoc, hP, hpY]

/-- `g(p) = 1` at primes above `Y`. -/
theorem dampedWeight_prime {x : ℝ} (hL : 1 ≤ Real.log x)
    (hYP : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x) {j p : ℕ} (hpp : p.Prime)
    (hp : proxyCutoff x < p) : dampedWeight x j p = 1 := by
  rw [dampedWeight_eq_cmul x j hpp.ne_zero, cmul_prime _ hpp, proxyLoc_of_gt hL hYP hp]

/-- The log density `∑_{m ≤ N} g(m)/m ≤ Π_P(t) Π_{(Y,N]}(1)`. -/
theorem sum_dampedWeight_div_le {x : ℝ} (hL : 1 ≤ Real.log x)
    (hYP : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x) {N : ℕ}
    (hYN : proxyCutoff x ≤ N) {j : ℕ} (hj : 1 ≤ j) :
    ∑ m ∈ Icc 1 N, dampedWeight x j m / m ≤
      (∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹) *
        ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹ := by
  have hsum : ∑ m ∈ Icc 1 N, dampedWeight x j m / m =
      ∑ m ∈ Icc 1 N, cmul (fun p => proxyLoc x j p / p) m := by
    refine sum_congr rfl fun m hm => ?_
    have hm0 : m ≠ 0 := by have := (mem_Icc.1 hm).1; omega
    rw [dampedWeight_eq_cmul x j hm0, cmul_div hm0]
  rw [hsum]
  refine (sum_cmul_le_prod (fun p hp => by have := proxyLoc_nonneg x j p; positivity)
    (fun p hp => ?_) N).trans (le_of_eq ?_)
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [div_lt_one (by linarith)]
    linarith [proxyLoc_le_one x hj p]
  · rw [prod_primes_split hL hYP hYN _ fun p hp hpY hP => by
      rw [proxyLoc_of_le hpY hP, zero_div]]
    congr 1
    · exact prod_congr rfl fun p hp => by rw [proxyLoc_of_candidate hp]
    · exact prod_congr rfl fun p hp => by
        rw [proxyLoc_of_gt hL hYP (mem_primesIoc.1 hp).2.1]

/-- The twisted second log density `∑_{m ≤ N} g(m)² r^{Ω(m)}/m ≤ Π_P(r t²) Π_{(Y,N]}(r)`. -/
theorem sum_dampedWeight_sq_div_le {x : ℝ} (hL : 1 ≤ Real.log x)
    (hYP : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x) {N : ℕ}
    (hYN : proxyCutoff x ≤ N) {j : ℕ} (hj : 1 ≤ j) {r : ℝ} (hr : 0 ≤ r) (hrj : r ≤ j)
    (hrY : r < proxyCutoff x) :
    ∑ m ∈ Icc 1 N, dampedWeight x j m ^ 2 * cmul (fun _ => r) m / m ≤
      (∏ p ∈ candidatePrimes x, (1 - r * ((j : ℝ)⁻¹) ^ 2 / p)⁻¹) *
        ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - r / p)⁻¹ := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hsum : ∑ m ∈ Icc 1 N, dampedWeight x j m ^ 2 * cmul (fun _ => r) m / m =
      ∑ m ∈ Icc 1 N, cmul (fun p => proxyLoc x j p * proxyLoc x j p * r / p) m := by
    refine sum_congr rfl fun m hm => ?_
    have hm0 : m ≠ 0 := by have := (mem_Icc.1 hm).1; omega
    rw [dampedWeight_eq_cmul x j hm0, sq, ← cmul_mul_loc, ← cmul_mul_loc, cmul_div hm0]
  rw [hsum]
  refine (sum_cmul_le_prod (fun p hp => by have := proxyLoc_nonneg x j p; positivity)
    (fun p hp => ?_) N).trans (le_of_eq ?_)
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [div_lt_one (by linarith)]
    unfold proxyLoc
    split_ifs with h1 h2
    · have : (j : ℝ)⁻¹ * (j : ℝ)⁻¹ * r ≤ 1 := by
        rw [mul_assoc, inv_mul_le_iff₀ (by linarith), mul_one]
        calc (j : ℝ)⁻¹ * r ≤ (j : ℝ)⁻¹ * j := by gcongr
          _ = 1 := inv_mul_cancel₀ (by linarith)
          _ ≤ j := hj'
      linarith
    · simp only [mul_zero, zero_mul]; linarith
    · have : proxyCutoff x < p := by push Not at h2; exact h2
      linarith
  · rw [prod_primes_split hL hYP hYN _ fun p hp hpY hP => by
      rw [proxyLoc_of_le hpY hP, zero_mul, zero_mul, zero_div]]
    congr 1
    · exact prod_congr rfl fun p hp => by rw [proxyLoc_of_candidate hp]; ring_nf
    · exact prod_congr rfl fun p hp => by
        rw [proxyLoc_of_gt hL hYP (mem_primesIoc.1 hp).2.1, one_mul, one_mul]

/-- `g(p^a m) = t^a g(m)` at a candidate prime. -/
theorem dampedWeight_pow_mul {x : ℝ} {j p : ℕ} (hp : p ∈ candidatePrimes x) (hpp : p.Prime)
    (a : ℕ) {m : ℕ} (hm : m ≠ 0) :
    dampedWeight x j (p ^ a * m) = ((j : ℝ)⁻¹) ^ a * dampedWeight x j m := by
  rw [dampedWeight_eq_cmul x j (mul_ne_zero (pow_ne_zero _ hpp.ne_zero) hm),
    dampedWeight_eq_cmul x j hm, map_mul, cmul_prime_pow _ hpp, proxyLoc_of_candidate hp]

/-- `v_p(m) = #{a ≤ N : p^a ∣ m}` for `m ≤ N`. -/
theorem factorization_eq_sum_dvd {p m N : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hmN : m ≤ N) :
    (m.factorization p : ℝ) = ∑ a ∈ Icc 1 N, if p ^ a ∣ m then (1 : ℝ) else 0 := by
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_one]
  have : (Icc 1 N).filter (fun a => p ^ a ∣ m) = Icc 1 (m.factorization p) := by
    ext a
    simp only [mem_filter, mem_Icc, hp.pow_dvd_iff_le_factorization hm]
    have := Nat.factorization_lt p hm
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, h2⟩
  rw [this, Nat.card_Icc, Nat.add_sub_cancel]

/-- The candidate logarithm: `∑_{m ≤ N} g(m) log(m / m̄) / m ≤ 2t (∑_P log p / p) ∑ g(m)/m`. -/
theorem sum_dampedWeight_log_div_le {x : ℝ} (hL : 1 ≤ Real.log x) {j : ℕ} (hj : 1 ≤ j)
    (N : ℕ) :
    ∑ m ∈ Icc 1 N, dampedWeight x j m *
        (Real.log m - Real.log (candidateStrip x m)) / m ≤
      2 * (j : ℝ)⁻¹ * (∑ p ∈ candidatePrimes x, Real.log p / p) *
        ∑ m ∈ Icc 1 N, dampedWeight x j m / m := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ht0 : 0 ≤ (j : ℝ)⁻¹ := by positivity
  have ht1 : (j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hj'
  set S := ∑ m ∈ Icc 1 N, dampedWeight x j m / m with hS
  -- expand `log(m / m̄)` over the candidate prime powers dividing `m`
  have hexp : ∀ m ∈ Icc 1 N, Real.log m - Real.log (candidateStrip x m) =
      ∑ p ∈ candidatePrimes x, ∑ a ∈ Icc 1 N, if p ^ a ∣ m then Real.log p else 0 := by
    intro m hm
    obtain ⟨h1, hmN⟩ := mem_Icc.1 hm
    have hm0 : m ≠ 0 := by omega
    rw [candidateStrip, log_eq_log_stripPrimes_add _ hm0, add_sub_cancel_left,
      filter_mem_eq_inter, inter_comm, ← filter_mem_eq_inter, sum_filter]
    refine sum_congr rfl fun p hp => ?_
    split_ifs with hpm
    · rw [factorization_eq_sum_dvd (Nat.prime_of_mem_primeFactors hpm) hm0 hmN, sum_mul]
      exact sum_congr rfl fun a _ => by split_ifs <;> simp
    · refine (sum_eq_zero fun a ha => ?_).symm
      rw [ite_eq_right_iff]
      intro hdvd
      have hpp := (mem_candidatePrimes hL hp).1
      have ha1 := (mem_Icc.1 ha).1
      exact absurd (Nat.mem_primeFactors.2 ⟨hpp, (dvd_pow_self p (by omega)).trans hdvd, hm0⟩)
        hpm
  -- each prime power `p^a` contributes `log p (t/p)^a S`
  have hinner : ∀ p ∈ candidatePrimes x, ∀ a ∈ Icc 1 N,
      ∑ m ∈ Icc 1 N, dampedWeight x j m * (if p ^ a ∣ m then Real.log p else 0) / m ≤
        Real.log p * ((j : ℝ)⁻¹ / p) ^ a * S := by
    intro p hp a ha
    have hpp := (mem_candidatePrimes hL hp).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have h1 : ∑ m ∈ Icc 1 N, dampedWeight x j m * (if p ^ a ∣ m then Real.log p else 0) / m =
        Real.log p * ∑ m ∈ (Icc 1 N).filter (p ^ a ∣ ·), dampedWeight x j m / m := by
      rw [mul_sum, sum_filter]
      refine sum_congr rfl fun m _ => ?_
      split_ifs <;> ring
    rw [h1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hlogp
    have hsub : (Icc 1 N).filter (p ^ a ∣ ·) ⊆ (Icc 1 N).image (p ^ a * ·) := by
      intro m hm
      obtain ⟨hmI, ⟨c, rfl⟩⟩ := mem_filter.1 hm
      obtain ⟨h1, h2⟩ := mem_Icc.1 hmI
      have hc : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with rfl | h
        · simp at h1
        · exact h
      exact mem_image.2 ⟨c, mem_Icc.2 ⟨hc, le_trans (Nat.le_mul_of_pos_left c
        (pow_pos hpp.pos a)) h2⟩, rfl⟩
    have hnn : ∀ m, 0 ≤ dampedWeight x j m / m := fun m =>
      div_nonneg (dampedWeight_nonneg x j m) (Nat.cast_nonneg m)
    calc ∑ m ∈ (Icc 1 N).filter (p ^ a ∣ ·), dampedWeight x j m / m
        ≤ ∑ m ∈ (Icc 1 N).image (p ^ a * ·), dampedWeight x j m / m :=
          sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => hnn m
      _ = ∑ c ∈ Icc 1 N, dampedWeight x j (p ^ a * c) / ((p ^ a * c : ℕ) : ℝ) :=
          sum_image fun c _ c' _ h =>
            Nat.eq_of_mul_eq_mul_left (pow_pos hpp.pos a) h
      _ = ((j : ℝ)⁻¹ / p) ^ a * S := by
          rw [hS, mul_sum]
          refine sum_congr rfl fun c hc => ?_
          have hc0 : c ≠ 0 := by have := (mem_Icc.1 hc).1; omega
          rw [dampedWeight_pow_mul hp hpp a hc0]
          push_cast
          rw [div_pow]
          field_simp
  -- sum the geometric series in `a`
  have hgeom : ∀ p ∈ candidatePrimes x, ∑ a ∈ Icc 1 N, ((j : ℝ)⁻¹ / p) ^ a ≤
      2 * (j : ℝ)⁻¹ / p := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_candidatePrimes hL hp).1.two_le
    have hq0 : 0 ≤ (j : ℝ)⁻¹ / p := by positivity
    have hq1 : (j : ℝ)⁻¹ / p ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hIcc : Icc 1 N = Ico 1 (N + 1) := rfl
    rw [hIcc]
    refine (geom_sum_Ico_le_of_lt_one hq0 (by linarith)).trans ?_
    rw [pow_one, div_le_iff₀ (by linarith)]
    have : (j : ℝ)⁻¹ / p * 2 = 2 * (j : ℝ)⁻¹ / p := by ring
    nlinarith
  have hS0 : 0 ≤ S := sum_nonneg fun m _ =>
    div_nonneg (dampedWeight_nonneg x j m) (Nat.cast_nonneg m)
  clear_value S
  calc ∑ m ∈ Icc 1 N, dampedWeight x j m * (Real.log m - Real.log (candidateStrip x m)) / m
      = ∑ p ∈ candidatePrimes x, ∑ a ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
          dampedWeight x j m * (if p ^ a ∣ m then Real.log p else 0) / m := by
        rw [sum_congr rfl fun m hm => by rw [hexp m hm]]
        simp only [mul_sum, sum_div]
        rw [sum_comm]
        exact sum_congr rfl fun p _ => sum_comm
    _ ≤ ∑ p ∈ candidatePrimes x, ∑ a ∈ Icc 1 N, Real.log p * ((j : ℝ)⁻¹ / p) ^ a * S :=
        sum_le_sum fun p hp => sum_le_sum fun a ha => hinner p hp a ha
    _ = ∑ p ∈ candidatePrimes x, Real.log p * (∑ a ∈ Icc 1 N, ((j : ℝ)⁻¹ / p) ^ a) * S := by
        refine sum_congr rfl fun p _ => ?_
        rw [mul_sum, sum_mul]
    _ ≤ ∑ p ∈ candidatePrimes x, Real.log p * (2 * (j : ℝ)⁻¹ / p) * S := by
        refine sum_le_sum fun p hp => ?_
        have hlogp : 0 ≤ Real.log p := Real.log_nonneg
          (by exact_mod_cast (mem_candidatePrimes hL hp).1.one_lt.le)
        gcongr
        exact hgeom p hp
    _ = _ := by
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun p _ => ?_
        ring

/-- An Euler product supported on `P` is at most the full product over `P`. -/
theorem prod_primes_ite_le (P : Finset ℕ) (u : ℕ → ℝ) (h0 : ∀ p ∈ P, 0 ≤ u p)
    (h1 : ∀ p ∈ P, u p < 1) (N : ℕ) :
    ∏ p ∈ (range (N + 1)).filter Nat.Prime, (1 - if p ∈ P then u p else 0)⁻¹ ≤
      ∏ p ∈ P, (1 - u p)⁻¹ := by
  have : ∏ p ∈ (range (N + 1)).filter Nat.Prime, (1 - if p ∈ P then u p else 0)⁻¹ =
      ∏ p ∈ ((range (N + 1)).filter Nat.Prime).filter (· ∈ P), (1 - u p)⁻¹ := by
    simp only [apply_ite (fun y : ℝ => (1 - y)⁻¹), sub_zero, inv_one]
    rw [← prod_filter]
  rw [this]
  refine prod_le_prod_of_subset_of_one_le₀ (fun p hp => (mem_filter.1 hp).2)
    (fun p hp => inv_nonneg.2 (by linarith [h1 p (mem_filter.1 hp).2])) fun p hp _ => ?_
  rw [one_le_inv₀ (by linarith [h1 p hp])]
  linarith [h0 p hp]

/-- The rough-count bound for the damped weight:
`∑_{m ≤ W} g(m) ≤ (A W / log Y) Π_P(t) + W^θ ∏_P (1 - p^{-θ})⁻¹`. -/
theorem sum_dampedWeight_le : ∃ A C₁ : ℝ, 0 < A ∧ ∀ (x : ℝ) (j W : ℕ) (θ : ℝ),
    1 ≤ Real.log x → 1 ≤ j → 2 ≤ proxyCutoff x → C₁ ≤ Real.log (proxyCutoff x) → 0 < θ →
    ∑ m ∈ Icc 1 W, dampedWeight x j m ≤
      A * W / Real.log (proxyCutoff x) * ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ +
        (W : ℝ) ^ θ * ∏ p ∈ candidatePrimes x, (1 - (p : ℝ) ^ (-θ))⁻¹ := by
  obtain ⟨A, C₁, hA, hrough⟩ := roughCount_le
  refine ⟨A, C₁, hA, fun x j W θ hL hj hY2 hC₁ hθ => ?_⟩
  set Y := proxyCutoff x with hYdef
  set P := candidatePrimes x with hPdef
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ht0 : 0 ≤ (j : ℝ)⁻¹ := by positivity
  have ht1 : (j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hj'
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (mem_candidatePrimes hL hp).1
  -- `g(m) ≤ [m̄ rough] g(m_P)`
  set R : ℕ → Prop := fun n => ∀ p : ℕ, p ∈ n.primeFactors → Y < p with hRdef
  have hsplit : ∀ m ∈ Icc 1 W, dampedWeight x j m ≤
      if R (stripPrimes P m) then dampedWeight x j (partPrimes P m) else 0 := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (mem_Icc.1 hm).1; omega
    have hfac : dampedWeight x j m =
        dampedWeight x j (stripPrimes P m) * dampedWeight x j (partPrimes P m) := by
      rw [dampedWeight_eq_cmul x j hm0, dampedWeight_eq_cmul x j (stripPrimes_ne_zero P m),
        dampedWeight_eq_cmul x j (partPrimes_ne_zero P m), ← map_mul,
        stripPrimes_mul_partPrimes P hm0]
    rw [hfac]
    have hpart0 := dampedWeight_nonneg x j (partPrimes P m)
    split_ifs with hR
    · exact mul_le_of_le_one_left hpart0 (dampedWeight_le_one x hj _)
    · simp only [hRdef, not_forall, not_lt] at hR
      obtain ⟨p, hp, hpY⟩ := hR
      rw [primeFactors_stripPrimes, mem_filter] at hp
      rw [dampedWeight_eq_cmul x j (stripPrimes_ne_zero P m),
        cmul_eq_zero (p := p) (by rw [primeFactors_stripPrimes, mem_filter]; exact hp)
          (proxyLoc_of_le hpY hp.2), zero_mul]
  -- group by the candidate part `a = m_P`
  have hmaps : ∀ m ∈ Icc 1 W, partPrimes P m ∈ Icc 1 W := by
    intro m hm
    obtain ⟨h1, hmW⟩ := mem_Icc.1 hm
    have hm0 : m ≠ 0 := by omega
    exact mem_Icc.2 ⟨Nat.pos_of_ne_zero (partPrimes_ne_zero P m),
      (partPrimes_le P hm0).trans hmW⟩
  have hfiber : ∀ a ∈ Icc 1 W, ∑ m ∈ (Icc 1 W).filter (partPrimes P · = a),
      (if R (stripPrimes P m) then dampedWeight x j (partPrimes P m) else 0) ≤
        (if a.primeFactors ⊆ P then dampedWeight x j a else 0) *
          (A * W / (a * Real.log Y) + 1) := by
    intro a ha
    have ha1 : 1 ≤ a := (mem_Icc.1 ha).1
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
    have hga := dampedWeight_nonneg x j a
    by_cases haP : a.primeFactors ⊆ P
    · simp only [haP, ite_true]
      set F := (Icc 1 W).filter (partPrimes P · = a) with hF
      have hsum : ∑ m ∈ F,
          (if R (stripPrimes P m) then dampedWeight x j (partPrimes P m) else 0) =
          dampedWeight x j a * (F.filter fun m => R (stripPrimes P m)).card := by
        rw [sum_congr rfl fun m hm => by rw [(mem_filter.1 hm).2], sum_ite, sum_const_zero,
          add_zero, sum_const, nsmul_eq_mul, mul_comm]
      rw [hsum]
      refine mul_le_mul_of_nonneg_left ?_ hga
      -- `m ↦ m̄` injects the fiber into the rough numbers up to `W / a`
      have hcard : (F.filter fun m => R (stripPrimes P m)).card ≤ roughCount Y (W / a) := by
        unfold roughCount
        refine card_le_card_of_injOn (stripPrimes P) (fun m hm => ?_) ?_
        · rw [mem_coe, mem_filter, hF, mem_filter, mem_Icc] at hm
          obtain ⟨⟨⟨h1, hmW⟩, hpa⟩, hR⟩ := hm
          have hm0 : m ≠ 0 := by omega
          have hmul := stripPrimes_mul_partPrimes P hm0
          rw [hpa] at hmul
          rw [mem_coe, mem_filter, mem_Icc]
          refine ⟨⟨Nat.pos_of_ne_zero (stripPrimes_ne_zero P m), ?_⟩, hR⟩
          rw [Nat.le_div_iff_mul_le (by omega), hmul]
          exact hmW
        · intro m hm m' hm' h
          rw [mem_coe, mem_filter, hF, mem_filter, mem_Icc] at hm hm'
          have e1 := stripPrimes_mul_partPrimes P (show m ≠ 0 by omega)
          have e2 := stripPrimes_mul_partPrimes P (show m' ≠ 0 by omega)
          rw [hm.1.2] at e1
          rw [hm'.1.2] at e2
          rw [← e1, ← e2, h]
      have hW : ((W / a : ℕ) : ℝ) ≤ W / a := Nat.cast_div_le
      calc ((F.filter fun m => R (stripPrimes P m)).card : ℝ) ≤ roughCount Y (W / a) := by
            exact_mod_cast hcard
        _ ≤ A * ((W / a : ℕ) : ℝ) / Real.log Y + 1 := hrough Y hY2 hC₁ _
        _ ≤ A * (W / a) / Real.log Y + 1 := by gcongr
        _ = A * W / (a * Real.log Y) + 1 := by field_simp
    · simp only [haP, ite_false, zero_mul]
      refine le_of_eq (sum_eq_zero fun m hm => ?_)
      exfalso
      apply haP
      rw [← (mem_filter.1 hm).2, primeFactors_partPrimes]
      exact fun p hp => (mem_filter.1 hp).2
  -- the two Euler products over `P`
  set Ploc : ℕ → ℝ := fun p => if p ∈ P then (j : ℝ)⁻¹ / p else 0 with hPloc
  set Qloc : ℕ → ℝ := fun p => if p ∈ P then (p : ℝ) ^ (-θ) else 0 with hQloc
  have hp2 : ∀ p ∈ P, (2 : ℝ) ≤ p := fun p hp => by exact_mod_cast (hPp p hp).two_le
  have hEulerP : ∑ a ∈ Icc 1 W, cmul Ploc a ≤ ∏ p ∈ P, (1 - (j : ℝ)⁻¹ / p)⁻¹ := by
    refine (sum_cmul_le_prod (fun p _ => ?_) (fun p _ => ?_) W).trans
      (prod_primes_ite_le P _ (fun p hp => by positivity) (fun p hp => ?_) W)
    · simp only [hPloc]; split_ifs <;> positivity
    · simp only [hPloc]; split_ifs with h
      · rw [div_lt_one (by linarith [hp2 p h])]; linarith [hp2 p h]
      · norm_num
    · rw [div_lt_one (by linarith [hp2 p hp])]; linarith [hp2 p hp]
  have hrpow : ∀ p ∈ P, (p : ℝ) ^ (-θ) < 1 := fun p hp =>
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith [hp2 p hp]) (by linarith)
  have hEulerQ : ∑ a ∈ Icc 1 W, cmul Qloc a ≤ ∏ p ∈ P, (1 - (p : ℝ) ^ (-θ))⁻¹ := by
    refine (sum_cmul_le_prod (fun p _ => ?_) (fun p _ => ?_) W).trans
      (prod_primes_ite_le P _ (fun p hp => by positivity) hrpow W)
    · simp only [hQloc]; split_ifs <;> positivity
    · simp only [hQloc]; split_ifs with h
      · exact hrpow p h
      · norm_num
  have hfirst : ∀ a ∈ Icc 1 W, (if a.primeFactors ⊆ P then dampedWeight x j a else 0) / a ≤
      cmul Ploc a := by
    intro a ha
    have ha0 : a ≠ 0 := by have := (mem_Icc.1 ha).1; omega
    split_ifs with haP
    · rw [dampedWeight_eq_cmul x j ha0, cmul_div ha0]
      refine le_of_eq (cmul_congr fun p hp => ?_)
      simp [hPloc, haP hp, proxyLoc_of_candidate (haP hp)]
    · rw [zero_div]
      exact cmul_nonneg (fun p _ => by simp only [hPloc]; split_ifs <;> positivity) a
  have hsecond : ∀ a ∈ Icc 1 W, (if a.primeFactors ⊆ P then dampedWeight x j a else 0) ≤
      (W : ℝ) ^ θ * cmul Qloc a := by
    intro a ha
    obtain ⟨ha1, haW⟩ := mem_Icc.1 ha
    have ha0 : a ≠ 0 := by omega
    have hcQ := cmul_nonneg (loc := Qloc) (fun p _ => by
      simp only [hQloc]; split_ifs <;> positivity) a
    split_ifs with haP
    · have hQ : cmul Qloc a = (a : ℝ) ^ (-θ) := by
        rw [← cmul_rpow (-θ) ha0]
        exact cmul_congr fun p hp => by simp [hQloc, haP hp]
      rw [hQ]
      have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha1
      have : (1 : ℝ) ≤ (W : ℝ) ^ θ * (a : ℝ) ^ (-θ) := by
        rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
        exact Real.rpow_le_rpow (by linarith) (by exact_mod_cast haW) hθ.le
      linarith [dampedWeight_le_one x hj a]
    · positivity
  calc ∑ m ∈ Icc 1 W, dampedWeight x j m
      ≤ ∑ m ∈ Icc 1 W, (if R (stripPrimes P m) then dampedWeight x j (partPrimes P m) else 0) :=
        sum_le_sum hsplit
    _ = ∑ a ∈ Icc 1 W, ∑ m ∈ (Icc 1 W).filter (partPrimes P · = a),
          (if R (stripPrimes P m) then dampedWeight x j (partPrimes P m) else 0) :=
        (sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ a ∈ Icc 1 W, (if a.primeFactors ⊆ P then dampedWeight x j a else 0) *
          (A * W / (a * Real.log Y) + 1) := sum_le_sum hfiber
    _ = A * W / Real.log Y *
            ∑ a ∈ Icc 1 W, (if a.primeFactors ⊆ P then dampedWeight x j a else 0) / a +
          ∑ a ∈ Icc 1 W, (if a.primeFactors ⊆ P then dampedWeight x j a else 0) := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun a ha => ?_
        have : (0 : ℝ) < a := by have := (mem_Icc.1 ha).1; exact_mod_cast this
        field_simp
    _ ≤ A * W / Real.log Y * ∑ a ∈ Icc 1 W, cmul Ploc a +
          ∑ a ∈ Icc 1 W, (W : ℝ) ^ θ * cmul Qloc a := by
        gcongr with a ha a ha
        · exact hfirst a ha
        · exact hsecond a ha
    _ ≤ _ := by
        rw [← mul_sum]
        gcongr

end Erdos408.TypeII
