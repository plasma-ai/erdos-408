import Erdos408.OneSided.Analysis.Divisor
import Erdos408.OneSided.Setup
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# A small prime factor and sparse frequencies

PD Lemma 5.3 (`blueprint/one_sided_type_ii.md` §6.2), with the kernel premise (G) in place
of PD (5.13)–(5.14). Let `PS` be a set of primes in `[P, 2P)`, with `P` between
`exp(L^{a₋})` and `exp(2 L^{a₊})`. Put `P_s(t) = P⁻¹ ∑_{p ∈ PS} χ(p) p^{i(t + ξ)}` and
`N_β(t) = H_n⁻¹ ∑_n β_n ψ(n) n^{it}`. The unit intervals `[k, k + 1]` meeting
`{|t| ≤ 2 X L^B : |P_s(t)| > L^{-A_s}}` form a sparse family `𝓘`, and:

* `card_sparseSet_le`: `|𝓘| ≤ exp(C₀ L^{0.91})`. Raise `P_s` to the power
  `j = ⌊log(4XL^B)/log(2P)⌋`; its coefficients have `∑|c_n|² ≤ j^j 3^j P^{-j}` (every
  entry of a `j`-tuple of primes with product `n` is one of the `j` primes of a fixed such
  tuple, and `|PS| ≤ 3P`). Then apply the well-spaced mean value to exceeding points in the
  two classes of intervals of each parity, which are `1`-separated.
* `sum_norm_sq_le_of_sparse`: `∑_{k ∈ 𝓘} |N_β(t_k)|² ≤ C₀ L^{2C + 1}` for any points
  `t_k ∈ [k, k + 1]`. By the `TT*` bound it suffices to bound the absolute row sums of the
  Gram matrix of `n ↦ n^{i t_k}` on `[H_n, 2H_n]`. Its entries are at most `H_n + 1`, which
  is used for `|k - k'| ≤ 1`. Otherwise `1 ≤ |Δ| ≤ 4 X L^B + 2`, and by (G) they are at most
  `c_G H_n (|Δ|^{-1} + exp(-L^{0.95}))` with `|Δ|^{-1} ≤ 2 |k - k'|^{-1}`. The row sums are
  `O(H_n L)`, and `‖β‖² ≤ (H_n + 1) L^{2C}`.

Both bounds are uniform in `ξ`, the characters, and the prime set.
-/

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

/-- The prime polynomial `P_s(t) = P⁻¹ ∑_{p ∈ PS} χ(p) p^{i(t + ξ)}`. -/
noncomputable def primePoly (P : ℝ) (PS : Finset ℕ) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (ξ t : ℝ) : ℂ :=
  (P : ℂ)⁻¹ * ∑ p ∈ PS, χ p * (p : ℂ) ^ (((t + ξ : ℝ) : ℂ) * Complex.I)

/-- The unmarked polynomial `N_β(t) = H_n⁻¹ ∑_n β_n ψ(n) n^{it}`. -/
noncomputable def unmarkedPoly (d : Data K) {k : ℕ} (ψ : DirichletCharacter ℂ k) (t : ℝ) : ℂ :=
  (d.Hn : ℂ)⁻¹ * ∑ n ∈ d.nRange, d.β n * ψ n * (n : ℂ) ^ ((t : ℂ) * Complex.I)

open scoped Classical in
/-- The sparse family: integers `k` such that `[k, k + 1]` meets
`{|t| ≤ Z : |P_s(t)| > L^{-A_s}}`. -/
noncomputable def sparseSet (x Z As P : ℝ) (PS : Finset ℕ) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (ξ : ℝ) : Finset ℤ :=
  (Icc (-⌈Z⌉ - 1) ⌈Z⌉).filter fun m =>
    ∃ t : ℝ, (m : ℝ) ≤ t ∧ t ≤ m + 1 ∧ |t| ≤ Z ∧
      Real.log x ^ (-As) < ‖primePoly P PS χ ξ t‖

/-! ### Growth comparisons -/

/-- `c L^a (1 + log L) ≤ L^b` eventually, for `a < b`. -/
private theorem eventually_mul_rpow_mul_one_add_log_le {a b : ℝ} (hab : a < b) (c : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      c * Real.log x ^ a * (1 + Real.log (Real.log x)) ≤ Real.log x ^ b := by
  set ε := (b - a) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hLε := (tendsto_rpow_atTop hε0).comp Real.tendsto_log_atTop
  filter_upwards [hLε.eventually_ge_atTop (|c| * (1 + ε⁻¹)),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hL
  have hx' : |c| * (1 + ε⁻¹) ≤ Real.log x ^ ε := hx
  have hL0 : 0 < Real.log x := by linarith
  have h1 : 1 ≤ Real.log x ^ ε := Real.one_le_rpow hL hε0.le
  have hlog : Real.log (Real.log x) ≤ Real.log x ^ ε / ε := Real.log_le_rpow_div hL0.le hε0
  have hlog0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL
  have hLa : 0 ≤ Real.log x ^ a := by positivity
  -- `1 + log L ≤ (1 + 1/ε) L^ε`
  have h2 : 1 + Real.log (Real.log x) ≤ (1 + ε⁻¹) * Real.log x ^ ε := by
    rw [div_eq_mul_inv] at hlog
    nlinarith
  calc c * Real.log x ^ a * (1 + Real.log (Real.log x))
      ≤ |c| * Real.log x ^ a * ((1 + ε⁻¹) * Real.log x ^ ε) := by
        gcongr
        exact le_abs_self c
    _ = |c| * (1 + ε⁻¹) * Real.log x ^ a * Real.log x ^ ε := by ring
    _ ≤ Real.log x ^ ε * Real.log x ^ a * Real.log x ^ ε := by gcongr
    _ = Real.log x ^ b := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, hε]
        ring_nf

/-! ### Unimodular phases -/

/-- `|n^{it}| = 1` for `n ≥ 1`. -/
private theorem norm_natCast_cpow_ofReal_mul_I {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖(n : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  simp

/-- `n^{ia} \overline{n^{ib}} = n^{i(a - b)}` for `n ≠ 0`. -/
private theorem natCast_cpow_mul_I_mul_conj_cpow {n : ℕ} (hn : n ≠ 0) (a b : ℝ) :
    (n : ℂ) ^ ((a : ℂ) * Complex.I) * starRingEnd ℂ ((n : ℂ) ^ ((b : ℂ) * Complex.I)) =
      (n : ℂ) ^ (((a - b : ℝ) : ℂ) * Complex.I) := by
  rw [natCast_cpow_mul_I hn, natCast_cpow_mul_I hn, natCast_cpow_mul_I hn, ← Complex.exp_conj,
    ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `(∏ f_i)^s = ∏ f_i^s` for natural numbers `f_i`. -/
private theorem natCast_prod_cpow {ι : Type*} (s : Finset ι) (f : ι → ℕ) (z : ℂ) :
    ((∏ i ∈ s, f i : ℕ) : ℂ) ^ z = ∏ i ∈ s, (f i : ℂ) ^ z := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [prod_cons, prod_cons, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih]

/-! ### Powers of the prime polynomial -/

/-- At most `j^j` ordered `j`-tuples of primes have a given product: every entry is one of the
`j` primes of a fixed such tuple. -/
private theorem card_filter_prod_eq_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (j n : ℕ) :
    #{q ∈ Fintype.piFinset (fun _ : Fin j => S) | ∏ i, q i = n} ≤ j ^ j := by
  rcases (filter (fun q : Fin j → ℕ => ∏ i, q i = n)
    (Fintype.piFinset fun _ : Fin j => S)).eq_empty_or_nonempty with h | ⟨q₀, hq₀⟩
  · rw [h, card_empty]
    exact Nat.zero_le _
  rw [mem_filter, Fintype.mem_piFinset] at hq₀
  calc #{q ∈ Fintype.piFinset (fun _ : Fin j => S) | ∏ i, q i = n}
      ≤ #(Fintype.piFinset fun _ : Fin j => univ.image q₀) := by
        refine card_le_card fun q hq => ?_
        rw [mem_filter, Fintype.mem_piFinset] at hq
        rw [Fintype.mem_piFinset]
        intro i
        -- `q i` is a prime dividing `∏ q₀ = n`
        have hp := hS _ (hq.1 i)
        have hdvd : q i ∣ ∏ k, q₀ k := hq₀.2 ▸ hq.2 ▸ dvd_prod_of_mem q (mem_univ i)
        obtain ⟨k, -, hk⟩ := (hp.prime.dvd_finsetProd_iff q₀).1 hdvd
        rw [(Nat.prime_dvd_prime_iff_eq hp (hS _ (hq₀.1 k))).1 hk]
        exact mem_image_of_mem q₀ (mem_univ k)
    _ = #(univ.image q₀) ^ j := by
        rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
    _ ≤ j ^ j := Nat.pow_le_pow_left (card_image_le.trans (by simp)) j

/-- The coefficients of `P_s(t)^j = ∑_n c_n n^{it}`:
`c_n = P^{-j} ∑_{p₁ ⋯ p_j = n} ∏_i χ(p_i) p_i^{iξ}`. -/
noncomputable def primePowCoeff (P : ℝ) (PS : Finset ℕ) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (ξ : ℝ) (j n : ℕ) : ℂ :=
  (P : ℂ)⁻¹ ^ j * ∑ q ∈ Fintype.piFinset (fun _ : Fin j => PS) with ∏ i, q i = n,
    ∏ i, χ (q i) * (q i : ℂ) ^ ((ξ : ℂ) * Complex.I)

/-- `P_s(t)^j = ∑_{n ≤ N} c_n n^{it}`, when every product of `j` primes of `PS` is in
`[1, N]`. The shift `p^{iξ}` goes into the coefficients. -/
theorem primePoly_pow_eq {P : ℝ} {PS : Finset ℕ} {k : ℕ} (χ : DirichletCharacter ℂ k)
    (ξ t : ℝ) {j N : ℕ} (hPS : ∀ p ∈ PS, p ≠ 0)
    (hN : ∀ q ∈ Fintype.piFinset (fun _ : Fin j => PS), ∏ i, q i ∈ Icc 1 N) :
    primePoly P PS χ ξ t ^ j =
      ∑ n ∈ Icc 1 N, primePowCoeff P PS χ ξ j n * (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
  -- each term of the power splits as the coefficient times `(∏ q_i)^{it}`
  have hterm : ∀ q ∈ Fintype.piFinset (fun _ : Fin j => PS),
      ∏ i, χ (q i) * (q i : ℂ) ^ (((t + ξ : ℝ) : ℂ) * Complex.I) =
        (∏ i, χ (q i) * (q i : ℂ) ^ ((ξ : ℂ) * Complex.I)) *
          ((∏ i, q i : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I) := by
    intro q hq
    rw [Fintype.mem_piFinset] at hq
    rw [natCast_prod_cpow, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [show ((t + ξ : ℝ) : ℂ) * Complex.I = (ξ : ℂ) * Complex.I + (t : ℂ) * Complex.I by
      push_cast; ring, Complex.cpow_add _ _ (Nat.cast_ne_zero.2 (hPS _ (hq i)))]
    ring
  unfold primePoly primePowCoeff
  rw [mul_pow, sum_pow', sum_congr rfl hterm, mul_sum,
    ← sum_fiberwise_of_maps_to hN]
  refine sum_congr rfl fun n _ => ?_
  rw [mul_assoc, sum_mul, mul_sum]
  refine sum_congr rfl fun q hq => ?_
  rw [(mem_filter.1 hq).2]

/-- `∑ |c_n|² ≤ j^j |PS|^j P^{-2j}`: each `|c_n|` is at most `P^{-j}` times the number of
tuples with product `n`, which is at most `j^j`. -/
theorem sum_norm_primePowCoeff_sq_le {P : ℝ} {PS : Finset ℕ} {k : ℕ}
    (χ : DirichletCharacter ℂ k) (ξ : ℝ) {j N : ℕ} (hP : 0 < P) (hPS : ∀ p ∈ PS, p.Prime)
    (hN : ∀ q ∈ Fintype.piFinset (fun _ : Fin j => PS), ∏ i, q i ∈ Icc 1 N) :
    ∑ n ∈ Icc 1 N, ‖primePowCoeff P PS χ ξ j n‖ ^ 2 ≤
      (j : ℝ) ^ j * (#PS : ℝ) ^ j / P ^ (2 * j) := by
  set F : ℕ → Finset (Fin j → ℕ) := fun n =>
    {q ∈ Fintype.piFinset (fun _ : Fin j => PS) | ∏ i, q i = n}
  -- `|c_n| ≤ P^{-j} |F_n|`
  have hc : ∀ n, ‖primePowCoeff P PS χ ξ j n‖ ≤ #(F n) / P ^ j := by
    intro n
    unfold primePowCoeff
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hP.le,
      inv_pow, div_eq_inv_mul]
    gcongr
    refine (norm_sum_le _ _).trans ?_
    rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine sum_le_sum fun q hq => ?_
    rw [mem_filter, Fintype.mem_piFinset] at hq
    rw [norm_prod]
    refine prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    rw [norm_mul, norm_natCast_cpow_ofReal_mul_I (hPS _ (hq.1 i)).pos, mul_one]
    exact DirichletCharacter.norm_le_one χ _
  have hcard : ∑ n ∈ Icc 1 N, (#(F n) : ℝ) = (#PS : ℝ) ^ j := by
    rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise hN, Fintype.card_piFinset, prod_const,
      card_univ, Fintype.card_fin, Nat.cast_pow]
  calc ∑ n ∈ Icc 1 N, ‖primePowCoeff P PS χ ξ j n‖ ^ 2
      ≤ ∑ n ∈ Icc 1 N, (j : ℝ) ^ j * #(F n) / P ^ (2 * j) := by
        refine sum_le_sum fun n _ => ?_
        have hF : (#(F n) : ℝ) ≤ (j : ℝ) ^ j := by exact_mod_cast card_filter_prod_eq_le hPS j n
        calc ‖primePowCoeff P PS χ ξ j n‖ ^ 2 ≤ (#(F n) / P ^ j) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (hc n) 2
          _ = #(F n) * #(F n) / P ^ (2 * j) := by rw [div_pow, ← pow_mul, mul_comm j]; ring
          _ ≤ (j : ℝ) ^ j * #(F n) / P ^ (2 * j) := by gcongr
    _ = (j : ℝ) ^ j * (#PS : ℝ) ^ j / P ^ (2 * j) := by
        rw [← sum_div, ← mul_sum, hcard]

/-! ### Counting the sparse family -/

/-- The exceeding points of one separated class: if `|P_s(t)| > η` at points of `[-Z, Z]`
with mutual spacing at least one, and `(2P)^j ≤ 2Z`, then
`|T| η^{2j} ≤ 2 (2Z + 1 + 16Z(1 + log 2Z)) (1 + log 2Z)² j^j 3^j P^{-j}`. -/
theorem card_mul_pow_le_of_separated {P Z η : ℝ} {PS : Finset ℕ} {k : ℕ}
    (χ : DirichletCharacter ℂ k) (ξ : ℝ) {j : ℕ} (hP : 1 ≤ P)
    (hPS : ∀ p ∈ PS, p.Prime ∧ (p : ℝ) < 2 * P) (hj : (2 * P) ^ j ≤ 2 * Z) (hη : 0 ≤ η)
    (T : Finset ℝ) (hT : ∀ t ∈ T, |t| ≤ Z) (hsep : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → 1 ≤ |t - s|)
    (hTη : ∀ t ∈ T, η < ‖primePoly P PS χ ξ t‖) :
    #T * η ^ (2 * j) ≤ 2 * (2 * Z + 1 + 16 * Z * (1 + Real.log (2 * Z))) *
      (1 + Real.log (2 * Z)) ^ 2 * ((j : ℝ) ^ j * 3 ^ j / P ^ j) := by
  set N := ⌊(2 * P) ^ j⌋₊
  have h2P : 1 ≤ 2 * P := by linarith
  have hN1 : 1 ≤ N := (Nat.one_le_floor_iff _).2 (one_le_pow₀ h2P)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNZ : (N : ℝ) ≤ 2 * Z := (Nat.floor_le (by positivity)).trans hj
  have hlogN : Real.log N ≤ Real.log (2 * Z) := Real.log_le_log hNpos hNZ
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hZ : 0 ≤ Z := by linarith
  -- every product of `j` primes of `PS` is in `[1, N]`
  have hmaps : ∀ q ∈ Fintype.piFinset (fun _ : Fin j => PS), ∏ i, q i ∈ Icc 1 N := by
    intro q hq
    rw [Fintype.mem_piFinset] at hq
    rw [mem_Icc]
    refine ⟨Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2 fun i _ => (hPS _ (hq i)).1.ne_zero),
      Nat.le_floor ?_⟩
    rw [Nat.cast_prod]
    calc ∏ i, ((q i : ℕ) : ℝ) ≤ ∏ _i : Fin j, 2 * P :=
          prod_le_prod₀ (fun i _ => by positivity) fun i _ => (hPS _ (hq i)).2.le
      _ = (2 * P) ^ j := by rw [prod_const, card_univ, Fintype.card_fin]
  -- `|PS| ≤ 3P`, so `∑ |c_n|² ≤ j^j 3^j P^{-j}`
  have hcardPS : (#PS : ℝ) ≤ 3 * P := by
    have hsub : PS ⊆ range ⌈2 * P⌉₊ := fun p hp => mem_range.2 (Nat.lt_ceil.2 (hPS p hp).2)
    have h₁ := Nat.ceil_lt_add_one (show 0 ≤ 2 * P by linarith)
    have h₂ : (#PS : ℝ) ≤ ⌈2 * P⌉₊ := by
      exact_mod_cast (card_le_card hsub).trans (card_range _).le
    linarith
  have hcoef : ∑ n ∈ Icc 1 N, ‖primePowCoeff P PS χ ξ j n‖ ^ 2 ≤
      (j : ℝ) ^ j * 3 ^ j / P ^ j := by
    refine (sum_norm_primePowCoeff_sq_le χ ξ (by linarith) (fun p hp => (hPS p hp).1)
      hmaps).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc (j : ℝ) ^ j * (#PS : ℝ) ^ j * P ^ j ≤ (j : ℝ) ^ j * (3 * P) ^ j * P ^ j := by gcongr
      _ = (j : ℝ) ^ j * 3 ^ j * P ^ (2 * j) := by ring
  -- each point contributes at least `η^{2j}`
  have hpt : ∀ t ∈ T, η ^ (2 * j) ≤
      ‖∑ n ∈ Icc 1 N, primePowCoeff P PS χ ξ j n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 := by
    intro t ht
    rw [← primePoly_pow_eq χ ξ t (fun p hp => (hPS p hp).1.ne_zero) hmaps, norm_pow,
      ← pow_mul, mul_comm j]
    exact pow_le_pow_left₀ hη (hTη t ht).le _
  calc #T * η ^ (2 * j) = ∑ t ∈ T, η ^ (2 * j) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ t ∈ T,
        ‖∑ n ∈ Icc 1 N, primePowCoeff P PS χ ξ j n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 :=
        sum_le_sum hpt
    _ ≤ 2 * (Z - -Z + 1 + 8 * N * (1 + Real.log N)) * (1 + Real.log N) ^ 2 *
        ∑ n ∈ Icc 1 N, ‖primePowCoeff P PS χ ξ j n‖ ^ 2 :=
        sum_norm_dirichlet_sq_le N _ (neg_le_self hZ) T (fun t ht => abs_le.1 (hT t ht)) hsep
    _ ≤ _ := by
        have hlog2Z : 0 ≤ Real.log (2 * Z) := hlogN0.trans hlogN
        have h₁ : Z - -Z + 1 + 8 * N * (1 + Real.log N) ≤
            2 * Z + 1 + 16 * Z * (1 + Real.log (2 * Z)) := by nlinarith
        have h₂ : (1 + Real.log N) ^ 2 ≤ (1 + Real.log (2 * Z)) ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h₁ two_pos.le) h₂
          (by positivity) (by nlinarith)) hcoef (sum_nonneg fun n _ => by positivity)
          (mul_nonneg (mul_nonneg two_pos.le (by nlinarith [mul_nonneg hZ hlog2Z]))
            (sq_nonneg _))

/-- Points `t ∈ [m, m + 1]` and `t' ∈ [m', m' + 1]` at distinct integers of the same parity
are at least `1` apart. -/
private theorem one_le_abs_sub_of_emod_two_eq {m m' : ℤ} (hmm' : m ≠ m') (hpar : m % 2 = m' % 2)
    {t t' : ℝ} (ht : (m : ℝ) ≤ t ∧ t ≤ m + 1) (ht' : (m' : ℝ) ≤ t' ∧ t' ≤ m' + 1) :
    1 ≤ |t - t'| := by
  rcases lt_or_gt_of_ne hmm' with h | h
  · have h₂ : (m : ℝ) + 2 ≤ m' := by exact_mod_cast (show m + 2 ≤ m' by omega)
    rw [abs_sub_comm]
    exact le_abs.2 (Or.inl (by linarith))
  · have h₂ : (m' : ℝ) + 2 ≤ m := by exact_mod_cast (show m' + 2 ≤ m by omega)
    exact le_abs.2 (Or.inl (by linarith))

/-- The sparse family, split by parity into two `1`-separated classes of exceeding points:
`|𝓘| L^{-2 A_s j} ≤ 4 (2Z + 1 + 16Z(1 + log 2Z)) (1 + log 2Z)² j^j 3^j P^{-j}`. -/
theorem card_sparseSet_mul_pow_le {x Z As P : ℝ} {PS : Finset ℕ} {k : ℕ}
    (χ : DirichletCharacter ℂ k) (ξ : ℝ) {j : ℕ} (hx : 0 ≤ Real.log x) (hP : 1 ≤ P)
    (hPS : ∀ p ∈ PS, p.Prime ∧ (p : ℝ) < 2 * P) (hj : (2 * P) ^ j ≤ 2 * Z) :
    #(sparseSet x Z As P PS χ ξ) * (Real.log x ^ (-As)) ^ (2 * j) ≤
      2 * (2 * (2 * Z + 1 + 16 * Z * (1 + Real.log (2 * Z))) *
        (1 + Real.log (2 * Z)) ^ 2 * ((j : ℝ) ^ j * 3 ^ j / P ^ j)) := by
  set S := sparseSet x Z As P PS χ ξ
  -- choose an exceeding point `t_m ∈ [m, m + 1]` for each `m ∈ 𝓘`
  have hex : ∀ m : ℤ, ∃ t : ℝ, m ∈ S → (m : ℝ) ≤ t ∧ t ≤ m + 1 ∧ |t| ≤ Z ∧
      Real.log x ^ (-As) < ‖primePoly P PS χ ξ t‖ := by
    intro m
    by_cases hm : m ∈ S
    · simp only [S, sparseSet, mem_filter] at hm
      obtain ⟨t, ht⟩ := hm.2
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose t ht using hex
  -- each parity class is `1`-separated
  have hclass : ∀ C ⊆ S, (∀ m ∈ C, ∀ m' ∈ C, m % 2 = m' % 2) →
      #C * (Real.log x ^ (-As)) ^ (2 * j) ≤
        2 * (2 * Z + 1 + 16 * Z * (1 + Real.log (2 * Z))) *
          (1 + Real.log (2 * Z)) ^ 2 * ((j : ℝ) ^ j * 3 ^ j / P ^ j) := by
    intro C hC hpar
    have hsep : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' → 1 ≤ |t m - t m'| := fun m hm m' hm' hne =>
      one_le_abs_sub_of_emod_two_eq hne (hpar m hm m' hm') ⟨(ht m (hC hm)).1,
        (ht m (hC hm)).2.1⟩ ⟨(ht m' (hC hm')).1, (ht m' (hC hm')).2.1⟩
    have hinj : Set.InjOn t C := by
      intro m hm m' hm' h
      by_contra hne
      have := hsep m hm m' hm' hne
      rw [h, sub_self, abs_zero] at this
      linarith
    rw [← card_image_of_injOn hinj]
    refine card_mul_pow_le_of_separated χ ξ hP hPS hj (Real.rpow_nonneg hx _) _ ?_ ?_ ?_
    · intro s hs
      obtain ⟨m, hm, rfl⟩ := mem_image.1 hs
      exact (ht m (hC hm)).2.2.1
    · intro s hs s' hs' hne
      obtain ⟨m, hm, rfl⟩ := mem_image.1 hs
      obtain ⟨m', hm', rfl⟩ := mem_image.1 hs'
      exact hsep m hm m' hm' fun h => hne (h ▸ rfl)
    · intro s hs
      obtain ⟨m, hm, rfl⟩ := mem_image.1 hs
      exact (ht m (hC hm)).2.2.2
  have h₀ := hclass _ (filter_subset (fun m : ℤ => m % 2 = 0) S) fun m hm m' hm' => by
    rw [(mem_filter.1 hm).2, (mem_filter.1 hm').2]
  have h₁ := hclass _ (filter_subset (fun m : ℤ => ¬m % 2 = 0) S) fun m hm m' hm' => by
    have := (mem_filter.1 hm).2
    have := (mem_filter.1 hm').2
    omega
  rw [← card_filter_add_card_filter_not (s := S) (fun m : ℤ => m % 2 = 0), Nat.cast_add,
    add_mul]
  linarith

/-- `1 ≤ 2Z` and `log 2Z ≤ 2L` for `Z = 2XL^B`, once `log(4M) + |B| log L ≤ L` with
`M = max(C_X, 1)`. -/
theorem one_le_two_mul_and_log_le_of_admissible {C CX alo ahi g B x : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d) (hx : 0 < x) (hL : 1 ≤ Real.log x)
    (hE : (Real.log (4 * max CX 1) + |B|) * (1 + Real.log (Real.log x)) ≤ Real.log x) :
    1 ≤ 2 * (2 * d.X * Real.log x ^ B) ∧
      Real.log (2 * (2 * d.X * Real.log x ^ B)) ≤ 2 * Real.log x := by
  set L := Real.log x
  set M := max CX 1
  have hL0 : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  -- `x / M ≤ X ≤ M x`
  have hHm : 0 < d.Hm := (Real.rpow_pos_of_pos hx _).trans_le hd.Hm_ge
  have hHn : 0 < d.Hn := (Real.rpow_pos_of_pos hx _).trans_le hd.Hn_ge
  have hX : 0 < d.X := mul_pos hHm hHn
  have hCX : 0 < CX := by
    by_contra h
    have := hd.X_le
    nlinarith [mul_pos hHm hHn]
  have hM1 : 1 ≤ M := le_max_right _ _
  have hCXM : CX ≤ M := le_max_left _ _
  have hXup : d.X ≤ M * x := hd.X_le.trans (by gcongr)
  have hXlo : x / M ≤ d.X := (div_le_div_of_nonneg_left hx.le hCX hCXM).trans hd.X_ge
  -- `4 M L^{|B|} ≤ x`
  have hlog4M : 0 ≤ Real.log (4 * M) := Real.log_nonneg (by linarith)
  have hBL : Real.log (4 * M) + |B| * Real.log L ≤ L := by
    nlinarith [mul_nonneg hlog4M hlogL, abs_nonneg B]
  have h4ML : 4 * M * L ^ |B| ≤ x := by
    have h : 4 * M * L ^ |B| = Real.exp (Real.log (4 * M) + |B| * Real.log L) := by
      rw [Real.exp_add, Real.exp_log (by positivity), Real.rpow_def_of_pos hL0, mul_comm |B|]
    rw [h]
    calc Real.exp (Real.log (4 * M) + |B| * Real.log L) ≤ Real.exp L := Real.exp_le_exp.2 hBL
      _ = x := Real.exp_log hx
  have hLB : 0 < L ^ |B| := by positivity
  constructor
  · have hLB' : (L ^ |B|)⁻¹ ≤ L ^ B := by
      rw [← Real.rpow_neg hL0.le]
      exact Real.rpow_le_rpow_of_exponent_le hL (neg_abs_le B)
    have h₁ : 1 ≤ 4 * (x / M) * (L ^ |B|)⁻¹ := by
      rw [show 4 * (x / M) * (L ^ |B|)⁻¹ = 4 * x / (M * L ^ |B|) by field_simp,
        le_div_iff₀ (by positivity), one_mul]
      linarith
    calc (1 : ℝ) ≤ 4 * (x / M) * (L ^ |B|)⁻¹ := h₁
      _ ≤ 4 * d.X * L ^ B := by gcongr
      _ = 2 * (2 * d.X * L ^ B) := by ring
  · have h₁ : L ^ B ≤ L ^ |B| := Real.rpow_le_rpow_of_exponent_le hL (le_abs_self B)
    have h₂ : 2 * (2 * d.X * L ^ B) ≤ x * x :=
      calc 2 * (2 * d.X * L ^ B) = 4 * d.X * L ^ B := by ring
        _ ≤ 4 * (M * x) * L ^ |B| := by gcongr
        _ = (4 * M * L ^ |B|) * x := by ring
        _ ≤ x * x := by gcongr
    calc Real.log (2 * (2 * d.X * L ^ B)) ≤ Real.log (x * x) :=
          Real.log_le_log (by positivity) h₂
      _ = 2 * L := by rw [Real.log_mul hx.ne' hx.ne']; ring

/-- The degree `j = ⌊log 2Z / log 2P⌋`: `(2P)^j ≤ 2Z < (2P)^{j + 1}` (so `Z P^{-j} ≤ 2^j P`),
and `j ≤ 2 L^{1 - a₋}` when `log 2Z ≤ 2L` and `L^{a₋} ≤ log 2P`. -/
private theorem exists_pow_le_two_mul {L P Z alo : ℝ} (hL : 1 ≤ L) (hP : 1 ≤ P) (h2Z : 1 ≤ 2 * Z)
    (hlog2Z : Real.log (2 * Z) ≤ 2 * L) (hlog2P : L ^ alo ≤ Real.log (2 * P)) :
    ∃ j : ℕ, (2 * P) ^ j ≤ 2 * Z ∧ Z / P ^ j ≤ 2 ^ j * P ∧ (j : ℝ) ≤ 2 * L ^ (1 - alo) := by
  have hL0 : 0 < L := by linarith
  have hLalo : 0 < L ^ alo := by positivity
  have hlogP0 : 0 < Real.log (2 * P) := hLalo.trans_le hlog2P
  have hratio : 0 ≤ Real.log (2 * Z) / Real.log (2 * P) :=
    div_nonneg (Real.log_nonneg h2Z) hlogP0.le
  have hpow : ∀ r : ℕ, (2 * P) ^ r = Real.exp (r * Real.log (2 * P)) := fun r => by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  refine ⟨⌊Real.log (2 * Z) / Real.log (2 * P)⌋₊, ?_, ?_, ?_⟩
  · have h := (le_div_iff₀ hlogP0).1 (Nat.floor_le hratio)
    calc (2 * P) ^ ⌊Real.log (2 * Z) / Real.log (2 * P)⌋₊
        = Real.exp (⌊Real.log (2 * Z) / Real.log (2 * P)⌋₊ * Real.log (2 * P)) := hpow _
      _ ≤ Real.exp (Real.log (2 * Z)) := Real.exp_le_exp.2 h
      _ = 2 * Z := Real.exp_log (by linarith)
  · have h := (div_lt_iff₀ hlogP0).1 (Nat.lt_floor_add_one
      (Real.log (2 * Z) / Real.log (2 * P)))
    have h' : 2 * Z < (2 * P) ^ (⌊Real.log (2 * Z) / Real.log (2 * P)⌋₊ + 1) := by
      calc 2 * Z = Real.exp (Real.log (2 * Z)) := (Real.exp_log (by linarith)).symm
        _ < Real.exp ((⌊Real.log (2 * Z) / Real.log (2 * P)⌋₊ + 1 : ℕ) * Real.log (2 * P)) := by
          push_cast
          exact Real.exp_lt_exp.2 h
        _ = _ := (hpow _).symm
    rw [div_le_iff₀ (by positivity)]
    rw [pow_succ, mul_pow] at h'
    nlinarith
  · calc (⌊Real.log (2 * Z) / Real.log (2 * P)⌋₊ : ℝ)
        ≤ Real.log (2 * Z) / Real.log (2 * P) := Nat.floor_le hratio
      _ ≤ 2 * L / L ^ alo := div_le_div₀ (by positivity) hlog2Z hLalo hlog2P
      _ = 2 * L ^ (1 - alo) := by rw [Real.rpow_sub hL0, Real.rpow_one, mul_div_assoc]

/-- The count of `card_sparseSet_mul_pow_le`, simplified with `1 ≤ 2Z`, `Z P^{-j} ≤ 2^j P`,
`j ≤ 2L` and `y = 1 + log 2Z ≤ 3L`: `|𝓘| ≤ 2160 L³ P (12 L^{1 + 2|A_s|})^j`. -/
private theorem le_of_mul_rpow_neg_pow_le {L P Z y As c : ℝ} {j : ℕ} (hL : 1 ≤ L) (hP : 1 ≤ P)
    (h2Z : 1 ≤ 2 * Z) (hy1 : 1 ≤ y) (hy : y ≤ 3 * L) (hjL : (j : ℝ) ≤ 2 * L)
    (hj : Z / P ^ j ≤ 2 ^ j * P)
    (hc : c * (L ^ (-As)) ^ (2 * j) ≤
      2 * (2 * (2 * Z + 1 + 16 * Z * y) * y ^ 2 * ((j : ℝ) ^ j * 3 ^ j / P ^ j))) :
    c ≤ 2160 * L ^ 3 * P * (12 * L ^ (1 + 2 * |As|)) ^ j := by
  have hL0 : 0 < L := by linarith
  have hη : L ^ (-As) * L ^ As = 1 := by
    rw [← Real.rpow_add hL0, neg_add_cancel, Real.rpow_zero]
  have hbase : 2 * (3 * j * (L ^ As) ^ 2) ≤ 12 * L ^ (1 + 2 * |As|) := by
    have h₁ : (L ^ As) ^ 2 ≤ L ^ (2 * |As|) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      exact Real.rpow_le_rpow_of_exponent_le hL (by push_cast; linarith [le_abs_self As])
    rw [Real.rpow_add hL0, Real.rpow_one]
    calc 2 * (3 * j * (L ^ As) ^ 2) = 6 * j * (L ^ As) ^ 2 := by ring
      _ ≤ 6 * (2 * L) * L ^ (2 * |As|) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hjL (by norm_num)) h₁ (by positivity)
            (by positivity)
      _ = 12 * (L * L ^ (2 * |As|)) := by ring
  have h₁ : 2 * Z + 1 + 16 * Z * y ≤ 20 * Z * y := by nlinarith
  calc c = c * (L ^ (-As)) ^ (2 * j) * (L ^ As) ^ (2 * j) := by
        rw [mul_assoc, ← mul_pow, hη, one_pow, mul_one]
    _ ≤ 2 * (2 * (2 * Z + 1 + 16 * Z * y) * y ^ 2 * ((j : ℝ) ^ j * 3 ^ j / P ^ j)) *
        (L ^ As) ^ (2 * j) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 4 * (2 * Z + 1 + 16 * Z * y) *
        (y ^ 2 * ((j : ℝ) ^ j * 3 ^ j / P ^ j) * (L ^ As) ^ (2 * j)) := by ring
    _ ≤ 4 * (20 * Z * y) * (y ^ 2 * ((j : ℝ) ^ j * 3 ^ j / P ^ j) * (L ^ As) ^ (2 * j)) := by
        gcongr
    _ = 80 * y ^ 3 * (Z / P ^ j) * (3 * j * (L ^ As) ^ 2) ^ j := by ring
    _ ≤ 80 * (3 * L) ^ 3 * (2 ^ j * P) * (3 * j * (L ^ As) ^ 2) ^ j := by
        have hy3 : y ^ 3 ≤ (3 * L) ^ 3 := pow_le_pow_left₀ (by linarith) hy 3
        exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hy3
          (by norm_num)) hj (div_nonneg (by linarith) (by positivity)) (by positivity))
          (by positivity)
    _ = 2160 * L ^ 3 * P * (2 ^ j * (3 * j * (L ^ As) ^ 2) ^ j) := by ring
    _ = 2160 * L ^ 3 * P * (2 * (3 * j * (L ^ As) ^ 2)) ^ j := by
        rw [mul_pow (2 : ℝ) (3 * (j : ℝ) * (L ^ As) ^ 2) j]
    _ ≤ 2160 * L ^ 3 * P * (12 * L ^ (1 + 2 * |As|)) ^ j := by gcongr

/-- `2160 L³ P (12 L^{1 + 2|A_s|})^j ≤ exp(3 L^{0.91})`, given `P ≤ exp(2 L^{a₊})`,
`j ≤ 2 L^{1 - a₋}` and the three growth comparisons with `L^{0.91}`. -/
private theorem poly_mul_pow_le_exp {L P alo ahi As : ℝ} {j : ℕ} (hL : 1 ≤ L) (hP0 : 0 ≤ P)
    (hP : P ≤ Real.exp (2 * L ^ ahi)) (hj : (j : ℝ) ≤ 2 * L ^ (1 - alo))
    (hE1 : 2 * (12 + 2 * |As|) * L ^ (1 - alo) * (1 + Real.log L) ≤ L ^ (91 / 100 : ℝ))
    (hE2 : 2160 * (1 + Real.log L) ≤ L ^ (91 / 100 : ℝ))
    (hE3 : 2 * L ^ ahi * (1 + Real.log L) ≤ L ^ (91 / 100 : ℝ)) :
    2160 * L ^ 3 * P * (12 * L ^ (1 + 2 * |As|)) ^ j ≤
      Real.exp (3 * L ^ (91 / 100 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hf₁ : 2160 * L ^ 3 ≤ Real.exp (L ^ (91 / 100 : ℝ)) := by
    rw [← Real.exp_log (show 0 < 2160 * L ^ 3 by positivity), Real.log_mul (by norm_num)
      (by positivity), Real.log_pow]
    refine Real.exp_le_exp.2 ?_
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2160 by norm_num)
    push_cast
    nlinarith
  have hf₂ : P ≤ Real.exp (L ^ (91 / 100 : ℝ)) :=
    hP.trans (Real.exp_le_exp.2 (by nlinarith [Real.rpow_nonneg hL0.le ahi]))
  have hb : 1 ≤ 12 * L ^ (1 + 2 * |As|) := by
    have := Real.one_le_rpow hL (show 0 ≤ 1 + 2 * |As| by positivity)
    linarith
  have hf₃ : (12 * L ^ (1 + 2 * |As|)) ^ j ≤ Real.exp (L ^ (91 / 100 : ℝ)) := by
    have hlogb : Real.log (12 * L ^ (1 + 2 * |As|)) ≤ (12 + 2 * |As|) * (1 + Real.log L) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hL0]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 12 by norm_num)
      nlinarith [abs_nonneg As]
    rw [← Real.exp_log (show 0 < 12 * L ^ (1 + 2 * |As|) by linarith), ← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have hlogb0 : 0 ≤ Real.log (12 * L ^ (1 + 2 * |As|)) := Real.log_nonneg hb
    calc (j : ℝ) * Real.log (12 * L ^ (1 + 2 * |As|))
        ≤ 2 * L ^ (1 - alo) * ((12 + 2 * |As|) * (1 + Real.log L)) := by gcongr
      _ = 2 * (12 + 2 * |As|) * L ^ (1 - alo) * (1 + Real.log L) := by ring
      _ ≤ _ := hE1
  calc 2160 * L ^ 3 * P * (12 * L ^ (1 + 2 * |As|)) ^ j
      ≤ Real.exp (L ^ (91 / 100 : ℝ)) * Real.exp (L ^ (91 / 100 : ℝ)) *
        Real.exp (L ^ (91 / 100 : ℝ)) :=
        mul_le_mul (mul_le_mul hf₁ hf₂ hP0 (Real.exp_pos _).le) hf₃ (by positivity)
          (by positivity)
    _ = Real.exp (3 * L ^ (91 / 100 : ℝ)) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf

/-- PD (5.10), first half: the sparse family has at most `exp(C₀ L^{0.91})` members. -/
theorem card_sparseSet_le {C CX alo ahi g B As : ℝ} (halo : 1 / 10 < alo)
    (hahi : ahi < 1 / 5) :
    ∃ C₀ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ∀ P : ℝ, Real.exp (Real.log x ^ alo) ≤ P → P ≤ Real.exp (2 * Real.log x ^ ahi) →
      ∀ PS : Finset ℕ, (∀ p ∈ PS, p.Prime ∧ P ≤ p ∧ (p : ℝ) < 2 * P) →
      ∀ (k : ℕ) (χ : DirichletCharacter ℂ k) (ξ : ℝ),
        ((sparseSet x (2 * d.X * Real.log x ^ B) As P PS χ ξ).card : ℝ) ≤
          Real.exp (C₀ * Real.log x ^ (91 / 100 : ℝ)) := by
  refine ⟨3, ?_⟩
  filter_upwards [eventually_mul_rpow_mul_one_add_log_le (show 1 - alo < 91 / 100 by linarith)
      (2 * (12 + 2 * |As|)),
    eventually_mul_rpow_mul_one_add_log_le (show (0 : ℝ) < 91 / 100 by norm_num) 2160,
    eventually_mul_rpow_mul_one_add_log_le (show ahi < 91 / 100 by linarith) 2,
    eventually_mul_rpow_mul_one_add_log_le (show (0 : ℝ) < 1 by norm_num)
      (Real.log (4 * max CX 1) + |B|),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop 0]
    with x hE1 hE2 hE3 hE4 hL hx d hd P hP1 hP2 PS hPS k χ ξ
  rw [Real.rpow_zero, mul_one] at hE2 hE4
  rw [Real.rpow_one] at hE4
  obtain ⟨h2Z, hlog2Z⟩ := one_le_two_mul_and_log_le_of_admissible hd hx hL hE4
  -- `1 ≤ P` and `L^{a₋} ≤ log 2P`
  have hP1' : 1 ≤ P := le_trans (Real.one_le_exp (by positivity)) hP1
  have hlog2P : Real.log (Real.exp (Real.log x ^ alo)) ≤ Real.log (2 * P) :=
    Real.log_le_log (Real.exp_pos _) (by linarith)
  rw [Real.log_exp] at hlog2P
  obtain ⟨j, hj1, hj2, hj3⟩ := exists_pow_le_two_mul hL hP1' h2Z hlog2Z hlog2P
  have hjL : (j : ℝ) ≤ 2 * Real.log x := by
    refine hj3.trans ?_
    have := Real.rpow_le_rpow_of_exponent_le hL (show 1 - alo ≤ 1 by linarith)
    rw [Real.rpow_one] at this
    linarith
  have hcard := card_sparseSet_mul_pow_le (x := x) (As := As) χ ξ (j := j) (by linarith) hP1'
    (fun p hp => ⟨(hPS p hp).1, (hPS p hp).2.2⟩) hj1
  have hy1 : 1 ≤ 1 + Real.log (2 * (2 * d.X * Real.log x ^ B)) := by
    have := Real.log_nonneg h2Z
    linarith
  have hy : 1 + Real.log (2 * (2 * d.X * Real.log x ^ B)) ≤ 3 * Real.log x := by linarith
  exact (le_of_mul_rpow_neg_pow_le hL hP1' h2Z hy1 hy hjL hj2 hcard).trans
    (poly_mul_pow_le_exp hL (by linarith) hP2 hj3 hE1 hE2 hE3)

/-! ### The energy on the sparse family -/

/-- The duality (`TT*`) bound: if each row of the Gram matrix
`G_{ii'} = ∑_n e_i(n) \overline{e_{i'}(n)}` has absolute sum at most `R`, then
`∑_i |∑_n c_n e_i(n)|² ≤ R ∑_n |c_n|²`. -/
private theorem sum_norm_sq_le_of_gram_rowSum {ι : Type*} (I : Finset ι) (S : Finset ℕ)
    (e : ι → ℕ → ℂ) (c : ℕ → ℂ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ i ∈ I, ∑ i' ∈ I, ‖∑ n ∈ S, e i n * starRingEnd ℂ (e i' n)‖ ≤ R) :
    ∑ i ∈ I, ‖∑ n ∈ S, c n * e i n‖ ^ 2 ≤ R * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  set b : ι → ℂ := fun i => ∑ n ∈ S, c n * e i n
  set G : ι → ι → ℂ := fun i i' => ∑ n ∈ S, e i n * starRingEnd ℂ (e i' n)
  set v : ℕ → ℂ := fun n => ∑ i ∈ I, starRingEnd ℂ (b i) * e i n
  set Q := ∑ i ∈ I, ‖b i‖ ^ 2
  have hQ0 : 0 ≤ Q := sum_nonneg fun i _ => by positivity
  have hc0 : 0 ≤ ∑ n ∈ S, ‖c n‖ ^ 2 := sum_nonneg fun n _ => by positivity
  -- `Q = ∑_n c_n v_n`
  have hQv : (Q : ℂ) = ∑ n ∈ S, c n * v n := by
    simp only [Q, v, Complex.ofReal_sum, Complex.ofReal_pow, ← Complex.conj_mul', mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    simp only [b, mul_sum]
    exact sum_congr rfl fun n _ => by ring
  -- `∑_n |v_n|² = ∑_{i, i'} \bar b_i b_{i'} G_{ii'}`
  have hvG : ((∑ n ∈ S, ‖v n‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ I, ∑ i' ∈ I, starRingEnd ℂ (b i) * b i' * G i i' := by
    simp only [Complex.ofReal_sum, Complex.ofReal_pow, ← Complex.conj_mul', v, G, map_sum,
      map_mul, Complex.conj_conj, sum_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun i' _ => sum_congr rfl fun n _ => by ring
  -- the Gram matrix is Hermitian
  have hGsymm : ∀ i i', ‖G i' i‖ = ‖G i i'‖ := by
    intro i i'
    have h : G i' i = starRingEnd ℂ (G i i') := by
      simp only [G, map_sum, map_mul, Complex.conj_conj]
      exact sum_congr rfl fun n _ => mul_comm _ _
    rw [h, Complex.norm_conj]
  -- `∑_n |v_n|² ≤ R Q`, by `2|ab| ≤ |a|² + |b|²`
  have hv : ∑ n ∈ S, ‖v n‖ ^ 2 ≤ R * Q := by
    have h₁ : ∑ n ∈ S, ‖v n‖ ^ 2 ≤
        ∑ i ∈ I, ∑ i' ∈ I, (‖b i‖ ^ 2 * ‖G i i'‖ + ‖b i'‖ ^ 2 * ‖G i' i‖) / 2 := by
      have h := congrArg norm hvG
      rw [Complex.norm_real, Real.norm_of_nonneg (sum_nonneg fun n _ => by positivity)] at h
      rw [h]
      refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => (norm_sum_le _ _).trans
        (sum_le_sum fun i' _ => ?_))
      rw [norm_mul, norm_mul, Complex.norm_conj, hGsymm]
      nlinarith [mul_nonneg (sq_nonneg (‖b i‖ - ‖b i'‖)) (norm_nonneg (G i' i))]
    have h₂ : ∑ i ∈ I, ∑ i' ∈ I, (‖b i‖ ^ 2 * ‖G i i'‖ + ‖b i'‖ ^ 2 * ‖G i' i‖) / 2 =
        ∑ i ∈ I, ‖b i‖ ^ 2 * ∑ i' ∈ I, ‖G i i'‖ := by
      simp only [add_div, sum_add_distrib]
      rw [sum_comm (f := fun i i' => ‖b i'‖ ^ 2 * ‖G i' i‖ / 2), ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_add_distrib, mul_sum]
      exact sum_congr rfl fun i' _ => by ring
    rw [h₂] at h₁
    refine h₁.trans ?_
    rw [mul_comm R, sum_mul]
    exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hR i hi) (by positivity)
  -- `Q² ≤ (∑ |c_n|²)(∑ |v_n|²)`, by Cauchy–Schwarz
  have hQ : Q ^ 2 ≤ (∑ n ∈ S, ‖c n‖ ^ 2) * (R * Q) := by
    have h : Q ≤ ∑ n ∈ S, ‖c n‖ * ‖v n‖ := by
      have := congrArg norm hQv
      rw [Complex.norm_real, Real.norm_of_nonneg hQ0] at this
      rw [this]
      exact (norm_sum_le _ _).trans_eq (sum_congr rfl fun n _ => norm_mul _ _)
    calc Q ^ 2 ≤ (∑ n ∈ S, ‖c n‖ * ‖v n‖) ^ 2 := pow_le_pow_left₀ hQ0 h 2
      _ ≤ (∑ n ∈ S, ‖c n‖ ^ 2) * ∑ n ∈ S, ‖v n‖ ^ 2 := sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hv hc0
  rcases hQ0.eq_or_lt with h | h
  · rw [← h]
    positivity
  · nlinarith

/-- `∑_{m' ∈ S} 1/|m - m'| ≤ 2 (1 + log N)` for `S` and `m` in an integer interval of
length `N`, the term `m' = m` being `0`. -/
private theorem sum_inv_abs_intCast_sub_le {S : Finset ℤ} {lo hi m : ℤ} (hS : S ⊆ Icc lo hi)
    (hm : m ∈ Icc lo hi) :
    ∑ m' ∈ S, |((m - m' : ℤ) : ℝ)|⁻¹ ≤ 2 * (1 + Real.log (hi - lo + 1).toNat) := by
  -- shift `[lo, hi]` to `[1, N]`
  set f : ℤ → ℕ := fun l => (l - lo + 1).toNat
  have hf : ∀ l ∈ Icc lo hi, ((f l : ℕ) : ℤ) = l - lo + 1 := fun l hl =>
    Int.toNat_of_nonneg (by rw [mem_Icc] at hl; omega)
  have hfmem : ∀ l ∈ Icc lo hi, f l ∈ Icc 1 (hi - lo + 1).toNat := by
    intro l hl
    have h := hf l hl
    rw [mem_Icc] at hl ⊢
    omega
  have hcast : ∀ l ∈ Icc lo hi, ((f l : ℕ) : ℝ) = ((l - lo + 1 : ℤ) : ℝ) := fun l hl => by
    rw [← hf l hl, Int.cast_natCast]
  have hinj : Set.InjOn f S := fun l hl l' hl' h => by
    have h₁ := hf l (hS hl)
    have h₂ := hf l' (hS hl')
    rw [h] at h₁
    omega
  calc ∑ m' ∈ S, |((m - m' : ℤ) : ℝ)|⁻¹ = ∑ m' ∈ S, |((f m : ℕ) : ℝ) - f m'|⁻¹ := by
        refine sum_congr rfl fun m' hm' => ?_
        rw [hcast m hm, hcast m' (hS hm')]
        push_cast
        ring_nf
    _ = ∑ n ∈ S.image f, |((f m : ℕ) : ℝ) - n|⁻¹ :=
        (sum_image (f := fun n : ℕ => |((f m : ℕ) : ℝ) - n|⁻¹) hinj).symm
    _ ≤ ∑ n ∈ Icc 1 (hi - lo + 1).toNat, |((f m : ℕ) : ℝ) - n|⁻¹ := by
        refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => by positivity
        obtain ⟨l, hl, rfl⟩ := mem_image.1 hn
        exact hfmem l (hS hl)
    _ ≤ _ := sum_inv_abs_sub_le (hfmem m hm)

/-- `|[H_n, 2H_n] ∩ ℤ| ≤ H_n + 1`. -/
theorem card_nRange_le (d : Data K) (hHn : 0 ≤ d.Hn) : (#d.nRange : ℝ) ≤ d.Hn + 1 := by
  unfold Data.nRange
  rw [Nat.card_Icc]
  rcases le_or_gt ⌈d.Hn⌉₊ (⌊2 * d.Hn⌋₊ + 1) with h | h
  · rw [Nat.cast_sub h]
    push_cast
    linarith [Nat.floor_le (show 0 ≤ 2 * d.Hn by linarith), Nat.le_ceil d.Hn]
  · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
    linarith

/-- A Gram entry `G_{mm'} = ∑_{n ∈ [H_n, 2H_n]} n^{i(τ_m - τ_{m'})}`, for points
`τ_m ∈ [m, m + 1]` of absolute value at most `Z + 1 = 2XL^B + 1`, is at most `H_n + 1` when
`|m - m'| ≤ 1`, plus `|c_G| H_n (2/|m - m'| + exp(-L^{0.95}))` by (G). -/
theorem norm_nRange_gram_le {B cG x : ℝ} {d : Data K} (hKB : KernelBound B cG x d) (hHn : 0 < d.Hn)
    {m m' : ℤ} {τ τ' : ℝ} (hτ : (m : ℝ) ≤ τ ∧ τ ≤ m + 1) (hτ' : (m' : ℝ) ≤ τ' ∧ τ' ≤ m' + 1)
    (hτZ : |τ| ≤ 2 * d.X * Real.log x ^ B + 1) (hτZ' : |τ'| ≤ 2 * d.X * Real.log x ^ B + 1) :
    ‖∑ n ∈ d.nRange, (n : ℂ) ^ ((τ : ℂ) * Complex.I) *
        starRingEnd ℂ ((n : ℂ) ^ ((τ' : ℂ) * Complex.I))‖ ≤
      (if |m - m'| ≤ 1 then d.Hn + 1 else 0) +
        |cG| * d.Hn * (2 * |((m - m' : ℤ) : ℝ)|⁻¹ + Real.exp (-Real.log x ^ (0.95 : ℝ))) := by
  have hn : ∀ n ∈ d.nRange, 0 < n := fun n hn =>
    lt_of_lt_of_le (Nat.ceil_pos.2 hHn) (mem_Icc.1 hn).1
  -- the entry is the kernel at `Δ = τ - τ'`
  have hG : ∑ n ∈ d.nRange, (n : ℂ) ^ ((τ : ℂ) * Complex.I) *
      starRingEnd ℂ ((n : ℂ) ^ ((τ' : ℂ) * Complex.I)) =
        ∑ n ∈ d.nRange, (n : ℂ) ^ (((τ - τ' : ℝ) : ℂ) * Complex.I) :=
    sum_congr rfl fun n hn' => natCast_cpow_mul_I_mul_conj_cpow (hn n hn').ne' τ τ'
  rw [hG]
  have hsecond : 0 ≤ |cG| * d.Hn *
      (2 * |((m - m' : ℤ) : ℝ)|⁻¹ + Real.exp (-Real.log x ^ (0.95 : ℝ))) := by positivity
  have hmm' : |((m - m' : ℤ) : ℝ)| ≤ |τ - τ'| + 1 := by
    push_cast
    rw [abs_le]
    constructor <;> cases abs_cases (τ - τ') <;> linarith
  by_cases h₁ : |m - m'| ≤ 1
  · -- `|m - m'| ≤ 1`: the trivial bound
    rw [ite_eq_left h₁]
    refine le_add_of_le_of_nonneg ((norm_sum_le _ _).trans ?_) hsecond
    calc ∑ n ∈ d.nRange, ‖(n : ℂ) ^ (((τ - τ' : ℝ) : ℂ) * Complex.I)‖
        = #d.nRange := by
          rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
          exact sum_congr rfl fun n hn' => norm_natCast_cpow_ofReal_mul_I (hn n hn') _
      _ ≤ d.Hn + 1 := card_nRange_le d hHn.le
  · -- `|m - m'| ≥ 2`, so `|τ - τ'| ≥ 1`: the kernel bound (G)
    rw [ite_eq_right h₁, zero_add]
    have h₂ : (2 : ℝ) ≤ |((m - m' : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast (show (2 : ℤ) ≤ |m - m'| by omega)
    have h : 1 ≤ |τ - τ'| := by linarith
    have hΔ : |τ - τ'| ≤ 4 * (d.Hm * d.Hn) * Real.log x ^ B + 2 := by
      have := abs_sub τ τ'
      have hX : d.X = d.Hm * d.Hn := rfl
      rw [hX] at hτZ hτZ'
      linarith
    have hK := hKB (τ - τ') h hΔ
    have hinv : |τ - τ'|⁻¹ ≤ 2 * |((m - m' : ℤ) : ℝ)|⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by linarith)]
      calc |τ - τ'|⁻¹ * |((m - m' : ℤ) : ℝ)| ≤ |τ - τ'|⁻¹ * (2 * |τ - τ'|) := by
            gcongr
            linarith
        _ = 2 := by field_simp
    calc ‖∑ n ∈ d.nRange, (n : ℂ) ^ (((τ - τ' : ℝ) : ℂ) * Complex.I)‖
        = d.Hn * (d.Hn⁻¹ *
            ‖∑ n ∈ d.nRange, (n : ℂ) ^ (((τ - τ' : ℝ) : ℂ) * Complex.I)‖) := by
          field_simp
      _ ≤ d.Hn * (cG * (|τ - τ'|⁻¹ + Real.exp (-Real.log x ^ (0.95 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hK hHn.le
      _ ≤ d.Hn * (|cG| * (2 * |((m - m' : ℤ) : ℝ)|⁻¹ +
            Real.exp (-Real.log x ^ (0.95 : ℝ)))) := by
          gcongr
          exact le_abs_self cG
      _ = _ := by ring

/-- The energy of `N_β` at points `τ_m ∈ [m, m + 1]` with `|τ_m| ≤ Z + 1`, over a set `S` of
integers in `[-⌈Z⌉ - 1, ⌈Z⌉]` with `|S| exp(-L^{0.95}) ≤ 1`, where `Z = 2XL^B`. By the
`TT*` bound with the Gram rows of `norm_nRange_gram_le`, it is at most
`H_n⁻² (3(H_n + 1) + |c_G| H_n (4(1 + log N) + 1)) (H_n + 1) L^{2C}` with `N = 2⌈Z⌉ + 2`. -/
theorem sum_norm_unmarkedPoly_sq_le {C CX alo ahi g B cG x Z : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d) (hKB : KernelBound B cG x d) (hL : 0 ≤ Real.log x)
    (hHn : 0 < d.Hn) (hZ : Z = 2 * d.X * Real.log x ^ B) {k : ℕ}
    (ψ : DirichletCharacter ℂ k) {S : Finset ℤ} (hS : S ⊆ Icc (-⌈Z⌉ - 1) ⌈Z⌉)
    (hSe : #S * Real.exp (-Real.log x ^ (0.95 : ℝ)) ≤ 1) (τ : ℤ → ℝ)
    (hτ : ∀ m ∈ S, (m : ℝ) ≤ τ m ∧ τ m ≤ m + 1 ∧ |τ m| ≤ Z + 1) :
    ∑ m ∈ S, ‖unmarkedPoly d ψ (τ m)‖ ^ 2 ≤
      d.Hn⁻¹ ^ 2 * (3 * (d.Hn + 1) +
        |cG| * d.Hn * (4 * (1 + Real.log (⌈Z⌉ - (-⌈Z⌉ - 1) + 1).toNat) + 1)) *
          ((d.Hn + 1) * Real.log x ^ (2 * C)) := by
  set R := 3 * (d.Hn + 1) +
    |cG| * d.Hn * (4 * (1 + Real.log (⌈Z⌉ - (-⌈Z⌉ - 1) + 1).toNat) + 1) with hR
  have hR0 : 0 ≤ R := by positivity
  set e : ℤ → ℕ → ℂ := fun m n => (n : ℂ) ^ ((τ m : ℂ) * Complex.I)
  -- the Gram rows are at most `R`
  have hrow : ∀ m ∈ S, ∑ m' ∈ S, ‖∑ n ∈ d.nRange, e m n * starRingEnd ℂ (e m' n)‖ ≤ R := by
    intro m hm
    have hnear : ∑ m' ∈ S, (if |m - m'| ≤ 1 then d.Hn + 1 else 0) ≤ 3 * (d.Hn + 1) := by
      rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
      have hsub : {m' ∈ S | |m - m'| ≤ 1} ⊆ Icc (m - 1) (m + 1) := fun m' hm' => by
        rw [mem_filter] at hm'
        rw [mem_Icc]
        constructor <;> cases abs_cases (m - m') <;> omega
      have hcard : (#{m' ∈ S | |m - m'| ≤ 1} : ℝ) ≤ 3 := by
        have h := card_le_card hsub
        rw [Int.card_Icc, show m + 1 + 1 - (m - 1) = 3 by ring] at h
        exact_mod_cast h
      nlinarith
    have hfar := sum_inv_abs_intCast_sub_le hS (hS hm)
    calc ∑ m' ∈ S, ‖∑ n ∈ d.nRange, e m n * starRingEnd ℂ (e m' n)‖
        ≤ ∑ m' ∈ S, ((if |m - m'| ≤ 1 then d.Hn + 1 else 0) +
            |cG| * d.Hn * (2 * |((m - m' : ℤ) : ℝ)|⁻¹ +
              Real.exp (-Real.log x ^ (0.95 : ℝ)))) := by
          refine sum_le_sum fun m' hm' => norm_nRange_gram_le hKB hHn ⟨(hτ m hm).1, (hτ m hm).2.1⟩
            ⟨(hτ m' hm').1, (hτ m' hm').2.1⟩ ?_ ?_
          · rw [← hZ]
            exact (hτ m hm).2.2
          · rw [← hZ]
            exact (hτ m' hm').2.2
      _ = ∑ m' ∈ S, (if |m - m'| ≤ 1 then d.Hn + 1 else 0) + |cG| * d.Hn *
            (2 * ∑ m' ∈ S, |((m - m' : ℤ) : ℝ)|⁻¹ +
              #S * Real.exp (-Real.log x ^ (0.95 : ℝ))) := by
          rw [sum_add_distrib, ← mul_sum, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ R := by
          have h := mul_le_mul_of_nonneg_left (show 2 * ∑ m' ∈ S, |((m - m' : ℤ) : ℝ)|⁻¹ +
            #S * Real.exp (-Real.log x ^ (0.95 : ℝ)) ≤
              4 * (1 + Real.log (⌈Z⌉ - (-⌈Z⌉ - 1) + 1).toNat) + 1 by linarith)
            (by positivity : 0 ≤ |cG| * d.Hn)
          rw [hR]
          linarith
  -- the coefficients `β_n ψ(n)` have `∑ |β_n ψ(n)|² ≤ (H_n + 1) L^{2C}`
  have hβ : ∀ n, ‖d.β n * ψ n‖ ^ 2 ≤ Real.log x ^ (2 * C) := by
    intro n
    have h₁ : ‖d.β n‖ ≤ Real.log x ^ C := by
      by_cases h : d.β n = 0
      · rw [h, norm_zero]
        exact Real.rpow_nonneg hL _
      · exact (hd.β_supp n h).2.2.2
    have h₂ : ‖d.β n * ψ n‖ ≤ Real.log x ^ C := by
      rw [norm_mul]
      calc ‖d.β n‖ * ‖ψ n‖ ≤ Real.log x ^ C * 1 :=
            mul_le_mul h₁ (DirichletCharacter.norm_le_one ψ _) (norm_nonneg _)
              (Real.rpow_nonneg hL _)
        _ = Real.log x ^ C := mul_one _
    calc ‖d.β n * ψ n‖ ^ 2 ≤ (Real.log x ^ C) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
      _ = Real.log x ^ (2 * C) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
          ring_nf
  have hcoef : ∑ n ∈ d.nRange, ‖d.β n * ψ n‖ ^ 2 ≤ (d.Hn + 1) * Real.log x ^ (2 * C) := by
    calc ∑ n ∈ d.nRange, ‖d.β n * ψ n‖ ^ 2 ≤ ∑ n ∈ d.nRange, Real.log x ^ (2 * C) :=
          sum_le_sum fun n _ => hβ n
      _ = #d.nRange * Real.log x ^ (2 * C) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (d.Hn + 1) * Real.log x ^ (2 * C) := by
          gcongr
          exact card_nRange_le d hHn.le
  have hgram := sum_norm_sq_le_of_gram_rowSum S d.nRange e (fun n => d.β n * ψ n) hR0 hrow
  calc ∑ m ∈ S, ‖unmarkedPoly d ψ (τ m)‖ ^ 2
      = d.Hn⁻¹ ^ 2 * ∑ m ∈ S, ‖∑ n ∈ d.nRange, d.β n * ψ n * e m n‖ ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun m _ => ?_
        rw [unmarkedPoly, norm_mul, mul_pow, norm_inv, Complex.norm_real,
          Real.norm_of_nonneg hHn.le]
    _ ≤ d.Hn⁻¹ ^ 2 * (R * ((d.Hn + 1) * Real.log x ^ (2 * C))) := by
        gcongr
        exact hgram.trans (mul_le_mul_of_nonneg_left hcoef hR0)
    _ = _ := by ring

/-- `log(2⌈Z⌉ + 2) ≤ 4 + log 2Z` for `2Z ≥ 1`. -/
private theorem log_toNat_ceil_le {Z : ℝ} (h2Z : 1 ≤ 2 * Z) :
    Real.log (⌈Z⌉ - (-⌈Z⌉ - 1) + 1).toNat ≤ 4 + Real.log (2 * Z) := by
  have hZ0 : 0 ≤ ⌈Z⌉ := Int.ceil_nonneg (by linarith)
  have hcast : (((⌈Z⌉ - (-⌈Z⌉ - 1) + 1).toNat : ℕ) : ℝ) = 2 * ⌈Z⌉ + 2 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast
    ring
  have hceil := Int.ceil_lt_add_one Z
  rw [hcast]
  calc Real.log (2 * ⌈Z⌉ + 2) ≤ Real.log (5 * (2 * Z)) :=
        Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 5 + Real.log (2 * Z) := Real.log_mul (by norm_num) (by positivity)
    _ ≤ 4 + Real.log (2 * Z) := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
        linarith

/-- PD (5.10), second half: under (G), the energy of `N_β` on the sparse family is at most
`C₀ L^{2C + 1}`, at any points `t_m ∈ [m, m + 1]`. -/
theorem sum_norm_sq_le_of_sparse {C CX alo ahi g B As cG : ℝ} (halo : 1 / 10 < alo)
    (hahi : ahi < 1 / 5) :
    ∃ C₀ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      KernelBound B cG x d →
      ∀ P : ℝ, Real.exp (Real.log x ^ alo) ≤ P → P ≤ Real.exp (2 * Real.log x ^ ahi) →
      ∀ PS : Finset ℕ, (∀ p ∈ PS, p.Prime ∧ P ≤ p ∧ (p : ℝ) < 2 * P) →
      ∀ (k : ℕ) (χ ψ : DirichletCharacter ℂ k) (ξ : ℝ) (τ : ℤ → ℝ),
        (∀ m : ℤ, (m : ℝ) ≤ τ m ∧ τ m ≤ m + 1) →
        ∑ m ∈ sparseSet x (2 * d.X * Real.log x ^ B) As P PS χ ξ,
            ‖unmarkedPoly d ψ (τ m)‖ ^ 2 ≤
          C₀ * Real.log x ^ (2 * C + 1) := by
  obtain ⟨C₁, hC₁⟩ := card_sparseSet_le (K := K) (C := C) (CX := CX) (g := g) (B := B)
    (As := As) halo hahi
  refine ⟨12 + 58 * |cG|, ?_⟩
  filter_upwards [hC₁, eventually_mul_rpow_mul_one_add_log_le
      (show (91 / 100 : ℝ) < 0.95 by norm_num) |C₁|,
    eventually_mul_rpow_mul_one_add_log_le (show (0 : ℝ) < 1 by norm_num)
      (Real.log (4 * max CX 1) + |B|),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop 1]
    with x hcard hE5 hE4 hL hx1 d hd hKB P hP1 hP2 PS hPS k χ ψ ξ τ hτ
  rw [Real.rpow_zero, mul_one, Real.rpow_one] at hE4
  have hx : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  obtain ⟨h2Z, hlog2Z⟩ := one_le_two_mul_and_log_le_of_admissible hd hx hL hE4
  have hHn : 1 ≤ d.Hn :=
    (Real.one_le_rpow hx1 ((Real.rpow_nonneg hL0.le _).trans hd.γ_ge)).trans hd.Hn_ge
  -- `|𝓘| exp(-L^{0.95}) ≤ 1`
  have hSe : (#(sparseSet x (2 * d.X * Real.log x ^ B) As P PS χ ξ) : ℝ) *
      Real.exp (-Real.log x ^ (0.95 : ℝ)) ≤ 1 := by
    have h₁ : C₁ * Real.log x ^ (91 / 100 : ℝ) ≤ Real.log x ^ (0.95 : ℝ) := by
      have hlogL := Real.log_nonneg hL
      have h91 := Real.rpow_nonneg hL0.le (91 / 100 : ℝ)
      calc C₁ * Real.log x ^ (91 / 100 : ℝ) ≤ |C₁| * Real.log x ^ (91 / 100 : ℝ) := by
            gcongr
            exact le_abs_self C₁
        _ ≤ |C₁| * Real.log x ^ (91 / 100 : ℝ) * (1 + Real.log (Real.log x)) := by
            nlinarith [mul_nonneg (abs_nonneg C₁) h91]
        _ ≤ _ := hE5
    calc (#(sparseSet x (2 * d.X * Real.log x ^ B) As P PS χ ξ) : ℝ) *
          Real.exp (-Real.log x ^ (0.95 : ℝ))
        ≤ Real.exp (Real.log x ^ (0.95 : ℝ)) * Real.exp (-Real.log x ^ (0.95 : ℝ)) := by
          gcongr
          exact (hcard d hd P hP1 hP2 PS hPS k χ ξ).trans (Real.exp_le_exp.2 h₁)
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  -- the points `τ_m` have `|τ_m| ≤ Z + 1`
  have hτS : ∀ m ∈ sparseSet x (2 * d.X * Real.log x ^ B) As P PS χ ξ,
      (m : ℝ) ≤ τ m ∧ τ m ≤ m + 1 ∧ |τ m| ≤ 2 * d.X * Real.log x ^ B + 1 := by
    intro m hm
    simp only [sparseSet, mem_filter] at hm
    obtain ⟨t, ht₁, ht₂, ht₃, -⟩ := hm.2
    obtain ⟨hτ₁, hτ₂⟩ := hτ m
    refine ⟨hτ₁, hτ₂, abs_le.2 ⟨?_, ?_⟩⟩ <;> cases abs_le.1 ht₃ <;> linarith
  have hsub : sparseSet x (2 * d.X * Real.log x ^ B) As P PS χ ξ ⊆
      Icc (-⌈2 * d.X * Real.log x ^ B⌉ - 1) ⌈2 * d.X * Real.log x ^ B⌉ := fun m hm => by
    simp only [sparseSet, mem_filter] at hm
    exact hm.1
  have hE := sum_norm_unmarkedPoly_sq_le hd hKB hL0.le (by linarith) rfl ψ hsub hSe τ hτS
  have hN := log_toNat_ceil_le h2Z
  have hN0 := Real.log_natCast_nonneg
    (⌈2 * d.X * Real.log x ^ B⌉ - (-⌈2 * d.X * Real.log x ^ B⌉ - 1) + 1).toNat
  set A := Real.log (⌈2 * d.X * Real.log x ^ B⌉ - (-⌈2 * d.X * Real.log x ^ B⌉ - 1) + 1).toNat
  set W := Real.log x ^ (2 * C) with hW
  have hW0 : 0 ≤ W := Real.rpow_nonneg hL0.le _
  -- `3(H_n + 1) + |c_G| H_n (4(1 + A) + 1) ≤ H_n (6 + 29 |c_G| L)`
  have h₁ : 3 * (d.Hn + 1) + |cG| * d.Hn * (4 * (1 + A) + 1) ≤
      d.Hn * (6 + 29 * |cG| * Real.log x) := by
    have h : 4 * (1 + A) + 1 ≤ 29 * Real.log x := by linarith
    have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ |cG| * d.Hn)
    nlinarith
  calc ∑ m ∈ sparseSet x (2 * d.X * Real.log x ^ B) As P PS χ ξ,
        ‖unmarkedPoly d ψ (τ m)‖ ^ 2
      ≤ d.Hn⁻¹ ^ 2 * (3 * (d.Hn + 1) + |cG| * d.Hn * (4 * (1 + A) + 1)) *
          ((d.Hn + 1) * W) := hE
    _ ≤ d.Hn⁻¹ ^ 2 * (d.Hn * (6 + 29 * |cG| * Real.log x)) * ((2 * d.Hn) * W) := by
        gcongr
        linarith
    _ = 2 * (6 + 29 * |cG| * Real.log x) * W := by
        field_simp
    _ ≤ (12 + 58 * |cG|) * (Real.log x * W) := by
        nlinarith [mul_nonneg (abs_nonneg cG) hW0]
    _ = (12 + 58 * |cG|) * Real.log x ^ (2 * C + 1) := by
        rw [hW, Real.rpow_add_one hL0.ne', mul_comm (Real.log x)]

end Erdos408.OneSided
