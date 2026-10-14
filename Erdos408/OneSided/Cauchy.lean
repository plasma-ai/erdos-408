module

public import Erdos408.OneSided.Bands
public import Mathlib.Algebra.Order.Chebyshev

/-!
# The Cauchy reduction

Interface 1 of `blueprint/one_sided_type_ii.md` (§3, PD §3.1). Expand the marked weight
into label products `b₀`, one prime from each band. Replacing the damping by
`q^{ω(h)}` with `mn - 1 = b₀ h` costs the squareful error, and invariance gives
`F(mn - 1) = F(h)`. Split `b₀` dyadically with `η(b₀ / Y)`, `Y = 2^j`, and apply Cauchy in
`h`: the square of the `Y` piece is at most `(4X / Y) Q_Y`. A bound
`Q_Y ≪ X Y L^{-D₁}` with `D₁ = 2D_* + 2` therefore bounds the sum by `X L^{-D_*}`, after
summing the `O(L)` relevant dyads.
-/

@[expose] public section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

/-! ### The dyadic bump -/

theorem dyadicBump_nonneg (y : ℝ) : 0 ≤ dyadicBump y := by
  unfold dyadicBump
  rcases le_or_gt 0 y with hy | hy
  · exact sub_nonneg.2 (smoothTransition.monotone (by linarith))
  · rw [smoothTransition.zero_of_nonpos (by linarith),
      smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem dyadicBump_le_one (y : ℝ) : dyadicBump y ≤ 1 := by
  unfold dyadicBump
  linarith [smoothTransition.le_one (y - 1), smoothTransition.nonneg (y / 2 - 1)]

/-- `η(y) ≠ 0` only for `1 < y < 4`. -/
theorem lt_of_dyadicBump_ne_zero {y : ℝ} (h : dyadicBump y ≠ 0) : 1 < y ∧ y < 4 := by
  unfold dyadicBump at h
  constructor
  · by_contra hy
    rw [not_lt] at hy
    rw [smoothTransition.zero_of_nonpos (by linarith),
      smoothTransition.zero_of_nonpos (by linarith), sub_zero] at h
    exact h rfl
  · by_contra hy
    rw [not_lt] at hy
    rw [smoothTransition.one_of_one_le (by linarith),
      smoothTransition.one_of_one_le (by linarith), sub_self] at h
    exact h rfl

/-- The dyadic partition telescopes: `∑_{j < J} η(b / 2^j) = s(b) - s(b / 2^J)`. -/
theorem sum_dyadicBump (b : ℝ) (J : ℕ) :
    ∑ j ∈ range J, dyadicBump (b / 2 ^ j) =
      smoothTransition (b - 1) - smoothTransition (b / 2 ^ J - 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, ih, dyadicBump, pow_succ, div_div]
    ring

/-- The dyadic partition of unity: `∑_{j < J} η(b / 2^j) = 1` for `2 ≤ b ≤ 2^J`. -/
theorem sum_dyadicBump_eq_one {b : ℝ} {J : ℕ} (hb : 2 ≤ b) (hbJ : b ≤ 2 ^ J) :
    ∑ j ∈ range J, dyadicBump (b / 2 ^ j) = 1 := by
  rw [sum_dyadicBump, smoothTransition.one_of_one_le (by linarith),
    smoothTransition.zero_of_nonpos, sub_zero]
  rw [sub_nonpos, div_le_one (by positivity)]
  exact hbJ

/-! ### The label expansion of the marked weight -/

/-- The marked weight as a sum over label tuples, one prime from each band:
`𝒲(N) = ∏V_i⁻¹ ∑_p q^{ω(N) - K} ∏_i [p_i ∣ N]`. -/
theorem markedWeight_eq_sum_labels (q x : ℝ) (d : Data K) (N : ℕ) :
    markedWeight Finset.univ q (fun i => band x (d.a i)) N =
      (d.bandMass x)⁻¹ * ∑ p ∈ d.labels x,
        q ^ ((∑ i, primeCount (band x (d.a i)) N : ℕ) - K : ℤ) *
          ∏ i, (if p i ∣ N then (1 : ℝ) else 0) := by
  unfold markedWeight Data.bandMass Data.labels
  rw [card_univ, Fintype.card_fin, ← Finset.mul_sum, mul_left_comm]
  congr 1
  rw [prod_div_distrib, div_eq_inv_mul]
  congr 1
  -- `ω_i(N) = ∑_{p ∈ 𝒫_i} [p ∣ N]`, and the product of sums is a sum over tuples
  have hω : ∀ i, (primeCount (band x (d.a i)) N : ℝ) =
      ∑ p ∈ band x (d.a i), if p ∣ N then (1 : ℝ) else 0 := by
    intro i
    rw [primeCount, card_filter]
    push_cast
    rfl
  simp_rw [hω]
  exact prod_univ_sum _ _

/-- Invariance under one prime from each band: `F(∏_i p_i · h) = F(h)`. -/
theorem F_labelProd_mul {C CX alo ahi g x : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d) {p : Fin K → ℕ} (hp : p ∈ d.labels x) (h : ℕ) :
    d.F ((∏ i, p i) * h) = d.F h := by
  have hp' : ∀ i, p i ∈ band x (d.a i) := Fintype.mem_piFinset.1 hp
  -- peel the primes one at a time
  have key : ∀ s : Finset (Fin K), d.F ((∏ i ∈ s, p i) * h) = d.F h := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [prod_insert hi, mul_assoc, hd.F_inv i _ (p i) (hp' i), ih]
  exact key univ

/-- With disjoint bands, if no label prime divides `h`, then
`ω(∏_i p_i · h) = ω(h) + K`. -/
theorem bandCount_labelProd_mul {x : ℝ} {d : Data K}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {p : Fin K → ℕ} (hp : p ∈ d.labels x) {h : ℕ} (hnd : ∀ i, ¬ p i ∣ h) :
    bandCount x d ((∏ j, p j) * h) = bandCount x d h + K := by
  have hp' : ∀ i, p i ∈ band x (d.a i) := Fintype.mem_piFinset.1 hp
  have hprime : ∀ i, (p i).Prime := fun i => (mem_filter.1 (hp' i)).2
  -- in band `i`, the primes dividing `∏_j p_j · h` are those dividing `h`, and `p i`
  have hband : ∀ i, primeCount (band x (d.a i)) ((∏ j, p j) * h) =
      primeCount (band x (d.a i)) h + 1 := by
    intro i
    unfold primeCount
    have hset : (band x (d.a i)).filter (· ∣ (∏ j, p j) * h) =
        insert (p i) ((band x (d.a i)).filter (· ∣ h)) := by
      ext r
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hr, hdvd⟩
        have hrp : r.Prime := (mem_filter.1 hr).2
        rcases (Nat.Prime.dvd_mul hrp).1 hdvd with hdp | hdh
        · obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hrp.prime _).1 hdp
          have hrj : r = p j := (Nat.prime_dvd_prime_iff_eq hrp (hprime j)).1 hj
          by_cases hij : i = j
          · exact Or.inl (hrj.trans (by rw [hij]))
          · exact absurd (hrj ▸ hp' j) (disjoint_left.1 (hdisj i j hij) hr)
        · exact Or.inr ⟨hr, hdh⟩
      · rintro (rfl | ⟨hr, hdh⟩)
        · exact ⟨hp' i, Dvd.dvd.mul_right (dvd_prod_of_mem _ (mem_univ i)) _⟩
        · exact ⟨hr, Dvd.dvd.mul_left hdh _⟩
    rw [hset, card_insert_of_notMem]
    simp only [mem_filter, not_and]
    exact fun _ => hnd i
  simp only [bandCount, hband, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

/-- With disjoint bands, `ω(∏_i p_i · h) ≤ ω(h) + K` for every `h`: in band `i` only `p_i`
can be added. -/
theorem bandCount_labelProd_mul_le {x : ℝ} {d : Data K}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {p : Fin K → ℕ} (hp : p ∈ d.labels x) (h : ℕ) :
    bandCount x d ((∏ j, p j) * h) ≤ bandCount x d h + K := by
  have hp' : ∀ i, p i ∈ band x (d.a i) := Fintype.mem_piFinset.1 hp
  have hprime : ∀ i, (p i).Prime := fun i => (mem_filter.1 (hp' i)).2
  have hband : ∀ i, primeCount (band x (d.a i)) ((∏ j, p j) * h) ≤
      primeCount (band x (d.a i)) h + 1 := by
    intro i
    unfold primeCount
    have hsub : (band x (d.a i)).filter (· ∣ (∏ j, p j) * h) ⊆
        insert (p i) ((band x (d.a i)).filter (· ∣ h)) := by
      intro r hr
      rw [mem_filter] at hr
      rw [mem_insert, mem_filter]
      have hrp : r.Prime := (mem_filter.1 hr.1).2
      rcases (Nat.Prime.dvd_mul hrp).1 hr.2 with hdp | hdh
      · obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hrp.prime _).1 hdp
        have hrj : r = p j := (Nat.prime_dvd_prime_iff_eq hrp (hprime j)).1 hj
        by_cases hij : i = j
        · exact Or.inl (hrj.trans (by rw [hij]))
        · exact absurd (hrj ▸ hp' j) (disjoint_left.1 (hdisj i j hij) hr.1)
      · exact Or.inr ⟨hr.1, hdh⟩
    exact (card_le_card hsub).trans (card_insert_le _ _)
  calc bandCount x d ((∏ j, p j) * h) ≤ ∑ i, (primeCount (band x (d.a i)) h + 1) :=
        sum_le_sum fun i _ => hband i
    _ = bandCount x d h + K := by
        simp [bandCount, sum_add_distrib]

/-- With disjoint bands the label primes are distinct, so
`∏_i [p_i ∣ N] = [∏_i p_i ∣ N]`. -/
theorem prod_ite_dvd_eq {x : ℝ} {d : Data K}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {p : Fin K → ℕ} (hp : p ∈ d.labels x) (N : ℕ) :
    ∏ i, (if p i ∣ N then (1 : ℝ) else 0) = if (∏ i, p i) ∣ N then 1 else 0 := by
  have hp' : ∀ i, p i ∈ band x (d.a i) := Fintype.mem_piFinset.1 hp
  have hprime : ∀ i, (p i).Prime := fun i => (mem_filter.1 (hp' i)).2
  by_cases hall : ∀ i, p i ∣ N
  · rw [prod_eq_one fun i _ => ite_eq_left (hall i), ite_eq_left]
    -- the labels are distinct primes
    have hinj : Function.Injective p := by
      intro i j hij
      by_contra hne
      exact disjoint_left.1 (hdisj i j hne) (hp' i) (hij ▸ hp' j)
    have himg : ∏ i, p i = ∏ r ∈ univ.image p, r :=
      (prod_image (f := fun r => r) fun i _ j _ h => hinj h).symm
    rw [himg]
    refine Finset.prod_primes_dvd N (fun r hr => ?_) fun r hr => ?_
    · obtain ⟨i, -, rfl⟩ := mem_image.1 hr
      exact (hprime i).prime
    · obtain ⟨i, -, rfl⟩ := mem_image.1 hr
      exact hall i
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    rw [prod_eq_zero (mem_univ i) (ite_eq_right hi), ite_eq_right]
    exact fun h => hi ((dvd_prod_of_mem p (mem_univ i)).trans h)

/-- The marked weight is at most `(2/(1 - q))^K` once every band has mass at least `1/2`. -/
theorem markedWeight_le {q x : ℝ} (hq : 0 < q) (hq₁ : q < 1) {d : Data K}
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i))) (N : ℕ) :
    markedWeight Finset.univ q (fun i => band x (d.a i)) N ≤ (2 / (1 - q)) ^ K := by
  rw [TypeII.markedWeight_eq_prod hq.ne']
  calc ∏ i, bandWeight q x (d.a i) N ≤ ∏ _i : Fin K, 2 / (1 - q) := by
        refine prod_le_prod₀ (fun i _ => TypeII.bandWeight_nonneg hq _ _ _) fun i _ => ?_
        have hVi := hV i
        calc bandWeight q x (d.a i) N
            ≤ 1 / ((1 - q) * harmonicMass (band x (d.a i))) :=
              TypeII.bandWeight_le hq hq₁ _ _ _ (by linarith)
          _ ≤ 2 / (1 - q) := by
              rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
              nlinarith
    _ = (2 / (1 - q)) ^ K := by rw [prod_const, card_univ, Fintype.card_fin]

/-- An interval contains at most `len/k + 1` solutions of `k ∣ m n - 1`: for `m n ≥ 1` the
solutions form one residue class modulo `k`. -/
theorem card_filter_dvd_mul_sub_one_le {k m A B : ℕ} (hk : 0 < k) (hm : 0 < m) (hA : 0 < A) :
    (((Icc A B).filter fun n => k ∣ m * n - 1).card : ℝ) ≤ ((B + 1 - A : ℕ) : ℝ) / k + 1 := by
  set S := (Icc A B).filter fun n => k ∣ m * n - 1
  -- all solutions are congruent modulo `k`
  have hcong : ∀ n ∈ S, ∀ n' ∈ S, n ≡ n' [MOD k] := by
    intro n hn n' hn'
    simp only [S, mem_filter, mem_Icc] at hn hn'
    have h1 : 1 ≤ m * n := Nat.mul_pos hm (by omega)
    have h1' : 1 ≤ m * n' := Nat.mul_pos hm (by omega)
    have e₁ : 1 ≡ m * n [MOD k] := (Nat.modEq_iff_dvd' h1).2 hn.2
    have e₂ : 1 ≡ m * n' [MOD k] := (Nat.modEq_iff_dvd' h1').2 hn'.2
    have hcop : Nat.Coprime k m := (Nat.coprime_of_mul_modEq_one n e₁.symm).symm
    have := Nat.ModEq.cancel_left_div_gcd hk (e₁.symm.trans e₂)
    rwa [Nat.Coprime.gcd_eq_one hcop, Nat.div_one] at this
  -- inject the solutions into `{0, …, (B - A)/k}` by `n ↦ (n - A)/k`
  rcases S.eq_empty_or_nonempty with hS | ⟨n₀, hn₀⟩
  · rw [hS, card_empty, Nat.cast_zero]
    positivity
  have hinj : Set.InjOn (fun n => (n - A) / k) S := by
    intro n hn n' hn' heq
    have hA1 : A ≤ n := (mem_Icc.1 (mem_filter.1 hn).1).1
    have hA2 : A ≤ n' := (mem_Icc.1 (mem_filter.1 hn').1).1
    have hc : (n - A) % k = (n' - A) % k :=
      Nat.ModEq.add_right_cancel' A (by
        rw [Nat.sub_add_cancel hA1, Nat.sub_add_cancel hA2]; exact hcong n hn n' hn')
    simp only at heq
    have : n - A = n' - A := by
      rw [← Nat.div_add_mod (n - A) k, ← Nat.div_add_mod (n' - A) k, heq, hc]
    omega
  have hmaps : ∀ n ∈ S, (n - A) / k ∈ range ((B + 1 - A) / k + 1) := by
    intro n hn
    have := (mem_Icc.1 (mem_filter.1 hn).1)
    rw [mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  calc (S.card : ℝ) ≤ (range ((B + 1 - A) / k + 1)).card := by
        exact_mod_cast card_le_card_of_injOn _ hmaps hinj
    _ = (((B + 1 - A) / k : ℕ) : ℝ) + 1 := by simp
    _ ≤ ((B + 1 - A : ℕ) : ℝ) / k + 1 := by
        gcongr
        exact Nat.cast_div_le

/-! ### The Cauchy step -/

/-- The weight `w(p, m, n) = ∏V_i⁻¹ η(∏ p_i / Y) α_m β_n` of a label tuple and a pair. -/
noncomputable def cauchyWeight (x : ℝ) (d : Data K) (Y : ℝ) (p : Fin K → ℕ) (m n : ℕ) : ℂ :=
  (((d.bandMass x)⁻¹ * dyadicBump ((∏ i, p i : ℕ) / Y) : ℝ) : ℂ) * (d.α m * d.β n)

/-- The inner sum `T_h = ∑_{(∏ p_i) h = mn - 1} w(p, m, n)` of the Cauchy step. -/
noncomputable def cauchyInner (x : ℝ) (d : Data K) (Y : ℝ) (h : ℕ) : ℂ :=
  ∑ p ∈ d.labels x, ∑ m ∈ d.mRange, ∑ n ∈ d.nRange,
    if m * n - 1 = (∏ i, p i) * h then cauchyWeight x d Y p m n else 0

open scoped Classical in
/-- `h ≥ 1` with `mn - 1 = a h` and `rs - 1 = b h` is unique and, for `m, n` in range, at most
`⌊2H_m⌋ ⌊2H_n⌋`; so summing the product of the two indicators over `h` gives the indicator
of a common `h`. -/
theorem sum_ite_ite_eq {a b M m n r s : ℕ} (ha : 0 < a) (hmn : m * n ≤ M) :
    ∑ h ∈ Icc 1 M, ((if m * n - 1 = a * h then (1 : ℂ) else 0) *
        if r * s - 1 = b * h then 1 else 0) =
      if ∃ h, 1 ≤ h ∧ m * n - 1 = a * h ∧ r * s - 1 = b * h then 1 else 0 := by
  by_cases hex : ∃ h, 1 ≤ h ∧ m * n - 1 = a * h ∧ r * s - 1 = b * h
  · obtain ⟨h₀, h₀1, h₀a, h₀b⟩ := hex
    rw [ite_eq_left ⟨h₀, h₀1, h₀a, h₀b⟩]
    have hle : h₀ ≤ M := by
      have : h₀ ≤ a * h₀ := Nat.le_mul_of_pos_left _ ha
      omega
    rw [sum_eq_single h₀]
    · simp [h₀a, h₀b]
    · intro h _ hne
      have : m * n - 1 ≠ a * h := by
        rw [h₀a]
        intro heq
        exact hne (Nat.eq_of_mul_eq_mul_left ha heq).symm
      simp [this]
    · intro hnot
      exact absurd (mem_Icc.2 ⟨h₀1, hle⟩) hnot
  · rw [ite_eq_right hex]
    refine sum_eq_zero fun h hh => ?_
    by_cases h₁ : m * n - 1 = a * h
    · have h₂ : ¬ r * s - 1 = b * h := fun h₂ => hex ⟨h, (mem_Icc.1 hh).1, h₁, h₂⟩
      simp [h₂]
    · simp [h₁]

open scoped Classical in
/-- The Cauchy square is `∑_h |T_h|²`, over `1 ≤ h ≤ ⌊2H_m⌋ ⌊2H_n⌋`. -/
theorem cauchySquare_eq_sum {x : ℝ} {d : Data K} (Y : ℝ)
    (hpos : ∀ p ∈ d.labels x, 0 < ∏ i, p i) :
    cauchySquare x d Y =
      ∑ h ∈ Icc 1 (⌊2 * d.Hm⌋₊ * ⌊2 * d.Hn⌋₊), ((‖cauchyInner x d Y h‖ ^ 2 : ℝ) : ℂ) := by
  -- `|T_h|² = T_h · conj T_h`, expanded over pairs of terms
  have hsq : ∀ h, ((‖cauchyInner x d Y h‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ d.labels x, ∑ m ∈ d.mRange, ∑ n ∈ d.nRange,
        ∑ p' ∈ d.labels x, ∑ r ∈ d.mRange, ∑ s ∈ d.nRange,
          ((if m * n - 1 = (∏ i, p i) * h then (1 : ℂ) else 0) *
            if r * s - 1 = (∏ i, p' i) * h then 1 else 0) *
          (cauchyWeight x d Y p m n * star (cauchyWeight x d Y p' r s)) := by
    intro h
    rw [Complex.ofReal_pow, ← Complex.mul_conj', cauchyInner]
    simp only [Finset.sum_mul]
    simp only [map_sum, Finset.mul_sum]
    refine sum_congr rfl fun p _ => sum_congr rfl fun m _ => sum_congr rfl fun n _ =>
      sum_congr rfl fun p' _ => sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  -- the Cauchy square in the same arrangement
  have hQ : cauchySquare x d Y =
      ∑ p ∈ d.labels x, ∑ m ∈ d.mRange, ∑ n ∈ d.nRange,
        ∑ p' ∈ d.labels x, ∑ r ∈ d.mRange, ∑ s ∈ d.nRange,
          (if ∃ h, 1 ≤ h ∧ m * n - 1 = (∏ i, p i) * h ∧ r * s - 1 = (∏ i, p' i) * h
            then (1 : ℂ) else 0) *
          (cauchyWeight x d Y p m n * star (cauchyWeight x d Y p' r s)) := by
    rw [cauchySquare]
    simp only [Finset.mul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun m _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun n _ => sum_congr rfl fun p' _ =>
      sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
    split_ifs
    · simp only [cauchyWeight, star_mul', Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    · simp
  rw [hQ]
  simp_rw [hsq]
  -- move the sum over `h` innermost and evaluate it
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun p hp => ?_
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun m hm => ?_
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun n hn => ?_
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun p' _ => ?_
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun r _ => ?_
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_mul, sum_ite_ite_eq (hpos p hp)
    (Nat.mul_le_mul (mem_Icc.1 hm).2 (mem_Icc.1 hn).2)]

/-- `T_h` vanishes unless `h ≤ 4X/Y`: a nonzero term has `η(∏ p_i / Y) ≠ 0`, so
`∏ p_i > Y`, and `(∏ p_i) h = mn - 1 < 4X`. -/
theorem le_of_cauchyInner_ne_zero {x : ℝ} {d : Data K} {Y : ℝ} (hY : 0 < Y)
    (hHm : 0 ≤ d.Hm) (hHn : 0 ≤ d.Hn) {h : ℕ} (hT : cauchyInner x d Y h ≠ 0) :
    (h : ℝ) ≤ 4 * d.X / Y := by
  obtain ⟨p, -, hp⟩ := exists_ne_zero_of_sum_ne_zero hT
  obtain ⟨m, hm, hm'⟩ := exists_ne_zero_of_sum_ne_zero hp
  obtain ⟨n, hn, hn'⟩ := exists_ne_zero_of_sum_ne_zero hm'
  by_cases heq : m * n - 1 = (∏ i, p i) * h
  · rw [ite_eq_left heq] at hn'
    have hη : dyadicBump ((∏ i, p i : ℕ) / Y) ≠ 0 := by
      intro h0
      apply hn'
      rw [cauchyWeight, h0]
      simp
    have ha : Y < (∏ i, p i : ℕ) := by
      have := (lt_of_dyadicBump_ne_zero hη).1
      rwa [one_lt_div hY] at this
    -- `(∏ p_i) h ≤ mn ≤ 4 H_m H_n`
    have hm2 : (m : ℝ) ≤ 2 * d.Hm := (Nat.le_floor_iff (by linarith)).1 (mem_Icc.1 hm).2
    have hn2 : (n : ℝ) ≤ 2 * d.Hn := (Nat.le_floor_iff (by linarith)).1 (mem_Icc.1 hn).2
    have hah : ((∏ i, p i : ℕ) : ℝ) * h ≤ m * n := by
      have : (∏ i, p i) * h ≤ m * n := by omega
      exact_mod_cast this
    have hmn : (m : ℝ) * n ≤ 4 * d.X := by
      unfold Data.X
      nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n]
    rw [le_div_iff₀ hY]
    nlinarith [Nat.cast_nonneg (α := ℝ) h]
  · rw [ite_eq_right heq] at hn'
    exact absurd rfl hn'

/-- **The Cauchy step.** For coefficients `|u_h| ≤ 1`,
`|∑_h u_h T_h|² ≤ (4X/Y) Q_Y`. -/
theorem norm_sum_mul_cauchyInner_sq_le {x : ℝ} {d : Data K} {Y : ℝ} (hY : 0 < Y)
    (hHm : 0 ≤ d.Hm) (hHn : 0 ≤ d.Hn) (hpos : ∀ p ∈ d.labels x, 0 < ∏ i, p i)
    (u : ℕ → ℂ) (hu : ∀ h, ‖u h‖ ≤ 1) :
    ‖∑ h ∈ Icc 1 (⌊2 * d.Hm⌋₊ * ⌊2 * d.Hn⌋₊), u h * cauchyInner x d Y h‖ ^ 2 ≤
      4 * d.X / Y * ‖cauchySquare x d Y‖ := by
  set H := Icc 1 (⌊2 * d.Hm⌋₊ * ⌊2 * d.Hn⌋₊)
  set H' := H.filter fun h => cauchyInner x d Y h ≠ 0
  have hX : 0 ≤ 4 * d.X / Y := div_nonneg (by unfold Data.X; positivity) hY.le
  -- `‖Q_Y‖ = ∑_h |T_h|²`
  have hQ : ‖cauchySquare x d Y‖ = ∑ h ∈ H, ‖cauchyInner x d Y h‖ ^ 2 := by
    rw [cauchySquare_eq_sum Y hpos, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sum_nonneg fun h _ => sq_nonneg _)]
  -- only `h ≤ 4X/Y` contribute
  have hcard : (H'.card : ℝ) ≤ 4 * d.X / Y := by
    have hsub : H' ⊆ Icc 1 ⌊4 * d.X / Y⌋₊ := by
      intro h hh
      rw [mem_filter] at hh
      exact mem_Icc.2 ⟨(mem_Icc.1 hh.1).1,
        Nat.le_floor (le_of_cauchyInner_ne_zero hY hHm hHn hh.2)⟩
    calc (H'.card : ℝ) ≤ (Icc 1 ⌊4 * d.X / Y⌋₊).card := by exact_mod_cast card_le_card hsub
      _ = ⌊4 * d.X / Y⌋₊ := by simp
      _ ≤ 4 * d.X / Y := Nat.floor_le hX
  have h₁ : ‖∑ h ∈ H, u h * cauchyInner x d Y h‖ ≤ ∑ h ∈ H', ‖cauchyInner x d Y h‖ := by
    calc ‖∑ h ∈ H, u h * cauchyInner x d Y h‖
        ≤ ∑ h ∈ H, ‖u h * cauchyInner x d Y h‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ H, ‖cauchyInner x d Y h‖ := by
          refine sum_le_sum fun h _ => ?_
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hu h)
      _ = ∑ h ∈ H with ‖cauchyInner x d Y h‖ ≠ 0, ‖cauchyInner x d Y h‖ :=
          (sum_filter_ne_zero _).symm
      _ = ∑ h ∈ H', ‖cauchyInner x d Y h‖ := by simp [H']
  calc ‖∑ h ∈ H, u h * cauchyInner x d Y h‖ ^ 2
      ≤ (∑ h ∈ H', ‖cauchyInner x d Y h‖) ^ 2 := by gcongr
    _ ≤ H'.card * ∑ h ∈ H', ‖cauchyInner x d Y h‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ 4 * d.X / Y * ∑ h ∈ H, ‖cauchyInner x d Y h‖ ^ 2 := by
        gcongr
        exact filter_subset _ _
    _ = 4 * d.X / Y * ‖cauchySquare x d Y‖ := by rw [hQ]

/-! ### The decomposition into dyadic pieces -/

/-- Reindexing by `h = (mn - 1)/∏ p_i`: `∑_h u(h) T_h` is the sum of the weights over the
triples with `∏ p_i ∣ mn - 1`, each multiplied by `u((mn - 1)/∏ p_i)`. -/
theorem sum_mul_cauchyInner {x : ℝ} {d : Data K} (Y : ℝ)
    (hpos : ∀ p ∈ d.labels x, 0 < ∏ i, p i)
    (hmn : ∀ m ∈ d.mRange, ∀ n ∈ d.nRange, 2 ≤ m * n) (u : ℕ → ℂ) :
    ∑ h ∈ Icc 1 (⌊2 * d.Hm⌋₊ * ⌊2 * d.Hn⌋₊), u h * cauchyInner x d Y h =
      ∑ p ∈ d.labels x, ∑ m ∈ d.mRange, ∑ n ∈ d.nRange,
        if (∏ i, p i) ∣ m * n - 1 then
          cauchyWeight x d Y p m n * u ((m * n - 1) / ∏ i, p i)
        else 0 := by
  simp only [cauchyInner, Finset.mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun p hp => ?_
  rw [sum_comm]
  refine sum_congr rfl fun m hm => ?_
  rw [sum_comm]
  refine sum_congr rfl fun n hn => ?_
  have ha := hpos p hp
  have h2 := hmn m hm n hn
  by_cases hdvd : (∏ i, p i) ∣ m * n - 1
  · -- the unique `h` is `(mn - 1)/∏ p_i`
    obtain ⟨h₀, hh₀⟩ := hdvd
    rw [ite_eq_left ⟨h₀, hh₀⟩, hh₀, Nat.mul_div_cancel_left _ ha]
    have h₀1 : 1 ≤ h₀ := by
      rcases Nat.eq_zero_or_pos h₀ with rfl | h
      · omega
      · exact h
    have h₀M : h₀ ≤ ⌊2 * d.Hm⌋₊ * ⌊2 * d.Hn⌋₊ := by
      have : h₀ ≤ (∏ i, p i) * h₀ := Nat.le_mul_of_pos_left _ ha
      have := Nat.mul_le_mul (mem_Icc.1 hm).2 (mem_Icc.1 hn).2
      omega
    rw [sum_eq_single h₀]
    · rw [ite_eq_left rfl, mul_comm]
    · intro h _ hne
      rw [ite_eq_right, mul_zero]
      exact fun heq => hne (Nat.eq_of_mul_eq_mul_left ha heq).symm
    · exact fun hnot => absurd (mem_Icc.2 ⟨h₀1, h₀M⟩) hnot
  · rw [ite_eq_right hdvd]
    refine sum_eq_zero fun h _ => ?_
    rw [ite_eq_right, mul_zero]
    exact fun heq => hdvd ⟨h, heq⟩

/-- The one-sided Type II sum after the label expansion and invariance:
`∑_{m,n,p} ∏V⁻¹ q^{ω(N) - K} [∏ p_i ∣ N] α_m β_n F(N / ∏ p_i)` with `N = mn - 1`. -/
theorem typeIISum_eq_labels {q C CX alo ahi g x : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) :
    typeIISum q x d = ∑ m ∈ d.mRange, ∑ n ∈ d.nRange, ∑ p ∈ d.labels x,
      (((d.bandMass x)⁻¹ * q ^ ((bandCount x d (m * n - 1) : ℤ) - K) : ℝ) : ℂ) *
        (if (∏ i, p i) ∣ m * n - 1 then
          d.α m * d.β n * d.F ((m * n - 1) / ∏ i, p i) else 0) := by
  unfold typeIISum
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
  rw [markedWeight_eq_sum_labels, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum,
    Finset.mul_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [prod_ite_dvd_eq hdisj hp]
  split_ifs with hdvd
  · -- `F(N) = F(N / ∏ p_i)` by invariance
    obtain ⟨h, hh⟩ := hdvd
    have hpos : 0 < ∏ i, p i := by
      rcases Nat.eq_zero_or_pos (∏ i, p i) with h0 | h0
      · rw [h0, zero_mul] at hh
        rw [hh] at *
        exact absurd h0 (by
          rw [prod_eq_zero_iff]; push Not
          exact fun i _ => (mem_filter.1 (Fintype.mem_piFinset.1 hp i)).2.ne_zero)
      · exact h0
    rw [hh, Nat.mul_div_cancel_left _ hpos, F_labelProd_mul hd hp]
    unfold bandCount
    push_cast
    ring
  · simp

/-- The dyadic main terms: with `u(h) = F(h) q^{ω(h)}`, summing `∑_h u(h) T_h` over the
dyadic `Y = 2^j`, `j < J`, gives `∑_{m,n,p} ∏V⁻¹ q^{ω(N/∏ p_i)} [∏ p_i ∣ N] α_m β_n F(N/∏ p_i)`
once every label product lies in `[2, 2^J]`. -/
theorem sum_dyadic_eq {q x : ℝ} {d : Data K} {J : ℕ}
    (hpos : ∀ p ∈ d.labels x, 0 < ∏ i, p i)
    (hJ : ∀ p ∈ d.labels x, 2 ≤ ∏ i, p i ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 ^ J)
    (hmn : ∀ m ∈ d.mRange, ∀ n ∈ d.nRange, 2 ≤ m * n) :
    ∑ j ∈ range J, ∑ h ∈ Icc 1 (⌊2 * d.Hm⌋₊ * ⌊2 * d.Hn⌋₊),
        (d.F h * ((q ^ bandCount x d h : ℝ) : ℂ)) * cauchyInner x d (2 ^ j) h =
      ∑ m ∈ d.mRange, ∑ n ∈ d.nRange, ∑ p ∈ d.labels x,
        (((d.bandMass x)⁻¹ * q ^ bandCount x d ((m * n - 1) / ∏ i, p i) : ℝ) : ℂ) *
          (if (∏ i, p i) ∣ m * n - 1 then
            d.α m * d.β n * d.F ((m * n - 1) / ∏ i, p i) else 0) := by
  simp_rw [sum_mul_cauchyInner _ hpos hmn]
  -- move the dyadic sum innermost and use the partition of unity
  rw [sum_comm]
  have hinner : ∀ p ∈ d.labels x, ∀ m n : ℕ,
      ∑ j ∈ range J, (if (∏ i, p i) ∣ m * n - 1 then
          cauchyWeight x d (2 ^ j) p m n *
            (d.F ((m * n - 1) / ∏ i, p i) *
              ((q ^ bandCount x d ((m * n - 1) / ∏ i, p i) : ℝ) : ℂ))
        else 0) =
      (((d.bandMass x)⁻¹ * q ^ bandCount x d ((m * n - 1) / ∏ i, p i) : ℝ) : ℂ) *
        (if (∏ i, p i) ∣ m * n - 1 then
          d.α m * d.β n * d.F ((m * n - 1) / ∏ i, p i) else 0) := by
    intro p hp m n
    split_ifs
    · simp only [cauchyWeight]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      simp_rw [Complex.ofReal_mul]
      rw [← Finset.mul_sum, ← Complex.ofReal_sum,
        sum_dyadicBump_eq_one (by exact_mod_cast (hJ p hp).1) (hJ p hp).2]
      push_cast
      ring
    · simp
  calc _ = ∑ p ∈ d.labels x, ∑ m ∈ d.mRange, ∑ n ∈ d.nRange,
        (((d.bandMass x)⁻¹ * q ^ bandCount x d ((m * n - 1) / ∏ i, p i) : ℝ) : ℂ) *
          (if (∏ i, p i) ∣ m * n - 1 then
            d.α m * d.β n * d.F ((m * n - 1) / ∏ i, p i) else 0) := by
        refine sum_congr rfl fun p hp => ?_
        rw [sum_comm]
        refine sum_congr rfl fun m _ => ?_
        rw [sum_comm]
        exact sum_congr rfl fun n _ => hinner p hp m n
    _ = _ := by
        rw [sum_comm]
        refine sum_congr rfl fun m _ => ?_
        rw [sum_comm]

/-- **The squareful error** at one pair `(m, n)`, `N = mn - 1`. Replacing `q^{ω(N) - K}` by
`q^{ω(N / ∏ p_i)}` changes nothing unless some label prime divides `N / ∏ p_i`, and then its
square divides `N`. The change is therefore at most
`|α_m| |β_n| (2/(1 - q))^K ∑_{band primes r} [r² ∣ N]`. -/
theorem norm_squareful_le {q C CX alo ahi g x : ℝ} (hq : 0 < q) (hq₁ : q < 1) {d : Data K}
    (hd : Admissible C CX alo ahi g x d)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i))) (m n : ℕ) :
    ‖∑ p ∈ d.labels x,
        ((((d.bandMass x)⁻¹ * q ^ ((bandCount x d (m * n - 1) : ℤ) - K) : ℝ) : ℂ) -
          (((d.bandMass x)⁻¹ * q ^ bandCount x d ((m * n - 1) / ∏ i, p i) : ℝ) : ℂ)) *
        (if (∏ i, p i) ∣ m * n - 1 then
          d.α m * d.β n * d.F ((m * n - 1) / ∏ i, p i) else 0)‖ ≤
      ‖d.α m‖ * ‖d.β n‖ * ((2 / (1 - q)) ^ K *
        ∑ i, ∑ r ∈ band x (d.a i), if r ^ 2 ∣ m * n - 1 then (1 : ℝ) else 0) := by
  set N := m * n - 1
  have hVpos : 0 < (d.bandMass x)⁻¹ :=
    inv_pos.2 (prod_pos fun i _ => by linarith [hV i])
  -- the indicator that some band prime has its square dividing `N`
  set sN : ℝ := if ∃ i, ∃ r ∈ band x (d.a i), r ^ 2 ∣ N then 1 else 0
  have hsN : sN ≤ ∑ i, ∑ r ∈ band x (d.a i), if r ^ 2 ∣ N then (1 : ℝ) else 0 := by
    simp only [sN]
    split_ifs with hex
    · obtain ⟨i, r, hr, hr2⟩ := hex
      calc (1 : ℝ) = if r ^ 2 ∣ N then 1 else 0 := by rw [ite_eq_left hr2]
        _ ≤ ∑ r ∈ band x (d.a i), if r ^ 2 ∣ N then (1 : ℝ) else 0 :=
            single_le_sum (f := fun r => if r ^ 2 ∣ N then (1 : ℝ) else 0)
              (fun r _ => by positivity) hr
        _ ≤ _ := single_le_sum (f := fun i => ∑ r ∈ band x (d.a i),
              if r ^ 2 ∣ N then (1 : ℝ) else 0) (fun i _ => sum_nonneg fun r _ => by positivity)
              (mem_univ i)
    · exact sum_nonneg fun i _ => sum_nonneg fun r _ => by positivity
  -- per label tuple: the change in damping is at most `q^{ω(N) - K} sN`
  have hdiff : ∀ p ∈ d.labels x, (∏ i, p i) ∣ N →
      |q ^ ((bandCount x d N : ℤ) - K) - q ^ bandCount x d (N / ∏ i, p i)| ≤
        q ^ ((bandCount x d N : ℤ) - K) * sN := by
    intro p hp hdvd
    obtain ⟨h, hh⟩ := hdvd
    have hp' : ∀ i, p i ∈ band x (d.a i) := Fintype.mem_piFinset.1 hp
    have hpos : 0 < ∏ i, p i :=
      prod_pos fun i _ => (mem_filter.1 (hp' i)).2.pos
    rw [hh, Nat.mul_div_cancel_left _ hpos]
    by_cases hnd : ∀ i, ¬ p i ∣ h
    · rw [bandCount_labelProd_mul hdisj hp hnd]
      push_cast
      rw [add_sub_cancel_right, zpow_natCast, sub_self, abs_zero]
      exact mul_nonneg (pow_nonneg hq.le _) (by simp only [sN]; split_ifs <;> norm_num)
    · push Not at hnd
      obtain ⟨i, hi⟩ := hnd
      have hs : sN = 1 := by
        refine ite_eq_left ⟨i, p i, hp' i, ?_⟩
        rw [hh, sq]
        exact Nat.mul_dvd_mul (dvd_prod_of_mem p (mem_univ i)) hi
      rw [hs, mul_one]
      -- `0 ≤ q^{ω(h)} ≤ q^{ω(N) - K}`
      have hle := bandCount_labelProd_mul_le hdisj hp h
      have h₁ : q ^ bandCount x d h ≤ q ^ ((bandCount x d ((∏ i, p i) * h) : ℤ) - K) := by
        rw [← zpow_natCast]
        exact zpow_le_zpow_right_of_le_one₀ hq hq₁.le (by omega)
      rw [abs_le]
      constructor <;> nlinarith [pow_nonneg hq.le (bandCount x d h),
        zpow_nonneg hq.le ((bandCount x d ((∏ i, p i) * h) : ℤ) - K)]
  calc _ ≤ ∑ p ∈ d.labels x, ‖((((d.bandMass x)⁻¹ * q ^ ((bandCount x d N : ℤ) - K) : ℝ) : ℂ) -
          (((d.bandMass x)⁻¹ * q ^ bandCount x d (N / ∏ i, p i) : ℝ) : ℂ)) *
        (if (∏ i, p i) ∣ N then d.α m * d.β n * d.F (N / ∏ i, p i) else 0)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ d.labels x, ‖d.α m‖ * ‖d.β n‖ * sN *
          ((d.bandMass x)⁻¹ * q ^ ((bandCount x d N : ℤ) - K) *
            ∏ i, (if p i ∣ N then (1 : ℝ) else 0)) := by
        refine sum_le_sum fun p hp => ?_
        rw [prod_ite_dvd_eq hdisj hp]
        split_ifs with hdvd
        · rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← mul_sub,
            abs_mul, abs_of_pos hVpos, norm_mul, norm_mul]
          have hF : ‖d.F (N / ∏ i, p i)‖ ≤ 1 := hd.F_le _
          have := hdiff p hp hdvd
          calc (d.bandMass x)⁻¹ * |q ^ ((bandCount x d N : ℤ) - K) -
                q ^ bandCount x d (N / ∏ i, p i)| * (‖d.α m‖ * ‖d.β n‖ * ‖d.F (N / ∏ i, p i)‖)
              ≤ (d.bandMass x)⁻¹ * (q ^ ((bandCount x d N : ℤ) - K) * sN) *
                  (‖d.α m‖ * ‖d.β n‖ * 1) := by gcongr
            _ = _ := by ring
        · simp
    _ = ‖d.α m‖ * ‖d.β n‖ * sN * markedWeight Finset.univ q (fun i => band x (d.a i)) N := by
        rw [markedWeight_eq_sum_labels, Finset.mul_sum, Finset.mul_sum]
        refine sum_congr rfl fun p _ => ?_
        simp only [bandCount]
        ring
    _ ≤ ‖d.α m‖ * ‖d.β n‖ * ((2 / (1 - q)) ^ K *
          ∑ i, ∑ r ∈ band x (d.a i), if r ^ 2 ∣ N then (1 : ℝ) else 0) := by
        have hW := markedWeight_le hq hq₁ hV N
        have hW0 : 0 ≤ markedWeight Finset.univ q (fun i => band x (d.a i)) N := by
          rw [TypeII.markedWeight_eq_prod hq.ne']
          exact prod_nonneg fun i _ => TypeII.bandWeight_nonneg hq _ _ _
        have hsN0 : 0 ≤ sN := by simp only [sN]; split_ifs <;> norm_num
        have key : sN * markedWeight Finset.univ q (fun i => band x (d.a i)) N ≤
            (2 / (1 - q)) ^ K *
              ∑ i, ∑ r ∈ band x (d.a i), if r ^ 2 ∣ N then (1 : ℝ) else 0 := by
          rw [mul_comm ((2 / (1 - q)) ^ K)]
          exact mul_le_mul hsN hW hW0 (le_trans hsN0 hsN)
        calc ‖d.α m‖ * ‖d.β n‖ * sN * markedWeight Finset.univ q (fun i => band x (d.a i)) N
            = ‖d.α m‖ * ‖d.β n‖ * (sN * markedWeight Finset.univ q
                (fun i => band x (d.a i)) N) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left key (by positivity)

/-- Exchanging two double sums. -/
theorem sum_comm₄ {α β γ δ M : Type*} [AddCommMonoid M] (A : Finset α) (B : Finset β)
    (C : Finset γ) (D : γ → Finset δ) (f : α → β → γ → δ → M) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ e ∈ D c, f a b c e =
      ∑ c ∈ C, ∑ e ∈ D c, ∑ a ∈ A, ∑ b ∈ B, f a b c e := by
  calc _ = ∑ a ∈ A, ∑ c ∈ C, ∑ e ∈ D c, ∑ b ∈ B, f a b c e := by
        refine sum_congr rfl fun a _ => ?_
        rw [sum_comm]
        exact sum_congr rfl fun c _ => sum_comm
    _ = _ := by
        rw [sum_comm]
        exact sum_congr rfl fun c _ => sum_comm

/-- The squareful error summed over all pairs: at most
`(2/(1 - q))^K K L^{2C} X (8 exp(-L^{a₋}) + 2 exp(2 L^{a₊}) / H_n)`. For each band prime `r`
the pairs with `r² ∣ mn - 1` number at most `|[H_m, 2H_m]| (|[H_n, 2H_n]| / r² + 1)`; then
B4 bounds `∑ 1/r²` and the number of band primes. -/
theorem norm_error_le {q C CX alo ahi g x : ℝ} (hq : 0 < q) (hq₁ : q < 1) {d : Data K}
    (hd : Admissible C CX alo ahi g x d)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i))) (hL : 1 ≤ Real.log x)
    (hHm : 1 ≤ d.Hm) (hHn : 1 ≤ d.Hn) :
    ‖∑ m ∈ d.mRange, ∑ n ∈ d.nRange, ∑ p ∈ d.labels x,
        ((((d.bandMass x)⁻¹ * q ^ ((bandCount x d (m * n - 1) : ℤ) - K) : ℝ) : ℂ) -
          (((d.bandMass x)⁻¹ * q ^ bandCount x d ((m * n - 1) / ∏ i, p i) : ℝ) : ℂ)) *
        (if (∏ i, p i) ∣ m * n - 1 then
          d.α m * d.β n * d.F ((m * n - 1) / ∏ i, p i) else 0)‖ ≤
      (2 / (1 - q)) ^ K * K * Real.log x ^ (2 * C) * d.X *
        (8 * Real.exp (-Real.log x ^ alo) + 2 * Real.exp (2 * Real.log x ^ ahi) / d.Hn) := by
  set L := Real.log x
  set CW : ℝ := (2 / (1 - q)) ^ K
  have hCW : 0 ≤ CW := pow_nonneg (div_nonneg zero_le_two (by linarith)) _
  -- coefficient bounds on the ranges
  have hα : ∀ m, ‖d.α m‖ ≤ L ^ C := fun m => by
    by_cases h : d.α m = 0
    · rw [h, norm_zero]; positivity
    · exact (hd.α_supp m h).2.2.2
  have hβ : ∀ n, ‖d.β n‖ ≤ L ^ C := fun n => by
    by_cases h : d.β n = 0
    · rw [h, norm_zero]; positivity
    · exact (hd.β_supp n h).2.2.2
  -- sizes of the ranges
  have hmR : (d.mRange.card : ℝ) ≤ 2 * d.Hm := by
    unfold Data.mRange
    rw [Nat.card_Icc]
    have h1 := Nat.floor_le (show 0 ≤ 2 * d.Hm by linarith)
    have h2 := Nat.le_ceil d.Hm
    rcases le_or_gt ⌈d.Hm⌉₊ (⌊2 * d.Hm⌋₊ + 1) with h | h
    · rw [Nat.cast_sub h]
      push_cast
      linarith
    · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
      linarith
  have hnR : ((⌊2 * d.Hn⌋₊ + 1 - ⌈d.Hn⌉₊ : ℕ) : ℝ) ≤ 2 * d.Hn := by
    have h1 := Nat.floor_le (show 0 ≤ 2 * d.Hn by linarith)
    have h2 := Nat.le_ceil d.Hn
    rcases le_or_gt ⌈d.Hn⌉₊ (⌊2 * d.Hn⌋₊ + 1) with h | h
    · rw [Nat.cast_sub h]
      push_cast
      linarith
    · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
      linarith
  -- pairs with `r² ∣ mn - 1`, for a band prime `r`
  have hpairs : ∀ i, ∀ r ∈ band x (d.a i), ∑ m ∈ d.mRange, ∑ n ∈ d.nRange,
      (if r ^ 2 ∣ m * n - 1 then (1 : ℝ) else 0) ≤ 2 * d.Hm * (2 * d.Hn / r ^ 2 + 1) := by
    intro i r hr
    have hrpos : 0 < r := (mem_filter.1 hr).2.pos
    calc ∑ m ∈ d.mRange, ∑ n ∈ d.nRange, (if r ^ 2 ∣ m * n - 1 then (1 : ℝ) else 0)
        ≤ ∑ _m ∈ d.mRange, (2 * d.Hn / r ^ 2 + 1) := by
          refine sum_le_sum fun m hm => ?_
          have hm0 : 0 < m := by
            have := (mem_Icc.1 hm).1
            have : 1 ≤ ⌈d.Hm⌉₊ := Nat.one_le_iff_ne_zero.2 (by positivity)
            omega
          rw [← sum_filter, sum_const, nsmul_one]
          have hA : 0 < ⌈d.Hn⌉₊ := by positivity
          calc (((d.nRange.filter fun n => r ^ 2 ∣ m * n - 1).card : ℕ) : ℝ)
              ≤ ((⌊2 * d.Hn⌋₊ + 1 - ⌈d.Hn⌉₊ : ℕ) : ℝ) / ((r ^ 2 : ℕ) : ℝ) + 1 :=
                card_filter_dvd_mul_sub_one_le (by positivity) hm0 hA
            _ ≤ 2 * d.Hn / r ^ 2 + 1 := by
                push_cast
                gcongr
      _ = d.mRange.card * (2 * d.Hn / r ^ 2 + 1) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 * d.Hm * (2 * d.Hn / r ^ 2 + 1) := by gcongr
  -- per band: `∑_r (2H_n/r² + 1) ≤ 4 H_n exp(-L^{a₋}) + exp(2 L^{a₊})`
  have hband : ∀ i, ∑ r ∈ band x (d.a i), (2 * d.Hn / (r : ℝ) ^ 2 + 1) ≤
      4 * d.Hn * Real.exp (-L ^ alo) + Real.exp (2 * L ^ ahi) := by
    intro i
    have ha := hd.window i
    rw [sum_add_distrib, sum_const, nsmul_one]
    have h1 : ∑ r ∈ band x (d.a i), 2 * d.Hn / (r : ℝ) ^ 2 ≤ 4 * d.Hn * Real.exp (-L ^ alo) := by
      calc ∑ r ∈ band x (d.a i), 2 * d.Hn / (r : ℝ) ^ 2
          = 2 * d.Hn * ∑ r ∈ band x (d.a i), 1 / (r : ℝ) ^ 2 := by
            rw [Finset.mul_sum]; exact sum_congr rfl fun r _ => by ring
        _ ≤ 2 * d.Hn * (2 * Real.exp (-L ^ d.a i)) := by
            gcongr; exact sum_band_inv_sq_le x (d.a i)
        _ ≤ 4 * d.Hn * Real.exp (-L ^ alo) := by
            have : Real.exp (-L ^ d.a i) ≤ Real.exp (-L ^ alo) :=
              Real.exp_le_exp.2 (neg_le_neg (Real.rpow_le_rpow_of_exponent_le hL ha.1))
            nlinarith
    have h2 : ((band x (d.a i)).card : ℝ) ≤ Real.exp (2 * L ^ ahi) :=
      (card_band_le x (d.a i)).trans (Real.exp_le_exp.2 (by
        have := Real.rpow_le_rpow_of_exponent_le hL ha.2
        linarith))
    linarith
  calc _ ≤ ∑ m ∈ d.mRange, ∑ n ∈ d.nRange, ‖d.α m‖ * ‖d.β n‖ * (CW *
        ∑ i, ∑ r ∈ band x (d.a i), if r ^ 2 ∣ m * n - 1 then (1 : ℝ) else 0) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
        refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
        exact norm_squareful_le hq hq₁ hd hdisj hV m n
    _ ≤ ∑ m ∈ d.mRange, ∑ n ∈ d.nRange, L ^ C * L ^ C * (CW *
        ∑ i, ∑ r ∈ band x (d.a i), if r ^ 2 ∣ m * n - 1 then (1 : ℝ) else 0) := by
        refine sum_le_sum fun m _ => sum_le_sum fun n _ => ?_
        have : 0 ≤ CW * ∑ i, ∑ r ∈ band x (d.a i), if r ^ 2 ∣ m * n - 1 then (1 : ℝ) else 0 :=
          mul_nonneg hCW (sum_nonneg fun i _ => sum_nonneg fun r _ => by positivity)
        gcongr
        · exact hα m
        · exact hβ n
    _ = L ^ C * L ^ C * CW * ∑ i, ∑ r ∈ band x (d.a i),
          ∑ m ∈ d.mRange, ∑ n ∈ d.nRange, (if r ^ 2 ∣ m * n - 1 then (1 : ℝ) else 0) := by
        simp_rw [Finset.mul_sum]
        rw [sum_comm₄]
        exact sum_congr rfl fun i _ => sum_congr rfl fun r _ => sum_congr rfl fun m _ =>
          sum_congr rfl fun n _ => by ring
    _ ≤ L ^ C * L ^ C * CW * ∑ i, ∑ r ∈ band x (d.a i),
          2 * d.Hm * (2 * d.Hn / (r : ℝ) ^ 2 + 1) := by
        gcongr with i _ r hr
        exact hpairs i r hr
    _ ≤ L ^ C * L ^ C * CW * ∑ _i : Fin K,
          2 * d.Hm * (4 * d.Hn * Real.exp (-L ^ alo) + Real.exp (2 * L ^ ahi)) := by
        gcongr with i
        rw [← Finset.mul_sum]
        gcongr
        exact hband i
    _ = CW * K * L ^ (2 * C) * d.X *
          (8 * Real.exp (-L ^ alo) + 2 * Real.exp (2 * L ^ ahi) / d.Hn) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
          show 2 * C = C + C by ring, Real.rpow_add (by linarith)]
        unfold Data.X
        field_simp
        ring

/-- Interface 1: a bound `Q_Y ≤ C' X Y L^{-D₁}` for every dyadic `Y` bounds the one-sided
Type II sum by `C₁ X L^{-D_*}`. At least one band is needed: with none, every `Q_Y`
vanishes. -/
theorem cauchy_reduction {q C CX alo ahi Dstar g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5) (hK : 1 ≤ K) (hg : 0 < g) (C' : ℝ) :
    ∃ C₁ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      (∀ j : ℕ, ‖cauchySquare x d (2 ^ j)‖ ≤
        C' * d.X * 2 ^ j * Real.log x ^ (-squarePrec Dstar)) →
      ‖typeIISum q x d‖ ≤ C₁ * d.X * Real.log x ^ (-Dstar) := by
  set CW : ℝ := (2 / (1 - q)) ^ K
  have hCW : 0 ≤ CW := pow_nonneg (div_nonneg zero_le_two (by linarith)) _
  have hlog := Real.tendsto_log_atTop
  -- (E1) the number `J` of dyadic scales is at most `L`
  have E1 : ∀ᶠ x : ℝ in atTop, 2 * K * Real.log x ^ ahi / Real.log 2 + 1 ≤ Real.log x := by
    have hc : 0 ≤ 2 * K / Real.log 2 := by positivity
    filter_upwards [((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp hlog).eventually_ge_atTop
      (2 * K / Real.log 2 + 1), hlog.eventually_ge_atTop 1] with x hx hL
    have h45 : 2 * K / Real.log 2 + 1 ≤ Real.log x ^ (4 / 5 : ℝ) := hx
    have h15 : 1 ≤ Real.log x ^ (1 / 5 : ℝ) := Real.one_le_rpow hL (by norm_num)
    have hah : Real.log x ^ ahi ≤ Real.log x ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL hahi.le
    have hsplit : Real.log x = Real.log x ^ (1 / 5 : ℝ) * Real.log x ^ (4 / 5 : ℝ) := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    calc 2 * K * Real.log x ^ ahi / Real.log 2 + 1
        = 2 * K / Real.log 2 * Real.log x ^ ahi + 1 := by ring
      _ ≤ 2 * K / Real.log 2 * Real.log x ^ (1 / 5 : ℝ) + Real.log x ^ (1 / 5 : ℝ) := by
          gcongr
      _ = Real.log x ^ (1 / 5 : ℝ) * (2 * K / Real.log 2 + 1) := by ring
      _ ≤ Real.log x ^ (1 / 5 : ℝ) * Real.log x ^ (4 / 5 : ℝ) := by gcongr
      _ = Real.log x := hsplit.symm
  -- (E2) the squareful error is at most `L^{-D_*}` times `X`
  have E2 : ∀ᶠ x : ℝ in atTop, CW * K * Real.log x ^ (2 * C) *
      (8 * Real.exp (-Real.log x ^ alo) +
        2 * Real.exp (2 * Real.log x ^ ahi) / Real.exp (Real.log x ^ (99 / 100 : ℝ))) ≤
      Real.log x ^ (-Dstar) := by
    set s := 10 * (2 * C + Dstar)
    have hu := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hlog
    have hgap := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 99 / 100 - 1 / 5)).comp hlog
    filter_upwards [((tendsto_exp_div_rpow_atTop s).comp hu).eventually_ge_atTop
      (10 * CW * K + 1), hgap.eventually_ge_atTop 3, hlog.eventually_ge_atTop 1]
      with x hx hg3 hL
    have hg3' : 3 ≤ Real.log x ^ (99 / 100 - 1 / 5 : ℝ) := hg3
    have hL0 : 0 < Real.log x := by linarith
    set u := Real.log x ^ (1 / 10 : ℝ)
    have hu0 : 0 < u := by positivity
    have hx' : 10 * CW * K + 1 ≤ Real.exp u / u ^ s := hx
    -- `u^s = L^{2C + D_*}`
    have hus : u ^ s = Real.log x ^ (2 * C + Dstar) := by
      rw [← Real.rpow_mul hL0.le]; congr 1; ring
    have hexp : 10 * CW * K * Real.log x ^ (2 * C + Dstar) ≤ Real.exp u := by
      rw [← hus]
      have := (le_div_iff₀ (by positivity : 0 < u ^ s)).1 hx'
      nlinarith [Real.rpow_nonneg hu0.le s]
    -- both exponentials are at most `exp(-u)`
    have hu_le : u ≤ Real.log x ^ alo :=
      Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    have h₁ : Real.exp (-Real.log x ^ alo) ≤ Real.exp (-u) := Real.exp_le_exp.2 (by linarith)
    have h₂ : 2 * Real.exp (2 * Real.log x ^ ahi) / Real.exp (Real.log x ^ (99 / 100 : ℝ)) ≤
        2 * Real.exp (-u) := by
      rw [div_le_iff₀ (Real.exp_pos _), mul_assoc, ← Real.exp_add]
      gcongr
      -- `2 L^{a₊} + L^{1/10} ≤ L^{0.99}`
      have hah : Real.log x ^ ahi ≤ Real.log x ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL hahi.le
      have hu15 : u ≤ Real.log x ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      have hsplit : Real.log x ^ (99 / 100 : ℝ) =
          Real.log x ^ (1 / 5 : ℝ) * Real.log x ^ (99 / 100 - 1 / 5 : ℝ) := by
        rw [← Real.rpow_add hL0]; norm_num
      have h15 : 0 ≤ Real.log x ^ (1 / 5 : ℝ) := by positivity
      have h3 : 3 * Real.log x ^ (1 / 5 : ℝ) ≤ Real.log x ^ (99 / 100 : ℝ) := by
        rw [hsplit]; nlinarith
      linarith
    have hLD : Real.log x ^ (2 * C) * Real.log x ^ Dstar = Real.log x ^ (2 * C + Dstar) :=
      (Real.rpow_add hL0 _ _).symm
    have hLn : Real.log x ^ (-Dstar) * Real.log x ^ Dstar = 1 := by
      rw [← Real.rpow_add hL0]; simp
    have hDpos : 0 < Real.log x ^ Dstar := by positivity
    rw [← mul_le_mul_iff_of_pos_right hDpos, hLn]
    calc CW * K * Real.log x ^ (2 * C) * (8 * Real.exp (-Real.log x ^ alo) +
          2 * Real.exp (2 * Real.log x ^ ahi) / Real.exp (Real.log x ^ (99 / 100 : ℝ))) *
          Real.log x ^ Dstar
        ≤ CW * K * Real.log x ^ (2 * C) * (8 * Real.exp (-u) + 2 * Real.exp (-u)) *
            Real.log x ^ Dstar := by gcongr
      _ = 10 * CW * K * Real.log x ^ (2 * C + Dstar) * Real.exp (-u) := by
          rw [← hLD]; ring
      _ ≤ Real.exp u * Real.exp (-u) := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  -- (E3) `exp(L^{0.99}) ≥ 2`
  have E3 : ∀ᶠ x : ℝ in atTop, 2 ≤ Real.exp (Real.log x ^ (99 / 100 : ℝ)) := by
    filter_upwards [((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 99 / 100)).comp
      hlog).eventually_ge_atTop 1] with x hx
    have hx' : (1 : ℝ) ≤ Real.log x ^ (99 / 100 : ℝ) := hx
    linarith [Real.add_one_le_exp (Real.log x ^ (99 / 100 : ℝ))]
  refine ⟨2 * Real.sqrt |C'| + 1, ?_⟩
  filter_upwards [eventually_band_disjoint hg, eventually_harmonicMass_band halo.le, E1, E2, E3,
    hlog.eventually_ge_atTop 1, eventually_ge_atTop 1] with x hE1 hE2 hJL hE2' hE3 hL hx1
  intro d hd hQ
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  -- the bands are disjoint and have mass at least `1/2`
  have hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hE1 _ _ (hd.gap i j h)
    · exact (hE1 _ _ (hd.gap j i h)).symm
  have hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) := fun i => (hE2 _ (hd.window i).1).1
  -- the scales are at least `exp(L^{0.99}) ≥ 2`
  have hγx : Real.exp (L ^ (99 / 100 : ℝ)) ≤ x ^ d.γ := by
    rw [Real.rpow_def_of_pos (show (0 : ℝ) < x by linarith) d.γ, Real.exp_le_exp]
    calc L ^ (99 / 100 : ℝ) = L * L ^ (-(1 / 100) : ℝ) := by
          rw [← Real.rpow_one_add' hL0.le (by norm_num)]; norm_num
      _ ≤ L * d.γ := by gcongr; exact hd.γ_ge
  have hHm : Real.exp (L ^ (99 / 100 : ℝ)) ≤ d.Hm := hγx.trans hd.Hm_ge
  have hHn : Real.exp (L ^ (99 / 100 : ℝ)) ≤ d.Hn := hγx.trans hd.Hn_ge
  have hX : 0 < d.X := by unfold Data.X; nlinarith
  -- the label products lie in `[2, 2^J]`
  set J := ⌈2 * K * L ^ ahi / Real.log 2⌉₊
  have hlabel : ∀ p ∈ d.labels x, 2 ≤ ∏ i, p i ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 ^ J := by
    intro p hp
    have hp' : ∀ i, p i ∈ band x (d.a i) := Fintype.mem_piFinset.1 hp
    have hprime : ∀ i, (p i).Prime := fun i => (mem_filter.1 (hp' i)).2
    constructor
    · calc 2 ≤ p ⟨0, hK⟩ := (hprime _).two_le
        _ ≤ ∏ i, p i := Finset.single_le_prod (fun i _ => (hprime i).one_lt.le) (mem_univ _)
    · rw [Nat.cast_prod]
      refine (labelProduct_bounds hp').2.trans ?_
      have hsum : ∑ i, L ^ d.a i ≤ K * L ^ ahi := by
        calc ∑ i, L ^ d.a i ≤ ∑ _i : Fin K, L ^ ahi :=
              sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_le hL (hd.window i).2
          _ = K * L ^ ahi := by simp
      calc Real.exp (2 * ∑ i, L ^ d.a i) ≤ Real.exp (J * Real.log 2) := by
            rw [Real.exp_le_exp]
            have := Nat.le_ceil (2 * K * L ^ ahi / Real.log 2)
            rw [div_le_iff₀ (Real.log_pos one_lt_two)] at this
            linarith
        _ = 2 ^ J := by rw [← Real.rpow_natCast, Real.rpow_def_of_pos two_pos, mul_comm]
  have hpos : ∀ p ∈ d.labels x, 0 < ∏ i, p i := fun p hp => by linarith [(hlabel p hp).1]
  have hmn : ∀ m ∈ d.mRange, ∀ n ∈ d.nRange, 2 ≤ m * n := by
    intro m hm n hn
    have h1 : 2 ≤ m := by
      have := (mem_Icc.1 hm).1
      have h2 : (2 : ℝ) ≤ ⌈d.Hm⌉₊ := (hE3.trans hHm).trans (Nat.le_ceil _)
      have : 2 ≤ ⌈d.Hm⌉₊ := by exact_mod_cast h2
      omega
    have h2 : 1 ≤ n := by
      have := (mem_Icc.1 hn).1
      have : 1 ≤ ⌈d.Hn⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne'
      omega
    nlinarith
  -- the decomposition: dyadic main terms plus the squareful error
  set u : ℕ → ℂ := fun h => d.F h * ((q ^ bandCount x d h : ℝ) : ℂ)
  set S := ∑ j ∈ range J, ∑ h ∈ Icc 1 (⌊2 * d.Hm⌋₊ * ⌊2 * d.Hn⌋₊), u h * cauchyInner x d (2 ^ j) h
  set E := ∑ m ∈ d.mRange, ∑ n ∈ d.nRange, ∑ p ∈ d.labels x,
    ((((d.bandMass x)⁻¹ * q ^ ((bandCount x d (m * n - 1) : ℤ) - K) : ℝ) : ℂ) -
      (((d.bandMass x)⁻¹ * q ^ bandCount x d ((m * n - 1) / ∏ i, p i) : ℝ) : ℂ)) *
    (if (∏ i, p i) ∣ m * n - 1 then d.α m * d.β n * d.F ((m * n - 1) / ∏ i, p i) else 0)
  have hdecomp : typeIISum q x d = S + E := by
    have hS2 : S = _ := sum_dyadic_eq (q := q) hpos hlabel hmn
    rw [typeIISum_eq_labels hd hdisj, hS2]
    simp only [E, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => sum_congr rfl fun p _ => ?_
    ring
  -- the error
  have hE : ‖E‖ ≤ d.X * L ^ (-Dstar) := by
    have h₁ := norm_error_le hq hq₁ hd hdisj hV hL (by linarith) (by linarith)
    have h₂ : 2 * Real.exp (2 * L ^ ahi) / d.Hn ≤
        2 * Real.exp (2 * L ^ ahi) / Real.exp (L ^ (99 / 100 : ℝ)) := by gcongr
    calc ‖E‖ ≤ CW * K * L ^ (2 * C) * d.X *
          (8 * Real.exp (-L ^ alo) + 2 * Real.exp (2 * L ^ ahi) / d.Hn) := h₁
      _ ≤ CW * K * L ^ (2 * C) * d.X *
          (8 * Real.exp (-L ^ alo) + 2 * Real.exp (2 * L ^ ahi) / Real.exp (L ^ (99 / 100 : ℝ))) := by
          gcongr
      _ = CW * K * L ^ (2 * C) *
          (8 * Real.exp (-L ^ alo) + 2 * Real.exp (2 * L ^ ahi) / Real.exp (L ^ (99 / 100 : ℝ))) *
            d.X := by ring
      _ ≤ L ^ (-Dstar) * d.X := by gcongr
      _ = d.X * L ^ (-Dstar) := mul_comm _ _
  -- each dyadic main term is at most `2 √|C'| X L^{-D_* - 1}`
  have hSj : ∀ j : ℕ, ‖∑ h ∈ Icc 1 (⌊2 * d.Hm⌋₊ * ⌊2 * d.Hn⌋₊), u h * cauchyInner x d (2 ^ j) h‖ ≤
      2 * Real.sqrt |C'| * d.X * L ^ (-(Dstar + 1)) := by
    intro j
    have hu : ∀ h, ‖u h‖ ≤ 1 := fun h => by
      simp only [u, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg hq.le _)]
      calc ‖d.F h‖ * q ^ bandCount x d h ≤ 1 * 1 :=
            mul_le_mul (hd.F_le h) (pow_le_one₀ hq.le hq₁.le) (pow_nonneg hq.le _) zero_le_one
        _ = 1 := one_mul 1
    have h₁ := norm_sum_mul_cauchyInner_sq_le (pow_pos two_pos j) (by linarith) (by linarith)
      hpos u hu
    have h₂ := hQ j
    have hb : 0 ≤ 2 * Real.sqrt |C'| * d.X * L ^ (-(Dstar + 1)) := by positivity
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) hb two_ne_zero).1 ?_
    calc _ ≤ 4 * d.X / 2 ^ j * ‖cauchySquare x d (2 ^ j)‖ := h₁
      _ ≤ 4 * d.X / 2 ^ j * (|C'| * d.X * 2 ^ j * L ^ (-squarePrec Dstar)) := by
          gcongr
          exact h₂.trans (by gcongr; exact le_abs_self _)
      _ = (2 * Real.sqrt |C'| * d.X * L ^ (-(Dstar + 1))) ^ 2 := by
          have hL2 : (L ^ (-(Dstar + 1))) ^ 2 = L ^ (-squarePrec Dstar) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, squarePrec]
            congr 1
            push_cast
            ring
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (abs_nonneg _), hL2]
          field_simp
          ring
  have hS : ‖S‖ ≤ 2 * Real.sqrt |C'| * d.X * L ^ (-Dstar) := by
    calc ‖S‖ ≤ ∑ j ∈ range J, 2 * Real.sqrt |C'| * d.X * L ^ (-(Dstar + 1)) :=
          (norm_sum_le _ _).trans (sum_le_sum fun j _ => hSj j)
      _ = J * (2 * Real.sqrt |C'| * d.X * L ^ (-(Dstar + 1))) := by simp
      _ ≤ L * (2 * Real.sqrt |C'| * d.X * L ^ (-(Dstar + 1))) := by
          gcongr
          have := Nat.ceil_lt_add_one (show 0 ≤ 2 * K * L ^ ahi / Real.log 2 by positivity)
          linarith
      _ = 2 * Real.sqrt |C'| * d.X * L ^ (-Dstar) := by
          rw [show -Dstar = 1 + -(Dstar + 1) by ring, Real.rpow_add hL0, Real.rpow_one]
          ring
  calc ‖typeIISum q x d‖ = ‖S + E‖ := by rw [hdecomp]
    _ ≤ ‖S‖ + ‖E‖ := norm_add_le _ _
    _ ≤ 2 * Real.sqrt |C'| * d.X * L ^ (-Dstar) + d.X * L ^ (-Dstar) := add_le_add hS hE
    _ = (2 * Real.sqrt |C'| + 1) * d.X * L ^ (-Dstar) := by ring

end Erdos408.OneSided
