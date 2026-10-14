module

public import Erdos408.Extraction.Allocation.Failure.Bonferroni
public import Erdos408.Extraction.Allocation.Failure.Residues

/-!
# Rough numbers in residue classes

The relative residue estimate of E6 for one factor, by Bonferroni at depth `R`
over the sifting primes `S` (in practice the primes up to `Y`).

Let `U ⊆ S` and `c` prime to `U`. Among `e ∈ (A, t]` with no prime factor in
`S`, those with `e c ≡ 1` modulo every `p ∈ U` number
`(t - A) Π / φ_U + O((t - A) ε / φ_U + N)`, where `Π = ∏_{p ∈ S} (1 - 1/p)`,
`φ_U = ∏_{p ∈ U} (p - 1)`, `ε = ∑_{u ⊆ S, |u| = R + 1} 1/∏u` is the omitted
envelope and `N = #{u ⊆ S : |u| ≤ R + 1}` counts the roundings.

By partial summation against a decreasing weight `w` with `w(A + 1) ≤ K w(e)`
on `(A, B]`, the weighted sums `S_U` satisfy
`|S_U - S_∅ / φ_U| ≤ δ S_∅ / φ_U + 4 N w(A + 1)` with `δ = 8 ε K / Π`.
-/

@[expose] public section

namespace Erdos408

open Finset

/-! ### Swapping the divisor sums -/

/-- `∑_e [Q e] ∑_{u ⊆ s(e), B u} F u = ∑_{u ⊆ P, B u} F u #{e : Q e, u ∣ e}`, where `s(e)` is the
set of primes of `P` dividing `e`. -/
private lemma sum_ite_sum_powerset_filter_dvd (s P : Finset ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (B : Finset ℕ → Prop) [DecidablePred B] (F : Finset ℕ → ℝ) :
    ∑ e ∈ s, (if Q e then ∑ u ∈ (P.filter (· ∣ e)).powerset with B u, F u else 0) =
      ∑ u ∈ P.powerset with B u, F u * ((s.filter fun e => Q e ∧ ∀ p ∈ u, p ∣ e).card : ℝ) := by
  have hpow : ∀ e, (P.filter (· ∣ e)).powerset = P.powerset.filter fun u => ∀ p ∈ u, p ∣ e := by
    intro e
    ext u
    simp only [mem_powerset, mem_filter, subset_iff]
    exact ⟨fun h => ⟨fun p hp => (h hp).1, fun p hp => (h hp).2⟩,
      fun h p hp => ⟨h.1 hp, h.2 p hp⟩⟩
  have hL : ∀ e ∈ s, (if Q e then ∑ u ∈ (P.filter (· ∣ e)).powerset with B u, F u else 0) =
      ∑ u ∈ P.powerset, (if Q e ∧ (∀ p ∈ u, p ∣ e) ∧ B u then F u else 0) := by
    intro e _
    rw [hpow, filter_filter, sum_filter]
    split_ifs with hQ
    · refine sum_congr rfl fun u _ => ?_
      by_cases hB : B u <;> by_cases hd : ∀ p ∈ u, p ∣ e <;> simp [hB, hd, hQ]
    · exact (sum_eq_zero fun u _ => by simp [hQ]).symm
  have hR : ∀ u ∈ P.powerset.filter B,
      F u * ((s.filter fun e => Q e ∧ ∀ p ∈ u, p ∣ e).card : ℝ) =
        ∑ e ∈ s, (if Q e ∧ (∀ p ∈ u, p ∣ e) ∧ B u then F u else 0) := by
    intro u hu
    have hB := (mem_filter.1 hu).2
    rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, mul_sum, sum_filter]
    refine sum_congr rfl fun e _ => ?_
    by_cases hQ : Q e <;> by_cases hd : ∀ p ∈ u, p ∣ e <;> simp [hB, hd, hQ]
  rw [sum_congr rfl hL, sum_congr rfl hR, sum_comm, sum_filter]
  refine sum_congr rfl fun u _ => ?_
  split_ifs with hB
  · rfl
  · exact sum_eq_zero fun e _ => by simp [hB]

/-! ### The count of rough numbers -/

/-- The integers of `(A, t]` with `e c ≡ 1` modulo every `p ∈ U` and divisible by every `p ∈ u`
number `(t - A) / (∏_U p ∏_u p) + O(1)`. -/
private lemma abs_card_cong_dvd_sub_le {U u : Finset ℕ} (hU : ∀ p ∈ U, p.Prime)
    (hu : ∀ p ∈ u, p.Prime) (hUu : Disjoint U u) {c : ℕ} (hc : ∀ p ∈ U, ¬ p ∣ c)
    {A t : ℕ} (hAt : A ≤ t) :
    |((((Ioc A t).filter fun e => (∀ p ∈ U, e * c ≡ 1 [MOD p]) ∧ ∀ p ∈ u, p ∣ e).card : ℕ) : ℝ) -
        ((t : ℝ) - A) / ((∏ p ∈ U, (p : ℝ)) * ∏ p ∈ u, (p : ℝ))| ≤ 1 := by
  -- inverses of `c` modulo the primes of `U`
  have hinv : ∀ p ∈ U, ∃ m, c * m ≡ 1 [MOD p] := by
    intro p hp
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hU p hp)).2 (hc p hp)))
      (hU p hp).one_lt
    exact ⟨m, by rw [Nat.ModEq, hm, Nat.mod_eq_of_lt (hU p hp).one_lt]⟩
  choose! m hm using hinv
  set a : ℕ → ℕ := fun p => if p ∈ U then m p else 0
  have hV : ∀ p ∈ U ∪ u, p.Prime := fun p hp => (mem_union.1 hp).elim (hU p) (hu p)
  have h := abs_card_filter_forall_modEq_sub_le (U ∪ u) hV a hAt
  have hfilt : ((Ioc A t).filter fun e => (∀ p ∈ U, e * c ≡ 1 [MOD p]) ∧ ∀ p ∈ u, p ∣ e) =
      (Ioc A t).filter fun e => ∀ p ∈ U ∪ u, e ≡ a p [MOD p] := by
    refine filter_congr fun e _ => ?_
    rw [forall_mem_union]
    refine and_congr (forall₂_congr fun p hp => ?_) (forall₂_congr fun p hp => ?_)
    · simp only [a, hp, ↓reduceIte]
      constructor
      · intro h
        calc e ≡ e * (c * m p) [MOD p] := by
              simpa using (Nat.ModEq.mul_left e (hm p hp)).symm
          _ = e * c * m p := by ring
          _ ≡ 1 * m p [MOD p] := Nat.ModEq.mul_right _ h
          _ = m p := one_mul _
      · intro h
        calc e * c ≡ m p * c [MOD p] := Nat.ModEq.mul_right _ h
          _ = c * m p := mul_comm _ _
          _ ≡ 1 [MOD p] := hm p hp
    · have hpU : p ∉ U := fun h => disjoint_left.1 hUu h hp
      simp only [a, hpU, ↓reduceIte]
      exact Nat.modEq_zero_iff_dvd.symm
  rw [hfilt, ← prod_union hUu]
  exact h

/-- The sifted count: among the `e ∈ (A, t]` free of the primes of `S`, those with `e c ≡ 1`
modulo every `p ∈ U` number `(t - A) Π / φ_U` up to `2 (t - A) ε / φ_U + N`. -/
theorem abs_card_rough_cong_sub_le (S U : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hUS : U ⊆ S)
    {c : ℕ} (hc : ∀ p ∈ U, ¬ p ∣ c) (R : ℕ) {A t : ℕ} (hAt : A ≤ t) :
    |((((Ioc A t).filter fun e => (∀ p ∈ S, ¬ p ∣ e) ∧ ∀ p ∈ U, e * c ≡ 1 [MOD p]).card : ℕ) : ℝ) -
        ((t : ℝ) - A) * (∏ p ∈ S, (1 - (1 : ℝ) / p)) / ∏ p ∈ U, ((p : ℝ) - 1)| ≤
      2 * ((t : ℝ) - A) * (∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) /
          (∏ p ∈ U, ((p : ℝ) - 1)) +
        ((S.powerset.filter (·.card ≤ R + 1)).card : ℝ) := by
  classical
  set P' := S \ U with hP'
  have hU : ∀ p ∈ U, p.Prime := fun p hp => hS p (hUS hp)
  have hP'pr : ∀ p ∈ P', p.Prime := fun p hp => hS p (mem_sdiff.1 hp).1
  set cong : ℕ → Prop := fun e => ∀ p ∈ U, e * c ≡ 1 [MOD p] with hcong
  set tA : ℝ := (t : ℝ) - A with htA
  have htA0 : 0 ≤ tA := by rw [htA, sub_nonneg]; exact_mod_cast hAt
  set qU : ℝ := ∏ p ∈ U, (p : ℝ) with hqU
  set φU : ℝ := ∏ p ∈ U, ((p : ℝ) - 1) with hφU
  have hφU1 : 1 ≤ φU := one_le_prod₀ fun p hp => by
    have := (hU p hp).two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast this
    linarith
  have hqφ : φU ≤ qU := prod_le_prod₀ (fun p hp => by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (hU p hp).two_le
      linarith) fun p _ => by linarith
  have hqU0 : 0 < qU := by linarith
  -- a congruent `e` is prime to `U`, so roughness only concerns `P'`
  have hrough : ∀ e, cong e → ((∀ p ∈ S, ¬ p ∣ e) ↔ P'.filter (· ∣ e) = ∅) := by
    intro e he
    rw [filter_eq_empty_iff]
    constructor
    · exact fun h p hp => h p (mem_sdiff.1 hp).1
    · intro h p hp hpe
      by_cases hpU : p ∈ U
      · have h1 : e * c ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.2 (dvd_mul_of_dvd_left hpe c)
        have h2 := (he p hpU).symm.trans h1
        rw [Nat.ModEq, Nat.zero_mod, Nat.mod_eq_of_lt (hU p hpU).one_lt] at h2
        exact one_ne_zero h2
      · exact h (mem_sdiff.2 ⟨hp, hpU⟩) hpe
  -- the count as a sum of indicators
  set Cu : Finset ℕ → ℝ := fun u =>
    ((((Ioc A t).filter fun e => cong e ∧ ∀ p ∈ u, p ∣ e).card : ℕ) : ℝ) with hCu
  have hcount : ((((Ioc A t).filter fun e => (∀ p ∈ S, ¬ p ∣ e) ∧ cong e).card : ℕ) : ℝ) =
      ∑ e ∈ Ioc A t, (if cong e then (if P'.filter (· ∣ e) = ∅ then (1 : ℝ) else 0) else 0) := by
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    refine sum_congr rfl fun e _ => ?_
    by_cases he : cong e
    · simp only [he, and_true, ↓reduceIte, hrough e he, Nat.cast_one]
    · simp [he]
  have hmain : ∑ e ∈ Ioc A t, (if cong e then
      ∑ u ∈ (P'.filter (· ∣ e)).powerset with u.card ≤ R, (-1 : ℝ) ^ u.card else 0) =
      ∑ u ∈ P'.powerset with u.card ≤ R, (-1 : ℝ) ^ u.card * Cu u :=
    sum_ite_sum_powerset_filter_dvd _ _ _ _ _
  have henv : ∑ e ∈ Ioc A t, (if cong e then
      ∑ u ∈ (P'.filter (· ∣ e)).powerset with u.card = R + 1, (1 : ℝ) else 0) =
      ∑ u ∈ P'.powerset with u.card = R + 1, 1 * Cu u :=
    sum_ite_sum_powerset_filter_dvd _ _ _ _ _
  -- pointwise Bonferroni, summed
  have hbon : |((((Ioc A t).filter fun e => (∀ p ∈ S, ¬ p ∣ e) ∧ cong e).card : ℕ) : ℝ) -
      ∑ u ∈ P'.powerset with u.card ≤ R, (-1 : ℝ) ^ u.card * Cu u| ≤
      ∑ u ∈ P'.powersetCard (R + 1), Cu u := by
    rw [hcount, ← hmain, powersetCard_eq_filter]
    have : ∑ u ∈ P'.powerset with u.card = R + 1, Cu u =
        ∑ u ∈ P'.powerset with u.card = R + 1, 1 * Cu u := by simp
    rw [this, ← henv, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e _ => ?_)
    by_cases he : cong e
    · simp only [he, ↓reduceIte, sum_const, nsmul_eq_mul, mul_one]
      have := abs_ite_sub_sum_powerset_le (P'.filter (· ∣ e)) R
      rwa [powersetCard_eq_filter] at this
    · simp [he]
  -- each `C_u` is `tA / (q_U ∏ u) + O(1)`
  have hCu_approx : ∀ u ∈ P'.powerset, |Cu u - tA / (qU * ∏ p ∈ u, (p : ℝ))| ≤ 1 := by
    intro u hu
    have hu' := mem_powerset.1 hu
    exact abs_card_cong_dvd_sub_le hU (fun p hp => hP'pr p (hu' hp))
      (disjoint_left.2 fun p hpU hpu => (mem_sdiff.1 (hu' hpu)).2 hpU) hc hAt
  have hrecip : ∀ u : Finset ℕ, tA / (qU * ∏ p ∈ u, (p : ℝ)) = tA / qU * ∏ p ∈ u, (1 : ℝ) / p := by
    intro u
    rw [prod_div_distrib, prod_const_one]
    field_simp
  -- the main terms
  set ε' := ∑ u ∈ P'.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p with hε'
  have hx : ∀ p ∈ P', 0 ≤ (1 : ℝ) / p ∧ (1 : ℝ) / p ≤ 1 := fun p hp => by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (hP'pr p hp).one_lt.le
    exact ⟨by positivity, by rw [div_le_one (by linarith)]; exact this⟩
  have hprod := abs_prod_one_sub_sub_sum_le P' R (fun p => (1 : ℝ) / p) hx
  have hround : |∑ u ∈ P'.powerset with u.card ≤ R, (-1 : ℝ) ^ u.card * Cu u -
      tA / qU * ∑ u ∈ P'.powerset with u.card ≤ R, (-1 : ℝ) ^ u.card * ∏ p ∈ u, (1 : ℝ) / p| ≤
      ((P'.powerset.filter (·.card ≤ R)).card : ℝ) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine sum_le_sum fun u hu => ?_
    rw [show tA / qU * ((-1 : ℝ) ^ u.card * ∏ p ∈ u, (1 : ℝ) / p) =
      (-1 : ℝ) ^ u.card * (tA / (qU * ∏ p ∈ u, (p : ℝ))) by rw [hrecip]; ring, ← mul_sub,
      abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hCu_approx u (mem_filter.1 hu).1
  have henv' : ∑ u ∈ P'.powersetCard (R + 1), Cu u ≤
      tA / qU * ε' + ((P'.powersetCard (R + 1)).card : ℝ) := by
    rw [hε', mul_sum, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, ← sum_add_distrib]
    refine sum_le_sum fun u hu => ?_
    have := (abs_le.1 (hCu_approx u (mem_powerset.2 (mem_powersetCard.1 hu).1))).2
    rw [hrecip] at this
    linarith
  -- assembling
  have hPi : tA / qU * ∏ p ∈ P', (1 - (1 : ℝ) / p) = tA * (∏ p ∈ S, (1 - (1 : ℝ) / p)) / φU := by
    rw [← prod_sdiff hUS, hφU, hqU]
    have hφ0 : ∏ p ∈ U, ((p : ℝ) - 1) ≠ 0 := by linarith
    have hq0 : ∏ p ∈ U, (p : ℝ) ≠ 0 := by linarith
    have hloc : (∏ p ∈ U, (1 - (1 : ℝ) / p)) * ∏ p ∈ U, (p : ℝ) = ∏ p ∈ U, ((p : ℝ) - 1) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun p hp => ?_
      have : (p : ℝ) ≠ 0 := by exact_mod_cast (hU p hp).ne_zero
      field_simp
    have hne : ∏ p ∈ U, (1 - (1 : ℝ) / p) ≠ 0 := prod_ne_zero_iff.2 fun p hp => by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (hU p hp).two_le
      have : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    rw [← hloc]
    field_simp
    rfl
  have hε'ε : ε' ≤ ∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p :=
    sum_le_sum_of_subset_of_nonneg (powersetCard_mono sdiff_subset) fun u hu _ =>
      prod_nonneg fun p _ => by positivity
  have hε'0 : 0 ≤ ε' := sum_nonneg fun u _ => prod_nonneg fun p _ => by positivity
  have hcards : ((P'.powerset.filter (·.card ≤ R)).card : ℝ) +
      ((P'.powersetCard (R + 1)).card : ℝ) ≤ ((S.powerset.filter (·.card ≤ R + 1)).card : ℝ) := by
    rw [← Nat.cast_add, ← card_union_of_disjoint]
    · refine Nat.cast_le.2 (card_le_card fun u hu => ?_)
      rcases mem_union.1 hu with hu | hu
      · obtain ⟨hu, hc⟩ := mem_filter.1 hu
        exact mem_filter.2 ⟨mem_powerset.2 ((mem_powerset.1 hu).trans sdiff_subset), by omega⟩
      · obtain ⟨hu, hc⟩ := mem_powersetCard.1 hu
        exact mem_filter.2 ⟨mem_powerset.2 (hu.trans sdiff_subset), by omega⟩
    · rw [disjoint_left]
      intro u hu hu'
      have := (mem_filter.1 hu).2
      have := (mem_powersetCard.1 hu').2
      omega
  have hqε : tA / qU * ε' ≤ tA * (∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) / φU := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hqU0 (by linarith)]
    have := mul_le_mul hε'ε hqφ (by linarith) (sum_nonneg fun u _ => prod_nonneg fun p _ =>
      by positivity)
    nlinarith
  have hfin := abs_sub_le (((((Ioc A t).filter fun e => (∀ p ∈ S, ¬ p ∣ e) ∧ cong e).card : ℕ) :
    ℝ)) (∑ u ∈ P'.powerset with u.card ≤ R, (-1 : ℝ) ^ u.card * Cu u)
    (tA / qU * ∏ p ∈ P', (1 - (1 : ℝ) / p))
  have hfin2 := abs_sub_le (∑ u ∈ P'.powerset with u.card ≤ R, (-1 : ℝ) ^ u.card * Cu u)
    (tA / qU * ∑ u ∈ P'.powerset with u.card ≤ R, (-1 : ℝ) ^ u.card * ∏ p ∈ u, (1 : ℝ) / p)
    (tA / qU * ∏ p ∈ P', (1 - (1 : ℝ) / p))
  have hfin3 : |tA / qU * ∑ u ∈ P'.powerset with u.card ≤ R, (-1 : ℝ) ^ u.card *
      ∏ p ∈ u, (1 : ℝ) / p - tA / qU * ∏ p ∈ P', (1 - (1 : ℝ) / p)| ≤ tA / qU * ε' := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity), abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hprod (by positivity)
  rw [← hPi]
  have h2 : 2 * tA * (∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) / φU =
      2 * (tA * (∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) / φU) := by ring
  rw [h2]
  linarith

/-! ### Partial summation -/

/-- `(A, n + 1] = (A, n] ∪ {n + 1}` for `A ≤ n`. -/
lemma Ioc_succ_right_eq_insert {A n : ℕ} (h : A ≤ n) :
    Ioc A (n + 1) = insert (n + 1) (Ioc A n) := by
  ext e
  simp only [mem_Ioc, mem_insert]
  omega

/-- Partial summation against a decreasing nonnegative weight: if the partial sums of `f` over
`(A, t]`, `t ≤ B`, are at most `η` in size, then `|∑_{(A, B]} f w| ≤ η w(A + 1)`. -/
lemma abs_sum_Ioc_mul_le {f w : ℕ → ℝ} {A B : ℕ} (hAB : A ≤ B) {η : ℝ}
    (hf : ∀ t, A ≤ t → t ≤ B → |∑ e ∈ Ioc A t, f e| ≤ η)
    (hw0 : ∀ e, A < e → 0 ≤ w e) (hw : ∀ e, A < e → w (e + 1) ≤ w e) :
    |∑ e ∈ Ioc A B, f e * w e| ≤ η * w (A + 1) := by
  set F : ℕ → ℝ := fun t => ∑ e ∈ Ioc A t, f e
  have key : ∀ n, A + n ≤ B → |∑ e ∈ Ioc A (A + n), f e * w e - F (A + n) * w (A + n + 1)| ≤
      η * (w (A + 1) - w (A + n + 1)) := by
    intro n
    induction n with
    | zero => intro _; simp [F]
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have hF : F (A + (n + 1)) = F (A + n) + f (A + n + 1) := by
        simp only [F, ← add_assoc]
        rw [Ioc_succ_right_eq_insert (by omega), sum_insert (by simp)]
        ring
      have hS : ∑ e ∈ Ioc A (A + (n + 1)), f e * w e =
          ∑ e ∈ Ioc A (A + n), f e * w e + f (A + n + 1) * w (A + n + 1) := by
        rw [← add_assoc, Ioc_succ_right_eq_insert (by omega), sum_insert (by simp)]
        ring
      have hFb := hf (A + (n + 1)) (by omega) hn
      have hdec := hw (A + n + 1) (by omega)
      have hsplit : ∑ e ∈ Ioc A (A + (n + 1)), f e * w e - F (A + (n + 1)) * w (A + (n + 1) + 1) =
          (∑ e ∈ Ioc A (A + n), f e * w e - F (A + n) * w (A + n + 1)) +
            F (A + (n + 1)) * (w (A + n + 1) - w (A + n + 1 + 1)) := by
        rw [hS, hF, show A + (n + 1) + 1 = A + n + 1 + 1 by ring]
        ring
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (sub_nonneg.2 hdec)]
      have : |F (A + (n + 1))| * (w (A + n + 1) - w (A + n + 1 + 1)) ≤
          η * (w (A + n + 1) - w (A + n + 1 + 1)) :=
        mul_le_mul_of_nonneg_right hFb (sub_nonneg.2 hdec)
      rw [show A + (n + 1) + 1 = A + n + 1 + 1 by ring]
      linarith
  obtain ⟨n, rfl⟩ : ∃ n, B = A + n := ⟨B - A, by omega⟩
  have h1 := key n le_rfl
  have hη : 0 ≤ η := by simpa using hf A le_rfl (by omega)
  have hFB := hf (A + n) (by omega) le_rfl
  have hwB := hw0 (A + n + 1) (by omega)
  calc |∑ e ∈ Ioc A (A + n), f e * w e|
      ≤ |∑ e ∈ Ioc A (A + n), f e * w e - F (A + n) * w (A + n + 1)| +
          |F (A + n) * w (A + n + 1)| := by
        have := abs_add_le (∑ e ∈ Ioc A (A + n), f e * w e - F (A + n) * w (A + n + 1))
          (F (A + n) * w (A + n + 1))
        simpa using this
    _ ≤ η * (w (A + 1) - w (A + n + 1)) + η * w (A + n + 1) := by
        rw [abs_mul, abs_of_nonneg hwB]
        exact add_le_add h1 (mul_le_mul_of_nonneg_right hFB hwB)
    _ = η * w (A + 1) := by ring

/-! ### The weighted comparison -/

/-- One residue system: `|S_U - (Π/φ_U) W| ≤ 2 ε K W / φ_U + N w(A + 1)`, where `W = ∑ w`. -/
lemma abs_weighted_sub_le (S U : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hUS : U ⊆ S)
    {c : ℕ} (hc : ∀ p ∈ U, ¬ p ∣ c) (R : ℕ) {A B : ℕ} (hAB : A ≤ B) {w : ℕ → ℝ}
    (hw0 : ∀ e, A < e → 0 ≤ w e) (hw : ∀ e, A < e → w (e + 1) ≤ w e) {K : ℝ}
    (hK : ∀ e ∈ Ioc A B, w (A + 1) ≤ K * w e) :
    |∑ e ∈ Ioc A B, (if (∀ p ∈ S, ¬ p ∣ e) ∧ ∀ p ∈ U, e * c ≡ 1 [MOD p] then w e else 0) -
        (∏ p ∈ S, (1 - (1 : ℝ) / p)) / (∏ p ∈ U, ((p : ℝ) - 1)) * ∑ e ∈ Ioc A B, w e| ≤
      2 * (∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) * K / (∏ p ∈ U, ((p : ℝ) - 1)) *
          ∑ e ∈ Ioc A B, w e +
        ((S.powerset.filter (·.card ≤ R + 1)).card : ℝ) * w (A + 1) := by
  classical
  set Pi := ∏ p ∈ S, (1 - (1 : ℝ) / p)
  set φU := ∏ p ∈ U, ((p : ℝ) - 1)
  set ε := ∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p
  set N := ((S.powerset.filter (·.card ≤ R + 1)).card : ℝ)
  set cond : ℕ → Prop := fun e => (∀ p ∈ S, ¬ p ∣ e) ∧ ∀ p ∈ U, e * c ≡ 1 [MOD p]
  have hφU0 : 0 < φU := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hS p (hUS hp)).two_le
    linarith
  have hε0 : 0 ≤ ε := sum_nonneg fun u _ => prod_nonneg fun p _ => by positivity
  set f : ℕ → ℝ := fun e => (if cond e then 1 else 0) - Pi / φU
  have hpart : ∀ t, A ≤ t → t ≤ B → |∑ e ∈ Ioc A t, f e| ≤ 2 * ((B : ℝ) - A) * ε / φU + N := by
    intro t hAt htB
    have h := abs_card_rough_cong_sub_le S U hS hUS hc R hAt
    have heq : ∑ e ∈ Ioc A t, f e = ((((Ioc A t).filter cond).card : ℕ) : ℝ) -
        ((t : ℝ) - A) * Pi / φU := by
      simp only [f, sum_sub_distrib, sum_const, Nat.card_Ioc, nsmul_eq_mul]
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, Nat.cast_sub hAt]
      ring
    rw [heq]
    refine h.trans (add_le_add ?_ le_rfl)
    have htB' : (t : ℝ) - A ≤ (B : ℝ) - A := by
      have : (t : ℝ) ≤ B := by exact_mod_cast htB
      linarith
    gcongr
  have habel := abs_sum_Ioc_mul_le hAB hpart hw0 hw
  have hsum : ∑ e ∈ Ioc A B, f e * w e =
      ∑ e ∈ Ioc A B, (if cond e then w e else 0) - Pi / φU * ∑ e ∈ Ioc A B, w e := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun e _ => ?_
    simp only [f]
    split_ifs <;> ring
  rw [hsum] at habel
  refine habel.trans ?_
  have hBA : ((B : ℝ) - A) * w (A + 1) ≤ K * ∑ e ∈ Ioc A B, w e := by
    have : ((B : ℝ) - A) * w (A + 1) = ∑ _e ∈ Ioc A B, w (A + 1) := by
      rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub hAB]
    rw [this, mul_sum]
    exact sum_le_sum hK
  have hwA := hw0 (A + 1) (by omega)
  calc (2 * ((B : ℝ) - A) * ε / φU + N) * w (A + 1)
      = 2 * ε / φU * (((B : ℝ) - A) * w (A + 1)) + N * w (A + 1) := by ring
    _ ≤ 2 * ε / φU * (K * ∑ e ∈ Ioc A B, w e) + N * w (A + 1) := by gcongr
    _ = 2 * ε * K / φU * ∑ e ∈ Ioc A B, w e + N * w (A + 1) := by ring

/-- The relative residue estimate: `|S_U - S_∅ / φ_U| ≤ δ S_∅ / φ_U + 4 N w(A + 1)` with
`δ = 8 ε K / Π`, provided `2 ε K / Π ≤ 1/2`. -/
theorem abs_weighted_cong_sub_le (S U : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hUS : U ⊆ S)
    {c : ℕ} (hc : ∀ p ∈ U, ¬ p ∣ c) (R : ℕ) {A B : ℕ} (hAB : A ≤ B) {w : ℕ → ℝ}
    (hw0 : ∀ e, A < e → 0 ≤ w e) (hw : ∀ e, A < e → w (e + 1) ≤ w e) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ e ∈ Ioc A B, w (A + 1) ≤ K * w e)
    (hδ : 2 * (∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) * K /
      ∏ p ∈ S, (1 - (1 : ℝ) / p) ≤ 1 / 2) :
    |∑ e ∈ Ioc A B, (if (∀ p ∈ S, ¬ p ∣ e) ∧ ∀ p ∈ U, e * c ≡ 1 [MOD p] then w e else 0) -
        (∑ e ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ e then w e else 0)) / ∏ p ∈ U, ((p : ℝ) - 1)| ≤
      8 * (∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) * K /
            (∏ p ∈ S, (1 - (1 : ℝ) / p)) *
          ((∑ e ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ e then w e else 0)) / ∏ p ∈ U, ((p : ℝ) - 1)) +
        4 * ((S.powerset.filter (·.card ≤ R + 1)).card : ℝ) * w (A + 1) := by
  classical
  set Pi := ∏ p ∈ S, (1 - (1 : ℝ) / p)
  set φU := ∏ p ∈ U, ((p : ℝ) - 1)
  set ε := ∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p
  set N := ((S.powerset.filter (·.card ≤ R + 1)).card : ℝ)
  set W := ∑ e ∈ Ioc A B, w e
  set SU := ∑ e ∈ Ioc A B, (if (∀ p ∈ S, ¬ p ∣ e) ∧ ∀ p ∈ U, e * c ≡ 1 [MOD p] then w e else 0)
  set S0 := ∑ e ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ e then w e else 0)
  have hPi0 : 0 < Pi := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    have : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hφU1 : 1 ≤ φU := one_le_prod₀ fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hS p (hUS hp)).two_le
    linarith
  have hφU0 : 0 < φU := by linarith
  have hW0 : 0 ≤ W := sum_nonneg fun e he => hw0 e (mem_Ioc.1 he).1
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hwA := hw0 (A + 1) (by omega)
  have hε0 : 0 ≤ ε := sum_nonneg fun u _ => prod_nonneg fun p _ => by positivity
  have h1 : |SU - Pi / φU * W| ≤ 2 * ε * K / φU * W + N * w (A + 1) :=
    abs_weighted_sub_le S U hS hUS hc R hAB hw0 hw hK
  have h2 : |S0 - Pi * W| ≤ 2 * ε * K * W + N * w (A + 1) := by
    have := abs_weighted_sub_le S ∅ hS (empty_subset S) (by simp) R hAB hw0 hw hK (c := c)
    simp only [prod_empty, div_one, notMem_empty, IsEmpty.forall_iff, implies_true, and_true]
      at this
    exact this
  -- `δ₁ = 2 ε K / Π`
  set δ₁ := 2 * ε * K / Pi with hδ₁
  have hδ₁0 : 0 ≤ δ₁ := by positivity
  have e1 : 2 * ε * K / φU * W = δ₁ * (Pi * W) / φU := by
    rw [hδ₁]; field_simp
  have e2 : 2 * ε * K * W = δ₁ * (Pi * W) := by
    rw [hδ₁]; field_simp
  rw [e1] at h1
  rw [e2] at h2
  have hPW0 : 0 ≤ Pi * W := by positivity
  have hPW : Pi * W ≤ 2 * (S0 + N * w (A + 1)) := by
    have := (abs_le.1 h2).1
    nlinarith [mul_nonneg (sub_nonneg.2 hδ) hPW0]
  have hsplit : SU - S0 / φU = (SU - Pi / φU * W) + (Pi * W - S0) / φU := by
    field_simp
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_of_pos hφU0, abs_sub_comm (Pi * W) S0]
  have h3 : |S0 - Pi * W| / φU ≤ δ₁ * (Pi * W) / φU + N * w (A + 1) := by
    rw [div_le_iff₀ hφU0]
    have : N * w (A + 1) ≤ N * w (A + 1) * φU := le_mul_of_one_le_right (by positivity) hφU1
    have h2' : |S0 - Pi * W| ≤ δ₁ * (Pi * W) + N * w (A + 1) := h2
    calc |S0 - Pi * W| ≤ δ₁ * (Pi * W) + N * w (A + 1) := h2'
      _ ≤ δ₁ * (Pi * W) / φU * φU + N * w (A + 1) * φU := by
          rw [div_mul_cancel₀ _ hφU0.ne']
          linarith
      _ = (δ₁ * (Pi * W) / φU + N * w (A + 1)) * φU := by ring
  have h4 : 2 * (δ₁ * (Pi * W) / φU) ≤ 4 * δ₁ * (S0 / φU) + 2 * N * w (A + 1) := by
    have : δ₁ * (Pi * W) ≤ δ₁ * (2 * (S0 + N * w (A + 1))) :=
      mul_le_mul_of_nonneg_left hPW hδ₁0
    have h5 : 4 * δ₁ * (N * w (A + 1)) / φU ≤ 2 * N * w (A + 1) := by
      rw [div_le_iff₀ hφU0]
      have : 4 * δ₁ ≤ 2 := by linarith
      have hNw : 0 ≤ N * w (A + 1) := by positivity
      nlinarith
    calc 2 * (δ₁ * (Pi * W) / φU) ≤ 2 * (δ₁ * (2 * (S0 + N * w (A + 1))) / φU) := by gcongr
      _ = 4 * δ₁ * (S0 / φU) + 4 * δ₁ * (N * w (A + 1)) / φU := by ring
      _ ≤ _ := by linarith
  have h6 : 8 * ε * K / Pi = 4 * δ₁ := by rw [hδ₁]; ring
  rw [h6]
  linarith

end Erdos408
