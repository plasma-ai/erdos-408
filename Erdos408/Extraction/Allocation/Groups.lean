module

public import Erdos408.Extraction.Allocation.Asymptotics
public import Erdos408.Extraction.Allocation.Coefficients
public import Erdos408.Mertens

/-!
# The candidate groups and the inert bands

The admissibility conditions of `TwoSidedCorrelation` for the active groups
and the inert bands, for large `x`.

* Every candidate group is a dyadic group `[e^y, e^{2y})` of primes, with
  `L^{0.28} ≤ y` and `2y ≤ L^{0.35}` (small) or `L^{0.40} ≤ y` and
  `2y ≤ L^{0.45}` (big). Any two distinct scales differ by a factor of at
  least `2`, so the groups are pairwise disjoint, and by Mertens each has
  reciprocal mass in `[1/2, 3]`. In particular the groups are nonempty, so
  the two families are disjoint. There are at most `T` groups of each kind,
  and the big groups are `primesIcc` intervals by definition.
* The band exponents `0.11 + c · 0.08/K + i · 2/T` lie in `[0.11, 0.195]`,
  and any two differ by at least `1/T`, so the bands
  `[exp(L^a), exp(2 L^a)]` are pairwise disjoint. A monomial has at most
  `K ⌈C_N s / K⌉ ≤ K + C_N s` bands. Each band has reciprocal mass at least
  `1/2`.
-/

@[expose] public section

namespace Erdos408

open Finset Filter Real

/-! ### Membership -/

/-- `q ∈ primesIcc a b` iff `q` is a prime in `[a, b]`. -/
lemma mem_primesIcc {a b : ℝ} {q : ℕ} : q ∈ primesIcc a b ↔ q.Prime ∧ a ≤ q ∧ (q : ℝ) ≤ b := by
  simp only [primesIcc, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨ha, hb⟩, hq⟩
    exact ⟨hq, Nat.ceil_le.1 ha, (Nat.le_floor_iff' hq.ne_zero).1 hb⟩
  · rintro ⟨hq, ha, hb⟩
    exact ⟨⟨Nat.ceil_le.2 ha, (Nat.le_floor_iff' hq.ne_zero).2 hb⟩, hq⟩

/-- `q ∈ dyadicGroup y` iff `q` is a prime in `[e^y, e^{2y})`. -/
lemma mem_dyadicGroup {y : ℝ} {q : ℕ} :
    q ∈ dyadicGroup y ↔ q.Prime ∧ Real.exp y ≤ q ∧ (q : ℝ) < Real.exp (2 * y) := by
  rw [dyadicGroup, mem_primesIcc, Nat.cast_le,
    Nat.le_sub_one_iff_lt (Nat.ceil_pos.2 (exp_pos _)), Nat.lt_ceil]

/-- The band of exponent `a` is the prime interval `[exp(L^a), exp(2 L^a)]`. -/
lemma band_eq_primesIcc (x a : ℝ) :
    band x a = primesIcc (Real.exp (Real.log x ^ a)) (Real.exp (2 * Real.log x ^ a)) :=
  rfl

/-- The groups of `doublingGroups x a b` are the dyadic groups at the scales
`y = 2^i L^a` with `2y ≤ L^b`. -/
lemma exists_of_mem_doublingGroups {x a b : ℝ} {g : Finset ℕ} (hg : g ∈ doublingGroups x a b) :
    ∃ i : ℕ, g = dyadicGroup (2 ^ i * Real.log x ^ a) ∧
      2 * (2 ^ i * Real.log x ^ a) ≤ Real.log x ^ b := by
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hg
  refine ⟨i, rfl, ?_⟩
  have := (mem_filter.1 hi).2
  rw [pow_succ] at this
  linarith

/-- There are at most `(b - a) T / log 2` doubling groups. -/
lemma card_doublingGroups_le {x : ℝ} (hx : 1 ≤ Real.log x) {a b : ℝ} (hab : a ≤ b) :
    ((doublingGroups x a b).card : ℝ) ≤ (b - a) * logLog x / Real.log 2 := by
  have hlog : Real.logb 2 (Real.log x ^ (b - a)) = (b - a) * logLog x / Real.log 2 := by
    rw [Real.logb, Real.log_rpow (by linarith), logLog]
  have hnn : 0 ≤ Real.logb 2 (Real.log x ^ (b - a)) :=
    Real.logb_nonneg (by norm_num) (Real.one_le_rpow hx (by linarith))
  calc ((doublingGroups x a b).card : ℝ)
      ≤ (⌊Real.logb 2 (Real.log x ^ (b - a))⌋₊ : ℝ) := by
        exact_mod_cast card_image_le.trans ((card_filter_le _ _).trans (card_range _).le)
    _ ≤ _ := hlog ▸ Nat.floor_le hnn

/-! ### Disjointness and mass of dyadic groups -/

/-- Dyadic groups at scales `y` and `y' ≥ 2y` are disjoint. -/
lemma disjoint_dyadicGroup {y y' : ℝ} (h : 2 * y ≤ y') :
    Disjoint (dyadicGroup y) (dyadicGroup y') := by
  rw [Finset.disjoint_left]
  intro q hq hq'
  have h1 := (mem_dyadicGroup.1 hq).2.2
  have h2 := (mem_dyadicGroup.1 hq').2.1
  have := exp_le_exp.2 h
  linarith

/-- `e^y - 1 ≥ e^{y - 1}` once `e^y ≥ 2`. -/
private lemma exp_sub_one_ge {y : ℝ} (hy : 2 ≤ Real.exp y) :
    Real.exp (y - 1) ≤ Real.exp y - 1 := by
  rw [exp_sub]
  have he : 2 ≤ Real.exp 1 := by linarith [exp_one_gt_d9]
  rw [div_le_iff₀ (exp_pos 1)]
  nlinarith

/-- The reciprocal mass of a dyadic group at a large scale lies in `[1/2, 3]`. -/
lemma harmonicMass_dyadicGroup : ∃ Y₀ : ℝ, ∀ y : ℝ, Y₀ ≤ y →
    1 / 2 ≤ harmonicMass (dyadicGroup y) ∧ harmonicMass (dyadicGroup y) ≤ 3 := by
  obtain ⟨E, hE, hM⟩ := mertens_second
  refine ⟨6 * (E + 2) + 4, fun y hy => ?_⟩
  have hy4 : 4 ≤ y := by linarith
  have hey : 2 ≤ Real.exp y - 1 := by
    have := add_one_le_exp y
    linarith
  have he2y : Real.exp y ≤ Real.exp (2 * y) - 1 := by
    have h := exp_add y y
    rw [show y + y = 2 * y by ring] at h
    have := add_one_le_exp y
    nlinarith
  have hlog1 : y - 1 ≤ Real.log (Real.exp y - 1) := by
    rw [← log_exp (y - 1)]
    exact log_le_log (exp_pos _) (exp_sub_one_ge (by linarith))
  have hlog2 : 2 * y - 1 ≤ Real.log (Real.exp (2 * y) - 1) := by
    rw [← log_exp (2 * y - 1)]
    exact log_le_log (exp_pos _) (exp_sub_one_ge (by linarith))
  constructor
  · -- lower bound from `(e^y, e^{2y} - 1]`
    have hsub : primesIoc (Real.exp y) (Real.exp (2 * y) - 1) ⊆ dyadicGroup y := by
      intro q hq
      obtain ⟨hp, h1, h2⟩ := mem_primesIoc.1 hq
      exact mem_dyadicGroup.2 ⟨hp, h1.le, by linarith⟩
    have hS := sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => (1 : ℝ) / q) hsub
      fun q _ _ => by positivity
    have hm := (abs_le.1 (hM (Real.exp y) (Real.exp (2 * y) - 1) (by linarith) he2y)).1
    rw [log_exp] at hm
    -- `log((2y - 1)/y) ≥ log 2 - 1/y`
    have hl : Real.log 2 - 1 / y ≤ Real.log (Real.log (Real.exp (2 * y) - 1) / y) := by
      have h1 : 2 - 1 / y ≤ Real.log (Real.exp (2 * y) - 1) / y := by
        rw [le_div_iff₀ (by linarith)]
        field_simp
        linarith
      have h2 : Real.log (2 - 1 / y) ≤ Real.log (Real.log (Real.exp (2 * y) - 1) / y) :=
        log_le_log (by
          have : 1 / y ≤ 1 / 4 := by gcongr
          linarith) h1
      have h3 : Real.log 2 - 1 / y ≤ Real.log (2 - 1 / y) := by
        have h4 : 2 - 1 / y = 2 * (1 - 1 / (2 * y)) := by field_simp
        have h5 : 0 < 1 - 1 / (2 * y) := by
          have : 1 / (2 * y) ≤ 1 / 8 := by
            rw [div_le_div_iff₀ (by linarith) (by norm_num)]
            linarith
          linarith
        rw [h4, log_mul (by norm_num) h5.ne']
        have h6 := one_sub_inv_le_log_of_pos h5
        have h7 : -(1 / y) ≤ 1 - (1 - 1 / (2 * y))⁻¹ := by
          have h8 : (1 - 1 / (2 * y))⁻¹ = 1 + 1 / (2 * y - 1) := by
            have : 2 * y - 1 ≠ 0 := by linarith
            field_simp
            ring
          rw [h8]
          have : 1 / (2 * y - 1) ≤ 1 / y :=
            one_div_le_one_div_of_le (by linarith) (by linarith)
          linarith
        linarith
      linarith
    have hE' : E / y ≤ (E + 1) / y := by gcongr; linarith
    have hEy : (E + 1) / y + 1 / y ≤ 1 / 6 := by
      rw [← add_div, div_le_iff₀ (by linarith)]
      linarith
    have := log_two_gt_d9
    unfold harmonicMass
    linarith
  · -- upper bound from `(e^y - 1, e^{2y}]`
    have hsub : dyadicGroup y ⊆ primesIoc (Real.exp y - 1) (Real.exp (2 * y)) := by
      intro q hq
      obtain ⟨hp, h1, h2⟩ := mem_dyadicGroup.1 hq
      exact mem_primesIoc.2 ⟨hp, by linarith, h2.le⟩
    have hS := sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => (1 : ℝ) / q) hsub
      fun q _ _ => by positivity
    have hexp : Real.exp y - 1 ≤ Real.exp (2 * y) := by
      have := exp_le_exp.2 (show y ≤ 2 * y by linarith)
      linarith
    have hm := (abs_le.1 (hM (Real.exp y - 1) (Real.exp (2 * y)) hey hexp)).2
    rw [log_exp] at hm
    have hl0 : 0 < Real.log (Real.exp y - 1) := by linarith
    have hl : Real.log (2 * y / Real.log (Real.exp y - 1)) ≤ 2 := by
      calc _ ≤ 2 * y / Real.log (Real.exp y - 1) - 1 := log_le_sub_one_of_pos (by positivity)
        _ ≤ 2 * y / (y - 1) - 1 := by gcongr; linarith
        _ ≤ 2 := by
          rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
          linarith
    have hE' : E / Real.log (Real.exp y - 1) ≤ 1 := by
      rw [div_le_one hl0]
      linarith
    unfold harmonicMass
    linarith

/-! ### The candidate groups -/

/-- A doubling group sits at a scale `y` with `L^a ≤ y` and `2y ≤ L^b`. -/
lemma exists_scale_of_mem_doublingGroups {x a b : ℝ} (hx : 1 ≤ Real.log x) {g : Finset ℕ}
    (hg : g ∈ doublingGroups x a b) :
    ∃ y : ℝ, g = dyadicGroup y ∧ Real.log x ^ a ≤ y ∧ 2 * y ≤ Real.log x ^ b := by
  obtain ⟨i, rfl, hi⟩ := exists_of_mem_doublingGroups hg
  refine ⟨_, rfl, ?_, hi⟩
  have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have : 0 < Real.log x ^ a := rpow_pos_of_pos (by linarith) a
  nlinarith

/-- Distinct groups of one doubling family are disjoint. -/
lemma disjoint_of_mem_doublingGroups {x a b : ℝ} (hx : 1 ≤ Real.log x) {g g' : Finset ℕ}
    (hg : g ∈ doublingGroups x a b) (hg' : g' ∈ doublingGroups x a b) (hne : g ≠ g') :
    Disjoint g g' := by
  obtain ⟨i, rfl, -⟩ := exists_of_mem_doublingGroups hg
  obtain ⟨i', rfl, -⟩ := exists_of_mem_doublingGroups hg'
  have hL : 0 < Real.log x ^ a := rpow_pos_of_pos (by linarith) a
  have key : ∀ i i' : ℕ, i < i' → 2 * (2 ^ i * Real.log x ^ a) ≤ 2 ^ i' * Real.log x ^ a := by
    intro i i' h
    rw [← mul_assoc, ← pow_succ']
    gcongr
    · norm_num
    · exact h
  rcases lt_trichotomy i i' with h | rfl | h
  · exact disjoint_dyadicGroup (key i i' h)
  · exact absurd rfl hne
  · exact (disjoint_dyadicGroup (key i' i h)).symm

/-- A small group sits at a scale in `[L^{0.28}, L^{0.35}/2]`. -/
lemma exists_scale_of_mem_smallGroups {x : ℝ} (hx : 1 ≤ Real.log x) {g : Finset ℕ}
    (hg : g ∈ smallGroups x) : ∃ y : ℝ, g = dyadicGroup y ∧
      Real.log x ^ (28 / 100 : ℝ) ≤ y ∧ 2 * y ≤ Real.log x ^ (35 / 100 : ℝ) :=
  exists_scale_of_mem_doublingGroups hx hg

/-- A big group sits at a scale in `[L^{0.40}, L^{0.45}/2]`. -/
lemma exists_scale_of_mem_bigGroups {x : ℝ} (hx : 1 ≤ Real.log x) {g : Finset ℕ}
    (hg : g ∈ bigGroups x) : ∃ y : ℝ, g = dyadicGroup y ∧
      Real.log x ^ (40 / 100 : ℝ) ≤ y ∧ 2 * y ≤ Real.log x ^ (45 / 100 : ℝ) :=
  exists_scale_of_mem_doublingGroups hx hg

/-- Every candidate group sits at a scale in `[L^{0.28}, L^{0.45}/2]`. -/
lemma exists_scale_of_mem_candidateGroups {x : ℝ} (hx : 1 ≤ Real.log x) {g : Finset ℕ}
    (hg : g ∈ candidateGroups x) : ∃ y : ℝ, g = dyadicGroup y ∧
      Real.log x ^ (28 / 100 : ℝ) ≤ y ∧ 2 * y ≤ Real.log x ^ (45 / 100 : ℝ) := by
  rcases mem_union.1 hg with hg | hg
  · obtain ⟨y, rfl, h1, h2⟩ := exists_scale_of_mem_smallGroups hx hg
    exact ⟨y, rfl, h1, h2.trans (rpow_le_rpow_of_exponent_le hx (by norm_num))⟩
  · obtain ⟨y, rfl, h1, h2⟩ := exists_scale_of_mem_bigGroups hx hg
    exact ⟨y, rfl, (rpow_le_rpow_of_exponent_le hx (by norm_num)).trans h1, h2⟩

/-- A small group and a big group are disjoint. -/
lemma disjoint_of_mem_small_of_mem_big {x : ℝ} (hx : 1 ≤ Real.log x) {g g' : Finset ℕ}
    (hg : g ∈ smallGroups x) (hg' : g' ∈ bigGroups x) : Disjoint g g' := by
  obtain ⟨y, rfl, -, h⟩ := exists_scale_of_mem_smallGroups hx hg
  obtain ⟨y', rfl, h', -⟩ := exists_scale_of_mem_bigGroups hx hg'
  exact disjoint_dyadicGroup (h.trans ((rpow_le_rpow_of_exponent_le hx (by norm_num)).trans h'))

/-- Distinct candidate groups are disjoint. -/
lemma pairwiseDisjoint_candidateGroups {x : ℝ} (hx : 1 ≤ Real.log x) :
    (candidateGroups x : Set (Finset ℕ)).PairwiseDisjoint id := by
  intro g hg g' hg' hne
  rcases mem_union.1 hg with hg | hg <;> rcases mem_union.1 hg' with hg' | hg'
  · exact disjoint_of_mem_doublingGroups hx hg hg' hne
  · exact disjoint_of_mem_small_of_mem_big hx hg hg'
  · exact (disjoint_of_mem_small_of_mem_big hx hg' hg).symm
  · exact disjoint_of_mem_doublingGroups hx hg hg' hne

/-- The big groups are prime intervals. -/
lemma exists_eq_primesIcc_of_mem_bigGroups {x : ℝ} {g : Finset ℕ} (hg : g ∈ bigGroups x) :
    ∃ y z : ℝ, g = primesIcc y z := by
  obtain ⟨i, rfl, -⟩ := exists_of_mem_doublingGroups hg
  exact ⟨_, _, rfl⟩

/-- The candidate groups for large `x`: masses in `[1/2, 3]`, disjoint
families, ranges as in PD (6.1), at most `T` groups of each kind, and every
candidate prime at least `exp(L^{0.28})`. -/
lemma eventually_candidateGroups : ∀ᶠ x : ℝ in atTop,
    (∀ g ∈ candidateGroups x, 1 / 2 ≤ harmonicMass g ∧ harmonicMass g ≤ 3) ∧
    Disjoint (smallGroups x) (bigGroups x) ∧
    (∀ g ∈ smallGroups x, g ⊆ primesIcc (Real.exp (Real.log x ^ (0.27 : ℝ)))
      (Real.exp (Real.log x ^ (0.36 : ℝ)))) ∧
    (∀ g ∈ bigGroups x, g ⊆ primesIcc (Real.exp (Real.log x ^ (0.39 : ℝ)))
      (Real.exp (Real.log x ^ (0.46 : ℝ)))) ∧
    ((smallGroups x).card : ℝ) ≤ logLog x ∧ ((bigGroups x).card : ℝ) ≤ logLog x ∧
    ∀ p ∈ candidatePrimes x, Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p := by
  obtain ⟨Y₀, hY₀⟩ := harmonicMass_dyadicGroup
  have hL : Tendsto (fun x : ℝ => Real.log x ^ (28 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  filter_upwards [hL.eventually_ge_atTop Y₀, eventually_le_log 1] with x hY hx
  have hmass : ∀ g ∈ candidateGroups x, 1 / 2 ≤ harmonicMass g ∧ harmonicMass g ≤ 3 := by
    intro g hg
    obtain ⟨y, rfl, h1, -⟩ := exists_scale_of_mem_candidateGroups hx hg
    exact hY₀ y (hY.trans h1)
  have hcard : ∀ a b : ℝ, a ≤ b → b - a ≤ 1 / 2 →
      ((doublingGroups x a b).card : ℝ) ≤ logLog x := by
    intro a b hab hba
    have hT : 0 ≤ logLog x := Real.log_nonneg hx
    refine (card_doublingGroups_le hx hab).trans ?_
    rw [div_le_iff₀ (Real.log_pos (by norm_num))]
    have := log_two_gt_d9
    nlinarith
  refine ⟨hmass, ?_, ?_, ?_, hcard _ _ (by norm_num) (by norm_num),
    hcard _ _ (by norm_num) (by norm_num), ?_⟩
  · rw [Finset.disjoint_left]
    intro g hg hg'
    have h := disjoint_of_mem_small_of_mem_big hx hg hg'
    rw [disjoint_self, bot_eq_empty] at h
    have := (hmass g (mem_union_left _ hg)).1
    simp [h, harmonicMass] at this
    linarith
  · intro g hg q hq
    obtain ⟨y, rfl, h1, h2⟩ := exists_scale_of_mem_smallGroups hx hg
    obtain ⟨hp, h3, h4⟩ := mem_dyadicGroup.1 hq
    refine mem_primesIcc.2 ⟨hp, le_trans (exp_le_exp.2 ?_) h3, le_trans h4.le (exp_le_exp.2 ?_)⟩
    · exact (rpow_le_rpow_of_exponent_le hx (by norm_num)).trans h1
    · exact h2.trans (rpow_le_rpow_of_exponent_le hx (by norm_num))
  · intro g hg q hq
    obtain ⟨y, rfl, h1, h2⟩ := exists_scale_of_mem_bigGroups hx hg
    obtain ⟨hp, h3, h4⟩ := mem_dyadicGroup.1 hq
    refine mem_primesIcc.2 ⟨hp, le_trans (exp_le_exp.2 ?_) h3, le_trans h4.le (exp_le_exp.2 ?_)⟩
    · exact (rpow_le_rpow_of_exponent_le hx (by norm_num)).trans h1
    · exact h2.trans (rpow_le_rpow_of_exponent_le hx (by norm_num))
  · intro p hp
    obtain ⟨g, hg, hpg⟩ := mem_biUnion.1 hp
    obtain ⟨y, rfl, h1, -⟩ := exists_scale_of_mem_candidateGroups hx hg
    exact (exp_le_exp.2 h1).trans (mem_dyadicGroup.1 hpg).2.1

/-- The facts about the candidate groups at a large `x`
(`eventually_candidateGroups`). -/
def GroupFacts (x : ℝ) : Prop :=
  (∀ g ∈ candidateGroups x, 1 / 2 ≤ harmonicMass g ∧ harmonicMass g ≤ 3) ∧
    Disjoint (smallGroups x) (bigGroups x) ∧
    (∀ g ∈ smallGroups x, g ⊆ primesIcc (Real.exp (Real.log x ^ (0.27 : ℝ)))
      (Real.exp (Real.log x ^ (0.36 : ℝ)))) ∧
    (∀ g ∈ bigGroups x, g ⊆ primesIcc (Real.exp (Real.log x ^ (0.39 : ℝ)))
      (Real.exp (Real.log x ^ (0.46 : ℝ)))) ∧
    ((smallGroups x).card : ℝ) ≤ logLog x ∧ ((bigGroups x).card : ℝ) ≤ logLog x ∧
    ∀ p ∈ candidatePrimes x, Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p

/-- The reciprocal sum of the candidate primes is at most `6 T`. -/
lemma sum_one_div_candidatePrimes_le {x : ℝ} (hx : 1 ≤ Real.log x) (hg : GroupFacts x) :
    ∑ p ∈ candidatePrimes x, (1 : ℝ) / p ≤ 6 * logLog x := by
  obtain ⟨hmass, -, -, -, hcs, hcb, -⟩ := hg
  rw [candidatePrimes, show smallGroups x ∪ bigGroups x = candidateGroups x from rfl,
    sum_biUnion (pairwiseDisjoint_candidateGroups hx)]
  have hcard : ((candidateGroups x).card : ℝ) ≤ 2 * logLog x := by
    have := card_union_le (smallGroups x) (bigGroups x)
    have : ((candidateGroups x).card : ℝ) ≤ (smallGroups x).card + (bigGroups x).card := by
      exact_mod_cast this
    linarith
  calc ∑ g ∈ candidateGroups x, ∑ p ∈ id g, (1 : ℝ) / p
      ≤ ∑ _g ∈ candidateGroups x, (3 : ℝ) := sum_le_sum fun g hg => (hmass g hg).2
    _ = 3 * (candidateGroups x).card := by rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ 6 * logLog x := by linarith

/-! ### The inert bands -/

/-- Bands whose exponents differ by at least `1/T` are disjoint. -/
lemma disjoint_band {x a a' : ℝ} (hx : 1 ≤ Real.log x) (h : 1 ≤ (a' - a) * logLog x) :
    Disjoint (band x a) (band x a') := by
  rw [Finset.disjoint_left]
  intro q hq hq'
  rw [band_eq_primesIcc, mem_primesIcc] at hq hq'
  -- `L^{a'} = L^a L^{a' - a} ≥ e L^a > 2 L^a`
  have hL : 0 < Real.log x := by linarith
  have h2 : 2 < Real.log x ^ (a' - a) := by
    rw [rpow_def_of_pos hL, mul_comm]
    have := exp_one_gt_d9
    have := exp_le_exp.2 h
    rw [logLog] at this
    linarith
  have h3 : Real.log x ^ a' = Real.log x ^ a * Real.log x ^ (a' - a) := by
    rw [← rpow_add hL]
    ring_nf
  have h4 : 0 < Real.log x ^ a := rpow_pos_of_pos hL a
  have h5 : Real.exp (2 * Real.log x ^ a) < Real.exp (Real.log x ^ a') :=
    exp_lt_exp.2 (by rw [h3]; nlinarith)
  linarith [hq.2.2, hq'.2.1]

/-- For large `x`, every band of exponent at least `0.11` has reciprocal mass
at least `1/2`. -/
lemma eventually_harmonicMass_band : ∀ᶠ x : ℝ in atTop,
    ∀ a : ℝ, 11 / 100 ≤ a → 1 / 2 ≤ harmonicMass (band x a) := by
  obtain ⟨E, hE, hM⟩ := mertens_second
  have hL : Tendsto (fun x : ℝ => Real.log x ^ (11 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  filter_upwards [hL.eventually_ge_atTop (6 * (E + 1)), eventually_le_log 1] with x hY hx a ha
  have hLa : 6 * (E + 1) ≤ Real.log x ^ a :=
    hY.trans (rpow_le_rpow_of_exponent_le hx ha)
  have hLa0 : 0 < Real.log x ^ a := by linarith
  have hsub : primesIoc (Real.exp (Real.log x ^ a)) (Real.exp (2 * Real.log x ^ a)) ⊆
      band x a := by
    intro q hq
    obtain ⟨hp, h1, h2⟩ := mem_primesIoc.1 hq
    exact band_eq_primesIcc x a ▸ mem_primesIcc.2 ⟨hp, h1.le, h2⟩
  have hS := sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => (1 : ℝ) / q) hsub
    fun q _ _ => by positivity
  have h2 : 2 ≤ Real.exp (Real.log x ^ a) := by
    have := add_one_le_exp (Real.log x ^ a)
    linarith
  have hm := (abs_le.1 (hM _ _ h2
    (exp_le_exp.2 (by linarith : Real.log x ^ a ≤ 2 * Real.log x ^ a)))).1
  rw [log_exp, log_exp, mul_div_assoc, div_self hLa0.ne', mul_one] at hm
  have hE' : E / Real.log x ^ a ≤ 1 / 6 := by
    rw [div_le_iff₀ hLa0]
    linarith
  have := log_two_gt_d9
  unfold harmonicMass
  linarith

/-- `⌈y⌉₊ ≤ max y 0 + 1`. -/
private lemma natCeil_le_max_add_one (y : ℝ) : (⌈y⌉₊ : ℝ) ≤ max y 0 + 1 :=
  (Nat.cast_le.2 (Nat.ceil_mono (le_max_left y 0))).trans
    (Nat.ceil_lt_add_one (le_max_right y 0)).le

/-- The number of bands per cluster is at most `C_N⁺ s / K + 1`. -/
lemma inertPerCluster_le {K : ℕ} (hK : 1 ≤ K) (CN : ℝ) {x : ℝ} (hs : 0 ≤ logLogLog x) :
    (inertPerCluster K CN x : ℝ) ≤ max CN 0 * logLogLog x / K + 1 := by
  refine (natCeil_le_max_add_one _).trans ?_
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  gcongr
  refine max_le ?_ (by positivity)
  gcongr
  exact le_max_left _ _

/-- The inert bands for large `x`: exponents in `[0.11, 0.195]`, pairwise
disjoint bands, and at most `K + C_N⁺ s` bands in all. -/
lemma eventually_inertBands {K : ℕ} (hK : 1 ≤ K) (CN : ℝ) : ∀ᶠ x : ℝ in atTop,
    (∀ p ∈ range K ×ˢ range (inertPerCluster K CN x),
      11 / 100 ≤ inertExponent K x p.1 p.2 ∧ inertExponent K x p.1 p.2 ≤ 39 / 200) ∧
    (∀ p ∈ range K ×ˢ range (inertPerCluster K CN x),
      ∀ p' ∈ range K ×ˢ range (inertPerCluster K CN x), p ≠ p' →
        Disjoint (band x (inertExponent K x p.1 p.2)) (band x (inertExponent K x p'.1 p'.2))) ∧
    ((K * inertPerCluster K CN x : ℕ) : ℝ) ≤ K + max CN 0 * logLogLog x := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hε : 0 < min (1 / 200 : ℝ) (1 / (25 * K)) := lt_min (by norm_num) (by positivity)
  filter_upwards [eventually_mul_logLogLog_le (2 * max CN 0) hε,
    eventually_le_logLog (25 * K + Real.exp 1), eventually_le_log 1] with x hsT hT hx
  have he1 : 1 ≤ Real.exp 1 := one_le_exp zero_le_one
  have hT1 : 1 ≤ logLog x := by nlinarith
  have hT0 : 0 < logLog x := by linarith
  have hs : 0 ≤ logLogLog x := by
    rw [logLogLog]
    exact Real.log_nonneg hT1
  have hN := inertPerCluster_le hK CN hs
  set N := inertPerCluster K CN x
  -- the band offsets `i · 2/T` are at most `min (1/200) (1/(25K))`
  have hoff : ∀ i < N, (i : ℝ) * (2 / logLog x) ≤ min (1 / 200 : ℝ) (1 / (25 * K)) := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
    have h1 : (i : ℝ) ≤ max CN 0 * logLogLog x / K := by linarith
    have h2 : max CN 0 * logLogLog x / K ≤ max CN 0 * logLogLog x := by
      rw [div_le_iff₀ hK0]
      have : 0 ≤ max CN 0 * logLogLog x := mul_nonneg (le_max_right _ _) hs
      have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
      nlinarith
    rw [mul_div_assoc', div_le_iff₀ hT0]
    nlinarith
  have hcl : ∀ c < K, (c : ℝ) * (8 / 100 / K) ≤ 8 / 100 - 8 / 100 / K := by
    intro c hc
    have : (c : ℝ) + 1 ≤ K := by exact_mod_cast hc
    rw [show (8 / 100 : ℝ) - 8 / 100 / K = (K - 1) * (8 / 100 / K) by field_simp]
    gcongr
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨c, i⟩ hp
    simp only [mem_product, mem_range] at hp
    have h1 := hoff i hp.2
    have h2 := hcl c hp.1
    have h3 : min (1 / 200 : ℝ) (1 / (25 * K)) ≤ 1 / 200 := min_le_left _ _
    have h4 : 0 ≤ (c : ℝ) * (8 / 100 / K) := by positivity
    have h5 : 0 ≤ (i : ℝ) * (2 / logLog x) := by positivity
    have h6 : 0 ≤ 8 / 100 / (K : ℝ) := by positivity
    simp only [inertExponent]
    constructor <;> linarith
  · -- lexicographically ordered pairs of exponents are `1/T` apart
    have key : ∀ p ∈ range K ×ˢ range N, ∀ p' ∈ range K ×ˢ range N,
        p.1 < p'.1 ∨ (p.1 = p'.1 ∧ p.2 < p'.2) →
        1 ≤ (inertExponent K x p'.1 p'.2 - inertExponent K x p.1 p.2) * logLog x := by
      rintro ⟨c, i⟩ hp ⟨c', i'⟩ hp' h
      simp only [mem_product, mem_range] at hp hp'
      simp only [inertExponent]
      rcases h with h | ⟨rfl, h⟩
      · have h1 := hoff i hp.2
        have h2 : (c : ℝ) + 1 ≤ c' := by exact_mod_cast h
        have h3 : min (1 / 200 : ℝ) (1 / (25 * K)) ≤ 1 / (25 * K) := min_le_right _ _
        have h4 : 0 ≤ (i' : ℝ) * (2 / logLog x) := by positivity
        have h5 : (c' : ℝ) * (8 / 100 / K) - c * (8 / 100 / K) ≥ 8 / 100 / K := by
          rw [← sub_mul]
          have : (1 : ℝ) ≤ c' - c := by linarith
          have : 0 ≤ 8 / 100 / (K : ℝ) := by positivity
          nlinarith
        have h6 : 1 ≤ (8 / 100 / K - 1 / (25 * K)) * logLog x := by
          rw [show (8 / 100 / K - 1 / (25 * K) : ℝ) = 1 / (25 * K) by field_simp; ring,
            one_div_mul_eq_div, le_div_iff₀ (by positivity)]
          linarith
        nlinarith
      · have h2 : (i : ℝ) + 1 ≤ i' := by exact_mod_cast h
        have : (11 / 100 + c * (8 / 100 / K) + i' * (2 / logLog x) -
            (11 / 100 + c * (8 / 100 / K) + i * (2 / logLog x))) * logLog x =
            2 * (i' - i) := by
          field_simp
          ring
        rw [this]
        linarith
    intro p hp p' hp' hne
    have hlex : p.1 < p'.1 ∨ (p.1 = p'.1 ∧ p.2 < p'.2) ∨ p'.1 < p.1 ∨
        (p'.1 = p.1 ∧ p'.2 < p.2) := by
      rcases lt_trichotomy p.1 p'.1 with h | h | h
      · exact Or.inl h
      · rcases lt_trichotomy p.2 p'.2 with h' | h' | h'
        · exact Or.inr (Or.inl ⟨h, h'⟩)
        · exact absurd (Prod.ext h h') hne
        · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
      · exact Or.inr (Or.inr (Or.inl h))
    rcases hlex with h | h | h | h
    · exact disjoint_band hx (key p hp p' hp' (Or.inl h))
    · exact disjoint_band hx (key p hp p' hp' (Or.inr h))
    · exact (disjoint_band hx (key p' hp' p hp (Or.inl h))).symm
    · exact (disjoint_band hx (key p' hp' p hp (Or.inr h))).symm
  · push_cast
    have : (K : ℝ) * N ≤ K * (max CN 0 * logLogLog x / K + 1) := by gcongr
    rw [mul_add, mul_div_cancel₀ _ hK0.ne', mul_one] at this
    linarith

end Erdos408
