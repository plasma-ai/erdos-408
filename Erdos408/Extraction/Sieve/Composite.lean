import Erdos408.Extraction.Sieve.Basic
import Mathlib.Data.Nat.Squarefree

/-!
# The composite decomposition of the presieved sum (E3)

After the presieve, `u + 1` has no prime factor `p ≤ z`. A squarefree such
`n = u + 1` with `2 ≤ ω(n) ≤ J` is counted exactly once by
`∑_{2 ≤ j ≤ J} Comp_j / j!`, since its `j!` orderings are the ordered
`j`-tuples of primes above `z` with product `n`. Every other `n` is weighted
by `1 - a(n)` with `0 ≤ a(n) ≤ 1`.

* `abs_sum_rough_sub_le`: the rough sum minus its prime part and
  `∑ Comp_j / j!` is at most the sum of `|G|` over nonsquarefree `n` and over
  `n` with `ω(n) > J`.
* `card_rough_not_squarefree_le`: at most `N / ⌊z⌋` nonsquarefree rough
  `n ≤ N`.
* `sum_two_pow_card_primeFactors_le` (Rankin): `∑_{n ≤ Y rough} 2^{ω(n)}` is
  at most `D Y (1 + ∏_{z < p ≤ Y} (1 + 1/p))`, given the sieve bound
  `#{b ≤ Y' rough} ≤ D Y'` for `z ≤ Y' ≤ Y`.
* `card_rough_le`: that sieve bound with `D = D₀ / log z`, from the upper
  form of `BlockSieve` with the primes up to `min(z, Y^{1/20})`.
-/

namespace Erdos408

open Finset

namespace Sieve

noncomputable section

/-- `n` has no prime factor `p ≤ z`. -/
def Rough (z : ℝ) (n : ℕ) : Prop :=
  ∀ p ∈ primesIcc 2 z, ¬ p ∣ n

instance (z : ℝ) : DecidablePred (Rough z) := fun n => by
  unfold Rough
  infer_instance

/-- The ordered `j`-tuples of primes of `A` with product `n`. -/
def tuplesWithProd (A : Finset ℕ) (j n : ℕ) : Finset (Fin j → ℕ) :=
  (Fintype.piFinset fun _ : Fin j => A).filter fun p => ∏ i, p i = n

/-! ### Roughness -/

/-- Membership in `primesIcc 2 z`. -/
lemma mem_primesIcc_two {z : ℝ} {p : ℕ} : p ∈ primesIcc 2 z ↔ p.Prime ∧ (p : ℝ) ≤ z := by
  simp only [primesIcc, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨-, h⟩, hp⟩
    exact ⟨hp, (Nat.le_floor_iff' hp.ne_zero).1 h⟩
  · rintro ⟨hp, h⟩
    refine ⟨⟨?_, (Nat.le_floor_iff' hp.ne_zero).2 h⟩, hp⟩
    rw [Nat.ceil_le]
    exact_mod_cast hp.two_le

/-- `n` is rough iff each of its prime factors exceeds `z`. -/
lemma rough_iff {z : ℝ} {n : ℕ} : Rough z n ↔ ∀ p, p.Prime → p ∣ n → z < p := by
  simp only [Rough, mem_primesIcc_two]
  constructor
  · intro h p hp hpn
    by_contra hle
    exact h p ⟨hp, not_lt.1 hle⟩ hpn
  · rintro h p ⟨hp, hle⟩ hpn
    exact absurd (h p hp hpn) (not_lt.2 hle)

/-- A divisor of a rough number is rough. -/
lemma Rough.of_dvd {z : ℝ} {n m : ℕ} (hn : Rough z n) (hm : m ∣ n) : Rough z m :=
  fun p hp hpm => hn p hp (hpm.trans hm)

/-- A rough number `2 ≤ b` exceeds `z`. -/
lemma Rough.lt {z : ℝ} {b : ℕ} (hb : Rough z b) (h2 : 2 ≤ b) : z < b := by
  have hp := Nat.minFac_prime (show b ≠ 1 by omega)
  have := rough_iff.1 hb _ hp (Nat.minFac_dvd b)
  have hle : (b.minFac : ℝ) ≤ b := by exact_mod_cast Nat.minFac_le (by omega)
  linarith

/-- For a set `S` of primes, a prime `p` divides `∏ S` iff `p ∈ S`. -/
lemma dvd_prod_primes_iff' {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {p : ℕ} (hp : p.Prime) :
    p ∣ ∏ q ∈ S, q ↔ p ∈ S := by
  rw [hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hq, hpq⟩
    rwa [(Nat.prime_dvd_prime_iff_eq hp (hS q hq)).1 hpq]
  · exact fun h => ⟨p, h, dvd_rfl⟩

/-! ### Counting ordered factorizations -/

/-- There are at most `j!` ordered `j`-tuples of primes with product `n`, and
none unless `n` has exactly `j` prime factors with multiplicity. -/
lemma card_tuplesWithProd_le {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) (j n : ℕ) :
    #(tuplesWithProd A j n) ≤ j.factorial ∧
      ((tuplesWithProd A j n).Nonempty → n.primeFactorsList.length = j) := by
  -- every tuple, as a list, is a permutation of the prime factorization of `n`
  have hperm : ∀ p ∈ tuplesWithProd A j n, (List.ofFn p).Perm n.primeFactorsList := by
    intro p hp
    obtain ⟨hpA, hprod⟩ := mem_filter.1 hp
    refine Nat.primeFactorsList_unique (by rw [List.prod_ofFn, hprod]) fun q hq => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hq
    exact hA _ (Fintype.mem_piFinset.1 hpA i)
  constructor
  · rcases (tuplesWithProd A j n).eq_empty_or_nonempty with h | ⟨p₀, hp₀⟩
    · rw [h, card_empty]
      exact Nat.zero_le _
    have hlen : n.primeFactorsList.length = j := by
      rw [← (hperm p₀ hp₀).length_eq, List.length_ofFn]
    calc #(tuplesWithProd A j n) ≤ #(n.primeFactorsList.permutations.toFinset) := by
          refine card_le_card_of_injOn List.ofFn (fun p hp => ?_) fun p _ q _ h =>
            List.ofFn_injective h
          rw [mem_coe, List.mem_toFinset]
          exact List.mem_permutations.2 (hperm p hp)
      _ ≤ n.primeFactorsList.permutations.length := List.toFinset_card_le _
      _ = j.factorial := by rw [List.length_permutations, hlen]
  · rintro ⟨p, hp⟩
    rw [← (hperm p hp).length_eq, List.length_ofFn]

/-- A squarefree `n` whose prime factors lie in `A` has exactly `ω(n)!` ordered
factorizations into `ω(n)` primes of `A`. -/
lemma card_tuplesWithProd_of_squarefree {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) {n : ℕ}
    (hn : Squarefree n) (hnA : n.primeFactors ⊆ A) :
    #(tuplesWithProd A #n.primeFactors n) = (#n.primeFactors).factorial := by
  refine le_antisymm (card_tuplesWithProd_le hA _ _).1 ?_
  set F := n.primeFactors
  let e : Fin #F ≃ F := F.equivFin.symm
  -- each permutation of `Fin #F` gives an ordering of the prime factors
  let t : Equiv.Perm (Fin #F) → Fin #F → ℕ := fun σ i => e (σ i)
  have ht : ∀ σ, t σ ∈ tuplesWithProd A #F n := by
    intro σ
    refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => hnA (e (σ i)).2, ?_⟩
    calc ∏ i, t σ i = ∏ i, ((e (σ i) : F) : ℕ) := rfl
      _ = ∏ i, ((e i : F) : ℕ) := Equiv.prod_comp σ fun i => ((e i : F) : ℕ)
      _ = ∏ q : F, (q : ℕ) := Equiv.prod_comp e fun q : F => (q : ℕ)
      _ = ∏ q ∈ F, q := prod_coe_sort F fun q => q
      _ = n := Nat.prod_primeFactors_of_squarefree hn
  have hinj : Function.Injective t := by
    intro σ τ h
    ext i
    have := congrFun h i
    simp only [t] at this
    exact congrArg Fin.val (e.injective (Subtype.ext this))
  calc (#F).factorial = Fintype.card (Equiv.Perm (Fin #F)) := by
        rw [Fintype.card_perm, Fintype.card_fin]
    _ = #(univ.image t) := (card_image_of_injective _ hinj).symm
    _ ≤ #(tuplesWithProd A #F n) :=
        card_le_card fun p hp => by
          obtain ⟨σ, -, rfl⟩ := mem_image.1 hp
          exact ht σ

/-- A squarefree number has as many prime factors with multiplicity as without. -/
lemma length_primeFactorsList_of_squarefree {n : ℕ} (hn : Squarefree n) :
    n.primeFactorsList.length = #n.primeFactors := by
  rw [← Nat.toFinset_factors, List.toFinset_card_of_nodup hn.nodup_primeFactorsList]

/-! ### The decomposition -/

/-- The weight `a(n) = ∑_{2 ≤ j ≤ J} #{ordered factorizations of n into j primes of A} / j!`. -/
def compositeWeight (A : Finset ℕ) (J n : ℕ) : ℝ :=
  ∑ j ∈ Icc 2 J, ((j.factorial : ℝ))⁻¹ * #(tuplesWithProd A j n)

/-- `a(n)` is the term `j = Ω(n)`. -/
lemma compositeWeight_eq {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) (J n : ℕ) :
    compositeWeight A J n = if n.primeFactorsList.length ∈ Icc 2 J then
      ((n.primeFactorsList.length.factorial : ℝ))⁻¹ *
        #(tuplesWithProd A n.primeFactorsList.length n) else 0 := by
  rw [compositeWeight]
  split_ifs with h
  · refine sum_eq_single_of_mem _ h fun j _ hj => ?_
    have : #(tuplesWithProd A j n) = 0 := by
      by_contra hne
      exact hj ((card_tuplesWithProd_le hA j n).2 (card_pos.1 (Nat.pos_of_ne_zero hne))).symm
    rw [this, Nat.cast_zero, mul_zero]
  · refine sum_eq_zero fun j hj => ?_
    have : #(tuplesWithProd A j n) = 0 := by
      by_contra hne
      have := (card_tuplesWithProd_le hA j n).2 (card_pos.1 (Nat.pos_of_ne_zero hne))
      exact h (this ▸ hj)
    rw [this, Nat.cast_zero, mul_zero]

/-- `0 ≤ a(n) ≤ 1`. -/
lemma compositeWeight_mem {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) (J n : ℕ) :
    0 ≤ compositeWeight A J n ∧ compositeWeight A J n ≤ 1 := by
  rw [compositeWeight_eq hA]
  split_ifs
  · set j := n.primeFactorsList.length
    have hj : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    have hle : (#(tuplesWithProd A j n) : ℝ) ≤ j.factorial := by
      exact_mod_cast (card_tuplesWithProd_le hA j n).1
    refine ⟨by positivity, ?_⟩
    rw [inv_mul_le_iff₀ hj, mul_one]
    exact hle
  · exact ⟨le_rfl, zero_le_one⟩

/-- A prime has `a(p) = 0`. -/
lemma compositeWeight_prime {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) (J : ℕ) {p : ℕ}
    (hp : p.Prime) : compositeWeight A J p = 0 := by
  rw [compositeWeight_eq hA, Nat.primeFactorsList_prime hp, ite_eq_right (by simp)]

/-- A squarefree `n` with `2 ≤ ω(n) ≤ J` and prime factors in `A` has `a(n) = 1`. -/
lemma compositeWeight_squarefree {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) {J n : ℕ}
    (hn : Squarefree n) (hnA : n.primeFactors ⊆ A) (h2 : 2 ≤ #n.primeFactors)
    (hJ : #n.primeFactors ≤ J) : compositeWeight A J n = 1 := by
  rw [compositeWeight_eq hA, length_primeFactorsList_of_squarefree hn,
    ite_eq_left (mem_Icc.2 ⟨h2, hJ⟩), card_tuplesWithProd_of_squarefree hA hn hnA]
  have : ((#n.primeFactors).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  exact inv_mul_cancel₀ this

/-- The tuples with entries above `z` are the tuples from the primes above `z`. -/
lemma sum_piFinset_ite_eq {j : ℕ} (A : Finset ℕ) (z : ℝ) (F : (Fin j → ℕ) → ℝ) :
    ∑ p ∈ Fintype.piFinset (fun _ : Fin j => A), (if ∀ i, z < (p i : ℝ) then F p else 0) =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin j => A.filter fun q : ℕ => z < (q : ℝ)), F p := by
  rw [← sum_filter]
  congr 1
  ext p
  simp only [mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨h1 i, h2 i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

/-- The sum over `j`-tuples is a sum over their products, counted with multiplicity. -/
lemma sum_piFinset_eq_sum_tuplesWithProd {j : ℕ} (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N : ℕ) (G : ℕ → ℝ) (hG : ∀ n, N < n → G n = 0) :
    ∑ p ∈ Fintype.piFinset (fun _ : Fin j => A), G (∏ i, p i) =
      ∑ n ∈ Icc 1 N, #(tuplesWithProd A j n) * G n := by
  rw [Finset.sum_comp]
  simp only [nsmul_eq_mul]
  have hpos : ∀ p ∈ Fintype.piFinset (fun _ : Fin j => A), 0 < ∏ i, p i := fun p hp =>
    prod_pos fun i _ => (hA _ (Fintype.mem_piFinset.1 hp i)).pos
  set I := (Fintype.piFinset fun _ : Fin j => A).image fun p => ∏ i, p i
  -- both sides are the sum over the union of the two index sets
  calc ∑ n ∈ I, (#((Fintype.piFinset fun _ : Fin j => A).filter fun p => ∏ i, p i = n) : ℝ) * G n
      = ∑ n ∈ I ∪ Icc 1 N, (#(tuplesWithProd A j n) : ℝ) * G n := by
        refine sum_subset subset_union_left fun n _ hn => ?_
        have : #(tuplesWithProd A j n) = 0 := by
          rw [card_eq_zero, eq_empty_iff_forall_notMem]
          intro p hp
          obtain ⟨hpA, hprod⟩ := mem_filter.1 hp
          exact hn (mem_image.2 ⟨p, hpA, hprod⟩)
        change (#(tuplesWithProd A j n) : ℝ) * G n = 0
        rw [this, Nat.cast_zero, zero_mul]
    _ = ∑ n ∈ Icc 1 N, (#(tuplesWithProd A j n) : ℝ) * G n := by
        refine (sum_subset subset_union_right fun n hn hnN => ?_).symm
        obtain ⟨p, hp, rfl⟩ := mem_image.1 ((mem_union.1 hn).resolve_right hnN)
        have h1 := hpos p hp
        have : N < ∏ i, p i := by
          by_contra hle
          exact hnN (mem_Icc.2 ⟨h1, not_lt.1 hle⟩)
        rw [hG _ this, mul_zero]

/-- E3: the rough sum minus its prime part and `∑_{2 ≤ j ≤ J} Comp_j / j!` is
at most the sum of `|G|` over the rough `n ≤ Y` that are not squarefree with
`ω(n) ≤ J`. -/
lemma abs_sum_rough_sub_le {z Y : ℝ} (J : ℕ) (G : ℕ → ℝ) (hG1 : G 1 = 0)
    (hGY : ∀ n, ⌊Y⌋₊ < n → G n = 0) :
    |∑ n ∈ (Icc 1 ⌊Y⌋₊).filter (Rough z), G n -
        ∑ n ∈ (Icc 1 ⌊Y⌋₊).filter (fun n => Rough z n ∧ n.Prime), G n -
        ∑ j ∈ Icc 2 J, ((j.factorial : ℝ))⁻¹ *
          ∑ p ∈ Fintype.piFinset (fun _ : Fin j => primesIcc z Y),
            (if ∀ i, z < (p i : ℝ) then G (∏ i, p i) else 0)| ≤
      ∑ n ∈ (Icc 1 ⌊Y⌋₊).filter (fun n => Rough z n ∧ ¬ (Squarefree n ∧ #n.primeFactors ≤ J)),
        |G n| := by
  set N := ⌊Y⌋₊
  set A := (primesIcc z Y).filter fun q : ℕ => z < (q : ℝ)
  have hA : ∀ p ∈ A, p.Prime := fun p hp => (mem_filter.1 (mem_filter.1 hp).1).2
  -- the composite sums, by products
  have hcomp : ∑ j ∈ Icc 2 J, ((j.factorial : ℝ))⁻¹ *
      ∑ p ∈ Fintype.piFinset (fun _ : Fin j => primesIcc z Y),
        (if ∀ i, z < (p i : ℝ) then G (∏ i, p i) else 0) =
      ∑ n ∈ Icc 1 N, compositeWeight A J n * G n := by
    have hj : ∀ j : ℕ, ∑ p ∈ Fintype.piFinset (fun _ : Fin j => primesIcc z Y),
        (if ∀ i, z < (p i : ℝ) then G (∏ i, p i) else 0) =
        ∑ n ∈ Icc 1 N, #(tuplesWithProd A j n) * G n := by
      intro j
      rw [sum_piFinset_ite_eq]
      exact sum_piFinset_eq_sum_tuplesWithProd A hA N G hGY
    simp only [hj, compositeWeight, mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun n _ => sum_congr rfl fun j _ => by ring
  -- `a(n) = 0` off the rough numbers
  have hrough : ∀ n, compositeWeight A J n ≠ 0 → Rough z n := by
    intro n hn
    rw [compositeWeight] at hn
    obtain ⟨j, -, hj⟩ := exists_ne_zero_of_sum_ne_zero hn
    have hne : (tuplesWithProd A j n).Nonempty := by
      rw [← card_pos]
      by_contra h
      simp [Nat.eq_zero_of_not_pos h] at hj
    obtain ⟨p, hp⟩ := hne
    obtain ⟨hpA, rfl⟩ := mem_filter.1 hp
    rw [rough_iff]
    intro q hq hqd
    obtain ⟨i, -, hqi⟩ := (hq.prime.dvd_finsetProd_iff _).1 hqd
    have hpi := Fintype.mem_piFinset.1 hpA i
    rw [(Nat.prime_dvd_prime_iff_eq hq (hA _ hpi)).1 hqi]
    exact (mem_filter.1 hpi).2
  have hcomp' : ∑ n ∈ Icc 1 N, compositeWeight A J n * G n =
      ∑ n ∈ (Icc 1 N).filter (Rough z), compositeWeight A J n * G n := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    split_ifs with h
    · rfl
    · by_cases hw : compositeWeight A J n = 0
      · rw [hw, zero_mul]
      · exact absurd (hrough n hw) h
  have hsplit : ∑ n ∈ (Icc 1 N).filter (fun n => Rough z n ∧ n.Prime), G n =
      ∑ n ∈ (Icc 1 N).filter (Rough z), (if n.Prime then G n else 0) := by
    rw [sum_filter, sum_filter]
    exact sum_congr rfl fun n _ => by split_ifs <;> simp_all
  rw [hcomp, hcomp', hsplit, ← sum_sub_distrib, ← sum_sub_distrib]
  set R := (Icc 1 N).filter (Rough z)
  have hterm : ∀ n ∈ R, |G n - (if n.Prime then G n else 0) - compositeWeight A J n * G n| ≤
      if ¬ (Squarefree n ∧ #n.primeFactors ≤ J) then |G n| else 0 := by
    intro n hn
    obtain ⟨hnN, hnz⟩ := mem_filter.1 hn
    have hw := compositeWeight_mem hA J n
    by_cases hp : n.Prime
    · rw [ite_eq_left hp, compositeWeight_prime hA J hp]
      simp only [sub_self, zero_mul, abs_zero]
      split_ifs <;> simp
    rw [ite_eq_right hp, sub_zero]
    have h1 : |G n - compositeWeight A J n * G n| ≤ |G n| := by
      rw [show G n - compositeWeight A J n * G n = (1 - compositeWeight A J n) * G n by ring,
        abs_mul, abs_of_nonneg (by linarith)]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)
    by_cases hbad : Squarefree n ∧ #n.primeFactors ≤ J
    · rw [ite_eq_right (not_not.2 hbad)]
      obtain ⟨hsq, hJ⟩ := hbad
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · have : n = 1 := by have := (mem_Icc.1 hnN).1; omega
        rw [this, hG1]
        simp
      -- `ω(n) ≥ 2`, since `n` is squarefree, not prime and not `1`
      have hω : 2 ≤ #n.primeFactors := by
        by_contra hlt
        rw [not_le] at hlt
        have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by omega)
        have h1 : #n.primeFactors = 1 := by have := card_pos.2 hne; omega
        obtain ⟨q, hq⟩ := card_eq_one.1 h1
        have := Nat.prod_primeFactors_of_squarefree hsq
        rw [hq, prod_singleton] at this
        have hq' : q ∈ n.primeFactors := by rw [hq]; exact mem_singleton_self q
        exact hp (this ▸ Nat.prime_of_mem_primeFactors hq')
      have hnA : n.primeFactors ⊆ A := by
        intro q hq
        have hqp := Nat.prime_of_mem_primeFactors hq
        have hqn : q ≤ n := Nat.le_of_mem_primeFactors hq
        have hzq := rough_iff.1 hnz q hqp (Nat.dvd_of_mem_primeFactors hq)
        refine mem_filter.2 ⟨mem_filter.2 ⟨mem_Icc.2 ⟨Nat.ceil_le.2 hzq.le, ?_⟩, hqp⟩, hzq⟩
        exact hqn.trans (mem_Icc.1 hnN).2
      rw [compositeWeight_squarefree hA hsq hnA hω hJ]
      simp
    · rw [ite_eq_left hbad]
      exact h1
  calc _ ≤ ∑ n ∈ R, |G n - (if n.Prime then G n else 0) - compositeWeight A J n * G n| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ R, if ¬ (Squarefree n ∧ #n.primeFactors ≤ J) then |G n| else 0 :=
        sum_le_sum hterm
    _ = _ := by rw [← sum_filter, filter_filter]

/-! ### Nonsquarefree rough numbers -/

/-- `∑_{a < m ≤ b} 1 / m² ≤ 1/a - 1/b` for `1 ≤ a ≤ b`. -/
lemma sum_Ioc_inv_sq_le {a : ℕ} (ha : 1 ≤ a) : ∀ b : ℕ, a ≤ b →
    ∑ m ∈ Ioc a b, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / a - 1 / b := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ioc_succ_top hab]
    have hb : (1 : ℝ) ≤ b := by exact_mod_cast ha.trans hab
    have : (1 : ℝ) / ((b + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / b - 1 / ((b + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

/-- The multiples of `d` in `[1, N]` number `N / d`. -/
lemma card_filter_dvd_Icc (N d : ℕ) : #((Icc 1 N).filter (d ∣ ·)) = N / d := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div N d]
  congr 1

/-- At most `N / ⌊z⌋` of the rough `n ≤ N` are not squarefree. -/
lemma card_rough_not_squarefree_le {z : ℝ} (hz : 1 ≤ z) (N : ℕ) :
    (#((Icc 1 N).filter fun n => Rough z n ∧ ¬ Squarefree n) : ℝ) ≤ N / ⌊z⌋₊ := by
  have hz1 : 1 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  set P := (Ioc ⌊z⌋₊ N).filter Nat.Prime
  have hsub : (Icc 1 N).filter (fun n => Rough z n ∧ ¬ Squarefree n) ⊆
      P.biUnion fun p => (Icc 1 N).filter (p * p ∣ ·) := by
    intro n hn
    obtain ⟨hnN, hr, hsq⟩ := mem_filter.1 hn
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    simp only [not_forall, not_not] at hsq
    obtain ⟨p, hp, hpp⟩ := hsq
    have hpn : p ∣ n := (Dvd.intro p rfl).trans hpp
    have hzp := rough_iff.1 hr p hp hpn
    have hpN : p ≤ N := (Nat.le_of_dvd (mem_Icc.1 hnN).1 hpn).trans (mem_Icc.1 hnN).2
    refine mem_biUnion.2 ⟨p, mem_filter.2 ⟨mem_Ioc.2 ⟨?_, hpN⟩, hp⟩, mem_filter.2 ⟨hnN, hpp⟩⟩
    exact (Nat.floor_lt (by linarith)).2 hzp
  have h1 := (card_le_card hsub).trans card_biUnion_le
  calc (#((Icc 1 N).filter fun n => Rough z n ∧ ¬ Squarefree n) : ℝ)
      ≤ ∑ p ∈ P, (#((Icc 1 N).filter (p * p ∣ ·)) : ℝ) := by exact_mod_cast h1
    _ ≤ ∑ p ∈ P, (N : ℝ) / (p : ℝ) ^ 2 := by
        refine sum_le_sum fun p _ => ?_
        rw [card_filter_dvd_Icc]
        have := Nat.cast_div_le (α := ℝ) (m := N) (n := p * p)
        rw [sq]
        exact_mod_cast this
    _ ≤ ∑ m ∈ Ioc ⌊z⌋₊ N, (N : ℝ) / (m : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
    _ = N * ∑ m ∈ Ioc ⌊z⌋₊ N, (1 : ℝ) / (m : ℝ) ^ 2 := by
        rw [mul_sum]
        exact sum_congr rfl fun m _ => by ring
    _ ≤ N * (1 / ⌊z⌋₊) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rcases le_or_gt ⌊z⌋₊ N with h | h
        · have := sum_Ioc_inv_sq_le hz1 N h
          have : (0 : ℝ) ≤ 1 / N := by positivity
          linarith
        · rw [Ioc_eq_empty (by omega), sum_empty]
          positivity
    _ = N / ⌊z⌋₊ := by ring

/-! ### Rankin's bound for `2^{ω(n)}` -/

/-- Rankin: if `#{b ≤ Y' rough} ≤ D Y'` for `z ≤ Y' ≤ Y`, then
`∑_{n ≤ Y rough} 2^{ω(n)} ≤ D Y (1 + ∏_{z < p ≤ Y} (1 + 1/p))`. -/
lemma sum_two_pow_card_primeFactors_le {z Y D : ℝ} (hz : 0 ≤ z) (hzY : z ≤ Y)
    (hup : ∀ Y' : ℝ, z ≤ Y' → Y' ≤ Y → (#((Icc 1 ⌊Y'⌋₊).filter (Rough z)) : ℝ) ≤ D * Y') :
    ∑ n ∈ (Icc 1 ⌊Y⌋₊).filter (Rough z), (2 : ℝ) ^ #n.primeFactors ≤
      D * Y * (1 + ∏ p ∈ primesIoc z Y, (1 + 1 / (p : ℝ))) := by
  set R := (Icc 1 ⌊Y⌋₊).filter (Rough z)
  set Q := primesIoc z Y
  have hY0 : 0 ≤ Y := hz.trans hzY
  have hD : 0 ≤ D * Y := by
    have := hup Y hzY le_rfl
    linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ #((Icc 1 ⌊Y⌋₊).filter (Rough z)))]
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => (mem_primesIoc.1 hp).1
  -- the prime factors of a rough `n ≤ Y` lie in `Q`
  have hpfQ : ∀ n ∈ R, n.primeFactors ⊆ Q := by
    intro n hn q hq
    obtain ⟨hnY, hr⟩ := mem_filter.1 hn
    have hqp := Nat.prime_of_mem_primeFactors hq
    refine mem_primesIoc.2 ⟨hqp, rough_iff.1 hr q hqp (Nat.dvd_of_mem_primeFactors hq), ?_⟩
    have hqY : q ≤ ⌊Y⌋₊ := (Nat.le_of_mem_primeFactors hq).trans (mem_Icc.1 hnY).2
    have : (q : ℝ) ≤ ⌊Y⌋₊ := by exact_mod_cast hqY
    exact this.trans (Nat.floor_le hY0)
  -- `2^{ω(n)} = #{S ⊆ Q : S ⊆ ω(n)}`
  have h2 : ∀ n ∈ R, (2 : ℝ) ^ #n.primeFactors =
      ∑ S ∈ Q.powerset, if S ⊆ n.primeFactors then (1 : ℝ) else 0 := by
    intro n hn
    rw [sum_boole, show (2 : ℝ) ^ #n.primeFactors = ((2 ^ #n.primeFactors : ℕ) : ℝ) by
      push_cast; ring, ← card_powerset]
    congr 2
    ext S
    simp only [mem_filter, mem_powerset]
    exact ⟨fun h => ⟨h.trans (hpfQ n hn), h⟩, fun h => h.2⟩
  rw [sum_congr rfl h2, sum_comm]
  simp only [← sum_filter, sum_const, nsmul_one]
  -- each `S` contributes at most the rough `b ≤ Y / ∏ S`
  have hS : ∀ S ∈ Q.powerset, (#(R.filter fun n => S ⊆ n.primeFactors) : ℝ) ≤
      D * Y * (1 / ∏ p ∈ S, (p : ℝ)) +
        (if Y < z * ∏ p ∈ S, (p : ℝ) ∧ ∏ p ∈ S, (p : ℝ) ≤ Y then 1 else 0) := by
    intro S hSQ
    have hSp : ∀ p ∈ S, p.Prime := fun p hp => hQ p (mem_powerset.1 hSQ hp)
    set d := ∏ p ∈ S, p
    have hd : 0 < d := prod_pos fun p hp => (hSp p hp).pos
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hdc : ((d : ℕ) : ℝ) = ∏ p ∈ S, (p : ℝ) := by push_cast [d]; rfl
    rw [← hdc]
    -- the injection `n ↦ n / d`
    have hinj : #(R.filter fun n => S ⊆ n.primeFactors) ≤
        #((Icc 1 ⌊Y / d⌋₊).filter (Rough z)) := by
      refine card_le_card_of_injOn (fun n => n / d) (fun n hn => ?_) fun n₁ hn₁ n₂ hn₂ h => ?_
      · obtain ⟨hnR, hSn⟩ := mem_filter.1 hn
        obtain ⟨hnY, hr⟩ := mem_filter.1 hnR
        have hdn : d ∣ n := prod_primes_dvd n (fun p hp => (hSp p hp).prime)
          fun p hp => Nat.dvd_of_mem_primeFactors (hSn hp)
        obtain ⟨b, rfl⟩ := hdn
        have hb : (d * b) / d = b := Nat.mul_div_cancel_left b hd
        simp only [mem_coe, hb]
        have hb0 : 0 < b := by
          rcases Nat.eq_zero_or_pos b with h | h
          · simp [h] at hnY
          · exact h
        refine mem_filter.2 ⟨mem_Icc.2 ⟨hb0, Nat.le_floor ?_⟩, hr.of_dvd (Dvd.intro_left d rfl)⟩
        rw [le_div_iff₀ hd']
        have : ((d * b : ℕ) : ℝ) ≤ ⌊Y⌋₊ := by exact_mod_cast (mem_Icc.1 hnY).2
        have := this.trans (Nat.floor_le hY0)
        push_cast at this
        linarith
      · have hdvd : ∀ n ∈ R.filter (fun n => S ⊆ n.primeFactors), d ∣ n := fun n hn =>
          prod_primes_dvd n (fun p hp => (hSp p hp).prime)
            fun p hp => Nat.dvd_of_mem_primeFactors ((mem_filter.1 hn).2 hp)
        have h₁ := Nat.div_mul_cancel (hdvd n₁ hn₁)
        have h₂ := Nat.div_mul_cancel (hdvd n₂ hn₂)
        simp only at h
        rw [← h₁, ← h₂, h]
    refine (Nat.cast_le.2 hinj).trans ?_
    split_ifs with hcase
    · -- `Y / d < z`: only `b = 1` is rough
      have hle : #((Icc 1 ⌊Y / d⌋₊).filter (Rough z)) ≤ 1 := by
        refine card_le_one.2 fun b₁ hb₁ b₂ hb₂ => ?_
        have key : ∀ b ∈ (Icc 1 ⌊Y / d⌋₊).filter (Rough z), b = 1 := by
          intro b hb
          obtain ⟨hbY, hbr⟩ := mem_filter.1 hb
          by_contra hb1
          have h2 : 2 ≤ b := by have := (mem_Icc.1 hbY).1; omega
          have h3 := hbr.lt h2
          have h4 : (b : ℝ) ≤ Y / d := by
            have := (Nat.le_floor_iff (div_nonneg hY0 hd'.le)).1 (mem_Icc.1 hbY).2
            exact this
          have h5 : Y / d < z := by
            rw [div_lt_iff₀ hd']
            linarith [hcase.1]
          linarith
        rw [key b₁ hb₁, key b₂ hb₂]
      have : 0 ≤ D * Y * (1 / (d : ℝ)) := mul_nonneg hD (by positivity)
      have : (#((Icc 1 ⌊Y / d⌋₊).filter (Rough z)) : ℝ) ≤ 1 := by exact_mod_cast hle
      linarith
    · rcases le_or_gt (z : ℝ) (Y / d) with hzd | hzd
      · have := hup (Y / d) hzd (div_le_self hY0 (by exact_mod_cast hd))
        rw [mul_one_div] at *
        have : D * (Y / d) = D * Y / d := by ring
        linarith
      · -- `Y / d < z` and `Y < d`: there is no `b`
        have hYd : Y < d := by
          by_contra h
          rw [not_lt] at h
          exact hcase ⟨by rw [div_lt_iff₀ hd'] at hzd; linarith, h⟩
        have : ⌊Y / d⌋₊ = 0 := Nat.floor_eq_zero.2 ((div_lt_one hd').2 hYd)
        rw [this]
        simp only [zero_lt_one, Icc_eq_empty_of_lt, filter_empty, card_empty,
          Nat.cast_zero, add_zero]
        exact mul_nonneg hD (by positivity)
  refine (sum_le_sum hS).trans ?_
  rw [sum_add_distrib, ← mul_sum]
  -- the main part: `∑_S 1 / ∏ S = ∏ (1 + 1/p)`
  have hprod : ∑ S ∈ Q.powerset, 1 / ∏ p ∈ S, (p : ℝ) = ∏ p ∈ Q, (1 + 1 / (p : ℝ)) := by
    rw [show ∏ p ∈ Q, (1 + 1 / (p : ℝ)) = ∏ p ∈ Q, (1 / (p : ℝ) + 1) from
      prod_congr rfl fun p _ => add_comm _ _, prod_add]
    refine sum_congr rfl fun S _ => ?_
    simp
  -- the boundary part: the sets `S` with `Y / z < ∏ S ≤ Y` inject into the rough `m ≤ Y`
  have hbd : ∑ S ∈ Q.powerset,
      (if Y < z * ∏ p ∈ S, (p : ℝ) ∧ ∏ p ∈ S, (p : ℝ) ≤ Y then (1 : ℝ) else 0) ≤ D * Y := by
    rw [sum_boole]
    refine le_trans ?_ (hup Y hzY le_rfl)
    refine Nat.cast_le.2 (card_le_card_of_injOn (fun S => ∏ p ∈ S, p) (fun S hS => ?_)
      fun S₁ hS₁ S₂ hS₂ h => ?_)
    · obtain ⟨hSQ, -, hSY⟩ := mem_filter.1 hS
      have hSp : ∀ p ∈ S, p.Prime := fun p hp => hQ p (mem_powerset.1 hSQ hp)
      refine mem_filter.2 ⟨mem_Icc.2 ⟨prod_pos fun p hp => (hSp p hp).pos, Nat.le_floor ?_⟩, ?_⟩
      · push_cast
        exact hSY
      · rw [rough_iff]
        intro q hq hqd
        rw [dvd_prod_primes_iff' hSp hq] at hqd
        exact (mem_primesIoc.1 (mem_powerset.1 hSQ hqd)).2.1
    · have hS₁p : ∀ p ∈ S₁, p.Prime := fun p hp =>
        hQ p (mem_powerset.1 (mem_filter.1 hS₁).1 hp)
      have hS₂p : ∀ p ∈ S₂, p.Prime := fun p hp =>
        hQ p (mem_powerset.1 (mem_filter.1 hS₂).1 hp)
      rw [← Nat.primeFactors_prod hS₁p, ← Nat.primeFactors_prod hS₂p]
      exact congrArg Nat.primeFactors h
  rw [hprod]
  nlinarith

/-! ### The sieve upper bound for rough numbers -/

/-- `primesIcc 2 w` and `primesIoc 1 w` are both the primes up to `w`. -/
lemma primesIcc_two_eq (w : ℝ) : primesIcc 2 w = primesIoc 1 w := by
  ext p
  rw [mem_primesIcc_two, mem_primesIoc_one]

/-- Sets of primes inject into their products: a sum over the sets with
product at most `Y` is at most the sum over `r ≤ Y`. -/
lemma sum_powerset_prod_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (Y : ℝ) (F : ℕ → ℝ)
    (hF : ∀ r, 0 ≤ F r) :
    ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Y), F (∏ p ∈ D, p) ≤
      ∑ r ∈ Icc 1 ⌊Y⌋₊, F r := by
  have hinj : Set.InjOn (fun D : Finset ℕ => ∏ p ∈ D, p)
      (P.powerset.filter fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Y) := by
    intro D₁ h₁ D₂ h₂ h
    have hD₁ : ∀ p ∈ D₁, p.Prime := fun p hp =>
      hP p (mem_powerset.1 (mem_filter.1 h₁).1 hp)
    have hD₂ : ∀ p ∈ D₂, p.Prime := fun p hp =>
      hP p (mem_powerset.1 (mem_filter.1 h₂).1 hp)
    rw [← Nat.primeFactors_prod hD₁, ← Nat.primeFactors_prod hD₂]
    exact congrArg Nat.primeFactors h
  rw [← sum_image hinj]
  refine sum_le_sum_of_subset_of_nonneg (fun r hr => ?_) fun r _ _ => hF r
  obtain ⟨D, hD, rfl⟩ := mem_image.1 hr
  obtain ⟨hDP, hDY⟩ := mem_filter.1 hD
  exact mem_Icc.2 ⟨prod_pos fun p hp => (hP p (mem_powerset.1 hDP hp)).pos, Nat.le_floor hDY⟩

/-- There are at most `Y` sets of primes with product at most `Y`. -/
lemma card_powerset_prod_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {Y : ℝ} (hY : 0 ≤ Y) :
    (#(P.powerset.filter fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Y) : ℝ) ≤ Y := by
  have := sum_powerset_prod_le hP Y (fun _ => (1 : ℝ)) fun _ => zero_le_one
  simp only [sum_const, nsmul_one, Nat.card_Icc, Nat.add_sub_cancel] at this
  exact this.trans (Nat.floor_le hY)

/-- The number of multiples of `d ≥ 1` in `[1, Y]` is `Y / d + O(1)`:
`|⌊Y⌋ / d - Y / d| ≤ 2`. -/
lemma abs_card_multiples_sub_le {Y : ℝ} (hY : 0 ≤ Y) {d : ℕ} (hd : 0 < d) :
    |((⌊Y⌋₊ / d : ℕ) : ℝ) - Y / d| ≤ 2 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ((⌊Y⌋₊ / d : ℕ) : ℝ) ≤ Y / d :=
    Nat.cast_div_le.trans (div_le_div_of_nonneg_right (Nat.floor_le hY) hd'.le)
  have h2 : (⌊Y⌋₊ : ℝ) < ((⌊Y⌋₊ / d : ℕ) : ℝ) * d + d := by
    exact_mod_cast Nat.lt_div_mul_add (a := ⌊Y⌋₊) hd
  have h3 : Y < ⌊Y⌋₊ + 1 := Nat.lt_floor_add_one Y
  have h4 : Y / d - 2 ≤ ((⌊Y⌋₊ / d : ℕ) : ℝ) := by
    rw [div_sub' hd'.ne', div_le_iff₀ hd']
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- The sieve upper bound for rough numbers, from `BlockSieve` at fixed depth:
`#{b ≤ Y : P⁻(b) > z} ≤ D₀ Y / log z` for `2²⁰ ≤ z ≤ Y`. -/
lemma card_rough_le (h₃ : BlockSieve) : ∃ D₀ : ℝ, 0 ≤ D₀ ∧ ∀ z Y : ℝ, 2 ^ 20 ≤ z → z ≤ Y →
    (#((Icc 1 ⌊Y⌋₊).filter (Rough z)) : ℝ) ≤ D₀ * Y / Real.log z := by
  obtain ⟨C₀, hC₀⟩ := sum_inv_primes_block_le
  obtain ⟨h₀, KB, hBS⟩ := h₃ (1 / 2) C₀ (by norm_num)
  obtain ⟨CM, hCM, hprod⟩ := prod_one_sub_inv_primes_le
  refine ⟨|KB| * (20 * CM + 4), by positivity, fun z Y hz hzY => ?_⟩
  have hz0 : 0 < z := by linarith
  have hY0 : 0 < Y := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlzY : Real.log z ≤ Real.log Y := Real.log_le_log hz0 hzY
  set v := Y ^ (1 / 20 : ℝ)
  set w := min z v
  -- `2 ≤ w`, `log z ≤ 20 log w` and `w¹⁰ ≤ Y^{1/2}`
  have hv : z ^ (1 / 20 : ℝ) ≤ v := Real.rpow_le_rpow hz0.le hzY (by norm_num)
  have hz20 : (2 : ℝ) ≤ z ^ (1 / 20 : ℝ) := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (20 : ℝ)) ^ (1 / 20 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ z ^ (1 / 20 : ℝ) := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hz)
          (by norm_num)
  have hw2 : 2 ≤ w := le_min (by linarith [show (2 : ℝ) ≤ 2 ^ 20 by norm_num]) (hz20.trans hv)
  have hlv : Real.log v = Real.log Y / 20 := by
    rw [Real.log_rpow hY0]
    ring
  have hlw : Real.log z / 20 ≤ Real.log w := by
    rcases le_total z v with h | h
    · rw [show w = z from min_eq_left h]
      linarith
    · rw [show w = v from min_eq_right h, hlv]
      linarith
  have hlw0 : 0 < Real.log w := by linarith
  have hw10 : w ^ 10 ≤ Y ^ (1 / 2 : ℝ) := by
    calc w ^ 10 ≤ v ^ 10 := pow_le_pow_left₀ (by linarith) (min_le_right _ _) 10
      _ = Y ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
          norm_num
  have hsqrt : Y ^ (1 / 2 : ℝ) * Real.log z ≤ 2 * Y := by
    have h1 := Real.log_le_rpow_div hY0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : Y ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ) = Y := by
      rw [← Real.rpow_add hY0]
      norm_num
    have h3 : 0 ≤ Y ^ (1 / 2 : ℝ) := by positivity
    nlinarith
  -- the block sieve on `[1, Y]` with the primes up to `w`
  set P := primesIcc 2 w
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (mem_primesIcc_two.1 hp).1
  have hBS' := hBS (Icc 1 ⌊Y⌋₊) (fun _ => (1 : ℝ)) P w Y (fun p b => p ∣ b)
    (fun p => 1 / (p : ℝ)) (fun _ _ => zero_le_one) (by linarith)
    (fun p hp => mem_primesIcc_two.1 hp)
    hY0.le (fun p hp => by
      have := (hPp p hp).two_le
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast this
      constructor
      · positivity
      · rw [div_le_iff₀ (by linarith)]
        linarith)
    (hC₀ P hPp)
  simp only at hBS'
  have hup := hBS'.2
  -- the sifted count dominates the rough count
  have hsift : (#((Icc 1 ⌊Y⌋₊).filter (Rough z)) : ℝ) ≤
      ∑ i ∈ (Icc 1 ⌊Y⌋₊).filter (fun b => ∀ p ∈ P, ¬ p ∣ b), (1 : ℝ) := by
    rw [sum_const, nsmul_one]
    refine Nat.cast_le.2 (card_le_card fun b hb => ?_)
    obtain ⟨hbY, hbr⟩ := mem_filter.1 hb
    refine mem_filter.2 ⟨hbY, fun p hp => hbr p ?_⟩
    obtain ⟨hpp, hpw⟩ := mem_primesIcc_two.1 hp
    exact mem_primesIcc_two.2 ⟨hpp, hpw.trans (min_le_left _ _)⟩
  -- the main term
  have hmain : Y * ∏ p ∈ P, (1 - 1 / (p : ℝ)) ≤ Y * (20 * CM / Real.log z) := by
    refine mul_le_mul_of_nonneg_left ?_ hY0.le
    rw [show P = primesIoc 1 w from primesIcc_two_eq w]
    refine (hprod w hw2).trans ?_
    rw [div_le_div_iff₀ hlw0 hlz]
    nlinarith
  have hmain0 : 0 ≤ Y * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
    refine mul_nonneg hY0.le (prod_nonneg fun p hp => ?_)
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hPp p hp).two_le
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  -- the remainders
  have hrem : ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ w ^ 10),
      |∑ i ∈ (Icc 1 ⌊Y⌋₊).filter (fun b => ∀ p ∈ D, p ∣ b), (1 : ℝ) -
        Y * ∏ p ∈ D, 1 / (p : ℝ)| ≤ 2 * w ^ 10 := by
    have hterm : ∀ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ w ^ 10),
        |∑ i ∈ (Icc 1 ⌊Y⌋₊).filter (fun b => ∀ p ∈ D, p ∣ b), (1 : ℝ) -
          Y * ∏ p ∈ D, 1 / (p : ℝ)| ≤ 2 := by
      intro D hD
      have hDp : ∀ p ∈ D, p.Prime := fun p hp => hPp p (mem_powerset.1 (mem_filter.1 hD).1 hp)
      have hd : 0 < ∏ p ∈ D, p := prod_pos fun p hp => (hDp p hp).pos
      have hfilt : (Icc 1 ⌊Y⌋₊).filter (fun b => ∀ p ∈ D, p ∣ b) =
          (Icc 1 ⌊Y⌋₊).filter ((∏ p ∈ D, p) ∣ ·) := by
        refine filter_congr fun b _ => ⟨fun h => prod_primes_dvd b (fun p hp => (hDp p hp).prime)
          h, fun h p hp => (dvd_prod_of_mem _ hp).trans h⟩
      rw [hfilt, sum_const, nsmul_one, card_filter_dvd_Icc]
      have : Y * ∏ p ∈ D, 1 / (p : ℝ) = Y / ((∏ p ∈ D, p : ℕ) : ℝ) := by
        push_cast
        rw [prod_div_distrib, prod_const_one, mul_one_div]
      rw [this]
      exact abs_card_multiples_sub_le hY0.le hd
    calc _ ≤ ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ w ^ 10), (2 : ℝ) :=
          sum_le_sum hterm
      _ ≤ 2 * w ^ 10 := by
          rw [sum_const, nsmul_eq_mul, mul_comm]
          exact mul_le_mul_of_nonneg_left (card_powerset_prod_le hPp (by positivity))
            (by norm_num)
  have hrem0 : 0 ≤ ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ w ^ 10),
      |∑ i ∈ (Icc 1 ⌊Y⌋₊).filter (fun b => ∀ p ∈ D, p ∣ b), (1 : ℝ) -
        Y * ∏ p ∈ D, 1 / (p : ℝ)| := sum_nonneg fun _ _ => abs_nonneg _
  have hKB1 := mul_le_mul_of_nonneg_left hmain (abs_nonneg KB)
  have hKB2 := mul_le_mul_of_nonneg_left hrem (abs_nonneg KB)
  have hKB3 : KB * (Y * ∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤ |KB| * (Y * ∏ p ∈ P, (1 - 1 / (p : ℝ))) :=
    mul_le_mul_of_nonneg_right (le_abs_self KB) hmain0
  have hKB4 := mul_le_mul_of_nonneg_right (le_abs_self KB) hrem0
  have hfin : 2 * w ^ 10 ≤ 4 * Y / Real.log z := by
    rw [le_div_iff₀ hlz]
    nlinarith
  have hKB5 := mul_le_mul_of_nonneg_left hfin (abs_nonneg KB)
  calc (#((Icc 1 ⌊Y⌋₊).filter (Rough z)) : ℝ) ≤ _ := hsift
    _ ≤ _ := hup
    _ ≤ |KB| * (Y * (20 * CM / Real.log z)) + |KB| * (4 * Y / Real.log z) := by linarith
    _ = |KB| * (20 * CM + 4) * Y / Real.log z := by ring

end

end Sieve

end Erdos408
