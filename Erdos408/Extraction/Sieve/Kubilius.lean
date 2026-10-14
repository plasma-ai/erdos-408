module

public import Erdos408.Extraction.Sieve.Composite
public import Erdos408.Extraction.Sieve.Inert
public import Erdos408.Extraction.Sieve.Smooth

/-!
# The independent divisor model in progressions (Kubilius)

The core of the progression lemma E1. Fix a finite set `𝔅` of primes `p ≤ m`,
a nonnegative weight `f` on `[1, N]`, and coprime moduli `r, ℓ` with `ℓ`
coprime to `𝔅`. For `S ⊆ 𝔅` let `N(S)` be the weight of the `u` with
`r ∣ u + 1`, `ℓ ∣ u` whose set of prime divisors in `𝔅` is exactly `S`, and
let `X = (r ℓ)⁻¹ ∑ f`. Then `∑_S |N(S) - X π_𝔅(S)|` is small:

* sets `S` meeting the primes `p ∣ r` have `N(S) = 0`, and model mass
  `≤ ∑_{p ∣ r} 1/p`;
* for `S` with `∏ S ≤ Y₀`, `BlockSieve` at depth `h` with the sieving primes
  `𝔅 \ (S ∪ {p ∣ r})` gives `N(S) = X π(S) (1 + O(e^{-h}))` up to the
  remainders, which are smooth progression sums (`abs_sum_dvd_sub_le`);
* sets with `∏ S > Y₀` have small model mass `τ`, and the `u` with band part
  above `Y₀` are divisible by some `∏ S'` with `Y₀ < ∏ S' ≤ Y₀ m`.

Consequently, for every function `Ĥ` of the band set with `|Ĥ| ≤ 1`, the
weighted progression sum `∑ f(u) Ĥ(bandSet u)` is `X M_𝔅(Ĥ)` up to the same
error (`exists_abs_sum_bandSet_sub_le`).
-/

@[expose] public section

namespace Erdos408

open Filter Real Finset

namespace Sieve

noncomputable section

/-- The primes of `𝔅` dividing `u`. -/
def bandSet (𝔅 : Finset ℕ) (u : ℕ) : Finset ℕ :=
  𝔅.filter (· ∣ u)

/-! ### Counting with large band parts -/

/-- Greedy: a set of numbers in `[1, m]` with product above `Y ≥ 1` has a subset with
product in `(Y, Y m]`. -/
lemma exists_subset_prod_mem {m Y : ℝ} (hY : 1 ≤ Y) :
    ∀ S : Finset ℕ, (∀ p ∈ S, (p : ℝ) ≤ m) → Y < ∏ p ∈ S, (p : ℝ) →
      ∃ S' ⊆ S, Y < ∏ p ∈ S', (p : ℝ) ∧ ∏ p ∈ S', (p : ℝ) ≤ Y * m := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ h; simp at h; linarith
  | insert a S ha ih =>
    intro hS h
    by_cases hS₀ : Y < ∏ p ∈ S, (p : ℝ)
    · obtain ⟨S', hS', h1, h2⟩ := ih (fun p hp => hS p (mem_insert_of_mem hp)) hS₀
      exact ⟨S', hS'.trans (subset_insert a S), h1, h2⟩
    · refine ⟨insert a S, le_rfl, h, ?_⟩
      rw [prod_insert ha, mul_comm]
      have ha' : (a : ℝ) ≤ m := hS a (mem_insert_self a S)
      exact mul_le_mul (not_lt.1 hS₀) ha' (Nat.cast_nonneg _) (by linarith)

/-- There are at most `N / (r d) + 1` numbers `u ≤ N` with `r ∣ u + 1` and `d ∣ u`. -/
lemma card_filter_dvd_le {r d : ℕ} (hr : 0 < r) (hd : 0 < d) (N : ℕ) :
    (#((Icc 1 N).filter fun u => r ∣ u + 1 ∧ d ∣ u) : ℝ) ≤ N / ((r * d : ℕ) : ℝ) + 1 := by
  by_cases hrd : Nat.Coprime r d
  · obtain ⟨v, hv⟩ := exists_modEq_iff hr hrd
    rw [filter_congr fun u _ => hv u]
    have h := abs_card_modEq_sub_le (Nat.mul_pos hr hd) v (le_refl 1) (by omega : 1 ≤ N + 1)
    rw [Nat.add_sub_cancel] at h
    linarith [(abs_le.1 h).2]
  · have : (Icc 1 N).filter (fun u => r ∣ u + 1 ∧ d ∣ u) = ∅ := by
      rw [filter_eq_empty_iff]
      rintro u - ⟨h1, h2⟩
      apply hrd
      rw [Nat.Coprime, ← Nat.dvd_one, show 1 = (u + 1) - u by omega]
      exact Nat.dvd_sub ((Nat.gcd_dvd_left r d).trans h1) ((Nat.gcd_dvd_right r d).trans h2)
    rw [this, card_empty, Nat.cast_zero]
    positivity

/-- A prime of `𝔅` dividing `u` does not divide `r` when `r ∣ u + 1`. -/
lemma not_dvd_of_dvd_succ {p r u : ℕ} (hp : p.Prime) (hr : r ∣ u + 1) (hpu : p ∣ u) : ¬ p ∣ r :=
  fun h => hp.one_lt.ne' (Nat.dvd_one.1 (by
    have := (Nat.dvd_sub (h.trans hr) hpu)
    rwa [show u + 1 - u = 1 by omega] at this))

/-- The `u` with band part above `Y₀` number at most `N / (r ℓ) τ + Y₀ m`, where `τ` is the
reciprocal mass of the sets with product above `Y₀`. -/
lemma card_large_bandSet_le {𝔅 : Finset ℕ} {m : ℝ} (h𝔅 : ∀ p ∈ 𝔅, p.Prime ∧ (p : ℝ) ≤ m)
    (hm : 1 ≤ m) {N r ℓ : ℕ} (hr : 0 < r) (hℓ : 0 < ℓ) (hℓ𝔅 : ∀ p ∈ 𝔅, ¬ p ∣ ℓ) {Y₀ : ℝ}
    (hY₀ : 1 ≤ Y₀) :
    (#((Icc 1 N).filter fun u => (r ∣ u + 1 ∧ ℓ ∣ u) ∧
        Y₀ < ∏ p ∈ bandSet 𝔅 u, (p : ℝ)) : ℝ) ≤
      N / ((r * ℓ : ℕ) : ℝ) *
          ∑ S ∈ 𝔅.powerset.filter (fun S : Finset ℕ => Y₀ < ∏ p ∈ S, (p : ℝ)),
            1 / ∏ p ∈ S, (p : ℝ) +
        Y₀ * m := by
  set T := 𝔅.powerset.filter fun S : Finset ℕ => Y₀ < ∏ p ∈ S, (p : ℝ) ∧ ∏ p ∈ S, (p : ℝ) ≤ Y₀ * m
  have h𝔅p : ∀ p ∈ 𝔅, p.Prime := fun p hp => (h𝔅 p hp).1
  -- every such `u` is divisible by `ℓ ∏ S'` for some `S' ∈ T`
  have hsub : (Icc 1 N).filter (fun u => (r ∣ u + 1 ∧ ℓ ∣ u) ∧
      Y₀ < ∏ p ∈ bandSet 𝔅 u, (p : ℝ)) ⊆
      T.biUnion fun S : Finset ℕ => (Icc 1 N).filter fun u => r ∣ u + 1 ∧ ℓ * ∏ p ∈ S, p ∣ u := by
    intro u hu
    obtain ⟨hu1, ⟨hru, hℓu⟩, hY⟩ := mem_filter.1 hu
    obtain ⟨S', hS', h1, h2⟩ := exists_subset_prod_mem hY₀ (bandSet 𝔅 u)
      (fun p hp => (h𝔅 p (mem_filter.1 hp).1).2) hY
    have hS'𝔅 : S' ⊆ 𝔅 := hS'.trans (filter_subset _ _)
    have hdvd : ∏ p ∈ S', p ∣ u := prod_primes_dvd u
      (fun p hp => (h𝔅p p (hS'𝔅 hp)).prime) fun p hp => (mem_filter.1 (hS' hp)).2
    have hcop : Nat.Coprime ℓ (∏ p ∈ S', p) := Nat.Coprime.prod_right fun p hp =>
      ((h𝔅p p (hS'𝔅 hp)).coprime_iff_not_dvd.2 (hℓ𝔅 p (hS'𝔅 hp))).symm
    exact mem_biUnion.2 ⟨S', mem_filter.2 ⟨mem_powerset.2 hS'𝔅, h1, h2⟩,
      mem_filter.2 ⟨hu1, hru, hcop.mul_dvd_of_dvd_of_dvd hℓu hdvd⟩⟩
  have hprod : ∀ S ∈ T, ((∏ p ∈ S, p : ℕ) : ℝ) = ∏ p ∈ S, (p : ℝ) := fun S _ => by push_cast; rfl
  have hpos : ∀ S ∈ T, 0 < ∏ p ∈ S, p := fun S hS => prod_pos fun p hp =>
    (h𝔅p p (mem_powerset.1 (mem_filter.1 hS).1 hp)).pos
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : ∀ S ∈ T, (#((Icc 1 N).filter fun u => r ∣ u + 1 ∧ ℓ * ∏ p ∈ S, p ∣ u) : ℝ) ≤
      N / ((r * ℓ : ℕ) : ℝ) * (1 / ∏ p ∈ S, (p : ℝ)) + 1 := by
    intro S hS
    refine (card_filter_dvd_le hr (Nat.mul_pos hℓ (hpos S hS)) N).trans (le_of_eq ?_)
    rw [← hprod S hS]
    push_cast
    field_simp
  have hT : (#T : ℝ) ≤ Y₀ * m := by
    refine le_trans ?_ (card_powerset_prod_le h𝔅p (by positivity : (0 : ℝ) ≤ Y₀ * m))
    refine Nat.cast_le.2 (card_le_card fun S hS => ?_)
    obtain ⟨hS𝔅, -, h⟩ := mem_filter.1 hS
    refine mem_filter.2 ⟨hS𝔅, ?_⟩
    push_cast
    exact h
  have hτ : ∑ S ∈ T, 1 / ∏ p ∈ S, (p : ℝ) ≤
      ∑ S ∈ 𝔅.powerset.filter (fun S : Finset ℕ => Y₀ < ∏ p ∈ S, (p : ℝ)),
        1 / ∏ p ∈ S, (p : ℝ) := by
    refine sum_le_sum_of_subset_of_nonneg (fun S hS => ?_) fun S _ _ => ?_
    · obtain ⟨hS𝔅, h, -⟩ := mem_filter.1 hS
      exact mem_filter.2 ⟨hS𝔅, h⟩
    · exact div_nonneg zero_le_one (prod_nonneg fun p _ => Nat.cast_nonneg p)
  have hN : 0 ≤ N / ((r * ℓ : ℕ) : ℝ) := by positivity
  calc (#((Icc 1 N).filter fun u => (r ∣ u + 1 ∧ ℓ ∣ u) ∧
        Y₀ < ∏ p ∈ bandSet 𝔅 u, (p : ℝ)) : ℝ)
      ≤ ∑ S ∈ T, (#((Icc 1 N).filter fun u => r ∣ u + 1 ∧ ℓ * ∏ p ∈ S, p ∣ u) : ℝ) := by
        exact_mod_cast h1
    _ ≤ ∑ S ∈ T, (N / ((r * ℓ : ℕ) : ℝ) * (1 / ∏ p ∈ S, (p : ℝ)) + 1) := sum_le_sum h2
    _ = N / ((r * ℓ : ℕ) : ℝ) * ∑ S ∈ T, 1 / ∏ p ∈ S, (p : ℝ) + #T := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_one]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hτ hN) hT

/-! ### The fibers over band sets -/

/-- The `u ≤ N` with `r ∣ u + 1` and `ℓ ∣ u`. -/
def progSet (N r ℓ : ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun u => r ∣ u + 1 ∧ ℓ ∣ u

/-- The weight `N(S)` of the progression with band set exactly `S`. -/
def fiberSum (𝔅 : Finset ℕ) (N r ℓ : ℕ) (f : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∑ u ∈ (progSet N r ℓ).filter (fun u => bandSet 𝔅 u = S), f u

/-- The model size `X = (r ℓ)⁻¹ ∑ f` of the progression. -/
def progMain (N r ℓ : ℕ) (f : ℕ → ℝ) : ℝ :=
  1 / ((r * ℓ : ℕ) : ℝ) * ∑ u ∈ Icc 1 N, f u

/-- The band primes not dividing `r`. -/
def bandCoprime (𝔅 : Finset ℕ) (r : ℕ) : Finset ℕ :=
  𝔅 \ 𝔅.filter (· ∣ r)

/-- The weighted progression sum is the sum of the fibers. -/
lemma sum_progSet_eq_sum_fiberSum (𝔅 : Finset ℕ) (N r ℓ : ℕ) (f : ℕ → ℝ)
    (Ĥ : Finset ℕ → ℝ) :
    ∑ u ∈ progSet N r ℓ, f u * Ĥ (bandSet 𝔅 u) =
      ∑ S ∈ 𝔅.powerset, fiberSum 𝔅 N r ℓ f S * Ĥ S := by
  rw [← sum_fiberwise_of_maps_to (g := bandSet 𝔅) (t := 𝔅.powerset)
    (fun u _ => mem_powerset.2 (filter_subset _ _))]
  refine sum_congr rfl fun S _ => ?_
  rw [fiberSum, sum_mul]
  exact sum_congr rfl fun u hu => by rw [(mem_filter.1 hu).2]

/-- Sets meeting the primes `p ∣ r` carry no weight. -/
lemma fiberSum_eq_zero {𝔅 : Finset ℕ} (h𝔅 : ∀ p ∈ 𝔅, p.Prime) {N r ℓ : ℕ} (f : ℕ → ℝ)
    {S : Finset ℕ} (hS : ¬ S ⊆ bandCoprime 𝔅 r) (hS𝔅 : S ⊆ 𝔅) : fiberSum 𝔅 N r ℓ f S = 0 := by
  refine sum_eq_zero fun u hu => ?_
  exfalso
  obtain ⟨hu, hband⟩ := mem_filter.1 hu
  obtain ⟨-, hru, -⟩ := mem_filter.1 hu
  obtain ⟨p, hpS, hp⟩ := not_subset.1 hS
  have hp𝔅 := hS𝔅 hpS
  have hpr : p ∣ r := by
    by_contra h
    exact hp (mem_sdiff.2 ⟨hp𝔅, fun h' => h (mem_filter.1 h').2⟩)
  have hpu : p ∣ u := by
    rw [← hband] at hpS
    exact (mem_filter.1 hpS).2
  exact not_dvd_of_dvd_succ (h𝔅 p hp𝔅) hru hpu hpr

/-- The model mass of the sets meeting the primes `p ∣ r` is at most `∑_{p ∣ r} 1/p`. -/
lemma sum_modelWeight_not_subset_le {𝔅 : Finset ℕ} (h𝔅 : ∀ p ∈ 𝔅, 0 < p) (r : ℕ) :
    ∑ S ∈ 𝔅.powerset.filter (fun S => ¬ S ⊆ bandCoprime 𝔅 r), modelWeight 𝔅 S ≤
      ∑ p ∈ 𝔅.filter (· ∣ r), (1 : ℝ) / p := by
  set R := 𝔅.filter (· ∣ r)
  have h1 : ∀ S ∈ 𝔅.powerset.filter (fun S => ¬ S ⊆ bandCoprime 𝔅 r),
      modelWeight 𝔅 S ≤ ∑ p ∈ R, if p ∈ S then modelWeight 𝔅 S else 0 := by
    intro S hS
    obtain ⟨hS𝔅, hS'⟩ := mem_filter.1 hS
    obtain ⟨p, hpS, hp⟩ := not_subset.1 hS'
    have hpR : p ∈ R := by
      by_contra h
      exact hp (mem_sdiff.2 ⟨mem_powerset.1 hS𝔅 hpS, h⟩)
    rw [← sum_filter]
    exact single_le_sum (f := fun _ => modelWeight 𝔅 S) (fun _ _ => modelWeight_nonneg h𝔅 S)
      (mem_filter.2 ⟨hpR, hpS⟩)
  refine (sum_le_sum h1).trans ?_
  rw [sum_comm]
  refine sum_le_sum fun p hp => ?_
  rw [← sum_modelWeight_mem (mem_filter.1 hp).1, ← sum_filter]
  exact sum_le_sum_of_subset_of_nonneg (fun S hS => by
    obtain ⟨hS1, hS2⟩ := mem_filter.1 hS
    exact mem_filter.2 ⟨(mem_filter.1 hS1).1, hS2⟩) fun S _ _ => modelWeight_nonneg h𝔅 S

/-! ### The sieve on one fiber -/

/-- `BlockSieve` for the divisibility conditions `p ∣ u` with `g(p) = 1/p`, at fixed
constants `h₀` and `K`. -/
def DvdSieve (h₀ : ℕ) (KB : ℝ) : Prop :=
  ∀ (objs : Finset ℕ) (wt : ℕ → ℝ) (P : Finset ℕ) (z X : ℝ), (∀ u ∈ objs, 0 ≤ wt u) → 1 ≤ z →
    (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) → 0 ≤ X → ∀ h : ℕ, Even h → h₀ ≤ h →
    |∑ u ∈ objs.filter (fun u => ∀ p ∈ P, ¬ p ∣ u), wt u - X * ∏ p ∈ P, (1 - 1 / (p : ℝ))| ≤
      KB * exp (-(h : ℝ)) * (X * ∏ p ∈ P, (1 - 1 / (p : ℝ))) +
        KB * ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * h + 2)),
          |∑ u ∈ objs.filter (fun u => ∀ p ∈ D, p ∣ u), wt u - X * ∏ p ∈ D, 1 / (p : ℝ)|

/-- `BlockSieve` gives the divisibility sieve. -/
lemma exists_dvdSieve (h₃ : BlockSieve) : ∃ (h₀ : ℕ) (KB : ℝ), DvdSieve h₀ KB := by
  obtain ⟨C₀, hC₀⟩ := sum_inv_primes_block_le
  obtain ⟨h₀, KB, hBS⟩ := h₃ (1 / 2) C₀ (by norm_num)
  refine ⟨h₀, KB, fun objs wt P z X hwt hz hP hX h heven hh => ?_⟩
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have h' := hBS objs wt P z X (fun p u => p ∣ u) (fun p => 1 / (p : ℝ)) hwt hz hP hX
    (fun p hp => by
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hPp p hp).two_le
      constructor
      · positivity
      · rw [div_le_iff₀ (by linarith)]
        linarith)
    (hC₀ P hPp)
  simp only at h'
  exact h'.1 h heven hh

/-- A product of primes not dividing `n` is coprime to `n`. -/
lemma coprime_prod_of_not_dvd {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {n : ℕ}
    (hn : ∀ p ∈ S, ¬ p ∣ n) : Nat.Coprime n (∏ p ∈ S, p) :=
  Nat.Coprime.prod_right fun p hp => ((hS p hp).coprime_iff_not_dvd.2 (hn p hp)).symm

/-- Products over disjoint sets of primes are coprime. -/
lemma coprime_prod_prod {S D : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hD : ∀ p ∈ D, p.Prime)
    (hSD : Disjoint S D) : Nat.Coprime (∏ p ∈ S, p) (∏ p ∈ D, p) :=
  Nat.Coprime.prod_left fun p hp => coprime_prod_of_not_dvd hD fun q hq hqp =>
    disjoint_left.1 hSD hp (by rwa [(Nat.prime_dvd_prime_iff_eq (hD q hq) (hS p hp)).1 hqp] at hq)

/-- The sieve on one fiber: for `S` avoiding the primes `p ∣ r`,
`N(S) = X π'(S) (1 + O(e^{-h})) + O(m^{4h+2} V)` with `π'` the model on the band primes
coprime to `r`. -/
lemma abs_fiberSum_sub_le {h₀ : ℕ} {KB : ℝ} (hBS : DvdSieve h₀ KB) {𝔅 : Finset ℕ} {m : ℝ}
    (h𝔅 : ∀ p ∈ 𝔅, p.Prime ∧ (p : ℝ) ≤ m) (hm : 1 ≤ m) {N r ℓ : ℕ} (hr : 0 < r) (hℓ : 0 < ℓ)
    (hrℓ : Nat.Coprime r ℓ) (hℓ𝔅 : ∀ p ∈ 𝔅, ¬ p ∣ ℓ) {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hf : ∀ u, 0 ≤ f u) {V : ℝ} (hV : ∑ k ∈ Icc 1 N, |f k - f (k - 1)| ≤ V) {h : ℕ}
    (heven : Even h) (hh : h₀ ≤ h) {S : Finset ℕ} (hS : S ⊆ bandCoprime 𝔅 r) :
    |fiberSum 𝔅 N r ℓ f S - progMain N r ℓ f * modelWeight (bandCoprime 𝔅 r) S| ≤
      |KB| * exp (-(h : ℝ)) * (progMain N r ℓ f * modelWeight (bandCoprime 𝔅 r) S) +
        |KB| * (m ^ (4 * h + 2) * V) := by
  set 𝔅' := bandCoprime 𝔅 r
  have h𝔅' : ∀ p ∈ 𝔅', p ∈ 𝔅 ∧ ¬ p ∣ r := fun p hp => by
    obtain ⟨h1, h2⟩ := mem_sdiff.1 hp
    exact ⟨h1, fun h => h2 (mem_filter.2 ⟨h1, h⟩)⟩
  have h𝔅p : ∀ p ∈ 𝔅, p.Prime := fun p hp => (h𝔅 p hp).1
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => h𝔅p p (h𝔅' p (hS hp)).1
  set P := 𝔅' \ S
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => h𝔅p p (h𝔅' p (mem_sdiff.1 hp).1).1
  set d := ℓ * ∏ p ∈ S, p
  have hd : 0 < d := Nat.mul_pos hℓ (prod_pos fun p hp => (hSp p hp).pos)
  have hℓS : Nat.Coprime ℓ (∏ p ∈ S, p) :=
    coprime_prod_of_not_dvd hSp fun p hp => hℓ𝔅 p (h𝔅' p (hS hp)).1
  set objs := (Icc 1 N).filter fun u => r ∣ u + 1 ∧ d ∣ u
  set X' := progMain N r ℓ f * ∏ p ∈ S, (1 : ℝ) / p
  have hX0 : 0 ≤ progMain N r ℓ f := by
    rw [progMain]
    exact mul_nonneg (by positivity) (sum_nonneg fun u _ => hf u)
  have hX'0 : 0 ≤ X' := mul_nonneg hX0 (prod_nonneg fun p _ => by positivity)
  -- the sifted set is the fiber over `S`
  have hset : objs.filter (fun u => ∀ p ∈ P, ¬ p ∣ u) =
      (progSet N r ℓ).filter (fun u => bandSet 𝔅 u = S) := by
    ext u
    simp only [objs, progSet, mem_filter]
    constructor
    · rintro ⟨⟨hu, hru, hdu⟩, hP⟩
      refine ⟨⟨hu, hru, (Dvd.intro _ rfl).trans hdu⟩, ?_⟩
      ext p
      simp only [bandSet, mem_filter]
      constructor
      · rintro ⟨hp𝔅, hpu⟩
        by_contra hpS
        by_cases hpr : p ∣ r
        · exact not_dvd_of_dvd_succ (h𝔅p p hp𝔅) hru hpu hpr
        · exact hP p (mem_sdiff.2 ⟨mem_sdiff.2 ⟨hp𝔅, fun h => hpr (mem_filter.1 h).2⟩, hpS⟩) hpu
      · intro hpS
        exact ⟨(h𝔅' p (hS hpS)).1, (dvd_prod_of_mem _ hpS).trans ((Dvd.intro_left _ rfl).trans hdu)⟩
    · rintro ⟨⟨hu, hru, hℓu⟩, hband⟩
      have hSu : ∏ p ∈ S, p ∣ u := prod_primes_dvd u (fun p hp => (hSp p hp).prime)
        fun p hp => by rw [← hband] at hp; exact (mem_filter.1 hp).2
      refine ⟨⟨hu, hru, hℓS.mul_dvd_of_dvd_of_dvd hℓu hSu⟩, fun p hp hpu => ?_⟩
      obtain ⟨hp𝔅', hpS⟩ := mem_sdiff.1 hp
      exact hpS (by rw [← hband]; exact mem_filter.2 ⟨(h𝔅' p hp𝔅').1, hpu⟩)
  -- the main term is the model weight
  have hmain : X' * ∏ p ∈ P, (1 - 1 / (p : ℝ)) = progMain N r ℓ f * modelWeight 𝔅' S := by
    rw [modelWeight]
    ring
  -- each remainder is a smooth progression error
  have hrem : ∀ D ∈ P.powerset,
      |∑ u ∈ objs.filter (fun u => ∀ p ∈ D, p ∣ u), f u - X' * ∏ p ∈ D, 1 / (p : ℝ)| ≤ V := by
    intro D hD
    have hDP := mem_powerset.1 hD
    have hDp : ∀ p ∈ D, p.Prime := fun p hp => hPp p (hDP hp)
    have hdD : Nat.Coprime d (∏ p ∈ D, p) := by
      refine Nat.coprime_mul_iff_left.2 ⟨coprime_prod_of_not_dvd hDp fun p hp =>
        hℓ𝔅 p (h𝔅' p (mem_sdiff.1 (hDP hp)).1).1, coprime_prod_prod hSp hDp ?_⟩
      exact disjoint_left.2 fun p hpS hpD => (mem_sdiff.1 (hDP hpD)).2 hpS
    have hrd : Nat.Coprime r (d * ∏ p ∈ D, p) := by
      refine Nat.Coprime.mul_right (Nat.Coprime.mul_right hrℓ ?_) ?_
      · exact coprime_prod_of_not_dvd hSp fun p hp => (h𝔅' p (hS hp)).2
      · exact coprime_prod_of_not_dvd hDp fun p hp => (h𝔅' p (mem_sdiff.1 (hDP hp)).1).2
    have hfilt : objs.filter (fun u => ∀ p ∈ D, p ∣ u) =
        (Icc 1 N).filter (fun u => r ∣ u + 1 ∧ d * ∏ p ∈ D, p ∣ u) := by
      ext u
      simp only [objs, mem_filter]
      constructor
      · rintro ⟨⟨hu, hru, hdu⟩, hD'⟩
        exact ⟨hu, hru, hdD.mul_dvd_of_dvd_of_dvd hdu
          (prod_primes_dvd u (fun p hp => (hDp p hp).prime) hD')⟩
      · rintro ⟨hu, hru, h⟩
        exact ⟨⟨hu, hru, (Dvd.intro _ rfl).trans h⟩, fun p hp =>
          (dvd_prod_of_mem _ hp).trans ((Dvd.intro_left _ rfl).trans h)⟩
    have hX : X' * ∏ p ∈ D, 1 / (p : ℝ) = 1 / ((r * (d * ∏ p ∈ D, p) : ℕ) : ℝ) *
        ∑ u ∈ Icc 1 N, f u := by
      simp only [X', progMain, d]
      push_cast
      rw [prod_div_distrib, prod_div_distrib, prod_const_one, prod_const_one]
      field_simp
    rw [hfilt, hX]
    exact (abs_sum_dvd_sub_le hr (Nat.mul_pos hd (prod_pos fun p hp => (hDp p hp).pos)) hrd N
      hf0).trans hV
  have hsum : ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ m ^ (4 * h + 2)),
      |∑ u ∈ objs.filter (fun u => ∀ p ∈ D, p ∣ u), f u - X' * ∏ p ∈ D, 1 / (p : ℝ)| ≤
      m ^ (4 * h + 2) * V := by
    have hV0 : 0 ≤ V := (sum_nonneg fun _ _ => abs_nonneg _).trans hV
    calc _ ≤ ∑ _D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ m ^ (4 * h + 2)), V :=
          sum_le_sum fun D hD => hrem D (mem_filter.1 hD).1
      _ = #(P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ m ^ (4 * h + 2))) * V := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ m ^ (4 * h + 2) * V :=
          mul_le_mul_of_nonneg_right (card_powerset_prod_le hPp (by positivity)) hV0
  have hsieve := hBS objs f P m X' (fun u _ => hf u) hm (fun p hp =>
    ⟨hPp p hp, (h𝔅 p (h𝔅' p (mem_sdiff.1 hp).1).1).2⟩) hX'0 h heven hh
  rw [hset, hmain] at hsieve
  have hw0 : 0 ≤ progMain N r ℓ f * modelWeight 𝔅' S :=
    mul_nonneg hX0 (modelWeight_nonneg (fun p hp => (h𝔅p p (h𝔅' p hp).1).pos) S)
  have hrem0 : 0 ≤ ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ m ^ (4 * h + 2)),
      |∑ u ∈ objs.filter (fun u => ∀ p ∈ D, p ∣ u), f u - X' * ∏ p ∈ D, 1 / (p : ℝ)| :=
    sum_nonneg fun _ _ => abs_nonneg _
  have h1 : KB * exp (-(h : ℝ)) * (progMain N r ℓ f * modelWeight 𝔅' S) ≤
      |KB| * exp (-(h : ℝ)) * (progMain N r ℓ f * modelWeight 𝔅' S) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (exp_pos _).le) hw0
  have h2 := mul_le_mul_of_nonneg_right (le_abs_self KB) hrem0
  have h3 := mul_le_mul_of_nonneg_left hsum (abs_nonneg KB)
  calc _ ≤ _ := hsieve
    _ ≤ _ := by linarith

/-! ### The total variation of the band sets -/

/-- The model weight of `S` is at most `1 / ∏ S`. -/
lemma modelWeight_le_inv_prod {A : Finset ℕ} (hA : ∀ p ∈ A, 0 < p) (S : Finset ℕ) :
    modelWeight A S ≤ 1 / ∏ p ∈ S, (p : ℝ) := by
  rw [modelWeight, one_div, ← prod_inv_distrib]
  have h1 : ∏ p ∈ A \ S, (1 - (1 : ℝ) / p) ≤ 1 := prod_le_one₀ (fun p hp => by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hA p (mem_sdiff.1 hp).1
    rw [sub_nonneg, div_le_one (by linarith)]
    exact this) fun p _ => by
      have : 0 ≤ (1 : ℝ) / p := by positivity
      linarith
  have h0 : 0 ≤ ∏ p ∈ S, (1 : ℝ) / p := prod_nonneg fun p _ => by positivity
  calc (∏ p ∈ S, (1 : ℝ) / p) * ∏ p ∈ A \ S, (1 - (1 : ℝ) / p) ≤ (∏ p ∈ S, (1 : ℝ) / p) * 1 :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = ∏ p ∈ S, (p : ℝ)⁻¹ := by simp

/-- The fibers avoiding the primes `p ∣ r` with `∏ S ≤ Y₀`. -/
lemma sum_small_fibers_le {h₀ : ℕ} {KB : ℝ} (hBS : DvdSieve h₀ KB) {𝔅 : Finset ℕ} {m : ℝ}
    (h𝔅 : ∀ p ∈ 𝔅, p.Prime ∧ (p : ℝ) ≤ m) (hm : 1 ≤ m) {N r ℓ : ℕ} (hr : 0 < r) (hℓ : 0 < ℓ)
    (hrℓ : Nat.Coprime r ℓ) (hℓ𝔅 : ∀ p ∈ 𝔅, ¬ p ∣ ℓ) {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hf : ∀ u, 0 ≤ f u) {V : ℝ} (hV : ∑ k ∈ Icc 1 N, |f k - f (k - 1)| ≤ V) {h : ℕ}
    (heven : Even h) (hh : h₀ ≤ h) {Y₀ : ℝ} (hY₀ : 1 ≤ Y₀) :
    ∑ S ∈ 𝔅.powerset.filter (fun S => S ⊆ bandCoprime 𝔅 r ∧ ∏ p ∈ S, (p : ℝ) ≤ Y₀),
        |fiberSum 𝔅 N r ℓ f S - progMain N r ℓ f * modelWeight 𝔅 S| ≤
      progMain N r ℓ f * (|KB| * exp (-(h : ℝ)) + ∑ p ∈ 𝔅.filter (· ∣ r), (1 : ℝ) / p) +
        Y₀ * (|KB| * (m ^ (4 * h + 2) * V)) := by
  set 𝔅' := bandCoprime 𝔅 r
  set Q := 𝔅.powerset.filter (fun S => S ⊆ 𝔅' ∧ ∏ p ∈ S, (p : ℝ) ≤ Y₀)
  set X := progMain N r ℓ f
  set σ := ∑ p ∈ 𝔅.filter (· ∣ r), (1 : ℝ) / p
  have h𝔅p : ∀ p ∈ 𝔅, p.Prime := fun p hp => (h𝔅 p hp).1
  have h𝔅'0 : ∀ p ∈ 𝔅', 0 < p := fun p hp => (h𝔅p p (mem_sdiff.1 hp).1).pos
  have hX0 : 0 ≤ X := by
    simp only [X, progMain]
    exact mul_nonneg (by positivity) (sum_nonneg fun u _ => hf u)
  have hR : 𝔅.filter (· ∣ r) ⊆ 𝔅 := filter_subset _ _
  -- the model weights on `𝔅` and on `𝔅'`
  have hw : ∀ S ∈ Q, |X * modelWeight 𝔅' S - X * modelWeight 𝔅 S| ≤
      X * modelWeight 𝔅' S * σ := by
    intro S hS
    have hS' := (mem_filter.1 hS).2.1
    have hsd : modelWeight 𝔅 S = modelWeight 𝔅' S * ∏ p ∈ 𝔅.filter (· ∣ r), (1 - (1 : ℝ) / p) :=
      modelWeight_sdiff hR hS'
    rw [hsd]
    have h0 : 0 ≤ modelWeight 𝔅' S := modelWeight_nonneg h𝔅'0 S
    have hprod := prod_mem_unit (𝔅.filter (· ∣ r)) (fun p => 1 - (1 : ℝ) / p) fun p hp => by
      have : (1 : ℝ) ≤ p := by exact_mod_cast (h𝔅p p (mem_filter.1 hp).1).one_lt.le
      constructor
      · rw [sub_nonneg, div_le_one (by linarith)]
        exact this
      · have : 0 ≤ (1 : ℝ) / p := by positivity
        linarith
    have h1 := one_sub_prod_one_sub_le (𝔅.filter (· ∣ r)) (fun p => (1 : ℝ) / p) fun p hp => by
      have : (1 : ℝ) ≤ p := by exact_mod_cast (h𝔅p p (mem_filter.1 hp).1).one_lt.le
      exact ⟨by positivity, by rw [div_le_one (by linarith)]; exact this⟩
    rw [show X * modelWeight 𝔅' S - X * (modelWeight 𝔅' S * ∏ p ∈ 𝔅.filter (· ∣ r),
        (1 - (1 : ℝ) / p)) = X * modelWeight 𝔅' S * (1 - ∏ p ∈ 𝔅.filter (· ∣ r),
        (1 - (1 : ℝ) / p)) by ring, abs_mul, abs_of_nonneg (mul_nonneg hX0 h0),
      abs_of_nonneg (by linarith [hprod.2])]
    exact mul_le_mul_of_nonneg_left h1 (mul_nonneg hX0 h0)
  have hterm : ∀ S ∈ Q, |fiberSum 𝔅 N r ℓ f S - X * modelWeight 𝔅 S| ≤
      (|KB| * exp (-(h : ℝ)) + σ) * (X * modelWeight 𝔅' S) + |KB| * (m ^ (4 * h + 2) * V) := by
    intro S hS
    have h1 := abs_fiberSum_sub_le hBS h𝔅 hm hr hℓ hrℓ hℓ𝔅 hf0 hf hV heven hh
      (mem_filter.1 hS).2.1
    have h2 := hw S hS
    have h3 := abs_sub_le (fiberSum 𝔅 N r ℓ f S) (X * modelWeight 𝔅' S) (X * modelWeight 𝔅 S)
    nlinarith
  have hsumw : ∑ S ∈ Q, X * modelWeight 𝔅' S ≤ X := by
    rw [← mul_sum]
    refine mul_le_of_le_one_right hX0 ?_
    rw [← sum_modelWeight 𝔅']
    exact sum_le_sum_of_subset_of_nonneg (fun S hS => mem_powerset.2 (mem_filter.1 hS).2.1)
      fun S _ _ => modelWeight_nonneg h𝔅'0 S
  have hQ : (#Q : ℝ) ≤ Y₀ := by
    refine le_trans ?_ (card_powerset_prod_le h𝔅p (by linarith))
    refine Nat.cast_le.2 (card_le_card fun S hS => ?_)
    obtain ⟨hS𝔅, -, hSY⟩ := mem_filter.1 hS
    refine mem_filter.2 ⟨hS𝔅, ?_⟩
    push_cast
    exact hSY
  have hc0 : 0 ≤ |KB| * exp (-(h : ℝ)) + σ := add_nonneg (by positivity)
    (sum_nonneg fun p _ => by positivity)
  have hV0 : 0 ≤ V := (sum_nonneg fun _ _ => abs_nonneg _).trans hV
  calc _ ≤ ∑ S ∈ Q, ((|KB| * exp (-(h : ℝ)) + σ) * (X * modelWeight 𝔅' S) +
        |KB| * (m ^ (4 * h + 2) * V)) := sum_le_sum hterm
    _ = (|KB| * exp (-(h : ℝ)) + σ) * ∑ S ∈ Q, X * modelWeight 𝔅' S +
        #Q * (|KB| * (m ^ (4 * h + 2) * V)) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    _ ≤ (|KB| * exp (-(h : ℝ)) + σ) * X + Y₀ * (|KB| * (m ^ (4 * h + 2) * V)) :=
        add_le_add (mul_le_mul_of_nonneg_left hsumw hc0)
          (mul_le_mul_of_nonneg_right hQ (by positivity))
    _ = _ := by ring

/-- The fibers with `∏ S > Y₀`. -/
lemma sum_large_fibers_le {𝔅 : Finset ℕ} {m : ℝ} (h𝔅 : ∀ p ∈ 𝔅, p.Prime ∧ (p : ℝ) ≤ m)
    (hm : 1 ≤ m) {N r ℓ : ℕ} (hr : 0 < r) (hℓ : 0 < ℓ) (hℓ𝔅 : ∀ p ∈ 𝔅, ¬ p ∣ ℓ) {f : ℕ → ℝ}
    (hf : ∀ u, 0 ≤ f u) {M₀ : ℝ} (hfM : ∀ u, f u ≤ M₀) {Y₀ : ℝ} (hY₀ : 1 ≤ Y₀) :
    ∑ S ∈ 𝔅.powerset.filter (fun S => S ⊆ bandCoprime 𝔅 r ∧ Y₀ < ∏ p ∈ S, (p : ℝ)),
        |fiberSum 𝔅 N r ℓ f S - progMain N r ℓ f * modelWeight 𝔅 S| ≤
      M₀ * (N / ((r * ℓ : ℕ) : ℝ) *
          ∑ S ∈ 𝔅.powerset.filter (fun S : Finset ℕ => Y₀ < ∏ p ∈ S, (p : ℝ)),
            1 / ∏ p ∈ S, (p : ℝ) + Y₀ * m) +
        progMain N r ℓ f *
          ∑ S ∈ 𝔅.powerset.filter (fun S : Finset ℕ => Y₀ < ∏ p ∈ S, (p : ℝ)),
            1 / ∏ p ∈ S, (p : ℝ) := by
  set Q := 𝔅.powerset.filter (fun S => S ⊆ bandCoprime 𝔅 r ∧ Y₀ < ∏ p ∈ S, (p : ℝ))
  set X := progMain N r ℓ f
  have h𝔅0 : ∀ p ∈ 𝔅, 0 < p := fun p hp => (h𝔅 p hp).1.pos
  have hX0 : 0 ≤ X := by
    simp only [X, progMain]
    exact mul_nonneg (by positivity) (sum_nonneg fun u _ => hf u)
  have hM0 : 0 ≤ M₀ := (hf 0).trans (hfM 0)
  have hN0 : ∀ S, 0 ≤ fiberSum 𝔅 N r ℓ f S := fun S => sum_nonneg fun u _ => hf u
  have hterm : ∀ S ∈ Q, |fiberSum 𝔅 N r ℓ f S - X * modelWeight 𝔅 S| ≤
      fiberSum 𝔅 N r ℓ f S + X * (1 / ∏ p ∈ S, (p : ℝ)) := by
    intro S _
    have h1 := mul_le_mul_of_nonneg_left (modelWeight_le_inv_prod h𝔅0 S) hX0
    have h2 := mul_nonneg hX0 (modelWeight_nonneg h𝔅0 S)
    rw [abs_le]
    constructor <;> linarith [hN0 S]
  -- the weight of the large fibers
  have hfib : ∑ S ∈ Q, fiberSum 𝔅 N r ℓ f S ≤
      ∑ u ∈ (progSet N r ℓ).filter (fun u => Y₀ < ∏ p ∈ bandSet 𝔅 u, (p : ℝ)), f u := by
    have h1 : ∑ S ∈ Q, fiberSum 𝔅 N r ℓ f S =
        ∑ u ∈ (progSet N r ℓ).filter (fun u => bandSet 𝔅 u ∈ Q), f u := by
      rw [← sum_fiberwise_of_maps_to (g := bandSet 𝔅) (t := Q) fun u hu => (mem_filter.1 hu).2]
      refine sum_congr rfl fun S hS => ?_
      rw [fiberSum, filter_filter]
      congr 1
      ext u
      simp only [mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2 ▸ hS, h2⟩
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
    rw [h1]
    exact sum_le_sum_of_subset_of_nonneg (fun u hu => by
      obtain ⟨h1, h2⟩ := mem_filter.1 hu
      exact mem_filter.2 ⟨h1, (mem_filter.1 h2).2.2⟩) fun u _ _ => hf u
  have hcount := card_large_bandSet_le h𝔅 hm (N := N) hr hℓ hℓ𝔅 hY₀
  have hu : ∑ u ∈ (progSet N r ℓ).filter (fun u => Y₀ < ∏ p ∈ bandSet 𝔅 u, (p : ℝ)), f u ≤
      M₀ * #((progSet N r ℓ).filter (fun u => Y₀ < ∏ p ∈ bandSet 𝔅 u, (p : ℝ))) := by
    calc _ ≤ ∑ _u ∈ (progSet N r ℓ).filter (fun u => Y₀ < ∏ p ∈ bandSet 𝔅 u, (p : ℝ)), M₀ :=
          sum_le_sum fun u _ => hfM u
      _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]
  have hset : (progSet N r ℓ).filter (fun u => Y₀ < ∏ p ∈ bandSet 𝔅 u, (p : ℝ)) =
      (Icc 1 N).filter fun u => (r ∣ u + 1 ∧ ℓ ∣ u) ∧ Y₀ < ∏ p ∈ bandSet 𝔅 u, (p : ℝ) := by
    rw [progSet, filter_filter]
  rw [← hset] at hcount
  have hτ : ∑ S ∈ Q, X * (1 / ∏ p ∈ S, (p : ℝ)) ≤
      X * ∑ S ∈ 𝔅.powerset.filter (fun S : Finset ℕ => Y₀ < ∏ p ∈ S, (p : ℝ)),
        1 / ∏ p ∈ S, (p : ℝ) := by
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (fun S hS => ?_)
      fun S _ _ => by positivity) hX0
    obtain ⟨h1, -, h2⟩ := mem_filter.1 hS
    exact mem_filter.2 ⟨h1, h2⟩
  calc _ ≤ ∑ S ∈ Q, (fiberSum 𝔅 N r ℓ f S + X * (1 / ∏ p ∈ S, (p : ℝ))) := sum_le_sum hterm
    _ = ∑ S ∈ Q, fiberSum 𝔅 N r ℓ f S + ∑ S ∈ Q, X * (1 / ∏ p ∈ S, (p : ℝ)) := sum_add_distrib
    _ ≤ _ := add_le_add (hfib.trans (hu.trans (mul_le_mul_of_nonneg_left hcount hM0))) hτ

/-- The independent divisor model in a progression: for `|Ĥ| ≤ 1`,
`|∑_{u ≤ N, r ∣ u+1, ℓ ∣ u} f(u) Ĥ(bandSet u) - X M_𝔅(Ĥ)|` is at most
`X (|K| e^{-h} + 2 ∑_{p ∣ r} 1/p + τ) + Y₀ |K| m^{4h+2} V + M₀ (N τ / (r ℓ) + Y₀ m)`. -/
lemma abs_sum_bandSet_sub_le {h₀ : ℕ} {KB : ℝ} (hBS : DvdSieve h₀ KB) {𝔅 : Finset ℕ} {m : ℝ}
    (h𝔅 : ∀ p ∈ 𝔅, p.Prime ∧ (p : ℝ) ≤ m) (hm : 1 ≤ m) {N r ℓ : ℕ} (hr : 0 < r) (hℓ : 0 < ℓ)
    (hrℓ : Nat.Coprime r ℓ) (hℓ𝔅 : ∀ p ∈ 𝔅, ¬ p ∣ ℓ) {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hf : ∀ u, 0 ≤ f u) {M₀ : ℝ} (hfM : ∀ u, f u ≤ M₀) {V : ℝ}
    (hV : ∑ k ∈ Icc 1 N, |f k - f (k - 1)| ≤ V) {h : ℕ} (heven : Even h) (hh : h₀ ≤ h)
    {Y₀ : ℝ} (hY₀ : 1 ≤ Y₀) (Ĥ : Finset ℕ → ℝ) (hĤ : ∀ S, |Ĥ S| ≤ 1) :
    |∑ u ∈ progSet N r ℓ, f u * Ĥ (bandSet 𝔅 u) - progMain N r ℓ f * modelMean 𝔅 Ĥ| ≤
      progMain N r ℓ f * (|KB| * exp (-(h : ℝ)) + 2 * ∑ p ∈ 𝔅.filter (· ∣ r), (1 : ℝ) / p +
          ∑ S ∈ 𝔅.powerset.filter (fun S : Finset ℕ => Y₀ < ∏ p ∈ S, (p : ℝ)),
            1 / ∏ p ∈ S, (p : ℝ)) +
        Y₀ * (|KB| * (m ^ (4 * h + 2) * V)) +
        M₀ * (N / ((r * ℓ : ℕ) : ℝ) *
          ∑ S ∈ 𝔅.powerset.filter (fun S : Finset ℕ => Y₀ < ∏ p ∈ S, (p : ℝ)),
            1 / ∏ p ∈ S, (p : ℝ) + Y₀ * m) := by
  set X := progMain N r ℓ f
  set 𝔅' := bandCoprime 𝔅 r
  set g : Finset ℕ → ℝ := fun S => |fiberSum 𝔅 N r ℓ f S - X * modelWeight 𝔅 S|
  have h𝔅p : ∀ p ∈ 𝔅, p.Prime := fun p hp => (h𝔅 p hp).1
  have h𝔅0 : ∀ p ∈ 𝔅, 0 < p := fun p hp => (h𝔅p p hp).pos
  have hX0 : 0 ≤ X := by
    simp only [X, progMain]
    exact mul_nonneg (by positivity) (sum_nonneg fun u _ => hf u)
  -- reduce to the total variation `∑_S |N(S) - X π(S)|`
  have h1 : |∑ u ∈ progSet N r ℓ, f u * Ĥ (bandSet 𝔅 u) - X * modelMean 𝔅 Ĥ| ≤
      ∑ S ∈ 𝔅.powerset, g S := by
    rw [sum_progSet_eq_sum_fiberSum, modelMean, mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun S _ => ?_)
    rw [show fiberSum 𝔅 N r ℓ f S * Ĥ S - X * (modelWeight 𝔅 S * Ĥ S) =
      (fiberSum 𝔅 N r ℓ f S - X * modelWeight 𝔅 S) * Ĥ S by ring, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hĤ S)
  -- split the band sets into three classes
  have hsplit : ∑ S ∈ 𝔅.powerset, g S =
      ∑ S ∈ 𝔅.powerset.filter (fun S => ¬ S ⊆ 𝔅'), g S +
        ∑ S ∈ 𝔅.powerset.filter (fun S => S ⊆ 𝔅' ∧ ∏ p ∈ S, (p : ℝ) ≤ Y₀), g S +
        ∑ S ∈ 𝔅.powerset.filter (fun S => S ⊆ 𝔅' ∧ Y₀ < ∏ p ∈ S, (p : ℝ)), g S := by
    rw [← sum_filter_add_sum_filter_not 𝔅.powerset (fun S => S ⊆ 𝔅'),
      ← sum_filter_add_sum_filter_not (𝔅.powerset.filter (fun S => S ⊆ 𝔅'))
        (fun S => ∏ p ∈ S, (p : ℝ) ≤ Y₀), filter_filter, filter_filter]
    simp only [not_le]
    ring
  -- the sets meeting the primes `p ∣ r`
  have hQ₁ : ∑ S ∈ 𝔅.powerset.filter (fun S => ¬ S ⊆ 𝔅'), g S ≤
      X * ∑ p ∈ 𝔅.filter (· ∣ r), (1 : ℝ) / p := by
    calc ∑ S ∈ 𝔅.powerset.filter (fun S => ¬ S ⊆ 𝔅'), g S
        = ∑ S ∈ 𝔅.powerset.filter (fun S => ¬ S ⊆ 𝔅'), X * modelWeight 𝔅 S := by
          refine sum_congr rfl fun S hS => ?_
          obtain ⟨hS𝔅, hS'⟩ := mem_filter.1 hS
          simp only [g]
          rw [fiberSum_eq_zero h𝔅p f hS' (mem_powerset.1 hS𝔅), zero_sub, abs_neg,
            abs_of_nonneg (mul_nonneg hX0 (modelWeight_nonneg h𝔅0 S))]
      _ ≤ _ := by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (sum_modelWeight_not_subset_le h𝔅0 r) hX0
  have hQ₂ := sum_small_fibers_le hBS h𝔅 hm hr hℓ hrℓ hℓ𝔅 hf0 hf hV heven hh hY₀
  have hQ₃ := sum_large_fibers_le h𝔅 hm (N := N) hr hℓ hℓ𝔅 hf hfM hY₀
  rw [hsplit] at h1
  refine h1.trans ?_
  simp only [g]
  linarith

/-! ### Rankin's bound for the model tail -/

/-- Rankin: the sets of primes `p ≤ m` of `𝔅` with product above `Y₀` have reciprocal mass
at most `exp(-log Y₀ / log m + e ∑_{p ∈ 𝔅} 1/p)`. -/
lemma sum_inv_prod_gt_le {𝔅 : Finset ℕ} {m Y₀ : ℝ} (h𝔅 : ∀ p ∈ 𝔅, p.Prime ∧ (p : ℝ) ≤ m)
    (hm : 1 < m) (hY₀ : 0 < Y₀) :
    ∑ S ∈ 𝔅.powerset.filter (fun S : Finset ℕ => Y₀ < ∏ p ∈ S, (p : ℝ)), 1 / ∏ p ∈ S, (p : ℝ) ≤
      exp (-(Real.log Y₀ / Real.log m) + exp 1 * ∑ p ∈ 𝔅, (1 : ℝ) / p) := by
  have hlm : 0 < Real.log m := Real.log_pos hm
  set σ := 1 / Real.log m
  have hσ : 0 < σ := by positivity
  have hp0 : ∀ p ∈ 𝔅, (0 : ℝ) < p := fun p hp => by exact_mod_cast (h𝔅 p hp).1.pos
  -- termwise: `1 / ∏ S ≤ Y₀^{-σ} ∏_{p ∈ S} p^σ / p` when `∏ S > Y₀`
  have hterm : ∀ S ∈ 𝔅.powerset.filter (fun S : Finset ℕ => Y₀ < ∏ p ∈ S, (p : ℝ)),
      1 / ∏ p ∈ S, (p : ℝ) ≤ Y₀ ^ (-σ) * ∏ p ∈ S, ((p : ℝ) ^ σ / p) := by
    intro S hS
    obtain ⟨hS𝔅, hSY⟩ := mem_filter.1 hS
    have hpos : 0 < ∏ p ∈ S, (p : ℝ) := prod_pos fun p hp => hp0 p (mem_powerset.1 hS𝔅 hp)
    rw [prod_div_distrib, Real.finsetProd_rpow _ _ (fun p hp =>
      (hp0 p (mem_powerset.1 hS𝔅 hp)).le)]
    have h1 : Y₀ ^ σ ≤ (∏ p ∈ S, (p : ℝ)) ^ σ := Real.rpow_le_rpow hY₀.le hSY.le hσ.le
    rw [rpow_neg hY₀.le, ← mul_div_assoc, inv_mul_eq_div, div_div, le_div_iff₀ (by positivity),
      one_div_mul_eq_div, div_le_iff₀ hpos]
    nlinarith [rpow_pos_of_pos hY₀ σ]
  have hsum : ∑ S ∈ 𝔅.powerset, ∏ p ∈ S, ((p : ℝ) ^ σ / p) = ∏ p ∈ 𝔅, ((p : ℝ) ^ σ / p + 1) := by
    rw [prod_add]
    simp
  have hfac : ∀ p ∈ 𝔅, (p : ℝ) ^ σ / p + 1 ≤ exp (exp 1 * (1 / p)) := by
    intro p hp
    have hpm : (p : ℝ) ^ σ ≤ exp 1 := by
      rw [rpow_def_of_pos (hp0 p hp)]
      refine exp_le_exp.2 ?_
      rw [show σ = 1 / Real.log m from rfl, mul_one_div, div_le_one hlm]
      exact Real.log_le_log (hp0 p hp) (h𝔅 p hp).2
    have := add_one_le_exp (exp 1 * (1 / (p : ℝ)))
    have : (p : ℝ) ^ σ / p ≤ exp 1 * (1 / p) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right hpm (by have := hp0 p hp; positivity)
    linarith
  calc _ ≤ ∑ S ∈ 𝔅.powerset.filter (fun S : Finset ℕ => Y₀ < ∏ p ∈ S, (p : ℝ)),
        Y₀ ^ (-σ) * ∏ p ∈ S, ((p : ℝ) ^ σ / p) := sum_le_sum hterm
    _ ≤ ∑ S ∈ 𝔅.powerset, Y₀ ^ (-σ) * ∏ p ∈ S, ((p : ℝ) ^ σ / p) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun S hS _ => mul_nonneg
          (by positivity) (prod_nonneg fun p hp => by
            have := hp0 p (mem_powerset.1 hS hp)
            positivity)
    _ = Y₀ ^ (-σ) * ∏ p ∈ 𝔅, ((p : ℝ) ^ σ / p + 1) := by rw [← mul_sum, hsum]
    _ ≤ Y₀ ^ (-σ) * ∏ p ∈ 𝔅, exp (exp 1 * (1 / p)) :=
        mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun p hp => by
          have := hp0 p hp
          positivity) hfac) (by positivity)
    _ = _ := by
        rw [← exp_sum, ← mul_sum, rpow_def_of_pos hY₀, ← exp_add]
        congr 1
        simp only [σ]
        ring

/-! ### Summing over the moduli -/

/-- The weighted progression sum is a combination of the sums over `progSet`. -/
lemma sum_filter_mul_sum_eq {ι : Type*} (S : Finset ι) (ℓ : ι → ℕ) (b : ι → ℝ) (N r : ℕ)
    (f H : ℕ → ℝ) :
    ∑ u ∈ (Icc 1 N).filter (r ∣ · + 1), f u * (∑ i ∈ S with ℓ i ∣ u, b i) * H u =
      ∑ i ∈ S, b i * ∑ u ∈ progSet N r (ℓ i), f u * H u := by
  calc ∑ u ∈ (Icc 1 N).filter (r ∣ · + 1), f u * (∑ i ∈ S with ℓ i ∣ u, b i) * H u
      = ∑ u ∈ (Icc 1 N).filter (r ∣ · + 1), ∑ i ∈ S,
          (if ℓ i ∣ u then b i * (f u * H u) else 0) := by
        refine sum_congr rfl fun u _ => ?_
        rw [sum_filter, mul_sum, sum_mul]
        exact sum_congr rfl fun i _ => by split_ifs <;> ring
    _ = ∑ i ∈ S, ∑ u ∈ (Icc 1 N).filter (r ∣ · + 1),
          (if ℓ i ∣ u then b i * (f u * H u) else 0) := sum_comm
    _ = _ := by
        refine sum_congr rfl fun i _ => ?_
        rw [← sum_filter, filter_filter, ← mul_sum]
        rfl

/-- E1 at a fixed scale: summing the model comparison over the moduli `r ≤ R` and the long
moduli `ℓ_i`. If the relative error is at most `δ` for every `r ≤ R`, the total is at most
`N M₀ H_R Λ δ + R #S (Y₀ |K| m^{4h+2} V + M₀ Y₀ m)`, where `H_R ≥ ∑_{r ≤ R} 1/r` and
`Λ ≥ ∑ 1/ℓ_i`. -/
lemma sum_progression_le {h₀ : ℕ} {KB : ℝ} (hBS : DvdSieve h₀ KB) {𝔅 : Finset ℕ} {m : ℝ}
    (h𝔅 : ∀ p ∈ 𝔅, p.Prime ∧ (p : ℝ) ≤ m) (hm : 1 ≤ m) {N R : ℕ} {ι : Type*} (S : Finset ι)
    (ℓ : ι → ℕ) (b : ι → ℝ) (hℓ : ∀ i ∈ S, 0 < ℓ i)
    (hrℓ : ∀ r ∈ Icc 1 R, ∀ i ∈ S, Nat.Coprime r (ℓ i)) (hℓ𝔅 : ∀ i ∈ S, ∀ p ∈ 𝔅, ¬ p ∣ ℓ i)
    (hb : ∀ i ∈ S, |b i| ≤ 1) {f : ℕ → ℝ} (hf0 : f 0 = 0) (hf : ∀ u, 0 ≤ f u) {M₀ : ℝ}
    (hfM : ∀ u, f u ≤ M₀) {V : ℝ} (hV : ∑ k ∈ Icc 1 N, |f k - f (k - 1)| ≤ V) {h : ℕ}
    (heven : Even h) (hh : h₀ ≤ h) {Y₀ : ℝ} (hY₀ : 1 ≤ Y₀) (H : ℕ → ℝ)
    (hH : ∀ n, |H n| ≤ 1) (hHb : ∀ n, H n = H (∏ p ∈ bandSet 𝔅 n, p)) {δ HR Λ : ℝ}
    (hδ : ∀ r ∈ Icc 1 R, |KB| * exp (-(h : ℝ)) + 2 * ∑ p ∈ 𝔅.filter (· ∣ r), (1 : ℝ) / p +
      2 * ∑ S ∈ 𝔅.powerset.filter (fun S : Finset ℕ => Y₀ < ∏ p ∈ S, (p : ℝ)),
        1 / ∏ p ∈ S, (p : ℝ) ≤ δ)
    (hδ0 : 0 ≤ δ) (hHR : ∑ r ∈ Icc 1 R, (1 : ℝ) / r ≤ HR) (hΛ : ∑ i ∈ S, (1 : ℝ) / ℓ i ≤ Λ) :
    ∑ r ∈ Icc 1 R, |∑ u ∈ (Icc 1 N).filter (r ∣ · + 1), f u * (∑ i ∈ S with ℓ i ∣ u, b i) * H u -
        ∑ i ∈ S, b i * (progMain N r (ℓ i) f * modelMean 𝔅 fun T => H (∏ p ∈ T, p))| ≤
      N * M₀ * HR * Λ * δ + R * #S * (Y₀ * (|KB| * (m ^ (4 * h + 2) * V)) + M₀ * (Y₀ * m)) := by
  have hM0 : 0 ≤ M₀ := (hf 0).trans (hfM 0)
  set τ := ∑ S ∈ 𝔅.powerset.filter (fun S : Finset ℕ => Y₀ < ∏ p ∈ S, (p : ℝ)),
    1 / ∏ p ∈ S, (p : ℝ)
  set E₀ := Y₀ * (|KB| * (m ^ (4 * h + 2) * V)) + M₀ * (Y₀ * m)
  have hτ0 : 0 ≤ τ := sum_nonneg fun S _ => div_nonneg zero_le_one
    (prod_nonneg fun p _ => Nat.cast_nonneg p)
  -- the bound for one pair `(r, ℓ_i)`
  have hpair : ∀ r ∈ Icc 1 R, ∀ i ∈ S,
      |∑ u ∈ progSet N r (ℓ i), f u * H u -
        progMain N r (ℓ i) f * modelMean 𝔅 fun T => H (∏ p ∈ T, p)| ≤
      N * M₀ * (1 / r) * (1 / ℓ i) * δ + E₀ := by
    intro r hr i hi
    have hr0 : 0 < r := (mem_Icc.1 hr).1
    have h1 := abs_sum_bandSet_sub_le hBS h𝔅 hm (N := N) hr0 (hℓ i hi) (hrℓ r hr i hi)
      (hℓ𝔅 i hi) hf0 hf hfM hV heven hh hY₀ (fun T => H (∏ p ∈ T, p)) fun T => hH _
    have hsum : ∑ u ∈ progSet N r (ℓ i), f u * H u =
        ∑ u ∈ progSet N r (ℓ i), f u * H (∏ p ∈ bandSet 𝔅 u, p) :=
      sum_congr rfl fun u _ => by rw [← hHb u]
    rw [hsum]
    have hX : progMain N r (ℓ i) f ≤ N * M₀ * (1 / r) * (1 / ℓ i) := by
      rw [progMain]
      calc 1 / ((r * ℓ i : ℕ) : ℝ) * ∑ u ∈ Icc 1 N, f u ≤
          1 / ((r * ℓ i : ℕ) : ℝ) * ∑ _u ∈ Icc 1 N, M₀ :=
            mul_le_mul_of_nonneg_left (sum_le_sum fun u _ => hfM u) (by positivity)
        _ = _ := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          push_cast
          field_simp
    have hX0 : 0 ≤ progMain N r (ℓ i) f := by
      rw [progMain]
      exact mul_nonneg (by positivity) (sum_nonneg fun u _ => hf u)
    have hNr : (N : ℝ) / ((r * ℓ i : ℕ) : ℝ) = N * (1 / r) * (1 / ℓ i) := by
      push_cast
      field_simp
    have hd := hδ r hr
    have hd0 : 0 ≤ |KB| * exp (-(h : ℝ)) + 2 * ∑ p ∈ 𝔅.filter (· ∣ r), (1 : ℝ) / p + τ := by
      have : 0 ≤ ∑ p ∈ 𝔅.filter (· ∣ r), (1 : ℝ) / p := sum_nonneg fun p _ => by positivity
      positivity
    have e1 : progMain N r (ℓ i) f * (|KB| * exp (-(h : ℝ)) +
        2 * ∑ p ∈ 𝔅.filter (· ∣ r), (1 : ℝ) / p + τ) ≤
        N * M₀ * (1 / r) * (1 / ℓ i) * (|KB| * exp (-(h : ℝ)) +
        2 * ∑ p ∈ 𝔅.filter (· ∣ r), (1 : ℝ) / p + τ) := mul_le_mul_of_nonneg_right hX hd0
    have e2 : M₀ * (N / ((r * ℓ i : ℕ) : ℝ) * τ) = N * M₀ * (1 / r) * (1 / ℓ i) * τ := by
      rw [hNr]
      ring
    have e3 : N * M₀ * (1 / r) * (1 / ℓ i) * (|KB| * exp (-(h : ℝ)) +
        2 * ∑ p ∈ 𝔅.filter (· ∣ r), (1 : ℝ) / p + τ) + N * M₀ * (1 / r) * (1 / ℓ i) * τ ≤
        N * M₀ * (1 / r) * (1 / ℓ i) * δ := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc _ ≤ _ := h1
      _ = progMain N r (ℓ i) f * (|KB| * exp (-(h : ℝ)) +
          2 * ∑ p ∈ 𝔅.filter (· ∣ r), (1 : ℝ) / p + τ) + M₀ * (N / ((r * ℓ i : ℕ) : ℝ) * τ) +
          E₀ := by ring
      _ ≤ _ := by linarith
  -- sum over `i` and `r`
  have hr_term : ∀ r ∈ Icc 1 R,
      |∑ u ∈ (Icc 1 N).filter (r ∣ · + 1), f u * (∑ i ∈ S with ℓ i ∣ u, b i) * H u -
        ∑ i ∈ S, b i * (progMain N r (ℓ i) f * modelMean 𝔅 fun T => H (∏ p ∈ T, p))| ≤
      N * M₀ * (1 / r) * Λ * δ + #S * E₀ := by
    intro r hr
    rw [sum_filter_mul_sum_eq, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ S, |b i * ∑ u ∈ progSet N r (ℓ i), f u * H u -
          b i * (progMain N r (ℓ i) f * modelMean 𝔅 fun T => H (∏ p ∈ T, p))|
        ≤ ∑ i ∈ S, (N * M₀ * (1 / r) * (1 / ℓ i) * δ + E₀) := by
          refine sum_le_sum fun i hi => ?_
          rw [← mul_sub, abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hb i hi) |>.trans (hpair r hr i hi)
      _ = N * M₀ * (1 / r) * δ * ∑ i ∈ S, (1 : ℝ) / ℓ i + #S * E₀ := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
          congr 1
          exact sum_congr rfl fun i _ => by ring
      _ ≤ N * M₀ * (1 / r) * δ * Λ + #S * E₀ := by
          gcongr
      _ = _ := by ring
  have hE₀ : 0 ≤ E₀ := by
    have hV0 : 0 ≤ V := (sum_nonneg fun _ _ => abs_nonneg _).trans hV
    positivity
  have hΛ0 : 0 ≤ Λ := (sum_nonneg fun i _ => by positivity).trans hΛ
  calc _ ≤ ∑ r ∈ Icc 1 R, (N * M₀ * (1 / r) * Λ * δ + #S * E₀) := sum_le_sum hr_term
    _ = N * M₀ * Λ * δ * ∑ r ∈ Icc 1 R, (1 : ℝ) / r + R * #S * E₀ := by
        rw [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_sum]
        congr 1
        · exact sum_congr rfl fun r _ => by ring
        · ring
    _ ≤ N * M₀ * Λ * δ * HR + R * #S * E₀ := by
        gcongr
    _ = _ := by ring

end

end Sieve

end Erdos408
