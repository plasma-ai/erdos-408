module

public import Erdos408.Hypotheses
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Log

/-!
# The block sieve

A proof of `BlockSieve` (WD Lemma 2.9, PD Lemma 2.6), following WD §2: the
product of block upper bounds and its one-block correction, as in Ford and
Halberstam (2000, §1, Lemma 1).

Put the designated prime `p ≤ z` in block `j = β(p)` when
`z^{2^{-j-1}} < p ≤ z^{2^{-j}}`, and give block `j` the even depth
`h_j = (j + 1) h`. In block `j` let `U_j` be inclusion–exclusion through
degree `h_j`, `E_j` the sum of the monomials of degree `h_j + 1`, and `I_j`
the indicator of avoiding every bad condition of the block.

* Bonferroni. With `t` bad conditions in the block, `U_j = 1` at `t = 0` and
  `U_j = C(t - 1, h_j)` otherwise, so `I_j ≤ U_j ≤ I_j + E_j`.
* Telescoping. `U = ∏ U_j` and `V = U - ∑_k E_k ∏_{j ≠ k} U_j` satisfy
  `V ≤ ∏ I_j ≤ U`. Their coefficients lie in `{-1, 0, 1}` and vanish unless
  `D` has at most `h_j + 1` primes in each block, so `∏ D ≤ z^{4h+2}`.
* The model. With independent probabilities `g(p)` the expectations factor
  over blocks. Each block avoids its bad conditions with probability
  `∏ (1 - g) ≥ exp(-C₀/η₀)`, and `E_j` has expectation at most
  `exp(e C₀) e^{-h_j - 1}`, so `U` and `V` have expectation
  `∏ (1 - g) (1 + O(e^{-h}))`.

Evaluating `U` and `V` on the objects gives the main term `X` times their
expectations plus a remainder `∑ λ_D r(D)` with `|λ_D| ≤ 1`.
-/

public section

open Finset Real

namespace Erdos408

namespace BlockSieve

/-! ### One block -/

/-- The inclusion–exclusion coefficient through degree `h`. -/
noncomputable def trunc (h : ℕ) (E : Finset ℕ) : ℝ :=
  if E.card ≤ h then (-1) ^ E.card else 0

/-- The indicator of the monomials of degree `h + 1`. -/
noncomputable def layer (h : ℕ) (E : Finset ℕ) : ℝ :=
  if E.card = h + 1 then 1 else 0

/-- `|trunc h E| ≤ 1`. -/
theorem abs_trunc_le (h : ℕ) (E : Finset ℕ) : |trunc h E| ≤ 1 := by
  unfold trunc; split_ifs <;> simp

/-- `|layer h E| ≤ 1`. -/
theorem abs_layer_le (h : ℕ) (E : Finset ℕ) : |layer h E| ≤ 1 := by
  unfold layer; split_ifs <;> simp

/-- A truncated binomial sum, extended by zero past `t`. -/
theorem sum_range_choose_trunc (t h : ℕ) :
    ∑ m ∈ range (t + 1), (if m ≤ h then (t.choose m : ℝ) * (-1) ^ m else 0) =
      ∑ m ∈ range (h + 1), (-1) ^ m * (t.choose m : ℝ) := by
  have hN : ∀ N, t + 1 ≤ N → h + 1 ≤ N →
      ∑ m ∈ range N, (if m ≤ h then (t.choose m : ℝ) * (-1) ^ m else 0) =
        ∑ m ∈ range (h + 1), (-1) ^ m * (t.choose m : ℝ) := by
    intro N htN hhN
    rw [← sum_subset (range_subset_range.2 hhN)]
    · exact sum_congr rfl fun m hm => by
        rw [ite_eq_left (by simpa [Nat.lt_succ_iff] using hm), mul_comm]
    · intro m _ hm
      rw [ite_eq_right (by simpa [Nat.lt_succ_iff] using hm)]
  rw [← hN (t + h + 2) (by omega) (by omega)]
  refine (sum_subset (range_subset_range.2 (by omega)) fun m _ hm => ?_)
  rw [Nat.choose_eq_zero_of_lt (by simpa [Nat.lt_succ_iff] using hm)]
  simp

/-- Bonferroni at even depth `h` for the set `T` of bad conditions:
`I ≤ ∑_{E ⊆ T} trunc h E ≤ I + ∑_{E ⊆ T} layer h E` with `I = [T = ∅]`. -/
theorem bonferroni {h : ℕ} (hh : Even h) (T : Finset ℕ) :
    (if T = ∅ then (1 : ℝ) else 0) ≤ ∑ E ∈ T.powerset, trunc h E ∧
      ∑ E ∈ T.powerset, trunc h E ≤
        (if T = ∅ then (1 : ℝ) else 0) + ∑ E ∈ T.powerset, layer h E := by
  have hU := sum_powerset_apply_card (fun a => if a ≤ h then (-1 : ℝ) ^ a else 0) (x := T)
  have hE := sum_powerset_apply_card (fun a => if a = h + 1 then (1 : ℝ) else 0) (x := T)
  simp only [nsmul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_range] at hU hE
  simp only [trunc, layer, hU, hE, sum_range_choose_trunc]
  rcases Nat.eq_zero_or_pos T.card with h0 | h0
  · rw [card_eq_zero.mp h0, sum_range_succ']
    simp
  · obtain ⟨n, hn⟩ : ∃ n, T.card = n + 1 := ⟨T.card - 1, by omega⟩
    have hT : T ≠ ∅ := fun hT => by simp [hT] at h0
    have halt := Int.alternating_sum_range_choose_eq_choose (n := n) (m := h)
    have halt' : ∑ m ∈ range (h + 1), (-1 : ℝ) ^ m * ((n + 1).choose m : ℝ) =
        (n.choose h : ℝ) := by
      rw [hh.neg_one_pow, one_mul] at halt
      exact_mod_cast halt
    have hlayer : (if h + 1 < n + 1 + 1 then (((n + 1).choose (h + 1) : ℕ) : ℝ) else 0) =
        ((n + 1).choose (h + 1) : ℝ) := by
      split_ifs with hm
      · rfl
      · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    rw [ite_eq_right hT, hn, halt', hlayer, Nat.choose_succ_succ, Nat.cast_add]
    have : (0 : ℝ) ≤ n.choose (h + 1) := by positivity
    exact ⟨by positivity, by linarith⟩

/-- Evaluating at the indicators of a predicate keeps the subsets on which it
holds. -/
theorem sum_powerset_mul_prod_boole (B : Finset ℕ) (q : ℕ → Prop) [DecidablePred q]
    (f : Finset ℕ → ℝ) :
    ∑ E ∈ B.powerset, f E * ∏ p ∈ E, (if q p then (1 : ℝ) else 0) =
      ∑ E ∈ (B.filter q).powerset, f E := by
  simp only [prod_boole, mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext E
  simp only [mem_filter, mem_powerset, subset_iff]
  exact ⟨fun h p hp => ⟨h.1 hp, h.2 p hp⟩, fun h => ⟨fun p hp => (h hp).1, fun p hp => (h hp).2⟩⟩

/-- Bonferroni in one block `B`, evaluated at the bad conditions `q`. -/
theorem bonferroni_boole {h : ℕ} (hh : Even h) (B : Finset ℕ) (q : ℕ → Prop) [DecidablePred q] :
    (if ∀ p ∈ B, ¬ q p then (1 : ℝ) else 0) ≤
        ∑ E ∈ B.powerset, trunc h E * ∏ p ∈ E, (if q p then (1 : ℝ) else 0) ∧
      ∑ E ∈ B.powerset, trunc h E * ∏ p ∈ E, (if q p then (1 : ℝ) else 0) ≤
        (if ∀ p ∈ B, ¬ q p then (1 : ℝ) else 0) +
          ∑ E ∈ B.powerset, layer h E * ∏ p ∈ E, (if q p then (1 : ℝ) else 0) := by
  simp only [sum_powerset_mul_prod_boole, ← filter_eq_empty_iff]
  exact bonferroni hh _

/-- The marginals of the product measure with probabilities `g`. -/
theorem sum_prod_measure {B E : Finset ℕ} (hE : E ⊆ B) (g : ℕ → ℝ) :
    ∑ T ∈ B.powerset with E ⊆ T, (∏ p ∈ T, g p) * ∏ p ∈ B \ T, (1 - g p) = ∏ p ∈ E, g p := by
  have key := prod_add g (fun p => if p ∈ E then 0 else 1 - g p) B
  rw [prod_congr rfl fun p _ => show (g p + if p ∈ E then 0 else 1 - g p) =
      if p ∈ E then g p else 1 by split_ifs <;> ring, prod_ite_mem, inter_eq_right.2 hE] at key
  rw [key, sum_filter]
  refine sum_congr rfl fun T _ => ?_
  split_ifs with hET
  · congr 1
    refine prod_congr rfl fun p hp => ?_
    rw [ite_eq_right fun hpE => (mem_sdiff.1 hp).2 (hET hpE)]
  · obtain ⟨p, hpE, hpT⟩ := not_subset.1 hET
    rw [prod_eq_zero (i := p) (mem_sdiff.2 ⟨hE hpE, hpT⟩) (by simp [hpE]), mul_zero]

/-- Bonferroni in one block `B` for independent bad conditions of
probabilities `g`. -/
theorem bonferroni_model {h : ℕ} (hh : Even h) (B : Finset ℕ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ B, 0 ≤ g p ∧ g p ≤ 1) :
    ∏ p ∈ B, (1 - g p) ≤ ∑ E ∈ B.powerset, trunc h E * ∏ p ∈ E, g p ∧
      ∑ E ∈ B.powerset, trunc h E * ∏ p ∈ E, g p ≤
        ∏ p ∈ B, (1 - g p) + ∑ E ∈ B.powerset, layer h E * ∏ p ∈ E, g p := by
  set μ : Finset ℕ → ℝ := fun T => (∏ p ∈ T, g p) * ∏ p ∈ B \ T, (1 - g p)
  have hμ : ∀ T ∈ B.powerset, 0 ≤ μ T := fun T hT => mul_nonneg
    (prod_nonneg fun p hp => (hg p (mem_powerset.1 hT hp)).1)
    (prod_nonneg fun p hp => sub_nonneg.2 (hg p (mem_sdiff.1 hp).1).2)
  -- expectations are integrals against `μ`
  have hint : ∀ f : Finset ℕ → ℝ, ∑ E ∈ B.powerset, f E * ∏ p ∈ E, g p =
      ∑ T ∈ B.powerset, μ T * ∑ E ∈ T.powerset, f E := by
    intro f
    simp only [mul_sum]
    rw [sum_comm' (t' := B.powerset) (s' := fun E => B.powerset.filter (E ⊆ ·))]
    · refine sum_congr rfl fun E hE => ?_
      rw [← sum_prod_measure (mem_powerset.1 hE) g, mul_sum]
      exact sum_congr rfl fun T _ => mul_comm _ _
    · intro T E
      simp only [mem_powerset, mem_filter]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2.trans h.1⟩, fun h => ⟨h.1.1, h.1.2⟩⟩
  have hempty : ∏ p ∈ B, (1 - g p) = ∑ T ∈ B.powerset, μ T * if T = ∅ then 1 else 0 := by
    simp [μ, mul_ite, sum_ite_eq']
  rw [hint, hint, hempty, ← sum_add_distrib]
  constructor
  · exact sum_le_sum fun T hT => mul_le_mul_of_nonneg_left (bonferroni hh T).1 (hμ T hT)
  · exact sum_le_sum fun T hT => by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (bonferroni hh T).2 (hμ T hT)

/-! ### Sizes in the model -/

/-- The monomials of degree `h + 1` have expectation at most
`exp(e ∑ g) e^{-(h+1)}`, since `∏ (1 + e g) ≤ exp(e ∑ g)`. -/
theorem sum_layer_le (B : Finset ℕ) (g : ℕ → ℝ) (hg : ∀ p ∈ B, 0 ≤ g p) (h : ℕ) :
    ∑ E ∈ B.powerset, layer h E * ∏ p ∈ E, g p ≤
      exp (exp 1 * ∑ p ∈ B, g p) * exp (-((h + 1 : ℕ) : ℝ)) := by
  have hexp : exp ((h + 1 : ℕ) : ℝ) * ∑ E ∈ B.powerset, layer h E * ∏ p ∈ E, g p ≤
      exp (exp 1 * ∑ p ∈ B, g p) :=
    calc exp ((h + 1 : ℕ) : ℝ) * ∑ E ∈ B.powerset, layer h E * ∏ p ∈ E, g p
        = ∑ E ∈ B.powerset, layer h E * ∏ p ∈ E, exp 1 * g p := by
          rw [mul_sum]
          refine sum_congr rfl fun E _ => ?_
          rw [prod_mul_distrib, prod_const]
          unfold layer
          split_ifs with hE
          · rw [hE, ← exp_nat_mul, mul_one]; ring
          · ring
      _ ≤ ∑ E ∈ B.powerset, ∏ p ∈ E, exp 1 * g p := sum_le_sum fun E hE => by
          have : 0 ≤ ∏ p ∈ E, exp 1 * g p :=
            prod_nonneg fun p hp => mul_nonneg (exp_pos 1).le (hg p (mem_powerset.1 hE hp))
          unfold layer
          split_ifs <;> linarith
      _ = ∏ p ∈ B, (1 + exp 1 * g p) := (prod_one_add B).symm
      _ ≤ ∏ p ∈ B, exp (exp 1 * g p) :=
          prod_le_prod₀ (fun p hp => by have := hg p hp; positivity)
            fun p _ => by linarith [add_one_le_exp (exp 1 * g p)]
      _ = exp (exp 1 * ∑ p ∈ B, g p) := by rw [mul_sum, exp_sum]
  rwa [← le_div_iff₀' (exp_pos _), div_eq_mul_inv, ← exp_neg] at hexp

/-- A block avoids all its bad conditions with probability at least
`exp(-∑ g / η₀)`, since `log (1 - u) ≥ -u / (1 - u)`. -/
theorem exp_le_prod_one_sub (B : Finset ℕ) (g : ℕ → ℝ) {η₀ : ℝ} (hη : 0 < η₀)
    (hg : ∀ p ∈ B, 0 ≤ g p ∧ g p ≤ 1 - η₀) :
    exp (-(∑ p ∈ B, g p) / η₀) ≤ ∏ p ∈ B, (1 - g p) := by
  rw [neg_div, div_eq_mul_inv, sum_mul, ← sum_neg_distrib, exp_sum]
  refine prod_le_prod₀ (fun p _ => (exp_pos _).le) fun p hp => ?_
  obtain ⟨h0, h1⟩ := hg p hp
  have hpos : 0 < 1 - g p := by linarith
  have hlog := one_sub_inv_le_log_of_pos hpos
  have hdiv : g p / (1 - g p) ≤ g p / η₀ := div_le_div_of_nonneg_left h0 hη (by linarith)
  have hinv : 1 - (1 - g p)⁻¹ = -(g p / (1 - g p)) := by field_simp; ring
  calc exp (-(g p * η₀⁻¹)) ≤ exp (log (1 - g p)) :=
      exp_le_exp.2 (by rw [← div_eq_mul_inv]; linarith)
    _ = 1 - g p := exp_log hpos

/-! ### Products over blocks -/

/-- Telescoping a product of nonnegative factors:
`∏ b - ∏ a ≤ ∑_k e_k ∏_{j ≠ k} b_j` when `0 ≤ a ≤ b` and `b - a ≤ e`. -/
theorem prod_sub_prod_le (J : Finset ℕ) {a b e : ℕ → ℝ} (ha : ∀ j ∈ J, 0 ≤ a j)
    (hab : ∀ j ∈ J, a j ≤ b j) (he : ∀ j ∈ J, b j - a j ≤ e j) :
    ∏ j ∈ J, b j - ∏ j ∈ J, a j ≤ ∑ k ∈ J, e k * ∏ j ∈ J.erase k, b j := by
  induction J using Finset.induction_on with
  | empty => simp
  | insert i J hi ih =>
    have ih := ih (fun j hj => ha j (mem_insert_of_mem hj))
      (fun j hj => hab j (mem_insert_of_mem hj)) (fun j hj => he j (mem_insert_of_mem hj))
    have hsum : ∑ k ∈ J, e k * ∏ j ∈ (insert i J).erase k, b j =
        b i * ∑ k ∈ J, e k * ∏ j ∈ J.erase k, b j := by
      rw [mul_sum]
      refine sum_congr rfl fun k hk => ?_
      rw [erase_insert_of_ne fun h => hi (by rw [h]; exact hk),
        prod_insert fun h => hi (mem_of_mem_erase h)]
      ring
    rw [prod_insert hi, prod_insert hi, sum_insert hi, erase_insert hi, hsum]
    have hai := ha i (mem_insert_self i J)
    have hbi := hab i (mem_insert_self i J)
    have hei := he i (mem_insert_self i J)
    have hb : ∀ j ∈ J, 0 ≤ b j := fun j hj =>
      (ha j (mem_insert_of_mem hj)).trans (hab j (mem_insert_of_mem hj))
    have hbJ : 0 ≤ ∏ j ∈ J, b j := prod_nonneg hb
    have hS : 0 ≤ ∑ k ∈ J, e k * ∏ j ∈ J.erase k, b j := sum_nonneg fun k hk =>
      mul_nonneg (by linarith [he k (mem_insert_of_mem hk), hab k (mem_insert_of_mem hk)])
        (prod_nonneg fun j hj => hb j (mem_of_mem_erase hj))
    nlinarith [mul_le_mul_of_nonneg_right hei hbJ, mul_le_mul_of_nonneg_left ih hai,
      mul_le_mul_of_nonneg_right hbi hS]

/-- Expanding one factor of a product: `∏ (A + [j = k] B) = ∏ A + ∏ (A with B at k)`. -/
theorem prod_add_ite {J : Finset ℕ} {k : ℕ} (hk : k ∈ J) (A B : ℕ → ℝ) :
    ∏ j ∈ J, (A j + if j = k then B j else 0) =
      ∏ j ∈ J, A j + ∏ j ∈ J, (if j = k then B j else A j) := by
  have h₁ : ∏ j ∈ J.erase k, (A j + if j = k then B j else 0) = ∏ j ∈ J.erase k, A j :=
    prod_congr rfl fun j hj => by simp [ne_of_mem_erase hj]
  have h₂ : ∏ j ∈ J.erase k, (if j = k then B j else A j) = ∏ j ∈ J.erase k, A j :=
    prod_congr rfl fun j hj => by simp [ne_of_mem_erase hj]
  rw [← mul_prod_erase J (fun j => A j + if j = k then B j else 0) hk,
    ← mul_prod_erase J A hk, ← mul_prod_erase J (fun j => if j = k then B j else A j) hk, h₁, h₂]
  simp only [ite_true]
  ring

/-- A sum over the subsets of `P` of a product over the blocks `β = j` factors
over the blocks. -/
theorem sum_powerset_prod_blocks (β : ℕ → ℕ) (J P : Finset ℕ) (hP : ∀ p ∈ P, β p ∈ J)
    (F : ℕ → Finset ℕ → ℝ) :
    ∑ D ∈ P.powerset, ∏ j ∈ J, F j (D.filter (β · = j)) =
      ∏ j ∈ J, ∑ E ∈ (P.filter (β · = j)).powerset, F j E := by
  induction P using Finset.induction_on generalizing F with
  | empty => simp
  | insert a P ha ih =>
    have hP' : ∀ p ∈ P, β p ∈ J := fun p hp => hP p (mem_insert_of_mem hp)
    have hj : β a ∈ J := hP a (mem_insert_self a P)
    -- adding `a` changes only the block of `a`
    have hD : ∀ D ∈ P.powerset, ∏ j ∈ J, F j ((insert a D).filter (β · = j)) =
        ∏ j ∈ J, (if j = β a then fun E => F j (insert a E) else F j) (D.filter (β · = j)) :=
      fun D _ => prod_congr rfl fun j _ => by
        rw [filter_insert]
        by_cases h : j = β a
        · rw [ite_eq_left h.symm, ite_eq_left h]
        · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
    have hE : ∀ j ∈ J, ∑ E ∈ ((insert a P).filter (β · = j)).powerset, F j E =
        ∑ E ∈ (P.filter (β · = j)).powerset, F j E +
          if j = β a then ∑ E ∈ (P.filter (β · = j)).powerset, F j (insert a E) else 0 := by
      intro j _
      rw [filter_insert]
      by_cases h : j = β a
      · rw [ite_eq_left h.symm, ite_eq_left h,
          sum_powerset_insert fun h' => ha (mem_filter.1 h').1]
      · rw [ite_eq_right (Ne.symm h), ite_eq_right h, add_zero]
    have hF : ∀ j ∈ J, ∑ E ∈ (P.filter (β · = j)).powerset,
        (if j = β a then fun E => F j (insert a E) else F j) E =
          if j = β a then ∑ E ∈ (P.filter (β · = j)).powerset, F j (insert a E)
          else ∑ E ∈ (P.filter (β · = j)).powerset, F j E := by
      intro j _
      split_ifs <;> rfl
    rw [sum_powerset_insert ha, sum_congr rfl hD, ih hP', ih hP', prod_congr rfl hE,
      prod_congr rfl hF, prod_add_ite hj]

/-! ### The blocks of the designated primes -/

/-- The block of a prime `p ≤ z`: `z^{2^{-j-1}} < p ≤ z^{2^{-j}}` for
`j = blk z p`. -/
noncomputable def blk (z : ℝ) (p : ℕ) : ℕ :=
  Nat.log 2 ⌊Real.log z / Real.log p⌋₊

/-- `2^j log p ≤ log z < 2^{j+1} log p` for `j = blk z p`. -/
theorem blk_spec {z : ℝ} {p : ℕ} (hp : p.Prime) (hpz : (p : ℝ) ≤ z) :
    2 ^ blk z p * Real.log p ≤ Real.log z ∧ Real.log z < 2 ^ (blk z p + 1) * Real.log p := by
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hy : 1 ≤ Real.log z / Real.log p := by
    rw [le_div_iff₀ hlogp, one_mul]
    exact Real.log_le_log (by exact_mod_cast hp.pos) hpz
  have hn : ⌊Real.log z / Real.log p⌋₊ ≠ 0 := (Nat.floor_pos.2 hy).ne'
  constructor
  · have h₁ : ((2 ^ blk z p : ℕ) : ℝ) ≤ Real.log z / Real.log p :=
      (Nat.cast_le.2 (Nat.pow_log_le_self 2 hn)).trans (Nat.floor_le (by linarith))
    rw [le_div_iff₀ hlogp] at h₁
    exact_mod_cast h₁
  · have h₂ : Real.log z / Real.log p < ((2 ^ (blk z p + 1) : ℕ) : ℝ) :=
      calc Real.log z / Real.log p < (⌊Real.log z / Real.log p⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        _ ≤ _ := by exact_mod_cast Nat.lt_pow_succ_log_self (b := 2) one_lt_two _
    rw [div_lt_iff₀ hlogp] at h₂
    exact_mod_cast h₂

/-- Each block carries `g`-mass at most `C₀`: block `j` lies in
`(w, w²]` for `w = z^{2^{-j-1}}`. -/
theorem sum_block_le {P : Finset ℕ} {z C₀ : ℝ} {g : ℕ → ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) (hg : ∀ p ∈ P, 0 ≤ g p)
    (hC : ∀ w : ℝ, 1 < w → ∑ p ∈ P.filter (fun p : ℕ => w < p ∧ (p : ℝ) ≤ w ^ 2), g p ≤ C₀)
    (j : ℕ) : ∑ p ∈ P.filter (blk z · = j), g p ≤ C₀ := by
  rcases (P.filter (blk z · = j)).eq_empty_or_nonempty with h | ⟨p₀, hp₀⟩
  · rw [h, sum_empty]
    exact (sum_nonneg fun p hp => hg p (mem_filter.1 hp).1).trans (hC 2 one_lt_two)
  obtain ⟨hp₀P, rfl⟩ := mem_filter.1 hp₀
  have hlogz : 0 < Real.log z := by
    have := (blk_spec (hP p₀ hp₀P).1 (hP p₀ hp₀P).2).1
    have : 0 < Real.log p₀ := Real.log_pos (by exact_mod_cast (hP p₀ hp₀P).1.one_lt)
    nlinarith [pow_pos (two_pos (α := ℝ)) (blk z p₀)]
  set y := Real.log z / 2 ^ (blk z p₀ + 1)
  have hw : 1 < exp y := one_lt_exp_iff.2 (by positivity)
  refine (sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p hp _ => hg p (mem_filter.1 hp).1).trans
    (hC (exp y) hw)
  obtain ⟨hpP, hpj⟩ := mem_filter.1 hp
  obtain ⟨hlo, hhi⟩ := blk_spec (hP p hpP).1 (hP p hpP).2
  rw [hpj] at hlo hhi
  have hp : (0 : ℝ) < p := by exact_mod_cast (hP p hpP).1.pos
  refine mem_filter.2 ⟨hpP, (Real.lt_log_iff_exp_lt hp).1 ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity), mul_comm]
    exact hhi
  · rw [sq, ← exp_add, ← Real.log_le_iff_le_exp hp]
    have : y + y = Real.log z / 2 ^ blk z p₀ := by
      simp only [y, pow_succ]
      field_simp
      ring
    rw [this, le_div_iff₀ (by positivity), mul_comm]
    exact hlo

/-- `∑_{j < N} ((j + 1) h + 1) / 2^j ≤ 4h + 2`. -/
theorem sum_range_div_two_pow_le (h N : ℕ) :
    ∑ j ∈ range N, (((j + 1) * h + 1 : ℕ) : ℝ) / 2 ^ j ≤ 4 * h + 2 := by
  have hid : ∀ N : ℕ, ∑ j ∈ range N, ((j : ℝ) + 1) / 2 ^ j + (2 * N + 4) / 2 ^ N = 4 := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
      have : ((N : ℝ) + 1) / 2 ^ N + (2 * ((N : ℝ) + 1) + 4) / (2 ^ N * 2) =
          (2 * N + 4) / 2 ^ N := by
        field_simp
        ring
      push_cast
      rw [sum_range_succ, pow_succ]
      linarith
  have hsplit : ∑ j ∈ range N, (((j + 1) * h + 1 : ℕ) : ℝ) / 2 ^ j =
      h * ∑ j ∈ range N, ((j : ℝ) + 1) / 2 ^ j + ∑ j ∈ range N, (1 / (2 : ℝ)) ^ j := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    rw [div_pow, one_pow]
    ring
  have h₁ : ∑ j ∈ range N, ((j : ℝ) + 1) / 2 ^ j ≤ 4 := by
    have : 0 ≤ (2 * (N : ℝ) + 4) / 2 ^ N := by positivity
    linarith [hid N]
  rw [hsplit]
  nlinarith [sum_geometric_two_le N, (Nat.cast_nonneg h : (0 : ℝ) ≤ h)]

/-- A product of designated primes with at most `(j + 1) h + 1` of them in
each block `j` is at most `z^{4h+2}`. -/
theorem prod_le_of_card_block_le {P D : Finset ℕ} {z : ℝ} (hz : 1 ≤ z)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) (hD : D ⊆ P) (h : ℕ)
    (hcard : ∀ j ∈ P.image (blk z), (D.filter (blk z · = j)).card ≤ (j + 1) * h + 1) :
    ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * h + 2) := by
  have hpos : ∀ p ∈ D, 0 < (p : ℝ) := fun p hp => by exact_mod_cast (hP p (hD hp)).1.pos
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz
  have hmap : ∀ p ∈ D, blk z p ∈ P.image (blk z) := fun p hp => mem_image_of_mem _ (hD hp)
  have hfib : ∀ j ∈ P.image (blk z), ∑ p ∈ D with blk z p = j, Real.log p ≤
      (((j + 1) * h + 1 : ℕ) : ℝ) / 2 ^ j * Real.log z := by
    intro j hj
    calc ∑ p ∈ D with blk z p = j, Real.log p
        ≤ ∑ p ∈ D with blk z p = j, Real.log z / 2 ^ j := sum_le_sum fun p hp => by
          obtain ⟨hpD, rfl⟩ := mem_filter.1 hp
          rw [le_div_iff₀ (by positivity), mul_comm]
          exact (blk_spec (hP p (hD hpD)).1 (hP p (hD hpD)).2).1
      _ = (D.filter (blk z · = j)).card * (Real.log z / 2 ^ j) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (((j + 1) * h + 1 : ℕ) : ℝ) * (Real.log z / 2 ^ j) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard j hj) (by positivity)
      _ = _ := by ring
  obtain ⟨N, hN⟩ : ∃ N, P.image (blk z) ⊆ range N :=
    ⟨(P.image (blk z)).sup id + 1, fun j hj => mem_range.2 (Nat.lt_succ_of_le (le_sup (f := id) hj))⟩
  have hlog : Real.log (∏ p ∈ D, (p : ℝ)) ≤ ((4 * h + 2 : ℕ) : ℝ) * Real.log z :=
    calc Real.log (∏ p ∈ D, (p : ℝ))
        = ∑ j ∈ P.image (blk z), ∑ p ∈ D with blk z p = j, Real.log p := by
          rw [Real.log_prod fun p hp => (hpos p hp).ne', sum_fiberwise_of_maps_to hmap]
      _ ≤ ∑ j ∈ P.image (blk z), (((j + 1) * h + 1 : ℕ) : ℝ) / 2 ^ j * Real.log z :=
          sum_le_sum hfib
      _ = (∑ j ∈ P.image (blk z), (((j + 1) * h + 1 : ℕ) : ℝ) / 2 ^ j) * Real.log z := by
          rw [sum_mul]
      _ ≤ (4 * h + 2) * Real.log z := mul_le_mul_of_nonneg_right
          ((sum_le_sum_of_subset_of_nonneg hN fun _ _ _ => by positivity).trans
            (sum_range_div_two_pow_le h N)) hlogz
      _ = _ := by push_cast; ring
  push_cast
  rw [← Real.exp_log (prod_pos hpos), ← Real.exp_log (by linarith : (0 : ℝ) < z), ← exp_nat_mul]
  exact exp_le_exp.2 hlog

/-! ### The upper and lower polynomials -/

/-- `U_j` in block `j` at depth `(j + 1) h`, evaluated at `x`. -/
noncomputable def blockU (z : ℝ) (P : Finset ℕ) (h j : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ E ∈ (P.filter (blk z · = j)).powerset, trunc ((j + 1) * h) E * ∏ p ∈ E, x p

/-- `E_j` in block `j` at depth `(j + 1) h`, evaluated at `x`. -/
noncomputable def blockE (z : ℝ) (P : Finset ℕ) (h j : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ E ∈ (P.filter (blk z · = j)).powerset, layer ((j + 1) * h) E * ∏ p ∈ E, x p

/-- The coefficient of `D` in `U = ∏_j U_j`. -/
noncomputable def upperCoeff (z : ℝ) (J : Finset ℕ) (h : ℕ) (D : Finset ℕ) : ℝ :=
  ∏ j ∈ J, trunc ((j + 1) * h) (D.filter (blk z · = j))

/-- The coefficient of `D` in the correction `E_k ∏_{j ≠ k} U_j`. -/
noncomputable def corrCoeff (z : ℝ) (J : Finset ℕ) (h k : ℕ) (D : Finset ℕ) : ℝ :=
  ∏ j ∈ J, (if j = k then layer ((j + 1) * h) else trunc ((j + 1) * h)) (D.filter (blk z · = j))

/-- The coefficient of `D` in `V = U - ∑_k E_k ∏_{j ≠ k} U_j`. -/
noncomputable def lowerCoeff (z : ℝ) (J : Finset ℕ) (h : ℕ) (D : Finset ℕ) : ℝ :=
  upperCoeff z J h D - ∑ k ∈ J, corrCoeff z J h k D

/-- Evaluating a product over blocks factors over the blocks. -/
theorem sum_prod_blocks_mul {z : ℝ} {J P : Finset ℕ} (hJ : ∀ p ∈ P, blk z p ∈ J)
    (f : ℕ → Finset ℕ → ℝ) (x : ℕ → ℝ) :
    ∑ D ∈ P.powerset, (∏ j ∈ J, f j (D.filter (blk z · = j))) * ∏ p ∈ D, x p =
      ∏ j ∈ J, ∑ E ∈ (P.filter (blk z · = j)).powerset, f j E * ∏ p ∈ E, x p := by
  rw [← sum_powerset_prod_blocks (blk z) J P hJ fun j E => f j E * ∏ p ∈ E, x p]
  refine sum_congr rfl fun D hD => ?_
  rw [prod_mul_distrib, prod_fiberwise_of_maps_to fun p hp => hJ p (mem_powerset.1 hD hp)]

/-- `U` evaluated at `x` is `∏_j U_j(x)`. -/
theorem sum_upperCoeff_mul {z : ℝ} {J P : Finset ℕ} (hJ : ∀ p ∈ P, blk z p ∈ J) (h : ℕ)
    (x : ℕ → ℝ) :
    ∑ D ∈ P.powerset, upperCoeff z J h D * ∏ p ∈ D, x p = ∏ j ∈ J, blockU z P h j x :=
  sum_prod_blocks_mul hJ _ x

/-- `V` evaluated at `x` is `∏_j U_j(x) - ∑_k E_k(x) ∏_{j ≠ k} U_j(x)`. -/
theorem sum_lowerCoeff_mul {z : ℝ} {J P : Finset ℕ} (hJ : ∀ p ∈ P, blk z p ∈ J) (h : ℕ)
    (x : ℕ → ℝ) :
    ∑ D ∈ P.powerset, lowerCoeff z J h D * ∏ p ∈ D, x p =
      ∏ j ∈ J, blockU z P h j x - ∑ k ∈ J, blockE z P h k x * ∏ j ∈ J.erase k, blockU z P h j x := by
  have hcorr : ∀ k ∈ J, ∑ D ∈ P.powerset, corrCoeff z J h k D * ∏ p ∈ D, x p =
      blockE z P h k x * ∏ j ∈ J.erase k, blockU z P h j x := by
    intro k hk
    simp only [corrCoeff]
    rw [sum_prod_blocks_mul hJ, ← mul_prod_erase J _ hk, ite_eq_left rfl]
    congr 1
    refine prod_congr rfl fun j hj => ?_
    rw [ite_eq_right (ne_of_mem_erase hj)]
    rfl
  simp only [lowerCoeff, sub_mul, sum_mul, sum_sub_distrib]
  rw [sum_upperCoeff_mul hJ, sum_comm, sum_congr rfl hcorr]

/-- `trunc n E ≠ 0` only if `|E| ≤ n`. -/
theorem trunc_ne_zero {n : ℕ} {E : Finset ℕ} (h : trunc n E ≠ 0) : E.card ≤ n := by
  unfold trunc at h
  split_ifs at h with hE
  · exact hE
  · exact absurd rfl h

/-- `layer n E ≠ 0` only if `|E| = n + 1`. -/
theorem layer_ne_zero {n : ℕ} {E : Finset ℕ} (h : layer n E ≠ 0) : E.card = n + 1 := by
  unfold layer at h
  split_ifs at h with hE
  · exact hE
  · exact absurd rfl h

/-- `|U_D| ≤ 1`. -/
theorem abs_upperCoeff_le (z : ℝ) (J : Finset ℕ) (h : ℕ) (D : Finset ℕ) :
    |upperCoeff z J h D| ≤ 1 := by
  rw [upperCoeff, abs_prod]
  exact prod_le_one₀ (fun _ _ => abs_nonneg _) fun _ _ => abs_trunc_le _ _

/-- The coefficients of each correction have modulus at most one. -/
theorem abs_corrCoeff_le (z : ℝ) (J : Finset ℕ) (h k : ℕ) (D : Finset ℕ) :
    |corrCoeff z J h k D| ≤ 1 := by
  rw [corrCoeff, abs_prod]
  refine prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => ?_
  split_ifs
  exacts [abs_layer_le _ _, abs_trunc_le _ _]

/-- `U_D ≠ 0` only if `D` has at most `(j + 1) h` primes in block `j`. -/
theorem card_le_of_upperCoeff_ne_zero {z : ℝ} {J : Finset ℕ} {h : ℕ} {D : Finset ℕ}
    (hD : upperCoeff z J h D ≠ 0) : ∀ j ∈ J, (D.filter (blk z · = j)).card ≤ (j + 1) * h :=
  fun j hj => trunc_ne_zero (prod_ne_zero_iff.1 hD j hj)

/-- The correction `k` has a nonzero coefficient at `D` only if `D` has exactly
`(k + 1) h + 1` primes in block `k` and at most `(j + 1) h` in every other
block `j`. -/
theorem card_of_corrCoeff_ne_zero {z : ℝ} {J : Finset ℕ} {h k : ℕ} {D : Finset ℕ}
    (hD : corrCoeff z J h k D ≠ 0) : ∀ j ∈ J,
      (j = k → (D.filter (blk z · = j)).card = (j + 1) * h + 1) ∧
        (j ≠ k → (D.filter (blk z · = j)).card ≤ (j + 1) * h) := by
  intro j hj
  have := prod_ne_zero_iff.1 hD j hj
  refine ⟨fun hjk => ?_, fun hjk => ?_⟩
  · rw [ite_eq_left hjk] at this
    exact layer_ne_zero this
  · rw [ite_eq_right hjk] at this
    exact trunc_ne_zero this

/-- The supports of `U` and of the corrections are disjoint, so `|V_D| ≤ 1`,
and `V_D ≠ 0` only if `D` has at most `(j + 1) h + 1` primes in block `j`. -/
theorem lowerCoeff_spec (z : ℝ) (J : Finset ℕ) (h : ℕ) (D : Finset ℕ) :
    |lowerCoeff z J h D| ≤ 1 ∧ (lowerCoeff z J h D ≠ 0 →
      ∀ j ∈ J, (D.filter (blk z · = j)).card ≤ (j + 1) * h + 1) := by
  by_cases hk : ∃ k ∈ J, corrCoeff z J h k D ≠ 0
  · obtain ⟨k, hkJ, hk⟩ := hk
    have hother : ∀ k' ∈ J, k' ≠ k → corrCoeff z J h k' D = 0 := by
      intro k' _ hne
      by_contra h'
      have := (card_of_corrCoeff_ne_zero h' k hkJ).2 (Ne.symm hne)
      have := (card_of_corrCoeff_ne_zero hk k hkJ).1 rfl
      omega
    have hU : upperCoeff z J h D = 0 := by
      by_contra h'
      have := card_le_of_upperCoeff_ne_zero h' k hkJ
      have := (card_of_corrCoeff_ne_zero hk k hkJ).1 rfl
      omega
    rw [lowerCoeff, hU, sum_eq_single_of_mem k hkJ hother, zero_sub, abs_neg]
    refine ⟨abs_corrCoeff_le z J h k D, fun _ j hj => ?_⟩
    by_cases hjk : j = k
    · exact ((card_of_corrCoeff_ne_zero hk j hj).1 hjk).le
    · exact ((card_of_corrCoeff_ne_zero hk j hj).2 hjk).trans (Nat.le_succ _)
  · push Not at hk
    rw [lowerCoeff, sum_eq_zero hk, sub_zero]
    exact ⟨abs_upperCoeff_le z J h D, fun hD j hj =>
      (card_le_of_upperCoeff_ne_zero hD j hj).trans (Nat.le_succ _)⟩

/-- A remainder with coefficients of modulus at most one, supported on
`∏ D ≤ Z`. -/
theorem abs_sum_coeff_mul_le {P : Finset ℕ} {c r : Finset ℕ → ℝ} {Z : ℝ}
    (hc : ∀ D ∈ P.powerset, |c D| ≤ 1)
    (hlev : ∀ D ∈ P.powerset, c D ≠ 0 → ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Z) :
    |∑ D ∈ P.powerset, c D * r D| ≤
      ∑ D ∈ P.powerset with ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Z, |r D| := by
  rw [← sum_filter_of_ne fun D hD h => hlev D hD (left_ne_zero_of_mul h)]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun D hD => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hc D (mem_filter.1 hD).1)

/-! ### Assembly -/

/-- The relative error `σ = ∑_j K e^{-(j+1)h-1}` of the model. -/
noncomputable def blockError (z : ℝ) (P : Finset ℕ) (K : ℝ) (h : ℕ) : ℝ :=
  ∑ j ∈ P.image (blk z), K * exp (-(((j + 1) * h + 1 : ℕ) : ℝ))

/-- For `h ≥ 1`, `σ ≤ K e^{-h}`, since `∑_j 2^{-j-1} ≤ 1`. -/
theorem blockError_le {z K : ℝ} {P : Finset ℕ} (hK : 0 ≤ K) {h : ℕ} (h1 : 1 ≤ h) :
    blockError z P K h ≤ K * exp (-(h : ℝ)) := by
  have h2 : exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le two_pos (by linarith [add_one_le_exp (1 : ℝ)])
  have hterm : ∀ j : ℕ, exp (-(((j + 1) * h + 1 : ℕ) : ℝ)) ≤ exp (-(h : ℝ)) * (1 / 2) ^ (j + 1) := by
    intro j
    calc exp (-(((j + 1) * h + 1 : ℕ) : ℝ))
        ≤ exp (-(h : ℝ) + ((j + 1 : ℕ) : ℝ) * (-1)) := exp_le_exp.2 (by
          have : (1 : ℝ) ≤ h := by exact_mod_cast h1
          push_cast
          nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
      _ = exp (-(h : ℝ)) * exp (-1) ^ (j + 1) := by rw [exp_add, exp_nat_mul]
      _ ≤ exp (-(h : ℝ)) * (1 / 2) ^ (j + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (exp_pos _).le h2 _) (exp_pos _).le
  obtain ⟨N, hN⟩ : ∃ N, P.image (blk z) ⊆ range N :=
    ⟨(P.image (blk z)).sup id + 1, fun j hj => mem_range.2 (Nat.lt_succ_of_le (le_sup (f := id) hj))⟩
  have hgeom : ∑ j ∈ range N, (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := by
    have := sum_geometric_two_le N
    simp only [pow_succ, ← sum_mul]
    linarith
  calc blockError z P K h
      ≤ ∑ j ∈ P.image (blk z), K * (exp (-(h : ℝ)) * (1 / 2) ^ (j + 1)) :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hterm j) hK
    _ ≤ ∑ j ∈ range N, K * (exp (-(h : ℝ)) * (1 / 2) ^ (j + 1)) :=
        sum_le_sum_of_subset_of_nonneg hN fun _ _ _ => by positivity
    _ = K * exp (-(h : ℝ)) * ∑ j ∈ range N, (1 / 2 : ℝ) ^ (j + 1) := by
        rw [mul_sum]
        exact sum_congr rfl fun _ _ => by ring
    _ ≤ K * exp (-(h : ℝ)) := mul_le_of_le_one_right (by positivity) hgeom

/-- The block sieve at one even depth `h`, with `σ = blockError`:
`sifted ≤ main e^σ + R` and, for `σ ≤ 1`, `sifted ≥ main (1 - σ) - R`. -/
theorem sifted_bounds {ι : Type} (objs : Finset ι) (wt : ι → ℝ) (P : Finset ℕ) (z X : ℝ)
    (bad : ℕ → ι → Prop) [∀ p i, Decidable (bad p i)] (g : ℕ → ℝ) {η₀ C₀ : ℝ} (hη : 0 < η₀)
    (hwt : ∀ i ∈ objs, 0 ≤ wt i) (hz : 1 ≤ z) (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z)
    (hX : 0 ≤ X) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 - η₀)
    (hC : ∀ w : ℝ, 1 < w → ∑ p ∈ P.filter (fun p : ℕ => w < p ∧ (p : ℝ) ≤ w ^ 2), g p ≤ C₀)
    {h : ℕ} (hh : Even h) :
    (∑ i ∈ objs with ∀ p ∈ P, ¬ bad p i, wt i) ≤
        X * (∏ p ∈ P, (1 - g p)) * exp (blockError z P (exp (exp 1 * C₀ + C₀ / η₀)) h) +
          ∑ D ∈ P.powerset with ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * h + 2),
            |(∑ i ∈ objs with ∀ p ∈ D, bad p i, wt i) - X * ∏ p ∈ D, g p| ∧
      (blockError z P (exp (exp 1 * C₀ + C₀ / η₀)) h ≤ 1 →
        X * (∏ p ∈ P, (1 - g p)) * (1 - blockError z P (exp (exp 1 * C₀ + C₀ / η₀)) h) -
            ∑ D ∈ P.powerset with ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * h + 2),
              |(∑ i ∈ objs with ∀ p ∈ D, bad p i, wt i) - X * ∏ p ∈ D, g p| ≤
          ∑ i ∈ objs with ∀ p ∈ P, ¬ bad p i, wt i) := by
  set K₂ := exp (exp 1 * C₀ + C₀ / η₀)
  set σ := blockError z P K₂ h
  set R := ∑ D ∈ P.powerset with ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * h + 2),
    |(∑ i ∈ objs with ∀ p ∈ D, bad p i, wt i) - X * ∏ p ∈ D, g p|
  set J := P.image (blk z)
  have hJ : ∀ p ∈ P, blk z p ∈ J := fun p hp => mem_image_of_mem _ hp
  have hev : ∀ j, Even ((j + 1) * h) := fun j => hh.mul_left _
  -- evaluation on the objects
  have heval : ∀ c : Finset ℕ → ℝ, ∑ i ∈ objs, wt i *
      ∑ D ∈ P.powerset, c D * ∏ p ∈ D, (if bad p i then (1 : ℝ) else 0) =
        X * ∑ D ∈ P.powerset, c D * ∏ p ∈ D, g p +
          ∑ D ∈ P.powerset, c D * ((∑ i ∈ objs with ∀ p ∈ D, bad p i, wt i) - X * ∏ p ∈ D, g p) := by
    intro c
    simp only [prod_boole, mul_ite, mul_one, mul_zero, mul_sum]
    rw [sum_comm, ← sum_add_distrib]
    refine sum_congr rfl fun D _ => ?_
    rw [show ∀ G S : ℝ, X * (c D * G) + c D * (S - X * G) = c D * S from fun _ _ => by ring,
      sum_filter, mul_sum]
    exact sum_congr rfl fun i _ => by split_ifs <;> ring
  have hR : ∀ c : Finset ℕ → ℝ, (∀ D ∈ P.powerset, |c D| ≤ 1) →
      (∀ D ∈ P.powerset, c D ≠ 0 → ∀ j ∈ J, (D.filter (blk z · = j)).card ≤ (j + 1) * h + 1) →
      |∑ D ∈ P.powerset, c D * ((∑ i ∈ objs with ∀ p ∈ D, bad p i, wt i) - X * ∏ p ∈ D, g p)| ≤ R :=
    fun c hc hcard => abs_sum_coeff_mul_le hc fun D hD hne =>
      prod_le_of_card_block_le hz hP (mem_powerset.1 hD) h (hcard D hD hne)
  have hRU := hR (upperCoeff z J h) (fun D _ => abs_upperCoeff_le z J h D) fun D _ hD j hj =>
    (card_le_of_upperCoeff_ne_zero hD j hj).trans (Nat.le_succ _)
  have hRV := hR (lowerCoeff z J h) (fun D _ => (lowerCoeff_spec z J h D).1) fun D _ =>
    (lowerCoeff_spec z J h D).2
  -- the sifted weight as a sum of products of block indicators
  have hsift : (∑ i ∈ objs with ∀ p ∈ P, ¬ bad p i, wt i) = ∑ i ∈ objs, wt i *
      ∏ j ∈ J, (if ∀ p ∈ P.filter (blk z · = j), ¬ bad p i then (1 : ℝ) else 0) := by
    rw [sum_filter]
    refine sum_congr rfl fun i _ => ?_
    have hiff : (∀ j ∈ J, ∀ p ∈ P.filter (blk z · = j), ¬ bad p i) ↔ ∀ p ∈ P, ¬ bad p i :=
      ⟨fun H p hp => H _ (hJ p hp) p (mem_filter.2 ⟨hp, rfl⟩),
        fun H _ _ p hp => H p (mem_filter.1 hp).1⟩
    rw [prod_boole, if_congr hiff rfl rfl, mul_ite, mul_one, mul_zero]
  -- Bonferroni on the objects
  have hobj : ∀ (i : ι) (j : ℕ),
      (if ∀ p ∈ P.filter (blk z · = j), ¬ bad p i then (1 : ℝ) else 0) ≤
          blockU z P h j (fun p => if bad p i then 1 else 0) ∧
        blockU z P h j (fun p => if bad p i then 1 else 0) ≤
          (if ∀ p ∈ P.filter (blk z · = j), ¬ bad p i then (1 : ℝ) else 0) +
            blockE z P h j (fun p => if bad p i then 1 else 0) :=
    fun i j => bonferroni_boole (hev j) (P.filter (blk z · = j)) (bad · i)
  -- the model
  set a : ℕ → ℝ := fun j => ∏ p ∈ P.filter (blk z · = j), (1 - g p)
  set ε : ℕ → ℝ := fun j => K₂ * exp (-(((j + 1) * h + 1 : ℕ) : ℝ))
  have hgB : ∀ j, ∀ p ∈ P.filter (blk z · = j), 0 ≤ g p ∧ g p ≤ 1 := fun j p hp =>
    ⟨(hg p (mem_filter.1 hp).1).1, by linarith [(hg p (mem_filter.1 hp).1).2]⟩
  have hmodel : ∀ j, a j ≤ blockU z P h j g ∧ blockU z P h j g ≤ a j + blockE z P h j g :=
    fun j => bonferroni_model (hev j) (P.filter (blk z · = j)) g (hgB j)
  have ha : ∀ j, 0 ≤ a j := fun j => prod_nonneg fun p hp => by linarith [(hgB j p hp).2]
  have hε : ∀ j, 0 ≤ ε j := fun j => by positivity
  have hmass := sum_block_le hP (fun p hp => (hg p hp).1) hC
  have he : ∀ j, blockE z P h j g ≤ ε j * a j := by
    intro j
    have h₁ := sum_layer_le (P.filter (blk z · = j)) g (fun p hp => (hgB j p hp).1) ((j + 1) * h)
    have h₂ := exp_le_prod_one_sub (P.filter (blk z · = j)) g hη fun p hp => hg p (mem_filter.1 hp).1
    have h₃ : exp (exp 1 * ∑ p ∈ P.filter (blk z · = j), g p) ≤ exp (exp 1 * C₀) :=
      exp_le_exp.2 (mul_le_mul_of_nonneg_left (hmass j) (exp_pos 1).le)
    have h₄ : exp (-C₀ / η₀) ≤ exp (-(∑ p ∈ P.filter (blk z · = j), g p) / η₀) :=
      exp_le_exp.2 (div_le_div_of_nonneg_right (neg_le_neg (hmass j)) hη.le)
    have h₅ : exp (exp 1 * C₀) * exp (-(((j + 1) * h + 1 : ℕ) : ℝ)) =
        ε j * exp (-C₀ / η₀) := by
      simp only [ε, K₂, ← exp_add]
      congr 1
      ring
    calc blockE z P h j g ≤ exp (exp 1 * C₀) * exp (-(((j + 1) * h + 1 : ℕ) : ℝ)) :=
          h₁.trans (mul_le_mul_of_nonneg_right h₃ (exp_pos _).le)
      _ = ε j * exp (-C₀ / η₀) := h₅
      _ ≤ ε j * a j := mul_le_mul_of_nonneg_left (h₄.trans h₂) (hε j)
  have hu0 : ∀ j, 0 ≤ blockU z P h j g := fun j => (ha j).trans (hmodel j).1
  have hA : ∏ j ∈ J, a j = ∏ p ∈ P, (1 - g p) := prod_fiberwise_of_maps_to hJ _
  have hA0 : 0 ≤ ∏ j ∈ J, a j := prod_nonneg fun j _ => ha j
  have hMlo : ∏ j ∈ J, a j ≤ ∏ j ∈ J, blockU z P h j g :=
    prod_le_prod₀ (fun j _ => ha j) fun j _ => (hmodel j).1
  have hMhi : ∏ j ∈ J, blockU z P h j g ≤ (∏ j ∈ J, a j) * exp σ :=
    calc ∏ j ∈ J, blockU z P h j g ≤ ∏ j ∈ J, (a j * (1 + ε j)) :=
          prod_le_prod₀ (fun j _ => hu0 j) fun j _ => by
            linarith [(hmodel j).2, he j, mul_comm (ε j) (a j)]
      _ = (∏ j ∈ J, a j) * ∏ j ∈ J, (1 + ε j) := prod_mul_distrib
      _ ≤ (∏ j ∈ J, a j) * exp σ :=
          mul_le_mul_of_nonneg_left (prod_one_add_le_exp_sum J hε) hA0
  have hcorr : ∑ k ∈ J, blockE z P h k g * ∏ j ∈ J.erase k, blockU z P h j g ≤
      σ * ∏ j ∈ J, blockU z P h j g := by
    rw [show σ = ∑ k ∈ J, ε k from rfl, sum_mul]
    refine sum_le_sum fun k hk => ?_
    rw [← mul_prod_erase J _ hk, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      ((he k).trans (mul_le_mul_of_nonneg_left (hmodel k).1 (hε k)))
      (prod_nonneg fun j _ => hu0 j)
  constructor
  · -- the upper bound
    calc (∑ i ∈ objs with ∀ p ∈ P, ¬ bad p i, wt i)
        ≤ ∑ i ∈ objs, wt i * ∑ D ∈ P.powerset, upperCoeff z J h D *
            ∏ p ∈ D, (if bad p i then (1 : ℝ) else 0) := by
          rw [hsift]
          refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hwt i hi)
          rw [sum_upperCoeff_mul hJ]
          exact prod_le_prod₀ (fun j _ => by split_ifs <;> norm_num) fun j _ => (hobj i j).1
      _ ≤ X * (∏ p ∈ P, (1 - g p)) * exp σ + R := by
          rw [heval, sum_upperCoeff_mul hJ, ← hA, mul_assoc]
          exact add_le_add (mul_le_mul_of_nonneg_left hMhi hX) ((le_abs_self _).trans hRU)
  · -- the lower bound
    intro hσ
    calc X * (∏ p ∈ P, (1 - g p)) * (1 - σ) - R
        ≤ X * ∑ D ∈ P.powerset, lowerCoeff z J h D * ∏ p ∈ D, g p +
            ∑ D ∈ P.powerset, lowerCoeff z J h D *
              ((∑ i ∈ objs with ∀ p ∈ D, bad p i, wt i) - X * ∏ p ∈ D, g p) := by
          rw [sum_lowerCoeff_mul hJ, ← hA, mul_assoc, sub_eq_add_neg]
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ hX) (neg_le_of_abs_le hRV)
          nlinarith [mul_le_mul_of_nonneg_right hMlo (sub_nonneg.2 hσ)]
      _ = ∑ i ∈ objs, wt i * ∑ D ∈ P.powerset, lowerCoeff z J h D *
            ∏ p ∈ D, (if bad p i then (1 : ℝ) else 0) := (heval _).symm
      _ ≤ (∑ i ∈ objs with ∀ p ∈ P, ¬ bad p i, wt i) := by
          rw [hsift]
          refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hwt i hi)
          rw [sum_lowerCoeff_mul hJ, sub_le_comm]
          exact prod_sub_prod_le J (fun j _ => by split_ifs <;> norm_num)
            (fun j _ => (hobj i j).1) fun j _ => by linarith [(hobj i j).2]

end BlockSieve

open BlockSieve in
/-- The block sieve (WD Lemma 2.9, PD Lemma 2.6), with `h₀ = ⌈K₂⌉ + 1` and
`K = 2 K₂ + exp K₂` for `K₂ = exp(e C₀ + C₀ / η₀)`. -/
theorem blockSieve : BlockSieve := by
  intro η₀ C₀ hη
  set K₂ := exp (exp 1 * C₀ + C₀ / η₀) with hK₂_def
  refine ⟨⌈K₂⌉₊ + 1, 2 * K₂ + exp K₂, ?_⟩
  intro ι objs wt P z X bad _ g hwt hz hP hX hg hC
  dsimp only
  have hK₂ : 0 < K₂ := exp_pos _
  have hK : 1 ≤ 2 * K₂ + exp K₂ := by linarith [one_le_exp hK₂.le]
  have hmain : 0 ≤ X * ∏ p ∈ P, (1 - g p) :=
    mul_nonneg hX (prod_nonneg fun p hp => by linarith [(hg p hp).2])
  have hσ0 : ∀ h, 0 ≤ blockError z P K₂ h := fun h => sum_nonneg fun _ _ => by positivity
  have hR0 : ∀ Z : ℝ, 0 ≤ ∑ D ∈ P.powerset with ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Z,
      |(∑ i ∈ objs with ∀ p ∈ D, bad p i, wt i) - X * ∏ p ∈ D, g p| :=
    fun Z => sum_nonneg fun _ _ => abs_nonneg _
  constructor
  · intro h hh hh₀
    obtain ⟨hU, hV⟩ := sifted_bounds objs wt P z X bad g hη hwt hz hP hX hg hC hh
    rw [← hK₂_def] at hU hV
    have hσ := blockError_le (z := z) (P := P) hK₂.le (h := h) (by omega)
    have hKh : K₂ * exp (-(h : ℝ)) ≤ 1 := by
      have hlt : K₂ < h := by
        have h₁ := Nat.le_ceil K₂
        have h₂ : ((⌈K₂⌉₊ + 1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hh₀
        push_cast at h₂
        linarith
      rw [exp_neg, ← div_eq_mul_inv, div_le_one (exp_pos _)]
      linarith [add_one_le_exp (h : ℝ)]
    have hσ1 := hσ.trans hKh
    have hexp : exp (blockError z P K₂ h) - 1 ≤ 2 * blockError z P K₂ h := by
      have := abs_exp_sub_one_le (x := blockError z P K₂ h) (by rw [abs_of_nonneg (hσ0 h)]; exact hσ1)
      rw [abs_of_nonneg (hσ0 h)] at this
      exact (le_abs_self _).trans this
    have hV := hV hσ1
    have p₁ := mul_le_mul_of_nonneg_left hσ hmain
    have p₂ := mul_le_mul_of_nonneg_left hexp hmain
    have p₃ : 0 ≤ exp K₂ * exp (-(h : ℝ)) * (X * ∏ p ∈ P, (1 - g p)) := by positivity
    have p₅ : 0 ≤ K₂ * exp (-(h : ℝ)) * (X * ∏ p ∈ P, (1 - g p)) := by positivity
    have p₄ := le_mul_of_one_le_left (hR0 (z ^ (4 * h + 2))) hK
    rw [abs_le]
    constructor <;> linarith
  · obtain ⟨hU, -⟩ := sifted_bounds objs wt P z X bad g hη hwt hz hP hX hg hC (h := 2) even_two
    rw [← hK₂_def, show 4 * 2 + 2 = 10 from rfl] at hU
    have hσ : blockError z P K₂ 2 ≤ K₂ := (blockError_le hK₂.le (by norm_num)).trans
      (mul_le_of_le_one_right hK₂.le (exp_le_one_iff.2 (by norm_num)))
    have p₁ := mul_le_mul_of_nonneg_left (exp_le_exp.2 hσ) hmain
    have p₂ := le_mul_of_one_le_left (hR0 (z ^ 10)) hK
    have p₃ : 0 ≤ 2 * K₂ * (X * ∏ p ∈ P, (1 - g p)) := by positivity
    nlinarith

end Erdos408
