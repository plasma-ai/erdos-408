module

public import Erdos408.Extraction.Defs
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Nat.ChineseRemainder

/-!
# Residue classes modulo products of distinct primes

* A system of congruences modulo the distinct primes of `V` is one congruence
  modulo `∏_{p ∈ V} p` (CRT).
* An interval `(A, t]` contains `(t - A)/M + O(1)` integers of each residue
  class modulo `M`; hence `(t - A)/∏_{p ∈ V} p + O(1)` solutions of each system.
-/

@[expose] public section

namespace Erdos408

open Finset

/-- CRT for distinct primes: `(∀ p ∈ V, e ≡ a_p [MOD p]) ↔ e ≡ k [MOD ∏_{p ∈ V} p]`. -/
lemma exists_forall_modEq_iff (V : Finset ℕ) (hV : ∀ p ∈ V, p.Prime) (a : ℕ → ℕ) :
    ∃ k : ℕ, ∀ e : ℕ, (∀ p ∈ V, e ≡ a p [MOD p]) ↔ e ≡ k [MOD ∏ p ∈ V, p] := by
  induction V using Finset.induction_on with
  | empty => exact ⟨0, fun e => by simp [Nat.modEq_one]⟩
  | insert q V hq ih =>
    obtain ⟨k, hk⟩ := ih fun p hp => hV p (mem_insert_of_mem hp)
    have hqp := hV q (mem_insert_self q V)
    have hco : q.Coprime (∏ p ∈ V, p) := Nat.Coprime.prod_right fun p hp =>
      (Nat.coprime_primes hqp (hV p (mem_insert_of_mem hp))).2 fun h => hq (h ▸ hp)
    obtain ⟨k', hk'q, hk'M⟩ := Nat.chineseRemainder hco (a q) k
    refine ⟨k', fun e => ?_⟩
    rw [prod_insert hq, ← Nat.modEq_and_modEq_iff_modEq_mul hco, forall_mem_insert, hk]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.trans hk'q.symm, h2.trans hk'M.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.trans hk'q, h2.trans hk'M⟩

/-- A residue class modulo `M ≥ 1` meets `(A, t]` in `(t - A)/M + O(1)` points. -/
lemma abs_card_filter_modEq_sub_le {M : ℕ} (hM : 0 < M) {A t : ℕ} (hAt : A ≤ t) (k : ℕ) :
    |((((Ioc A t).filter (· ≡ k [MOD M])).card : ℕ) : ℝ) - ((t : ℝ) - A) / M| ≤ 1 := by
  have h := Nat.Ioc_filter_modEq_card A t hM k
  set α : ℚ := ((A : ℚ) - k) / M
  set β : ℚ := ((t : ℚ) - k) / M
  have hαβ : α ≤ β := by
    simp only [α, β]
    gcongr
  have hfl : ⌊α⌋ ≤ ⌊β⌋ := Int.floor_mono hαβ
  rw [max_eq_left (by omega)] at h
  have hc : (((Ioc A t).filter (· ≡ k [MOD M])).card : ℝ) = ((⌊β⌋ - ⌊α⌋ : ℤ) : ℝ) := by
    exact_mod_cast h
  have hdiff : ((t : ℝ) - A) / M = ((β - α : ℚ) : ℝ) := by
    simp only [α, β]
    push_cast
    field_simp
    ring
  rw [hc, hdiff, abs_le]
  have h1 := Int.floor_le α
  have h2 := Int.lt_floor_add_one α
  have h3 := Int.floor_le β
  have h4 := Int.lt_floor_add_one β
  have e1 : ((⌊α⌋ : ℚ) : ℝ) ≤ (α : ℝ) := by exact_mod_cast h1
  have e2 : (α : ℝ) < ((⌊α⌋ : ℚ) : ℝ) + 1 := by exact_mod_cast h2
  have e3 : ((⌊β⌋ : ℚ) : ℝ) ≤ (β : ℝ) := by exact_mod_cast h3
  have e4 : (β : ℝ) < ((⌊β⌋ : ℚ) : ℝ) + 1 := by exact_mod_cast h4
  push_cast at e1 e2 e3 e4 ⊢
  constructor <;> linarith

/-- A system of congruences modulo the distinct primes of `V` has
`(t - A)/∏_{p ∈ V} p + O(1)` solutions in `(A, t]`. -/
lemma abs_card_filter_forall_modEq_sub_le (V : Finset ℕ) (hV : ∀ p ∈ V, p.Prime) (a : ℕ → ℕ)
    {A t : ℕ} (hAt : A ≤ t) :
    |((((Ioc A t).filter fun e => ∀ p ∈ V, e ≡ a p [MOD p]).card : ℕ) : ℝ) -
        ((t : ℝ) - A) / ∏ p ∈ V, (p : ℝ)| ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_forall_modEq_iff V hV a
  have hM : 0 < ∏ p ∈ V, p := prod_pos fun p hp => (hV p hp).pos
  have h := abs_card_filter_modEq_sub_le hM hAt k
  have hfilt : ((Ioc A t).filter fun e => ∀ p ∈ V, e ≡ a p [MOD p]) =
      (Ioc A t).filter (· ≡ k [MOD ∏ p ∈ V, p]) := filter_congr fun e _ => hk e
  rw [hfilt]
  push_cast at h
  exact h

end Erdos408
