import Erdos408.Mertens
import Erdos408.Extraction.Defs

/-!
# Prime sums for the proxy estimates

Mertens' third theorem in the form `∏_{p ≤ y} (1 - 1/p) ≥ c₃ / log y`, and the
identification of the prime sets `primesIcc 2 y`, `primesIoc 1 y` and
`{p ≤ N prime}` used by the Euler-product bounds.
-/

namespace Erdos408.TypeII

open Finset Real

theorem mem_primesIcc {a b : ℝ} {p : ℕ} :
    p ∈ primesIcc a b ↔ p.Prime ∧ ⌈a⌉₊ ≤ p ∧ p ≤ ⌊b⌋₊ := by
  simp only [primesIcc, mem_filter, mem_Icc]
  tauto

/-- The primes up to `y ≥ 0` are `primesIcc 2 y`. -/
theorem primesIcc_two_eq (y : ℝ) : primesIcc 2 y = (Ioc 0 ⌊y⌋₊).filter Nat.Prime := by
  ext p
  rw [mem_primesIcc, mem_filter, mem_Ioc]
  have h2 : ⌈(2 : ℝ)⌉₊ = 2 := by norm_num
  rw [h2]
  constructor
  · rintro ⟨hp, -, h⟩
    exact ⟨⟨hp.pos, h⟩, hp⟩
  · rintro ⟨⟨-, h⟩, hp⟩
    exact ⟨hp, hp.two_le, h⟩

/-- The primes up to `N` are `primesIcc 2 N`. -/
theorem range_filter_prime_eq (N : ℕ) :
    (range (N + 1)).filter Nat.Prime = primesIcc 2 (N : ℝ) := by
  rw [primesIcc_two_eq, Nat.floor_natCast]
  ext p
  simp only [mem_filter, mem_range, mem_Ioc]
  constructor
  · rintro ⟨h, hp⟩
    exact ⟨⟨hp.pos, by omega⟩, hp⟩
  · rintro ⟨⟨-, h⟩, hp⟩
    exact ⟨by omega, hp⟩

/-- The primes up to `y` are `primesIoc 1 y`. -/
theorem primesIcc_two_eq_primesIoc (y : ℝ) : primesIcc 2 y = primesIoc 1 y := by
  ext p
  rw [mem_primesIoc_one, primesIcc_two_eq, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨-, h⟩, hp⟩
    exact ⟨hp, (Nat.le_floor_iff' hp.ne_zero).1 h⟩
  · rintro ⟨hp, h⟩
    exact ⟨⟨hp.pos, (Nat.le_floor_iff' hp.ne_zero).2 h⟩, hp⟩

/-- Mertens' third theorem, lower bound: `∏_{p ≤ y} (1 - 1/p) ≥ c₃ / log y`. -/
theorem mertens_third_lower : ∃ c₃ : ℝ, 0 < c₃ ∧ ∀ y : ℝ, 2 ≤ y →
    c₃ / Real.log y ≤ ∏ p ∈ primesIcc 2 y, (1 - (1 : ℝ) / p) := by
  obtain ⟨C, hC⟩ := Mertens.E₃.abs_le
  refine ⟨Real.exp (-eulerMascheroniConstant) * Real.exp (-(|C| / Real.log 2)), by positivity,
    fun y hy => ?_⟩
  have hly : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlpos : 0 < Real.log y := lt_of_lt_of_le hl2 hly
  rw [primesIcc_two_eq, Mertens.prod_one_minus_div_prime_eq (by linarith)]
  have hE := hC y hy
  have hE' : -(|C| / Real.log 2) ≤ Mertens.E₃ y := by
    have h1 : C / Real.log y ≤ |C| / Real.log 2 := by
      calc C / Real.log y ≤ |C| / Real.log y := by gcongr; exact le_abs_self C
        _ ≤ |C| / Real.log 2 := div_le_div_of_nonneg_left (abs_nonneg C) hl2 hly
    have := neg_abs_le (Mertens.E₃ y)
    rw [abs_le] at hE
    linarith
  gcongr

/-- The reciprocal form: `∏_{p ≤ y} (1 - 1/p)⁻¹ ≤ log y / c₃`. -/
theorem mertens_third_inv_upper : ∃ c₃ : ℝ, 0 < c₃ ∧ ∀ y : ℝ, 2 ≤ y →
    ∏ p ∈ primesIcc 2 y, (1 - (1 : ℝ) / p)⁻¹ ≤ Real.log y / c₃ := by
  obtain ⟨c₃, hc₃, h⟩ := mertens_third_lower
  refine ⟨c₃, hc₃, fun y hy => ?_⟩
  have hlpos : 0 < Real.log y := Real.log_pos (by linarith)
  have hpos : 0 < ∏ p ∈ primesIcc 2 y, (1 - (1 : ℝ) / p) := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesIcc.1 hp).1.two_le
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  rw [prod_inv_distrib, inv_le_comm₀ hpos (by positivity), inv_div]
  exact h y hy

end Erdos408.TypeII
