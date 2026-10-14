module

public import Erdos408.Additive

/-!
# Prime sums of the additive companion

With `F` from `Erdos408.Additive`, this file names the harmonic sums
`B(x) = ∑_{q ≤ x} F(q) / q`, `C(x) = ∑_{q ≤ x} F(q)² / q` and
`D(x) = ∑_{q ≠ r, q r ≤ x} F(q) F(r) / (q r)` over primes, and the prime
moments `A₁(x) = ∑_{p ≤ x} F(p)` and `A₂(x) = ∑_{p ≤ x} F(p)²`. These are the
quantities of Erdős, Granville, Pomerance and Spiro (1990, Section 2). The
membership and splitting lemmas for `primesIoc` are shared by the later files.
-/

@[expose] public section

namespace Erdos408

/-- The primes `p` with `y < p ≤ z`. -/
noncomputable def primesIoc (y z : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime

/-- The dyad `(x, 2x]` is `primesIoc x (2 * x)`. -/
theorem dyadicPrimes_eq_primesIoc (x : ℝ) : dyadicPrimes x = primesIoc x (2 * x) :=
  rfl

/-- `q ∈ primesIoc y z` iff `q` is a prime with `y < q ≤ z`. No sign conditions are
needed, since `q ≠ 0`. -/
theorem mem_primesIoc {y z : ℝ} {q : ℕ} :
    q ∈ primesIoc y z ↔ q.Prime ∧ y < q ∧ (q : ℝ) ≤ z := by
  simp only [primesIoc, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hy, hz⟩, hq⟩
    exact ⟨hq, (Nat.floor_lt' hq.ne_zero).1 hy, (Nat.le_floor_iff' hq.ne_zero).1 hz⟩
  · rintro ⟨hq, hy, hz⟩
    exact ⟨⟨(Nat.floor_lt' hq.ne_zero).2 hy, (Nat.le_floor_iff' hq.ne_zero).2 hz⟩, hq⟩

/-- `q ∈ primesIoc 1 x` iff `q` is a prime with `q ≤ x`. -/
theorem mem_primesIoc_one {x : ℝ} {q : ℕ} : q ∈ primesIoc 1 x ↔ q.Prime ∧ (q : ℝ) ≤ x := by
  rw [mem_primesIoc]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, by exact_mod_cast h.1.one_lt, h.2⟩⟩

/-- Prime sums over `(y, z]` and `(z, w]` add up to the sum over `(y, w]`. -/
theorem sum_primesIoc_add (g : ℕ → ℝ) {y z w : ℝ} (hyz : y ≤ z) (hzw : z ≤ w) :
    ∑ p ∈ primesIoc y z, g p + ∑ p ∈ primesIoc z w, g p = ∑ p ∈ primesIoc y w, g p := by
  simp only [primesIoc, Finset.sum_filter]
  exact Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor hyz) (Nat.floor_le_floor hzw)

/-- `B(x) = ∑_{q ≤ x} F(q) / q` over primes `q`. -/
noncomputable def harmonicF (x : ℝ) : ℝ :=
  ∑ q ∈ primesIoc 1 x, (F q : ℝ) / q

/-- `C(x) = ∑_{q ≤ x} F(q)² / q` over primes `q`. -/
noncomputable def harmonicFSq (x : ℝ) : ℝ :=
  ∑ q ∈ primesIoc 1 x, (F q : ℝ) ^ 2 / q

/-- `D(x) = ∑ F(q) F(r) / (q r)` over ordered pairs of distinct primes with
`q r ≤ x`. -/
noncomputable def harmonicFPair (x : ℝ) : ℝ :=
  ∑ q ∈ primesIoc 1 x, ∑ r ∈ primesIoc 1 (x / q) with r ≠ q, (F q : ℝ) * F r / (q * r)

/-- `A₁(x) = ∑_{p ≤ x} F(p)` over primes `p`. -/
noncomputable def primeF (x : ℝ) : ℝ :=
  ∑ p ∈ primesIoc 1 x, (F p : ℝ)

/-- `A₂(x) = ∑_{p ≤ x} F(p)²` over primes `p`. -/
noncomputable def primeFSq (x : ℝ) : ℝ :=
  ∑ p ∈ primesIoc 1 x, (F p : ℝ) ^ 2

end Erdos408
