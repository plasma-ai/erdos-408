module

public import Erdos408.Extraction.Allocation.Coefficients

/-!
# Regrouping the proxy sum by the product

Group the `j`-tuples of the proxy sum by `w = m₁ ⋯ m_j - 1`. The cutoff
forces `x/κ ≤ w ≤ κ x`, so every factorization of `w + 1` lies in the box
`[1, κ x + 1]^j`, and
`Prox_j = ∑_{1 ≤ w ≤ κ x} Φ(w/x) P(w) (f_𝔟(w) - C_𝔟) A_j(w + 1)`.
-/

@[expose] public section

namespace Erdos408

open Finset

/-- The proxy sum regrouped by `w = ∏ m_i - 1`. -/
theorem proxySum_eq_sum (q cw : ℝ) (K : ℕ) (CN : ℝ) {x : ℝ} (γ : ℝ) {κ : ℝ} (j : ℕ)
    {Φ : ℝ → ℝ} {k : ℕ} (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) (hx : 0 < x)
    (hκ : 0 < κ) (hsupp : ∀ y, Φ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) :
    proxySum q cw K CN x γ κ j Φ u v B =
      ∑ w ∈ Icc 1 ⌊κ * x⌋₊,
        Φ (w / x) * endpoint q cw K CN x u v B w * proxyCoeff x γ j (w + 1) := by
  set box := Fintype.piFinset fun _ : Fin j => Icc 1 ⌊κ * x + 1⌋₊
  set G : (Fin j → ℕ) → ℝ := fun m =>
    Φ (((∏ i, m i : ℕ) - 1 : ℝ) / x) * endpoint q cw K CN x u v B ((∏ i, m i) - 1) *
      ∏ i, strippedProxy x γ j (m i)
  have hκx : 0 ≤ κ * x := by positivity
  -- a nonzero term has `1 ≤ ∏ m - 1 ≤ κ x`
  have hrange : ∀ m ∈ box, G m ≠ 0 → (∏ i, m i) - 1 ∈ Icc 1 ⌊κ * x⌋₊ := by
    intro m _ hm
    have hΦ : Φ (((∏ i, m i : ℕ) - 1 : ℝ) / x) ≠ 0 := by
      intro h
      exact hm (by simp only [G, h, zero_mul])
    obtain ⟨h1, h2⟩ := hsupp _ hΦ
    have hpos : 0 < (((∏ i, m i : ℕ) - 1 : ℝ) / x) := lt_of_lt_of_le (inv_pos.2 hκ) h1
    have hgt : (1 : ℝ) < (∏ i, m i : ℕ) := by
      have := (div_pos_iff_of_pos_right hx).1 hpos
      linarith
    have hgt' : 1 < ∏ i, m i := by exact_mod_cast hgt
    rw [mem_Icc]
    refine ⟨by omega, Nat.le_floor ?_⟩
    rw [Nat.cast_sub hgt'.le, Nat.cast_one]
    rwa [div_le_iff₀ hx] at h2
  rw [proxySum, ← sum_filter_of_ne hrange, ← sum_fiberwise_of_maps_to (t := Icc 1 ⌊κ * x⌋₊)
    (g := fun m => (∏ i, m i) - 1) (f := G) fun m hm => (mem_filter.1 hm).2]
  refine sum_congr rfl fun w hw => ?_
  have hw1 : 1 ≤ w := (mem_Icc.1 hw).1
  have hwN : w + 1 ≤ ⌊κ * x + 1⌋₊ := by
    rw [Nat.floor_add_one hκx]
    exact Nat.succ_le_succ (mem_Icc.1 hw).2
  -- the fiber over `w` is the set of factorizations of `w + 1`
  have hfiber : (box.filter fun m => (∏ i, m i) - 1 ∈ Icc 1 ⌊κ * x⌋₊).filter
      (fun m => (∏ i, m i) - 1 = w) = Nat.finMulAntidiag j (w + 1) := by
    ext m
    simp only [mem_filter, Nat.mem_finMulAntidiag, box, Fintype.mem_piFinset]
    constructor
    · rintro ⟨⟨-, -⟩, h⟩
      exact ⟨by omega, by omega⟩
    · rintro ⟨h, -⟩
      have hm : m ∈ Nat.finMulAntidiag j (w + 1) := Nat.mem_finMulAntidiag.2 ⟨h, by omega⟩
      refine ⟨⟨fun i => mem_Icc.2 ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_finMulAntidiag hm i),
        (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_finMulAntidiag hm i)).trans hwN⟩, ?_⟩, ?_⟩
      · rw [h]
        simpa using hw
      · omega
  rw [hfiber, proxyCoeff, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hprod := Nat.prod_eq_of_mem_finMulAntidiag hm
  simp only [G, hprod, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]

end Erdos408
