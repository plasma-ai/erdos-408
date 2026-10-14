import Erdos821.S2.LifespanAlgebra

/-! Exact averaging of the one-prime orphan polynomial over uniform residues. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2

lemma uniform_residue_hit_sum (p : ℕ) [NeZero p] (h : ZMod p) :
    (∑ r : ZMod p, if r + h = 0 then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_eq_single (-h)]
  · simp
  · intro r _ hr
    apply if_neg
    intro he
    apply hr
    calc
      r = (r + h) - h := by abel
      _ = -h := by rw [he]; simp
  · intro hn
    exact False.elim (hn (Finset.mem_univ _))

lemma uniform_residue_pair_sum (p : ℕ) [NeZero p] (n : ℕ)
    (η : Fin n → ℝ) (h : Fin n → ZMod p) (j i : Fin n) :
    (∑ r : ZMod p,
      (η j * if r + h j = 0 then 1 else 0) *
      (η i * if r + h i = 0 then 1 else 0) *
      ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i),
        (1 - η t * if r + h t = 0 then 1 else 0)) =
    η j * η i * (if h j = h i then 1 else 0) *
      ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i),
        (1 - η t * if h t = h j then 1 else 0) := by
  have hz (u : ZMod p) : -h j + u = 0 ↔ u = h j := by
    constructor
    · intro he
      have he' := congrArg (fun z => h j + z) he
      simpa only [add_assoc, add_neg_cancel_left, add_zero] using he'
    · intro he
      rw [he]
      simp
  have hi : -h j + h i = 0 ↔ h j = h i := (hz (h i)).trans eq_comm
  rw [Finset.sum_eq_single (-h j)]
  · simp only [hi, hz, neg_add_cancel, if_true, mul_one]
    ring
  · intro r _ hr
    have hn : ¬ r + h j = 0 := by
      intro he
      apply hr
      calc
        r = (r + h j) - h j := by abel
        _ = -h j := by rw [he]; simp
    simp only [if_neg hn, mul_zero, zero_mul]
  · intro hn
    exact False.elim (hn (Finset.mem_univ _))

/-- eq:orphan-expansion. No primality or size hypothesis is needed for this identity. -/
theorem orphan_expansion (p n : ℕ) [NeZero p] (η : Fin n → ℝ) (h : Fin n → ZMod p) :
    ((p : ℝ)⁻¹ * ∑ r : ZMod p, ∏ i, (1 - η i * if r + h i = 0 then 1 else 0)) =
      1 - (p : ℝ)⁻¹ * ∑ i, η i + (p : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),
          η j * η i * (if h j = h i then 1 else 0) *
            ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i),
              (1 - η t * if h t = h j then 1 else 0) := by
  let f (r : ZMod p) (i : Fin n) : ℝ := η i * if r + h i = 0 then 1 else 0
  let pair (j i : Fin n) : ℝ := η j * η i * (if h j = h i then 1 else 0) *
    ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i),
      (1 - η t * if h t = h j then 1 else 0)
  have hsing : (∑ r : ZMod p, ∑ i : Fin n, f r i) = ∑ i, η i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    change (∑ r : ZMod p, η i * if r + h i = 0 then 1 else 0) = η i
    rw [← Finset.mul_sum, uniform_residue_hit_sum]
    simp
  have hpairs :
      (∑ r : ZMod p, ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),
        f r j * f r i * ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i), (1 - f r t)) =
      ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i), pair j i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact uniform_residue_pair_sum p n η h j i
  have hpoly (r : ZMod p) := orphan_polynomial_ordered (Finset.univ : Finset (Fin n)) (f r)
  have hsum : (∑ r : ZMod p, ∏ i : Fin n, (1 - f r i)) =
      (p : ℝ) - (∑ i, η i) +
        ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i), pair j i := by
    calc
      _ = ∑ r : ZMod p, (1 - (∑ i : Fin n, f r i) +
        ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),
          f r j * f r i * ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i), (1 - f r t)) :=
        Finset.sum_congr rfl (fun r _ => hpoly r)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsing, hpairs]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card, mul_one]
  change (p : ℝ)⁻¹ * (∑ r : ZMod p, ∏ i : Fin n, (1 - f r i)) =
    1 - (p : ℝ)⁻¹ * (∑ i, η i) + (p : ℝ)⁻¹ *
      (∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i), pair j i)
  rw [hsum]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  field_simp [hp]


end Erdos821.S2
