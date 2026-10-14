import Erdos821.S2.PrimeLifespans

/-! A finite enumeration of the possible ghost endpoints of an active prime. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

def prefixChoice {n : ℕ} (a : Fin n) (f : Fin n → ℝ) : Option (Fin n) → ℝ
  | none => 1
  | some j => if j < a then -f j * ∏ i ∈ Finset.univ.filter (fun i => j < i ∧ i < a), (1 - f i) else 0

def suffixChoice {n : ℕ} (z : Fin n) (f : Fin n → ℝ) : Option (Fin n) → ℝ
  | none => 1
  | some j => if z < j then -f j * ∏ i ∈ Finset.univ.filter (fun i => z < i ∧ i < j), (1 - f i) else 0

theorem prefixChoice_sum {n : ℕ} (a : Fin n) (f : Fin n → ℝ) :
    (∑ b : Option (Fin n), prefixChoice a f b) =
      1 - ∑ j ∈ Finset.univ.filter (fun j => j < a),
        f j * ∏ i ∈ Finset.univ.filter (fun i => j < i ∧ i < a), (1 - f i) := by
  rw [Fintype.sum_option]
  simp only [prefixChoice]
  rw [← Finset.sum_filter]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

theorem suffixChoice_sum {n : ℕ} (z : Fin n) (f : Fin n → ℝ) :
    (∑ e : Option (Fin n), suffixChoice z f e) =
      1 - ∑ j ∈ Finset.univ.filter (fun j => z < j),
        f j * ∏ i ∈ Finset.univ.filter (fun i => z < i ∧ i < j), (1 - f i) := by
  rw [Fintype.sum_option]
  simp only [suffixChoice]
  rw [← Finset.sum_filter]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

/-- `none` means the corresponding endpoint is the first/last active visit.
A selected earlier/later ghost endpoint supplies its own negative eta factor. -/
def activeSpanTerm (p n : ℕ) [NeZero p] (eta : Fin n → ℝ) (h : Fin n → ZMod p)
    (active : Finset (Fin n)) (a z : Fin n) (birth stop : Option (Fin n)) : ℝ :=
  let f i := eta i * if h i = h a then 1 else 0
  if ∀ i ∈ active, h i = h a then
    (p : ℝ)⁻¹ * prefixChoice a f birth *
      (∏ i ∈ Finset.univ.filter (fun i => a < i ∧ i < z ∧ i ∉ active), (1 - f i)) *
      suffixChoice z f stop
  else 0

/-- One reciprocal-prime charge covers every active use and every later hit. -/
theorem active_span_sum (p n : ℕ) [NeZero p] (eta : Fin n → ℝ) (h : Fin n → ZMod p)
    (active : Finset (Fin n)) (a z : Fin n) (ha : a ∈ active) (hz : z ∈ active)
    (hfirst : ∀ i ∈ active, a ≤ i) (hlast : ∀ i ∈ active, i ≤ z) :
    (∑ birth : Option (Fin n), ∑ stop : Option (Fin n), activeSpanTerm p n eta h active a z birth stop) =
      onePrimeExpectation p n eta h active := by
  let f (i : Fin n) := eta i * if h i = h a then (1 : ℝ) else 0
  let mid : ℝ := ∏ i ∈ Finset.univ.filter (fun i => a < i ∧ i < z ∧ i ∉ active), (1 - f i)
  have he := active_lifespan_expansion n f active a z ha hz hfirst hlast
  rw [onePrimeExpectation_active p n eta h active a ha]
  by_cases hc : ∀ i ∈ active, h i = h a
  · simp only [activeSpanTerm, ite_eq_left hc]
    have hs :
        (∑ birth : Option (Fin n), ∑ stop : Option (Fin n),
          (p : ℝ)⁻¹ * prefixChoice a f birth * mid * suffixChoice z f stop) =
        (p : ℝ)⁻¹ * (∑ birth : Option (Fin n), prefixChoice a f birth) * mid *
          (∑ stop : Option (Fin n), suffixChoice z f stop) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    change (∑ birth : Option (Fin n), ∑ stop : Option (Fin n),
      (p : ℝ)⁻¹ * prefixChoice a f birth * mid * suffixChoice z f stop) =
        (p : ℝ)⁻¹ * ∏ i ∈ Finset.univ.filter (fun i => i ∉ active), (1 - f i)
    rw [hs, prefixChoice_sum, suffixChoice_sum]
    simpa only [mid, mul_assoc] using congrArg (fun v => (p : ℝ)⁻¹ * v) he.symm
  · simp only [activeSpanTerm, ite_eq_right hc, Finset.sum_const_zero, mul_zero]


end Erdos821.S2Core
