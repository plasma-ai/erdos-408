import Mathlib
import Erdos821.Blueprint.Graph
import Erdos821.Blueprint.Analytic

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace Erdos821.GraphLemmas

theorem fin_tail_filter (n : ℕ) (j : Fin n) :
    (Finset.univ.filter (fun i : Fin (n+1) => j.castSucc < i))
    = insert (Fin.last n) (Finset.image Fin.castSucc
      (Finset.univ.filter (fun i : Fin n => j < i))) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_image]
  constructor
  · intro hi
    by_cases hlast : i = Fin.last n
    · left; exact hlast
    · right
      have hex : ∃ j0 : Fin n, j0.castSucc = i :=
        Fin.exists_castSucc_eq.mpr hlast
      obtain ⟨i0, hi0⟩ := hex
      refine ⟨i0, ?_, hi0⟩
      have hlt : j.castSucc < i0.castSucc := hi0 ▸ hi
      exact Fin.castSucc_lt_castSucc_iff.mp hlt
  · intro hi
    rcases hi with rfl | ⟨i0, hi0, heq⟩
    · exact Fin.castSucc_lt_last j
    · rw [← heq]
      exact Fin.castSucc_lt_castSucc_iff.mpr hi0

theorem fin_last_tail_empty (n : ℕ) :
    (Finset.univ.filter (fun i : Fin (n+1) => Fin.last n < i)) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro i _
  exact not_lt_of_ge (Fin.le_last i)

theorem fin_prefix {R : Type*} [CommRing R] (n : ℕ) (f : Fin n → R) :
    (∏ i, (1 - f i)) =
      1 - ∑ j, f j * ∏ i ∈ Finset.univ.filter (fun i => j < i), (1 - f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprod : (∏ i : Fin (n+1), (1 - f i))
        = (∏ i : Fin n, (1 - f i.castSucc)) * (1 - f (Fin.last n)) := by
      rw [Fin.prod_univ_castSucc]
    have htail : ∀ j : Fin n,
        (∏ i ∈ Finset.univ.filter (fun i : Fin (n+1) => j.castSucc < i), (1 - f i))
        = (∏ i ∈ Finset.univ.filter (fun i : Fin n => j < i), (1 - f i.castSucc))
          * (1 - f (Fin.last n)) := by
      intro j
      rw [fin_tail_filter n j]
      have hlast_not : Fin.last n ∉ Finset.image Fin.castSucc
          (Finset.univ.filter (fun i : Fin n => j < i)) := by
        intro hcon
        obtain ⟨i0, _, hi0⟩ := Finset.mem_image.mp hcon
        have hne : i0.castSucc ≠ Fin.last n := by
          intro hcontra
          have hex : ∃ k : Fin n, k.castSucc = Fin.last n := ⟨i0, hcontra⟩
          have := (Fin.exists_castSucc_eq.mp hex)
          exact this rfl
        exact hne hi0
      rw [Finset.prod_insert hlast_not,
        Finset.prod_image (Fin.castSucc_injective n).injOn]
      ring
    have hempty : (∏ i ∈ Finset.univ.filter (fun i : Fin (n+1) => Fin.last n < i),
        (1 - f i)) = 1 := by
      rw [fin_last_tail_empty]
      exact Finset.prod_empty
    have hsum : (∑ j : Fin (n+1), f j * ∏ i ∈ Finset.univ.filter (fun i => j < i), (1 - f i))
        = (∑ j : Fin n, f j.castSucc * (∏ i ∈ Finset.univ.filter (fun i => j < i), (1 - f i.castSucc)))
          * (1 - f (Fin.last n)) + f (Fin.last n) := by
      rw [Fin.sum_univ_castSucc]
      simp only [hempty, mul_one]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [htail j, mul_assoc]
    have ih' := ih (fun i : Fin n => f i.castSucc)
    rw [hprod, hsum, ih']
    ring

theorem fin_interval_stable (n : ℕ) (j i : Fin n) :
    (Finset.univ.filter (fun t : Fin (n+1) => j.castSucc < t ∧ t < i.castSucc))
    = Finset.image Fin.castSucc (Finset.univ.filter (fun t : Fin n => j < t ∧ t < i)) := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro ht
    obtain ⟨hlt, htu⟩ := ht
    have hne : t ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le htu (Fin.le_last _))
    have hex : ∃ t0 : Fin n, t0.castSucc = t := Fin.exists_castSucc_eq.mpr hne
    obtain ⟨t0, ht0⟩ := hex
    refine ⟨t0, ⟨?_, ?_⟩, ht0⟩
    · have h : j.castSucc < t0.castSucc := ht0 ▸ hlt
      exact Fin.castSucc_lt_castSucc_iff.mp h
    · have h : t0.castSucc < i.castSucc := ht0 ▸ htu
      exact Fin.castSucc_lt_castSucc_iff.mp h
  · intro ht
    obtain ⟨t0, ⟨hj, hi⟩, ht0⟩ := ht
    rw [← ht0]
    exact ⟨Fin.castSucc_lt_castSucc_iff.mpr hj, Fin.castSucc_lt_castSucc_iff.mpr hi⟩

theorem fin_tail_interval (n : ℕ) (j : Fin n) :
    (Finset.univ.filter (fun t : Fin (n+1) => j.castSucc < t ∧ t < Fin.last n))
    = Finset.image Fin.castSucc (Finset.univ.filter (fun t : Fin n => j < t)) := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro ht
    obtain ⟨hlt, htu⟩ := ht
    have hne : t ≠ Fin.last n := ne_of_lt htu
    have hex : ∃ t0 : Fin n, t0.castSucc = t := Fin.exists_castSucc_eq.mpr hne
    obtain ⟨t0, ht0⟩ := hex
    refine ⟨t0, ?_, ht0⟩
    have h : j.castSucc < t0.castSucc := ht0 ▸ hlt
    exact Fin.castSucc_lt_castSucc_iff.mp h
  · intro ht
    obtain ⟨t0, hj, ht0⟩ := ht
    rw [← ht0]
    exact ⟨Fin.castSucc_lt_castSucc_iff.mpr hj, Fin.castSucc_lt_last _⟩

theorem fin_orphan {R : Type*} [CommRing R] (n : ℕ) (f : Fin n → R) :
    (∏ i, (1 - f i)) =
      1 - (∑ i, f i) +
        ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
          f j * f i * ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i), (1 - f t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprod : (∏ i : Fin (n+1), (1 - f i))
        = (∏ i : Fin n, (1 - f i.castSucc)) * (1 - f (Fin.last n)) := by
      rw [Fin.prod_univ_castSucc]
    have hS : (∑ i : Fin (n+1), f i)
        = (∑ i : Fin n, f i.castSucc) + f (Fin.last n) := by
      rw [Fin.sum_univ_castSucc]
    have hinner : ∀ j : Fin n,
        (∑ i ∈ Finset.univ.filter (fun i : Fin (n+1) => j.castSucc < i),
          f j.castSucc * f i * ∏ t ∈ Finset.univ.filter (fun t : Fin (n+1) => j.castSucc < t ∧ t < i), (1 - f t))
        = (∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),
          f j.castSucc * f i.castSucc * ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i), (1 - f t.castSucc))
          + f j.castSucc * f (Fin.last n) * ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t), (1 - f t.castSucc) := by
      intro j
      rw [fin_tail_filter n j]
      have hlast_not : Fin.last n ∉ Finset.image Fin.castSucc
          (Finset.univ.filter (fun i : Fin n => j < i)) := by
        intro hcon
        obtain ⟨i0, _, hi0⟩ := Finset.mem_image.mp hcon
        have hne : i0.castSucc ≠ Fin.last n := by
          intro hcontra
          have hex : ∃ k : Fin n, k.castSucc = Fin.last n := ⟨i0, hcontra⟩
          have := (Fin.exists_castSucc_eq.mp hex)
          exact this rfl
        exact hne hi0
      rw [Finset.sum_insert hlast_not, add_comm]
      congr 1
      · rw [Finset.sum_image (Fin.castSucc_injective n).injOn]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [fin_interval_stable n j i,
          Finset.prod_image (Fin.castSucc_injective n).injOn]
      · have hlast_prod : (∏ t ∈ Finset.univ.filter
            (fun t : Fin (n+1) => j.castSucc < t ∧ t < Fin.last n), (1 - f t))
            = ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t), (1 - f t.castSucc) := by
          rw [fin_tail_interval n j,
            Finset.prod_image (Fin.castSucc_injective n).injOn]
        rw [hlast_prod]
    have hempty_inner : (∑ i ∈ Finset.univ.filter (fun i : Fin (n+1) => Fin.last n < i),
        f (Fin.last n) * f i * ∏ t ∈ Finset.univ.filter (fun t : Fin (n+1) => Fin.last n < t ∧ t < i), (1 - f t)) = 0 := by
      rw [fin_last_tail_empty]
      exact Finset.sum_empty
    have hD : (∑ j : Fin (n+1), ∑ i ∈ Finset.univ.filter (fun i : Fin (n+1) => j < i),
          f j * f i * ∏ t ∈ Finset.univ.filter (fun t : Fin (n+1) => j < t ∧ t < i), (1 - f t))
        = (∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),
          f j.castSucc * f i.castSucc * ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i), (1 - f t.castSucc))
          + f (Fin.last n) * (∑ j : Fin n, f j.castSucc * ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t), (1 - f t.castSucc)) := by
      rw [Fin.sum_univ_castSucc, hempty_inner, add_zero, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [hinner j]
      ring
    have hpref := fin_prefix n (fun i : Fin n => f i.castSucc)
    have htailsum : (∑ j : Fin n, f j.castSucc * ∏ i ∈ Finset.univ.filter (fun i => j < i), (1 - f i.castSucc))
        = 1 - ∏ i : Fin n, (1 - f i.castSucc) := by
      rw [hpref]
      ring
    have ih' := ih (fun i : Fin n => f i.castSucc)
    rw [hprod, hS, hD, htailsum, ih']
    ring

variable {p n : ℕ} [NeZero p]

theorem single_avg_swap (h : Fin n → ZMod p) (η : Fin n → ℝ) :
    (∑ r : ZMod p, ∑ i : Fin n, η i * (if r + h i = 0 then (1:ℝ) else 0))
    = ∑ i : Fin n, η i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  have h1 : (∑ r : ZMod p, (if r + h i = 0 then (1:ℝ) else 0)) = 1 := by
    rw [Finset.sum_eq_single (-h i)]
    · simp
    · intro r _ hr
      have hne : ¬ (r + h i = 0) := by
        intro hcon
        have : r = -h i := add_eq_zero_iff_eq_neg.mp hcon
        exact hr this
      simp [hne]
    · simp
  rw [h1, mul_one]

theorem avg_one2 : ((p : ℝ)⁻¹ * ∑ _r : ZMod p, (1 : ℝ)) = 1 := by
  have hcard : (∑ _r : ZMod p, (1 : ℝ)) = (p : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card p]
    simp
  rw [hcard]
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  field_simp

theorem double_residue_sum2 (h : Fin n → ZMod p) (η : Fin n → ℝ)
    (j : Fin n) (i : Fin n) :
    (∑ r : ZMod p,
      ((if r + h j = 0 then (1:ℝ) else 0) * (if r + h i = 0 then (1:ℝ) else 0) *
        ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i),
          (1 - η t * (if r + h t = 0 then (1:ℝ) else 0))))
    = ((if h j = h i then (1:ℝ) else 0) *
        ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i),
          (1 - η t * (if h t = h j then (1:ℝ) else 0))) := by
  by_cases heq : h j = h i
  · have hprod : ∀ r : ZMod p,
        (if r + h j = 0 then (1:ℝ) else 0) * (if r + h i = 0 then (1:ℝ) else 0)
        = (if r + h i = 0 then (1:ℝ) else 0) := by
      intro r
      by_cases hr : r + h i = 0
      · have hrj : r + h j = 0 := heq ▸ hr
        simp [hr, hrj]
      · have hrj : ¬ (r + h j = 0) := fun hcon => hr (heq ▸ hcon)
        simp [hr, hrj]
    simp only [hprod]
    rw [if_pos heq, one_mul]
    rw [Finset.sum_eq_single (-h i)]
    · have hr0 : (-h i) + h i = 0 := neg_add_cancel (h i)
      rw [if_pos hr0, one_mul]
      apply Finset.prod_congr rfl
      intro t _
      have hiff : ((-h i + h t = 0) ↔ (h t = h j)) := by
        rw [neg_add_eq_zero, ← heq]
        exact ⟨Eq.symm, Eq.symm⟩
      simp only [hiff]
    · intro r _ hrne
      have hrne' : ¬ (r + h i = 0) := by
        intro hcon
        have : r = -h i := add_eq_zero_iff_eq_neg.mp hcon
        exact hrne this
      simp [hrne']
    · simp
  · rw [if_neg heq, zero_mul]
    apply Finset.sum_eq_zero
    intro r _
    by_cases hrj : r + h j = 0
    · have hri : ¬ (r + h i = 0) := by
        intro hcon
        have ej : r = -h j := add_eq_zero_iff_eq_neg.mp hrj
        have ei : r = -h i := add_eq_zero_iff_eq_neg.mp hcon
        have h1 : -h j = -h i := by rw [← ej, ← ei]
        exact heq (neg_inj.mp h1)
      simp [hrj, hri]
    · simp [hrj]

theorem double_avg_swap2 (h : Fin n → ZMod p) (η : Fin n → ℝ) :
    (∑ r : ZMod p, ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i => j < i),
      η j * η i *
        (((if r + h j = 0 then (1:ℝ) else 0) * (if r + h i = 0 then (1:ℝ) else 0) *
        ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
          (1 - η t * (if r + h t = 0 then (1:ℝ) else 0)))))
    = ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i => j < i),
      η j * η i *
        (((if h j = h i then (1:ℝ) else 0) *
        ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
          (1 - η t * (if h t = h j then (1:ℝ) else 0)))) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [← Finset.mul_sum]
  congr 1
  exact double_residue_sum2 h η j i

end Erdos821.GraphLemmas

namespace Erdos821.Blueprint.Graph

theorem orphan_expansion (p n : ℕ) [NeZero p] (η : Fin n → ℝ) (h : Fin n → ZMod p) :
    ((p : ℝ)⁻¹ * ∑ r : ZMod p, ∏ i, (1 - η i * if r + h i = 0 then 1 else 0)) =
      1 - (p : ℝ)⁻¹ * ∑ i, η i + (p : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),
          η j * η i * (if h j = h i then 1 else 0) *
            ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i),
              (1 - η t * if h t = h j then 1 else 0) := by
  have hfin : ∀ r : ZMod p,
      (∏ i, (1 - η i * (if r + h i = 0 then (1:ℝ) else 0)))
      = 1 - (∑ i, η i * (if r + h i = 0 then (1:ℝ) else 0)) +
        ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
          (η j * (if r + h j = 0 then (1:ℝ) else 0)) *
          (η i * (if r + h i = 0 then (1:ℝ) else 0)) *
          ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
            (1 - η t * (if r + h t = 0 then (1:ℝ) else 0)) := by
    intro r
    have hh := Erdos821.GraphLemmas.fin_orphan n (fun i => η i * (if r + h i = 0 then (1:ℝ) else 0))
    simpa [mul_assoc] using hh
  -- sum over r
  have hsum : (∑ r : ZMod p, ∏ i, (1 - η i * (if r + h i = 0 then (1:ℝ) else 0)))
      = (∑ _r : ZMod p, (1:ℝ)) - (∑ r : ZMod p, ∑ i, η i * (if r + h i = 0 then (1:ℝ) else 0)) +
        (∑ r : ZMod p, ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
          (η j * (if r + h j = 0 then (1:ℝ) else 0)) *
          (η i * (if r + h i = 0 then (1:ℝ) else 0)) *
          ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
            (1 - η t * (if r + h t = 0 then (1:ℝ) else 0))) := by
    calc (∑ r : ZMod p, ∏ i, (1 - η i * (if r + h i = 0 then (1:ℝ) else 0)))
        = ∑ r : ZMod p, (1 - (∑ i, η i * (if r + h i = 0 then (1:ℝ) else 0)) +
          (∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
            (η j * (if r + h j = 0 then (1:ℝ) else 0)) *
            (η i * (if r + h i = 0 then (1:ℝ) else 0)) *
            ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
              (1 - η t * (if r + h t = 0 then (1:ℝ) else 0)))) := by
          apply Finset.sum_congr rfl
          intro r _
          exact hfin r
      _ = ((∑ _r : ZMod p, (1:ℝ)) - (∑ r : ZMod p, ∑ i, η i * (if r + h i = 0 then (1:ℝ) else 0)) +
          (∑ r : ZMod p, ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
            (η j * (if r + h j = 0 then (1:ℝ) else 0)) *
            (η i * (if r + h i = 0 then (1:ℝ) else 0)) *
            ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
              (1 - η t * (if r + h t = 0 then (1:ℝ) else 0)))) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- factor double sum summands to match double_avg_swap2 form
  have hDrew : (∑ r : ZMod p, ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
          (η j * (if r + h j = 0 then (1:ℝ) else 0)) *
          (η i * (if r + h i = 0 then (1:ℝ) else 0)) *
          ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
            (1 - η t * (if r + h t = 0 then (1:ℝ) else 0)))
      = (∑ r : ZMod p, ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i => j < i),
        η j * η i *
          (((if r + h j = 0 then (1:ℝ) else 0) * (if r + h i = 0 then (1:ℝ) else 0) *
          ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
            (1 - η t * (if r + h t = 0 then (1:ℝ) else 0))))) := by
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hS := Erdos821.GraphLemmas.single_avg_swap h η
  have hD := Erdos821.GraphLemmas.double_avg_swap2 h η
  have h1 := Erdos821.GraphLemmas.avg_one2 (p := p)
  -- combine: multiply by (p:ℝ)⁻¹ and distribute
  calc ((p : ℝ)⁻¹ * ∑ r : ZMod p, ∏ i, (1 - η i * if r + h i = 0 then 1 else 0))
      = (p:ℝ)⁻¹ * ((∑ _r : ZMod p, (1:ℝ)) - (∑ r : ZMod p, ∑ i, η i * (if r + h i = 0 then (1:ℝ) else 0)) +
        (∑ r : ZMod p, ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
          (η j * (if r + h j = 0 then (1:ℝ) else 0)) *
          (η i * (if r + h i = 0 then (1:ℝ) else 0)) *
          ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
            (1 - η t * (if r + h t = 0 then (1:ℝ) else 0)))) := by
        rw [hsum]
    _ = ((p:ℝ)⁻¹ * ∑ _r : ZMod p, (1:ℝ)) - (p:ℝ)⁻¹ * (∑ r : ZMod p, ∑ i, η i * (if r + h i = 0 then (1:ℝ) else 0)) +
        (p:ℝ)⁻¹ * (∑ r : ZMod p, ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
          (η j * (if r + h j = 0 then (1:ℝ) else 0)) *
          (η i * (if r + h i = 0 then (1:ℝ) else 0)) *
          ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
            (1 - η t * (if r + h t = 0 then (1:ℝ) else 0))) := by
        ring
    _ = 1 - (p:ℝ)⁻¹ * ∑ i, η i + (p:ℝ)⁻¹ *
        ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),
          η j * η i * (if h j = h i then 1 else 0) *
            ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i),
              (1 - η t * if h t = h j then 1 else 0) := by
        rw [h1, hS, hDrew, hD]
        ring

example : @Erdos821.Blueprint.Graph.orphan_expansion =
    @Erdos821.Blueprint.Graph.orphan_expansion := rfl

end Erdos821.Blueprint.Graph

