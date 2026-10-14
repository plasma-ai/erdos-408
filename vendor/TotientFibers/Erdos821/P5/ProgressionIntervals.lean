import Erdos821.P5.Basic

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core

theorem nat_interval_mem_iff (lo hi : ℝ) (n : ℕ) (hhi : 0 ≤ hi) :
    n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊ ↔ lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi := by
  simp only [Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hhi]

/-- Reindex multiples by their quotient, retaining the real interval endpoints. -/
theorem sum_interval_multiples {α : Type*} [AddCommMonoid α]
    (lo hi : ℝ) (d : ℕ) (f : ℕ → α)
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (fun n => d ∣ n), f n) =
      ∑ v ∈ Finset.Icc ⌈lo / (d : ℝ)⌉₊ ⌊hi / (d : ℝ)⌋₊, f (d * v) := by
  classical
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hhi : 0 ≤ hi := hlo.trans hlohi
  have hhid : 0 ≤ hi / (d : ℝ) := div_nonneg hhi hdR.le
  have hmul (n : ℕ) (hn : d ∣ n) : d * (n / d) = n := Nat.mul_div_cancel' hn
  refine Finset.sum_nbij' (fun n => n / d) (fun v => d * v) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnI, hdn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnlo, hnhi⟩ := (nat_interval_mem_iff lo hi n hhi).mp hnI
    have heq : (d : ℝ) * (n / d : ℕ) = (n : ℝ) := by exact_mod_cast hmul n hdn
    apply (nat_interval_mem_iff _ _ _ hhid).mpr
    constructor
    · apply (div_le_iff₀ hdR).mpr
      nlinarith
    · apply (le_div_iff₀ hdR).mpr
      nlinarith
  · intro v hv
    obtain ⟨hvlo, hvhi⟩ := (nat_interval_mem_iff _ _ _ hhid).mp hv
    apply Finset.mem_filter.mpr
    refine ⟨(nat_interval_mem_iff lo hi (d * v) hhi).mpr ?_, dvd_mul_right _ _⟩
    constructor <;> push_cast
    · have := (div_le_iff₀ hdR).mp hvlo
      nlinarith
    · have := (le_div_iff₀ hdR).mp hvhi
      nlinarith
  · intro n hn
    exact hmul n (Finset.mem_filter.mp hn).2
  · intro v hv
    simp [hd.ne']
  · intro n hn
    rw [hmul n (Finset.mem_filter.mp hn).2]

/-- A single residue class is exactly an integer interval in the quotient
variable. The lower bound ensures that `Int.toNat` preserves every endpoint. -/
theorem sum_interval_residue (lo hi : ℝ) (q a : ℕ) (f : ℕ → ℂ)
    (hq : 0 < q) (haq : a < q) (hlo : (q : ℝ) ≤ lo) (hlohi : lo ≤ hi) :
    (∑ v ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (fun v => v % q = a), f v) =
      ∑ y ∈ Finset.Icc ⌈(lo - a) / (q : ℝ)⌉ ⌊(hi - a) / (q : ℝ)⌋,
        f (q * y.toNat + a) := by
  classical
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have haR : (a : ℝ) < q := by exact_mod_cast haq
  have hhi : 0 ≤ hi := hqR.le.trans (hlo.trans hlohi)
  have hdecomp (v : ℕ) (hv : v % q = a) : v = q * (v / q) + a := by
    have h := Nat.mod_add_div v q
    rw [hv] at h
    omega
  have hnonneg (y : ℤ)
      (hy : y ∈ Finset.Icc ⌈(lo - a) / (q : ℝ)⌉ ⌊(hi - a) / (q : ℝ)⌋) : 0 ≤ y := by
    have hylo := Int.ceil_le.mp (Finset.mem_Icc.mp hy).1
    have hstart : 0 < (lo - a) / (q : ℝ) := by apply div_pos <;> linarith
    have : 0 ≤ (y : ℝ) := (hstart.trans_le hylo).le
    exact_mod_cast this
  have hreal (y : ℤ) (hy : 0 ≤ y) : (q * y.toNat + a : ℕ) = (q : ℤ) * y + a := by
    push_cast
    rw [Int.toNat_of_nonneg hy]
  have hdiv (y : ℤ) : (q * y.toNat + a) / q = y.toNat := by
    have hmod : (q * y.toNat + a) % q = a := by simp [Nat.add_mod, Nat.mod_eq_of_lt haq]
    have h := hdecomp (q * y.toNat + a) hmod
    have hm : q * ((q * y.toNat + a) / q) = q * y.toNat := by omega
    exact Nat.eq_of_mul_eq_mul_left hq hm
  refine Finset.sum_nbij' (fun v => ((v / q : ℕ) : ℤ))
    (fun y => q * y.toNat + a) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    obtain ⟨hvI, hmod⟩ := Finset.mem_filter.mp hv
    obtain ⟨hvlo, hvhi⟩ := (nat_interval_mem_iff lo hi v hhi).mp hvI
    have heq : (v : ℝ) = (q : ℝ) * (v / q : ℕ) + a := by exact_mod_cast hdecomp v hmod
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.ceil_le.mpr
      apply (div_le_iff₀ hqR).mpr
      simp only [Int.cast_natCast]
      nlinarith
    · apply Int.le_floor.mpr
      apply (le_div_iff₀ hqR).mpr
      simp only [Int.cast_natCast]
      nlinarith
  · intro y hy
    have hy0 := hnonneg y hy
    have heq : (q * y.toNat + a : ℕ) = (q : ℤ) * y + a := hreal y hy0
    have heqR : (q * y.toNat + a : ℕ) = (q : ℝ) * (y : ℝ) + a := by exact_mod_cast heq
    have hylo := (div_le_iff₀ hqR).mp (Int.ceil_le.mp (Finset.mem_Icc.mp hy).1)
    have hyhi := (le_div_iff₀ hqR).mp (Int.le_floor.mp (Finset.mem_Icc.mp hy).2)
    refine Finset.mem_filter.mpr ⟨(nat_interval_mem_iff lo hi _ hhi).mpr ?_, ?_⟩
    · constructor <;> nlinarith
    · simp [Nat.add_mod, Nat.mod_eq_of_lt haq]
  · intro v hv
    simp only [Int.toNat_natCast]
    exact (hdecomp v (Finset.mem_filter.mp hv).2).symm
  · intro y hy
    rw [hdiv, Int.toNat_of_nonneg (hnonneg y hy)]
  · intro v hv
    simp only [Int.toNat_natCast]
    rw [← hdecomp v (Finset.mem_filter.mp hv).2]

/-- Sum every residue class before invoking its analytic cancellation bound. -/
theorem sum_interval_residues (lo hi : ℝ) (q : ℕ) (f : ℕ → ℂ)
    (hq : 0 < q) (hlo : (q : ℝ) ≤ lo) (hlohi : lo ≤ hi) :
    (∑ v ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊, f v) =
      ∑ a ∈ Finset.range q,
        ∑ y ∈ Finset.Icc ⌈(lo - a) / (q : ℝ)⌉ ⌊(hi - a) / (q : ℝ)⌋,
          f (q * y.toNat + a) := by
  classical
  calc
    _ = ∑ a ∈ Finset.range q,
        ∑ v ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (fun v => v % q = a), f v := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun v _ => Finset.mem_range.mpr (Nat.mod_lt v hq)) f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      exact sum_interval_residue lo hi q a f hq (Finset.mem_range.mp ha) hlo hlohi

end Erdos821.P5Core
