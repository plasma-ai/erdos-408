import Erdos821.S34.Bilinear
import Erdos821.S34.IntegerLargeSieve

set_option autoImplicit false

open scoped BigOperators Classical
open OAI.LargePrimeGaps

namespace Erdos821.S34.Proofs

def shortBlockStep (r : ℕ) : ℕ := (r + 1) / 2
def shortBlock (start : ℤ) (r : ℕ) (t : ℤ) : ℕ :=
  (t - start).toNat / shortBlockStep r

theorem shortBlockStep_pos (r : ℕ) (hr : 1 ≤ r) : 0 < shortBlockStep r := by
  unfold shortBlockStep
  omega

theorem shortBlock_span (start i j : ℤ) (r : ℕ) (hr : 1 ≤ r)
    (hi : start ≤ i) (hj : start ≤ j) (hblock : shortBlock start r i = shortBlock start r j) :
    |((i - j : ℤ) : ℝ)| ≤ (r : ℝ) / 2 := by
  have hstep := shortBlockStep_pos r hr
  have hmi := Nat.mod_lt (i - start).toNat hstep
  have hmj := Nat.mod_lt (j - start).toNat hstep
  have hdi := Nat.mod_add_div (i - start).toNat (shortBlockStep r)
  have hdj := Nat.mod_add_div (j - start).toNat (shortBlockStep r)
  change (i - start).toNat / shortBlockStep r = (j - start).toNat / shortBlockStep r at hblock
  rw [hblock] at hdi
  have hpi : (i : ℝ) - j ≤ (shortBlockStep r : ℝ) - 1 := by
    exact_mod_cast (show i - j ≤ (shortBlockStep r : ℤ) - 1 by omega)
  have hpj : (j : ℝ) - i ≤ (shortBlockStep r : ℝ) - 1 := by
    exact_mod_cast (show j - i ≤ (shortBlockStep r : ℤ) - 1 by omega)
  have hu : 2 * shortBlockStep r ≤ r + 1 := by unfold shortBlockStep; omega
  have hu' : 2 * (shortBlockStep r : ℝ) ≤ (r : ℝ) + 1 := by exact_mod_cast hu
  push_cast
  apply abs_le.mpr
  constructor <;> linarith

theorem shortBlock_count (s : Finset ℤ) (start : ℤ) (r : ℕ) (hr : 1 ≤ r)
    (A : ℝ) (hA : 0 ≤ A)
    (hs : ∀ t ∈ s, start ≤ t ∧ (t : ℝ) - start ≤ A) :
    ((s.image (shortBlock start r)).card : ℝ) ≤ 2 * A / r + 1 := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hlow : r ≤ 2 * shortBlockStep r := by unfold shortBlockStep; omega
  have hlow' : (r : ℝ) ≤ 2 * (shortBlockStep r : ℝ) := by exact_mod_cast hlow
  have hindex (t : ℤ) (ht : t ∈ s) : (shortBlock start r t : ℝ) ≤ 2 * A / r := by
    obtain ⟨hstart, hbound⟩ := hs t ht
    have hoff : ((t - start).toNat : ℝ) = (t : ℝ) - start := by
      exact_mod_cast (show ((t - start).toNat : ℤ) = t - start by omega)
    have hquot : (shortBlock start r t : ℝ) * (shortBlockStep r : ℝ) ≤ A := by
      have h : (shortBlock start r t : ℝ) * (shortBlockStep r : ℝ) ≤
          ((t - start).toNat : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self (t - start).toNat (shortBlockStep r)
      exact h.trans (hoff ▸ hbound)
    have hmul := mul_le_mul_of_nonneg_left hlow' (Nat.cast_nonneg (shortBlock start r t))
    apply (le_div_iff₀ hrpos).mpr
    nlinarith
  have hsub : s.image (shortBlock start r) ⊆ Finset.range (⌊2 * A / r⌋₊ + 1) := by
    intro b hb
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
    have h := Nat.le_floor (hindex t ht)
    exact Finset.mem_range.mpr (by omega)
  have hcard : ((s.image (shortBlock start r)).card : ℝ) ≤ (⌊2 * A / r⌋₊ : ℝ) + 1 := by
    exact_mod_cast (by simpa only [Finset.card_range] using Finset.card_le_card hsub)
  have hfloor := Nat.floor_le (show 0 ≤ 2 * A / (r : ℝ) by positivity)
  linarith

theorem sum_filter_partition {ι κ E : Type*} [DecidableEq κ] [AddCommMonoid E]
    (s : Finset ι) (index : ι → κ) (f : ι → E) :
    (∑ i ∈ s, f i) = ∑ b ∈ s.image index, ∑ i ∈ s.filter (fun i => index i = b), f i := by
  calc
    _ = ∑ b ∈ s.image index, ∑ i ∈ s, if index i = b then f i else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      have hb := Finset.mem_image_of_mem index hi
      simp [hb]
    _ = _ := by simp only [Finset.sum_filter]

theorem norm_sum_mul_sq {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * (∑ i ∈ s, ‖b i‖ ^ 2) := by
  have h : ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun i => a i * b i)
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖))

/-- The squared frequency estimate underlying §3's integer bilinear bound. -/
theorem rational_block_large_sieve (α β : ℝ) (u : ℤ) (r : ℕ)
    (hr : 1 ≤ r) (hu : Nat.Coprime u.natAbs r)
    (hα : α = (u : ℝ) / r + β) (hβ : |β| ≤ 1 / (r : ℝ) ^ 2)
    (t : Finset ℤ) (start : ℤ) (A : ℝ) (hA : 0 ≤ A)
    (ht : ∀ v ∈ t, start ≤ v ∧ (v : ℝ) - start ≤ A)
    (s : Finset ℤ) (lo : ℤ) (N : ℕ) (a : ℤ → ℂ)
    (hs : ∀ n ∈ s, lo ≤ n ∧ n < lo + N) :
    (∑ v ∈ t, ‖∑ n ∈ s, a n * bvExp (α * n * v)‖ ^ 2) ≤
      (2 * A / r + 1) * ((N : ℝ) + 2 * r * (harmonic (2 * r) : ℝ)) *
        (∑ n ∈ s, ‖a n‖ ^ 2) := by
  let K : ℝ := (N : ℝ) + 2 * r * (harmonic (2 * r) : ℝ)
  let E : ℝ := ∑ n ∈ s, ‖a n‖ ^ 2
  have hH : 0 ≤ (harmonic (2 * r) : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg (fun _ _ => by
      simp only [Rat.cast_inv, Rat.cast_natCast]
      positivity)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hblock (b : ℕ) :
      (∑ v ∈ t.filter (fun v => shortBlock start r v = b),
        ‖∑ n ∈ s, a n * bvExp (α * n * v)‖ ^ 2) ≤ K * E := by
    have hsep : ∀ i ∈ t.filter (fun v => shortBlock start r v = b),
        ∀ j ∈ t.filter (fun v => shortBlock start r v = b), i ≠ j →
        ∀ q : ℤ, 1 / ((2 * r : ℕ) : ℝ) ≤ |α * i - α * j - q| := by
      intro i hi j hj hij q
      obtain ⟨hi, hbi⟩ := Finset.mem_filter.mp hi
      obtain ⟨hj, hbj⟩ := Finset.mem_filter.mp hj
      have hspan := shortBlock_span start i j r hr (ht i hi).1 (ht j hj).1
        (hbi.trans hbj.symm)
      have h := rational_frequency_separation α β u (i - j) q r hr hu hα hβ
        (sub_ne_zero.mpr hij) hspan
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Int.cast_sub, mul_sub] using h
    have h := integer_additive_large_sieve
      (t.filter (fun v => shortBlock start r v = b)) (fun v => α * (v : ℝ))
      (2 * r) (by omega) hsep s lo N a hs
    convert h using 1
    · apply Finset.sum_congr rfl
      intro v _
      congr 2
      apply Finset.sum_congr rfl
      intro n _
      congr 2
      ring
    · simp only [K, E, Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ = ∑ b ∈ t.image (shortBlock start r),
        ∑ v ∈ t.filter (fun v => shortBlock start r v = b),
          ‖∑ n ∈ s, a n * bvExp (α * n * v)‖ ^ 2 :=
      sum_filter_partition t (shortBlock start r) _
    _ ≤ ∑ _ ∈ t.image (shortBlock start r), K * E :=
      Finset.sum_le_sum fun b _ => hblock b
    _ = ((t.image (shortBlock start r)).card : ℝ) * (K * E) := by simp
    _ ≤ (2 * A / r + 1) * (K * E) :=
      mul_le_mul_of_nonneg_right (shortBlock_count t start r hr A hA ht) (mul_nonneg hK hE)
    _ = _ := by dsimp [K, E]; ring

end Erdos821.S34.Proofs
