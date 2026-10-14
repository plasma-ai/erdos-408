import OAI.NumberTheory.PrimeGaps.AdditiveSieve
import Mathlib

set_option autoImplicit false

open scoped BigOperators Classical
open OAI.LargePrimeGaps

namespace Erdos821.S34.Proofs

/-- Extend a sequence by zero into an integer interval, without changing its
sum. The origin lo is unrestricted. -/
theorem sum_interval_extension {E : Type*} [AddCommMonoid E]
    (s : Finset ℤ) (lo : ℤ) (N : ℕ)
    (hs : ∀ n ∈ s, lo ≤ n ∧ n < lo + N) (f : ℤ → E) :
    (∑ i : Fin N, if lo + (i : ℤ) ∈ s then f (lo + (i : ℤ)) else 0) =
      ∑ n ∈ s, f n := by
  let index : Fin N → ℤ := fun i => lo + (i : ℤ)
  have hinj : Function.Injective index := by
    intro i j h
    apply Fin.ext
    dsimp [index] at h
    exact_mod_cast add_left_cancel h
  have him : s ⊆ Finset.univ.image index := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := hs n hn
    refine Finset.mem_image.mpr ⟨⟨(n - lo).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp [index]
    omega
  calc
    _ = ∑ n ∈ Finset.univ.image index, if n ∈ s then f n else 0 :=
      (Finset.sum_image (f := fun n => if n ∈ s then f n else 0)
        (fun i _ j _ h => hinj h)).symm
    _ = ∑ n ∈ s, f n := by
      symm
      calc
        _ = ∑ n ∈ s, if n ∈ s then f n else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          simp [hn]
        _ = _ := Finset.sum_subset him (fun n _ hn => by simp [hn])

/-- The prebuilt additive large sieve on an arbitrary integer interval, with
arbitrary holes in the coefficient support. -/
theorem integer_additive_large_sieve {ι : Type*} (frequencies : Finset ι) (θ : ι → ℝ)
    (D : ℕ) (hD : 0 < D)
    (hsep : ∀ i ∈ frequencies, ∀ j ∈ frequencies, i ≠ j →
      ∀ m : ℤ, 1 / (D : ℝ) ≤ |θ i - θ j - m|)
    (s : Finset ℤ) (lo : ℤ) (N : ℕ) (a : ℤ → ℂ)
    (hs : ∀ n ∈ s, lo ≤ n ∧ n < lo + N) :
    (∑ i ∈ frequencies, ‖∑ n ∈ s, a n * bvExp ((n : ℝ) * θ i)‖ ^ 2) ≤
      ((N : ℝ) + (D : ℝ) * (harmonic D : ℝ)) * (∑ n ∈ s, ‖a n‖ ^ 2) := by
  let a' : Fin N → ℂ := fun i => if lo + (i : ℤ) ∈ s then a (lo + (i : ℤ)) else 0
  have hsq : (∑ i : Fin N, ‖a' i‖ ^ 2) = ∑ n ∈ s, ‖a n‖ ^ 2 := by
    simpa [a', apply_ite] using sum_interval_extension s lo N hs (fun n => ‖a n‖ ^ 2)
  have hsum (t : ℝ) : (∑ n ∈ s, a n * bvExp ((n : ℝ) * t)) =
      bvExp ((lo : ℝ) * t) * (∑ i : Fin N, a' i * bvExp (((i : ℕ) : ℝ) * t)) := by
    calc
      _ = ∑ i : Fin N, a' i * bvExp (((lo + (i : ℤ) : ℤ) : ℝ) * t) := by
        symm
        simpa [a', ite_mul] using
          sum_interval_extension s lo N hs (fun n => a n * bvExp ((n : ℝ) * t))
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        rw [add_mul, bvExp_add]
        ring
  calc
    _ = ∑ i ∈ frequencies, ‖∑ n : Fin N, a' n * bvExp (((n : ℕ) : ℝ) * θ i)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hsum, norm_mul]
      simp
    _ ≤ _ := additive_large_sieve frequencies θ hD hsep N a'
    _ = _ := by rw [hsq]

end Erdos821.S34.Proofs
