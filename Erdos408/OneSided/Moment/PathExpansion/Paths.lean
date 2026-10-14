import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Paths in matrix powers

Two generic facts for the path expansion (`blueprint/one_sided_type_ii.md` §12, S1).

* `sum_mul_pow_apply`: an entry of `A^N`, paired with a weight on its endpoints, expands into
  paths `path 0, …, path N` with weight `∏_{j < N} A(path j, path (j + 1))`.
* Restriction along an injection `ι : α → β`: products of restricted matrices are restrictions
  of products with the indicator `V` of the image inserted, and powers of a restriction are
  restrictions of powers when the big matrix vanishes off the image.
-/

namespace Erdos408.OneSided

open Finset

variable {α β : Type*} [Fintype α] [Fintype β]

/-- An entry of `A^N` paired with a weight `g` on its endpoints is the sum over paths
`path 0, …, path N` of `g (path 0) (path N) ∏_{j < N} A(path j, path (j + 1))`. -/
theorem sum_mul_pow_apply [DecidableEq α] (A : Matrix α α ℂ) (N : ℕ) (g : α → α → ℂ) :
    ∑ i, ∑ k, g i k * (A ^ N) i k =
      ∑ path : Fin (N + 1) → α, g (path 0) (path (Fin.last N)) *
        ∏ j : Fin N, A (path j.castSucc) (path j.succ) := by
  induction N generalizing g with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) α).symm.sum_comp]
    simp [Matrix.one_apply]
  | succ N ih =>
    calc ∑ i, ∑ k, g i k * (A ^ (N + 1)) i k
        = ∑ m, ∑ k, (∑ i, g i k * A i m) * (A ^ N) m k := by
          -- step: the first edge `i → m`
          simp only [pow_succ', Matrix.mul_apply, mul_sum, sum_mul, mul_assoc]
          rw [sum_comm]
          refine (sum_congr rfl fun k _ => sum_comm).trans ?_
          rw [sum_comm]
      _ = ∑ path : Fin (N + 1) → α, (∑ i, g i (path (Fin.last N)) * A i (path 0)) *
            ∏ j : Fin N, A (path j.castSucc) (path j.succ) := ih _
      _ = _ := by
          -- step: prepend the first vertex
          symm
          rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type, sum_comm]
          refine sum_congr rfl fun path _ => ?_
          rw [sum_mul]
          refine sum_congr rfl fun i _ => ?_
          simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero,
            Fin.castSucc_zero, ← Fin.succ_last, Fin.cons_succ, ← Fin.succ_castSucc, mul_assoc]

/-! ### Restriction along an injection -/

section Restrict

variable {ι : α → β} (hι : Function.Injective ι)
include hι

/-- If `X` and `Y` are the restrictions of `X'` and `Y'` along `ι`, then `X Y` is the
restriction of `X' V Y'`, where `V` is the diagonal indicator `v` of the image of `ι`. -/
theorem mul_apply_eq_restrict [DecidableEq β] {X Y : Matrix α α ℂ} {X' Y' : Matrix β β ℂ}
    {v : β → ℂ} (hv : ∀ i, v (ι i) = 1) (hv₀ : ∀ k ∉ Set.range ι, v k = 0)
    (hX : ∀ i j, X i j = X' (ι i) (ι j)) (hY : ∀ i j, Y i j = Y' (ι i) (ι j)) (i j : α) :
    (X * Y) i j = (X' * Matrix.diagonal v * Y') (ι i) (ι j) := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  refine Fintype.sum_of_injective ι hι _ _ (fun k hk => by rw [hv₀ k hk, mul_zero, zero_mul])
    fun k => ?_
  rw [hX, hY, hv, mul_one]

/-- Powers of the restriction of `B` along `ι` are the restrictions of the powers of `B` when
the columns of `B` off the image of `ι` vanish. -/
theorem pow_apply_eq_restrict [DecidableEq α] [DecidableEq β] {A : Matrix α α ℂ}
    {B : Matrix β β ℂ} (hA : ∀ i j, A i j = B (ι i) (ι j))
    (hB : ∀ k ∉ Set.range ι, ∀ i, B i k = 0) (n : ℕ) (i j : α) :
    (A ^ n) i j = (B ^ n) (ι i) (ι j) := by
  induction n generalizing i j with
  | zero => simp only [pow_zero, Matrix.one_apply, hι.eq_iff]
  | succ n ih =>
    simp only [pow_succ', Matrix.mul_apply]
    exact Fintype.sum_of_injective ι hι _ _ (fun k hk => by rw [hB k hk, zero_mul])
      fun k => by rw [hA, ih]

/-- With `n ≥ 1` and `B` vanishing off the image of `ι` in both indices, the endpoint sums of
`A^n` and `B^n` agree, for the restriction `A` of `B` along `ι`. -/
theorem sum_mul_pow_apply_eq_restrict [DecidableEq α] [DecidableEq β] {A : Matrix α α ℂ}
    {B : Matrix β β ℂ} (hA : ∀ i j, A i j = B (ι i) (ι j))
    (hrow : ∀ k ∉ Set.range ι, ∀ j, B k j = 0) (hcol : ∀ k ∉ Set.range ι, ∀ i, B i k = 0)
    {n : ℕ} (hn : 0 < n) (g : β → β → ℂ) :
    ∑ i, ∑ j, g (ι i) (ι j) * (A ^ n) i j = ∑ k, ∑ l, g k l * (B ^ n) k l := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  -- step: the rows and columns of `B^n` off the image vanish
  have hrow' : ∀ k ∉ Set.range ι, ∀ l, (B ^ (0 + n + 1)) k l = 0 := fun k hk l => by
    rw [zero_add, pow_succ', Matrix.mul_apply]
    exact sum_eq_zero fun m _ => by rw [hrow k hk, zero_mul]
  have hcol' : ∀ l ∉ Set.range ι, ∀ k, (B ^ (0 + n + 1)) k l = 0 := fun l hl k => by
    rw [zero_add, pow_succ, Matrix.mul_apply]
    exact sum_eq_zero fun m _ => by rw [hcol l hl, mul_zero]
  refine Fintype.sum_of_injective ι hι _ _ (fun k hk => sum_eq_zero fun l _ => by
    rw [hrow' k hk, mul_zero]) fun i => ?_
  refine Fintype.sum_of_injective ι hι _ _ (fun l hl => by rw [hcol' l hl, mul_zero])
    fun j => ?_
  rw [pow_apply_eq_restrict hι hA hcol]

end Restrict

/-- The restriction of `𝒢 𝒮 𝒯 𝒮 𝒢` with the indicator `V` inserted, and the weight `W` on
both sides of `𝒯`, is `W 𝒢 𝒮 𝒯 𝒮 𝒢 W` when `W` commutes with `𝒢` and `𝒮` and
`V W = W V = W`. -/
theorem edge_restrict_eq {R : Type*} [Semiring R] {G S T V W : R} (hGW : G * W = W * G)
    (hSW : S * W = W * S) (hVW : V * W = W) (hWV : W * V = W) :
    G * V * S * V * (W * T * W) * V * S * V * G = W * (G * S * T * S * G) * W := by
  simp only [mul_assoc]
  -- step: absorb the inner indicators into `W`
  rw [← mul_assoc V W, hVW, ← mul_assoc W V, hWV]
  -- step: move `W` out past `𝒮` and absorb the outer indicators
  rw [← mul_assoc S W, hSW, mul_assoc W S, ← mul_assoc V W, hVW]
  rw [← mul_assoc W S (V * G), ← hSW, mul_assoc S W]
  -- step: move `W` out past `𝒢`
  rw [← mul_assoc G W, hGW, mul_assoc W G, ← mul_assoc W V G, hWV, ← hGW]

end Erdos408.OneSided
