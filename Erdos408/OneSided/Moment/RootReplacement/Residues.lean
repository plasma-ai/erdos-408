import Erdos408.OneSided.Moment.Reindex
import Erdos408.OneSided.Moment.RootReplacement.Lines

/-!
# Root equidistribution for functions of the lines

RR4 of `blueprint/one_sided_type_ii.md` §15, combined with RR5. The integer roots of a box
are the primitive `(u, v)` with `u/U ∈ [a₁, b₁)`, `v/V ∈ [a₂, b₂)` and `c/u ∈ [a₃, b₃)`,
`c = rootC u v` (`boxRoots`). For a function `G` of the lines at a set `P` of band primes,
`S = ∏_{p ∈ P} p`,

`|∑_{P₀ ∈ box} G(ℓ(P₀)) - c₂ U V |box| 𝔼_ℓ G| ≤ ‖G‖_∞ S⁶ · C₀ U V min(U, V)^{-1/5}`.

The lines `ℓ(P₀)_p = [(c, -u)]_p` are the kernel lines of the root matrix `g = (u c; v d)`
modulo `S`. Sort the roots by `g mod S ∈ SL₂(ℤ/S)` and apply `abs_rootCount_sub_le` to each
class: the main terms add up to `c₂ U V |box|` times the average over `SL₂(ℤ/S)`, which is the
independent line average by RR5; the errors add up to at most `|SL₂(ℤ/S)| ≤ S⁴` times one
root-count error.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

/-- The integer roots of a box: the primitive `(u, v)` with `u/U ∈ [a₁, b₁)`,
`v/V ∈ [a₂, b₂)` and `c/u ∈ [a₃, b₃)`, the set counted by `rootCount`. -/
def boxRoots (U V a₁ b₁ a₂ b₂ a₃ b₃ : ℝ) : Finset (ℕ × ℕ) :=
  (Icc ⌈a₁ * U⌉₊ ⌊b₁ * U⌋₊ ×ˢ Icc ⌈a₂ * V⌉₊ ⌊b₂ * V⌋₊).filter fun P =>
    Nat.Coprime P.1 P.2 ∧ (P.1 : ℝ) < b₁ * U ∧ (P.2 : ℝ) < b₂ * V ∧
      a₃ ≤ (rootC P.1 P.2 : ℝ) / P.1 ∧ (rootC P.1 P.2 : ℝ) / P.1 < b₃

/-- Root equidistribution with the constant `C₀`: for every box of `[1, 16] × [1, 2] × [0, 1]`
at scales `U, V ≥ 2`, and every function `G` of the lines at a set `P` of band primes,
bounded by `M`, the sum of `G(ℓ(P₀))` over the roots of the box is
`c₂ U V |box| 𝔼_ℓ G` up to `M S⁶ C₀ U V min(U, V)^{-1/5}`, `S = ∏_{p ∈ P} p`. -/
def RootEquidist (K : ℕ) (C₀ : ℝ) : Prop :=
  ∀ (x : ℝ) (d : Data K) (U V : ℝ), 2 ≤ U → 2 ≤ V →
    ∀ a₁ b₁ a₂ b₂ a₃ b₃ : ℝ, 1 ≤ a₁ → a₁ ≤ b₁ → b₁ ≤ 16 → 1 ≤ a₂ → a₂ ≤ b₂ → b₂ ≤ 2 →
      0 ≤ a₃ → a₃ ≤ b₃ → b₃ ≤ 1 →
    ∀ P : Finset ℕ, P ⊆ bandPrimes x d → ∀ (G : (ℕ → ℕ) → ℂ) (M : ℝ),
      (∀ ℓ ℓ' : ℕ → ℕ, (∀ p ∈ P, ℓ p = ℓ' p) → G ℓ = G ℓ') → (∀ ℓ, ‖G ℓ‖ ≤ M) →
      ‖∑ P₀ ∈ boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃, G (rootLines P₀) -
          ((primitiveDensity * U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) : ℝ) : ℂ) *
            lineAverage x d G‖ ≤
        M * (∏ p ∈ P, (p : ℝ)) ^ 6 * (C₀ * U * V * min U V ^ (-(1 / 5 : ℝ)))

/-- The line `[z]_p` depends on `z` only modulo `p`: for `p ∣ S`, the lines of the residues
`(c, -u) mod S` and of `(c, -u)` agree. -/
theorem lineOf_val_eq {S p : ℕ} [NeZero S] (hp : p ∣ S) (u c : ℕ) :
    lineOf p ((((c : ZMod S).val : ℕ) : ℤ), -(((u : ZMod S).val : ℕ) : ℤ)) =
      lineOf p ((c : ℤ), -(u : ℤ)) := by
  simp only [lineOf, Int.cast_natCast, Int.cast_neg]
  simp only [ZMod.natCast_val, ZMod.cast_natCast hp]

/-- `|SL₂(ℤ/S)| ≤ S⁴`. -/
theorem card_SL_le (S : ℕ) [NeZero S] :
    (Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) ≤ (S : ℝ) ^ 4 := by
  have h := Fintype.card_le_of_injective _
    (Subtype.val_injective (p := fun A : Matrix (Fin 2) (Fin 2) (ZMod S) => A.det = 1))
  have hcard : Fintype.card (Matrix (Fin 2) (Fin 2) (ZMod S)) = S ^ 4 := by
    rw [Fintype.card_eq_nat_card]
    simp [Matrix, ← pow_mul]
  exact_mod_cast h.trans hcard.le

/-- **RR4 with RR5**: root equidistribution holds with some constant `C₀ ≥ 0`. -/
theorem exists_rootEquidist (K : ℕ) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ RootEquidist K C₀ := by
  obtain ⟨C, hC⟩ := abs_rootCount_sub_le
  refine ⟨max C 0, le_max_right _ _, fun x d U V hU hV a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂
    hb₂ ha₃ hab₃ hb₃ P hP G M hG hM => ?_⟩
  classical
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => by
    obtain ⟨i, -, hi⟩ := mem_biUnion.1 (hP hp)
    exact prime_of_mem_band hi
  set S := ∏ p ∈ P, p with hS
  have : NeZero S := ⟨prod_ne_zero_iff.2 fun p hp => (hPp p hp).ne_zero⟩
  have hSsq : Squarefree S := Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.1
      ((Nat.coprime_primes (hPp p hp) (hPp q hq)).2 hpq))
    fun p hp => (hPp p hp).prime.squarefree
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- step: the root matrix modulo `S`, an element of `SL₂(ℤ/S)` at the roots of the box
  set mat : ℕ × ℕ → Matrix (Fin 2) (Fin 2) (ZMod S) := fun P₀ =>
    !![(P₀.1 : ZMod S), (rootC P₀.1 P₀.2 : ZMod S); (P₀.2 : ZMod S),
      (rootD P₀.1 P₀.2 : ZMod S)]
  set cls : ℕ × ℕ → Matrix.SpecialLinearGroup (Fin 2) (ZMod S) := fun P₀ =>
    if h : (mat P₀).det = 1 then ⟨mat P₀, h⟩ else 1
  have hdet : ∀ P₀ ∈ boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃, (mat P₀).det = 1 := by
    intro P₀ hP₀
    obtain ⟨hbox, hco, -⟩ := mem_filter.1 hP₀
    have h₁ : ⌈a₁ * U⌉₊ ≤ P₀.1 := (mem_Icc.1 (mem_product.1 hbox).1).1
    have h₂ : 0 < ⌈a₁ * U⌉₊ := Nat.ceil_pos.2 (by nlinarith)
    exact RootResidue.det_root_matrix (h₂.trans_le h₁) hco
  have hcls : ∀ P₀ ∈ boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃, (cls P₀).1 = mat P₀ := fun P₀ hP₀ => by
    simp only [cls, hdet P₀ hP₀, ↓reduceDIte]
  -- step: the lines of a root are the kernel lines of its matrix modulo `S`
  have hlines : ∀ P₀ ∈ boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃,
      G (rootLines P₀) = G (fun p => matLine p (cls P₀).1) := fun P₀ hP₀ =>
    hG _ _ fun p hp => by
      rw [hcls P₀ hP₀, rootLines, matLine, ← lineOf_val_eq (dvd_prod_of_mem (fun p => p) hp)]
      rfl
  -- step: sort the roots by their matrix modulo `S`
  have hsum : ∑ P₀ ∈ boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃, G (rootLines P₀) =
      ∑ g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
        (rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ S g₀ : ℂ) * G (fun p => matLine p g₀.1) := by
    rw [sum_congr rfl hlines, ← sum_fiberwise_of_maps_to (t := univ) (g := cls)
      fun _ _ => mem_univ _]
    refine sum_congr rfl fun g₀ _ => ?_
    rw [sum_congr rfl fun P₀ hP₀ => by rw [(mem_filter.1 hP₀).2], sum_const, nsmul_eq_mul]
    refine congrArg (fun n : ℕ => (n : ℂ) * G (fun p => matLine p g₀.1)) ?_
    rw [rootCount, boxRoots, filter_filter]
    refine congrArg card (filter_congr fun P₀ hP₀ => ?_)
    constructor
    · rintro ⟨hQ, hg⟩
      have hP₀' : P₀ ∈ boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃ := mem_filter.2 ⟨hP₀, hQ⟩
      exact ⟨hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2.1, hQ.2.2.2.2, by rw [← hg, hcls P₀ hP₀']⟩
    · rintro ⟨h₁, h₂, h₃, h₄, h₅, hg⟩
      have hP₀' : P₀ ∈ boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃ :=
        mem_filter.2 ⟨hP₀, h₁, h₂, h₃, h₄, h₅⟩
      exact ⟨⟨h₁, h₂, h₃, h₄, h₅⟩, Subtype.ext ((hcls P₀ hP₀').trans hg)⟩
  -- step: the main term is the average over `SL₂(ℤ/S)`, the independent line average (RR5)
  have hmain := average_matLine_eq_lineAverage x d hP S rfl G hG
  have hdiff : ∑ P₀ ∈ boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃, G (rootLines P₀) -
      ((primitiveDensity * U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) : ℝ) : ℂ) *
        lineAverage x d G =
      ∑ g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
        (((rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ S g₀ : ℝ) -
          primitiveDensity * U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) /
            Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) : ℂ) *
          G (fun p => matLine p g₀.1) := by
    rw [hsum, ← hmain, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun g₀ _ => ?_
    push_cast
    ring
  -- step: one root-count error for each of the `|SL₂(ℤ/S)| ≤ S⁴` classes
  set E := max C 0 * U * V * min U V ^ (-(1 / 5 : ℝ))
  have hE : 0 ≤ E := by
    have : 0 ≤ min U V ^ (-(1 / 5 : ℝ)) := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ max C 0 := le_max_right _ _
    positivity
  have hterm : ∀ g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
      ‖(((rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ S g₀ : ℝ) -
          primitiveDensity * U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) /
            Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) : ℂ) *
          G (fun p => matLine p g₀.1)‖ ≤ (S : ℝ) ^ 2 * E * M := by
    intro g₀
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul ((hC U V hU hV S hSsq g₀ a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂ hb₂ ha₃
      hab₃ hb₃).trans ?_) (hM _) (norm_nonneg _) (by positivity)
    have : 0 ≤ U * V * (S : ℝ) ^ 2 * min U V ^ (-(1 / 5 : ℝ)) := by
      have : 0 ≤ min U V ^ (-(1 / 5 : ℝ)) := Real.rpow_nonneg (by positivity) _
      positivity
    calc C * U * V * (S : ℝ) ^ 2 * min U V ^ (-(1 / 5 : ℝ))
        = C * (U * V * (S : ℝ) ^ 2 * min U V ^ (-(1 / 5 : ℝ))) := by ring
      _ ≤ max C 0 * (U * V * (S : ℝ) ^ 2 * min U V ^ (-(1 / 5 : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = (S : ℝ) ^ 2 * E := by ring
  have hS4 := card_SL_le S
  have hSR : (∏ p ∈ P, (p : ℝ)) = (S : ℝ) := by rw [hS, Nat.cast_prod]
  rw [hdiff, hSR]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun g₀ _ => hterm g₀).trans ?_)
  rw [sum_const, card_univ, nsmul_eq_mul]
  have hEM : 0 ≤ E * M := mul_nonneg hE hM0
  have hS2 : 0 ≤ (S : ℝ) ^ 2 := by positivity
  calc (Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) * ((S : ℝ) ^ 2 * E * M)
      = (Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) * (S : ℝ) ^ 2 *
          (E * M) := by ring
    _ ≤ (S : ℝ) ^ 4 * (S : ℝ) ^ 2 * (E * M) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS4 hS2) hEM
    _ = M * (S : ℝ) ^ 6 * E := by ring

end Erdos408.OneSided
