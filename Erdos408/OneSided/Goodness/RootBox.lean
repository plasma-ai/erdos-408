module

public import Erdos408.OneSided.RootResidue
public import Erdos408.OneSided.Pairing.Endpoint

/-!
# Root ratios in a box under a linear congruence

The counting input of `eventually_badMass_le` (`blueprint/one_sided_type_ii.md` §14). The
root residues (`RootResidue.lean`) count the positions of the box
`[U, 16U] × [V, 2V]` whose root ratio `r = c/u` lies in an interval and whose root matrix
`g = (u c; v d)` has a prescribed residue mod a squarefree `S`.

* For a unimodular pair `(l, m)` over a finite ring `R`, at most `|R|²` matrices of
  `SL₂(R)` have `l u + m c = 0`: the first row is a multiple `s (-m, l)` with `s` a unit,
  and the second row is then fixed by `x d - y v`, where `x l + y m = 1`.
* Summing the root count over these residues, with `c₂ / |SL₂(ℤ/S)| = σ(S)/S³` and
  `|σ(S)| ≤ 2`, gives at most `30 UV |I| / S` up to the root-residue error, for every
  interval `I` (closed intervals by a limit). The positions on the upper faces
  `u = 16U` or `v = 2V` are counted trivially.
* `card_cong_le`: the positions with `G ∣ u` and `a ∣ z c + (k - ⌊z r⌋) u`, for
  squarefree `G a` and `(z, a) = 1`, have at most `90 UV |I| / (G a)` ratios in `I`, up to
  `3|z|` errors. On each piece of `I` where `⌊|z| r⌋` is constant the floor `⌊z r⌋` takes at
  most three values, and for each the condition is a unimodular congruence mod `G a` (CRT).
-/

@[expose] public section

namespace Erdos408.OneSided

open Finset

/-! ### Unimodular congruences in `SL₂` -/

/-- For `x l + y m = 1`, at most `|R|²` matrices of `SL₂(R)` have `l u + m c = 0` in their
first row: `g ↦ (x c - y u, x d - y v)` is injective on them. -/
theorem card_filter_specialLinearGroup_le {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {l m x y : R} (h : x * l + y * m = 1) :
    (univ.filter fun g : Matrix.SpecialLinearGroup (Fin 2) R => l * g 0 0 + m * g 0 1 = 0).card ≤
      Fintype.card R ^ 2 := by
  set f : Matrix.SpecialLinearGroup (Fin 2) R → R × R :=
    fun g => (x * g 0 1 - y * g 0 0, x * g 1 1 - y * g 1 0)
  have hinj : Set.InjOn f
      (univ.filter fun g : Matrix.SpecialLinearGroup (Fin 2) R => l * g 0 0 + m * g 0 1 = 0) := by
    intro g hg g' hg' hf
    have hl : l * g 0 0 + m * g 0 1 = 0 := (mem_filter.1 hg).2
    have hl' : l * g' 0 0 + m * g' 0 1 = 0 := (mem_filter.1 hg').2
    have hs : x * g 0 1 - y * g 0 0 = x * g' 0 1 - y * g' 0 0 := congrArg Prod.fst hf
    have hs' : x * g 1 1 - y * g 1 0 = x * g' 1 1 - y * g' 1 0 := congrArg Prod.snd hf
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      rw [← Matrix.det_fin_two]
      exact g.2
    have hdet' : g' 0 0 * g' 1 1 - g' 0 1 * g' 1 0 = 1 := by
      rw [← Matrix.det_fin_two]
      exact g'.2
    -- the first row is `s (-m, l)` with `s = x c - y u`
    have hu : g 0 0 = g' 0 0 := by
      linear_combination (g' 0 0 - g 0 0) * h + x * hl - x * hl' - m * hs
    have hc : g 0 1 = g' 0 1 := by
      linear_combination (g' 0 1 - g 0 1) * h + y * hl - y * hl' + l * hs
    -- `s (m d + l v) = -1`, so `m d + l v` is fixed by the first row
    have hS : (x * g 0 1 - y * g 0 0) * (m * g 1 1 + l * g 1 0) = -1 := by
      linear_combination (-(g 1 1 * g 0 0) + g 1 0 * g 0 1) * h +
        (g 1 1 * x - g 1 0 * y) * hl - hdet
    have hS' : (x * g 0 1 - y * g 0 0) * (m * g' 1 1 + l * g' 1 0) = -1 := by
      rw [hu, hc]
      linear_combination (-(g' 1 1 * g' 0 0) + g' 1 0 * g' 0 1) * h +
        (g' 1 1 * x - g' 1 0 * y) * hl' - hdet'
    have hT : m * (g 1 1 - g' 1 1) + l * (g 1 0 - g' 1 0) = 0 := by
      linear_combination -(m * g 1 1 + l * g 1 0) * (hS - hS') +
        (m * (g 1 1 - g' 1 1) + l * (g 1 0 - g' 1 0)) * hS
    have hv : g 1 0 = g' 1 0 := by
      linear_combination -(g 1 0 - g' 1 0) * h + x * hT - m * hs'
    have hd : g 1 1 = g' 1 1 := by
      linear_combination -(g 1 1 - g' 1 1) * h + y * hT + l * hs'
    ext i j
    fin_cases i <;> fin_cases j
    · exact hu
    · exact hc
    · exact hv
    · exact hd
  calc (univ.filter fun g : Matrix.SpecialLinearGroup (Fin 2) R =>
        l * g 0 0 + m * g 0 1 = 0).card
      ≤ (univ : Finset (R × R)).card :=
        card_le_card_of_injOn f (fun _ _ => mem_coe.2 (mem_univ _)) hinj
    _ = Fintype.card R ^ 2 := by rw [card_univ, Fintype.card_prod, sq]

/-! ### Root ratios in the box -/

/-- The box `[U, 16U] × [V, 2V]` of primitive positions. -/
noncomputable def rootBox (U V : ℝ) : Finset (ℕ × ℕ) :=
  ((Icc ⌈U⌉₊ ⌊16 * U⌋₊) ×ˢ (Icc ⌈V⌉₊ ⌊2 * V⌋₊)).filter fun P => Nat.Coprime P.1 P.2

/-- The positions are the box at `U = d₀ Y H_m`, `V = H_n`. -/
theorem positions_eq_rootBox {K : ℕ} (d : Data K) (Y d₀ : ℝ) :
    positions d Y d₀ = rootBox (d₀ * Y * d.Hm) d.Hn :=
  rfl

/-- The root ratio is `c / u` with `c = rootC u v`. -/
theorem rootRatio_eq (P : ℕ × ℕ) : rootRatio P = (rootC P.1 P.2 : ℝ) / P.1 :=
  rfl

/-- `r ≥ 0`. -/
theorem rootRatio_nonneg (P : ℕ × ℕ) : 0 ≤ rootRatio P := by
  rw [rootRatio_eq]
  positivity

/-- `r < 1` for `u > 0`, since `c < u`. -/
theorem rootRatio_lt_one {P : ℕ × ℕ} (hP : 0 < P.1) : rootRatio P < 1 := by
  rw [rootRatio_eq, div_lt_one (by exact_mod_cast hP)]
  exact_mod_cast RootResidue.rootC_lt hP P.2

/-- `|σ(S)| ≤ 2`, from the tail bound at `K = 1`. -/
theorem abs_coprimeDensity_le (S : ℕ) : |RootResidue.coprimeDensity S| ≤ 2 := by
  have h := RootResidue.abs_coprimeDensity_sub_le S one_pos
  simpa [RootResidue.densityTerm] using h

/-- A position of the box has `U ≤ u ≤ 16U` and `V ≤ v ≤ 2V`, and is primitive. -/
theorem mem_rootBox_bounds {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) {P : ℕ × ℕ}
    (hP : P ∈ rootBox U V) :
    U ≤ P.1 ∧ (P.1 : ℝ) ≤ 16 * U ∧ V ≤ P.2 ∧ (P.2 : ℝ) ≤ 2 * V ∧ Nat.Coprime P.1 P.2 := by
  unfold rootBox at hP
  rw [mem_filter, mem_product, mem_Icc, mem_Icc] at hP
  exact ⟨Nat.ceil_le.1 hP.1.1.1, (Nat.le_floor_iff (by positivity)).1 hP.1.1.2,
    Nat.ceil_le.1 hP.1.2.1, (Nat.le_floor_iff (by positivity)).1 hP.1.2.2, hP.2⟩

/-- The positions of the box on the upper faces `u = 16U` or `v = 2V` number at most
`16U + V + 2`. -/
theorem card_rootBox_face_le {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (#{P ∈ rootBox U V | ¬ ((P.1 : ℝ) < 16 * U ∧ (P.2 : ℝ) < 2 * V)} : ℝ) ≤
      16 * U + V + 2 := by
  have hsub : {P ∈ rootBox U V | ¬ ((P.1 : ℝ) < 16 * U ∧ (P.2 : ℝ) < 2 * V)} ⊆
      ({⌊16 * U⌋₊} ×ˢ Icc ⌈V⌉₊ ⌊2 * V⌋₊) ∪ (Icc ⌈U⌉₊ ⌊16 * U⌋₊ ×ˢ {⌊2 * V⌋₊}) := by
    intro P hP
    rw [mem_filter] at hP
    obtain ⟨hbox, hface⟩ := hP
    have hmem := (mem_filter.1 hbox).1
    rw [mem_product, mem_Icc, mem_Icc] at hmem
    rw [not_and_or, not_lt, not_lt] at hface
    rw [mem_union, mem_product, mem_product, mem_singleton, mem_singleton, mem_Icc, mem_Icc]
    rcases hface with h | h
    · refine Or.inl ⟨le_antisymm hmem.1.2 (Nat.floor_le_of_le h), hmem.2⟩
    · refine Or.inr ⟨hmem.1, le_antisymm hmem.2.2 (Nat.floor_le_of_le h)⟩
  have hu := card_Icc_ceil_floor_le hU (by linarith : U ≤ 16 * U)
  have hv := card_Icc_ceil_floor_le hV (by linarith : V ≤ 2 * V)
  calc (#{P ∈ rootBox U V | ¬ ((P.1 : ℝ) < 16 * U ∧ (P.2 : ℝ) < 2 * V)} : ℝ)
      ≤ ((({⌊16 * U⌋₊} ×ˢ Icc ⌈V⌉₊ ⌊2 * V⌋₊) ∪
          (Icc ⌈U⌉₊ ⌊16 * U⌋₊ ×ˢ {⌊2 * V⌋₊})).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ((Icc ⌈V⌉₊ ⌊2 * V⌋₊).card : ℝ) + (Icc ⌈U⌉₊ ⌊16 * U⌋₊).card := by
        have := card_union_le ({⌊16 * U⌋₊} ×ˢ Icc ⌈V⌉₊ ⌊2 * V⌋₊)
          (Icc ⌈U⌉₊ ⌊16 * U⌋₊ ×ˢ {⌊2 * V⌋₊})
        rw [card_product, card_product, card_singleton, card_singleton, one_mul,
          mul_one] at this
        exact_mod_cast this
    _ ≤ 16 * U + V + 2 := by linarith

/-- The root ratios of the box in `[α, β)` whose first row satisfies a unimodular congruence
`l u + m c = 0` mod `S` number at most `30 UV (β - α)/S` up to the root-residue error and
the faces. -/
theorem exists_card_rootBox_lt_le : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ U V : ℝ, 2 ≤ U → 2 ≤ V →
    ∀ (S : ℕ) [NeZero S], Squarefree S → ∀ l m x y : ZMod S, x * l + y * m = 1 →
    ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 1 →
      (#{P ∈ rootBox U V | l * P.1 + m * rootC P.1 P.2 = 0 ∧ α ≤ rootRatio P ∧
          rootRatio P < β} : ℝ) ≤
        30 * U * V * (β - α) / S + C₀ * U * V * (S : ℝ) ^ 4 * min U V ^ (-(1 / 5 : ℝ)) +
          (16 * U + V + 2) := by
  obtain ⟨C, hC⟩ := abs_rootCount_sub_le
  refine ⟨max C 0, le_max_right _ _, fun U V hU hV S _ hS l m x y hxy α β hα hαβ hβ => ?_⟩
  set Γ := univ.filter fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) =>
    l * g 0 0 + m * g 0 1 = 0
  set E := C * U * V * (S : ℝ) ^ 2 * min U V ^ (-(1 / 5 : ℝ))
  set n := (Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)
  have hn : 0 < n := Nat.cast_pos.2 Fintype.card_pos
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast NeZero.one_le
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < V := by linarith
  have hm0 : 0 ≤ min U V ^ (-(1 / 5 : ℝ)) := by positivity
  -- the root matrix of a primitive position
  set M : ℕ × ℕ → Matrix (Fin 2) (Fin 2) (ZMod S) := fun P =>
    !![(P.1 : ZMod S), (rootC P.1 P.2 : ZMod S); (P.2 : ZMod S), (rootD P.1 P.2 : ZMod S)]
  set g : ℕ × ℕ → Matrix.SpecialLinearGroup (Fin 2) (ZMod S) := fun P =>
    if h : (M P).det = 1 then ⟨M P, h⟩ else 1
  set F := {P ∈ rootBox U V | l * P.1 + m * rootC P.1 P.2 = 0 ∧ α ≤ rootRatio P ∧
    rootRatio P < β}
  set R : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) → Finset (ℕ × ℕ) := fun g₀ =>
    (Icc ⌈1 * U⌉₊ ⌊16 * U⌋₊ ×ˢ Icc ⌈1 * V⌉₊ ⌊2 * V⌋₊).filter fun P =>
      Nat.Coprime P.1 P.2 ∧ (P.1 : ℝ) < 16 * U ∧ (P.2 : ℝ) < 2 * V ∧
        α ≤ (rootC P.1 P.2 : ℝ) / P.1 ∧ (rootC P.1 P.2 : ℝ) / P.1 < β ∧
        !![(P.1 : ZMod S), (rootC P.1 P.2 : ZMod S); (P.2 : ZMod S), (rootD P.1 P.2 : ZMod S)] =
          (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S))
  have hR : ∀ g₀, (R g₀).card = rootCount U V 1 16 1 2 α β S g₀ := fun g₀ => rfl
  -- off the faces, every position lies over its root matrix
  have hsub : F ⊆ Γ.biUnion R ∪
      {P ∈ rootBox U V | ¬ ((P.1 : ℝ) < 16 * U ∧ (P.2 : ℝ) < 2 * V)} := by
    intro P hP
    rw [mem_filter] at hP
    obtain ⟨hbox, hcong, hα', hβ'⟩ := hP
    by_cases hface : (P.1 : ℝ) < 16 * U ∧ (P.2 : ℝ) < 2 * V
    · refine mem_union_left _ ?_
      have hmem := (mem_filter.1 hbox).1
      have hcop := (mem_filter.1 hbox).2
      have hP1 : 0 < P.1 := (Nat.ceil_pos.2 hU0).trans_le (mem_Icc.1 (mem_product.1 hmem).1).1
      have hdet : (M P).det = 1 := RootResidue.det_root_matrix hP1 hcop
      have hg : (g P : Matrix (Fin 2) (Fin 2) (ZMod S)) = M P := by
        simp only [g, hdet, ↓reduceDIte]
      refine mem_biUnion.2 ⟨g P, mem_filter.2 ⟨mem_univ _, ?_⟩, ?_⟩
      · rw [hg]
        simpa [M] using hcong
      · refine mem_filter.2 ⟨by simpa only [one_mul] using hmem, hcop, hface.1, hface.2, hα',
          hβ', ?_⟩
        rw [hg]
    · exact mem_union_right _ (mem_filter.2 ⟨hbox, hface⟩)
  -- each root count is at most `30 UV (β - α)/S³ + E`
  have hcount : ∀ g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
      (rootCount U V 1 16 1 2 α β S g₀ : ℝ) ≤
        30 * U * V * (β - α) / (S : ℝ) ^ 3 + max C 0 * U * V * (S : ℝ) ^ 2 *
          min U V ^ (-(1 / 5 : ℝ)) := by
    intro g₀
    have h := hC U V hU hV S hS g₀ 1 16 1 2 α β le_rfl (by norm_num) le_rfl le_rfl
      (by norm_num) le_rfl hα hαβ hβ
    have hdens := RootResidue.coprimeDensity_div_eq S hS
    have hmain : |primitiveDensity * U * V * (16 - 1) * (2 - 1) * (β - α) / n| ≤
        30 * U * V * (β - α) / (S : ℝ) ^ 3 := by
      have he : primitiveDensity * U * V * (16 - 1) * (2 - 1) * (β - α) / n =
          primitiveDensity / n * (15 * U * V * (β - α)) := by ring
      have hβα : 0 ≤ β - α := by linarith
      rw [he, ← hdens, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (S : ℝ) ^ 3),
        abs_of_nonneg (by positivity : 0 ≤ 15 * U * V * (β - α))]
      have hσ := abs_coprimeDensity_le S
      calc |RootResidue.coprimeDensity S| / (S : ℝ) ^ 3 * (15 * U * V * (β - α))
          ≤ 2 / (S : ℝ) ^ 3 * (15 * U * V * (β - α)) := by
            gcongr
        _ = 30 * U * V * (β - α) / (S : ℝ) ^ 3 := by ring
    have hE : E ≤ max C 0 * U * V * (S : ℝ) ^ 2 * min U V ^ (-(1 / 5 : ℝ)) := by
      have : 0 ≤ U * V * (S : ℝ) ^ 2 * min U V ^ (-(1 / 5 : ℝ)) := by positivity
      simp only [E]
      nlinarith [le_max_left C 0]
    rw [abs_le] at h
    have := (abs_le.1 hmain).2
    linarith [h.2]
  have hΓ : (Γ.card : ℝ) ≤ (S : ℝ) ^ 2 := by
    have := card_filter_specialLinearGroup_le hxy
    rw [ZMod.card] at this
    exact_mod_cast this
  have hface := card_rootBox_face_le hU0.le hV0.le
  calc (F.card : ℝ)
      ≤ ((Γ.biUnion R).card : ℝ) +
          #{P ∈ rootBox U V | ¬ ((P.1 : ℝ) < 16 * U ∧ (P.2 : ℝ) < 2 * V)} := by
        exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    _ ≤ ∑ g₀ ∈ Γ, (30 * U * V * (β - α) / (S : ℝ) ^ 3 + max C 0 * U * V * (S : ℝ) ^ 2 *
          min U V ^ (-(1 / 5 : ℝ))) + (16 * U + V + 2) := by
        gcongr
        calc ((Γ.biUnion R).card : ℝ) ≤ ∑ g₀ ∈ Γ, ((R g₀).card : ℝ) := by
              exact_mod_cast card_biUnion_le
          _ ≤ _ := sum_le_sum fun g₀ _ => by rw [hR]; exact hcount g₀
    _ = Γ.card * (30 * U * V * (β - α) / (S : ℝ) ^ 3 + max C 0 * U * V * (S : ℝ) ^ 2 *
          min U V ^ (-(1 / 5 : ℝ))) + (16 * U + V + 2) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (S : ℝ) ^ 2 * (30 * U * V * (β - α) / (S : ℝ) ^ 3 + max C 0 * U * V * (S : ℝ) ^ 2 *
          min U V ^ (-(1 / 5 : ℝ))) + (16 * U + V + 2) := by
        gcongr
    _ = 30 * U * V * (β - α) / S + max C 0 * U * V * (S : ℝ) ^ 4 *
          min U V ^ (-(1 / 5 : ℝ)) + (16 * U + V + 2) := by
        field_simp

/-- The closed version of `exists_card_rootBox_lt_le`: `[α, β] ⊆ [α, β + δ)` for every
`δ > 0`, and the ratios are below one. -/
theorem exists_card_rootBox_le : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ U V : ℝ, 2 ≤ U → 2 ≤ V →
    ∀ (S : ℕ) [NeZero S], Squarefree S → ∀ l m x y : ZMod S, x * l + y * m = 1 →
    ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 1 →
      (#{P ∈ rootBox U V | l * P.1 + m * rootC P.1 P.2 = 0 ∧ α ≤ rootRatio P ∧
          rootRatio P ≤ β} : ℝ) ≤
        30 * U * V * (β - α) / S + C₀ * U * V * (S : ℝ) ^ 4 * min U V ^ (-(1 / 5 : ℝ)) +
          (16 * U + V + 2) := by
  obtain ⟨C₀, hC₀, h⟩ := exists_card_rootBox_lt_le
  refine ⟨C₀, hC₀, fun U V hU hV S _ hS l m x y hxy α β hα hαβ hβ => ?_⟩
  have hU0 : 0 < U := by linarith
  have hS0 : (0 : ℝ) < S := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε * S / (30 * U * V)
  have hδ : 0 < δ := by positivity
  set β' := min (β + δ) 1
  have hβ' : β ≤ β' := le_min (by linarith) hβ
  -- the closed interval lies in `[α, β')`
  have hsub : {P ∈ rootBox U V | l * P.1 + m * rootC P.1 P.2 = 0 ∧ α ≤ rootRatio P ∧
      rootRatio P ≤ β} ⊆ {P ∈ rootBox U V | l * P.1 + m * rootC P.1 P.2 = 0 ∧
        α ≤ rootRatio P ∧ rootRatio P < β'} := by
    intro P hP
    rw [mem_filter] at hP ⊢
    obtain ⟨hbox, hcong, h₁, h₂⟩ := hP
    have hP1 : 0 < P.1 := by
      have := (mem_rootBox_bounds hU0.le (by linarith) hbox).1
      exact_mod_cast hU0.trans_le this
    exact ⟨hbox, hcong, h₁, lt_min (by linarith) (rootRatio_lt_one hP1)⟩
  have hδε : 30 * U * V * δ / S = ε := by
    simp only [δ]
    field_simp
  calc (#{P ∈ rootBox U V | l * P.1 + m * rootC P.1 P.2 = 0 ∧ α ≤ rootRatio P ∧
        rootRatio P ≤ β} : ℝ)
      ≤ #{P ∈ rootBox U V | l * P.1 + m * rootC P.1 P.2 = 0 ∧ α ≤ rootRatio P ∧
          rootRatio P < β'} := by exact_mod_cast card_le_card hsub
    _ ≤ 30 * U * V * (β' - α) / S + C₀ * U * V * (S : ℝ) ^ 4 * min U V ^ (-(1 / 5 : ℝ)) +
          (16 * U + V + 2) :=
        h U V hU hV S hS l m x y hxy α β' hα (hαβ.trans hβ') (min_le_right _ _)
    _ ≤ 30 * U * V * (β + δ - α) / S + C₀ * U * V * (S : ℝ) ^ 4 * min U V ^ (-(1 / 5 : ℝ)) +
          (16 * U + V + 2) := by
        gcongr
        exact min_le_left _ _
    _ = 30 * U * V * (β - α) / S + C₀ * U * V * (S : ℝ) ^ 4 * min U V ^ (-(1 / 5 : ℝ)) +
          (16 * U + V + 2) + 30 * U * V * δ / S := by ring
    _ = _ := by rw [hδε]

/-! ### The congruences of a joint count -/

/-- CRT: for coprime `G, a` and `(z, a) = 1`, the conditions `G ∣ u` and `a ∣ z c + z₁ u`
imply a unimodular congruence `l u + m c = 0` mod `G a`. With `e G + f a = 1`, take
`l = f a + z₁ e G`, `m = z e G`, `x = f a` and `y = z' e G`, where `z' z ≡ 1 (mod a)`. -/
theorem exists_unimodular_of_dvd {G a : ℕ} (hGa : Nat.Coprime G a) {z : ℤ}
    (hz : IsCoprime z (a : ℤ)) (z₁ : ℤ) :
    ∃ l m x y : ZMod (G * a), x * l + y * m = 1 ∧ ∀ u c : ℕ, (G : ℤ) ∣ u →
      (a : ℤ) ∣ z * c + z₁ * u → l * u + m * c = 0 := by
  obtain ⟨e, f, hef⟩ := Nat.isCoprime_iff_coprime.2 hGa
  obtain ⟨z', w, hzw⟩ := hz
  have hGa0 : (G : ZMod (G * a)) * (a : ZMod (G * a)) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_self]
  have h₁ : (e : ZMod (G * a)) * G + f * a = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod (G * a)) hef
    push_cast at this
    exact this
  have h₂ : (z' : ZMod (G * a)) * z + w * a = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod (G * a)) hzw
    push_cast at this
    exact this
  refine ⟨f * a + z₁ * e * G, z * e * G, f * a, z' * e * G, ?_, fun u c hu hc => ?_⟩
  · linear_combination (e * G + f * a + 1 : ZMod (G * a)) * h₁ +
      (z₁ * e * f - 2 * e * f - w * e ^ 2 * G : ZMod (G * a)) * hGa0 +
      (e ^ 2 * G ^ 2 : ZMod (G * a)) * h₂
  · obtain ⟨t, ht⟩ := hu
    obtain ⟨t', ht'⟩ := hc
    have hu' : (u : ZMod (G * a)) = G * t := by
      have := congrArg (Int.cast : ℤ → ZMod (G * a)) ht
      push_cast at this
      exact this
    have hc' : (z : ZMod (G * a)) * c + z₁ * u = a * t' := by
      have := congrArg (Int.cast : ℤ → ZMod (G * a)) ht'
      push_cast at this
      exact this
    linear_combination (f * a : ZMod (G * a)) * hu' + (e * G : ZMod (G * a)) * hc' +
      (f * t + e * t' : ZMod (G * a)) * hGa0

/-- `⌊z r⌋ ∈ {j, -j, -j - 1}` for `j = ⌊|z| r⌋` and `r ≥ 0`. -/
theorem floor_mul_mem {z : ℤ} {r : ℝ} (hr : 0 ≤ r) :
    ⌊(z : ℝ) * r⌋ ∈ ({(⌊(z.natAbs : ℝ) * r⌋₊ : ℤ), -(⌊(z.natAbs : ℝ) * r⌋₊ : ℤ),
      -(⌊(z.natAbs : ℝ) * r⌋₊ : ℤ) - 1} : Finset ℤ) := by
  have habs : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hj : (⌊(z.natAbs : ℝ) * r⌋₊ : ℤ) = ⌊(z.natAbs : ℝ) * r⌋ :=
    Int.natCast_floor_eq_floor (by positivity)
  rw [hj, habs, mem_insert, mem_insert, mem_singleton]
  rcases le_total 0 z with hz | hz
  · left
    rw [abs_of_nonneg (by exact_mod_cast hz)]
  · right
    rw [abs_of_nonpos (by exact_mod_cast hz), neg_mul, Int.floor_neg, neg_neg]
    have h₁ := Int.floor_le_ceil ((z : ℝ) * r)
    have h₂ := Int.ceil_le_floor_add_one ((z : ℝ) * r)
    omega

/-- **Joint congruence count.** For squarefree `G a`, `z ≠ 0` with `(z, a) = 1` and any `k`,
the positions of the box with `G ∣ u` and `a ∣ z c + (k - ⌊z r⌋) u` have at most
`90 UV (β - α)/(G a) + 3 |z| E` ratios in `[α, β]`, where `E` is the error of
`exists_card_rootBox_le` at `S = G a`. -/
theorem exists_card_cong_le : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ U V : ℝ, 2 ≤ U → 2 ≤ V →
    ∀ G a : ℕ, Squarefree (G * a) → ∀ z : ℤ, z ≠ 0 → IsCoprime z (a : ℤ) → ∀ k : ℤ,
    ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 1 →
      (#{P ∈ rootBox U V | (G : ℤ) ∣ P.1 ∧
          (a : ℤ) ∣ z * rootC P.1 P.2 + (k - ⌊(z : ℝ) * rootRatio P⌋) * P.1 ∧
          α ≤ rootRatio P ∧ rootRatio P ≤ β} : ℝ) ≤
        90 * U * V * (β - α) / ((G : ℝ) * a) + 3 * |(z : ℝ)| *
          (C₀ * U * V * ((G : ℝ) * a) ^ 4 * min U V ^ (-(1 / 5 : ℝ)) + (16 * U + V + 2)) := by
  obtain ⟨C₀, hC₀, h⟩ := exists_card_rootBox_le
  refine ⟨C₀, hC₀, fun U V hU hV G a hS z hz hza k α β hα hαβ hβ => ?_⟩
  have : NeZero (G * a) := ⟨hS.ne_zero⟩
  have hGa : Nat.Coprime G a := (Nat.squarefree_mul_iff.1 hS).1
  have hU0 : 0 < U := by linarith
  set N := z.natAbs
  have hN : 0 < N := Int.natAbs_pos.2 hz
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNz : (N : ℝ) = |(z : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  set E := C₀ * U * V * ((G : ℝ) * a) ^ 4 * min U V ^ (-(1 / 5 : ℝ)) + (16 * U + V + 2)
  -- the pieces `[f j, f (j + 1)]` of `[α, β]`
  set f : ℕ → ℝ := fun j => max α (min β ((j : ℝ) / N))
  have hf0 : ∀ j, 0 ≤ f j := fun j => hα.trans (le_max_left _ _)
  have hf1 : ∀ j, f j ≤ 1 := fun j => max_le (hαβ.trans hβ) ((min_le_left _ _).trans hβ)
  have hmono : ∀ j, f j ≤ f (j + 1) := by
    intro j
    refine max_le_max le_rfl (min_le_min le_rfl ?_)
    gcongr
    linarith
  set piece : ℤ → ℕ → Finset (ℕ × ℕ) := fun n j =>
    {P ∈ rootBox U V | (G : ℤ) ∣ P.1 ∧ (a : ℤ) ∣ z * rootC P.1 P.2 + (k - n) * P.1 ∧
      f j ≤ rootRatio P ∧ rootRatio P ≤ f (j + 1)}
  -- each piece is a unimodular congruence count
  have hpiece : ∀ n j, ((piece n j).card : ℝ) ≤
      30 * U * V * (f (j + 1) - f j) / ((G : ℝ) * a) + E := by
    intro n j
    obtain ⟨l, m, x, y, hxy, hcong⟩ := exists_unimodular_of_dvd hGa hza (k - n)
    have hsub : piece n j ⊆ {P ∈ rootBox U V | l * P.1 + m * rootC P.1 P.2 = 0 ∧
        f j ≤ rootRatio P ∧ rootRatio P ≤ f (j + 1)} := by
      intro P hP
      rw [mem_filter] at hP ⊢
      obtain ⟨hbox, hG, ha, h₁, h₂⟩ := hP
      refine ⟨hbox, hcong _ _ hG ?_, h₁, h₂⟩
      rwa [show z * (rootC P.1 P.2 : ℤ) + (k - n) * (P.1 : ℤ) =
        z * (rootC P.1 P.2 : ℕ) + (k - n) * (P.1 : ℕ) by rfl] at ha
    have := h U V hU hV (G * a) hS l m x y hxy (f j) (f (j + 1)) (hf0 j) (hmono j) (hf1 _)
    rw [Nat.cast_mul] at this
    exact (Nat.cast_le.2 (card_le_card hsub)).trans (this.trans_eq (by simp only [E]; ring))
  -- every counted position lies in a piece
  have hsub : {P ∈ rootBox U V | (G : ℤ) ∣ P.1 ∧
      (a : ℤ) ∣ z * rootC P.1 P.2 + (k - ⌊(z : ℝ) * rootRatio P⌋) * P.1 ∧
      α ≤ rootRatio P ∧ rootRatio P ≤ β} ⊆
        (range N).biUnion fun j =>
          ({(j : ℤ), -(j : ℤ), -(j : ℤ) - 1} : Finset ℤ).biUnion fun n => piece n j := by
    intro P hP
    rw [mem_filter] at hP
    obtain ⟨hbox, hG, ha, h₁, h₂⟩ := hP
    have hP1 : 0 < P.1 := by
      have := (mem_rootBox_bounds hU0.le (by linarith) hbox).1
      exact_mod_cast hU0.trans_le this
    set r := rootRatio P
    have hr0 : 0 ≤ r := rootRatio_nonneg P
    have hr1 : r < 1 := rootRatio_lt_one hP1
    set j := ⌊(N : ℝ) * r⌋₊
    have hjle : (j : ℝ) ≤ N * r := Nat.floor_le (by positivity)
    have hjlt : (N : ℝ) * r < j + 1 := Nat.lt_floor_add_one _
    have hjN : j < N := by
      have : (j : ℝ) < N := by nlinarith
      exact_mod_cast this
    refine mem_biUnion.2 ⟨j, mem_range.2 hjN, mem_biUnion.2 ⟨_, floor_mul_mem hr0, ?_⟩⟩
    refine mem_filter.2 ⟨hbox, hG, ha, ?_, ?_⟩
    · refine max_le h₁ ((min_le_right _ _).trans ?_)
      rw [div_le_iff₀ hN0]
      linarith
    · refine le_max_of_le_right (le_min h₂ ?_)
      rw [le_div_iff₀ hN0]
      push_cast
      linarith
  -- the pieces telescope
  have htel : ∑ j ∈ range N, (f (j + 1) - f j) = β - α := by
    rw [sum_range_sub (f := f)]
    simp only [f, Nat.cast_zero, zero_div, div_self hN0.ne']
    rw [min_eq_left hβ, max_eq_right hαβ, min_eq_right (hα.trans hαβ), max_eq_left hα]
  have hE : 0 ≤ E := by positivity
  have hGa0 : (0 : ℝ) < (G : ℝ) * a := by
    have : (0 : ℝ) < ((G * a : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hS.ne_zero
    exact_mod_cast this
  calc (#{P ∈ rootBox U V | (G : ℤ) ∣ P.1 ∧
        (a : ℤ) ∣ z * rootC P.1 P.2 + (k - ⌊(z : ℝ) * rootRatio P⌋) * P.1 ∧
        α ≤ rootRatio P ∧ rootRatio P ≤ β} : ℝ)
      ≤ ∑ j ∈ range N, ∑ n ∈ ({(j : ℤ), -(j : ℤ), -(j : ℤ) - 1} : Finset ℤ),
          ((piece n j).card : ℝ) := by
        refine (Nat.cast_le.2 (card_le_card hsub)).trans ?_
        refine (Nat.cast_le.2 card_biUnion_le).trans ?_
        push_cast
        exact sum_le_sum fun j _ => by exact_mod_cast card_biUnion_le
    _ ≤ ∑ j ∈ range N, 3 * (30 * U * V * (f (j + 1) - f j) / ((G : ℝ) * a) + E) := by
        refine sum_le_sum fun j _ => ?_
        have h3 : (({(j : ℤ), -(j : ℤ), -(j : ℤ) - 1} : Finset ℤ).card : ℝ) ≤ 3 := by
          exact_mod_cast card_le_three
        have hnn : 0 ≤ 30 * U * V * (f (j + 1) - f j) / ((G : ℝ) * a) + E := by
          have := hmono j
          have : 0 ≤ f (j + 1) - f j := by linarith
          positivity
        calc ∑ n ∈ ({(j : ℤ), -(j : ℤ), -(j : ℤ) - 1} : Finset ℤ), ((piece n j).card : ℝ)
            ≤ ∑ _n ∈ ({(j : ℤ), -(j : ℤ), -(j : ℤ) - 1} : Finset ℤ),
                (30 * U * V * (f (j + 1) - f j) / ((G : ℝ) * a) + E) :=
              sum_le_sum fun n _ => hpiece n j
          _ ≤ _ := by
              rw [sum_const, nsmul_eq_mul]
              exact mul_le_mul_of_nonneg_right h3 hnn
    _ = 90 * U * V / ((G : ℝ) * a) * ∑ j ∈ range N, (f (j + 1) - f j) + 3 * N * E := by
        have hj : ∀ j, 3 * (30 * U * V * (f (j + 1) - f j) / ((G : ℝ) * a) + E) =
            90 * U * V / ((G : ℝ) * a) * (f (j + 1) - f j) + 3 * E := fun j => by ring
        rw [sum_congr rfl fun j _ => hj j, sum_add_distrib, ← mul_sum, sum_const, card_range,
          nsmul_eq_mul]
        ring
    _ = _ := by
        rw [htel, hNz]
        ring

end Erdos408.OneSided
