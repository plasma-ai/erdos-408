module

public import Erdos408.OneSided.Moment.RootReplacement.Bonferroni

/-!
# The grid of cubes

Step 3 of the assembly in `blueprint/one_sided_type_ii.md` §15 and the boundary step of §5.4,
for one configuration. The normalized root box `[1, 16] × [1, 2] × [0, 1]` is cut into the
`15 n³` half-open cubes of side `1/n` (`cubeIndices`, `cubeRoots`). Every physical position
lies in exactly one cube, except those on the upper faces `u = 16U` or `v = 2V`
(`edgeRoots`), which number `O(U + V)`.

For an archimedean indicator `A` that is constant on the roots of every cube outside a set
`bad`, the normalized root sum of `A · F` is the Riemann sum `c₂ n⁻³ ∑_Q A(ϱ_Q) 𝔼_ℓ F` up to

* the box estimate (`norm_boxRoots_prod_sub_le`) on the good cubes;
* `4 n⁻³ + C₀ min(U, V)^{-1/5}` on each bad cube, bounded absolutely;
* `(16U + 2V + 2)/(UV)` from the upper faces.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

/-- The indices `(i₁, i₂, i₃) ∈ [0, 15n) × [0, n) × [0, n)` of the cubes. -/
def cubeIndices (n : ℕ) : Finset (ℕ × ℕ × ℕ) := range (15 * n) ×ˢ range n ×ˢ range n

/-- The integer roots of the cube `i`:
`u/U ∈ [1 + i₁/n, 1 + (i₁+1)/n)`, `v/V ∈ [1 + i₂/n, 1 + (i₂+1)/n)`, `c/u ∈ [i₃/n, (i₃+1)/n)`. -/
def cubeRoots (U V : ℝ) (n : ℕ) (i : ℕ × ℕ × ℕ) : Finset (ℕ × ℕ) :=
  boxRoots U V (1 + i.1 / n) (1 + (i.1 + 1) / n) (1 + i.2.1 / n) (1 + (i.2.1 + 1) / n)
    (i.2.2 / n) ((i.2.2 + 1) / n)

/-- The positions on the upper faces `u ≥ 16U` or `v ≥ 2V`, which lie in no cube. -/
def edgeRoots (d : Data K) (Y d₀ : ℝ) : Finset (ℕ × ℕ) :=
  (positions d Y d₀).filter fun P => 16 * (d₀ * Y * d.Hm) ≤ P.1 ∨ 2 * d.Hn ≤ P.2

/-- `⌊t n⌋₊ = k` if and only if `t ∈ [k/n, (k+1)/n)`, for `t ≥ 0`. -/
theorem floor_mul_natCast_eq_iff {t : ℝ} (ht : 0 ≤ t) {n : ℕ} (hn : 0 < n) {k : ℕ} :
    ⌊t * n⌋₊ = k ↔ (k : ℝ) / n ≤ t ∧ t < (k + 1) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.floor_eq_iff (by positivity), div_le_iff₀ hn', lt_div_iff₀ hn']

/-- For `u ≥ U > 0`, `⌊(u/U - 1) n⌋₊ = k` if and only if `u/U ∈ [1 + k/n, 1 + (k+1)/n)`. -/
theorem floor_div_sub_one_mul_eq_iff {U u : ℝ} (hU : 0 < U) (hu : U ≤ u) {n : ℕ} (hn : 0 < n)
    {k : ℕ} : ⌊(u / U - 1) * n⌋₊ = k ↔ (1 + k / n) * U ≤ u ∧ u < (1 + (k + 1) / n) * U := by
  rw [floor_mul_natCast_eq_iff (sub_nonneg.2 ((one_le_div hU).2 hu)) hn, le_sub_iff_add_le,
    sub_lt_iff_lt_add, le_div_iff₀ hU, div_lt_iff₀ hU, add_comm ((k : ℝ) / n) 1,
    add_comm (((k : ℝ) + 1) / n) 1]

/-- The roots of the cube `i` are the primitive `(u, v)` with `u/U`, `v/V` and `c/u` in the
three intervals of the cube. -/
theorem mem_cubeRoots {U V : ℝ} {n : ℕ} {i : ℕ × ℕ × ℕ} {P : ℕ × ℕ} :
    P ∈ cubeRoots U V n i ↔ Nat.Coprime P.1 P.2 ∧
      ((1 + i.1 / n) * U ≤ P.1 ∧ (P.1 : ℝ) < (1 + (i.1 + 1) / n) * U) ∧
      ((1 + i.2.1 / n) * V ≤ P.2 ∧ (P.2 : ℝ) < (1 + (i.2.1 + 1) / n) * V) ∧
      ((i.2.2 : ℝ) / n ≤ (rootC P.1 P.2 : ℝ) / P.1 ∧
        (rootC P.1 P.2 : ℝ) / P.1 < (i.2.2 + 1) / n) := by
  simp only [cubeRoots, boxRoots, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨h₁, -⟩, h₂, -⟩, hc, h₃, h₄, h₅, h₆⟩
    exact ⟨hc, ⟨Nat.ceil_le.1 h₁, h₃⟩, ⟨Nat.ceil_le.1 h₂, h₄⟩, h₅, h₆⟩
  · rintro ⟨hc, ⟨h₁, h₃⟩, ⟨h₂, h₄⟩, h₅, h₆⟩
    exact ⟨⟨⟨Nat.ceil_le.2 h₁, Nat.le_floor h₃.le⟩, Nat.ceil_le.2 h₂, Nat.le_floor h₄.le⟩,
      hc, h₃, h₄, h₅, h₆⟩

/-- The positions off the upper faces are the primitive `(u, v)` with `u ∈ [U, 16U)` and
`v ∈ [V, 2V)`. -/
theorem mem_positions_filter_not (d : Data K) {Y d₀ : ℝ} {P : ℕ × ℕ} :
    P ∈ (positions d Y d₀).filter (fun P => ¬(16 * (d₀ * Y * d.Hm) ≤ P.1 ∨ 2 * d.Hn ≤ P.2)) ↔
      Nat.Coprime P.1 P.2 ∧ (d₀ * Y * d.Hm ≤ P.1 ∧ (P.1 : ℝ) < 16 * (d₀ * Y * d.Hm)) ∧
        (d.Hn ≤ P.2 ∧ (P.2 : ℝ) < 2 * d.Hn) := by
  simp only [positions, mem_filter, mem_product, mem_Icc, not_or, not_le]
  constructor
  · rintro ⟨⟨⟨⟨h₁, -⟩, h₂, -⟩, hc⟩, h₃, h₄⟩
    exact ⟨hc, ⟨Nat.ceil_le.1 h₁, h₃⟩, Nat.ceil_le.1 h₂, h₄⟩
  · rintro ⟨hc, ⟨h₁, h₃⟩, h₂, h₄⟩
    exact ⟨⟨⟨⟨Nat.ceil_le.2 h₁, Nat.le_floor h₃.le⟩, Nat.ceil_le.2 h₂, Nat.le_floor h₄.le⟩, hc⟩,
      h₃, h₄⟩

/-- Every position lies in exactly one cube or on an upper face. -/
theorem sum_positions_eq (d : Data K) {Y d₀ : ℝ} (hU : 0 < d₀ * Y * d.Hm) (hV : 0 < d.Hn)
    {n : ℕ} (hn : 1 ≤ n) (f : ℕ × ℕ → ℂ) :
    ∑ P ∈ positions d Y d₀, f P =
      ∑ i ∈ cubeIndices n, ∑ P ∈ cubeRoots (d₀ * Y * d.Hm) d.Hn n i, f P +
        ∑ P ∈ edgeRoots d Y d₀, f P := by
  classical
  have hn₀ : 0 < n := hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- step: split off the upper faces
  have hsplit : ∑ P ∈ positions d Y d₀, f P =
      ∑ P ∈ (positions d Y d₀).filter
        (fun P => ¬(16 * (d₀ * Y * d.Hm) ≤ P.1 ∨ 2 * d.Hn ≤ P.2)), f P +
        ∑ P ∈ edgeRoots d Y d₀, f P := by
    rw [edgeRoots, add_comm, sum_filter_add_sum_filter_not]
  rw [hsplit]
  congr 1
  -- step: the cube of a position
  set ι : ℕ × ℕ → ℕ × ℕ × ℕ := fun P => (⌊((P.1 : ℝ) / (d₀ * Y * d.Hm) - 1) * n⌋₊,
    ⌊((P.2 : ℝ) / d.Hn - 1) * n⌋₊, ⌊(rootC P.1 P.2 : ℝ) / P.1 * n⌋₊) with hι
  have hιeq : ∀ (P : ℕ × ℕ) (i : ℕ × ℕ × ℕ), d₀ * Y * d.Hm ≤ P.1 → d.Hn ≤ P.2 →
      (ι P = i ↔
        ((1 + i.1 / n) * (d₀ * Y * d.Hm) ≤ P.1 ∧
          (P.1 : ℝ) < (1 + (i.1 + 1) / n) * (d₀ * Y * d.Hm)) ∧
        ((1 + i.2.1 / n) * d.Hn ≤ P.2 ∧ (P.2 : ℝ) < (1 + (i.2.1 + 1) / n) * d.Hn) ∧
        ((i.2.2 : ℝ) / n ≤ (rootC P.1 P.2 : ℝ) / P.1 ∧
          (rootC P.1 P.2 : ℝ) / P.1 < (i.2.2 + 1) / n)) := by
    intro P i hu hv
    obtain ⟨i₁, i₂, i₃⟩ := i
    simp only [hι, Prod.mk.injEq]
    rw [floor_div_sub_one_mul_eq_iff hU hu hn₀, floor_div_sub_one_mul_eq_iff hV hv hn₀,
      floor_mul_natCast_eq_iff (by positivity) hn₀]
  have hmaps : ∀ P ∈ (positions d Y d₀).filter
      (fun P => ¬(16 * (d₀ * Y * d.Hm) ≤ P.1 ∨ 2 * d.Hn ≤ P.2)), ι P ∈ cubeIndices n := by
    intro P hP
    obtain ⟨-, ⟨hu₁, hu₂⟩, hv₁, hv₂⟩ := (mem_positions_filter_not d).1 hP
    have hu₀ : 0 < P.1 := by exact_mod_cast hU.trans_le hu₁
    have h₁ : (P.1 : ℝ) / (d₀ * Y * d.Hm) - 1 < 15 := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hU]
      linarith
    have h₂ : (P.2 : ℝ) / d.Hn - 1 < 1 := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hV]
      linarith
    have h₃ : (rootC P.1 P.2 : ℝ) / P.1 < 1 :=
      (div_lt_one (by exact_mod_cast hu₀)).2 (by exact_mod_cast RootResidue.rootC_lt hu₀ P.2)
    simp only [hι, cubeIndices, mem_product, mem_range]
    refine ⟨(Nat.floor_lt ?_).2 ?_, (Nat.floor_lt ?_).2 ?_, (Nat.floor_lt ?_).2 ?_⟩
    · exact mul_nonneg (sub_nonneg.2 ((one_le_div hU).2 hu₁)) hn'.le
    · push_cast
      exact mul_lt_mul_of_pos_right h₁ hn'
    · exact mul_nonneg (sub_nonneg.2 ((one_le_div hV).2 hv₁)) hn'.le
    · simpa using mul_lt_mul_of_pos_right h₂ hn'
    · positivity
    · simpa using mul_lt_mul_of_pos_right h₃ hn'
  -- step: sort the positions off the upper faces by their cube
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun i hi => sum_congr ?_ fun _ _ => rfl
  simp only [cubeIndices, mem_product, mem_range] at hi
  obtain ⟨hi₁, hi₂, hi₃⟩ := hi
  ext P
  rw [mem_filter, mem_cubeRoots]
  constructor
  · rintro ⟨hP, rfl⟩
    obtain ⟨hc, ⟨hu₁, -⟩, hv₁, -⟩ := (mem_positions_filter_not d).1 hP
    exact ⟨hc, (hιeq P _ hu₁ hv₁).1 rfl⟩
  · rintro ⟨hc, ⟨hu₁, hu₂⟩, ⟨hv₁, hv₂⟩, h₃⟩
    have hb₁ : ((i.1 : ℝ) + 1) / n ≤ 15 := by
      rw [div_le_iff₀ hn']
      exact_mod_cast (show i.1 + 1 ≤ 15 * n by omega)
    have hb₂ : ((i.2.1 : ℝ) + 1) / n ≤ 1 := by
      rw [div_le_iff₀ hn']
      exact_mod_cast (show i.2.1 + 1 ≤ 1 * n by omega)
    have hu : d₀ * Y * d.Hm ≤ P.1 :=
      le_trans (le_mul_of_one_le_left hU.le (le_add_of_nonneg_right (by positivity))) hu₁
    have hv : d.Hn ≤ P.2 :=
      le_trans (le_mul_of_one_le_left hV.le (le_add_of_nonneg_right (by positivity))) hv₁
    refine ⟨(mem_positions_filter_not d).2 ⟨hc, ⟨hu, ?_⟩, hv, ?_⟩,
      (hιeq P i hu hv).2 ⟨⟨hu₁, hu₂⟩, ⟨hv₁, hv₂⟩, h₃⟩⟩
    · calc (P.1 : ℝ) < (1 + (i.1 + 1) / n) * (d₀ * Y * d.Hm) := hu₂
        _ ≤ 16 * (d₀ * Y * d.Hm) := mul_le_mul_of_nonneg_right (by linarith) hU.le
    · calc (P.2 : ℝ) < (1 + (i.2.1 + 1) / n) * d.Hn := hv₂
        _ ≤ 2 * d.Hn := mul_le_mul_of_nonneg_right (by linarith) hV.le

/-- The upper faces carry at most `16U + 2V + 2` positions. -/
theorem card_edgeRoots_le (d : Data K) {Y d₀ : ℝ} (hU : 0 < d₀ * Y * d.Hm) (hV : 0 < d.Hn) :
    ((edgeRoots d Y d₀).card : ℝ) ≤ 16 * (d₀ * Y * d.Hm) + 2 * d.Hn + 2 := by
  classical
  set U := d₀ * Y * d.Hm with hUdef
  set V := d.Hn with hVdef
  -- step: the upper faces lie on two segments
  have hsub : edgeRoots d Y d₀ ⊆ ({⌊16 * U⌋₊} ×ˢ Icc ⌈V⌉₊ ⌊2 * V⌋₊) ∪
      (Icc ⌈U⌉₊ ⌊16 * U⌋₊ ×ˢ {⌊2 * V⌋₊}) := by
    intro P hP
    simp only [edgeRoots, positions, mem_filter, mem_product, mem_Icc] at hP
    obtain ⟨⟨⟨⟨hu₁, hu₂⟩, hv₁, hv₂⟩, -⟩, hedge⟩ := hP
    simp only [mem_union, mem_product, mem_singleton, mem_Icc]
    rcases hedge with h | h
    · refine Or.inl ⟨le_antisymm hu₂ ?_, hv₁, hv₂⟩
      exact_mod_cast (Nat.floor_le (by positivity)).trans h
    · refine Or.inr ⟨⟨hu₁, hu₂⟩, le_antisymm hv₂ ?_⟩
      exact_mod_cast (Nat.floor_le (by positivity)).trans h
  -- step: count the two segments
  have hIcc : ∀ {a b : ℝ}, a ≤ b → 0 ≤ b → ((Icc ⌈a⌉₊ ⌊b⌋₊).card : ℝ) ≤ b + 1 - a := by
    intro a b hab hb
    rw [Nat.card_Icc]
    rcases le_or_gt ⌈a⌉₊ (⌊b⌋₊ + 1) with h | h
    · rw [Nat.cast_sub h]
      push_cast
      linarith [Nat.floor_le hb, Nat.le_ceil a]
    · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
      linarith
  have hcard := card_le_card hsub
  have hcard' : ((edgeRoots d Y d₀).card : ℝ) ≤
      ((Icc ⌈V⌉₊ ⌊2 * V⌋₊).card : ℝ) + (Icc ⌈U⌉₊ ⌊16 * U⌋₊).card := by
    have := hcard.trans (card_union_le _ _)
    rw [card_product, card_product, card_singleton, card_singleton, one_mul, mul_one] at this
    exact_mod_cast this
  linarith [hIcc (by linarith : V ≤ 2 * V) (by linarith : (0 : ℝ) ≤ 2 * V),
    hIcc (by linarith : U ≤ 16 * U) (by linarith : (0 : ℝ) ≤ 16 * U)]

/-- The line average of a function bounded by `1` is bounded by `1`. -/
theorem norm_lineAverage_le_one (x : ℝ) (d : Data K) {G : (ℕ → ℕ) → ℂ} (hG : ∀ ℓ, ‖G ℓ‖ ≤ 1) :
    ‖lineAverage x d G‖ ≤ 1 := by
  rw [lineAverage, norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (lineAssignments x d).card with h | h
  · simp [h]
  · calc ((lineAssignments x d).card : ℝ)⁻¹ * ‖∑ ℓ ∈ lineAssignments x d, G ℓ‖
        ≤ ((lineAssignments x d).card : ℝ)⁻¹ * ∑ _ℓ ∈ lineAssignments x d, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun ℓ _ => hG ℓ))
            (by positivity)
      _ = 1 := by
          rw [sum_const, nsmul_eq_mul, mul_one, inv_mul_cancel₀ (by exact_mod_cast h.ne')]

/-- `RootEquidist` for `G ≡ 1`: a box at scales `U, V ≥ 2` has at most
`UV (|c₂| |box| + C₀ min(U, V)^{-1/5})` roots. -/
theorem card_boxRoots_le {C₀ : ℝ} (hE : RootEquidist K C₀) (x : ℝ) (d : Data K) {U V : ℝ}
    (hU : 2 ≤ U) (hV : 2 ≤ V) {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (ha₁ : 1 ≤ a₁) (hab₁ : a₁ ≤ b₁)
    (hb₁ : b₁ ≤ 16) (ha₂ : 1 ≤ a₂) (hab₂ : a₂ ≤ b₂) (hb₂ : b₂ ≤ 2) (ha₃ : 0 ≤ a₃)
    (hab₃ : a₃ ≤ b₃) (hb₃ : b₃ ≤ 1) :
    ((boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃).card : ℝ) ≤
      U * V * (|primitiveDensity| * ((b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃)) +
        C₀ * min U V ^ (-(1 / 5 : ℝ))) := by
  have h := hE x d U V hU hV a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂ hb₂ ha₃ hab₃ hb₃ ∅
    (empty_subset _) (fun _ => 1) 1 (fun _ _ _ => rfl) (fun _ => by simp)
  simp only [sum_const, nsmul_eq_mul, mul_one, prod_empty, one_pow, one_mul] at h
  have hl := norm_lineAverage_le_one x d (G := fun _ => 1) (fun _ => by simp)
  have hs := norm_sub_norm_le ((boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃).card : ℂ)
    (((primitiveDensity * U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) : ℝ) : ℂ) *
      lineAverage x d fun _ => 1)
  rw [Complex.norm_natCast, norm_mul, Complex.norm_real, Real.norm_eq_abs] at hs
  have hvol : 0 ≤ (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) :=
    mul_nonneg (mul_nonneg (sub_nonneg.2 hab₁) (sub_nonneg.2 hab₂)) (sub_nonneg.2 hab₃)
  have habs : |primitiveDensity * U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃)| =
      U * V * (|primitiveDensity| * ((b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃))) := by
    rw [show primitiveDensity * U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) =
      primitiveDensity * (U * V * ((b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃))) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ U * V * ((b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃)))]
    ring
  rw [habs] at hs
  have hX : U * V * (|primitiveDensity| * ((b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃))) *
      ‖lineAverage x d fun _ => (1 : ℂ)‖ ≤
        U * V * (|primitiveDensity| * ((b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃))) :=
    mul_le_of_le_one_right (by positivity) hl
  linarith

/-- **Root replacement for one configuration.** Let `A` be an indicator bounded by `1` that
is constant on the roots of each cube outside `bad`, and `F = ∏_p λ_p` a product of line
factors in `[0, 1]`. Then the normalized root sum of `A · F` over the positions is the
Riemann sum `c₂ n⁻³ ∑_Q A(ϱ_Q) 𝔼_ℓ F` at the lower corners, up to the box errors on the good
cubes, the bad cubes, and the upper faces. -/
theorem norm_sum_positions_sub_le {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hE : RootEquidist K C₀) (x : ℝ)
    (d : Data K) {Y d₀ : ℝ} (hU : 2 ≤ d₀ * Y * d.Hm) (hV : 2 ≤ d.Hn) {n : ℕ} (hn : 1 ≤ n)
    (A : ℝ → ℝ → ℝ → ℝ) (hA : ∀ u v r, |A u v r| ≤ 1) (lam : ℕ → ℕ → ℝ)
    (hlam : ∀ p ∈ bandPrimes x d, ∀ l, 0 ≤ lam p l ∧ lam p l ≤ 1) (act : Finset ℕ)
    (hact : act ⊆ bandPrimes x d) (T : ℕ) {pmax : ℝ} (hpmax₁ : 1 ≤ pmax)
    (hpmax : ∀ p ∈ bandPrimes x d, (p : ℝ) ≤ pmax) (bad : Finset (ℕ × ℕ × ℕ))
    (hbad : ∀ i ∈ cubeIndices n, i ∉ bad → ∀ P₀ ∈ cubeRoots (d₀ * Y * d.Hm) d.Hn n i,
      A P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) =
        A (d₀ * Y * d.Hm * (1 + i.1 / n)) (d.Hn * (1 + i.2.1 / n)) (i.2.2 / n)) :
    ‖((d₀ * Y * d.Hm * d.Hn : ℝ) : ℂ)⁻¹ * ∑ P₀ ∈ positions d Y d₀,
          (A P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) : ℂ) *
            ∏ p ∈ bandPrimes x d, (lam p (rootLines P₀ p) : ℂ) -
        (primitiveDensity : ℂ) * (((n : ℂ) ^ 3)⁻¹ * ∑ i ∈ cubeIndices n,
          (A (d₀ * Y * d.Hm * (1 + i.1 / n)) (d.Hn * (1 + i.2.1 / n)) (i.2.2 / n) : ℂ) *
            lineAverage x d (fun ℓ => ∏ p ∈ bandPrimes x d, (lam p (ℓ p) : ℂ)))‖ ≤
      15 * (4 * dampMass x d act lam ^ T / T.factorial +
          (n : ℝ) ^ 3 * (((bandPrimes x d).card : ℝ) + 1) ^ T * C₀ *
            pmax ^ (6 * (act.card + T)) * min (d₀ * Y * d.Hm) d.Hn ^ (-(1 / 5 : ℝ))) +
        bad.card * (4 / (n : ℝ) ^ 3 + C₀ * min (d₀ * Y * d.Hm) d.Hn ^ (-(1 / 5 : ℝ))) +
        (16 * (d₀ * Y * d.Hm) + 2 * d.Hn + 2) / (d₀ * Y * d.Hm * d.Hn) := by
  classical
  have hU₀ : 0 < d₀ * Y * d.Hm := by linarith
  have hV₀ : 0 < d.Hn := by linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hedge := card_edgeRoots_le d hU₀ hV₀
  rw [sum_positions_eq d hU₀ hV₀ hn]
  set U := d₀ * Y * d.Hm with hUdef
  set V := d.Hn with hVdef
  set L := lineAverage x d (fun ℓ => ∏ p ∈ bandPrimes x d, (lam p (ℓ p) : ℂ)) with hLdef
  set m := min U V ^ (-(1 / 5 : ℝ)) with hm
  have hm₀ : 0 ≤ m := Real.rpow_nonneg (le_min hU₀.le hV₀.le) _
  have hc₂ : |primitiveDensity| ≤ 2 := RootResidue.abs_primitiveDensity_le
  have hUV : 0 < U * V := mul_pos hU₀ hV₀
  have hn₃ : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  -- step: the factors are bounded by `1`
  have hF₁ : ∀ ℓ : ℕ → ℕ, ‖∏ p ∈ bandPrimes x d, (lam p (ℓ p) : ℂ)‖ ≤ 1 := fun ℓ => by
    rw [norm_prod]
    refine prod_le_one₀ (fun _ _ => norm_nonneg _) fun p hp => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlam p hp (ℓ p)).1]
    exact (hlam p hp (ℓ p)).2
  have hL₁ : ‖L‖ ≤ 1 := norm_lineAverage_le_one x d hF₁
  have hsum₁ : ∀ s : Finset (ℕ × ℕ), ‖((U * V : ℝ) : ℂ)⁻¹ * ∑ P₀ ∈ s,
      (A P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) : ℂ) *
        ∏ p ∈ bandPrimes x d, (lam p (rootLines P₀ p) : ℂ)‖ ≤ (U * V)⁻¹ * s.card := by
    intro s
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hUV]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (inv_nonneg.2 hUV.le)
    calc _ ≤ ∑ _P₀ ∈ s, (1 : ℝ) := sum_le_sum fun P₀ _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc _ ≤ 1 * 1 := mul_le_mul (hA _ _ _) (hF₁ _) (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = s.card := by rw [sum_const, nsmul_eq_mul, mul_one]
  -- step: the cubes are boxes of volume `n⁻³`
  have hvol : ∀ i : ℕ × ℕ × ℕ,
      (1 + ((i.1 : ℝ) + 1) / n - (1 + (i.1 : ℝ) / n)) *
        (1 + ((i.2.1 : ℝ) + 1) / n - (1 + (i.2.1 : ℝ) / n)) *
          (((i.2.2 : ℝ) + 1) / n - (i.2.2 : ℝ) / n) = ((n : ℝ) ^ 3)⁻¹ := fun i => by
    field_simp
    ring
  have hside : ∀ k : ℕ, (k : ℝ) / n ≤ ((k : ℝ) + 1) / n := fun k =>
    div_le_div_of_nonneg_right (by linarith) hn'.le
  have hcorner : ∀ i ∈ cubeIndices n,
      1 ≤ 1 + (i.1 : ℝ) / n ∧ 1 + (i.1 : ℝ) / n ≤ 1 + ((i.1 : ℝ) + 1) / n ∧
        1 + ((i.1 : ℝ) + 1) / n ≤ 16 ∧
      1 ≤ 1 + (i.2.1 : ℝ) / n ∧ 1 + (i.2.1 : ℝ) / n ≤ 1 + ((i.2.1 : ℝ) + 1) / n ∧
        1 + ((i.2.1 : ℝ) + 1) / n ≤ 2 ∧
      0 ≤ (i.2.2 : ℝ) / n ∧ (i.2.2 : ℝ) / n ≤ ((i.2.2 : ℝ) + 1) / n ∧
        ((i.2.2 : ℝ) + 1) / n ≤ 1 := by
    intro i hi
    simp only [cubeIndices, mem_product, mem_range] at hi
    obtain ⟨hi₁, hi₂, hi₃⟩ := hi
    have h₁ : ((i.1 : ℝ) + 1) / n ≤ 15 := by
      rw [div_le_iff₀ hn']
      exact_mod_cast (show i.1 + 1 ≤ 15 * n by omega)
    have h₂ : ((i.2.1 : ℝ) + 1) / n ≤ 1 := by
      rw [div_le_iff₀ hn']
      exact_mod_cast (show i.2.1 + 1 ≤ 1 * n by omega)
    have h₃ : ((i.2.2 : ℝ) + 1) / n ≤ 1 := by
      rw [div_le_iff₀ hn']
      exact_mod_cast (show i.2.2 + 1 ≤ 1 * n by omega)
    have h₀ : ∀ k : ℕ, 0 ≤ (k : ℝ) / n := fun k => by positivity
    refine ⟨by linarith [h₀ i.1], by linarith [hside i.1], by linarith, by linarith [h₀ i.2.1],
      by linarith [hside i.2.1], by linarith, h₀ i.2.2, hside i.2.2, h₃⟩
  -- step: the error of each cube
  obtain ⟨D, hD⟩ : ∃ D : ℕ × ℕ × ℕ → ℂ, D = fun i =>
      ((U * V : ℝ) : ℂ)⁻¹ * ∑ P₀ ∈ cubeRoots U V n i,
          (A P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) : ℂ) *
            ∏ p ∈ bandPrimes x d, (lam p (rootLines P₀ p) : ℂ) -
        (primitiveDensity : ℂ) * (((n : ℂ) ^ 3)⁻¹ *
          ((A (U * (1 + i.1 / n)) (V * (1 + i.2.1 / n)) (i.2.2 / n) : ℂ) * L)) := ⟨_, rfl⟩
  have hgood : ∀ i ∈ cubeIndices n, i ∉ bad → ‖D i‖ ≤
      4 * ((n : ℝ) ^ 3)⁻¹ * dampMass x d act lam ^ T / T.factorial +
        (((bandPrimes x d).card : ℝ) + 1) ^ T * C₀ * pmax ^ (6 * (act.card + T)) * m := by
    intro i hi hib
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := hcorner i hi
    have hb := norm_boxRoots_prod_sub_le hC₀ hE x d hU hV h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ lam hlam act
      hact T hpmax₁ hpmax
    rw [hvol i, ← hLdef, ← hm] at hb
    have hs : ∑ P₀ ∈ cubeRoots U V n i, (A P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) : ℂ) *
        ∏ p ∈ bandPrimes x d, (lam p (rootLines P₀ p) : ℂ) =
          (A (U * (1 + i.1 / n)) (V * (1 + i.2.1 / n)) (i.2.2 / n) : ℂ) *
            ∑ P₀ ∈ cubeRoots U V n i, ∏ p ∈ bandPrimes x d, (lam p (rootLines P₀ p) : ℂ) := by
      rw [mul_sum]
      exact sum_congr rfl fun P₀ hP₀ => by rw [hbad i hi hib P₀ hP₀]
    have hDi : D i = (A (U * (1 + i.1 / n)) (V * (1 + i.2.1 / n)) (i.2.2 / n) : ℂ) *
        (((U * V : ℝ) : ℂ)⁻¹ * ∑ P₀ ∈ cubeRoots U V n i,
            ∏ p ∈ bandPrimes x d, (lam p (rootLines P₀ p) : ℂ) -
          ((primitiveDensity * ((n : ℝ) ^ 3)⁻¹ : ℝ) : ℂ) * L) := by
      rw [hD]
      simp only
      rw [hs]
      push_cast
      ring
    rw [hDi, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ 1 * (4 * ((n : ℝ) ^ 3)⁻¹ * dampMass x d act lam ^ T / T.factorial +
          (((bandPrimes x d).card : ℝ) + 1) ^ T * C₀ * pmax ^ (6 * (act.card + T)) * m) :=
          mul_le_mul (hA _ _ _) hb (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hbad' : ∀ i ∈ cubeIndices n, ‖D i‖ ≤ 4 / (n : ℝ) ^ 3 + C₀ * m := by
    intro i hi
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := hcorner i hi
    have hc := card_boxRoots_le hE x d hU hV h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
    rw [hvol i, ← hm] at hc
    have hroot : (U * V)⁻¹ * ((cubeRoots U V n i).card : ℝ) ≤ 2 * ((n : ℝ) ^ 3)⁻¹ + C₀ * m := by
      calc (U * V)⁻¹ * ((cubeRoots U V n i).card : ℝ)
          ≤ (U * V)⁻¹ * (U * V * (|primitiveDensity| * ((n : ℝ) ^ 3)⁻¹ + C₀ * m)) :=
            mul_le_mul_of_nonneg_left hc (inv_nonneg.2 hUV.le)
        _ = |primitiveDensity| * ((n : ℝ) ^ 3)⁻¹ + C₀ * m := by field_simp
        _ ≤ 2 * ((n : ℝ) ^ 3)⁻¹ + C₀ * m := by gcongr
    have hmain : ‖(primitiveDensity : ℂ) * (((n : ℂ) ^ 3)⁻¹ *
        ((A (U * (1 + i.1 / n)) (V * (1 + i.2.1 / n)) (i.2.2 / n) : ℂ) * L))‖ ≤
          2 * ((n : ℝ) ^ 3)⁻¹ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, norm_inv, norm_pow, Complex.norm_natCast]
      have hAL : |A (U * (1 + i.1 / n)) (V * (1 + i.2.1 / n)) (i.2.2 / n)| * ‖L‖ ≤ 1 := by
        calc _ ≤ 1 * 1 := mul_le_mul (hA _ _ _) hL₁ (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc _ ≤ 2 * (((n : ℝ) ^ 3)⁻¹ * 1) := by gcongr
        _ = _ := by ring
    rw [hD]
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ (U * V)⁻¹ * ((cubeRoots U V n i).card : ℝ) + 2 * ((n : ℝ) ^ 3)⁻¹ :=
          add_le_add (hsum₁ _) hmain
      _ ≤ 4 / (n : ℝ) ^ 3 + C₀ * m := by
          rw [div_eq_mul_inv]
          linarith
  -- step: assemble the cubes and the upper faces
  have hsplit : ((U * V : ℝ) : ℂ)⁻¹ * (∑ i ∈ cubeIndices n, ∑ P₀ ∈ cubeRoots U V n i,
          (A P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) : ℂ) *
            ∏ p ∈ bandPrimes x d, (lam p (rootLines P₀ p) : ℂ) +
        ∑ P₀ ∈ edgeRoots d Y d₀, (A P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) : ℂ) *
            ∏ p ∈ bandPrimes x d, (lam p (rootLines P₀ p) : ℂ)) -
      (primitiveDensity : ℂ) * (((n : ℂ) ^ 3)⁻¹ * ∑ i ∈ cubeIndices n,
          (A (U * (1 + i.1 / n)) (V * (1 + i.2.1 / n)) (i.2.2 / n) : ℂ) * L) =
      ∑ i ∈ cubeIndices n, D i + ((U * V : ℝ) : ℂ)⁻¹ * ∑ P₀ ∈ edgeRoots d Y d₀,
          (A P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) : ℂ) *
            ∏ p ∈ bandPrimes x d, (lam p (rootLines P₀ p) : ℂ) := by
    rw [hD, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
    ring
  rw [hsplit]
  have hgoodsum : ∑ i ∈ cubeIndices n with i ∉ bad, ‖D i‖ ≤
      15 * (4 * dampMass x d act lam ^ T / T.factorial +
        (n : ℝ) ^ 3 * (((bandPrimes x d).card : ℝ) + 1) ^ T * C₀ *
          pmax ^ (6 * (act.card + T)) * m) := by
    have hB : 0 ≤ 4 * ((n : ℝ) ^ 3)⁻¹ * dampMass x d act lam ^ T / T.factorial +
        (((bandPrimes x d).card : ℝ) + 1) ^ T * C₀ * pmax ^ (6 * (act.card + T)) * m := by
      have := dampMass_nonneg (act := act) fun p hp l => (hlam p hp l).2
      have : (0 : ℝ) ≤ pmax ^ (6 * (act.card + T)) := pow_nonneg (by linarith) _
      positivity
    calc _ ≤ ∑ i ∈ cubeIndices n with i ∉ bad,
          (4 * ((n : ℝ) ^ 3)⁻¹ * dampMass x d act lam ^ T / T.factorial +
            (((bandPrimes x d).card : ℝ) + 1) ^ T * C₀ * pmax ^ (6 * (act.card + T)) * m) :=
          sum_le_sum fun i hi => hgood i (mem_filter.1 hi).1 (mem_filter.1 hi).2
      _ ≤ ∑ _i ∈ cubeIndices n,
          (4 * ((n : ℝ) ^ 3)⁻¹ * dampMass x d act lam ^ T / T.factorial +
            (((bandPrimes x d).card : ℝ) + 1) ^ T * C₀ * pmax ^ (6 * (act.card + T)) * m) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => hB
      _ = 15 * (4 * dampMass x d act lam ^ T / T.factorial +
          (n : ℝ) ^ 3 * (((bandPrimes x d).card : ℝ) + 1) ^ T * C₀ *
            pmax ^ (6 * (act.card + T)) * m) := by
          rw [sum_const, nsmul_eq_mul, cubeIndices, card_product, card_product, card_range,
            card_range]
          push_cast
          field_simp
  have hbadsum : ∑ i ∈ cubeIndices n with i ∈ bad, ‖D i‖ ≤
      bad.card * (4 / (n : ℝ) ^ 3 + C₀ * m) := by
    calc _ ≤ ∑ i ∈ cubeIndices n with i ∈ bad, (4 / (n : ℝ) ^ 3 + C₀ * m) :=
          sum_le_sum fun i hi => hbad' i (mem_filter.1 hi).1
      _ = ((cubeIndices n).filter (· ∈ bad)).card * (4 / (n : ℝ) ^ 3 + C₀ * m) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ bad.card * (4 / (n : ℝ) ^ 3 + C₀ * m) := by
          gcongr
          exact fun i hi => (mem_filter.1 hi).2
  have hedge' : (U * V)⁻¹ * ((edgeRoots d Y d₀).card : ℝ) ≤
      (16 * U + 2 * V + 2) / (U * V) := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hedge (inv_nonneg.2 hUV.le)
  calc _ ≤ ‖∑ i ∈ cubeIndices n, D i‖ + ‖((U * V : ℝ) : ℂ)⁻¹ * ∑ P₀ ∈ edgeRoots d Y d₀,
          (A P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) : ℂ) *
            ∏ p ∈ bandPrimes x d, (lam p (rootLines P₀ p) : ℂ)‖ := norm_add_le _ _
    _ ≤ ∑ i ∈ cubeIndices n, ‖D i‖ + (U * V)⁻¹ * ((edgeRoots d Y d₀).card : ℝ) :=
        add_le_add (norm_sum_le _ _) (hsum₁ _)
    _ = ∑ i ∈ cubeIndices n with i ∈ bad, ‖D i‖ + ∑ i ∈ cubeIndices n with i ∉ bad, ‖D i‖ +
        (U * V)⁻¹ * ((edgeRoots d Y d₀).card : ℝ) := by
        rw [sum_filter_add_sum_filter_not]
    _ ≤ _ := by linarith

end Erdos408.OneSided
