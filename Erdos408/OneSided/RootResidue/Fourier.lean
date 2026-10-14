import Erdos408.OneSided.Analysis.Divisor
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Counting a periodic set in a box by completion

The discrepancy step of PD Lemma 3.3, in the form of `blueprint/one_sided_type_ii.md` §5.2.
Let `G ⊆ (ℤ/m)²` and let `A, B` be finite sets of naturals. Expanding the indicator of `G`
in additive characters gives

`#{(a, b) ∈ A × B : (a, b) mod m ∈ G} - (|B|/m) #{(a, y) ∈ A × ℤ/m : (a, y) ∈ G}
  = m⁻² ∑_h ∑_{k ≠ 0} Ŝ_G(h, k) Â(h) B̂(k)`,

with `Ŝ_G(h, k) = ∑_{(x, y) ∈ G} e((h x + k y)/m)` and `Â(h) = ∑_{a ∈ A} e(-h a/m)`.

When `A, B` are arithmetic progressions `{r + q j : α ≤ j < β}` with `q` a unit mod `m`, the
transforms are geometric sums, `|Â(h)| ≤ m / (2 ‖h q‖)` with `‖·‖` the distance to `0` in
`ℤ/m`. If `|Ŝ_G(h, k)| ≤ X (k, m)` for `k ≠ 0`, the error is therefore at most
`X τ(m) (2 + log m)²` (`abs_card_filter_mem_prog_sub_le`), whatever the length of `B`.
-/

namespace Erdos408.OneSided.RootResidue

open Finset

variable {m : ℕ} [NeZero m]

/-! ### Characters and transforms -/

/-- The exponential sum `Ŝ_G(h, k) = ∑_{(x, y) ∈ G} e((h x + k y)/m)` of a set of residue
pairs. -/
noncomputable def pairSum (G : Finset (ZMod m × ZMod m)) (h k : ZMod m) : ℂ :=
  ∑ p ∈ G, ZMod.stdAddChar (h * p.1 + k * p.2)

/-- The transform `Â(h) = ∑_{a ∈ A} e(-h f(a)/m)` of a finite set `A` placed in `ℤ/m` by
`f`. -/
noncomputable def transform {α : Type*} (f : α → ZMod m) (A : Finset α) (h : ZMod m) : ℂ :=
  ∑ a ∈ A, ZMod.stdAddChar (-(h * f a))

/-- `|e(x/m)| = 1`. -/
theorem norm_stdAddChar (x : ZMod m) : ‖(ZMod.stdAddChar x : ℂ)‖ = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

/-- Orthogonality: `∑_h e(h z/m) = m [z = 0]`. -/
theorem sum_stdAddChar_mul (z : ZMod m) :
    ∑ h : ZMod m, ZMod.stdAddChar (h * z) = if z = 0 then (m : ℂ) else 0 := by
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar m), ZMod.card]
  split_ifs <;> simp

/-- The Fourier expansion of the indicator of `G`:
`[(x, y) ∈ G] = m⁻² ∑_{h, k} Ŝ_G(h, k) e(-h x/m) e(-k y/m)`. -/
theorem indicator_eq_sum_pairSum (G : Finset (ZMod m × ZMod m)) (x y : ZMod m) :
    (if (x, y) ∈ G then (1 : ℂ) else 0) = ((m : ℂ) ^ 2)⁻¹ * ∑ h : ZMod m, ∑ k : ZMod m,
      pairSum G h k * ZMod.stdAddChar (-(h * x)) * ZMod.stdAddChar (-(k * y)) := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  -- swap the sums and use orthogonality in each coordinate
  have h₁ : ∑ h : ZMod m, ∑ k : ZMod m,
      pairSum G h k * ZMod.stdAddChar (-(h * x)) * ZMod.stdAddChar (-(k * y)) =
      ∑ p ∈ G, (∑ h : ZMod m, ZMod.stdAddChar (h * (p.1 - x))) *
        ∑ k : ZMod m, ZMod.stdAddChar (k * (p.2 - y)) := by
    simp only [pairSum, sum_mul, mul_sum]
    rw [sum_congr rfl fun h _ => sum_comm, sum_comm]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun k _ => sum_congr rfl fun h _ => ?_
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [h₁]
  simp only [sum_stdAddChar_mul, sub_eq_zero, ite_zero_mul_ite_zero]
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have h₂ : ({p ∈ G | p.1 = x ∧ p.2 = y} : Finset _) = if (x, y) ∈ G then {(x, y)} else ∅ := by
    ext p
    split_ifs with hxy
    · simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨_, h₁, h₂⟩
        exact Prod.ext h₁ h₂
      · rintro rfl
        exact ⟨hxy, rfl, rfl⟩
    · simp only [mem_filter, notMem_empty, iff_false, not_and]
      intro hp h₁ h₂
      exact hxy (by rw [← h₁, ← h₂]; exact hp)
  rw [h₂]
  split_ifs <;> field_simp <;> simp

/-- The count of `A × B` in `G`, expanded:
`#{(a, b) ∈ A × B : (f a, g b) ∈ G} = m⁻² ∑_{h, k} Ŝ_G(h, k) Â(h) B̂(k)`. -/
theorem card_filter_mem_eq_sum {α β : Type*} (G : Finset (ZMod m × ZMod m)) (f : α → ZMod m)
    (g : β → ZMod m) (A : Finset α) (B : Finset β) :
    ((#{p ∈ A ×ˢ B | (f p.1, g p.2) ∈ G} : ℕ) : ℂ) =
      ((m : ℂ) ^ 2)⁻¹ * ∑ h : ZMod m, ∑ k : ZMod m,
        pairSum G h k * transform f A h * transform g B k := by
  rw [card_filter, Nat.cast_sum, sum_product]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, indicator_eq_sum_pairSum, ← mul_sum]
  congr 1
  -- bring `h, k` outside and recognize the two transforms
  rw [sum_congr rfl fun a _ => sum_comm, sum_comm]
  refine sum_congr rfl fun h _ => ?_
  rw [sum_congr rfl fun a _ => sum_comm, sum_comm]
  refine sum_congr rfl fun k _ => ?_
  simp only [transform, mul_sum, sum_mul]
  exact sum_comm

/-- `B̂(0) = |B|`. -/
theorem transform_zero {α : Type*} (f : α → ZMod m) (A : Finset α) :
    transform f A 0 = #A := by
  simp [transform]

/-- The transform of all of `ℤ/m` is `m [k = 0]`. -/
theorem transform_id_univ (k : ZMod m) :
    transform id (univ : Finset (ZMod m)) k = if k = 0 then (m : ℂ) else 0 := by
  rw [transform]
  convert sum_stdAddChar_mul (-k) using 1
  · exact sum_congr rfl fun y _ => by rw [id, mul_neg, mul_comm]
  · simp only [neg_eq_zero]

/-- **The box identity.** With `Mc = #{(a, y) ∈ A × ℤ/m : (f a, y) ∈ G}`,
`#{(a, b) ∈ A × B : (f a, g b) ∈ G} - (|B|/m) Mc = m⁻² ∑_h ∑_{k ≠ 0} Ŝ_G(h, k) Â(h) B̂(k)`. -/
theorem card_filter_mem_sub_eq_sum {α β : Type*} (G : Finset (ZMod m × ZMod m))
    (f : α → ZMod m) (g : β → ZMod m) (A : Finset α) (B : Finset β) :
    ((#{p ∈ A ×ˢ B | (f p.1, g p.2) ∈ G} : ℕ) : ℂ) -
        (#B : ℂ) / m * (#{p ∈ A ×ˢ (univ : Finset (ZMod m)) | (f p.1, p.2) ∈ G} : ℕ) =
      ((m : ℂ) ^ 2)⁻¹ * ∑ h : ZMod m, ∑ k ∈ univ.erase 0,
        pairSum G h k * transform f A h * transform g B k := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  have hMc := card_filter_mem_eq_sum G f id A (univ : Finset (ZMod m))
  simp only [id] at hMc
  -- split off `k = 0` in both expansions
  have hsplit : ∀ Φ : ZMod m → ZMod m → ℂ, ∑ h : ZMod m, ∑ k : ZMod m, Φ h k =
      ∑ h : ZMod m, Φ h 0 + ∑ h : ZMod m, ∑ k ∈ univ.erase 0, Φ h k := fun Φ => by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun h _ => (add_sum_erase _ _ (mem_univ 0)).symm
  rw [card_filter_mem_eq_sum, hMc, hsplit, hsplit]
  have hz : ∑ h : ZMod m, ∑ k ∈ univ.erase 0,
      pairSum G h k * transform f A h * transform id univ k = 0 := by
    refine sum_eq_zero fun h _ => sum_eq_zero fun k hk => ?_
    rw [transform_id_univ, ite_eq_right_iff.2 fun h0 => absurd h0 (ne_of_mem_erase hk), mul_zero]
  rw [hz, add_zero]
  simp only [transform_zero, card_univ, ZMod.card]
  rw [← sum_mul, ← sum_mul]
  field_simp
  ring

/-- **The box bound.** If `|Ŝ_G(h, k)| ≤ X (k, m)` for `k ≠ 0`, the box identity gives
`|#{(a, b) ∈ A × B : (f a, g b) ∈ G} - (|B|/m) Mc| ≤
m⁻² (∑_h |Â(h)|) ∑_{k ≠ 0} |B̂(k)| X (k, m)`. -/
theorem abs_card_filter_mem_sub_le {α β : Type*} (G : Finset (ZMod m × ZMod m))
    (f : α → ZMod m) (g : β → ZMod m) (A : Finset α) (B : Finset β) {X : ℝ}
    (hX : ∀ h k, k ≠ 0 → ‖pairSum G h k‖ ≤ X * Nat.gcd k.val m) :
    |(#{p ∈ A ×ˢ B | (f p.1, g p.2) ∈ G} : ℝ) -
        (#B : ℝ) / m * #{p ∈ A ×ˢ (univ : Finset (ZMod m)) | (f p.1, p.2) ∈ G}| ≤
      ((m : ℝ) ^ 2)⁻¹ * (∑ h : ZMod m, ‖transform f A h‖) *
        ∑ k ∈ univ.erase 0, ‖transform g B k‖ * (X * Nat.gcd k.val m) := by
  have hC := card_filter_mem_sub_eq_sum G f g A B
  calc |(#{p ∈ A ×ˢ B | (f p.1, g p.2) ∈ G} : ℝ) -
        (#B : ℝ) / m * #{p ∈ A ×ˢ (univ : Finset (ZMod m)) | (f p.1, p.2) ∈ G}|
      = ‖((m : ℂ) ^ 2)⁻¹ * ∑ h : ZMod m, ∑ k ∈ univ.erase 0,
          pairSum G h k * transform f A h * transform g B k‖ := by
        rw [← hC, ← Real.norm_eq_abs, ← Complex.norm_real]
        push_cast
        rfl
    _ ≤ ((m : ℝ) ^ 2)⁻¹ * ∑ h : ZMod m, ∑ k ∈ univ.erase 0,
          ‖transform f A h‖ * (‖transform g B k‖ * (X * Nat.gcd k.val m)) := by
        rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
        gcongr
        refine (norm_sum_le _ _).trans (sum_le_sum fun h _ => ?_)
        refine (norm_sum_le _ _).trans (sum_le_sum fun k hk => ?_)
        rw [norm_mul, norm_mul]
        calc ‖pairSum G h k‖ * ‖transform f A h‖ * ‖transform g B k‖
            ≤ (X * Nat.gcd k.val m) * ‖transform f A h‖ * ‖transform g B k‖ := by
              gcongr
              exact hX h k (ne_of_mem_erase hk)
          _ = _ := by ring
    _ = _ := by rw [mul_assoc, sum_mul_sum]

/-! ### Transforms of progressions -/

/-- `sin(π s) ≥ 2 s` for `0 ≤ s ≤ 1/2`. -/
theorem two_mul_le_sin_pi_mul {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) :
    2 * s ≤ Real.sin (Real.pi * s) := by
  have h := Real.mul_le_sin (x := Real.pi * s) (by positivity) (by nlinarith [Real.pi_pos])
  rwa [show 2 / Real.pi * (Real.pi * s) = 2 * s by field_simp] at h

/-- Jordan's inequality on the circle: `|e(w/m) - 1| ≥ 4 ‖w‖/m`, where
`‖w‖ = min(w, m - w)` is the distance to `0` in `ℤ/m`. -/
theorem le_norm_stdAddChar_sub_one (w : ZMod m) :
    4 * ((min w.val (m - w.val) : ℕ) : ℝ) / m ≤ ‖(ZMod.stdAddChar w : ℂ) - 1‖ := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 (NeZero.pos m)
  have hw : w.val < m := ZMod.val_lt w
  set t : ℝ := w.val / m
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := (div_le_one hm).2 (by exact_mod_cast hw.le)
  -- `|e(t) - 1| = 2 sin(π t)`
  have hnorm : ‖(ZMod.stdAddChar w : ℂ) - 1‖ = 2 * Real.sin (Real.pi * t) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    have : 2 * ↑Real.pi * Complex.I * (w.val : ℂ) / m =
        Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) := by
      simp only [t]
      push_cast
      ring
    rw [this, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
      show 2 * Real.pi * t / 2 = Real.pi * t by ring, abs_of_nonneg]
    exact mul_nonneg two_pos.le (Real.sin_nonneg_of_nonneg_of_le_pi
      (by positivity) (by nlinarith [Real.pi_pos]))
  rw [hnorm]
  have hsub : ((m - w.val : ℕ) : ℝ) = m - w.val := Nat.cast_sub hw.le
  have htm : (w.val : ℝ) = t * m := by simp only [t]; field_simp
  rcases le_total w.val (m - w.val) with hle | hle
  · -- `t ≤ 1/2`
    rw [min_eq_left hle]
    have hle' : (w.val : ℝ) ≤ m - w.val := by rw [← hsub]; exact_mod_cast hle
    have := two_mul_le_sin_pi_mul ht0 (by nlinarith)
    rw [htm, mul_div_assoc, mul_div_cancel_right₀ _ hm.ne']
    linarith
  · -- `1 - t ≤ 1/2`, and `sin(π t) = sin(π (1 - t))`
    rw [min_eq_right hle, hsub]
    have hle' : (m : ℝ) - w.val ≤ w.val := by rw [← hsub]; exact_mod_cast hle
    have := two_mul_le_sin_pi_mul (s := 1 - t) (by linarith) (by nlinarith)
    rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring, Real.sin_pi_sub] at this
    rw [htm, show (m : ℝ) - t * m = (1 - t) * m by ring, mul_div_assoc,
      mul_div_cancel_right₀ _ hm.ne']
    linarith

/-- A nonzero residue has `‖w‖ = min(w, m - w) ≥ 1`. -/
theorem one_le_min_val {w : ZMod m} (hw : w ≠ 0) : 1 ≤ min w.val (m - w.val) := by
  have h₁ := ZMod.val_pos.2 hw
  have h₂ := ZMod.val_lt w
  omega

/-- The weight `m / (2 ‖w‖)`, with `‖w‖ = min(w, m - w)`; it vanishes at `w = 0`. -/
noncomputable def freqWeight (w : ZMod m) : ℝ := m / (2 * ((min w.val (m - w.val) : ℕ) : ℝ))

/-- The transform of a progression `{r + q j : α ≤ j < β}` is a geometric sum:
`|Â(h)| ≤ m / (2 ‖h q‖)` when `h q ≠ 0`. -/
theorem norm_transform_image_le (q r α β : ℕ) {h : ZMod m} (hq : h * (q : ZMod m) ≠ 0) :
    ‖transform (fun a : ℕ => (a : ZMod m)) ((Ico α β).image fun j => r + q * j) h‖ ≤
      freqWeight (-(h * (q : ZMod m))) := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  set z : ℂ := ZMod.stdAddChar (-(h * (q : ZMod m)))
  have hz1 : z ≠ 1 := by
    intro hz
    rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := m))] at hz
    exact hq (neg_eq_zero.1 (ZMod.injective_stdAddChar hz))
  have hz : ‖z‖ = 1 := norm_stdAddChar _
  have hzs : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz1)
  -- the transform is `e(-h r/m) z^α (z^n - 1)/(z - 1)`
  have hsum : transform (fun a : ℕ => (a : ZMod m)) ((Ico α β).image fun j => r + q * j) h =
      ZMod.stdAddChar (-(h * (r : ZMod m))) * (z ^ α * ((z ^ (β - α) - 1) / (z - 1))) := by
    rw [transform, sum_image fun i _ j _ hij => by simpa [hq0] using hij,
      sum_Ico_eq_sum_range, ← geom_sum_eq hz1, mul_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← pow_add, ← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul, nsmul_eq_mul]
    congr 1
    push_cast
    ring
  -- `|z^α| = 1`, `|z^n - 1| ≤ 2` and `|z - 1| ≥ 4 ‖h q‖/m`
  have hnum : ‖z ^ (β - α) - 1‖ ≤ 2 := by
    calc ‖z ^ (β - α) - 1‖ ≤ ‖z ^ (β - α)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
  have hden := le_norm_stdAddChar_sub_one (-(h * (q : ZMod m)))
  rw [hsum, norm_mul, norm_stdAddChar, one_mul, norm_mul, norm_pow, hz, one_pow, one_mul,
    norm_div, freqWeight]
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 (NeZero.pos m)
  calc ‖z ^ (β - α) - 1‖ / ‖z - 1‖ ≤ 2 / ‖z - 1‖ := by gcongr
    _ ≤ 2 / (4 * ((min (-(h * (q : ZMod m))).val (m - (-(h * (q : ZMod m))).val) : ℕ) : ℝ) /
          m) := by
        refine div_le_div_of_nonneg_left two_pos.le ?_ hden
        have := one_le_min_val (neg_ne_zero.2 hq)
        positivity
    _ = _ := by field_simp; ring

/-! ### Sums of the weights -/

/-- `∑_{w ≠ 0} G(w) ≤ ∑_{1 ≤ j ≤ m} G(j)` for nonnegative `G`. -/
theorem sum_ite_val_le_sum_Icc (G : ℕ → ℝ) (hG : ∀ j, 0 ≤ G j) :
    ∑ w : ZMod m, (if w = 0 then 0 else G w.val) ≤ ∑ j ∈ Icc 1 m, G j := by
  rw [sum_ite, sum_const_zero, zero_add,
    ← sum_image fun a _ b _ hab => ZMod.val_injective m hab]
  refine sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => hG j
  obtain ⟨w, hw, rfl⟩ := mem_image.1 hj
  have h₁ := ZMod.val_pos.2 (mem_filter.1 hw).2
  exact mem_Icc.2 ⟨h₁, (ZMod.val_lt w).le⟩

/-- `∑_w (m / (2 ‖w‖)) g(w) ≤ m ∑_{1 ≤ j ≤ m} g(j)/j` for nonnegative `g` with
`g(m - j) = g(j)`: bound `1/‖w‖ ≤ 1/w + 1/(m - w)` and reflect `w ↦ -w`. -/
theorem sum_freqWeight_mul_le (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j)
    (hsym : ∀ j, j < m → g (m - j) = g j) :
    ∑ w : ZMod m, freqWeight w * g w.val ≤ m * ∑ j ∈ Icc 1 m, g j / j := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 (NeZero.pos m)
  set F₁ : ZMod m → ℝ := fun w => if w = 0 then 0 else g w.val / w.val
  set F₂ : ZMod m → ℝ := fun w => if w = 0 then 0 else g w.val / ((m - w.val : ℕ) : ℝ)
  -- the pointwise bound
  have hpt : ∀ w : ZMod m, freqWeight w * g w.val ≤ m / 2 * (F₁ w + F₂ w) := by
    intro w
    by_cases hw : w = 0
    · simp [hw, freqWeight, F₁, F₂]
    have h₁ := ZMod.val_pos.2 hw
    have h₂ := ZMod.val_lt w
    have ha : (0 : ℝ) < w.val := by exact_mod_cast h₁
    have hb : (0 : ℝ) < ((m - w.val : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt h₂
    simp only [freqWeight, F₁, F₂, hw, ite_false]
    rcases le_total w.val (m - w.val) with hle | hle
    · rw [min_eq_left hle]
      have : (0 : ℝ) ≤ g w.val / ((m - w.val : ℕ) : ℝ) := div_nonneg (hg _) hb.le
      have hgw := hg w.val
      calc (m : ℝ) / (2 * (w.val : ℝ)) * g w.val = m / 2 * (g w.val / w.val) := by
            field_simp
        _ ≤ _ := by gcongr; linarith
    · rw [min_eq_right hle]
      have : (0 : ℝ) ≤ g w.val / w.val := div_nonneg (hg _) ha.le
      calc (m : ℝ) / (2 * ((m - w.val : ℕ) : ℝ)) * g w.val =
            m / 2 * (g w.val / ((m - w.val : ℕ) : ℝ)) := by field_simp
        _ ≤ _ := by gcongr; linarith
  -- the reflection `w ↦ -w` turns `F₂` into `F₁`
  have hrefl : ∑ w : ZMod m, F₂ w = ∑ w : ZMod m, F₁ w := by
    rw [← Fintype.sum_equiv (Equiv.neg (ZMod m)) (fun w => F₂ (-w)) F₂ fun _ => rfl]
    refine sum_congr rfl fun w _ => ?_
    by_cases hw : w = 0
    · simp [hw, F₁, F₂]
    have : NeZero w := ⟨hw⟩
    have h₂ := ZMod.val_lt w
    simp only [F₁, F₂, neg_eq_zero, hw, ite_false, ZMod.val_neg_of_ne_zero,
      Nat.sub_sub_self h₂.le]
    rw [hsym _ h₂]
  have hF₁ : ∑ w : ZMod m, F₁ w ≤ ∑ j ∈ Icc 1 m, g j / j :=
    sum_ite_val_le_sum_Icc (fun j => g j / j) fun j => div_nonneg (hg j) j.cast_nonneg
  calc ∑ w : ZMod m, freqWeight w * g w.val ≤ ∑ w : ZMod m, m / 2 * (F₁ w + F₂ w) :=
        sum_le_sum fun w _ => hpt w
    _ = m * ∑ w : ZMod m, F₁ w := by
        rw [← mul_sum, sum_add_distrib, hrefl]
        ring
    _ ≤ _ := by gcongr

/-- `∑_{1 ≤ j ≤ m} (j, m)/j ≤ τ(m) (1 + log m)`: bound `(j, m)` by the sum of the divisors
`d ∣ m` dividing `j`, and substitute `j = d i`. -/
theorem sum_gcd_div_le :
    ∑ j ∈ Icc 1 m, (Nat.gcd j m : ℝ) / j ≤ m.divisors.card * (1 + Real.log m) := by
  have hm := NeZero.ne m
  calc ∑ j ∈ Icc 1 m, (Nat.gcd j m : ℝ) / j
      ≤ ∑ j ∈ Icc 1 m, ∑ d ∈ m.divisors, if d ∣ j then (d : ℝ) / j else 0 := by
        refine sum_le_sum fun j _ => ?_
        have hmem : Nat.gcd j m ∈ m.divisors := Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right _ _, hm⟩
        refine le_trans ?_ (single_le_sum (f := fun d => if d ∣ j then (d : ℝ) / j else 0)
          (fun d _ => by positivity) hmem)
        rw [ite_eq_left_iff.2 fun h => absurd (Nat.gcd_dvd_left _ _) h]
    _ = ∑ d ∈ m.divisors, ∑ j ∈ Icc 1 m with d ∣ j, (d : ℝ) / j := by
        rw [sum_comm]
        exact sum_congr rfl fun d _ => (sum_filter _ _).symm
    _ ≤ ∑ d ∈ m.divisors, (1 + Real.log m) := by
        refine sum_le_sum fun d hd => ?_
        have hdm := Nat.dvd_of_mem_divisors hd
        have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
        -- the multiples of `d` in `[1, m]` are `d i`, `1 ≤ i ≤ m/d`
        have himg : ({j ∈ Icc 1 m | d ∣ j} : Finset ℕ) = (Icc 1 (m / d)).image (d * ·) := by
          ext j
          simp only [mem_filter, mem_Icc, mem_image]
          constructor
          · rintro ⟨⟨h₁, h₂⟩, i, rfl⟩
            refine ⟨i, ⟨?_, (Nat.le_div_iff_mul_le hd0).2 (by linarith [mul_comm d i])⟩, rfl⟩
            rcases Nat.eq_zero_or_pos i with rfl | hi
            · simp at h₁
            · exact hi
          · rintro ⟨i, ⟨h₁, h₂⟩, rfl⟩
            refine ⟨⟨Nat.mul_pos hd0 h₁ |>.le |> fun h => by nlinarith, ?_⟩, dvd_mul_right _ _⟩
            calc d * i ≤ d * (m / d) := Nat.mul_le_mul_left _ h₂
              _ ≤ m := Nat.mul_div_le m d
        rw [himg, sum_image fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hd0 hab]
        calc ∑ i ∈ Icc 1 (m / d), (d : ℝ) / ((d * i : ℕ) : ℝ)
            = ∑ i ∈ Icc 1 (m / d), (i : ℝ)⁻¹ := by
              refine sum_congr rfl fun i _ => ?_
              have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
              push_cast
              field_simp
          _ ≤ 1 + Real.log (m / d : ℕ) := sum_Icc_inv_le _
          _ ≤ 1 + Real.log m := by
              have h₁ : (0 : ℝ) < (m / d : ℕ) := by
                exact_mod_cast Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdm) hd0
              gcongr
              exact_mod_cast Nat.div_le_self m d
    _ = _ := by rw [sum_const, nsmul_eq_mul]

/-! ### The box bound for progressions -/

omit [NeZero m] in
/-- `(k w, m) = (k, m)` for a unit `w` of `ℤ/m`. -/
theorem gcd_val_mul_of_isUnit (k : ZMod m) {w : ZMod m} (hw : IsUnit w) :
    Nat.gcd (k * w).val m = Nat.gcd k.val m := by
  have hcop : w.val.Coprime m := by
    have := ZMod.val_coe_unit_coprime hw.unit
    rwa [IsUnit.unit_spec] at this
  rw [ZMod.val_mul, ← Nat.gcd_rec, Nat.gcd_comm, Nat.Coprime.gcd_mul_right_cancel _ hcop]

/-- `∑_h |Â(h)| ≤ m (2 + log m)` for a progression `A = {r + q j : α ≤ j < β}` with
`β - α ≤ m` and `q` a unit mod `m`. -/
theorem sum_norm_transform_image_le {q : ℕ} (hq : IsUnit (q : ZMod m)) (r α β : ℕ)
    (hA : β - α ≤ m) :
    ∑ h : ZMod m, ‖transform (fun a : ℕ => (a : ZMod m)) ((Ico α β).image fun j => r + q * j) h‖
      ≤ m * (2 + Real.log m) := by
  set A := (Ico α β).image fun j => r + q * j
  have hcard : (#A : ℝ) ≤ m := by
    have : #A ≤ m := card_image_le.trans (by rw [Nat.card_Ico]; exact hA)
    exact_mod_cast this
  have hw0 : ∀ w : ZMod m, 0 ≤ freqWeight w := fun w => by unfold freqWeight; positivity
  -- each term is at most `|A| [h = 0] + m / (2 ‖h q‖)`
  have hpt : ∀ h : ZMod m, ‖transform (fun a : ℕ => (a : ZMod m)) A h‖ ≤
      (if h = 0 then (#A : ℝ) else 0) + freqWeight (-(h * (q : ZMod m))) := by
    intro h
    by_cases h0 : h = 0
    · rw [h0, transform_zero, Complex.norm_natCast, zero_mul, neg_zero]
      simp only [ite_true]
      linarith [hw0 0]
    · rw [ite_eq_right_iff.2 fun h' => absurd h' h0, zero_add]
      exact norm_transform_image_le q r α β ((hq.mul_left_eq_zero).not.2 h0)
  -- `h ↦ -h q` permutes `ℤ/m`
  have hperm : ∑ h : ZMod m, freqWeight (-(h * (q : ZMod m))) = ∑ w : ZMod m, freqWeight w :=
    Fintype.sum_equiv ((Units.mulRight hq.unit).trans (Equiv.neg _)) _ _ fun h => by
      simp [Units.mulRight]
  have hw : ∑ w : ZMod m, freqWeight w ≤ m * (1 + Real.log m) := by
    have := sum_freqWeight_mul_le (m := m) (fun _ => 1) (fun _ => zero_le_one) fun _ _ => rfl
    simp only [mul_one, one_div] at this
    exact this.trans (by gcongr; exact sum_Icc_inv_le m)
  calc ∑ h : ZMod m, ‖transform (fun a : ℕ => (a : ZMod m)) A h‖
      ≤ ∑ h : ZMod m, ((if h = 0 then (#A : ℝ) else 0) + freqWeight (-(h * (q : ZMod m)))) :=
        sum_le_sum fun h _ => hpt h
    _ = #A + ∑ w : ZMod m, freqWeight w := by
        rw [sum_add_distrib, sum_ite_eq', ite_eq_left_iff.2 fun h => absurd (mem_univ _) h, hperm]
    _ ≤ m + m * (1 + Real.log m) := add_le_add hcard hw
    _ = m * (2 + Real.log m) := by ring

/-- `∑_{k ≠ 0} |B̂(k)| (k, m) ≤ m τ(m) (1 + log m)` for a progression
`B = {r + q j : α ≤ j < β}` with `q` a unit mod `m`, of any length. -/
theorem sum_norm_transform_image_mul_gcd_le {q : ℕ} (hq : IsUnit (q : ZMod m)) (r α β : ℕ) :
    ∑ k ∈ univ.erase 0,
        ‖transform (fun a : ℕ => (a : ZMod m)) ((Ico α β).image fun j => r + q * j) k‖ *
          Nat.gcd k.val m ≤
      m * m.divisors.card * (1 + Real.log m) := by
  have hw0 : ∀ w : ZMod m, 0 ≤ freqWeight w := fun w => by unfold freqWeight; positivity
  have hnq : IsUnit (-(q : ZMod m)) := hq.neg
  calc ∑ k ∈ univ.erase 0,
        ‖transform (fun a : ℕ => (a : ZMod m)) ((Ico α β).image fun j => r + q * j) k‖ *
          Nat.gcd k.val m
      ≤ ∑ k ∈ univ.erase 0, freqWeight (-(k * (q : ZMod m))) *
          Nat.gcd (-(k * (q : ZMod m))).val m := by
        refine sum_le_sum fun k hk => ?_
        rw [← mul_neg, gcd_val_mul_of_isUnit k hnq]
        gcongr
        rw [mul_neg]
        exact norm_transform_image_le q r α β ((hq.mul_left_eq_zero).not.2 (ne_of_mem_erase hk))
    _ ≤ ∑ k : ZMod m, freqWeight (-(k * (q : ZMod m))) *
          Nat.gcd (-(k * (q : ZMod m))).val m :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun k _ _ => by
          have := hw0 (-(k * (q : ZMod m)))
          positivity
    _ = ∑ w : ZMod m, freqWeight w * Nat.gcd w.val m :=
        Fintype.sum_equiv ((Units.mulRight hq.unit).trans (Equiv.neg _)) _
          (fun w => freqWeight w * Nat.gcd w.val m) fun h => by simp [Units.mulRight]
    _ ≤ m * ∑ j ∈ Icc 1 m, (Nat.gcd j m : ℝ) / j :=
        sum_freqWeight_mul_le (fun j => (Nat.gcd j m : ℝ)) (fun _ => Nat.cast_nonneg _)
          fun j hj => by rw [Nat.gcd_self_sub_left hj.le]
    _ ≤ m * (m.divisors.card * (1 + Real.log m)) := by gcongr; exact sum_gcd_div_le
    _ = _ := by ring

/-- **The box bound for progressions.** Let `A = {r + q j : α ≤ j < β}` with `β - α ≤ m` and
`B = {r' + q' j : γ ≤ j < δ}`, with `q, q'` units mod `m`. If `|Ŝ_G(h, k)| ≤ X (k, m)` for
`k ≠ 0`, then `|#{(a, b) ∈ A × B : (a, b) mod m ∈ G} - (|B|/m) Mc| ≤ X τ(m) (2 + log m)²`. -/
theorem abs_card_filter_mem_prog_sub_le (G : Finset (ZMod m × ZMod m)) {q q' : ℕ}
    (hq : IsUnit (q : ZMod m)) (hq' : IsUnit (q' : ZMod m)) (r r' α β γ δ : ℕ)
    (hA : β - α ≤ m) {X : ℝ} (hX0 : 0 ≤ X)
    (hX : ∀ h k, k ≠ 0 → ‖pairSum G h k‖ ≤ X * Nat.gcd k.val m) :
    |(#{p ∈ ((Ico α β).image fun j => r + q * j) ×ˢ ((Ico γ δ).image fun j => r' + q' * j) |
          ((p.1 : ZMod m), (p.2 : ZMod m)) ∈ G} : ℝ) -
        (#((Ico γ δ).image fun j => r' + q' * j) : ℝ) / m *
          #{p ∈ ((Ico α β).image fun j => r + q * j) ×ˢ (univ : Finset (ZMod m)) |
            ((p.1 : ZMod m), p.2) ∈ G}| ≤
      X * m.divisors.card * (2 + Real.log m) ^ 2 := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 (NeZero.pos m)
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  refine (abs_card_filter_mem_sub_le G (fun a : ℕ => (a : ZMod m)) (fun a : ℕ => (a : ZMod m))
    _ _ hX).trans ?_
  have h₁ := sum_norm_transform_image_le hq r α β hA
  have h₂ := sum_norm_transform_image_mul_gcd_le hq' r' γ δ
  have h₃ : ∑ k ∈ univ.erase 0, ‖transform (fun a : ℕ => (a : ZMod m))
        ((Ico γ δ).image fun j => r' + q' * j) k‖ * (X * Nat.gcd k.val m) ≤
      X * (m * m.divisors.card * (1 + Real.log m)) := by
    calc _ = X * ∑ k ∈ univ.erase 0, ‖transform (fun a : ℕ => (a : ZMod m))
          ((Ico γ δ).image fun j => r' + q' * j) k‖ * Nat.gcd k.val m := by
          rw [mul_sum]
          exact sum_congr rfl fun k _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h₂ hX0
  calc ((m : ℝ) ^ 2)⁻¹ * (∑ h : ZMod m, ‖transform (fun a : ℕ => (a : ZMod m))
          ((Ico α β).image fun j => r + q * j) h‖) *
        ∑ k ∈ univ.erase 0, ‖transform (fun a : ℕ => (a : ZMod m))
          ((Ico γ δ).image fun j => r' + q' * j) k‖ * (X * Nat.gcd k.val m)
      ≤ ((m : ℝ) ^ 2)⁻¹ * (m * (2 + Real.log m)) *
          (X * (m * m.divisors.card * (1 + Real.log m))) := by
        gcongr
    _ = X * m.divisors.card * ((2 + Real.log m) * (1 + Real.log m)) := by
        field_simp
    _ ≤ X * m.divisors.card * (2 + Real.log m) ^ 2 := by
        gcongr
        nlinarith

end Erdos408.OneSided.RootResidue
