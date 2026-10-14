module

public import Erdos408.OneSided.Model

/-!
# Neighbors in the root box

PD `mem:neighbor` at a real root, for the crude edge bound (`exists_phasedEdge_normLe` in
`Moment/Phased.lean`).

* `card_filter_det_le`, `card_filter_det_le'`: for a position `w` of the root box and a value
  `n`, at most `16` positions `z` of the box have `det(w, z) = n` (or `det(z, w) = n`). Two
  such `z` differ by `m w` for an integer `m`, since `w` is primitive, and then
  `u τ(z) ∈ [U, 16U]` and `u τ(w) ≥ U` leave one `z` for each value of `⌊u τ(z)/U⌋`.
* `sum_dvd_le_of_card_le`: if the fibers of `e` have at most `16` points, then a sum over the
  points `z` with `D ∣ e(z)` of `g(e(z)/D)`, for `g ≥ 0` supported in `[-M, M]`, is at most
  `16 ∑_{|t| ≤ M} g(t)`.
-/

@[expose] public section

namespace Erdos408.OneSided

open Finset

/-- **The neighbor count** (PD `mem:neighbor`): for a position `w` of the root box with
`U > 0` and a value `n`, at most `16` positions `z` of the box have `det(w, z) = n`. -/
theorem card_filter_det_le {U V u v r : ℝ} (hU : 0 < U) {w : ℤ × ℤ}
    (hw : w ∈ rootPositions U V u v r) (n : ℤ) :
    ((rootPositions U V u v r).filter fun z => w.1 * z.2 - w.2 * z.1 = n).card ≤ 16 := by
  unfold rootPositions at hw
  rw [mem_filter] at hw
  obtain ⟨-, hgcd, hwU, -⟩ := hw
  -- `w` is primitive: `α w₁ + β w₂ = 1`
  obtain ⟨α, β, hαβ⟩ := Int.isCoprime_iff_gcd_eq_one.2 hgcd
  have hbox : ∀ z ∈ (rootPositions U V u v r).filter fun z => w.1 * z.2 - w.2 * z.1 = n,
      U ≤ u * tau r z ∧ u * tau r z ≤ 16 * U ∧ w.1 * z.2 - w.2 * z.1 = n := by
    intro z hz
    unfold rootPositions at hz
    simp only [mem_filter] at hz
    exact ⟨hz.1.2.2.1, hz.1.2.2.2.1, hz.2⟩
  calc _ ≤ (Icc (1 : ℤ) 16).card := by
        refine card_le_card_of_injOn (fun z => ⌊u * tau r z / U⌋) (fun z hz => ?_)
          (fun z hz z' hz' h => ?_)
        · -- `u τ(z)/U ∈ [1, 16]`
          obtain ⟨h₁, h₂, -⟩ := hbox z hz
          have h₁' : (1 : ℝ) ≤ u * tau r z / U := (one_le_div hU).2 h₁
          have h₂' : u * tau r z / U ≤ 16 := (div_le_iff₀ hU).2 h₂
          refine mem_coe.2 (mem_Icc.2 ⟨Int.le_floor.2 (by exact_mod_cast h₁'), ?_⟩)
          have := Int.floor_le (u * tau r z / U)
          exact_mod_cast this.trans h₂'
        · -- the difference is `m w` with `|m| u τ(w) < U ≤ u τ(w)`, so `m = 0`
          obtain ⟨-, -, hzn⟩ := hbox z hz
          obtain ⟨-, -, hzn'⟩ := hbox z' hz'
          have hlt := Int.abs_sub_lt_one_of_floor_eq_floor h
          set m := α * (z.1 - z'.1) + β * (z.2 - z'.2) with hm
          have hm₁ : z.1 - z'.1 = m * w.1 := by
            linear_combination (-(z.1 - z'.1)) * hαβ + β * (hzn' - hzn)
          have hm₂ : z.2 - z'.2 = m * w.2 := by
            linear_combination (-(z.2 - z'.2)) * hαβ + α * (hzn - hzn')
          have htau : u * tau r z - u * tau r z' = m * (u * tau r w) := by
            have h₁ : (z.1 : ℝ) - z'.1 = m * w.1 := by exact_mod_cast hm₁
            have h₂ : (z.2 : ℝ) - z'.2 = m * w.2 := by exact_mod_cast hm₂
            unfold tau
            linear_combination u * h₁ + u * r * h₂
          have hm0 : m = 0 := by
            by_contra hm0
            have h1m : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
            rw [← sub_div, abs_div, abs_of_pos hU, div_lt_one hU, htau, abs_mul,
              abs_of_pos (hU.trans_le hwU)] at hlt
            nlinarith
          rw [hm0, zero_mul, sub_eq_zero] at hm₁ hm₂
          exact Prod.ext hm₁ hm₂
    _ = 16 := by simp

/-- **The neighbor count** with the fixed position second: at most `16` positions `z` of the
box have `det(z, w) = n`. -/
theorem card_filter_det_le' {U V u v r : ℝ} (hU : 0 < U) {w : ℤ × ℤ}
    (hw : w ∈ rootPositions U V u v r) (n : ℤ) :
    ((rootPositions U V u v r).filter fun z => z.1 * w.2 - z.2 * w.1 = n).card ≤ 16 := by
  calc _ = ((rootPositions U V u v r).filter fun z => w.1 * z.2 - w.2 * z.1 = -n).card := by
        congr 1
        refine filter_congr fun z _ => ?_
        constructor <;> intro h <;> linear_combination -h
    _ ≤ 16 := card_filter_det_le hU hw (-n)

/-- **The sum over the neighbors**: if every fiber of `e` on `T` has at most `16` points, then
`∑_{z ∈ T, D ∣ e(z)} g(e(z)/D) ≤ 16 ∑_{|t| ≤ M} g(t)` for `g ≥ 0` vanishing outside
`[-M, M]`. -/
theorem sum_dvd_le_of_card_le {α : Type*} {T : Finset α} {e : α → ℤ}
    (he : ∀ n, (T.filter fun z => e z = n).card ≤ 16) {D : ℕ} (hD : 0 < D) {M : ℕ}
    {g : ℤ → ℝ} (hg : ∀ t, 0 ≤ g t) (hgM : ∀ t, g t ≠ 0 → t ∈ Icc (-(M : ℤ)) M) :
    ∑ z ∈ T, (if (D : ℤ) ∣ e z then g (e z / D) else 0) ≤
      16 * ∑ t ∈ Icc (-(M : ℤ)) M, g t := by
  have hD' : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  -- each term is at most the sum over `t` of `[e(z) = D t] g(t)`
  have hpt : ∀ z, (if (D : ℤ) ∣ e z then g (e z / D) else 0) ≤
      ∑ t ∈ Icc (-(M : ℤ)) M, if e z = D * t then g t else 0 := by
    intro z
    have hnn : 0 ≤ ∑ t ∈ Icc (-(M : ℤ)) M, if e z = D * t then g t else 0 :=
      sum_nonneg fun t _ => by split_ifs; exacts [hg t, le_rfl]
    split_ifs with hdvd
    · obtain ⟨t₀, ht₀⟩ := hdvd
      rw [show e z / D = t₀ by rw [ht₀, Int.mul_ediv_cancel_left _ hD']]
      by_cases hg₀ : g t₀ = 0
      · rw [hg₀]
        exact hnn
      · calc g t₀ = if e z = D * t₀ then g t₀ else 0 := (ite_eq_left ht₀).symm
          _ ≤ ∑ t ∈ Icc (-(M : ℤ)) M, if e z = D * t then g t else 0 :=
            single_le_sum (f := fun t => if e z = D * t then g t else 0)
              (fun t _ => by split_ifs; exacts [hg t, le_rfl]) (hgM t₀ hg₀)
    · exact hnn
  calc ∑ z ∈ T, (if (D : ℤ) ∣ e z then g (e z / D) else 0)
      ≤ ∑ z ∈ T, ∑ t ∈ Icc (-(M : ℤ)) M, if e z = D * t then g t else 0 :=
        sum_le_sum fun z _ => hpt z
    _ = ∑ t ∈ Icc (-(M : ℤ)) M, ((T.filter fun z => e z = D * t).card : ℝ) * g t := by
        rw [sum_comm]
        refine sum_congr rfl fun t _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ ∑ t ∈ Icc (-(M : ℤ)) M, 16 * g t :=
        sum_le_sum fun t _ => mul_le_mul_of_nonneg_right (by exact_mod_cast he _) (hg t)
    _ = 16 * ∑ t ∈ Icc (-(M : ℤ)) M, g t := (mul_sum _ _ _).symm

end Erdos408.OneSided
