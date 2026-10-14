import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Erdos408.OneSided.Moment.Phased.Neighbor

/-!
# The line count

PD `mem:line-count` for the dirty comparison edges (M8, `eventually_edgeComp_normLe` in
`Moment/Edge.lean`), without the lattice shape. Fix a good position `w` of the root box with
complement `c = w_w`, a pad product `D` and a prime `p ∤ D`. A position `z` with
`det(w, z) = D t` is `z = m w + D t c`, and the box gives `0 ≤ m + t α ≤ 16` with
`α = D τ(c)/τ(w)` (`mem:neighbor`). A prescribed line `[z]_p = ℓ` is one nonzero linear
congruence `A · z ≡ 0 (mod p)`, hence `m ≡ c₀ t (mod p)` or `p ∣ t`. In the first case
`‖t (c₀ + α)/p‖ ≤ 16/p`.

* `card_block_le`: for a rational approximation `|q' β - a'| ≤ η` with `(a', q') = 1`, at most
  `2q'(δ + η) + 1` integers `t` of an interval of length `q'` have `‖t β‖ ≤ δ`: the integers
  `t a' - q' round(t β)` are distinct and lie in an interval of length `2q'(δ + η)`.
* `card_filter_circleDist_le`: hence at most `(2M/q' + 1)(2q'(δ + η) + 1)` integers
  `|t| ≤ M` have `‖t β‖ ≤ δ`.
* `exists_approx_of_good`: test (i), `‖l α‖ > Y^{-0.7}` for `1 ≤ l ≤ Y^{0.2}`, and Dirichlet's
  approximation with denominators at most `p Y^{0.7}` give an approximation of
  `β = (c₀ + α)/p` with `Y^{0.2} < q' ≤ p Y^{0.7} + 1`.
* `exists_lineForm`: a line `[z]_p = ℓ` implies a congruence `A · z ≡ 0 (mod p)` with `A` not
  zero mod `p`.
* `card_filter_line_le`: the positions `z` of the box with `det(w, z) = D t`, `|t| ≤ M ≤ 6Y`,
  and `[z]_p = ℓ` number at most `2^13 (Y/p + Y^{0.8})`.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real

/-! ### The circle distance -/

/-- `‖t‖ ≤ |t - n|` for every integer `n`. -/
private theorem circleDist_le_abs_sub' (t : ℝ) (n : ℤ) : circleDist t ≤ |t - n| := round_le t n

/-! ### Counting small multiples -/

/-- **One block**: if `|q' β - a'| ≤ η` with `(a', q') = 1`, then at most `2q'(δ + η) + 1`
integers `t ∈ [t₀, t₀ + q')` have `‖t β‖ ≤ δ`. The map `t ↦ t a' - q' round(t β)` is injective
on the block, and `|t a' - q' round(t β) + t₀ (q' β - a')| ≤ q'(δ + η)`. -/
theorem card_block_le {β δ η : ℝ} {a' : ℤ} {q' : ℕ} (hq : 0 < q') (hcop : IsCoprime a' q')
    (hη : |q' * β - a'| ≤ η) (hδ : 0 ≤ δ) (t₀ : ℤ) (T : Finset ℤ)
    (hT : ∀ t ∈ T, t₀ ≤ t ∧ t < t₀ + q' ∧ circleDist (t * β) ≤ δ) :
    (T.card : ℝ) ≤ 2 * q' * (δ + η) + 1 := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hη
  set e := (q' : ℝ) * β - a' with he
  set R := (q' : ℝ) * (δ + η) with hR
  set g : ℤ → ℤ := fun t => t * a' - q' * round (t * β) with hg
  -- `g` lands in an interval of length `2R` around `-t₀ e`
  have hgb : ∀ t ∈ T, |(g t : ℝ) + t₀ * e| ≤ R := by
    intro t ht
    obtain ⟨h₁, h₂, h₃⟩ := hT t ht
    have hs0 : (0 : ℝ) ≤ t - t₀ := by
      have : (t₀ : ℝ) ≤ t := by exact_mod_cast h₁
      linarith
    have hsq : (t : ℝ) - t₀ ≤ q' := by
      have : (t : ℝ) < t₀ + q' := by exact_mod_cast h₂
      linarith
    have hkey : (g t : ℝ) + t₀ * e = q' * (t * β - round (t * β)) - (t - t₀) * e := by
      simp only [hg, he]
      push_cast
      ring
    rw [hkey]
    calc |(q' : ℝ) * (t * β - round (t * β)) - (t - t₀) * e|
        ≤ |(q' : ℝ) * (t * β - round (t * β))| + |(t - t₀) * e| := abs_sub _ _
      _ = q' * circleDist (t * β) + (t - t₀) * |e| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hs0, Nat.abs_cast]
          rfl
      _ ≤ q' * δ + q' * η :=
          add_le_add (mul_le_mul_of_nonneg_left h₃ (Nat.cast_nonneg _))
            (mul_le_mul hsq hη (abs_nonneg _) (Nat.cast_nonneg _))
      _ = R := by rw [hR]; ring
  -- `g` is injective on the block
  have hinj : Set.InjOn g T := by
    intro t₁ ht₁ t₂ ht₂ h
    simp only [hg] at h
    have hdvd : (q' : ℤ) ∣ (t₁ - t₂) * a' :=
      ⟨round (t₁ * β) - round (t₂ * β), by linear_combination h⟩
    have hdvd' : (q' : ℤ) ∣ t₁ - t₂ := hcop.symm.dvd_of_dvd_mul_right hdvd
    have hlt : |t₁ - t₂| < q' := by
      obtain ⟨a₁, b₁, -⟩ := hT t₁ ht₁
      obtain ⟨a₂, b₂, -⟩ := hT t₂ ht₂
      rw [abs_lt]
      constructor <;> omega
    exact sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd hdvd' hlt)
  -- count the interval
  set lo := ⌈-(t₀ * e) - R⌉ with hlo
  set hi := ⌊-(t₀ * e) + R⌋ with hhi
  have hmaps : ∀ t ∈ T, g t ∈ Icc lo hi := by
    intro t ht
    have h := abs_le.1 (hgb t ht)
    refine mem_Icc.2 ⟨Int.ceil_le.2 (by linarith), Int.le_floor.2 (by linarith)⟩
  have hcard := card_le_card_of_injOn g hmaps hinj
  rw [Int.card_Icc] at hcard
  have hcast : (T.card : ℝ) ≤ ((hi + 1 - lo).toNat : ℝ) := by exact_mod_cast hcard
  have htoNat : (((hi + 1 - lo).toNat : ℤ) : ℝ) = max ((hi + 1 - lo : ℤ) : ℝ) 0 := by
    rw [Int.toNat_eq_max]
    push_cast
    rfl
  have hhi' : (hi : ℝ) ≤ -(t₀ * e) + R := Int.floor_le _
  have hlo' : -(t₀ * e) - R ≤ (lo : ℝ) := Int.le_ceil _
  have hR0 : 0 ≤ R := by positivity
  calc (T.card : ℝ) ≤ ((hi + 1 - lo).toNat : ℝ) := hcast
    _ = max ((hi + 1 - lo : ℤ) : ℝ) 0 := by rw [← htoNat]; rfl
    _ ≤ 2 * R + 1 := by
        refine max_le ?_ (by linarith)
        push_cast
        linarith
    _ = 2 * q' * (δ + η) + 1 := by rw [hR]; ring

/-- **The small multiples**: if `|q' β - a'| ≤ η` with `(a', q') = 1`, then at most
`(2M/q' + 1)(2q'(δ + η) + 1)` integers `|t| ≤ M` have `‖t β‖ ≤ δ`: split `[-M, M]` into
`⌊2M/q'⌋ + 1` blocks of length `q'`. -/
theorem card_filter_circleDist_le {β δ η : ℝ} {a' : ℤ} {q' : ℕ} (hq : 0 < q')
    (hcop : IsCoprime a' q') (hη : |q' * β - a'| ≤ η) (hδ : 0 ≤ δ) (M : ℕ) :
    (((Icc (-(M : ℤ)) M).filter fun t : ℤ => circleDist ((t : ℝ) * β) ≤ δ).card : ℝ) ≤
      (2 * M / q' + 1) * (2 * q' * (δ + η) + 1) := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hη
  set T := (Icc (-(M : ℤ)) M).filter fun t : ℤ => circleDist ((t : ℝ) * β) ≤ δ with hTdef
  set nb := 2 * M / q' + 1 with hnb
  set f : ℤ → ℕ := fun t => ((t + M) / q').toNat with hf
  have hq' : (0 : ℤ) < q' := by exact_mod_cast hq
  have hmaps : ∀ t ∈ T, f t ∈ range nb := by
    intro t ht
    obtain ⟨h₁, h₂⟩ := mem_Icc.1 (mem_filter.1 ht).1
    have h0 : 0 ≤ (t + M) / q' := Int.ediv_nonneg (by omega) hq'.le
    have hle : (t + M) / q' ≤ ((2 * M : ℕ) : ℤ) / q' := Int.ediv_le_ediv hq' (by push_cast; omega)
    rw [mem_range, hnb, Nat.lt_succ_iff]
    have : (((t + M) / q').toNat : ℤ) ≤ ((2 * M / q' : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0]
      push_cast
      exact_mod_cast hle
    exact_mod_cast this
  -- each fiber is a block
  have hblock : ∀ b ∈ range nb, ((T.filter fun t => f t = b).card : ℝ) ≤
      2 * q' * (δ + η) + 1 := by
    intro b _
    refine card_block_le hq hcop hη hδ (b * q' - M) _ fun t ht => ?_
    obtain ⟨ht, hfb⟩ := mem_filter.1 ht
    obtain ⟨hIcc, hcd⟩ := mem_filter.1 ht
    obtain ⟨h₁, -⟩ := mem_Icc.1 hIcc
    have h0 : 0 ≤ (t + M) / q' := Int.ediv_nonneg (by omega) hq'.le
    have hb : (t + M) / q' = b := by
      have := congrArg (fun n : ℕ => (n : ℤ)) hfb
      simp only [hf, Int.toNat_of_nonneg h0] at this
      exact this
    have hlow := Int.ediv_mul_le (t + M) hq'.ne'
    have hhigh := Int.lt_ediv_add_one_mul_self (t + M) hq'
    rw [hb] at hlow hhigh
    refine ⟨by linarith, by linarith, hcd⟩
  have hsum := card_eq_sum_card_fiberwise hmaps
  have hnb' : (nb : ℝ) ≤ 2 * M / q' + 1 := by
    rw [hnb]
    push_cast
    have := Nat.cast_div_le (α := ℝ) (m := 2 * M) (n := q')
    push_cast at this
    linarith
  calc (T.card : ℝ) = ∑ b ∈ range nb, ((T.filter fun t => f t = b).card : ℝ) := by
        exact_mod_cast hsum
    _ ≤ ∑ _b ∈ range nb, (2 * q' * (δ + η) + 1) := sum_le_sum hblock
    _ = nb * (2 * q' * (δ + η) + 1) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ (2 * M / q' + 1) * (2 * q' * (δ + η) + 1) :=
        mul_le_mul_of_nonneg_right hnb' (by positivity)

/-! ### The rational approximation -/

/-- **The approximation from test (i)**: if `‖l α‖ > Y^{-0.7}` for `1 ≤ l ≤ Y^{0.2}`, then
`β = (c₀ + α)/p` has an approximation `|q' β - a'| ≤ 1/q'` with `(a', q') = 1` and
`Y^{0.2} < q' ≤ p Y^{0.7} + 1`. Dirichlet with denominators at most `n = ⌈p Y^{0.7}⌉` gives
`|q' β - a'| ≤ 1/(n + 1)`, so `‖q' α‖ ≤ p |q' β - a'| < Y^{-0.7}`. -/
theorem exists_approx_of_good {α Y : ℝ} (hY : 1 ≤ Y)
    (hgood : ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (1 / 5 : ℝ) →
      Y ^ (-(7 / 10 : ℝ)) < circleDist (l * α))
    {p : ℕ} (hp : 0 < p) (c₀ : ℤ) :
    ∃ a' : ℤ, ∃ q' : ℕ, 0 < q' ∧ IsCoprime a' q' ∧
      |q' * ((c₀ + α) / p) - a'| ≤ 1 / q' ∧ Y ^ (1 / 5 : ℝ) < q' ∧
        (q' : ℝ) ≤ p * Y ^ (7 / 10 : ℝ) + 1 := by
  set β := (c₀ + α) / p with hβ
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hY0 : 0 < Y := by linarith
  have hY7 : 0 < Y ^ (7 / 10 : ℝ) := Real.rpow_pos_of_pos hY0 _
  set n := ⌈(p : ℝ) * Y ^ (7 / 10 : ℝ)⌉₊ with hn
  have hn0 : 0 < n := Nat.ceil_pos.2 (by positivity)
  have hnle : (p : ℝ) * Y ^ (7 / 10 : ℝ) ≤ n := Nat.le_ceil _
  obtain ⟨Q, hQ, hQden⟩ := Real.exists_rat_abs_sub_le_and_den_le β hn0
  have hd0 : (0 : ℝ) < Q.den := by exact_mod_cast Q.pos
  have hcop : IsCoprime Q.num (Q.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact Q.reduced
  -- `|q' β - a'| ≤ 1/(n + 1)`
  have happ : |(Q.den : ℝ) * β - Q.num| ≤ 1 / ((n : ℝ) + 1) := by
    have hQ' : (Q : ℝ) = Q.num / Q.den := by
      rw [Rat.cast_def]
    have : (Q.den : ℝ) * β - Q.num = Q.den * (β - Q) := by
      rw [hQ']
      field_simp
    rw [this, abs_mul, Nat.abs_cast]
    calc (Q.den : ℝ) * |β - Q| ≤ Q.den * (1 / ((n + 1) * Q.den)) :=
          mul_le_mul_of_nonneg_left hQ hd0.le
      _ = 1 / ((n : ℝ) + 1) := by field_simp
  have hn1 : (Q.den : ℝ) < n + 1 := by
    have : (Q.den : ℝ) ≤ n := by exact_mod_cast hQden
    linarith
  refine ⟨Q.num, Q.den, Q.pos, hcop, ?_, ?_, ?_⟩
  · refine happ.trans ?_
    exact one_div_le_one_div_of_le hd0 hn1.le
  · -- `‖q' α‖ < Y^{-0.7}` rules out `q' ≤ Y^{0.2}`
    by_contra hle
    push Not at hle
    have hlt : circleDist (Q.den * α) < Y ^ (-(7 / 10 : ℝ)) := by
      have hid : (Q.den : ℝ) * α - ((p * Q.num - Q.den * c₀ : ℤ) : ℝ) =
          p * ((Q.den : ℝ) * β - Q.num) := by
        rw [hβ]
        push_cast
        field_simp
        ring
      calc circleDist (Q.den * α) ≤ |(Q.den : ℝ) * α - ((p * Q.num - Q.den * c₀ : ℤ) : ℝ)| :=
            circleDist_le_abs_sub' _ _
        _ = p * |(Q.den : ℝ) * β - Q.num| := by rw [hid, abs_mul, Nat.abs_cast]
        _ ≤ p * (1 / ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left happ hp'.le
        _ < p * (1 / (p * Y ^ (7 / 10 : ℝ))) := by
            refine mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt (by positivity) ?_) hp'
            linarith
        _ = Y ^ (-(7 / 10 : ℝ)) := by
            rw [Real.rpow_neg hY0.le]
            field_simp
    exact absurd (hgood Q.den Q.pos hle) (not_lt.2 hlt.le)
  · have : (Q.den : ℝ) ≤ n := by exact_mod_cast hQden
    have hn' : (n : ℝ) < p * Y ^ (7 / 10 : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith

/-! ### Lines as congruences -/

/-- **A line is a congruence**: for a prime `p` and a line `ℓ`, there is an integer linear form
`A`, not zero mod `p`, with `p ∣ A · z` whenever `[z]_p = ℓ`. For `ℓ < p` it is
`ℓ z₁ - z₂`, and for `ℓ ≥ p` it is `z₁`. -/
theorem exists_lineForm {p : ℕ} (hp : p.Prime) (ℓ : ℕ) :
    ∃ A₁ A₂ : ℤ, ¬ ((p : ℤ) ∣ A₁ ∧ (p : ℤ) ∣ A₂) ∧
      ∀ z : ℤ × ℤ, lineOf p z = ℓ → (p : ℤ) ∣ A₁ * z.1 + A₂ * z.2 := by
  have hF : Fact p.Prime := ⟨hp⟩
  have hp1 : ¬ (p : ℤ) ∣ 1 := by
    rw [Int.natCast_dvd_ofNat]
    exact hp.not_dvd_one
  by_cases hℓ : ℓ < p
  · refine ⟨ℓ, -1, fun h => hp1 (by simpa using h.2), fun z hz => ?_⟩
    unfold lineOf at hz
    split_ifs at hz with h0
    · omega
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hℓ' : ((ℓ : ℕ) : ZMod p) = (z.2 : ZMod p) * (z.1 : ZMod p)⁻¹ := by
        rw [← hz, ZMod.natCast_zmod_val]
      have hcast : (((ℓ : ℤ) * z.1 + -1 * z.2 : ℤ) : ZMod p) =
          ((ℓ : ℕ) : ZMod p) * (z.1 : ZMod p) - (z.2 : ZMod p) := by
        push_cast
        ring
      rw [hcast, hℓ', mul_assoc, inv_mul_cancel₀ h0, mul_one, sub_self]
  · refine ⟨1, 0, fun h => hp1 h.1, fun z hz => ?_⟩
    unfold lineOf at hz
    split_ifs at hz with h0
    · rw [one_mul, zero_mul, add_zero, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h0
    · exact absurd (hz ▸ ZMod.val_lt _) hℓ

/-! ### The line count -/

/-- **The line count** (PD `mem:line-count`, without the lattice shape): let `w` be a position
of the root box, `α = D τ(w_w)/τ(w)` with `‖l α‖ > Y^{-0.7}` for `1 ≤ l ≤ Y^{0.2}` (test (i)),
and `p ∤ D` a prime. Then at most `2^13 (Y/p + Y^{0.8})` positions `z` of the box have
`det(w, z) = D t` with `|t| ≤ M ≤ 6Y` and `[z]_p = ℓ`. -/
theorem card_filter_line_le {U V u v r Y : ℝ} (hU : 0 < U) (hY : 1 ≤ Y) {w : ℤ × ℤ}
    (hw : w ∈ rootPositions U V u v r) {D : ℕ}
    (hgood : ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (1 / 5 : ℝ) →
      Y ^ (-(7 / 10 : ℝ)) < circleDist (l * D * (tau r (complement w) / tau r w)))
    {p : ℕ} (hp : p.Prime) (hpD : ¬ p ∣ D) (ℓ : ℕ) {M : ℕ} (hM : (M : ℝ) ≤ 6 * Y) :
    (((rootPositions U V u v r).filter fun z =>
        (∃ t ∈ Icc (-(M : ℤ)) M, w.1 * z.2 - w.2 * z.1 = D * t) ∧ lineOf p z = ℓ).card : ℝ) ≤
      2 ^ 13 * (Y / p + Y ^ (4 / 5 : ℝ)) := by
  classical
  set c := complement w with hc
  set α := (D : ℝ) * (tau r c / tau r w) with hα
  have hp0 : 0 < p := hp.pos
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hY0 : 0 < Y := by linarith
  have hY45 : 1 ≤ Y ^ (4 / 5 : ℝ) := Real.one_le_rpow hY (by norm_num)
  -- the box facts at `w`
  have hw' := hw
  unfold rootPositions at hw'
  rw [mem_filter] at hw'
  obtain ⟨-, hgcd, hwU, -⟩ := hw'
  have huw : 0 < u * tau r w := hU.trans_le hwU
  -- `det(w, c) = 1`
  have hdetc : w.1 * c.2 - w.2 * c.1 = 1 := by
    simp only [hc, complement]
    have := Int.gcd_eq_gcd_ab w.1 w.2
    rw [hgcd] at this
    push_cast at this
    linarith
  -- the linear form of the line
  obtain ⟨A₁, A₂, hA0, hA⟩ := exists_lineForm hp ℓ
  set Aw := A₁ * w.1 + A₂ * w.2 with hAw
  set Ac := A₁ * c.1 + A₂ * c.2 with hAc
  -- `z = m w + n c` with `m = det(z, c)` and `n = det(w, z)`
  have hdecomp : ∀ z : ℤ × ℤ, z.1 = (z.1 * c.2 - z.2 * c.1) * w.1 + (w.1 * z.2 - w.2 * z.1) * c.1 ∧
      z.2 = (z.1 * c.2 - z.2 * c.1) * w.2 + (w.1 * z.2 - w.2 * z.1) * c.2 := fun z =>
    ⟨by linear_combination (-z.1) * hdetc, by linear_combination (-z.2) * hdetc⟩
  -- the strip: `0 ≤ m + t α ≤ 16`
  have hstrip : ∀ z ∈ rootPositions U V u v r, ∀ t : ℤ, w.1 * z.2 - w.2 * z.1 = D * t →
      0 ≤ ((z.1 * c.2 - z.2 * c.1 : ℤ) : ℝ) + t * α ∧
        ((z.1 * c.2 - z.2 * c.1 : ℤ) : ℝ) + t * α ≤ 16 := by
    intro z hz t ht
    unfold rootPositions at hz
    rw [mem_filter] at hz
    obtain ⟨-, -, hzU, hzU', -⟩ := hz
    have hτ : tau r z = ((z.1 * c.2 - z.2 * c.1 : ℤ) : ℝ) * tau r w + (D * t : ℤ) * tau r c := by
      obtain ⟨h₁, h₂⟩ := hdecomp z
      rw [← ht]
      unfold tau
      have h₁' : (z.1 : ℝ) = ((z.1 * c.2 - z.2 * c.1 : ℤ) : ℝ) * w.1 +
          ((w.1 * z.2 - w.2 * z.1 : ℤ) : ℝ) * c.1 := by exact_mod_cast h₁
      have h₂' : (z.2 : ℝ) = ((z.1 * c.2 - z.2 * c.1 : ℤ) : ℝ) * w.2 +
          ((w.1 * z.2 - w.2 * z.1 : ℤ) : ℝ) * c.2 := by exact_mod_cast h₂
      rw [h₁', h₂']
      ring
    have hτw : tau r w ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at huw
      exact lt_irrefl _ huw
    have hratio : ((z.1 * c.2 - z.2 * c.1 : ℤ) : ℝ) + t * α = (u * tau r z) / (u * tau r w) := by
      rw [hτ, hα]
      have hu : u ≠ 0 := by
        rintro rfl
        rw [zero_mul] at huw
        exact lt_irrefl _ huw
      push_cast
      field_simp
    rw [hratio]
    refine ⟨div_nonneg (hU.le.trans hzU) huw.le, ?_⟩
    rw [div_le_iff₀ huw]
    nlinarith
  -- the admissible values of `t`, by cases on `A · w mod p`
  have hcount : ∃ β δ η : ℝ, ∃ a' : ℤ, ∃ q' : ℕ, 0 < q' ∧ IsCoprime a' q' ∧
      |q' * β - a'| ≤ η ∧ 0 ≤ δ ∧
      (∀ z ∈ rootPositions U V u v r, ∀ t : ℤ, w.1 * z.2 - w.2 * z.1 = D * t →
        lineOf p z = ℓ → circleDist ((t : ℝ) * β) ≤ δ) ∧
      (2 * M / q' + 1) * (2 * q' * (δ + η) + 1) ≤ 384 * Y / p + 103 * Y ^ (4 / 5 : ℝ) := by
    by_cases hAw0 : (p : ℤ) ∣ Aw
    · -- `p ∣ t`
      have hAc0 : ¬ (p : ℤ) ∣ Ac := by
        intro hAc0
        refine hA0 ⟨?_, ?_⟩
        · have : A₁ = c.2 * Aw - w.2 * Ac := by
            simp only [hAw, hAc]
            linear_combination (-A₁) * hdetc
          rw [this]
          exact dvd_sub (dvd_mul_of_dvd_right hAw0 _) (dvd_mul_of_dvd_right hAc0 _)
        · have : A₂ = w.1 * Ac - c.1 * Aw := by
            simp only [hAw, hAc]
            linear_combination (-A₂) * hdetc
          rw [this]
          exact dvd_sub (dvd_mul_of_dvd_right hAc0 _) (dvd_mul_of_dvd_right hAw0 _)
      refine ⟨1 / p, 0, 0, 1, p, hp0, isCoprime_one_left, ?_, le_rfl, ?_, ?_⟩
      · rw [mul_one_div_cancel hp'.ne', Int.cast_one, sub_self, abs_zero]
      · intro z hz t ht hl
        have hdiv := hA z hl
        obtain ⟨h₁, h₂⟩ := hdecomp z
        have hlin : A₁ * z.1 + A₂ * z.2 = (z.1 * c.2 - z.2 * c.1) * Aw + D * t * Ac := by
          rw [← ht]
          simp only [hAw, hAc]
          linear_combination A₁ * h₁ + A₂ * h₂
        rw [hlin] at hdiv
        have hpt : (p : ℤ) ∣ D * t * Ac := (dvd_add_right (dvd_mul_of_dvd_right hAw0 _)).1 hdiv
        have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
        have hpD' : ¬ (p : ℤ) ∣ D := by exact_mod_cast hpD
        obtain ⟨k, hk⟩ : (p : ℤ) ∣ t := by
          rcases hpp.dvd_or_dvd hpt with h | h
          · exact (hpp.dvd_or_dvd h).resolve_left hpD'
          · exact absurd h hAc0
        rw [hk]
        have : ((p * k : ℤ) : ℝ) * (1 / p) = (k : ℝ) := by
          push_cast
          field_simp
        rw [this]
        have := circleDist_le_abs_sub' (k : ℝ) k
        rw [sub_self, abs_zero] at this
        exact this
      · have hM' : (2 * M / p + 1 : ℝ) * (2 * p * (0 + 0) + 1) = 2 * M / p + 1 := by ring
        rw [hM']
        have h1 : 2 * (M : ℝ) / p ≤ 12 * Y / p :=
          div_le_div_of_nonneg_right (by linarith) hp'.le
        have h2 : 12 * Y / p ≤ 384 * Y / p := by
          gcongr
          norm_num
        linarith
    · -- `m ≡ c₀ t (mod p)`, so `‖t (c₀ + α)/p‖ ≤ 16/p`
      have hcopw : IsCoprime Aw p := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        have : Nat.Coprime Aw.natAbs p := by
          rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
          intro h
          exact hAw0 (Int.natCast_dvd.2 h)
        simpa [Int.gcd] using this
      obtain ⟨μ, κ, hμκ⟩ := hcopw
      set c₀ : ℤ := -(D * Ac * μ) with hc₀
      obtain ⟨a', q', hq0, hcop, happ, hqY, hqp⟩ := exists_approx_of_good (α := α) hY
        (fun l hl hlY => by
          have := hgood l hl hlY
          rw [hα, ← mul_assoc]
          exact this) hp0 c₀
      refine ⟨(c₀ + α) / p, 16 / p, 1 / q', a', q', hq0, hcop, happ, by positivity, ?_, ?_⟩
      · intro z hz t ht hl
        have hdiv := hA z hl
        obtain ⟨h₁, h₂⟩ := hdecomp z
        set m := z.1 * c.2 - z.2 * c.1 with hm
        have hlin : A₁ * z.1 + A₂ * z.2 = m * Aw + D * t * Ac := by
          rw [← ht]
          simp only [hAw, hAc, hm]
          linear_combination A₁ * h₁ + A₂ * h₂
        rw [hlin] at hdiv
        -- `m - c₀ t = μ (m A·w + D t A·c) + p m κ`
        have hmc : (p : ℤ) ∣ m - c₀ * t := by
          have : m - c₀ * t = μ * (m * Aw + D * t * Ac) + p * (m * κ) := by
            rw [hc₀]
            linear_combination (-m) * hμκ
          rw [this]
          exact dvd_add (dvd_mul_of_dvd_right hdiv _) (dvd_mul_right _ _)
        obtain ⟨k, hk⟩ := hmc
        obtain ⟨hs₁, hs₂⟩ := hstrip z hz t ht
        rw [← hm] at hs₁ hs₂
        have hid : (t : ℝ) * ((c₀ + α) / p) - ((-k : ℤ) : ℝ) = ((m : ℝ) + t * α) / p := by
          have hk' : (m : ℝ) = c₀ * t + p * k := by
            have := congrArg (fun n : ℤ => (n : ℝ)) hk
            push_cast at this
            linarith
          rw [hk']
          push_cast
          field_simp
          ring
        calc circleDist (t * ((c₀ + α) / p)) ≤ |(t : ℝ) * ((c₀ + α) / p) - ((-k : ℤ) : ℝ)| :=
              circleDist_le_abs_sub' _ _
          _ = ((m : ℝ) + t * α) / p := by
              rw [hid, abs_of_nonneg (div_nonneg hs₁ hp'.le)]
          _ ≤ 16 / p := div_le_div_of_nonneg_right hs₂ hp'.le
      · -- `(2M/q' + 1)(32 q'/p + 3) ≤ 384 Y/p + 103 Y^{0.8}`
        have hq' : (0 : ℝ) < q' := by exact_mod_cast hq0
        have hY15 : 0 < Y ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hY0 _
        have hexp : 2 * (q' : ℝ) * (16 / p + 1 / q') + 1 = 32 * q' / p + 3 := by
          field_simp
          ring
        rw [hexp]
        have hYq : Y / q' ≤ Y ^ (4 / 5 : ℝ) := by
          rw [div_le_iff₀ hq']
          calc Y = Y ^ (4 / 5 : ℝ) * Y ^ (1 / 5 : ℝ) := by
                rw [← Real.rpow_add hY0]
                norm_num
            _ ≤ Y ^ (4 / 5 : ℝ) * q' := by gcongr
        have hY7 : Y ^ (7 / 10 : ℝ) ≤ Y ^ (4 / 5 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
        have hqp' : (q' : ℝ) / p ≤ Y ^ (7 / 10 : ℝ) + 1 := by
          rw [div_le_iff₀ hp']
          have : (1 : ℝ) ≤ p := by exact_mod_cast hp0
          nlinarith [Real.rpow_pos_of_pos hY0 (7 / 10 : ℝ)]
        have hMq : (M : ℝ) / q' ≤ 6 * Y ^ (4 / 5 : ℝ) := by
          calc (M : ℝ) / q' ≤ 6 * Y / q' := by gcongr
            _ = 6 * (Y / q') := by ring
            _ ≤ 6 * Y ^ (4 / 5 : ℝ) := by gcongr
        have hMp : (M : ℝ) / p ≤ 6 * Y / p := by gcongr
        have hexpand : (2 * M / q' + 1 : ℝ) * (32 * q' / p + 3) =
            64 * (M / p) + 6 * (M / q') + 32 * (q' / p) + 3 := by
          field_simp
          ring
        rw [hexpand]
        have : 6 * Y / p * 64 = 384 * Y / p := by ring
        nlinarith
  obtain ⟨β, δ, η, a', q', hq0, hcop, hη, hδ, hgoodt, hbound⟩ := hcount
  -- the positions sit over the admissible `t`, at most `16` over each
  set Tg := (Icc (-(M : ℤ)) M).filter fun t : ℤ => circleDist ((t : ℝ) * β) ≤ δ with hTg
  have hsub : ((rootPositions U V u v r).filter fun z =>
      (∃ t ∈ Icc (-(M : ℤ)) M, w.1 * z.2 - w.2 * z.1 = D * t) ∧ lineOf p z = ℓ) ⊆
        Tg.biUnion fun t => (rootPositions U V u v r).filter fun z =>
          w.1 * z.2 - w.2 * z.1 = D * t := by
    intro z hz
    obtain ⟨hzT, ⟨t, htI, ht⟩, hl⟩ := mem_filter.1 hz
    exact mem_biUnion.2 ⟨t, mem_filter.2 ⟨htI, hgoodt z hzT t ht hl⟩, mem_filter.2 ⟨hzT, ht⟩⟩
  have hcard := (card_le_card hsub).trans card_biUnion_le
  have h16 : ∑ t ∈ Tg, ((rootPositions U V u v r).filter fun z =>
      w.1 * z.2 - w.2 * z.1 = D * t).card ≤ ∑ _t ∈ Tg, 16 :=
    sum_le_sum fun t _ => card_filter_det_le hU hw _
  rw [sum_const, smul_eq_mul] at h16
  have hTgc := card_filter_circleDist_le hq0 hcop hη hδ M (β := β)
  have hfin : (((rootPositions U V u v r).filter fun z =>
      (∃ t ∈ Icc (-(M : ℤ)) M, w.1 * z.2 - w.2 * z.1 = D * t) ∧ lineOf p z = ℓ).card : ℝ) ≤
        Tg.card * 16 := by exact_mod_cast hcard.trans h16
  calc _ ≤ (Tg.card : ℝ) * 16 := hfin
    _ ≤ (384 * Y / p + 103 * Y ^ (4 / 5 : ℝ)) * 16 :=
        mul_le_mul_of_nonneg_right (hTgc.trans hbound) (by norm_num)
    _ ≤ 2 ^ 13 * (Y / p + Y ^ (4 / 5 : ℝ)) := by
        have : 0 ≤ Y / p := by positivity
        have : 384 * Y / p = 384 * (Y / p) := by ring
        nlinarith

end Erdos408.OneSided
