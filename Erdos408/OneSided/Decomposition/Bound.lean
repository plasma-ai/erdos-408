module

public import Erdos408.OneSided.Decomposition.Collision

/-!
# The decomposition at one `x`

For coprime label products the raw equations are `t = b - a` (Lemma 1.3), so the pair error
is the coprime-pair error of the lift. Then
`Q_Y - Q_Y^maj - ∑_k 2^{-k} ⟨f, 𝒯 f⟩_{2^k}` is the shared-label part plus the pad-collision
part. With `|E(a, b)| ≤ B` for `a, b ∈ (Y, 4Y)`, `∏V_i⁻² η(a/Y) η(b/Y) ≤ 16 Y² μ(p) μ(p')`,
and the collision probabilities, it is at most `16 Y² B (K² + (KJ)² + 2KJ) ε`.
-/

@[expose] public section

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

/-! ### Lemma 1.3 -/

/-- Label tuples sharing no prime have coprime products. -/
theorem coprime_prod_of_unshared {x : ℝ} {d : Data K} {p p' : Fin K → ℕ}
    (hp : p ∈ d.labels x) (hp' : p' ∈ d.labels x) (hU : Unshared p p') :
    Nat.Coprime (∏ i, p i) (∏ i, p' i) :=
  Nat.Coprime.prod_left fun i _ => Nat.Coprime.prod_right fun i' _ =>
    (Nat.coprime_primes (mem_filter.1 (mem_band_of_mem_labels hp i)).2
      (mem_filter.1 (mem_band_of_mem_labels hp' i')).2).2 (hU i i')

open scoped Classical in
/-- **Lemma 1.3.** For coprime `a, b ∈ (0, 4Y)` and `mn, rs ≥ 2`,
`[∃ h ≥ 1 : mn - 1 = ah, rs - 1 = bh] = ψ(t/Y) [t = b - a]` with `t = bmn - ars`. -/
theorem ite_exists_eq {a b m n r s : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) {Y : ℝ}
    (hY : 0 < Y) (ha4 : (a : ℝ) < 4 * Y) (hb4 : (b : ℝ) < 4 * Y) (hmn : 2 ≤ m * n)
    (hrs : 2 ≤ r * s) :
    (if ∃ h, 1 ≤ h ∧ m * n - 1 = a * h ∧ r * s - 1 = b * h then (1 : ℂ) else 0) =
      ((plateau (((b * m * n - a * r * s : ℤ) : ℝ) / Y) : ℝ) : ℂ) *
        (if (b * m * n - a * r * s : ℤ) = (b : ℤ) - a then 1 else 0) := by
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le (show 1 ≤ m * n by omega)
  obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le (show 1 ≤ r * s by omega)
  have ht : (b * m * n - a * r * s : ℤ) = b * u - a * v + b - a := by
    have hu' : ((m * n : ℕ) : ℤ) = 1 + u := by exact_mod_cast hu
    have hv' : ((r * s : ℕ) : ℤ) = 1 + v := by exact_mod_cast hv
    push_cast at hu' hv'
    linear_combination (b : ℤ) * hu' - (a : ℤ) * hv'
  -- the equation `t = b - a` is `bu = av`, which for coprime `a, b` is `u = ah`, `v = bh`
  have hiff : (∃ h, 1 ≤ h ∧ m * n - 1 = a * h ∧ r * s - 1 = b * h) ↔
      (b * m * n - a * r * s : ℤ) = (b : ℤ) - a := by
    rw [ht, hu, hv, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    constructor
    · rintro ⟨h, -, rfl, rfl⟩
      push_cast
      ring
    · intro heq
      have hbu : b * u = a * v := by
        have : (b * u : ℤ) = a * v := by linarith
        exact_mod_cast this
      obtain ⟨h, rfl⟩ : a ∣ u := hab.dvd_of_dvd_mul_left ⟨v, hbu⟩
      refine ⟨h, ?_, rfl, ?_⟩
      · rcases Nat.eq_zero_or_pos h with rfl | h1
        · omega
        · exact h1
      · have : a * (b * h) = a * v := by rw [← hbu]; ring
        exact (Nat.eq_of_mul_eq_mul_left ha this).symm
  by_cases heq : (b * m * n - a * r * s : ℤ) = (b : ℤ) - a
  · rw [ite_eq_left (hiff.2 heq), ite_eq_left heq, mul_one, heq]
    -- `|b - a| < 4Y`, so the plateau is one
    have hψ : plateau ((((b : ℤ) - a : ℤ) : ℝ) / Y) = 1 := by
      unfold plateau
      refine smoothTransition.one_of_one_le ?_
      have : |(((b : ℤ) - a : ℤ) : ℝ) / Y| ≤ 4 := by
        rw [abs_div, abs_of_pos hY, div_le_iff₀ hY, abs_le]
        push_cast
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]
      linarith
    rw [hψ, Complex.ofReal_one]
  · rw [ite_eq_right (fun h => heq (hiff.1 h)), ite_eq_right heq, mul_zero]

open scoped Classical in
/-- For unshared label tuples with products in `(0, 4Y)`, the pair error is the coprime-pair
error of the lift, once `mn ≥ 2` on the support. -/
theorem liftError_eq_pairError (A₀ : ℝ) {C CX alo ahi g x : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d) (hHm : 2 ≤ d.Hm) (hHn : 1 ≤ d.Hn) {Y : ℝ}
    (hY : 0 < Y) {p p' : Fin K → ℕ} (hp : p ∈ d.labels x) (hp' : p' ∈ d.labels x)
    (hU : Unshared p p') (ha4 : ((∏ i, p i : ℕ) : ℝ) < 4 * Y)
    (hb4 : ((∏ i, p' i : ℕ) : ℝ) < 4 * Y) :
    liftError A₀ x d Y p p' = pairError A₀ x d Y (∏ i, p i) (∏ i, p' i) := by
  have hab := coprime_prod_of_unshared hp hp' hU
  have ha : 0 < ∏ i, p i := prod_pos fun i _ => (mem_filter.1 (mem_band_of_mem_labels hp i)).2.pos
  -- `mn ≥ 2` when `α_m β_n ≠ 0`
  have hmn : ∀ m n : ℕ, d.α m ≠ 0 → d.β n ≠ 0 → 2 ≤ m * n := by
    intro m n hm hn
    have h₁ : (2 : ℝ) ≤ m := hHm.trans (hd.α_supp m hm).1
    have h₂ : (1 : ℝ) ≤ n := hHn.trans (hd.β_supp n hn).1
    have : (2 : ℝ) ≤ m * n := by nlinarith
    exact_mod_cast this
  unfold liftError pairError
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => sum_congr rfl fun r _ =>
    sum_congr rfl fun s _ => ?_
  by_cases hc : d.α m * star (d.α r) * d.β n * star (d.β s) = 0
  · rw [hc, zero_mul, zero_mul, mul_zero]
  have hm : d.α m ≠ 0 := fun h => hc (by rw [h]; ring)
  have hr : d.α r ≠ 0 := fun h => hc (by rw [h]; simp)
  have hn : d.β n ≠ 0 := fun h => hc (by rw [h]; ring)
  have hs : d.β s ≠ 0 := fun h => hc (by rw [h]; simp)
  rw [ite_exists_eq hab ha hY ha4 hb4 (hmn m n hm hn) (hmn r s hr hs), majorWeight]
  unfold liftDet
  push_cast
  ring

/-! ### The bound at one `x` -/

/-- `μ(p) = (∏ p_i)⁻¹ ∏V_i⁻¹`. -/
theorem labelWeight_eq (x : ℝ) (d : Data K) (p : Fin K → ℕ) :
    labelWeight x d p = ((∏ i, p i : ℕ) : ℝ)⁻¹ * (d.bandMass x)⁻¹ := by
  simp [labelWeight, Data.bandMass, prod_mul_distrib, prod_inv_distrib]
  ring

/-- `η(b/Y) ≤ 4Y/b`. -/
theorem dyadicBump_le_div {Y : ℝ} (hY : 0 < Y) (b : ℕ) :
    dyadicBump (b / Y) ≤ 4 * Y / b := by
  by_cases hη : dyadicBump (b / Y) = 0
  · rw [hη]
    positivity
  obtain ⟨h₁, h₂⟩ := lt_of_dyadicBump_ne_zero hη
  have hb : (0 : ℝ) < b := by
    by_contra hb
    rw [show (b : ℝ) = 0 by linarith [Nat.cast_nonneg (α := ℝ) b], zero_div] at h₁
    linarith
  rw [div_lt_iff₀ hY] at h₂
  rw [le_div_iff₀ hb]
  linarith [dyadicBump_le_one (b / Y), mul_le_mul_of_nonneg_right (dyadicBump_le_one (b / Y))
    hb.le]

/-- `∏V_i⁻² η(a/Y) η(b/Y) ≤ 16 Y² μ(p) μ(p')`. -/
theorem mul_dyadicBump_le {x : ℝ} {d : Data K} (hV : 0 < d.bandMass x) {Y : ℝ} (hY : 0 < Y)
    (p p' : Fin K → ℕ) :
    (d.bandMass x)⁻¹ ^ 2 * (dyadicBump ((∏ i, p i : ℕ) / Y) *
        dyadicBump ((∏ i, p' i : ℕ) / Y)) ≤
      16 * Y ^ 2 * (labelWeight x d p * labelWeight x d p') := by
  rw [labelWeight_eq, labelWeight_eq]
  have h₁ := dyadicBump_le_div hY (∏ i, p i)
  have h₂ := dyadicBump_le_div hY (∏ i, p' i)
  calc (d.bandMass x)⁻¹ ^ 2 * (dyadicBump ((∏ i, p i : ℕ) / Y) *
        dyadicBump ((∏ i, p' i : ℕ) / Y))
      ≤ (d.bandMass x)⁻¹ ^ 2 * (4 * Y / (∏ i, p i : ℕ) * (4 * Y / (∏ i, p' i : ℕ))) := by
        gcongr
        exact dyadicBump_nonneg _
    _ = _ := by ring

open scoped Classical in
/-- **The decomposition at one `x`.** With `|E(a, b)| ≤ B` for label products
`a, b ∈ (Y, 4Y)`, atoms at most `ε`, and every pad product below `2^{N + 1}`,
`|Q_Y - Q_Y^maj - ∑_{k ≤ N} 2^{-k} ⟨f, 𝒯 f⟩_{2^k}| ≤ 16 Y² B (K² + (KJ)² + 2KJ) ε`. -/
theorem norm_square_decomposition_le (q A₀ : ℝ) {C CX alo ahi g x : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hrough : ∀ i, ∀ r ∈ band x (d.a i), ∀ m : ℕ, m ≠ 0 → IsRough x m → ¬ r ∣ m)
    (hHm : 2 ≤ d.Hm) (hHn : 1 ≤ d.Hn) (hV : ∀ i, 0 < harmonicMass (band x (d.a i)))
    {Y : ℝ} (hY : 1 ≤ Y) (hYW : ∀ p ∈ d.labels x, Y < (∏ i, p i : ℕ) → 5 * Y ≤ roughLevel x)
    {N : ℕ} (hN : ∀ z ∈ padSet x d (padCount x), ∏ c, z c < 2 ^ (N + 1)) {ε : ℝ}
    (hε0 : 0 ≤ ε)
    (hε : ∀ i, ∀ y ∈ band x (d.a i), 1 / ((y : ℝ) * harmonicMass (band x (d.a i))) ≤ ε)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ p ∈ d.labels x, ∀ p' ∈ d.labels x, Y < (∏ i, p i : ℕ) → Y < (∏ i, p' i : ℕ) →
      ((∏ i, p i : ℕ) : ℝ) < 4 * Y → ((∏ i, p' i : ℕ) : ℝ) < 4 * Y →
      ‖pairError A₀ x d Y (∏ i, p i) (∏ i, p' i)‖ ≤ B) :
    ‖cauchySquare x d Y - majorSquare A₀ x d Y -
        ∑ k ∈ range (N + 1), ((2 : ℂ) ^ k)⁻¹ * rowPairing q A₀ x d Y (2 ^ k)‖ ≤
      16 * Y ^ 2 * B * ((K : ℝ) ^ 2 + (((K * padCount x : ℕ) : ℝ) ^ 2 +
        2 * (K * padCount x : ℕ))) * ε := by
  have hV' : 0 < d.bandMass x := prod_pos fun i _ => hV i
  have hY0 : 0 < Y := by linarith
  set c : ℝ := ((K * padCount x : ℕ) : ℝ) ^ 2 + 2 * (K * padCount x : ℕ)
  set bad : (Fin K → ℕ) → (Fin K → ℕ) → ℝ := fun p p' =>
    ∑ z ∈ padSet x d (padCount x), if GoodPads p p' z then 0 else padWeight x d z
  have hw0 : ∀ p, 0 ≤ labelWeight x d p := fun p =>
    prod_nonneg fun i _ => one_div_mul_harmonicMass_nonneg (hV i) _
  have hμ0 : ∀ z : Fin K × Fin (padCount x) → ℕ, 0 ≤ padWeight x d z := fun z =>
    prod_nonneg fun c _ => one_div_mul_harmonicMass_nonneg (hV c.1) _
  have hbad0 : ∀ p p', 0 ≤ bad p p' := fun p p' =>
    sum_nonneg fun z _ => by split_ifs <;> simp [hμ0]
  -- the good pads have mass `1 - bad`
  have hgood : ∀ p p', ∑ z ∈ padSet x d (padCount x),
      (if GoodPads p p' z then padWeight x d z else 0) = 1 - bad p p' := by
    intro p p'
    rw [← sum_padWeight hV (padCount x), eq_sub_iff_add_eq, ← sum_add_distrib]
    exact sum_congr rfl fun z _ => by split_ifs <;> simp
  -- one pair of label tuples
  have key : ∀ p ∈ d.labels x, ∀ p' ∈ d.labels x,
      (d.bandMass x)⁻¹ ^ 2 * ‖((dyadicBump ((∏ i, p i : ℕ) / Y) *
          dyadicBump ((∏ i, p' i : ℕ) / Y) : ℝ) : ℂ) *
          pairError A₀ x d Y (∏ i, p i) (∏ i, p' i) -
        (if Unshared p p' then
          ((dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) : ℝ) : ℂ) *
            ∑ z ∈ padSet x d (padCount x),
              if GoodPads p p' z then (padWeight x d z : ℂ) * liftError A₀ x d Y p p' else 0
        else 0)‖ ≤
      16 * Y ^ 2 * B * (labelWeight x d p * labelWeight x d p') *
        (bad p p' + if Unshared p p' then 0 else 1) := by
    intro p hp p' hp'
    set η := dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)
    have hη0 : 0 ≤ η := mul_nonneg (dyadicBump_nonneg _) (dyadicBump_nonneg _)
    have hR0 : 0 ≤ 16 * Y ^ 2 * B * (labelWeight x d p * labelWeight x d p') *
        (bad p p' + if Unshared p p' then 0 else 1) := by
      have := hbad0 p p'
      have : (0 : ℝ) ≤ if Unshared p p' then 0 else 1 := by split_ifs <;> norm_num
      have := hw0 p
      have := hw0 p'
      positivity
    by_cases hη : η = 0
    · simp only [hη, Complex.ofReal_zero, zero_mul, ite_self, sub_zero, norm_zero, mul_zero]
      exact hR0
    -- the label products lie in `(Y, 4Y)`
    have hab : ∀ {b : ℕ}, dyadicBump (b / Y) ≠ 0 → Y < b ∧ (b : ℝ) < 4 * Y := by
      intro b hb
      obtain ⟨h₁, h₂⟩ := lt_of_dyadicBump_ne_zero hb
      rw [one_lt_div hY0] at h₁
      rw [div_lt_iff₀ hY0] at h₂
      exact ⟨h₁, h₂⟩
    have hpY := hab (left_ne_zero_of_mul hη)
    have hp'Y := hab (right_ne_zero_of_mul hη)
    have hE := hB p hp p' hp' hpY.1 hp'Y.1 hpY.2 hp'Y.2
    have hVη := mul_dyadicBump_le hV' hY0 p p'
    by_cases hU : Unshared p p'
    · -- coprime labels: the difference is the bad-pad part
      rw [show (if Unshared p p' then (0 : ℝ) else 1) = 0 from ite_eq_left hU, add_zero]
      rw [ite_eq_left hU, liftError_eq_pairError A₀ hd hHm hHn hY0 hp hp' hU hpY.2 hp'Y.2]
      have hsum : ∑ z ∈ padSet x d (padCount x), (if GoodPads p p' z then
          (padWeight x d z : ℂ) * pairError A₀ x d Y (∏ i, p i) (∏ i, p' i) else 0) =
          ((1 - bad p p' : ℝ) : ℂ) * pairError A₀ x d Y (∏ i, p i) (∏ i, p' i) := by
        rw [← hgood, Complex.ofReal_sum, sum_mul]
        exact sum_congr rfl fun z _ => by split_ifs <;> simp
      rw [hsum, ← mul_assoc, ← Complex.ofReal_mul, ← sub_mul, ← Complex.ofReal_sub,
        show η - η * (1 - bad p p') = η * bad p p' by ring, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hη0 (hbad0 p p'))]
      calc (d.bandMass x)⁻¹ ^ 2 * (η * bad p p' *
            ‖pairError A₀ x d Y (∏ i, p i) (∏ i, p' i)‖)
          = ((d.bandMass x)⁻¹ ^ 2 * η) * bad p p' *
              ‖pairError A₀ x d Y (∏ i, p i) (∏ i, p' i)‖ := by ring
        _ ≤ (16 * Y ^ 2 * (labelWeight x d p * labelWeight x d p')) * bad p p' * B := by
            exact mul_le_mul (mul_le_mul_of_nonneg_right hVη (hbad0 p p')) hE (norm_nonneg _)
              (mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (hw0 p) (hw0 p')))
                (hbad0 p p'))
        _ = _ := by ring
    · -- shared labels: the whole term
      rw [show (if Unshared p p' then (0 : ℝ) else 1) = 1 from ite_eq_right hU]
      rw [ite_eq_right hU, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hη0]
      calc (d.bandMass x)⁻¹ ^ 2 * (η * ‖pairError A₀ x d Y (∏ i, p i) (∏ i, p' i)‖)
          = ((d.bandMass x)⁻¹ ^ 2 * η) * ‖pairError A₀ x d Y (∏ i, p i) (∏ i, p' i)‖ := by
            ring
        _ ≤ (16 * Y ^ 2 * (labelWeight x d p * labelWeight x d p')) * B := by
            gcongr
            exact mul_nonneg (by positivity) (mul_nonneg (hw0 p) (hw0 p'))
        _ ≤ 16 * Y ^ 2 * B * (labelWeight x d p * labelWeight x d p') * (bad p p' + 1) := by
            have := hbad0 p p'
            have := hw0 p
            have := hw0 p'
            nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 16 * Y ^ 2)
              hB0) (mul_nonneg (hw0 p) (hw0 p'))) (hbad0 p p')]
  -- assemble
  rw [cauchySquare_sub_majorSquare, ← sum_liftTerm_eq q A₀ hd hdisj hrough (by linarith)
    (by linarith) hV' hY hYW hN, sum_liftTerm_eq_sum_labels, ← mul_sub, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (d.bandMass x)⁻¹ ^ 2 * ‖∑ p ∈ d.labels x, ∑ p' ∈ d.labels x,
        (((dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) : ℝ) : ℂ) *
          pairError A₀ x d Y (∏ i, p i) (∏ i, p' i) -
        (if Unshared p p' then
          ((dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) : ℝ) : ℂ) *
            ∑ z ∈ padSet x d (padCount x),
              if GoodPads p p' z then (padWeight x d z : ℂ) * liftError A₀ x d Y p p' else 0
        else 0))‖
      ≤ ∑ p ∈ d.labels x, ∑ p' ∈ d.labels x, 16 * Y ^ 2 * B *
          (labelWeight x d p * labelWeight x d p') *
          (bad p p' + if Unshared p p' then 0 else 1) := by
        refine (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun p _ =>
          norm_sum_le _ _)) (by positivity)).trans ?_
        rw [mul_sum]
        refine sum_le_sum fun p hp => ?_
        rw [mul_sum]
        exact sum_le_sum fun p' hp' => key p hp p' hp'
    _ = 16 * Y ^ 2 * B * (∑ p ∈ d.labels x, ∑ p' ∈ d.labels x,
          labelWeight x d p * labelWeight x d p' * bad p p' +
        ∑ p ∈ d.labels x, ∑ p' ∈ d.labels x,
          (if Unshared p p' then 0 else labelWeight x d p * labelWeight x d p')) := by
        rw [← sum_add_distrib, mul_sum]
        refine sum_congr rfl fun p _ => ?_
        rw [← sum_add_distrib, mul_sum]
        refine sum_congr rfl fun p' _ => ?_
        split_ifs <;> ring
    _ ≤ 16 * Y ^ 2 * B * (∑ p ∈ d.labels x, ∑ p' ∈ d.labels x,
          labelWeight x d p * labelWeight x d p' * (c * ε) + K ^ 2 * ε) := by
        gcongr with p _ p' _
        · exact mul_nonneg (hw0 p) (hw0 p')
        · exact sum_padWeight_bad_le hV hε0 hε _ p p'
        · exact sum_labelWeight_shared_le hV hε0 hε
    _ = 16 * Y ^ 2 * B * ((K : ℝ) ^ 2 + c) * ε := by
        simp_rw [← sum_mul, ← mul_sum, sum_labelWeight hV, mul_one]
        rw [sum_labelWeight hV]
        ring

end Erdos408.OneSided
