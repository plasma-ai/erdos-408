import Erdos408.OneSided.Moment.Edge.Block
import Erdos408.OneSided.Moment.Edge.Parseval

/-!
# The core kernel of the clean edge

PD `mem:clean-kernel` to `mem:minor-decay`. On the root box `𝒵` times a finite set `X` of
label tuples with an injective product map `β`, consider the kernel

`[z good] [D ∣ det(z, z')] ψ(t/Y) {[t - β x + β x' = 0] - ∫_𝔐 e(θ(t - β x + β x')) dθ}`,
`t = det(z, z')/D`.

`exists_coreKer_bound`: its norm is at most `C₀ Y (1 + log 4Y) (L^{-A₀} + Y^{-0.1})` for an
absolute constant `C₀`. The proof:

1. `sub_arcIntegral_eq` writes the kernel as the minor-arc integral of `e(θ(t - β x + β x'))`,
   and `kerLe_parseval` reduces it to the fibers `[z good] [D ∣ det] ψ(t/Y) e(θ t)` with `θ`
   minor.
2. Since `ψ(t/Y) ≠ 0` forces `|det| < 10 d₀ Y`, a fiber is a sum over at most `5121` cell
   shifts `δ`. `exists_kerLe_cutoff` removes `ψ`: it costs the norms of the twisted kernels at
   `ϑ = θ + ξ/Y`, for `|ξ| ≤ L^{A₀}/2` and for all `ξ`.
3. `kerLe_shiftKernel_of_box` reduces a twisted kernel to the determinant matrix on a box
   `A' B' ≪ Y`, `A', B' ≤ Y^{0.9}`. Its norm is at most the trivial `(2A' + 1)(2B' + 1) ≪ Y`,
   and for `|ξ| ≤ L^{A₀}/2` at most `Y (1 + log 4Y) (C/L^{A₀} + C Y^{-0.1})` by Dirichlet's
   approximation `exists_dirichlet_minor`, the Gram bound `kerLe_phaseBox`, the spacing bound
   `sum_dirBound_le` and the tensor step `kerLe_detPhase`.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real

/-! ### The determinant matrix on a box -/

/-- The cardinality of the box `|m₁| ≤ A`, `|m₂| ≤ B` is `(2A + 1)(2B + 1)`. -/
theorem card_intBox (A B : ℕ) : ((intBox A B).card : ℝ) = (2 * A + 1) * (2 * B + 1) := by
  rw [intBox, card_product, Int.card_Icc, Int.card_Icc]
  rw [show (A : ℤ) + 1 - -(A : ℤ) = ((2 * A + 1 : ℕ) : ℤ) by push_cast; ring,
    show (B : ℤ) + 1 - -(B : ℤ) = ((2 * B + 1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast,
    Int.toNat_natCast]
  push_cast
  ring

/-- `Y^{0.9} ≤ Y` for `Y ≥ 1`. -/
private theorem rpow_nine_tenths_le {Y : ℝ} (hY : 1 ≤ Y) : Y ^ (9 / 10 : ℝ) ≤ Y := by
  calc Y ^ (9 / 10 : ℝ) ≤ Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
    _ = Y := Real.rpow_one Y

/-- **The trivial bound** on a box `A' B' ≤ 6 c² Y`, `A', B' ≤ Y^{0.9}`: the determinant matrix
has norm at most `(2A' + 1)(2B' + 1) ≤ (24 c² + 5) Y`. -/
theorem kerLe_detBox_triv {ϑ Y c : ℝ} {A' B' : ℕ} (hY : 1 ≤ Y) (hAB : (A' : ℝ) * B' ≤ 6 * c ^ 2 * Y)
    (hA : (A' : ℝ) ≤ Y ^ (9 / 10 : ℝ)) (hB : (B' : ℝ) ≤ Y ^ (9 / 10 : ℝ)) :
    KerLe (intBox A' B') (intBox A' B') (fun m m' => ephase (ϑ * (m.1 * m'.2 - m.2 * m'.1)))
      ((24 * c ^ 2 + 5) * Y) := by
  have h := kerLe_of_norm_le (k := fun m m' : ℤ × ℤ => ephase (ϑ * (m.1 * m'.2 - m.2 * m'.1)))
    (S := intBox A' B') (S' := intBox A' B') zero_le_one fun m _ m' _ => (norm_ephase _).le
  refine h.mono (by positivity) ?_
  rw [one_mul, Real.sqrt_mul_self (Nat.cast_nonneg _), card_intBox]
  have h9 := rpow_nine_tenths_le hY
  nlinarith

/-- The numerical form of the Gram bound: with `P < d ≤ 2Y/P`, `A B ≤ 6 c² Y`, `A, B ≤ Y^{0.9}`
and `1 + log 2d ≤ Λ`, `(8A/d + 1)(4B + 2 + 4d(1 + log 2d)) ≤ Y Λ ((192 c² + 8)/P + 54 Y^{-0.1})`. -/
private theorem gram_numeric {A B d Y P c Λ : ℝ} (hA0 : 0 ≤ A) (_hB0 : 0 ≤ B)
    (hAB : A * B ≤ 6 * c ^ 2 * Y) (hA : A ≤ Y ^ (9 / 10 : ℝ)) (hB : B ≤ Y ^ (9 / 10 : ℝ))
    (hP : 1 ≤ P) (hPd : P < d) (hdY : d ≤ 2 * Y / P) (hl : 1 + Real.log (2 * d) ≤ Λ)
    (hY : 1 ≤ Y) :
    (4 * (2 * A) / d + 1) * (2 * (2 * B + 1) + 4 * d * (1 + Real.log (2 * d))) ≤
      Y * Λ * ((192 * c ^ 2 + 8) / P + 54 * Y ^ (-(1 / 10 : ℝ))) := by
  have hd0 : 0 < d := by linarith
  have hY0 : 0 < Y := by linarith
  have hP0 : 0 < P := by linarith
  set l := 1 + Real.log (2 * d) with hldef
  have hl1 : 1 ≤ l := by
    have : 0 ≤ Real.log (2 * d) := Real.log_nonneg (by linarith)
    linarith
  have hΛ1 : 1 ≤ Λ := hl1.trans hl
  set Yt := Y ^ (9 / 10 : ℝ) with hYt
  have hYt1 : 1 ≤ Yt := Real.one_le_rpow hY (by norm_num)
  have hYt : Y * Y ^ (-(1 / 10 : ℝ)) = Yt := by
    rw [hYt, ← Real.rpow_one_add' hY0.le (by norm_num)]
    norm_num
  -- the six terms of the product
  have e : (4 * (2 * A) / d + 1) * (2 * (2 * B + 1) + 4 * d * l) =
      32 * (A * B / d) + 16 * (A / d) + 32 * A * l + 4 * B + 2 + 4 * d * l := by
    field_simp
    ring
  have t1 : A * B / d ≤ 6 * c ^ 2 * Y / P := by
    calc A * B / d ≤ 6 * c ^ 2 * Y / d := div_le_div_of_nonneg_right hAB hd0.le
      _ ≤ 6 * c ^ 2 * Y / P := div_le_div_of_nonneg_left (by positivity) hP0 hPd.le
  have t2 : A / d ≤ A := div_le_self hA0 (by linarith)
  have t3 : 4 * d * l ≤ 8 * Y * Λ / P := by
    have : d * l ≤ (2 * Y / P) * Λ := mul_le_mul hdY hl (by linarith) (by positivity)
    rw [show 8 * Y * Λ / P = 4 * ((2 * Y / P) * Λ) by ring]
    linarith
  have t4 : A * l ≤ Yt * Λ := mul_le_mul hA hl (by linarith) (by linarith)
  rw [e]
  have hR : Y * Λ * ((192 * c ^ 2 + 8) / P + 54 * Y ^ (-(1 / 10 : ℝ))) =
      192 * (c ^ 2 * Y * Λ / P) + 8 * Y * Λ / P + 54 * (Yt * Λ) := by
    rw [← hYt]
    field_simp
  rw [hR]
  have h1 : 32 * (A * B / d) ≤ 192 * (c ^ 2 * Y * Λ / P) := by
    have : 6 * c ^ 2 * Y / P ≤ 6 * (c ^ 2 * Y * Λ / P) := by
      rw [show 6 * (c ^ 2 * Y * Λ / P) = 6 * c ^ 2 * Y / P * Λ by ring]
      exact le_mul_of_one_le_right (by positivity) hΛ1
    linarith
  have h2 : A ≤ Yt * Λ := hA.trans (le_mul_of_one_le_right (by linarith) hΛ1)
  have h3 : B ≤ Yt * Λ := hB.trans (le_mul_of_one_le_right (by linarith) hΛ1)
  have h4 : (1 : ℝ) ≤ Yt * Λ := by nlinarith
  nlinarith

/-- **The minor-arc bound** on a box (PD `mem:bilinear-gram`, `mem:minor-decay`): if
`|ϑ - c/d| ≤ 1/(dQ)` with `(c, d) = 1`, `P < d ≤ Q ≤ 2Y/P`, then on a box `A' B' ≤ 6 c₀² Y`,
`A', B' ≤ Y^{0.9}` the determinant matrix has norm at most
`Y (1 + log 4Y) ((192 c₀² + 8)/P + 54 Y^{-0.1})`. -/
theorem kerLe_detBox_minor {ϑ Y P c : ℝ} {A' B' : ℕ} {cc : ℤ} {d Q : ℕ} (hY : 1 ≤ Y)
    (hAB : (A' : ℝ) * B' ≤ 6 * c ^ 2 * Y) (hA : (A' : ℝ) ≤ Y ^ (9 / 10 : ℝ))
    (hB : (B' : ℝ) ≤ Y ^ (9 / 10 : ℝ)) (hP : 1 ≤ P) (hd : P < d) (hdQ : d ≤ Q)
    (hQ : (Q : ℝ) ≤ 2 * Y / P) (hcop : Int.gcd cc d = 1) (happ : |ϑ - cc / d| ≤ 1 / (d * Q)) :
    KerLe (intBox A' B') (intBox A' B') (fun m m' => ephase (ϑ * (m.1 * m'.2 - m.2 * m'.1)))
      (Y * (1 + Real.log (4 * Y)) * ((192 * c ^ 2 + 8) / P + 54 * Y ^ (-(1 / 10 : ℝ)))) := by
  have hd0 : 0 < d := by
    have : (0 : ℝ) < d := by linarith
    exact_mod_cast this
  have hdr : (d : ℝ) ≤ 2 * Y / P := (Nat.cast_le.2 hdQ).trans hQ
  have hY0 : 0 < Y := by linarith
  have hP0 : 0 < P := by linarith
  have hlog : 1 + Real.log (2 * d) ≤ 1 + Real.log (4 * Y) := by
    have h2d : 2 * (d : ℝ) ≤ 4 * Y := by
      have : 2 * Y / P ≤ 2 * Y := div_le_self (by positivity) hP
      linarith
    have : Real.log (2 * d) ≤ Real.log (4 * Y) :=
      Real.log_le_log (by have h0 : (0 : ℝ) < d := (by exact_mod_cast hd0); positivity) h2d
    linarith
  -- the two Gram bounds
  have happ' : |-ϑ - (-cc : ℤ) / d| ≤ 1 / (d * Q) := by
    rw [show -ϑ - ((-cc : ℤ) : ℝ) / d = -(ϑ - cc / d) by push_cast; ring, abs_neg]
    exact happ
  have hcop' : Int.gcd (-cc) d = 1 := by rw [Int.neg_gcd]; exact hcop
  have hS₁ := sum_dirBound_le hd0 hdQ hcop' happ' (2 * A') (n := 2 * B' + 1) (by positivity)
  have hS₂ := sum_dirBound_le hd0 hdQ hcop happ (2 * B') (n := 2 * A' + 1) (by positivity)
  have hG₁ := kerLe_phaseBox (-ϑ) B' A'
  have hG₂ := kerLe_phaseBox ϑ A' B'
  set Γ₁sq := ∑ m ∈ Icc (-(2 * A' : ℤ)) (2 * A'), dirBound (2 * B' + 1) (m * -ϑ) with hΓ₁
  set Γ₂sq := ∑ m ∈ Icc (-(2 * B' : ℤ)) (2 * B'), dirBound (2 * A' + 1) (m * ϑ) with hΓ₂
  have hΓ₁0 : 0 ≤ Γ₁sq := sum_nonneg fun m _ => dirBound_nonneg (by positivity) _
  have hΓ₂0 : 0 ≤ Γ₂sq := sum_nonneg fun m _ => dirBound_nonneg (by positivity) _
  have hE := kerLe_detPhase ϑ A' B' hG₁ hG₂
  refine hE.mono (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ?_
  -- `√a √b ≤ (a + b)/2 ≤ max`
  have hcast1 : ((2 * A' : ℕ) : ℤ) = 2 * (A' : ℤ) := by push_cast; ring
  have hcast2 : ((2 * B' : ℕ) : ℤ) = 2 * (B' : ℤ) := by push_cast; ring
  rw [hcast1] at hS₁
  rw [hcast2] at hS₂
  push_cast at hS₁ hS₂
  have hb1 : Γ₁sq ≤ Y * (1 + Real.log (4 * Y)) * ((192 * c ^ 2 + 8) / P + 54 * Y ^ (-(1 / 10 : ℝ))) :=
    hS₁.trans (gram_numeric (Nat.cast_nonneg _) (Nat.cast_nonneg _) hAB hA hB hP hd hdr hlog hY)
  have hb2 : Γ₂sq ≤ Y * (1 + Real.log (4 * Y)) * ((192 * c ^ 2 + 8) / P + 54 * Y ^ (-(1 / 10 : ℝ))) :=
    hS₂.trans (gram_numeric (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith) hB hA hP hd hdr
      hlog hY)
  have hsq : Real.sqrt Γ₁sq * Real.sqrt Γ₂sq ≤ (Γ₁sq + Γ₂sq) / 2 := by
    have := two_mul_le_add_sq (Real.sqrt Γ₁sq) (Real.sqrt Γ₂sq)
    rw [Real.sq_sqrt hΓ₁0, Real.sq_sqrt hΓ₂0] at this
    linarith
  linarith

/-! ### Cells -/

/-- `ψ(u) ≠ 0` only for `|u| < 5`. -/
private theorem abs_lt_five_of_plateau_ne_zero {t : ℝ} (h : plateau t ≠ 0) : |t| < 5 := by
  by_contra ht
  exact h (smoothTransition.zero_of_nonpos (by linarith))

/-- **Nearby cells**: if `D ∣ det(z, z')` with `D < 2d₀` and `ψ(det/(DY)) ≠ 0`, then the cells
of `z` and `z'` differ by at most `2560`. -/
theorem abs_rootCell_sub_le {Y d₀ U V u v r : ℝ} {D : ℕ} (hY : 0 < Y) (hd₀ : 0 < d₀)
    (hD0 : 0 < D) (hD2 : (D : ℝ) < 2 * d₀) (hU : 0 < U) (hUu : U ≤ u) (hu : u ≤ 16 * U)
    {z z' : ℤ × ℤ} (hz : z ∈ rootPositions U V u v r) (hz' : z' ∈ rootPositions U V u v r)
    (hdvd : (D : ℤ) ∣ zdet z z') (hψ : plateau (((zdet z z' / D : ℤ) : ℝ) / Y) ≠ 0) :
    |rootCell (d₀ * Y) r z' - rootCell (d₀ * Y) r z| ≤ 2560 := by
  obtain ⟨hτ1, hτ2⟩ := tau_mem_of_mem_rootPositions hU hUu hu hz
  obtain ⟨hτ1', hτ2'⟩ := tau_mem_of_mem_rootPositions hU hUu hu hz'
  have hτ : 0 < tau r z := by linarith
  have hτ' : 0 < tau r z' := by linarith
  have hD0' : (0 : ℝ) < D := by exact_mod_cast hD0
  have hH : 0 < d₀ * Y := by positivity
  -- `|det| < 5 D Y < 10 d₀ Y`
  have h5 := abs_lt_five_of_plateau_ne_zero hψ
  rw [abs_div, abs_of_pos hY, div_lt_iff₀ hY] at h5
  have hdet : (zdet z z' : ℝ) = D * ((zdet z z' / D : ℤ) : ℝ) := by
    exact_mod_cast (Int.mul_ediv_cancel' hdvd).symm
  have hdet' : |(zdet z z' : ℝ)| < 10 * (d₀ * Y) := by
    rw [hdet, abs_mul, abs_of_pos hD0']
    have : (D : ℝ) * |((zdet z z' / D : ℤ) : ℝ)| ≤ D * (5 * Y) :=
      mul_le_mul_of_nonneg_left h5.le hD0'.le
    nlinarith
  -- `|z'₂/τ(z') - z₂/τ(z)| < 2560 d₀ Y`
  have hdiff : |(z'.2 : ℝ) / tau r z' - z.2 / tau r z| < 2560 * (d₀ * Y) := by
    rw [div_tau_sub_div_tau r hτ.ne' hτ'.ne', abs_div, abs_of_pos (mul_pos hτ hτ'),
      div_lt_iff₀ (mul_pos hτ hτ')]
    have : 1 / 256 ≤ tau r z * tau r z' := by nlinarith
    nlinarith
  -- the cells
  unfold rootCell
  set a := ((z'.2 : ℝ) / tau r z') / (d₀ * Y)
  set b := ((z.2 : ℝ) / tau r z) / (d₀ * Y)
  have hab : |a - b| < 2560 := by
    rw [← sub_div, abs_div, abs_of_pos hH, div_lt_iff₀ hH]
    exact hdiff
  have h1 := Int.floor_le a
  have h2 := Int.lt_floor_add_one a
  have h3 := Int.floor_le b
  have h4 := Int.lt_floor_add_one b
  rw [abs_lt] at hab
  have hlt : ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) < 2561 := by push_cast; linarith
  have hgt : (-2561 : ℝ) < ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) := by push_cast; linarith
  have hlt' : ⌊a⌋ - ⌊b⌋ < 2561 := by exact_mod_cast hlt
  have hgt' : -2561 < ⌊a⌋ - ⌊b⌋ := by exact_mod_cast hgt
  rw [abs_le]
  constructor <;> omega

/-- A term supported on cell shifts `|b - a| ≤ 2560` is the sum over the shifts `δ` of its
restrictions to `b = a + δ`. -/
private theorem sum_shift_eq (c₁ c₂ : Prop) [Decidable c₁] [Decidable c₂] (a b : ℤ) (g : ℂ)
    (h : c₁ → c₂ → g ≠ 0 → |b - a| ≤ 2560) :
    (if c₁ ∧ c₂ then g else 0) =
      ∑ δ ∈ Icc (-2560 : ℤ) 2560, (if c₁ ∧ c₂ ∧ b = a + δ then (1 : ℂ) else 0) * g := by
  by_cases hc : c₁ ∧ c₂
  · by_cases hg : g = 0
    · simp [hg]
    · have hab := h hc.1 hc.2 hg
      simp only [hc.1, hc.2, true_and, ↓reduceIte]
      rw [sum_eq_single_of_mem (b - a) (mem_Icc.2 (abs_le.1 hab)) fun δ _ hne => by
        have : ¬ b = a + δ := fun h' => hne (by rw [h']; ring)
        simp only [this, ↓reduceIte, zero_mul]]
      simp
  · have hc' : ∀ δ : ℤ, ¬ (c₁ ∧ c₂ ∧ b = a + δ) := fun δ h' => hc ⟨h'.1, h'.2.1⟩
    simp only [hc, hc', ↓reduceIte, zero_mul, sum_const_zero]

/-- The final arithmetic of the core bound:
`5121 (C/2)(Y Λ (K₁/P + 54 ε) + K_t Y/(P/2)) ≤ (5121 (C/2)(K₁ + 54 + 2K_t) + 1) Y Λ (P⁻¹ + ε)`. -/
private theorem core_numeric {Cψ K₁ Kt Y P Λ ε : ℝ} (hCψ : 0 ≤ Cψ) (hK₁ : 0 ≤ K₁) (hKt : 0 ≤ Kt)
    (hY : 0 < Y) (hP : 0 < P) (hΛ : 1 ≤ Λ) (hε : 0 ≤ ε) :
    5121 * (Cψ / 2 * (Y * Λ * (K₁ / P + 54 * ε) + Kt * Y / (P / 2))) ≤
      (5121 * (Cψ / 2) * (K₁ + 54 + 2 * Kt) + 1) * Y * Λ * (P⁻¹ + ε) := by
  set S := Y * Λ * (P⁻¹ + ε) with hS
  have hS0 : 0 ≤ S := mul_nonneg (mul_nonneg hY.le (by linarith)) (add_nonneg (inv_nonneg.2 hP.le) hε)
  have hP' : 0 ≤ P⁻¹ := inv_nonneg.2 hP.le
  have hYΛ : 0 ≤ Y * Λ := mul_nonneg hY.le (by linarith)
  have h1 : Y * Λ * (K₁ / P + 54 * ε) ≤ (K₁ + 54) * S := by
    rw [hS, div_eq_mul_inv]
    have : K₁ * P⁻¹ + 54 * ε ≤ (K₁ + 54) * (P⁻¹ + ε) := by nlinarith
    calc Y * Λ * (K₁ * P⁻¹ + 54 * ε) ≤ Y * Λ * ((K₁ + 54) * (P⁻¹ + ε)) :=
          mul_le_mul_of_nonneg_left this hYΛ
      _ = (K₁ + 54) * (Y * Λ * (P⁻¹ + ε)) := by ring
  have h2 : Kt * Y / (P / 2) ≤ 2 * Kt * S := by
    rw [hS, div_div_eq_mul_div, div_eq_mul_inv]
    have : Y ≤ Y * Λ := le_mul_of_one_le_right hY.le hΛ
    have h3 : Y * P⁻¹ ≤ Y * Λ * (P⁻¹ + ε) := by
      calc Y * P⁻¹ ≤ Y * Λ * P⁻¹ := mul_le_mul_of_nonneg_right this hP'
        _ ≤ Y * Λ * (P⁻¹ + ε) := mul_le_mul_of_nonneg_left (by linarith) hYΛ
    calc Kt * Y * 2 * P⁻¹ = 2 * Kt * (Y * P⁻¹) := by ring
      _ ≤ 2 * Kt * (Y * Λ * (P⁻¹ + ε)) := mul_le_mul_of_nonneg_left h3 (by linarith)
  have hC : 0 ≤ Cψ / 2 := div_nonneg hCψ zero_le_two
  calc 5121 * (Cψ / 2 * (Y * Λ * (K₁ / P + 54 * ε) + Kt * Y / (P / 2)))
      ≤ 5121 * (Cψ / 2 * ((K₁ + 54) * S + 2 * Kt * S)) := by
        have := add_le_add h1 h2
        have := mul_le_mul_of_nonneg_left this hC
        linarith
    _ = 5121 * (Cψ / 2) * (K₁ + 54 + 2 * Kt) * S := by ring
    _ ≤ (5121 * (Cψ / 2) * (K₁ + 54 + 2 * Kt) + 1) * S := by linarith
    _ = (5121 * (Cψ / 2) * (K₁ + 54 + 2 * Kt) + 1) * Y * Λ * (P⁻¹ + ε) := by rw [hS]; ring

open scoped Classical in
/-- **The core kernel bound** (PD `mem:minor-decay`). For `L^{A₀} ≥ 2`, `Y ≥ 8 L^{3A₀}`,
`Y^{0.1} ≥ 8 c₀`, a squarefree pad product `D ∈ [d₀, 2d₀)` and `U ≤ u ≤ 16U`, the core kernel on
`𝒵 × X` has norm at most `C₀ Y (1 + log 4Y) (L^{-A₀} + Y^{-0.1})`. -/
theorem exists_coreKer_bound : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {κ : Type} (X : Finset κ) (β : κ → ℤ),
    Set.InjOn β X → ∀ (A₀ x Y d₀ U V u v r : ℝ) (D : ℕ),
    2 ≤ Real.log x ^ A₀ → 8 * (Real.log x ^ A₀) ^ 3 ≤ Y → 8 * latConst ≤ Y ^ (1 / 10 : ℝ) →
    0 < d₀ → d₀ ≤ D → (D : ℝ) < 2 * d₀ → Squarefree D → 0 < U → U ≤ u → u ≤ 16 * U →
    KerLe (rootPositions U V u v r ×ˢ X) (rootPositions U V u v r ×ˢ X)
      (fun q q' => if GoodPad Y D (posRatio r q.1) ∧ (D : ℤ) ∣ zdet q.1 q'.1 then
        (plateau ((zdet q.1 q'.1 / D : ℤ) / Y) : ℂ) *
          ((if zdet q.1 q'.1 / D - β q.2 + β q'.2 = 0 then 1 else 0) -
            arcIntegral A₀ x Y (zdet q.1 q'.1 / D - β q.2 + β q'.2))
        else 0)
      (C₀ * Y * (1 + Real.log (4 * Y)) * ((Real.log x ^ A₀)⁻¹ + Y ^ (-(1 / 10 : ℝ)))) := by
  obtain ⟨Cψ, hCψ, hcut⟩ := exists_kerLe_cutoff
  set K₁ : ℝ := 192 * latConst ^ 2 + 8 with hK₁
  set Kt : ℝ := 24 * latConst ^ 2 + 5 with hKt
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hKt0 : 0 ≤ Kt := by positivity
  refine ⟨5121 * (Cψ / 2) * (K₁ + 54 + 2 * Kt) + 1, by positivity, ?_⟩
  intro κ X β hβ A₀ x Y d₀ U V u v r D hP hY8 hYc hd₀ hD hD2 hDsq hU hUu hu
  set P := Real.log x ^ A₀ with hPdef
  have hP1 : 1 ≤ P := by linarith
  have hP0 : 0 < P := by linarith
  have hP3 : P ≤ P ^ 3 := le_self_pow₀ hP1 (by norm_num)
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hYP : P ≤ Y := by linarith
  have hD0 : 0 < D := by
    have : (0 : ℝ) < D := hd₀.trans_le hD
    exact_mod_cast this
  set Λ := 1 + Real.log (4 * Y) with hΛ
  have hΛ1 : 1 ≤ Λ := by
    have : 0 ≤ Real.log (4 * Y) := Real.log_nonneg (by linarith)
    linarith
  set nmin := Y * Λ * (K₁ / P + 54 * Y ^ (-(1 / 10 : ℝ))) with hnmin
  set ntriv := Kt * Y with hntriv
  have hnmin0 : 0 ≤ nmin := mul_nonneg (mul_nonneg hY0.le (by linarith))
    (add_nonneg (div_nonneg hK₁0 hP0.le) (mul_nonneg (by norm_num) (Real.rpow_nonneg hY0.le _)))
  have hntriv0 : 0 ≤ ntriv := mul_nonneg hKt0 hY0.le
  have hterm0 : 0 ≤ Cψ / 2 * (nmin + ntriv / (P / 2)) :=
    mul_nonneg (div_nonneg hCψ zero_le_two) (add_nonneg hnmin0 (div_nonneg hntriv0 (by linarith)))
  set ε₁ := ∑ _δ ∈ Icc (-2560 : ℤ) 2560, Cψ / 2 * (nmin + ntriv / (P / 2)) with hε₁
  have hε₁0 : 0 ≤ ε₁ := sum_nonneg fun _ _ => hterm0
  set Z := rootPositions U V u v r with hZ
  set T : ℤ × ℤ → ℤ × ℤ → ℤ := fun z z' => zdet z z' / D with hT
  set G : ℤ × ℤ → ℤ × ℤ → ℂ := fun z z' =>
    if GoodPad Y D (posRatio r z) ∧ (D : ℤ) ∣ zdet z z' then (plateau ((T z z' : ℝ) / Y) : ℂ)
    else 0 with hG
  set Q := ⌈Y / P⌉₊ with hQ
  have hQ2 : (Q : ℝ) ≤ 2 * Y / P := by
    have h1 : (Q : ℝ) < Y / P + 1 := Nat.ceil_lt_add_one (div_nonneg hY0.le hP0.le)
    have h2 : 1 ≤ Y / P := by rw [le_div_iff₀ hP0]; linarith
    have : Y / P + 1 ≤ 2 * Y / P := by
      rw [show 2 * Y / P = Y / P + Y / P by ring]
      linarith
    linarith
  -- the fibers at minor `θ`
  have hfib : ∀ θ ∈ Set.Ioc (-(2 * arcRadius A₀ x Y)) (-(2 * arcRadius A₀ x Y) + 1),
      minorWeight A₀ x Y θ ≠ 0 → KerLe Z Z (fun z z' => G z z' * ephase (θ * T z z')) ε₁ := by
    intro θ hθ hw
    have hminor := (minorWeight_spec hP1 hY8 θ).2 hθ hw
    -- one cell shift `δ`
    set Hδ : ℤ → ℤ × ℤ → ℤ × ℤ → ℂ := fun δ z z' =>
      if GoodPad Y D (posRatio r z) ∧ (D : ℤ) ∣ zdet z z' ∧
          rootCell (d₀ * Y) r z' = rootCell (d₀ * Y) r z + δ then 1 else 0 with hHδ
    have hshift : ∀ δ ∈ Icc (-2560 : ℤ) 2560, KerLe Z Z
        (fun z z' => Hδ δ z z' * ((plateau (T z z' / Y) : ℂ) * ephase (θ * T z z')))
        (Cψ / 2 * (nmin + ntriv / (P / 2))) := by
      intro δ hδ
      have hδ' : |δ| ≤ 2560 := abs_le.2 (mem_Icc.1 hδ)
      -- the twisted kernels at `ϑ = θ + ξ/Y`
      have htw : ∀ (ϑ n : ℝ), 0 ≤ n → (∀ A' B' : ℕ, (A' : ℝ) * B' ≤ 6 * latConst ^ 2 * Y →
          (A' : ℝ) ≤ Y ^ (9 / 10 : ℝ) → (B' : ℝ) ≤ Y ^ (9 / 10 : ℝ) →
          KerLe (intBox A' B') (intBox A' B')
            (fun m m' => ephase (ϑ * (m.1 * m'.2 - m.2 * m'.1))) n) →
          KerLe Z Z (fun z z' => Hδ δ z z' * ephase (ϑ * T z z')) n := by
        intro ϑ n hn hbox
        refine (kerLe_shiftKernel_of_box hδ' hY1 hYc hd₀ hD hDsq hU hUu hu hn hbox).congr
          fun z _ z' _ => ?_
        simp only [hHδ, hT]
        split_ifs <;> simp
      refine hcut Z (Hδ δ) T θ Y (P / 2) nmin ntriv hY0 (by linarith) hnmin0 hntriv0
        (fun ξ hξ => ?_) (fun ξ => ?_)
      · obtain ⟨c, d, hcop, hPd, hdQ, happ⟩ := exists_dirichlet_minor hP0 hY0 hminor hξ
        exact htw _ _ hnmin0 fun A' B' hAB hA hB =>
          kerLe_detBox_minor hY1 hAB hA hB hP1 hPd hdQ hQ2 hcop happ
      · exact htw _ _ hntriv0 fun A' B' hAB hA hB => kerLe_detBox_triv hY1 hAB hA hB
    refine (KerLe.sum _ hshift fun _ _ => hterm0).congr fun z hz z' hz' => ?_
    -- only the shift `cell z' - cell z` contributes
    simp only [hG, hHδ]
    rw [ite_mul, zero_mul]
    refine (sum_shift_eq _ _ _ _ _ fun hc₁ hc₂ hne => ?_).symm
    have hψ : plateau ((T z z' : ℝ) / Y) ≠ 0 := fun h => hne (by rw [h]; simp)
    exact abs_rootCell_sub_le hY0 hd₀ hD0 hD2 hU hUu hu hz hz' hc₂ hψ
  -- Fourier in the product variable
  have hpar := kerLe_parseval Z X hβ G T (measurable_minorWeight)
    (fun θ => (minorWeight_spec hP1 hY8 θ).1) (-(2 * arcRadius A₀ x Y)) hε₁0 hfib
  refine (hpar.congr fun q _ q' _ => ?_).mono hε₁0 ?_
  · rw [← sub_arcIntegral_eq hP1 hY8]
    simp only [hG, hT]
    split_ifs <;> simp
  · -- the numerical bound
    rw [hε₁, sum_const, Int.card_Icc, nsmul_eq_mul]
    have hcard : (((2560 : ℤ) + 1 - -2560).toNat : ℝ) = 5121 := by norm_num
    rw [hcard]
    exact core_numeric hCψ hK₁0 hKt0 hY0 hP0 hΛ1 (Real.rpow_nonneg hY0.le _)

end Erdos408.OneSided
