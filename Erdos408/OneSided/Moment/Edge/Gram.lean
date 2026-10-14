module

public import Erdos408.OneSided.Lift
public import Erdos408.OneSided.Moment.Edge.Operator
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The bilinear Gram bound

PD `mem:bilinear-gram` and the tensor step of `mem:minor-decay`, as kernel bounds on boxes of
integers.

* `ephase t = e(t) = exp(2πit)`.
* `norm_sum_ephase_le`: the geometric sum `|∑_{|h| ≤ A} e(h t)|` is at most `1 / (2‖t‖)`.
  With the trivial bound `2A + 1` this is `dirBound (2A + 1) t`.
* `kerLe_phaseBox`: the matrix `T(h, k) = e(ϑ h k)` on `|h| ≤ A`, `|k| ≤ B` has
  `‖T‖² ≤ ∑_{|m| ≤ 2B} dirBound (2A + 1) (m ϑ)` (Gram matrix and Schur).
* `sum_dirBound_le`: if `|ϑ - c/d| ≤ 1/(dQ)` with `(c, d) = 1` and `d ≤ Q`, then
  `∑_{|m| ≤ M} dirBound n (m ϑ) ≤ (4M/d + 1) (2n + 4d (1 + log 2d))`: split `m` into blocks of
  length at most `d/2 + 1`, in which the points `m ϑ` are `1/(2d)`-separated modulo one.
* `kerLe_detPhase`: the determinant matrix `e(ϑ (h₁ l₂ - l₁ h₂))` on a box is a tensor product
  of two such matrices, so its norm is at most the product of their norms.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset Real

/-! ### The circle distance -/

/-- `‖t‖ ≥ 0`. -/
theorem circleDist_nonneg (t : ℝ) : 0 ≤ circleDist t := abs_nonneg _

/-- `‖t‖ ≤ |t - n|` for every integer `n`. -/
theorem circleDist_le_abs_sub (t : ℝ) (n : ℤ) : circleDist t ≤ |t - n| := round_le t n

/-- `‖t‖ ≤ 1/2`. -/
theorem circleDist_le_half (t : ℝ) : circleDist t ≤ 1 / 2 := abs_sub_round t

/-- `‖-t‖ = ‖t‖`. -/
theorem circleDist_neg (t : ℝ) : circleDist (-t) = circleDist t := by
  refine le_antisymm ?_ ?_
  · calc circleDist (-t) ≤ |-t - ((-round t : ℤ) : ℝ)| := circleDist_le_abs_sub _ _
      _ = circleDist t := by
          rw [circleDist, Int.cast_neg, ← abs_neg]
          ring_nf
  · calc circleDist t ≤ |t - ((-round (-t) : ℤ) : ℝ)| := circleDist_le_abs_sub _ _
      _ = circleDist (-t) := by
          rw [circleDist, Int.cast_neg, ← abs_neg]
          ring_nf

/-- `‖s + t‖ ≤ ‖s‖ + |t|`. -/
theorem circleDist_add_le (s t : ℝ) : circleDist (s + t) ≤ circleDist s + |t| := by
  calc circleDist (s + t) ≤ |s + t - round s| := circleDist_le_abs_sub _ _
    _ = |(s - round s) + t| := by ring_nf
    _ ≤ |s - round s| + |t| := abs_add_le _ _

/-- `‖s - t‖ ≤ ‖s‖ + ‖t‖`. -/
theorem circleDist_sub_le (s t : ℝ) : circleDist (s - t) ≤ circleDist s + circleDist t := by
  calc circleDist (s - t) ≤ |s - t - ((round s - round t : ℤ) : ℝ)| :=
        circleDist_le_abs_sub _ _
    _ = |(s - round s) - (t - round t)| := by push_cast; ring_nf
    _ ≤ |s - round s| + |t - round t| := abs_sub _ _

/-- For an integer `n` not divisible by `d ≥ 1`, `‖n/d‖ ≥ 1/d`. -/
theorem one_div_le_circleDist_div {n : ℤ} {d : ℕ} (hd : 0 < d) (hn : ¬ (d : ℤ) ∣ n) :
    1 / (d : ℝ) ≤ circleDist (n / d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold circleDist
  set k := round ((n : ℝ) / d)
  have hne : n - k * d ≠ 0 := fun h => hn ⟨k, by linear_combination h⟩
  have h1 : (1 : ℝ) ≤ |((n - k * d : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hne
  have e : (n : ℝ) / d - k = ((n - k * d : ℤ) : ℝ) / d := by
    push_cast
    field_simp
  rw [e, abs_div, abs_of_pos hd']
  exact div_le_div_of_nonneg_right h1 hd'.le

/-! ### The phase -/

/-- `e(t) = exp(2πit)`. -/
def ephase (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * t)

/-- `|e(t)| = 1`. -/
theorem norm_ephase (t : ℝ) : ‖ephase t‖ = 1 := by
  rw [ephase, show 2 * (π : ℂ) * Complex.I * t = ((2 * π * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `e(s + t) = e(s) e(t)`. -/
theorem ephase_add (s t : ℝ) : ephase (s + t) = ephase s * ephase t := by
  rw [ephase, ephase, ephase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `e(n) = 1` for an integer `n`. -/
theorem ephase_intCast (n : ℤ) : ephase n = 1 := by
  rw [ephase, show 2 * (π : ℂ) * Complex.I * ((n : ℝ) : ℂ) = n * (2 * π * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- `e(0) = 1`. -/
theorem ephase_zero : ephase 0 = 1 := by simp [ephase]

/-- `\overline{e(t)} = e(-t)`. -/
theorem star_ephase (t : ℝ) : star (ephase t) = ephase (-t) := by
  rw [ephase, ephase, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

/-- `e(n t) = e(t)^n` for a natural `n`. -/
theorem ephase_natCast_mul (n : ℕ) (t : ℝ) : ephase (n * t) = ephase t ^ n := by
  induction n with
  | zero => simp [ephase_zero]
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, ephase_add, ih, pow_succ]

/-- `|e(t) - 1| ≥ 4 ‖t‖`. -/
theorem four_mul_circleDist_le (t : ℝ) : 4 * circleDist t ≤ ‖ephase t - 1‖ := by
  set y := t - round t with hy
  have hyt : ephase t = ephase y := by
    rw [hy, sub_eq_add_neg, ephase_add, ← Int.cast_neg, ephase_intCast, mul_one]
  have hy2 : |y| ≤ 1 / 2 := abs_sub_round t
  -- `|e(y) - 1| = 2 |sin(π y)| ≥ 4 |y|`
  have e : ephase y = Complex.exp (Complex.I * ((2 * π * y : ℝ) : ℂ)) := by
    rw [ephase]
    congr 1
    push_cast
    ring
  rw [hyt, e, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, show 2 * π * y / 2 = π * y by ring, abs_two]
  have hpos : 0 ≤ π * |y| := by positivity
  have hle : π * |y| ≤ π / 2 := by nlinarith [Real.pi_pos]
  have hs := Real.mul_le_sin hpos hle
  have habs : |Real.sin (π * y)| = Real.sin (π * |y|) := by
    have hyb := abs_le.1 hy2
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h]
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by nlinarith [Real.pi_pos]))
    · rw [abs_of_nonpos h, mul_neg, Real.sin_neg]
      have := Real.sin_nonneg_of_nonneg_of_le_pi (x := π * -y) (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
      rw [mul_neg, Real.sin_neg] at this
      exact abs_of_nonpos (by linarith)
  rw [habs]
  unfold circleDist
  rw [← hy]
  have : 2 / π * (π * |y|) = 2 * |y| := by field_simp
  linarith

/-! ### Geometric sums -/

/-- The bound `min(n, 1/(2‖t‖))` for a geometric sum of `n` terms, read as `n` when `‖t‖ = 0`. -/
def dirBound (n t : ℝ) : ℝ := if circleDist t = 0 then n else min n (1 / (2 * circleDist t))

/-- `dirBound n t ≤ n`. -/
theorem dirBound_le (n t : ℝ) : dirBound n t ≤ n := by
  unfold dirBound
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- `dirBound n t ≥ 0` for `n ≥ 0`. -/
theorem dirBound_nonneg {n : ℝ} (hn : 0 ≤ n) (t : ℝ) : 0 ≤ dirBound n t := by
  unfold dirBound
  split_ifs
  · exact hn
  · exact le_min hn (by have := circleDist_nonneg t; positivity)

/-- `dirBound n t ≤ 1/(2‖t‖)` when `‖t‖ ≠ 0`. -/
theorem dirBound_le_inv {n t : ℝ} (ht : circleDist t ≠ 0) :
    dirBound n t ≤ 1 / (2 * circleDist t) := by
  simp only [dirBound, ht, ↓reduceIte]
  exact min_le_right _ _

/-- `dirBound` is even. -/
theorem dirBound_neg (n t : ℝ) : dirBound n (-t) = dirBound n t := by
  simp only [dirBound, circleDist_neg]

/-- **The geometric sum**: `|∑_{|h| ≤ A} e(h t)| ≤ dirBound (2A + 1) t`. -/
theorem norm_sum_ephase_le (A : ℕ) (t : ℝ) :
    ‖∑ h ∈ Icc (-(A : ℤ)) A, ephase (h * t)‖ ≤ dirBound (2 * A + 1) t := by
  -- reindex `h = j - A`, `0 ≤ j ≤ 2A`
  have e : ∑ h ∈ Icc (-(A : ℤ)) A, ephase (h * t) =
      ephase (-(A * t)) * ∑ j ∈ range (2 * A + 1), ephase t ^ j := by
    rw [mul_sum]
    refine sum_nbij' (fun h => (h + A).toNat) (fun j => (j : ℤ) - A) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      simp only [mem_Icc, mem_range] at hh ⊢
      omega
    · intro j hj
      simp only [mem_Icc, mem_range] at hj ⊢
      omega
    · intro h hh
      simp only [mem_Icc] at hh ⊢
      omega
    · intro j _
      simp
    · intro h hh
      simp only [mem_Icc] at hh
      rw [← ephase_natCast_mul, ← ephase_add]
      congr 1
      have : (((h + A).toNat : ℕ) : ℝ) = h + A := by
        exact_mod_cast Int.toNat_of_nonneg (by omega)
      rw [this]
      ring
  have htriv : ‖∑ h ∈ Icc (-(A : ℤ)) A, ephase (h * t)‖ ≤ 2 * A + 1 := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_ephase, sum_const, Int.card_Icc, nsmul_eq_mul, mul_one]
    have : (((A : ℤ) + 1 - -(A : ℤ)).toNat : ℝ) = 2 * A + 1 := by
      rw [show (A : ℤ) + 1 - -(A : ℤ) = ((2 * A + 1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
      push_cast
      ring
    rw [this]
  unfold dirBound
  split_ifs with h0
  · exact htriv
  · refine le_min htriv ?_
    have hpos : 0 < circleDist t := lt_of_le_of_ne (circleDist_nonneg t) (Ne.symm h0)
    have h4 := four_mul_circleDist_le t
    have hne : ephase t - 1 ≠ 0 := by
      intro h
      rw [h, norm_zero] at h4
      linarith
    have hne' : ephase t ≠ 1 := sub_ne_zero.1 hne
    rw [e, geom_sum_eq hne', norm_mul, norm_ephase, one_mul, norm_div]
    have hnum : ‖ephase t ^ (2 * A + 1) - 1‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow, norm_ephase, one_pow, norm_one]
      norm_num
    have hden : 0 < ‖ephase t - 1‖ := norm_pos_iff.2 hne
    calc ‖ephase t ^ (2 * A + 1) - 1‖ / ‖ephase t - 1‖ ≤ 2 / ‖ephase t - 1‖ :=
          div_le_div_of_nonneg_right hnum hden.le
      _ ≤ 2 / (4 * circleDist t) := div_le_div_of_nonneg_left (by norm_num) (by positivity) h4
      _ = 1 / (2 * circleDist t) := by field_simp; norm_num

/-! ### The Gram bound -/

/-- **The Gram bound**: the matrix `e(ϑ h k)` from `|k| ≤ B` to `|h| ≤ A` has squared norm at
most `∑_{|m| ≤ 2B} dirBound (2A + 1) (m ϑ)`. -/
theorem kerLe_phaseBox (ϑ : ℝ) (A B : ℕ) :
    KerLe (Icc (-(A : ℤ)) A) (Icc (-(B : ℤ)) B) (fun h k => ephase (ϑ * h * k))
      (Real.sqrt (∑ m ∈ Icc (-(2 * B : ℤ)) (2 * B), dirBound (2 * A + 1) (m * ϑ))) := by
  intro f
  set Γ := ∑ m ∈ Icc (-(2 * B : ℤ)) (2 * B), dirBound (2 * A + 1) (m * ϑ) with hΓ
  have hΓ0 : 0 ≤ Γ := sum_nonneg fun m _ => dirBound_nonneg (by positivity) _
  rw [Real.sq_sqrt hΓ0]
  set IA := Icc (-(A : ℤ)) A
  set IB := Icc (-(B : ℤ)) B
  -- the Gram entries `G(k, k') = ∑_h e(ϑ h (k - k'))`
  set G : ℤ → ℤ → ℂ := fun k k' => ∑ h ∈ IA, ephase (h * ((k - k' : ℤ) * ϑ)) with hG
  have hGle : ∀ k k', ‖G k k'‖ ≤ dirBound (2 * A + 1) ((k - k' : ℤ) * ϑ) := fun k k' =>
    norm_sum_ephase_le A _
  have hGsymm : ∀ k k', ‖G k' k‖ = ‖G k k'‖ := by
    intro k k'
    have : G k' k = star (G k k') := by
      rw [hG]
      simp only [star_sum, star_ephase]
      refine sum_congr rfl fun h _ => ?_
      congr 1
      push_cast
      ring
    rw [this, norm_star]
  -- expand the square
  have hexp : ((∑ h ∈ IA, ‖∑ k ∈ IB, ephase (ϑ * h * k) * f k‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ IB, ∑ k' ∈ IB, f k * star (f k') * G k k' := by
    push_cast
    have : ∀ h, ((‖∑ k ∈ IB, ephase (ϑ * h * k) * f k‖ : ℝ) : ℂ) ^ 2 =
        ∑ k ∈ IB, ∑ k' ∈ IB, f k * star (f k') * ephase (h * ((k - k' : ℤ) * ϑ)) := by
      intro h
      rw [← Complex.mul_conj', ← Complex.star_def, star_sum, sum_mul_sum]
      refine sum_congr rfl fun k _ => sum_congr rfl fun k' _ => ?_
      rw [star_mul', star_ephase]
      have : ephase (ϑ * h * k) * ephase (-(ϑ * h * k')) = ephase (h * ((k - k' : ℤ) * ϑ)) := by
        rw [← ephase_add]
        congr 1
        push_cast
        ring
      rw [← this]
      ring
    simp_rw [this]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun k' _ => ?_
    rw [hG, mul_sum]
  have hreal : ∑ h ∈ IA, ‖∑ k ∈ IB, ephase (ϑ * h * k) * f k‖ ^ 2 ≤
      ∑ k ∈ IB, ∑ k' ∈ IB, ‖f k‖ * ‖f k'‖ * ‖G k k'‖ := by
    have h0 : 0 ≤ ∑ h ∈ IA, ‖∑ k ∈ IB, ephase (ϑ * h * k) * f k‖ ^ 2 :=
      sum_nonneg fun _ _ => sq_nonneg _
    calc _ = ‖((∑ h ∈ IA, ‖∑ k ∈ IB, ephase (ϑ * h * k) * f k‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg h0]
      _ ≤ _ := by
          rw [hexp]
          refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => (norm_sum_le _ _).trans
            (sum_le_sum fun k' _ => le_of_eq ?_))
          rw [norm_mul, norm_mul, norm_star]
  -- AM–GM and the symmetry of the Gram matrix
  have hamgm : ∑ k ∈ IB, ∑ k' ∈ IB, ‖f k‖ * ‖f k'‖ * ‖G k k'‖ ≤
      ∑ k ∈ IB, ‖f k‖ ^ 2 * ∑ k' ∈ IB, ‖G k k'‖ := by
    have h1 : ∑ k ∈ IB, ∑ k' ∈ IB, ‖f k‖ * ‖f k'‖ * ‖G k k'‖ ≤
        ∑ k ∈ IB, ∑ k' ∈ IB, (‖f k‖ ^ 2 / 2 * ‖G k k'‖ + ‖f k'‖ ^ 2 / 2 * ‖G k k'‖) :=
      sum_le_sum fun k _ => sum_le_sum fun k' _ => by
        have := two_mul_le_add_sq ‖f k‖ ‖f k'‖
        nlinarith [norm_nonneg (G k k')]
    have h2 : ∑ k ∈ IB, ∑ k' ∈ IB, ‖f k'‖ ^ 2 / 2 * ‖G k k'‖ =
        ∑ k ∈ IB, ∑ k' ∈ IB, ‖f k‖ ^ 2 / 2 * ‖G k k'‖ := by
      rw [sum_comm]
      exact sum_congr rfl fun k _ => sum_congr rfl fun k' _ => by rw [hGsymm]
    rw [sum_congr rfl fun k _ => sum_add_distrib, sum_add_distrib, h2] at h1
    refine h1.trans (le_of_eq ?_)
    rw [← two_mul, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun k' _ => by ring
  -- each Gram row sum is at most `Γ`
  have hrow : ∀ k ∈ IB, ∑ k' ∈ IB, ‖G k k'‖ ≤ Γ := by
    intro k hk
    calc ∑ k' ∈ IB, ‖G k k'‖ ≤ ∑ k' ∈ IB, dirBound (2 * A + 1) ((k - k' : ℤ) * ϑ) :=
          sum_le_sum fun k' _ => hGle k k'
      _ = ∑ m ∈ IB.image (fun k' => k - k'), dirBound (2 * A + 1) (m * ϑ) := by
          rw [sum_image fun a _ b _ h => by simpa using h]
      _ ≤ Γ := by
          refine sum_le_sum_of_subset_of_nonneg (fun m hm => ?_)
            fun m _ _ => dirBound_nonneg (by positivity) _
          obtain ⟨k', hk', rfl⟩ := mem_image.1 hm
          rw [mem_Icc] at hk hk' ⊢
          constructor <;> omega
  calc _ ≤ _ := hreal
    _ ≤ _ := hamgm
    _ ≤ ∑ k ∈ IB, ‖f k‖ ^ 2 * Γ :=
        sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hrow k hk) (sq_nonneg _)
    _ = Γ * ∑ k ∈ IB, ‖f k‖ ^ 2 := by rw [mul_sum]; exact sum_congr rfl fun k _ => by ring

/-! ### The spacing bound -/

/-- Points `m ϑ` with `m` in a block of at most `d/2 + 1` consecutive integers are
`1/(2d)`-separated modulo one, when `|ϑ - c/d| ≤ 1/(dQ)`, `(c, d) = 1` and `d ≤ Q`. -/
theorem circleDist_mul_ge {ϑ : ℝ} {c : ℤ} {d Q : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (hcop : Int.gcd c d = 1) (happ : |ϑ - c / d| ≤ 1 / (d * Q)) {j : ℤ} (hj : j ≠ 0)
    (hjd : 2 * |j| ≤ d) : 1 / (2 * d) ≤ circleDist (j * ϑ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hQ' : (d : ℝ) ≤ Q := by exact_mod_cast hdQ
  -- `d ∤ j c`
  have hndvd : ¬ (d : ℤ) ∣ j * c := by
    intro h
    have h1 : (d : ℤ) ∣ j := by
      have hc : IsCoprime (d : ℤ) c := by
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
        exact hcop
      exact hc.dvd_of_dvd_mul_right h
    have h2 := Int.le_of_dvd (abs_pos.2 hj) ((dvd_abs _ _).2 h1)
    have : (1 : ℤ) ≤ |j| := Int.one_le_abs hj
    omega
  have h1 := one_div_le_circleDist_div hd hndvd
  have hjr : (2 : ℝ) * |(j : ℝ)| ≤ d := by exact_mod_cast hjd
  have herr : |(j : ℝ)| * |ϑ - c / d| ≤ 1 / (2 * d) := by
    calc |(j : ℝ)| * |ϑ - c / d| ≤ (d / 2) * (1 / (d * Q)) :=
          mul_le_mul (by linarith) happ (abs_nonneg _) (by positivity)
      _ = 1 / (2 * Q) := by field_simp
      _ ≤ 1 / (2 * d) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 := circleDist_add_le ((j : ℝ) * ϑ) (((j * c : ℤ) : ℝ) / d - j * ϑ)
  rw [add_sub_cancel] at h2
  have e : |((j * c : ℤ) : ℝ) / d - j * ϑ| = |(j : ℝ)| * |ϑ - c / d| := by
    rw [← abs_mul, abs_sub_comm]
    congr 1
    push_cast
    ring
  rw [e] at h2
  have : 1 / (d : ℝ) = 1 / (2 * d) + 1 / (2 * d) := by field_simp; norm_num
  linarith

/-- At most two points of a `1/(2d)`-separated family lie at circle distances in one interval
`[j/(4d), (j+1)/(4d))`, one on each side of zero. -/
private theorem card_bucket_le_two {ϑ : ℝ} {d : ℕ} (hd : 0 < d) (T : Finset ℤ)
    (hsep : ∀ m ∈ T, ∀ m' ∈ T, m ≠ m' → 1 / (2 * d) ≤ circleDist ((m - m' : ℤ) * ϑ)) (j : ℕ)
    (hT : ∀ m ∈ T, ⌊4 * d * circleDist (m * ϑ)⌋₊ = j) : T.card ≤ 2 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set sgn : ℤ → Bool := fun m => decide (0 ≤ (m : ℝ) * ϑ - round ((m : ℝ) * ϑ))
  have hfib : ∀ b ∈ T.image sgn, (T.filter fun m => sgn m = b).card ≤ 1 := by
    intro b _
    refine card_le_one.2 fun m hm m' hm' => ?_
    by_contra hne
    rw [mem_filter] at hm hm'
    have hs := hsep m hm.1 m' hm'.1 hne
    have hj := hT m hm.1
    have hj' := hT m' hm'.1
    set y := (m : ℝ) * ϑ - round ((m : ℝ) * ϑ)
    set y' := (m' : ℝ) * ϑ - round ((m' : ℝ) * ϑ)
    have hb : (0 ≤ y ↔ 0 ≤ y') := by
      have h := hm.2.trans hm'.2.symm
      simp only [sgn, decide_eq_decide] at h
      exact h
    -- `|y|, |y'| ∈ [j/(4d), (j+1)/(4d))`
    have hy0 : 0 ≤ 4 * d * |y| := by positivity
    have hy0' : 0 ≤ 4 * d * |y'| := by positivity
    have hyl := Nat.floor_le hy0
    have hyu := Nat.lt_floor_add_one (4 * d * |y|)
    have hyl' := Nat.floor_le hy0'
    have hyu' := Nat.lt_floor_add_one (4 * d * |y'|)
    simp only [circleDist] at hj hj'
    rw [hj] at hyl hyu
    rw [hj'] at hyl' hyu'
    have key : |4 * d * y - 4 * d * y'| < 1 := by
      by_cases h : 0 ≤ y
      · have h' := hb.1 h
        rw [abs_of_nonneg h] at hyl hyu
        rw [abs_of_nonneg h'] at hyl' hyu'
        exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
      · have h' : ¬ 0 ≤ y' := fun h' => h (hb.2 h')
        push Not at h h'
        rw [abs_of_neg h] at hyl hyu
        rw [abs_of_neg h'] at hyl' hyu'
        exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    have hclose : |y - y'| < 1 / (4 * d) := by
      have e : |4 * d * y - 4 * d * y'| = 4 * d * |y - y'| := by
        rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
      rw [lt_div_iff₀ (by positivity)]
      linarith
    have hdist : circleDist ((m - m' : ℤ) * ϑ) ≤ |y - y'| := by
      calc circleDist ((m - m' : ℤ) * ϑ)
          ≤ |((m - m' : ℤ) : ℝ) * ϑ - ((round ((m : ℝ) * ϑ) - round ((m' : ℝ) * ϑ) : ℤ) : ℝ)| :=
            circleDist_le_abs_sub _ _
        _ = |y - y'| := by congr 1; push_cast; ring
    have : 1 / (4 * (d : ℝ)) < 1 / (2 * d) := one_div_lt_one_div_of_lt (by positivity)
      (by linarith)
    linarith
  calc T.card ≤ 1 * (T.image sgn).card := card_le_mul_card_image T 1 hfib
    _ ≤ 1 * (univ : Finset Bool).card := by gcongr; exact subset_univ _
    _ = 2 := by simp

/-- `∑_{j=1}^{n} 1/j ≤ 1 + log n`. -/
private theorem sum_inv_le_one_add_log (n : ℕ) :
    ∑ j ∈ Icc 1 n, (1 : ℝ) / j ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- Within a block of `1/(2d)`-separated points, `∑ dirBound n (m ϑ) ≤ 2n + 4d (1 + log 2d)`. -/
private theorem sum_block_le {ϑ : ℝ} {d : ℕ} (hd : 0 < d) {n : ℝ} (hn : 0 ≤ n) (T : Finset ℤ)
    (hsep : ∀ m ∈ T, ∀ m' ∈ T, m ≠ m' → 1 / (2 * d) ≤ circleDist ((m - m' : ℤ) * ϑ)) :
    ∑ m ∈ T, dirBound n (m * ϑ) ≤ 2 * n + 4 * d * (1 + Real.log (2 * d)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set bucket : ℤ → ℕ := fun m => ⌊4 * d * circleDist (m * ϑ)⌋₊
  have hmaps : ∀ m ∈ T, bucket m ∈ range (2 * d + 1) := by
    intro m _
    rw [mem_range, Nat.lt_succ_iff]
    refine Nat.floor_le_of_le ?_
    have := circleDist_le_half (m * ϑ)
    push_cast
    nlinarith
  rw [← sum_fiberwise_of_maps_to hmaps]
  -- the bound in bucket `j`
  set bnd : ℕ → ℝ := fun j => if j = 0 then n else 2 * d / j with hbnd
  have hb : ∀ j ∈ range (2 * d + 1), ∑ m ∈ T with bucket m = j, dirBound n (m * ϑ) ≤ 2 * bnd j := by
    intro j _
    have hcard := card_bucket_le_two hd (T.filter fun m => bucket m = j)
      (fun m hm m' hm' hne => hsep m (mem_filter.1 hm).1 m' (mem_filter.1 hm').1 hne) j
      (fun m hm => (mem_filter.1 hm).2)
    have hpt : ∀ m ∈ T.filter (fun m => bucket m = j), dirBound n (m * ϑ) ≤ bnd j := by
      intro m hm
      have hj := (mem_filter.1 hm).2
      rw [hbnd]
      dsimp only
      split_ifs with h0
      · exact dirBound_le _ _
      · -- `‖m ϑ‖ ≥ j/(4d) > 0`
        have hjpos : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero h0
        have hfl : (j : ℝ) ≤ 4 * d * circleDist (m * ϑ) := by
          rw [← hj]
          exact Nat.floor_le (by have := circleDist_nonneg (m * ϑ); positivity)
        have hc : 0 < circleDist (m * ϑ) := by
          by_contra hc
          have : circleDist (m * ϑ) = 0 := le_antisymm (not_lt.1 hc) (circleDist_nonneg _)
          rw [this] at hfl
          linarith
        calc dirBound n (m * ϑ) ≤ 1 / (2 * circleDist (m * ϑ)) := dirBound_le_inv hc.ne'
          _ ≤ 2 * d / j := by
              rw [div_le_div_iff₀ (by positivity) hjpos]
              nlinarith
    have hbj : 0 ≤ bnd j := by
      rw [hbnd]
      dsimp only
      split_ifs
      · exact hn
      · positivity
    calc ∑ m ∈ T with bucket m = j, dirBound n (m * ϑ) ≤ ∑ m ∈ T with bucket m = j, bnd j :=
          sum_le_sum hpt
      _ = (T.filter fun m => bucket m = j).card * bnd j := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 * bnd j := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hbj
  refine (sum_le_sum hb).trans ?_
  rw [← mul_sum, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
  have htail : ∑ j ∈ Ico (0 + 1) (2 * d + 1), bnd j = 2 * d * ∑ j ∈ Icc 1 (2 * d), (1 : ℝ) / j := by
    rw [mul_sum]
    refine sum_congr (by ext j; simp) fun j hj => ?_
    have hj0 : j ≠ 0 := by simp at hj; omega
    simp only [hbnd, hj0, ↓reduceIte]
    ring
  rw [htail]
  have hlog := sum_inv_le_one_add_log (2 * d)
  have : bnd 0 = n := by simp [hbnd]
  rw [this]
  push_cast at hlog ⊢
  nlinarith

/-- **The spacing bound** (PD `mem:bilinear-gram`): if `|ϑ - c/d| ≤ 1/(dQ)` with
`(c, d) = 1` and `1 ≤ d ≤ Q`, then
`∑_{|m| ≤ M} dirBound n (m ϑ) ≤ (4M/d + 1) (2n + 4d (1 + log 2d))`. -/
theorem sum_dirBound_le {ϑ : ℝ} {c : ℤ} {d Q : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (hcop : Int.gcd c d = 1) (happ : |ϑ - c / d| ≤ 1 / (d * Q)) (M : ℕ) {n : ℝ} (hn : 0 ≤ n) :
    ∑ m ∈ Icc (-(M : ℤ)) M, dirBound n (m * ϑ) ≤
      (4 * M / d + 1) * (2 * n + 4 * d * (1 + Real.log (2 * d))) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set ℓ := d / 2 + 1 with hℓ
  have hℓ0 : 0 < ℓ := by omega
  -- blocks `q = ⌊(m + M)/ℓ⌋`
  set blk : ℤ → ℕ := fun m => (m + M).toNat / ℓ
  have hmaps : ∀ m ∈ Icc (-(M : ℤ)) M, blk m ∈ range (2 * M / ℓ + 1) := by
    intro m hm
    rw [mem_Icc] at hm
    rw [mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hW : 0 ≤ 2 * n + 4 * d * (1 + Real.log (2 * d)) := by
    have : 0 ≤ Real.log (2 * d) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith)
    positivity
  have hblock : ∀ q ∈ range (2 * M / ℓ + 1),
      ∑ m ∈ Icc (-(M : ℤ)) M with blk m = q, dirBound n (m * ϑ) ≤
        2 * n + 4 * d * (1 + Real.log (2 * d)) := by
    intro q _
    refine sum_block_le hd hn _ fun m hm m' hm' hne => ?_
    rw [mem_filter, mem_Icc] at hm hm'
    refine circleDist_mul_ge hd hdQ hcop happ (sub_ne_zero.2 hne) ?_
    -- two points of one block differ by less than `ℓ`
    have h1 := hm.2
    have h2 := hm'.2
    simp only [blk] at h1 h2
    have hq1 := Nat.div_add_mod (m + M).toNat ℓ
    have hq2 := Nat.div_add_mod (m' + M).toNat ℓ
    have hr1 := Nat.mod_lt (m + M).toNat hℓ0
    have hr2 := Nat.mod_lt (m' + M).toNat hℓ0
    rw [h1] at hq1
    rw [h2] at hq2
    have e1 : (((m + M).toNat : ℕ) : ℤ) = m + M := Int.toNat_of_nonneg (by omega)
    have e2 : (((m' + M).toNat : ℕ) : ℤ) = m' + M := Int.toNat_of_nonneg (by omega)
    have : |m - m'| < ℓ := by
      rw [abs_lt]
      constructor <;> zify at hq1 hq2 hr1 hr2 <;> omega
    omega
  calc _ ≤ ∑ q ∈ range (2 * M / ℓ + 1), (2 * n + 4 * d * (1 + Real.log (2 * d))) :=
        sum_le_sum hblock
    _ = ((2 * M / ℓ : ℕ) + 1 : ℝ) * (2 * n + 4 * d * (1 + Real.log (2 * d))) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (4 * M / d + 1) * (2 * n + 4 * d * (1 + Real.log (2 * d))) := by
        refine mul_le_mul_of_nonneg_right ?_ hW
        have h1 : ((2 * M / ℓ : ℕ) : ℝ) ≤ (2 * M : ℕ) / (ℓ : ℝ) := Nat.cast_div_le
        have h2 : (d : ℝ) ≤ 2 * ℓ := by
          have : d ≤ 2 * ℓ := by omega
          exact_mod_cast this
        have h3 : ((2 * M : ℕ) : ℝ) / ℓ ≤ 4 * M / d := by
          rw [div_le_div_iff₀ (by exact_mod_cast hℓ0) hd']
          push_cast
          nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
        linarith

/-! ### The determinant matrix -/

/-- **The tensor step** (PD `mem:minor-decay`): the determinant matrix
`e(ϑ (h₁ l₂ - l₁ h₂))` on the box `|h| ≤ A`, `|l| ≤ B` is the tensor product of
`e(-ϑ l h)` and `e(ϑ h l)`, so its norm is at most the product of their norms. -/
theorem kerLe_detPhase (ϑ : ℝ) (A B : ℕ) {Γ₁ Γ₂ : ℝ}
    (h₁ : KerLe (Icc (-(B : ℤ)) B) (Icc (-(A : ℤ)) A) (fun l h => ephase (-ϑ * l * h)) Γ₁)
    (h₂ : KerLe (Icc (-(A : ℤ)) A) (Icc (-(B : ℤ)) B) (fun h l => ephase (ϑ * h * l)) Γ₂) :
    KerLe (Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B) (Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B)
      (fun p p' => ephase (ϑ * (p.1 * p'.2 - p.2 * p'.1))) (Γ₁ * Γ₂) := by
  intro f
  set IA := Icc (-(A : ℤ)) A
  set IB := Icc (-(B : ℤ)) B
  -- `g(l₁, l₂) = ∑_{h₂} e(-ϑ l₁ h₂) f(h₂, l₂)`
  set g : ℤ → ℤ → ℂ := fun l₁ l₂ => ∑ h₂ ∈ IA, ephase (-ϑ * l₁ * h₂) * f (h₂, l₂) with hg
  have hE : ∀ p : ℤ × ℤ, ∑ p' ∈ IA ×ˢ IB, ephase (ϑ * (p.1 * p'.2 - p.2 * p'.1)) * f p' =
      ∑ l₂ ∈ IB, ephase (ϑ * p.1 * l₂) * g p.2 l₂ := by
    intro p
    rw [sum_product, sum_comm]
    refine sum_congr rfl fun l₂ _ => ?_
    rw [hg, mul_sum]
    refine sum_congr rfl fun h₂ _ => ?_
    rw [← mul_assoc, ← ephase_add]
    congr 2
    ring
  calc ∑ p ∈ IA ×ˢ IB, ‖∑ p' ∈ IA ×ˢ IB, ephase (ϑ * (p.1 * p'.2 - p.2 * p'.1)) * f p'‖ ^ 2
      = ∑ l₁ ∈ IB, ∑ h₁ ∈ IA, ‖∑ l₂ ∈ IB, ephase (ϑ * h₁ * l₂) * g l₁ l₂‖ ^ 2 := by
        rw [sum_product, sum_comm]
        exact sum_congr rfl fun l₁ _ => sum_congr rfl fun h₁ _ => by rw [hE]
    _ ≤ ∑ l₁ ∈ IB, Γ₂ ^ 2 * ∑ l₂ ∈ IB, ‖g l₁ l₂‖ ^ 2 := sum_le_sum fun l₁ _ => h₂ (g l₁)
    _ = Γ₂ ^ 2 * ∑ l₂ ∈ IB, ∑ l₁ ∈ IB, ‖∑ h₂ ∈ IA, ephase (-ϑ * l₁ * h₂) * f (h₂, l₂)‖ ^ 2 := by
        rw [← mul_sum, sum_comm]
    _ ≤ Γ₂ ^ 2 * ∑ l₂ ∈ IB, Γ₁ ^ 2 * ∑ h₂ ∈ IA, ‖f (h₂, l₂)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun l₂ _ => h₁ fun h₂ => f (h₂, l₂))
          (sq_nonneg _)
    _ = (Γ₁ * Γ₂) ^ 2 * ∑ p ∈ IA ×ˢ IB, ‖f p‖ ^ 2 := by
        rw [sum_product, sum_comm, ← mul_sum]
        ring

end Erdos408.OneSided
