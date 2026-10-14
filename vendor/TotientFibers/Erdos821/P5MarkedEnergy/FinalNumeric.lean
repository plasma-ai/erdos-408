import Erdos821.P5MarkedEnergy.FinalSimplify
import Erdos821.P5MarkedEnergy.Sizes

/-! The final numerical inequalities: every term of the piece bound is a
monomial in `L x` of exponent below `-A` once the parameters are chosen. -/

noncomputable section
open Filter Real

namespace Erdos821.P5Marked
open Blueprint.Analytic

/-- Product of monomial bounds. -/
theorem mono_mul {ℓ x y cx cy ax ay : ℝ} (hℓ : 0 < ℓ) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hx : x ≤ cx * ℓ ^ ax) (hy : y ≤ cy * ℓ ^ ay) : x * y ≤ (cx * cy) * ℓ ^ (ax + ay) := by
  rw [Real.rpow_add hℓ]
  calc x * y ≤ (cx * ℓ ^ ax) * (cy * ℓ ^ ay) := mul_le_mul hx hy hy0 (hx0.trans hx)
    _ = cx * cy * (ℓ ^ ax * ℓ ^ ay) := by ring

theorem mono_atom {ℓ : ℝ} (a : ℝ) : ℓ ^ a ≤ 1 * ℓ ^ a := by rw [one_mul]

theorem mono_const {ℓ : ℝ} (hℓ : 0 < ℓ) (c : ℝ) : c ≤ c * ℓ ^ (0 : ℝ) := by
  rw [Real.rpow_zero, mul_one]

theorem mono_sq {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ) : (ℓ ^ a) ^ 2 ≤ 1 * ℓ ^ (2 * a) := by
  rw [one_mul, ← Real.rpow_natCast, ← Real.rpow_mul hℓ.le]; norm_num; rw [mul_comm]

theorem mono_lin {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    c + d * ℓ ≤ (c + d) * ℓ ^ (1 : ℝ) := by
  rw [Real.rpow_one]; nlinarith

theorem mono_two_pow {ℓ : ℝ} (hℓ : 0 < ℓ) (c : ℝ) : (2 * ℓ) ^ c ≤ 2 ^ c * ℓ ^ c := by
  rw [Real.mul_rpow (by norm_num) hℓ.le]

theorem mono_box {ℓ : ℝ} (hℓ : 1 ≤ ℓ) : (3 * ℓ + 1) ^ 4 ≤ 256 * ℓ ^ (4 : ℝ) := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have : 3 * ℓ + 1 ≤ 4 * ℓ := by linarith
  calc (3 * ℓ + 1) ^ 4 ≤ (4 * ℓ) ^ 4 := pow_le_pow_left₀ (by linarith) this 4
    _ = 256 * ℓ ^ 4 := by ring

theorem mono_w {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (n : ℕ) : ((1 + ℓ) ^ n)⁻¹ ≤ 1 * ℓ ^ (-(n : ℝ)) := by
  rw [one_mul, Real.rpow_neg (by linarith), Real.rpow_natCast]
  apply inv_anti₀ (by positivity)
  exact pow_le_pow_left₀ (by linarith) (by linarith) n

/-- The uniform piece bound divided by `Y`. -/
def Psi1 (ℓ KLM αmin Kmm K3r c3r As Al Kl B0 B C Cmk vmax KW cW KAm At : ℝ) (j : ℕ) : ℝ :=
  KLM / αmin * ((3 * ℓ + 1) ^ 4 * ℓ ^ Kmm * ((3 * ℓ + 1) ^ 4 *
    (ℓ ^ Kmm * (PhiJ ℓ K3r c3r As Al Kl B0 B C Cmk vmax +
      ((1 + ℓ) ^ (j - 4))⁻¹ * PhiW ℓ KW cW C Cmk) + KAm * ℓ ^ (-At) * PhiW ℓ KW cW C Cmk)))

theorem rpow3 {ℓ : ℝ} (hℓ : 0 < ℓ) (a b c : ℝ) : ℓ ^ a * ℓ ^ b * ℓ ^ c = ℓ ^ (a + b + c) := by
  rw [Real.rpow_add hℓ, Real.rpow_add hℓ]

theorem psi1_le_terms {ℓ kk KLM αmin Kmm K3r c3r As Al Kl B0 B C Cmk vmax KW cW KAm At : ℝ}
    {j : ℕ} (hℓ : 1 ≤ ℓ) (hkk : 0 ≤ kk) (hKLM : 0 ≤ KLM) (hα : 0 < αmin) (hK3 : 0 ≤ K3r)
    (hKl : 0 ≤ Kl) (hv : 0 ≤ vmax) (hKW : 0 ≤ KW) (hKA : 0 ≤ KAm) :
    2 * kk ^ 2 * ℓ ^ (2 * C) * Psi1 ℓ KLM αmin Kmm K3r c3r As Al Kl B0 B C Cmk vmax KW cW KAm At j ≤
      (2 * kk ^ 2 * (KLM / αmin) * 256 * 256 * 1 * 1 * K3r * 1 * 17 * 1 * 2 ^ c3r) *
          ℓ ^ ((2 * C + 4 + 4) + Kmm + Kmm + 0 + 2 * (-As) + 1 + 2 * (C + C + Cmk) + c3r) +
        (2 * kk ^ 2 * (KLM / αmin) * 256 * 256 * 1 * 1 * K3r * Kl ^ 2 * vmax ^ 2 * 2 ^ c3r * 2) *
          ℓ ^ ((2 * C + 4 + 4) + Kmm + Kmm + 0 + 2 * (-Al) + 2 * (C + C + Cmk) + c3r + 1) +
        (2 * kk ^ 2 * (KLM / αmin) * 256 * 256 * 1 * 1 * 2 * 1 * vmax ^ 2) *
          ℓ ^ ((2 * C + 4 + 4) + Kmm + Kmm + B0 + 2 * (-B) + 2 * (C + Cmk)) +
        (2 * kk ^ 2 * (KLM / αmin) * 256 * 256 * 1 * 1 * 1 * (3 * (16 * KW)) * 1 * 2 ^ cW) *
          ℓ ^ ((2 * C + 4 + 4) + Kmm + Kmm + (-((j - 4 : ℕ) : ℝ)) + 1 + 2 * (C + C + Cmk) + cW) +
        (2 * kk ^ 2 * (KLM / αmin) * 256 * 256 * 1 * KAm * (3 * (16 * KW)) * 1 * 2 ^ cW) *
          ℓ ^ ((2 * C + 4 + 4) + Kmm + (-At) + 1 + 2 * (C + C + Cmk) + cW) := by
  have hℓ0 : 0 < ℓ := by linarith
  -- common blocks
  have hPre : 2 * kk ^ 2 * ℓ ^ (2 * C) * (KLM / αmin) * (3 * ℓ + 1) ^ 4 * (3 * ℓ + 1) ^ 4 ≤
      (2 * kk ^ 2 * (KLM / αmin) * 256 * 256) * ℓ ^ (2 * C + 4 + 4) := by
    have h1 := mono_mul hℓ0 (by positivity) (by positivity) (mono_const hℓ0 (2 * kk ^ 2))
      (mono_atom (ℓ := ℓ) (2 * C))
    have h2 := mono_mul hℓ0 (by positivity) (by positivity) h1 (mono_const hℓ0 (KLM / αmin))
    have h3 := mono_mul hℓ0 (by positivity) (by positivity) h2 (mono_box hℓ)
    have h4 := mono_mul hℓ0 (by positivity) (by positivity) h3 (mono_box hℓ)
    convert h4 using 2 <;> ring
  have hCC : (ℓ ^ C * ℓ ^ C * ℓ ^ Cmk) ^ 2 ≤ 1 * ℓ ^ (2 * (C + C + Cmk)) := by
    rw [rpow3 hℓ0]; exact mono_sq hℓ0 _
  have hCCv : (ℓ ^ C * ℓ ^ C * (vmax * ℓ ^ Cmk)) ^ 2 ≤ vmax ^ 2 * ℓ ^ (2 * (C + C + Cmk)) := by
    have e : (ℓ ^ C * ℓ ^ C * (vmax * ℓ ^ Cmk)) ^ 2 = vmax ^ 2 * (ℓ ^ C * ℓ ^ C * ℓ ^ Cmk) ^ 2 := by
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hCC (sq_nonneg vmax)
    linarith
  have hCv : (ℓ ^ C * (vmax * ℓ ^ Cmk)) ^ 2 ≤ vmax ^ 2 * ℓ ^ (2 * (C + Cmk)) := by
    have e : (ℓ ^ C * (vmax * ℓ ^ Cmk)) ^ 2 = vmax ^ 2 * (ℓ ^ C * ℓ ^ Cmk) ^ 2 := by ring
    rw [e, ← Real.rpow_add hℓ0]
    have := mul_le_mul_of_nonneg_left (mono_sq hℓ0 (C + Cmk)) (sq_nonneg vmax)
    linarith
  have hKl2 : (Kl * ℓ ^ (-Al)) ^ 2 ≤ Kl ^ 2 * ℓ ^ (2 * (-Al)) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left ((mono_sq hℓ0 _).trans_eq (one_mul _)) (sq_nonneg Kl)
  have hW16 : KW * (16 * (1 + 2 * ℓ)) ≤ 3 * (16 * KW) * ℓ ^ (1 : ℝ) := by
    rw [Real.rpow_one]; nlinarith
  have h2l : 2 * ℓ ≤ 2 * ℓ ^ (1 : ℝ) := by rw [Real.rpow_one]
  have h16 : 1 + 16 * ℓ ≤ 17 * ℓ ^ (1 : ℝ) := by
    have := mono_lin hℓ 1 16 (by norm_num) (by norm_num); norm_num at this ⊢; linarith
  have hB0 : 2 * ℓ ^ B0 ≤ 2 * ℓ ^ B0 := le_rfl
  -- expansion
  have hexp : 2 * kk ^ 2 * ℓ ^ (2 * C) *
      Psi1 ℓ KLM αmin Kmm K3r c3r As Al Kl B0 B C Cmk vmax KW cW KAm At j =
      2 * kk ^ 2 * ℓ ^ (2 * C) * (KLM / αmin) * (3 * ℓ + 1) ^ 4 * (3 * ℓ + 1) ^ 4 * ℓ ^ Kmm *
          ℓ ^ Kmm * K3r * (ℓ ^ (-As)) ^ 2 * (1 + 16 * ℓ) * (ℓ ^ C * ℓ ^ C * ℓ ^ Cmk) ^ 2 *
          (2 * ℓ) ^ c3r +
        2 * kk ^ 2 * ℓ ^ (2 * C) * (KLM / αmin) * (3 * ℓ + 1) ^ 4 * (3 * ℓ + 1) ^ 4 * ℓ ^ Kmm *
          ℓ ^ Kmm * K3r * (Kl * ℓ ^ (-Al)) ^ 2 * (ℓ ^ C * ℓ ^ C * (vmax * ℓ ^ Cmk)) ^ 2 *
          (2 * ℓ) ^ c3r * (2 * ℓ) +
        2 * kk ^ 2 * ℓ ^ (2 * C) * (KLM / αmin) * (3 * ℓ + 1) ^ 4 * (3 * ℓ + 1) ^ 4 * ℓ ^ Kmm *
          ℓ ^ Kmm * (2 * ℓ ^ B0) * (ℓ ^ (-B)) ^ 2 * (ℓ ^ C * (vmax * ℓ ^ Cmk)) ^ 2 +
        2 * kk ^ 2 * ℓ ^ (2 * C) * (KLM / αmin) * (3 * ℓ + 1) ^ 4 * (3 * ℓ + 1) ^ 4 * ℓ ^ Kmm *
          ℓ ^ Kmm * ((1 + ℓ) ^ (j - 4))⁻¹ * (KW * (16 * (1 + 2 * ℓ))) *
          (ℓ ^ C * ℓ ^ C * ℓ ^ Cmk) ^ 2 * (2 * ℓ) ^ cW +
        2 * kk ^ 2 * ℓ ^ (2 * C) * (KLM / αmin) * (3 * ℓ + 1) ^ 4 * (3 * ℓ + 1) ^ 4 * ℓ ^ Kmm *
          (KAm * ℓ ^ (-At)) * (KW * (16 * (1 + 2 * ℓ))) * (ℓ ^ C * ℓ ^ C * ℓ ^ Cmk) ^ 2 *
          (2 * ℓ) ^ cW := by
    unfold Psi1 PhiJ PhiW; ring
  rw [hexp]
  set Pre := 2 * kk ^ 2 * ℓ ^ (2 * C) * (KLM / αmin) * (3 * ℓ + 1) ^ 4 * (3 * ℓ + 1) ^ 4
  have hPre0 : 0 ≤ Pre := by positivity
  -- term bounds
  have t1 := mono_mul hℓ0 (by positivity) (by positivity)
    (mono_mul hℓ0 (by positivity) (by positivity)
      (mono_mul hℓ0 (by positivity) (by positivity)
        (mono_mul hℓ0 (by positivity) (by positivity)
          (mono_mul hℓ0 (by positivity) (by positivity)
            (mono_mul hℓ0 (by positivity) (by positivity)
              (mono_mul hℓ0 hPre0 (by positivity) hPre (mono_atom (ℓ := ℓ) Kmm))
              (mono_atom (ℓ := ℓ) Kmm)) (mono_const hℓ0 K3r)) (mono_sq hℓ0 (-As))) h16) hCC)
    (mono_two_pow hℓ0 c3r)
  have t2 := mono_mul hℓ0 (by positivity) (by positivity)
    (mono_mul hℓ0 (by positivity) (by positivity)
      (mono_mul hℓ0 (by positivity) (by positivity)
        (mono_mul hℓ0 (by positivity) (by positivity)
          (mono_mul hℓ0 (by positivity) (by positivity)
            (mono_mul hℓ0 (by positivity) (by positivity)
              (mono_mul hℓ0 hPre0 (by positivity) hPre (mono_atom (ℓ := ℓ) Kmm))
              (mono_atom (ℓ := ℓ) Kmm)) (mono_const hℓ0 K3r)) hKl2) hCCv)
      (mono_two_pow hℓ0 c3r)) h2l
  have t3 := mono_mul hℓ0 (by positivity) (by positivity)
    (mono_mul hℓ0 (by positivity) (by positivity)
      (mono_mul hℓ0 (by positivity) (by positivity)
        (mono_mul hℓ0 (by positivity) (by positivity)
          (mono_mul hℓ0 hPre0 (by positivity) hPre (mono_atom (ℓ := ℓ) Kmm))
          (mono_atom (ℓ := ℓ) Kmm))
        (show 2 * ℓ ^ B0 ≤ 2 * ℓ ^ B0 from le_rfl)) (mono_sq hℓ0 (-B))) hCv
  have t4 := mono_mul hℓ0 (by positivity) (by positivity)
    (mono_mul hℓ0 (by positivity) (by positivity)
      (mono_mul hℓ0 (by positivity) (by positivity)
        (mono_mul hℓ0 (by positivity) (by positivity)
          (mono_mul hℓ0 (by positivity) (by positivity)
            (mono_mul hℓ0 hPre0 (by positivity) hPre (mono_atom (ℓ := ℓ) Kmm))
            (mono_atom (ℓ := ℓ) Kmm)) (mono_w hℓ (j - 4))) hW16) hCC)
    (mono_two_pow hℓ0 cW)
  have t5 := mono_mul hℓ0 (by positivity) (by positivity)
    (mono_mul hℓ0 (by positivity) (by positivity)
      (mono_mul hℓ0 (by positivity) (by positivity)
        (mono_mul hℓ0 (by positivity) (by positivity)
          (mono_mul hℓ0 hPre0 (by positivity) hPre (mono_atom (ℓ := ℓ) Kmm))
          (show KAm * ℓ ^ (-At) ≤ KAm * ℓ ^ (-At) from le_rfl)) hW16) hCC)
    (mono_two_pow hℓ0 cW)
  have e3 : (2 * kk ^ 2 * (KLM / αmin) * 256 * 256 * 1 * 1 * 2 * 1 * vmax ^ 2) *
      ℓ ^ ((2 * C + 4 + 4) + Kmm + Kmm + B0 + 2 * (-B) + 2 * (C + Cmk)) =
      (2 * kk ^ 2 * (KLM / αmin) * 256 * 256 * 1 * 1 * 2 * 1 * vmax ^ 2) *
      ℓ ^ ((2 * C + 4 + 4) + Kmm + Kmm + B0 + 2 * (-B) + 2 * (C + Cmk)) := rfl
  linarith

theorem ev_psi1 (kk KLM αmin Kmm K3r c3r As Al Kl B0 B C Cmk vmax KW cW KAm At A : ℝ) (j : ℕ)
    (hkk : 0 ≤ kk) (hKLM : 0 ≤ KLM) (hα : 0 < αmin) (hK3 : 0 ≤ K3r)
    (hKl : 0 ≤ Kl) (hv : 0 ≤ vmax) (hKW : 0 ≤ KW) (hKA : 0 ≤ KAm)
    (he1 : (2 * C + 4 + 4) + Kmm + Kmm + 0 + 2 * (-As) + 1 + 2 * (C + C + Cmk) + c3r < -A)
    (he2 : (2 * C + 4 + 4) + Kmm + Kmm + 0 + 2 * (-Al) + 2 * (C + C + Cmk) + c3r + 1 < -A)
    (he3 : (2 * C + 4 + 4) + Kmm + Kmm + B0 + 2 * (-B) + 2 * (C + Cmk) < -A)
    (he4 : (2 * C + 4 + 4) + Kmm + Kmm + (-((j - 4 : ℕ) : ℝ)) + 1 + 2 * (C + C + Cmk) + cW < -A)
    (he5 : (2 * C + 4 + 4) + Kmm + (-At) + 1 + 2 * (C + C + Cmk) + cW < -A) :
    ∀ᶠ x : ℝ in atTop, 2 * kk ^ 2 * L x ^ (2 * C) *
      Psi1 (L x) KLM αmin Kmm K3r c3r As Al Kl B0 B C Cmk vmax KW cW KAm At j ≤
        L x ^ (-A) / 3 := by
  filter_upwards [
    ev_monomial_le (2 * kk ^ 2 * (KLM / αmin) * 256 * 256 * 1 * 1 * K3r * 1 * 17 * 1 * 2 ^ c3r)
      _ A 15 he1 (by norm_num),
    ev_monomial_le (2 * kk ^ 2 * (KLM / αmin) * 256 * 256 * 1 * 1 * K3r * Kl ^ 2 * vmax ^ 2 *
      2 ^ c3r * 2) _ A 15 he2 (by norm_num),
    ev_monomial_le (2 * kk ^ 2 * (KLM / αmin) * 256 * 256 * 1 * 1 * 2 * 1 * vmax ^ 2)
      _ A 15 he3 (by norm_num),
    ev_monomial_le (2 * kk ^ 2 * (KLM / αmin) * 256 * 256 * 1 * 1 * 1 * (3 * (16 * KW)) * 1 * 2 ^ cW)
      _ A 15 he4 (by norm_num),
    ev_monomial_le (2 * kk ^ 2 * (KLM / αmin) * 256 * 256 * 1 * KAm * (3 * (16 * KW)) * 1 * 2 ^ cW)
      _ A 15 he5 (by norm_num), ev_L_ge 1] with x h1 h2 h3 h4 h5 hL
  have := psi1_le_terms (ℓ := L x) (kk := kk) (KLM := KLM) (αmin := αmin) (Kmm := Kmm) (K3r := K3r)
    (c3r := c3r) (As := As) (Al := Al) (Kl := Kl) (B0 := B0) (B := B) (C := C) (Cmk := Cmk)
    (vmax := vmax) (KW := KW) (cW := cW) (KAm := KAm) (At := At) (j := j)
    hL hkk hKLM hα hK3 hKl hv hKW hKA
  linarith

theorem sq_rpow {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ) : (ℓ ^ a) ^ 2 = ℓ ^ (2 * a) := by
  have := mono_sq hℓ a
  rw [one_mul] at this
  apply le_antisymm this
  rw [← Real.rpow_natCast (ℓ ^ a) 2, ← Real.rpow_mul hℓ.le]
  norm_num; rw [mul_comm]

/-- Polylogarithms against `exp(-L^a)`. -/
theorem ev_poly_mul_exp_neg_rpow (c e a A : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, c * L x ^ e * Real.exp (-(L x ^ a)) ≤ L x ^ (-A) := by
  have ht : Tendsto (fun u : ℝ => u ^ ((e + A) / a) * Real.exp (-1 * u)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (by norm_num)
  have ht2 := ht.comp ((tendsto_rpow_atTop ha).comp tendsto_L)
  have hev : ∀ᶠ x : ℝ in atTop, (L x ^ a) ^ ((e + A) / a) * Real.exp (-1 * L x ^ a) ≤
      1 / (|c| + 1) := ht2.eventually (ge_mem_nhds (by positivity))
  filter_upwards [hev, ev_L_ge 1] with x hx hL1
  have hLpos : 0 < L x := by linarith
  have hpow : (L x ^ a) ^ ((e + A) / a) = L x ^ (e + A) := by
    rw [← Real.rpow_mul hLpos.le]; congr 1; field_simp
  rw [hpow, neg_one_mul] at hx
  have hsplit : L x ^ e = L x ^ (e + A) * L x ^ (-A) := by
    rw [← Real.rpow_add hLpos]; congr 1; ring
  have hc : c ≤ |c| + 1 := by linarith [le_abs_self c]
  have hLA : 0 < L x ^ (-A) := Real.rpow_pos_of_pos hLpos _
  have hE : 0 ≤ L x ^ (e + A) * Real.exp (-(L x ^ a)) := by positivity
  calc c * L x ^ e * Real.exp (-(L x ^ a))
      = c * (L x ^ (e + A) * Real.exp (-(L x ^ a))) * L x ^ (-A) := by rw [hsplit]; ring
    _ ≤ (|c| + 1) * (1 / (|c| + 1)) * L x ^ (-A) := by
        apply mul_le_mul_of_nonneg_right _ hLA.le
        exact mul_le_mul hc hx hE (by positivity)
    _ = L x ^ (-A) := by field_simp

/-- The piece coefficient term divided by `Y`. -/
theorem ev_psi2 (kk K0 b0 C v1 v2 Cmk KS hi cS αmin A : ℝ) (hkk : 0 ≤ kk) (hK0 : 0 ≤ K0)
    (hb0 : 0 ≤ b0) (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2) (hKS : 0 ≤ KS) (hhi : 0 ≤ hi) (hα : 0 < αmin) :
    ∀ᶠ x : ℝ in atTop, 2 * kk ^ 2 * L x ^ (2 * C) *
      (K0 * (b0 * L x ^ C) ^ 2 * (L x ^ C * v1 * 1 * (L x ^ C * (v2 * L x ^ Cmk))) ^ 2 *
        (KS * hi * (2 * L x) ^ cS) / αmin ^ 2 * Real.exp (-(1.96 * L x))) ≤ L x ^ (-A) / 3 := by
  filter_upwards [ev_poly_mul_exp_neg (3 * (2 * kk ^ 2 * K0 * b0 ^ 2 * v1 ^ 2 * v2 ^ 2 * KS * hi *
      2 ^ cS / αmin ^ 2)) (2 * C + 2 * C + 2 * (C + C + Cmk) + cS) 1.96 (by norm_num) A,
    ev_L_ge 1] with x h hL1
  have hLpos : 0 < L x := by linarith
  have hL : ∀ y : ℝ, 0 ≤ L x ^ y := fun y => Real.rpow_nonneg hLpos.le y
  have e1 : (b0 * L x ^ C) ^ 2 = b0 ^ 2 * L x ^ (2 * C) := by
    rw [mul_pow, sq_rpow hLpos]
  have e2 : (L x ^ C * v1 * 1 * (L x ^ C * (v2 * L x ^ Cmk))) ^ 2 =
      v1 ^ 2 * v2 ^ 2 * L x ^ (2 * (C + C + Cmk)) := by
    have : L x ^ C * v1 * 1 * (L x ^ C * (v2 * L x ^ Cmk)) = v1 * v2 * (L x ^ C * L x ^ C * L x ^ Cmk) := by
      ring
    rw [this, rpow3 hLpos, mul_pow, mul_pow, sq_rpow hLpos]
  have e3 : (2 * L x) ^ cS = 2 ^ cS * L x ^ cS := Real.mul_rpow (by norm_num) hLpos.le
  have hcomb : L x ^ (2 * C) * L x ^ (2 * C) * L x ^ (2 * (C + C + Cmk)) * L x ^ cS =
      L x ^ (2 * C + 2 * C + 2 * (C + C + Cmk) + cS) := by
    rw [Real.rpow_add hLpos, Real.rpow_add hLpos, Real.rpow_add hLpos]
  rw [e1, e2, e3]
  have hexpr : 2 * kk ^ 2 * L x ^ (2 * C) * (K0 * (b0 ^ 2 * L x ^ (2 * C)) *
      (v1 ^ 2 * v2 ^ 2 * L x ^ (2 * (C + C + Cmk))) * (KS * hi * (2 ^ cS * L x ^ cS)) / αmin ^ 2 *
      Real.exp (-(1.96 * L x))) = (2 * kk ^ 2 * K0 * b0 ^ 2 * v1 ^ 2 * v2 ^ 2 * KS * hi *
      2 ^ cS / αmin ^ 2) * (L x ^ (2 * C) * L x ^ (2 * C) * L x ^ (2 * (C + C + Cmk)) * L x ^ cS) *
      Real.exp (-(1.96 * L x)) := by ring
  rw [hexpr, hcomb]
  have h3 : 3 * (2 * kk ^ 2 * K0 * b0 ^ 2 * v1 ^ 2 * v2 ^ 2 * KS * hi * 2 ^ cS / αmin ^ 2) *
      L x ^ (2 * C + 2 * C + 2 * (C + C + Cmk) + cS) * Real.exp (-(1.96 * L x)) =
      3 * ((2 * kk ^ 2 * K0 * b0 ^ 2 * v1 ^ 2 * v2 ^ 2 * KS * hi * 2 ^ cS / αmin ^ 2) *
      L x ^ (2 * C + 2 * C + 2 * (C + C + Cmk) + cS) * Real.exp (-(1.96 * L x))) := by ring
  rw [h3] at h
  linarith

/-- The error term divided by `Y`. -/
theorem ev_psi3 (b0 C Cms Cmk J0 KE lo cE vmax a A : ℝ) (ha : 0 < a) (hb0 : 0 ≤ b0)
    (hJ0 : 0 ≤ J0) (hKE : 0 ≤ KE) (hlo : 0 ≤ lo) (hv : 0 ≤ vmax) :
    ∀ᶠ x : ℝ in atTop, 2 * ((b0 * L x ^ C * (L x ^ Cms + 3 * L x * L x ^ Cmk)) ^ 2 *
      (J0 * KE * lo * L x ^ (4 * C) * (2 * L x) ^ cE * (vmax * Real.exp (-(L x ^ a))))) ≤
        L x ^ (-A) / 3 := by
  set N := |Cms| + |Cmk| + 1 with hN
  filter_upwards [ev_poly_mul_exp_neg_rpow (6 * (b0 ^ 2 * 16 * J0 * KE * lo * 2 ^ cE * vmax))
      (2 * C + 2 * N + 4 * C + cE) a A ha, ev_L_ge 1] with x h hL1
  have hLpos : 0 < L x := by linarith
  have hM : L x ^ Cms + 3 * L x * L x ^ Cmk ≤ 4 * L x ^ N := by
    have h1 : L x ^ Cms ≤ L x ^ N :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by rw [hN]; linarith [le_abs_self Cms, abs_nonneg Cmk])
    have h2 : L x * L x ^ Cmk ≤ L x ^ N := by
      rw [show L x * L x ^ Cmk = L x ^ (1 + Cmk) by rw [Real.rpow_add hLpos, Real.rpow_one]]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by rw [hN]; linarith [le_abs_self Cmk, abs_nonneg Cms])
    linarith
  have hM0 : 0 ≤ L x ^ Cms + 3 * L x * L x ^ Cmk := by positivity
  have hpoly : (b0 * L x ^ C * (L x ^ Cms + 3 * L x * L x ^ Cmk)) ^ 2 ≤
      b0 ^ 2 * 16 * L x ^ (2 * C + 2 * N) := by
    have : (b0 * L x ^ C * (L x ^ Cms + 3 * L x * L x ^ Cmk)) ^ 2 ≤ (b0 * L x ^ C * (4 * L x ^ N)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hM (by positivity)) 2
    refine this.trans (le_of_eq ?_)
    calc (b0 * L x ^ C * (4 * L x ^ N)) ^ 2 = b0 ^ 2 * 16 * ((L x ^ C) ^ 2 * (L x ^ N) ^ 2) := by ring
      _ = b0 ^ 2 * 16 * (L x ^ (2 * C) * L x ^ (2 * N)) := by rw [sq_rpow hLpos, sq_rpow hLpos]
      _ = b0 ^ 2 * 16 * L x ^ (2 * C + 2 * N) := by rw [← Real.rpow_add hLpos]
  have e3 : (2 * L x) ^ cE = 2 ^ cE * L x ^ cE := Real.mul_rpow (by norm_num) hLpos.le
  have hrest0 : 0 ≤ J0 * KE * lo * L x ^ (4 * C) * (2 * L x) ^ cE * (vmax * Real.exp (-(L x ^ a))) := by
    positivity
  calc 2 * ((b0 * L x ^ C * (L x ^ Cms + 3 * L x * L x ^ Cmk)) ^ 2 *
        (J0 * KE * lo * L x ^ (4 * C) * (2 * L x) ^ cE * (vmax * Real.exp (-(L x ^ a)))))
      ≤ 2 * (b0 ^ 2 * 16 * L x ^ (2 * C + 2 * N) *
        (J0 * KE * lo * L x ^ (4 * C) * (2 * L x) ^ cE * (vmax * Real.exp (-(L x ^ a))))) := by
        gcongr
    _ = (6 * (b0 ^ 2 * 16 * J0 * KE * lo * 2 ^ cE * vmax)) *
          (L x ^ (2 * C + 2 * N) * L x ^ (4 * C) * L x ^ cE) * Real.exp (-(L x ^ a)) / 3 := by
        rw [e3]; ring
    _ = (6 * (b0 ^ 2 * 16 * J0 * KE * lo * 2 ^ cE * vmax)) *
          L x ^ (2 * C + 2 * N + 4 * C + cE) * Real.exp (-(L x ^ a)) / 3 := by
        rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
    _ ≤ L x ^ (-A) / 3 := by linarith

end Erdos821.P5Marked
