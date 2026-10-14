import Mathlib

/-! Scalar asymptotic absorption for the restored memory norm: the low-rank margin,
the high-rank geometric tail, the rank cutoff `r0`, and eventual facts in `L x`. -/

noncomputable section

namespace Erdos821.P3Restore

open Filter

theorem npow_eq_exp {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) :
    ℓ ^ k = Real.exp (k * Real.log ℓ) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hℓ, mul_comm]

theorem rpow_eq_exp {ℓ : ℝ} (hℓ : 0 < ℓ) (y : ℝ) :
    ℓ ^ y = Real.exp (Real.log ℓ * y) :=
  Real.rpow_def_of_pos hℓ y

theorem exp_pow' (y : ℝ) (k : ℕ) : Real.exp y ^ k = Real.exp (k * y) :=
  (Real.exp_nat_mul y k).symm

theorem sq_le_exp_eight {ℓ : ℝ} {a : ℕ} (hℓ : 0 < ℓ) (ha : (a : ℝ) ≤ ℓ ^ (4 : ℕ)) :
    (a : ℝ) ^ 2 ≤ Real.exp (8 * Real.log ℓ) := by
  calc (a : ℝ) ^ 2 ≤ (ℓ ^ (4 : ℕ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) ha 2
    _ = ℓ ^ (8 : ℕ) := by rw [← pow_mul]
    _ = Real.exp (8 * Real.log ℓ) := by rw [npow_eq_exp hℓ]; norm_num

theorem smallV_le {ℓ C c : ℝ} {a : ℕ} (hℓ : 0 < ℓ) (hC : 0 < C)
    (ha : (a : ℝ) ≤ ℓ ^ (4 : ℕ)) (h5 : 8 * Real.log ℓ + Real.log C ≤ ℓ ^ c / 2) :
    (a : ℝ) ^ 2 * (C / Real.exp (ℓ ^ c)) ≤ Real.exp (-(ℓ ^ c / 2)) := by
  calc (a : ℝ) ^ 2 * (C / Real.exp (ℓ ^ c))
      ≤ Real.exp (8 * Real.log ℓ) * (C / Real.exp (ℓ ^ c)) :=
        mul_le_mul_of_nonneg_right (sq_le_exp_eight hℓ ha)
          (div_nonneg hC.le (Real.exp_pos _).le)
    _ = Real.exp (8 * Real.log ℓ + Real.log C - ℓ ^ c) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log hC]; ring
    _ ≤ Real.exp (-(ℓ ^ c / 2)) := Real.exp_le_exp.mpr (by linarith)

theorem exp_neg_half_le {y : ℝ} (h6 : 2 * Real.log 2 ≤ y) :
    Real.exp (-(y / 2)) ≤ 1 / 2 := by
  have h2 : (1 : ℝ) / 2 = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  rw [h2]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Low ranks against the margin `G - E - Cv = 5`, high ranks against the geometric tail. -/
theorem scalar_bound (ℓ E Cv Ca Ch C c CG G K : ℝ) (n a r0 : ℕ)
    (hG : G = E + Cv + 5) (hK : K = 8 + 2 * (Ca + G))
    (hℓ : 4 ≤ ℓ) (hCv : 0 ≤ Cv) (hCa : 0 ≤ Ca) (hE : 0 ≤ E) (hC : 0 < C)
    (hCG0 : 0 ≤ CG) (hCG : CG ≤ ℓ ^ Cv) (ha : (a : ℝ) ≤ ℓ ^ (4 : ℕ))
    (hr0 : (r0 : ℝ) * (K + 1) + 1 + Cv ≤ 5 * n)
    (hr0' : 2 * (Ch + E + 2) * n * Real.log ℓ ≤ ℓ ^ c * r0)
    (h5 : 8 * Real.log ℓ + Real.log C ≤ ℓ ^ c / 2)
    (h6 : 2 * Real.log 2 ≤ ℓ ^ c)
    (h7 : Real.log 4 + Ch * Real.log ℓ ≤ 2 * n * Real.log ℓ) :
    r0 * (2 * CG ^ (n + 1) * (ℓ ^ (-G)) ^ n) *
        (max 1 ((a : ℝ) ^ 2 * (ℓ ^ Ca / ℓ ^ (-G)) ^ 2)) ^ r0 +
      ℓ ^ (Ch * ((n + 1 : ℕ) : ℝ)) * ((a : ℝ) ^ 2 * (C / Real.exp (ℓ ^ c))) ^ r0 /
        (1 - (a : ℝ) ^ 2 * (C / Real.exp (ℓ ^ c))) ≤
      ℓ ^ (-E * (n : ℝ)) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hT0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have hG5 : 5 ≤ G := by rw [hG]; linarith
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  have hfin : ℓ ^ (-E * (n : ℝ)) = Real.exp (Real.log ℓ * (-E * n)) := rpow_eq_exp hℓ0 _
  -- low ranks
  have hCGp : CG ^ (n + 1) ≤ Real.exp (((n : ℝ) + 1) * (Real.log ℓ * Cv)) := by
    calc CG ^ (n + 1) ≤ (ℓ ^ Cv) ^ (n + 1) := pow_le_pow_left₀ hCG0 hCG _
      _ = _ := by rw [rpow_eq_exp hℓ0, exp_pow']; push_cast; ring_nf
  have hCEp : (ℓ ^ (-G)) ^ n = Real.exp (n * (Real.log ℓ * (-G))) := by
    rw [rpow_eq_exp hℓ0, exp_pow']
  have hY : (a : ℝ) ^ 2 * (ℓ ^ Ca / ℓ ^ (-G)) ^ 2 ≤ Real.exp (Real.log ℓ * K) := by
    have hr : (ℓ ^ Ca / ℓ ^ (-G)) ^ 2 =
        Real.exp (2 * (Real.log ℓ * Ca - Real.log ℓ * (-G))) := by
      rw [rpow_eq_exp hℓ0, rpow_eq_exp hℓ0, ← Real.exp_sub, exp_pow']; norm_num
    rw [hr]
    calc _ ≤ Real.exp (8 * Real.log ℓ) * Real.exp (2 * (Real.log ℓ * Ca - Real.log ℓ * (-G))) :=
          mul_le_mul_of_nonneg_right (sq_le_exp_eight hℓ0 ha) (Real.exp_pos _).le
      _ = Real.exp (Real.log ℓ * K) := by rw [← Real.exp_add, hK]; ring_nf
  have hMax : max 1 ((a : ℝ) ^ 2 * (ℓ ^ Ca / ℓ ^ (-G)) ^ 2) ≤ Real.exp (Real.log ℓ * K) :=
    max_le (Real.one_le_exp (mul_nonneg hT0 hK0)) hY
  have hM0 : 0 ≤ max 1 ((a : ℝ) ^ 2 * (ℓ ^ Ca / ℓ ^ (-G)) ^ 2) :=
    le_trans zero_le_one (le_max_left _ _)
  have hMaxp : (max 1 ((a : ℝ) ^ 2 * (ℓ ^ Ca / ℓ ^ (-G)) ^ 2)) ^ r0 ≤
      Real.exp (r0 * (Real.log ℓ * K)) := by
    rw [← exp_pow']
    exact pow_le_pow_left₀ hM0 hMax r0
  have hr0e : (r0 : ℝ) ≤ Real.exp (((r0 : ℝ) + 1) * Real.log ℓ) / 4 := by
    have h1 : (r0 : ℝ) ≤ 4 ^ r0 := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 3 by norm_num) r0
      norm_num at this
      linarith
    have h2 : (4 : ℝ) ^ (r0 + 1) ≤ ℓ ^ (r0 + 1) := pow_le_pow_left₀ (by norm_num) hℓ _
    have h3 : ℓ ^ (r0 + 1) = Real.exp (((r0 : ℝ) + 1) * Real.log ℓ) := by
      rw [npow_eq_exp hℓ0]; push_cast; ring_nf
    rw [pow_succ] at h2
    rw [← h3]
    linarith
  have hlow : r0 * (2 * CG ^ (n + 1) * (ℓ ^ (-G)) ^ n) *
      (max 1 ((a : ℝ) ^ 2 * (ℓ ^ Ca / ℓ ^ (-G)) ^ 2)) ^ r0 ≤
      1 / 2 * Real.exp (Real.log ℓ * (-E * n)) := by
    have hinner : 2 * CG ^ (n + 1) * (ℓ ^ (-G)) ^ n ≤
        2 * Real.exp (((n : ℝ) + 1) * (Real.log ℓ * Cv)) *
          Real.exp (n * (Real.log ℓ * (-G))) := by
      rw [hCEp]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCGp (by norm_num))
        (Real.exp_pos _).le
    have hinner0 : 0 ≤ 2 * CG ^ (n + 1) * (ℓ ^ (-G)) ^ n :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hCG0 _))
        (pow_nonneg (Real.rpow_nonneg hℓ0.le _) _)
    calc _ ≤ (Real.exp (((r0 : ℝ) + 1) * Real.log ℓ) / 4) *
          (2 * Real.exp (((n : ℝ) + 1) * (Real.log ℓ * Cv)) *
            Real.exp (n * (Real.log ℓ * (-G)))) * Real.exp (r0 * (Real.log ℓ * K)) := by
          apply mul_le_mul (mul_le_mul hr0e hinner hinner0 (by positivity)) hMaxp
            (pow_nonneg hM0 _) (by positivity)
      _ = 1 / 2 * Real.exp (((r0 : ℝ) + 1) * Real.log ℓ +
            ((n : ℝ) + 1) * (Real.log ℓ * Cv) + n * (Real.log ℓ * (-G)) +
              r0 * (Real.log ℓ * K)) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
      _ ≤ 1 / 2 * Real.exp (Real.log ℓ * (-E * n)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.exp_le_exp.mpr
          have he : ((r0 : ℝ) + 1) * Real.log ℓ +
              ((n : ℝ) + 1) * (Real.log ℓ * Cv) + n * (Real.log ℓ * (-G)) +
                r0 * (Real.log ℓ * K) =
              Real.log ℓ * (-E * n) -
                Real.log ℓ * (5 * n - ((r0 : ℝ) * (K + 1) + 1 + Cv)) := by
            rw [hG]; ring
          rw [he]
          have := mul_nonneg hT0 (sub_nonneg.mpr hr0)
          linarith
  -- high ranks
  set V := (a : ℝ) ^ 2 * (C / Real.exp (ℓ ^ c)) with hV
  have hV0 : 0 ≤ V := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (div_nonneg hC.le (Real.exp_pos _).le)
  have hVle : V ≤ Real.exp (-(ℓ ^ c / 2)) := smallV_le hℓ0 hC ha h5
  have hhalf : Real.exp (-(ℓ ^ c / 2)) ≤ 1 / 2 := exp_neg_half_le h6
  have h1V : 0 < 1 - V := by linarith
  have hVp : V ^ r0 ≤ Real.exp (r0 * (-(ℓ ^ c / 2))) := by
    rw [← exp_pow']
    exact pow_le_pow_left₀ hV0 hVle r0
  have hZ : ℓ ^ (Ch * ((n + 1 : ℕ) : ℝ)) =
      Real.exp (Real.log ℓ * (Ch * ((n : ℝ) + 1))) := by
    rw [rpow_eq_exp hℓ0]; push_cast; ring_nf
  have hhigh : ℓ ^ (Ch * ((n + 1 : ℕ) : ℝ)) * V ^ r0 / (1 - V) ≤
      1 / 2 * Real.exp (Real.log ℓ * (-E * n)) := by
    rw [div_le_iff₀ h1V, hZ]
    have hZ0 : 0 ≤ Real.exp (Real.log ℓ * (Ch * ((n : ℝ) + 1))) * V ^ r0 :=
      mul_nonneg (Real.exp_pos _).le (pow_nonneg hV0 _)
    calc Real.exp (Real.log ℓ * (Ch * ((n : ℝ) + 1))) * V ^ r0
        ≤ Real.exp (Real.log ℓ * (Ch * ((n : ℝ) + 1))) * Real.exp (r0 * (-(ℓ ^ c / 2))) :=
          mul_le_mul_of_nonneg_left hVp (Real.exp_pos _).le
      _ = Real.exp (Real.log ℓ * (Ch * ((n : ℝ) + 1)) + r0 * (-(ℓ ^ c / 2))) := by
          rw [Real.exp_add]
      _ ≤ Real.exp (Real.log (1 / 4) + Real.log ℓ * (-E * n)) := by
          apply Real.exp_le_exp.mpr
          have h14 : Real.log (1 / 4) = - Real.log 4 := by
            rw [one_div, Real.log_inv]
          rw [h14]
          have he : (2 * (Ch + E + 2) * n * Real.log ℓ) / 2 =
              (Ch + E + 2) * n * Real.log ℓ := by ring
          have hr : (r0 : ℝ) * (-(ℓ ^ c / 2)) = -((ℓ ^ c * r0) / 2) := by ring
          rw [hr]
          have hlin : Real.log ℓ * (Ch * ((n : ℝ) + 1)) =
              Ch * Real.log ℓ + Ch * n * Real.log ℓ := by ring
          have hlin2 : Real.log ℓ * (-E * n) = -(E * n * Real.log ℓ) := by ring
          rw [hlin, hlin2]
          have hexp : (Ch + E + 2) * n * Real.log ℓ =
              Ch * n * Real.log ℓ + E * n * Real.log ℓ + 2 * n * Real.log ℓ := by ring
          have hq : (Ch + E + 2) * n * Real.log ℓ ≤ (ℓ ^ c * r0) / 2 := by linarith
          linarith
      _ = 1 / 4 * Real.exp (Real.log ℓ * (-E * n)) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ 1 / 2 * Real.exp (Real.log ℓ * (-E * n)) * (1 - V) := by
          have hE0 : 0 ≤ 1 / 2 * Real.exp (Real.log ℓ * (-E * n)) := by positivity
          have hh : (1 : ℝ) / 2 ≤ 1 - V := by linarith
          have := mul_le_mul_of_nonneg_left hh hE0
          linarith
  rw [hfin]
  linarith

theorem r0_bounds (ℓ c K C'' Cv : ℝ) (n : ℕ) (hℓ : 1 ≤ ℓ) (hK : 0 ≤ K) (hC'' : 0 ≤ C'')
    (hA3 : (K + 1) * C'' * Real.log ℓ ≤ ℓ ^ c) (hA4 : K + 2 + Cv ≤ 4 * n) :
    (⌈C'' * n * Real.log ℓ / ℓ ^ c⌉₊ : ℝ) * (K + 1) + 1 + Cv ≤ 5 * n ∧
      C'' * n * Real.log ℓ ≤ ℓ ^ c * ⌈C'' * n * Real.log ℓ / ℓ ^ c⌉₊ := by
  have hℓ0 : 0 < ℓ := by linarith
  have hc : 0 < ℓ ^ c := Real.rpow_pos_of_pos hℓ0 c
  have hT : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  set y := C'' * n * Real.log ℓ / ℓ ^ c with hy
  have hy0 : 0 ≤ y :=
    div_nonneg (mul_nonneg (mul_nonneg hC'' (Nat.cast_nonneg _)) hT) hc.le
  have hup := Nat.ceil_lt_add_one hy0
  have hdn := Nat.le_ceil y
  constructor
  · have h1 : y * (K + 1) ≤ n := by
      rw [hy, div_mul_eq_mul_div, div_le_iff₀ hc]
      have : C'' * n * Real.log ℓ * (K + 1) = n * ((K + 1) * C'' * Real.log ℓ) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hA3 (Nat.cast_nonneg _)
    have h2 : (⌈y⌉₊ : ℝ) * (K + 1) ≤ (y + 1) * (K + 1) :=
      mul_le_mul_of_nonneg_right hup.le (by linarith)
    calc (⌈y⌉₊ : ℝ) * (K + 1) + 1 + Cv ≤ (y + 1) * (K + 1) + 1 + Cv := by linarith
      _ = y * (K + 1) + (K + 2 + Cv) := by ring
      _ ≤ n + 4 * n := by linarith
      _ = 5 * n := by ring
  · have := (div_le_iff₀ hc).mp hdn
    linarith [mul_comm (⌈y⌉₊ : ℝ) (ℓ ^ c)]

theorem ev_log_le {c : ℝ} (hc : 0 < c) (D : ℝ) :
    ∀ᶠ ℓ : ℝ in atTop, D * Real.log ℓ ≤ ℓ ^ c := by
  have hD : 0 < |D| + 1 := by positivity
  have hε : (0 : ℝ) < 1 / (|D| + 1) := by positivity
  filter_upwards [(isLittleO_log_rpow_atTop hc).bound hε, eventually_ge_atTop (1 : ℝ)]
    with ℓ h hℓ
  have hT : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have hp : 0 ≤ ℓ ^ c := Real.rpow_nonneg (by linarith) c
  rw [Real.norm_of_nonneg hT, Real.norm_of_nonneg hp] at h
  have h' : (|D| + 1) * Real.log ℓ ≤ ℓ ^ c := by
    calc (|D| + 1) * Real.log ℓ ≤ (|D| + 1) * (1 / (|D| + 1) * ℓ ^ c) :=
          mul_le_mul_of_nonneg_left h hD.le
      _ = ℓ ^ c := by rw [← mul_assoc, mul_one_div_cancel hD.ne', one_mul]
  calc D * Real.log ℓ ≤ (|D| + 1) * Real.log ℓ :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self D]) hT
    _ ≤ ℓ ^ c := h'

theorem ev_rpow_ge {c : ℝ} (hc : 0 < c) (M : ℝ) : ∀ᶠ ℓ : ℝ in atTop, M ≤ ℓ ^ c :=
  (tendsto_rpow_atTop hc).eventually (eventually_ge_atTop M)

theorem ev_N_ge (M : ℝ) :
    ∀ᶠ ℓ : ℝ in atTop, M ≤ ((2 * ⌈ℓ ^ ((52 : ℝ) / 100)⌉₊ : ℕ) : ℝ) := by
  filter_upwards [ev_rpow_ge (by norm_num : (0 : ℝ) < 52 / 100) M,
    eventually_ge_atTop (0 : ℝ)] with ℓ h h0
  have h1 := Nat.le_ceil (ℓ ^ ((52 : ℝ) / 100))
  have h2 : 0 ≤ ℓ ^ ((52 : ℝ) / 100) := Real.rpow_nonneg h0 _
  push_cast
  linarith

theorem eventually_log {Q : ℝ → Prop} (h : ∀ᶠ ℓ : ℝ in atTop, Q ℓ) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, Q (Real.log x) :=
  Filter.eventually_atTop.mp (Real.tendsto_log_atTop.eventually h)


end Erdos821.P3Restore
