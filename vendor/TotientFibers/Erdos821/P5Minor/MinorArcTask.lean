import Erdos821.P5.MinorArcTask
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P5Minor
open Erdos821.Blueprint.Analytic

lemma exp_log_dominates (δ M : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, L x ^ M ≤ Real.exp (L x ^ δ) := by
  have hL : Tendsto (fun x : ℝ => L x) atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop
  have hY := (tendsto_rpow_atTop hδ).comp hL
  have hratio := (tendsto_exp_div_rpow_atTop (M / δ)).comp hY
  filter_upwards [hratio.eventually_ge_atTop 1, hL.eventually_gt_atTop 0] with x hx hpos
  have hpow : (L x ^ δ) ^ (M / δ) = L x ^ M := by
    calc
      (L x ^ δ) ^ (M / δ) = L x ^ (δ * (M / δ)) := by
        symm
        exact Real.rpow_mul hpos.le δ (M / δ)
      _ = L x ^ M := by congr 1 <;> field_simp
  have hden : 0 < L x ^ M := Real.rpow_pos_of_pos hpos _
  change 1 ≤ Real.exp (L x ^ δ) / (L x ^ δ) ^ (M / δ) at hx
  rw [hpow] at hx
  simpa using (le_div_iff₀ hden).1 hx


lemma dirichlet_approximation (α Qarg : ℝ) (hQ : 1 ≤ Qarg) :
    ∃ u : ℤ, ∃ r : ℕ, ∃ β : ℝ,
      1 ≤ r ∧ (r : ℝ) ≤ Qarg ∧ Nat.Coprime u.natAbs r ∧
        α = (u : ℝ) / r + β ∧ |β| ≤ (r : ℝ) ^ (-2 : ℤ) ∧
        |β| ≤ 1 / Qarg := by
  have hQarg : 0 ≤ Qarg := by linarith
  let Q : ℕ := ⌊Qarg⌋₊
  have hQpos : 0 < Q := by
    have hQone : 1 ≤ Q := by
      dsimp [Q]
      exact (Nat.one_le_floor_iff Qarg).2 hQ
    omega
  obtain ⟨q, happrox, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hQpos
  let u : ℤ := q.num
  let r : ℕ := q.den
  let β : ℝ := α - (q : ℝ)
  have hrpos : 0 < r := by exact Rat.pos q
  have hrone : 1 ≤ r := by omega
  have hrarg : (r : ℝ) ≤ Qarg := by
    calc
      (r : ℝ) ≤ Q := by exact_mod_cast hden
      _ ≤ Qarg := by
        dsimp [Q]
        exact Nat.floor_le hQarg
  have hrep : (q : ℝ) = (u : ℝ) / r := by
    dsimp [u, r]
    exact Rat.cast_def q
  have heq : α = (u : ℝ) / r + β := by
    rw [← hrep]
    dsimp [β]
    ring
  have happrox' : |β| ≤ 1 / (((Q : ℝ) + 1) * (r : ℝ)) := by
    dsimp [β]
    simpa [Q, r, Nat.cast_add, Nat.cast_one, Nat.cast_mul] using happrox
  have hdenom : (r : ℝ) * (r : ℝ) ≤ ((Q : ℝ) + 1) * (r : ℝ) := by
    exact mul_le_mul_of_nonneg_right (by
      have : (r : ℝ) ≤ Q := by exact_mod_cast hden
      linarith) (by positivity)
  have hrecip : 1 / (((Q : ℝ) + 1) * (r : ℝ)) ≤
      1 / ((r : ℝ) * (r : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) hdenom
  have hbeta : |β| ≤ (r : ℝ) ^ (-2 : ℤ) := by
    have hz : (r : ℝ) ^ (-2 : ℤ) = 1 / ((r : ℝ) * (r : ℝ)) := by
      rw [zpow_neg, zpow_ofNat, pow_two]
      simp [div_eq_mul_inv]
    rw [hz]
    exact happrox'.trans hrecip
  have happroxQ : |β| ≤ 1 / ((Q : ℝ) + 1) := by
    exact happrox'.trans (one_div_le_one_div_of_le (by positivity) (by
      have hrR : 1 ≤ (r : ℝ) := by exact_mod_cast hrone
      nlinarith))
  have hQlt : Qarg < (Q : ℝ) + 1 := by
    dsimp [Q]
    exact Nat.lt_floor_add_one Qarg
  have hsmall : |β| ≤ 1 / Qarg := by
    exact happroxQ.trans (one_div_lt_one_div_of_lt (by linarith) hQlt).le
  refine ⟨u, r, β, hrone, hrarg, ?_, heq, hbeta, hsmall⟩
  simpa [u, r] using q.reduced

lemma scaled_fraction (k u : ℤ) (r : ℕ) (hk : k ≠ 0) (hr : 0 < r) :
    ((-(u * k.sign) : ℤ) : ℝ) / ((r * k.natAbs : ℕ) : ℝ) =
      -((u : ℝ) / (r : ℝ)) / (k : ℝ) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hsignZ : k.sign * k = (k.natAbs : ℤ) := Int.sign_mul_self_eq_natAbs k
  have hsign : (k.sign : ℝ) * (k : ℝ) = (k.natAbs : ℝ) := by
    calc
      (k.sign : ℝ) * (k : ℝ) = ((k.sign * k : ℤ) : ℝ) := by norm_cast
      _ = ((k.natAbs : ℤ) : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) hsignZ
      _ = (k.natAbs : ℝ) := by simp [Int.natCast_natAbs]
  have hmul := congrArg (fun z : ℝ => -(u : ℝ) * z) hsign
  push_cast
  field_simp [hkR, hrR]
  ring_nf at hmul ⊢
  linarith

lemma large_denominator_of_minor_arc
    (C Cp Carc L H θ : ℝ) (k u : ℤ) (r : ℕ) (β : ℝ)
    (hL : 1 ≤ L) (hLpos : 0 < L) (hC : 0 ≤ C) (hCp : 0 ≤ Cp)
    (hCarc : C + Cp ≤ Carc) (hH : 0 < H)
    (hk : k ≠ 0) (hkbound : |(k : ℝ)| ≤ L ^ C)
    (hr : 1 ≤ r) (hrbound : (r : ℝ) ≤ H / L ^ Cp)
    (hphase : -(k : ℝ) * θ = (u : ℝ) / (r : ℝ) + β)
    (hbeta : |β| ≤ L ^ Cp / H)
    (harc : ∀ (q : ℕ) (v : ℤ), 1 ≤ q → (q : ℝ) ≤ L ^ Carc →
      L ^ Carc / H < |θ - (v : ℝ) / (q : ℝ)|) :
    L ^ Cp < (r : ℝ) := by
  by_contra hnot
  have hrsmall : (r : ℝ) ≤ L ^ Cp := le_of_not_gt hnot
  let d : ℕ := r * k.natAbs
  let v : ℤ := -(u * k.sign)
  have hkabsNat : 1 ≤ k.natAbs := by
    have hpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk
    omega
  have hdpos : 1 ≤ d := by
    dsimp [d]
    nlinarith [hr, hkabsNat]
  have hkabs : (k.natAbs : ℝ) = |(k : ℝ)| := by
    simp
  have hdbound : (d : ℝ) ≤ L ^ Carc := by
    have hkabsbound : (k.natAbs : ℝ) ≤ L ^ C := by simpa [hkabs] using hkbound
    have hprod : (r : ℝ) * (k.natAbs : ℝ) ≤ L ^ Cp * L ^ C :=
      mul_le_mul hrsmall hkabsbound (by positivity) (by positivity)
    have hpow : L ^ Cp * L ^ C = L ^ (Cp + C) := by
      rw [Real.rpow_add hLpos Cp C]
    have hexp : Cp + C ≤ Carc := by linarith
    have hmono : L ^ (Cp + C) ≤ L ^ Carc :=
      Real.rpow_le_rpow_of_exponent_le hL hexp
    calc
      (d : ℝ) = (r : ℝ) * (k.natAbs : ℝ) := by simp [d, Nat.cast_mul]
      _ ≤ L ^ Cp * L ^ C := hprod
      _ = L ^ (Cp + C) := hpow
      _ ≤ L ^ Carc := hmono
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hcenter : (v : ℝ) / (d : ℝ) =
      -((u : ℝ) / (r : ℝ)) / (k : ℝ) := by
    dsimp [v, d]
    exact scaled_fraction k u r hk (by omega)
  have hlin : (k : ℝ) * θ + (u : ℝ) / (r : ℝ) = -β := by
    linarith [hphase]
  have htheta : θ + ((u : ℝ) / (r : ℝ)) / (k : ℝ) = -β / (k : ℝ) := by
    calc
      θ + ((u : ℝ) / (r : ℝ)) / (k : ℝ) =
          ((k : ℝ) * θ + (u : ℝ) / (r : ℝ)) / (k : ℝ) := by
            field_simp [hkR]
      _ = -β / (k : ℝ) := by rw [hlin]
  have hdist : |θ - (v : ℝ) / (d : ℝ)| = |β| / |(k : ℝ)| := by
    calc
      |θ - (v : ℝ) / (d : ℝ)| = |θ + ((u : ℝ) / (r : ℝ)) / (k : ℝ)| := by
        rw [hcenter]
        congr 1 <;> ring
      _ = |-β / (k : ℝ)| := by rw [← htheta]
      _ = |β| / |(k : ℝ)| := by simp [abs_div]
  have hkabsone : 1 ≤ |(k : ℝ)| := by
    have hnat : 1 ≤ k.natAbs := hkabsNat
    rw [← hkabs]
    exact_mod_cast hnat
  have hbetaDiv : |β| / |(k : ℝ)| ≤ |β| := by
    apply (div_le_iff₀ (abs_pos.mpr hkR)).2
    calc
      |β| = |β| * 1 := by ring
      _ ≤ |β| * |(k : ℝ)| :=
        mul_le_mul_of_nonneg_left hkabsone (abs_nonneg β)
  have hdistSmall : |θ - (v : ℝ) / (d : ℝ)| ≤ L ^ Cp / H :=
    (hdist ▸ hbetaDiv).trans hbeta
  have hpowArc : L ^ Cp ≤ L ^ Carc :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hthreshold : L ^ Cp / H ≤ L ^ Carc / H :=
    div_le_div_of_nonneg_right hpowArc (le_of_lt hH)
  have hArc := harc d v hdpos hdbound
  linarith

lemma bilinear_factor_bound
    (C A L U V r ell : ℝ)
    (hL : 9 ≤ L) (hLpos : 0 < L) (hC : 0 < C) (hA : 0 < A)
    (hU : L ^ (2 * C + 2 * A + 10) ≤ U)
    (hV : L ^ (2 * C + 2 * A + 10) ≤ V)
    (hrlo : L ^ (4 * C + 4 * A + 20) < r)
    (hrhi : r ≤ U * V / L ^ (4 * C + 4 * A + 20))
    (hell : 0 ≤ ell) (hellhi : ell ≤ 3 * L) :
    (L ^ C / U) * (L ^ C / V) *
      (U + (1 + V / r) * (U + r * ell)) ≤ L ^ (-2 * A) := by
  let m : ℝ := 2 * C + 2 * A
  let Cp : ℝ := 4 * C + 4 * A + 20
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hCpEq : Cp = 2 * m + 20 := by dsimp [Cp, m]; ring
  have hUEq : 2 * C + 2 * A + 10 = m + 10 := by dsimp [m]
  have hVpowpos : 0 < L ^ (m + 10) := Real.rpow_pos_of_pos hLpos _
  have hUpowle : L ^ (m + 10) ≤ U := by simpa [← hUEq] using hU
  have hVpowle : L ^ (m + 10) ≤ V := by simpa [← hUEq] using hV
  have hUpos : 0 < U := lt_of_lt_of_le hVpowpos hUpowle
  have hVpos : 0 < V := lt_of_lt_of_le hVpowpos hVpowle
  have hCpPos : 0 < Cp := by dsimp [Cp]; positivity
  have hRpowpos : 0 < L ^ Cp := Real.rpow_pos_of_pos hLpos Cp
  have hRpowone : 1 ≤ L ^ Cp := by
    apply Real.one_le_rpow (by linarith) (by linarith)
  have hrpos : 0 < r := lt_trans hRpowpos hrlo
  have hHpos : 0 < U * V := mul_pos hUpos hVpos
  have hHbound : 0 < U * V / L ^ Cp := div_pos hHpos hRpowpos
  have hm9leCp : m + 9 ≤ Cp := by rw [hCpEq]; linarith [hm]
  have hm10leCp : m + 10 ≤ Cp := by rw [hCpEq]; linarith [hm]
  have hpowm9 : L ^ (m + 9) ≤ L ^ Cp :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hm9leCp
  have hpowm10 : L ^ (m + 10) ≤ L ^ Cp :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hm10leCp
  have hpow9le10 : L ^ (m + 9) ≤ L ^ (m + 10) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hInvUstrong : 1 / U ≤ 1 / L ^ (m + 10) :=
    one_div_le_one_div_of_le hVpowpos hUpowle
  have hInvVstrong : 1 / V ≤ 1 / L ^ (m + 10) :=
    one_div_le_one_div_of_le hVpowpos hVpowle
  have hInvU : 1 / U ≤ 1 / L ^ (m + 9) :=
    hInvUstrong.trans (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hLpos _)
      hpow9le10)
  have hInvV : 1 / V ≤ 1 / L ^ (m + 9) :=
    hInvVstrong.trans (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hLpos _)
      hpow9le10)
  have hInvR : 1 / r ≤ 1 / L ^ (m + 9) := by
    have hpowr : L ^ Cp ≤ r := hrlo.le
    exact (one_div_le_one_div_of_le hRpowpos hpowr).trans
      (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hLpos _) hpowm9)
  have hRdiv : r / (U * V) ≤ 1 / L ^ Cp := by
    apply (div_le_iff₀ hHpos).2
    calc
      r ≤ U * V / L ^ Cp := hrhi
      _ = (1 / L ^ Cp) * (U * V) := by ring
  have hcross : r * ell / (U * V) ≤ ell / L ^ Cp := by
    calc
      r * ell / (U * V) = (r / (U * V)) * ell := by ring
      _ ≤ (1 / L ^ Cp) * ell :=
        mul_le_mul_of_nonneg_right hRdiv hell
      _ = ell / L ^ Cp := by ring
  have hcross' : r * ell / (U * V) ≤ 3 / L ^ (m + 9) := by
    have hInvCp : 1 / L ^ Cp ≤ 1 / L ^ (m + 10) :=
      one_div_le_one_div_of_le hVpowpos hpowm10
    calc
      r * ell / (U * V) ≤ ell / L ^ Cp := hcross
      _ ≤ (3 * L) / L ^ Cp :=
        div_le_div_of_nonneg_right hellhi (le_of_lt hRpowpos)
      _ = (3 * L) * (1 / L ^ Cp) := by ring
      _ ≤ (3 * L) * (1 / L ^ (m + 10)) :=
        mul_le_mul_of_nonneg_left hInvCp (by positivity)
      _ = (3 * L) / L ^ (m + 10) := by ring
      _ = 3 / L ^ (m + 9) := by
        have hpow : L ^ (m + 10) = L ^ (m + 9) * L := by
          calc
            L ^ (m + 10) = L ^ ((m + 9) + 1) := by congr 1 <;> ring
            _ = L ^ (m + 9) * L ^ (1 : ℝ) := Real.rpow_add hLpos _ _
            _ = L ^ (m + 9) * L := by rw [Real.rpow_one]
        rw [hpow]
        field_simp
  have hlogterm : ell / U ≤ 3 / L ^ (m + 9) := by
    calc
      ell / U = ell * (1 / U) := by ring
      _ ≤ (3 * L) * (1 / U) :=
        mul_le_mul_of_nonneg_right hellhi (by positivity)
      _ ≤ (3 * L) * (1 / L ^ (m + 10)) :=
        mul_le_mul_of_nonneg_left hInvUstrong (by positivity)
      _ = 3 / L ^ (m + 9) := by
        have hpow : L ^ (m + 10) = L ^ (m + 9) * L := by
          calc
            L ^ (m + 10) = L ^ ((m + 9) + 1) := by congr 1 <;> ring
            _ = L ^ (m + 9) * L ^ (1 : ℝ) := Real.rpow_add hLpos _ _
            _ = L ^ (m + 9) * L := by rw [Real.rpow_one]
        rw [div_eq_mul_inv]
        rw [hpow]
        field_simp
  let B : ℝ := 2 / V + 1 / r + ell / U + r * ell / (U * V)
  have hB : B ≤ 9 / L ^ (m + 9) := by
    dsimp [B]
    have h1 : 2 / V ≤ 2 / L ^ (m + 9) := by
      calc
        2 / V = 2 * (1 / V) := by ring
        _ ≤ 2 * (1 / L ^ (m + 9)) :=
          mul_le_mul_of_nonneg_left hInvV (by norm_num)
        _ = 2 / L ^ (m + 9) := by ring
    have h2 : 1 / r ≤ 1 / L ^ (m + 9) := hInvR
    calc
      2 / V + 1 / r + ell / U + r * ell / (U * V) ≤
          2 / L ^ (m + 9) + 1 / L ^ (m + 9) +
            3 / L ^ (m + 9) + 3 / L ^ (m + 9) :=
        add_le_add (add_le_add (add_le_add h1 h2) hlogterm) hcross'
      _ = 9 / L ^ (m + 9) := by ring
  have hL9 : 9 ≤ L ^ (9 : ℝ) := by
    have hpow : L = L ^ (1 : ℝ) := by rw [Real.rpow_one]
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L)
      (by norm_num : (1 : ℝ) ≤ 9)
    rw [← hpow] at h
    linarith
  have hBgoal : B ≤ 1 / L ^ m := by
    have hrecip : 9 / L ^ (9 : ℝ) ≤ 1 := by
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hLpos _)).2
      nlinarith [hL9]
    calc
      B ≤ 9 / L ^ (m + 9) := hB
      _ = (1 / L ^ m) * (9 / L ^ (9 : ℝ)) := by
        rw [Real.rpow_add hLpos m 9]
        field_simp
      _ ≤ (1 / L ^ m) * 1 :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = 1 / L ^ m := by ring
  have hpowC : L ^ C * L ^ C = L ^ (2 * C) := by
    calc
      L ^ C * L ^ C = L ^ (C + C) := (Real.rpow_add hLpos C C).symm
      _ = L ^ (2 * C) := by congr 1 <;> ring
  have hfactor :
      (L ^ C / U) * (L ^ C / V) *
        (U + (1 + V / r) * (U + r * ell)) =
          L ^ (2 * C) * B := by
    calc
      (L ^ C / U) * (L ^ C / V) *
          (U + (1 + V / r) * (U + r * ell)) =
          (L ^ C * L ^ C) *
            (2 / V + 1 / r + ell / U + r * ell / (U * V)) := by
              field_simp [ne_of_gt hUpos, ne_of_gt hVpos, ne_of_gt hrpos]
              ring
      _ = L ^ (2 * C) * B := by rw [hpowC]
  have hpowm : L ^ m = L ^ (2 * C) * L ^ (2 * A) := by
    rw [show m = 2 * C + 2 * A by rfl, Real.rpow_add hLpos]
  have hlast : L ^ (2 * C) * (1 / L ^ m) = L ^ (-2 * A) := by
    rw [hpowm]
    rw [show -2 * A = -(2 * A) by ring]
    rw [Real.rpow_neg (le_of_lt hLpos) (2 * A)]
    field_simp
  calc
    (L ^ C / U) * (L ^ C / V) *
        (U + (1 + V / r) * (U + r * ell)) = L ^ (2 * C) * B := hfactor
    _ ≤ L ^ (2 * C) * (1 / L ^ m) :=
      mul_le_mul_of_nonneg_left hBgoal (by positivity)
    _ = L ^ (-2 * A) := hlast

end Erdos821.P5Minor

namespace Erdos821.P5Core

open Erdos821.Blueprint.Analytic

theorem minorArcTask_proof : MinorArcTask := by
  intro hbil C δ A hC hδ hA
  obtain ⟨K₀, hK₀, hbil⟩ := hbil 2 (by norm_num)
  let Cp : ℝ := 4 * C + 4 * A + 20
  let Carc : ℝ := C + Cp + 1
  have hCpPos : 0 < Cp := by dsimp [Cp]; positivity
  have hCarcPos : 0 < Carc := by dsimp [Carc]; positivity
  have hCpHalf : Cp / 2 = 2 * C + 2 * A + 10 := by dsimp [Cp]; ring
  have hExpAbsorb := Erdos821.P5Minor.exp_log_dominates δ (Cp / 2) hδ
  have hXevent : ∀ᶠ x : ℝ in atTop, Real.exp 9 ≤ x :=
    Filter.eventually_ge_atTop (Real.exp 9)
  refine ⟨Carc, K₀, hCarcPos, hK₀, ?_⟩
  filter_upwards [hExpAbsorb, hXevent] with x hExp hx
  intro U V θ k s t a b hUexp hVexp hUV hk hkbound hs ht hsa hsb harc
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 9) hx
  have hL : 9 ≤ L x := by
    have hlog := Real.log_le_log (Real.exp_pos 9) hx
    simpa [L, Real.log_exp] using hlog
  have hLpos : 0 < L x := by linarith
  have hLone : 1 ≤ L x := by linarith
  have hCpNonneg : 0 ≤ Cp := le_of_lt hCpPos
  have hLpPos : 0 < L x ^ Cp := Real.rpow_pos_of_pos hLpos Cp
  have hLpOne : 1 ≤ L x ^ Cp := Real.one_le_rpow hLone hCpNonneg
  have hPowHalf : L x ^ (2 * C + 2 * A + 10) ≤
      Real.exp (L x ^ δ) := by
    simpa [hCpHalf] using hExp
  have hUlow : L x ^ (2 * C + 2 * A + 10) ≤ U :=
    hPowHalf.trans hUexp
  have hVlow : L x ^ (2 * C + 2 * A + 10) ≤ V :=
    hPowHalf.trans hVexp
  have hLδone : 1 ≤ L x ^ δ := Real.one_le_rpow hLone hδ.le
  have hexpOne : 1 ≤ Real.exp (L x ^ δ) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hUone : 1 ≤ U := hexpOne.trans hUexp
  have hVone : 1 ≤ V := hexpOne.trans hVexp
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num) hUone
  have hVpos : 0 < V := lt_of_lt_of_le (by norm_num) hVone
  let H : ℝ := U * V
  have hHpos : 0 < H := by dsimp [H]; exact mul_pos hUpos hVpos
  have hPowSplit : L x ^ Cp =
      L x ^ (Cp / 2) * L x ^ (Cp / 2) := by
    calc
      L x ^ Cp = L x ^ (Cp / 2 + Cp / 2) := by congr 1 <;> ring
      _ = L x ^ (Cp / 2) * L x ^ (Cp / 2) :=
        Real.rpow_add hLpos _ _
  have hProductLow : L x ^ Cp ≤ H := by
    calc
      L x ^ Cp = L x ^ (Cp / 2) * L x ^ (Cp / 2) := hPowSplit
      _ ≤ U * V := by
        apply mul_le_mul
        · simpa [hCpHalf] using hUlow
        · simpa [hCpHalf] using hVlow
        · positivity
        · positivity
      _ = H := by rfl
  have hArgOne : 1 ≤ H / (L x ^ Cp) := by
    apply (le_div_iff₀ hLpPos).2
    simpa using hProductLow
  let α : ℝ := -(k : ℝ) * θ
  obtain ⟨u, r, β, hrone, hrarg, hcoprime, hphase, hbeta, hbetaSmall⟩ :=
    Erdos821.P5Minor.dirichlet_approximation α (H / (L x ^ Cp)) hArgOne
  have hbetaArc : |β| ≤ L x ^ Cp / H := by
    calc
      |β| ≤ 1 / (H / L x ^ Cp) := hbetaSmall
      _ = L x ^ Cp / H := by field_simp [ne_of_gt hHpos, ne_of_gt hLpPos]
  have hCarcBound : C + Cp ≤ Carc := by dsimp [Carc]; linarith
  have hlarge : L x ^ Cp < (r : ℝ) :=
    Erdos821.P5Minor.large_denominator_of_minor_arc
      C Cp Carc (L x) H θ k u r β hLone hLpos hC.le hCpNonneg
      hCarcBound hHpos hk hkbound hrone hrarg hphase hbetaArc harc
  let ell : ℝ := Real.log (2 * (r : ℝ))
  have hrRealOne : 1 ≤ (r : ℝ) := by exact_mod_cast hrone
  have hellNonneg : 0 ≤ ell := by
    dsimp [ell]
    apply Real.log_nonneg
    nlinarith
  have hrleH : (r : ℝ) ≤ H := by
    have hdiv : H / L x ^ Cp ≤ H := by
      apply (div_le_iff₀ hLpPos).2
      calc
        H = 1 * H := by ring
        _ ≤ L x ^ Cp * H :=
          mul_le_mul_of_nonneg_right hLpOne hHpos.le
        _ = H * L x ^ Cp := by ring
    exact hrarg.trans hdiv
  have hrleXsq : (r : ℝ) ≤ x ^ (2 : ℕ) := by
    calc
      (r : ℝ) ≤ H := hrleH
      _ = U * V := by rfl
      _ ≤ x ^ (2 : ℕ) := hUV
  have hLogArgLe : 2 * (r : ℝ) ≤ 2 * x ^ 2 := by nlinarith
  have hLogMono : Real.log (2 * (r : ℝ)) ≤ Real.log (2 * x ^ 2) :=
    Real.log_le_log (by nlinarith [hrRealOne]) hLogArgLe
  have hLogExpand : Real.log (2 * x ^ 2) = Real.log 2 + 2 * L x := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hxpos.ne'), Real.log_pow]
    simp [L]
  have hLogTwo : Real.log 2 ≤ 1 := by
    calc
      Real.log 2 ≤ (2 : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
      _ = 1 := by norm_num
  have hellBound : ell ≤ 3 * L x := by
    dsimp [ell]
    rw [hLogExpand] at hLogMono
    linarith
  have hFactor :=
    Erdos821.P5Minor.bilinear_factor_bound C A (L x) U V (r : ℝ) ell
      hL hLpos hC hA hUlow hVlow (by simpa [Cp] using hlarge)
      (by simpa [H, Cp] using hrarg) hellNonneg hellBound
  have hIntervals : ∀ n ∈ s,
      U ≤ (n : ℝ) ∧ (n : ℝ) ≤ U + (2 : ℝ) * U := by
    intro n hn
    rcases hs n hn with ⟨hnlo, hnhi⟩
    exact ⟨hnlo, by linarith [hUpos]⟩
  have hIntervals' : ∀ n ∈ t,
      V ≤ (n : ℝ) ∧ (n : ℝ) ≤ V + (2 : ℝ) * V := by
    intro n hn
    rcases ht n hn with ⟨hnlo, hnhi⟩
    exact ⟨hnlo, by linarith [hVpos]⟩
  have hBilinear :=
    hbil U V U V α β u r s t a b hUone hVone hrone hcoprime hphase hbeta
      hIntervals hIntervals'
  have hsa0 : 0 ≤ (∑ n ∈ s, ‖a n‖ ^ 2) := by
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hsb0 : 0 ≤ (∑ n ∈ t, ‖b n‖ ^ 2) := by
    apply Finset.sum_nonneg
    intro n hn
    positivity
  let S : ℝ := U + (1 + V / (r : ℝ)) * (U + (r : ℝ) * ell)
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    positivity
  let T : ℝ :=
    Real.sqrt (∑ n ∈ s, ‖a n‖ ^ 2) *
      Real.sqrt (∑ n ∈ t, ‖b n‖ ^ 2) * Real.sqrt S
  have hTnonneg : 0 ≤ T := by positivity [T]
  have hTargetNonneg : 0 ≤ (L x) ^ (-A) :=
    Real.rpow_nonneg (le_of_lt hLpos) _
  have hTargetSq : (L x ^ (-A)) ^ 2 = (L x) ^ (-2 * A) := by
    rw [pow_two]
    calc
      L x ^ (-A) * L x ^ (-A) = L x ^ ((-A) + (-A)) :=
        (Real.rpow_add hLpos (-A) (-A)).symm
      _ = L x ^ (-2 * A) := by congr 1 <;> ring
  have hTle : T ≤ (L x) ^ (-A) := by
    apply (sq_le_sq₀ hTnonneg hTargetNonneg).1
    have hTidentity : T ^ 2 =
        (∑ n ∈ s, ‖a n‖ ^ 2) * (∑ n ∈ t, ‖b n‖ ^ 2) * S := by
      dsimp [T]
      rw [show (Real.sqrt (∑ n ∈ s, ‖a n‖ ^ 2) *
          Real.sqrt (∑ n ∈ t, ‖b n‖ ^ 2) * Real.sqrt S) ^ 2 =
          (Real.sqrt (∑ n ∈ s, ‖a n‖ ^ 2)) ^ 2 *
            (Real.sqrt (∑ n ∈ t, ‖b n‖ ^ 2)) ^ 2 * (Real.sqrt S) ^ 2 by ring,
        Real.sq_sqrt hsa0, Real.sq_sqrt hsb0, Real.sq_sqrt hSnonneg]
    calc
      T ^ 2 = (∑ n ∈ s, ‖a n‖ ^ 2) *
          (∑ n ∈ t, ‖b n‖ ^ 2) * S := hTidentity
      _ ≤ (L x ^ C / U) * (L x ^ C / V) * S := by
        apply mul_le_mul_of_nonneg_right
        exact mul_le_mul hsa hsb hsb0 (by positivity)
        exact hSnonneg
      _ ≤ (L x) ^ (-2 * A) := hFactor
      _ = (L x ^ (-A)) ^ 2 := hTargetSq.symm
  calc
    ‖∑ n ∈ s, ∑ v ∈ t, a n * b v * e (α * n * v)‖ ≤ K₀ * T := by
      simpa [T, mul_assoc] using hBilinear
    _ ≤ K₀ * (L x) ^ (-A) :=
      mul_le_mul_of_nonneg_left hTle hK₀.le

end Erdos821.P5Core

example : Erdos821.P5Core.MinorArcTask :=
  @Erdos821.P5Core.minorArcTask_proof
