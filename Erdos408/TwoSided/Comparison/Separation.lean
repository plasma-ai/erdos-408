module

public import Erdos408.Extraction.Allocation.Groups
public import Erdos408.TwoSided.Setup

/-!
# Separation and endpoint energies

S5 of `blueprint/two_sided_correlation.md` §5.1 (PD §6.3, (6.17)–(6.19); WD §5.3). Fix a
pattern `(A, B, φ, φ', ψ, ψ', U, U')`, `C = A ∪ B` and `Y₀ = x U U'`.

* Mellin: `Ψ(w/(x D_C))/w = Y₀⁻¹ ρ₀(w/Y₀) ∫ a(ξ) (w/x)^{2πiξ} D_A^{-2πiξ} D_B^{-2πiξ} dξ`, where
  `w/Y₀ ∈ [κ⁻¹, κe²]` on the support; the unimodular factors enter `b₁ = φ D_A^{-iσ}` and
  `b₂ = φ' D_B^{-iσ}`, `σ = 2πξ`.
* Partition of unity: fixed pieces `ψ_{1,m}` supported in `[1, 2]` with
  `∑_m ψ_{1,m}(z/y_m) = 1/z` on `[κ⁻¹, κe²]`, as the local Mellin energy (PD Lemma 6.4)
  needs support in `[Y, 2Y]`.
* Form (6.18): `strippedComparison = ∫ a(ξ) x^{-iσ} ∑_m (y_m/Y_m) 𝔅_m(ξ) dξ`, where
  `𝔅_m = 𝔼_a b₁(D_A) b₂(D_B) ∑_w 𝒰_m(w) 𝒱(w + D_C)` (`comparisonBilinear`) and
  `𝒰_m = endpointCoeff … C (ψ' ∘ X_B) ψ_{1,m} Y_m σ`, `Y_m = y_m Y₀`.
* Energies (6.19): `|Y_m⁻¹ 𝔅_m| ≤ L^{C₅}` pointwise (U7, U9); no divisor moments (X4).

The helpers live in the namespace `Separation`; the crude forms of U7 and U9 used for (6.19)
are in `Setup.lean`.
-/

@[expose] public section

namespace Erdos408.TwoSided

open Filter MeasureTheory

/-- The bilinear form (6.18) of one partition piece `ψ₁` at scale `Y` and twist `σ`:
`∑_a ∏ μ(a) φ(D_A) D_A^{-iσ} φ'(D_B) D_B^{-iσ} ∑_{Y ≤ w ≤ 2Y} 𝒰(w) G(w + D_C) W^{ψ(X_A)}(w + D_C)`,
with `𝒰 = endpointCoeff … (A ∪ B) (ψ' ∘ X_B) ψ₁ Y σ`. -/
noncomputable def comparisonBilinear (x q q₀ : ℝ) {r d : ℕ} (a : Fin r → ℝ)
    (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) {J : ℕ} (A B : ι → Finset (Fin J)) (φ φ' ψ ψ' : ℕ → ℂ) (G : ℕ → ℝ)
    (ψ₁ : ℝ → ℂ) (Y σ : ℝ) : ℂ :=
  ∑ l ∈ auxLabels P (fun g => A g ∪ B g),
    ((∏ g, ∏ i ∈ A g ∪ B g, (harmonicMass (P g) * l g i)⁻¹ : ℝ) : ℂ) *
      (φ (slotProduct A l) * (slotProduct A l : ℂ) ^ (-((σ : ℂ) * Complex.I))) *
      (φ' (slotProduct B l) * (slotProduct B l : ℂ) ^ (-((σ : ℂ) * Complex.I))) *
      ∑ w ∈ Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊,
        endpointCoeff x q q₀ a u v Bc P (fun g => A g ∪ B g)
            (fun p => ψ' (slotProduct B fun g i => p g i.castSucc)) ψ₁ Y σ w *
          ((G (w + slotProduct (fun g => A g ∪ B g) l) : ℂ) *
            markedListWeight P q₀ (unsharedSlots fun g => A g ∪ B g)
              (fun p => ψ (slotProduct A fun g i => p g i.castSucc))
              (w + slotProduct (fun g => A g ∪ B g) l))

/-! ### The partition of unity -/

namespace Separation

/-- The points `y_m = a/2 + m a/4` of the partition. -/
private noncomputable def partPoint (a : ℝ) (m : ℕ) : ℝ :=
  a / 2 + m * (a / 4)

/-- The step `S_m(z) = smoothTransition(4(z - y_m)/a)`: `0` for `z ≤ y_m`, `1` from
`y_m + a/4 = y_{m+1}` on. -/
private noncomputable def partStep (a : ℝ) (m : ℕ) (z : ℝ) : ℝ :=
  Real.smoothTransition ((z - partPoint a m) / (a / 4))

/-- The piece `η_m = S_m - S_{m+1}` of the partition of unity. -/
private noncomputable def partBump (a : ℝ) (m : ℕ) (z : ℝ) : ℝ :=
  partStep a m z - partStep a (m + 1) z

/-- The piece `ψ_{1,m}(w) = η_m(y_m w)/(y_m w)`. -/
private noncomputable def partPiece (a : ℝ) (m : ℕ) (w : ℝ) : ℂ :=
  ((partBump a m (partPoint a m * w) * (partPoint a m * w)⁻¹ : ℝ) : ℂ)

/-- `S_m(z) = 0` for `z ≤ y_m`. -/
private theorem partStep_eq_zero {a : ℝ} (ha : 0 < a) {m : ℕ} {z : ℝ} (hz : z ≤ partPoint a m) :
    partStep a m z = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by positivity))

/-- `S_m(z) = 1` for `z ≥ y_m + a/4`. -/
private theorem partStep_eq_one {a : ℝ} (ha : 0 < a) {m : ℕ} {z : ℝ}
    (hz : partPoint a m + a / 4 ≤ z) : partStep a m z = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by positivity)]; linarith)

/-- `y_{m+1} = y_m + a/4`. -/
private theorem partPoint_succ (a : ℝ) (m : ℕ) : partPoint a (m + 1) = partPoint a m + a / 4 := by
  unfold partPoint
  push_cast
  ring

/-- `η_m` lives in `(y_m, y_m + a/2)`. -/
private theorem lt_of_partBump_ne_zero {a : ℝ} (ha : 0 < a) {m : ℕ} {z : ℝ}
    (hz : partBump a m z ≠ 0) : partPoint a m < z ∧ z < partPoint a m + a / 2 := by
  have hs := partPoint_succ a m
  by_contra h
  rcases not_and_or.1 h with h | h
  · refine hz ?_
    rw [partBump, partStep_eq_zero ha (not_lt.1 h), partStep_eq_zero ha (by linarith)]
    norm_num
  · refine hz ?_
    rw [partBump, partStep_eq_one ha (by linarith), partStep_eq_one ha (by linarith)]
    norm_num

/-- `y_m ≥ a/2`. -/
private theorem half_le_partPoint {a : ℝ} (ha : 0 < a) (m : ℕ) : a / 2 ≤ partPoint a m := by
  unfold partPoint
  have : 0 ≤ (m : ℝ) * (a / 4) := by positivity
  linarith

/-- `ψ_{1,m}` lives in `[1, 2]`. -/
private theorem le_of_partPiece_ne_zero {a : ℝ} (ha : 0 < a) {m : ℕ} {w : ℝ}
    (hw : partPiece a m w ≠ 0) : 1 ≤ w ∧ w ≤ 2 := by
  have hy := half_le_partPoint ha m
  have hy0 : 0 < partPoint a m := by linarith
  have hb : partBump a m (partPoint a m * w) ≠ 0 := by
    intro h
    apply hw
    simp [partPiece, h]
  obtain ⟨h₁, h₂⟩ := lt_of_partBump_ne_zero ha hb
  constructor
  · by_contra h
    have : partPoint a m * w < partPoint a m * 1 := mul_lt_mul_of_pos_left (not_le.1 h) hy0
    linarith
  · by_contra h
    have : partPoint a m * 2 < partPoint a m * w := mul_lt_mul_of_pos_left (not_le.1 h) hy0
    linarith

/-- The steps are smooth. -/
private theorem contDiff_partStep {a : ℝ} (m : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (partStep a m) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

/-- The pieces are smooth: they vanish near `w ≤ 1`, and `w ↦ (y_m w)⁻¹` is smooth on
`w > 0`. -/
private theorem contDiff_partPiece {a : ℝ} (ha : 0 < a) (m : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (partPiece a m) := by
  have hy0 : 0 < partPoint a m := by linarith [half_le_partPoint ha m]
  have hbump : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun w => partBump a m (partPoint a m * w) :=
    ((contDiff_partStep m).sub (contDiff_partStep (m + 1))).comp (contDiff_const.mul contDiff_id)
  refine Complex.ofRealCLM.contDiff.comp ?_
  rw [contDiff_iff_contDiffAt]
  intro w
  rcases lt_or_ge w 1 with hw | hw
  · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hw] with w' hw'
    by_contra h
    have h' : partPiece a m w' ≠ 0 := by
      rw [partPiece, Ne, Complex.ofReal_eq_zero]
      exact h
    exact absurd (le_of_partPiece_ne_zero ha h').1 (not_le.2 hw')
  · refine hbump.contDiffAt.mul ((contDiff_const.mul contDiff_id).contDiffAt.inv ?_)
    exact (mul_pos hy0 (show (0 : ℝ) < w by linarith)).ne'

/-- A smooth function supported in `[1, 2]` has bounded derivatives of every order. -/
private theorem exists_norm_iteratedDeriv_le {f : ℝ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hs : ∀ z, f z ≠ 0 → 1 ≤ z ∧ z ≤ 2) (j : ℕ) :
    ∃ C, ∀ z, ‖iteratedDeriv j f z‖ ≤ C := by
  have hc : HasCompactSupport f := HasCompactSupport.intro isCompact_Icc fun z hz => by
    by_contra h
    exact hz (Set.mem_Icc.2 (hs z h))
  have hcj : HasCompactSupport (iteratedDeriv j f) := by
    rw [iteratedDeriv_eq_iterate]
    clear hs
    induction j with
    | zero => exact hc
    | succ j ih => rw [Function.iterate_succ_apply']; exact ih.deriv
  exact (hf.continuous_iteratedDeriv j (by exact_mod_cast le_top)).bounded_above_of_compact_support
    hcj

end Separation

open Separation in
/-- **The partition of unity (§5.1 step 2).** For `κ > 1` there are finitely many fixed
smooth pieces `ψ_{1,m}` supported in `[1, 2]`, with derivative bounds `M₁`, and points
`y_m ∈ [(4κ)⁻¹, 2κe²]` such that `∑_m ψ_{1,m}(z/y_m) = 1/z` for `z ∈ [κ⁻¹, κe²]`. With
`a = κ⁻¹`, take the points `y_m = a/2 + m a/4`, `m < ⌈4κe²/a⌉`, the steps
`S_m(z) = smoothTransition(4(z - y_m)/a)` and `η_m = S_m - S_{m+1}`, supported in
`[y_m, y_m + a/2] ⊆ [y_m, 2y_m]`; the sum telescopes to `S_0 - S_n = 1` on `[κ⁻¹, κe²]`. Put
`ψ_{1,m}(z) = η_m(y_m z)/(y_m z)`; the derivative bounds hold by compact support. -/
theorem exists_partition (κ : ℝ) (hκ : 1 < κ) :
    ∃ (n : ℕ) (ψ₁ : Fin n → ℝ → ℂ) (y : Fin n → ℝ) (M₁ : ℕ → ℝ),
      (∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ₁ m) ∧
        (∀ z, ψ₁ m z ≠ 0 → 1 ≤ z ∧ z ≤ 2) ∧
        ∀ (j : ℕ) (z : ℝ), ‖iteratedDeriv j (ψ₁ m) z‖ ≤ M₁ j) ∧
      (∀ m, (4 * κ)⁻¹ ≤ y m ∧ y m ≤ 2 * κ * Real.exp 2) ∧
      ∀ z : ℝ, κ⁻¹ ≤ z → z ≤ κ * Real.exp 2 → ∑ m, ψ₁ m (z / y m) = ((z⁻¹ : ℝ) : ℂ) := by
  set a := κ⁻¹ with ha_def
  set b := κ * Real.exp 2 with hb_def
  have hκ0 : 0 < κ := by linarith
  have ha : 0 < a := inv_pos.2 hκ0
  have hab : a < b := by
    have : a < 1 := inv_lt_one_of_one_lt₀ hκ
    have : 1 < b := one_lt_mul_of_lt_of_le hκ (Real.one_le_exp (by norm_num))
    linarith
  set n := ⌈4 * b / a⌉₊ with hn
  have hsm := fun m : Fin n => contDiff_partPiece ha m
  have hss := fun (m : Fin n) z (h : partPiece a m z ≠ 0) => le_of_partPiece_ne_zero ha h
  choose C hC using fun (m : Fin n) j => exists_norm_iteratedDeriv_le (hsm m) (hss m) j
  refine ⟨n, fun m => partPiece a m, fun m => partPoint a m, fun j => ∑ m, C m j,
    fun m => ⟨hsm m, hss m, fun j z => (hC m j z).trans ?_⟩, fun m => ⟨?_, ?_⟩, ?_⟩
  · refine Finset.single_le_sum (f := fun m => C m j) (fun m' _ => ?_) (Finset.mem_univ m)
    exact (norm_nonneg _).trans (hC m' j 0)
  · refine le_trans ?_ (half_le_partPoint ha m)
    rw [ha_def, mul_inv]
    have : (4 : ℝ)⁻¹ ≤ 2⁻¹ := by norm_num
    calc 4⁻¹ * κ⁻¹ ≤ 2⁻¹ * κ⁻¹ := by gcongr
      _ = κ⁻¹ / 2 := by ring
  · -- `m < 4b/a`, so `y_m < a/2 + b ≤ 2b`
    have hm : (m : ℝ) + 1 ≤ n := by exact_mod_cast m.2
    have hn' : (n : ℝ) < 4 * b / a + 1 := Nat.ceil_lt_add_one (by positivity)
    have hma : (m : ℝ) * (a / 4) < b := by
      have : (m : ℝ) < 4 * b / a := by linarith
      rw [lt_div_iff₀ ha] at this
      linarith
    show partPoint a m ≤ 2 * κ * Real.exp 2
    unfold partPoint
    have : a / 2 ≤ b := by linarith
    nlinarith
  · intro z hz₁ hz₂
    have hterm : ∀ m : Fin n, partPiece a m (z / partPoint a m) =
        ((partBump a m z * z⁻¹ : ℝ) : ℂ) := by
      intro m
      have hy0 : partPoint a m ≠ 0 := by linarith [half_le_partPoint ha m]
      rw [partPiece, mul_div_cancel₀ z hy0]
    simp only [hterm]
    rw [← Complex.ofReal_sum, ← Finset.sum_mul]
    congr 1
    have htel : ∑ m : Fin n, partBump a m z = partStep a 0 z - partStep a n z :=
      (Fin.sum_univ_eq_sum_range (fun m => partBump a m z) n).trans
        (Finset.sum_range_sub' (fun m => partStep a m z) n)
    rw [htel, partStep_eq_one ha, partStep_eq_zero ha]
    · ring
    · unfold partPoint
      have : 4 * b / a ≤ n := Nat.le_ceil _
      rw [div_le_iff₀ ha] at this
      linarith
    · unfold partPoint
      push_cast
      linarith

/-! ### The separation identity -/

namespace Separation

/-- Eventually `log κ + K T L^{0.46} ≤ L`. -/
private theorem eventually_log_add_mul_le (κ K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ x : ℝ in atTop,
      Real.log κ + K * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) ≤ Real.log x := by
  have ho := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.54)).bound
    (show (0 : ℝ) < 1 / (2 * (K + 1)) by positivity))
  filter_upwards [Real.tendsto_log_atTop.eventually ho,
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * |Real.log κ| + 1)] with x hx hL
  set L := Real.log x
  have hL1 : 1 ≤ L := by linarith [abs_nonneg (Real.log κ)]
  have hL0 : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  rw [Real.norm_of_nonneg hlogL, Real.norm_of_nonneg (by positivity)] at hx
  have hsplit : L ^ (0.54 : ℝ) * L ^ (0.46 : ℝ) = L := by
    rw [← Real.rpow_add hL0]
    norm_num
  have h46 : 0 ≤ L ^ (0.46 : ℝ) := by positivity
  have h₁ : K * Real.log L * L ^ (0.46 : ℝ) ≤ K * (1 / (2 * (K + 1))) * L := by
    calc K * Real.log L * L ^ (0.46 : ℝ)
        ≤ K * (1 / (2 * (K + 1)) * L ^ (0.54 : ℝ)) * L ^ (0.46 : ℝ) := by gcongr
      _ = K * (1 / (2 * (K + 1))) * (L ^ (0.54 : ℝ) * L ^ (0.46 : ℝ)) := by ring
      _ = K * (1 / (2 * (K + 1))) * L := by rw [hsplit]
  have h₂ : K * (1 / (2 * (K + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have h₃ : K * (1 / (2 * (K + 1))) * L ≤ 1 / 2 * L := mul_le_mul_of_nonneg_right h₂ hL0.le
  linarith [le_abs_self (Real.log κ)]

/-- **U10 for the free labels.** Eventually, for groups as in (6.1) and free slots `C` with at
most `m₀` slots in each big group and none in the small ones, `κ D_C ≤ x` for every
auxiliary label. -/
theorem eventually_mul_slotProduct_le (c₀ C₀ vlo vhi κ : ℝ) (hκ : 0 < κ) (m₀ : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (J : ℕ) (C : ι → Finset (Fin J)), (∀ g, (C g).card ≤ m₀) → (∀ g ∉ big, C g = ∅) →
        ∀ l ∈ auxLabels P C, κ * slotProduct C l ≤ x := by
  filter_upwards [eventually_log_add_mul_le κ (m₀ * |C₀|) (by positivity),
    eventually_gt_atTop 0, Real.tendsto_log_atTop.eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 0]
    with x hx hx0 hL0 hT0
  simp only [Function.comp_apply] at hT0
  intro ι _ _ P big hadm J C hC hCb l hl
  set E := Real.exp (Real.log x ^ (0.46 : ℝ)) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  -- each label in a big group is at most `E`
  have hgi : ∀ g, ∏ i ∈ C g, (l g i : ℝ) ≤ if g ∈ big then E ^ m₀ else 1 := by
    intro g
    split_ifs with hg
    · calc ∏ i ∈ C g, (l g i : ℝ) ≤ ∏ _i ∈ C g, E := by
            refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i hi => ?_
            have h := Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hl g) i
            simp only [hi, ↓reduceIte] at h
            exact (mem_primesIcc.1 (hadm.2.2.2.2.2.2.2.1 g hg h)).2.2
        _ = E ^ (C g).card := Finset.prod_const _
        _ ≤ E ^ m₀ := pow_le_pow_right₀ hE1 (hC g)
    · rw [hCb g hg, Finset.prod_empty]
  have hprod : (slotProduct C l : ℝ) ≤ (E ^ m₀) ^ big.card := by
    unfold slotProduct
    push_cast
    calc ∏ g, ∏ i ∈ C g, (l g i : ℝ) ≤ ∏ g, if g ∈ big then E ^ m₀ else 1 :=
          Finset.prod_le_prod₀ (fun g _ => Finset.prod_nonneg fun i _ => by positivity)
            fun g _ => hgi g
      _ = (E ^ m₀) ^ big.card := by
          rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  -- `E^{m₀ |big|} ≤ exp(m₀ |C₀| T L^{0.46}) ≤ x/κ`
  have hT : (big.card : ℝ) ≤ |C₀| * Real.log (Real.log x) := by
    have h := hadm.2.2.2.2.1
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C₀) hT0)
  have hpow : (E ^ m₀) ^ big.card ≤ Real.exp (m₀ * |C₀| * Real.log (Real.log x) *
      Real.log x ^ (0.46 : ℝ)) := by
    rw [← pow_mul, hE, ← Real.exp_nat_mul, Real.exp_le_exp]
    push_cast
    have : 0 ≤ Real.log x ^ (0.46 : ℝ) := by positivity
    calc ((m₀ : ℝ) * big.card) * Real.log x ^ (0.46 : ℝ)
        ≤ ((m₀ : ℝ) * (|C₀| * Real.log (Real.log x))) * Real.log x ^ (0.46 : ℝ) := by gcongr
      _ = _ := by ring
  have hxκ : Real.exp (m₀ * |C₀| * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ)) ≤ x / κ := by
    rw [le_div_iff₀ hκ, ← Real.exp_log hκ, ← Real.exp_add, ← Real.exp_log hx0]
    rw [Real.exp_log hx0]
    calc Real.exp (_ + Real.log κ) ≤ Real.exp (Real.log x) := Real.exp_le_exp.2 (by linarith)
      _ = x := Real.exp_log hx0
  have := hprod.trans (hpow.trans hxκ)
  rw [le_div_iff₀ hκ] at this
  linarith

/-- `(w/(x D_A D_B))^s = x^{-s} D_A^{-s} D_B^{-s} w^s` for positive `x, D_A, D_B, w`. -/
private theorem cpow_div_mul_mul {x : ℝ} (hx : 0 < x) {DA DB w : ℕ} (hA : 0 < DA) (hB : 0 < DB)
    (hw : 0 < w) (s : ℂ) :
    ((((w : ℝ) / (x * ((DA * DB : ℕ) : ℝ)) : ℝ)) : ℂ) ^ s =
      (x : ℂ) ^ (-s) * (DA : ℂ) ^ (-s) * (DB : ℂ) ^ (-s) * (w : ℂ) ^ s := by
  have hA' : (0 : ℝ) < DA := by exact_mod_cast hA
  have hB' : (0 : ℝ) < DB := by exact_mod_cast hB
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hz : (0 : ℝ) < (w : ℝ) / (x * ((DA * DB : ℕ) : ℝ)) := by push_cast; positivity
  rw [← Complex.ofReal_natCast DA, ← Complex.ofReal_natCast DB, ← Complex.ofReal_natCast w,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hz.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hA'.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hB'.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hw'.ne'),
    ← Complex.ofReal_log hz.le, ← Complex.ofReal_log hx.le, ← Complex.ofReal_log hA'.le,
    ← Complex.ofReal_log hB'.le, ← Complex.ofReal_log hw'.le, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  rw [Real.log_div hw'.ne' (by positivity), Real.log_mul hx.ne' (by positivity),
    Real.log_mul hA'.ne' hB'.ne']
  push_cast
  ring

end Separation

/-- **The separation (§5.1 steps 1 and 3).** For a partition as in
`exists_partition`, eventually, for groups as in (6.1), all data, every comparison pattern
and every `Ψ` supported in `[κ⁻¹, κ]` with a Mellin density `a`,
`strippedComparison = ∫ a(ξ) x^{-iσ} ∑_m y_m Y_m⁻¹ 𝔅_m(σ) dξ` (form (6.18)) with `σ = 2πξ`
and `Y_m = y_m x U U'`. On the support, `D_C ∈ [UU', e²UU']` (the cells of `φ, φ'`), so
`w/Y₀ ∈ [κ⁻¹, κe²]` and `Y₀⁻¹ ∑_m ψ_{1,m}(w/Y_m) = 1/w`; every `w ≤ κ x D_C ≤ x²` (U10); and
`(w/(x D_C))^{iσ} = x^{-iσ} w^{iσ} D_A^{-iσ} D_B^{-iσ}`. -/
theorem eventually_strippedComparison_eq (q q₀ c₀ C₀ vlo vhi κ : ℝ) (hκ : 1 < κ) (m₀ : ℕ)
    {n : ℕ} {ψ₁ : Fin n → ℝ → ℂ} {y : Fin n → ℝ} (hψ₁ : ∀ m z, ψ₁ m z ≠ 0 → 1 ≤ z ∧ z ≤ 2)
    (hy : ∀ m, (4 * κ)⁻¹ ≤ y m ∧ y m ≤ 2 * κ * Real.exp 2)
    (hsum : ∀ z : ℝ, κ⁻¹ ≤ z → z ≤ κ * Real.exp 2 → ∑ m, ψ₁ m (z / y m) = ((z⁻¹ : ℝ) : ℂ)) :
    ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ {r d : ℕ} (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ)
          (G : ℕ → ℝ) (Ψ : ℝ → ℝ),
        ∀ (J : ℕ) (A B : ι → Finset (Fin J)) (φ φ' ψ ψ' : ℕ → ℂ) (U U' : ℝ),
          ComparisonPattern m₀ big A B φ φ' ψ ψ' U U' →
        ∀ α : ℝ → ℂ, Integrable α → (∀ z, Ψ z ≠ 0 → κ⁻¹ ≤ z ∧ z ≤ κ) →
          (∀ z : ℝ, 0 < z →
            (Ψ z : ℂ) = ∫ ξ, α ξ * (z : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) →
          strippedComparison x q₀ P A B φ φ' ψ ψ' (centeredCore x q a u v Bc) G Ψ =
            ∫ ξ, α ξ * ((x : ℂ) ^ (-(((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) *
              ∑ m, (y m : ℂ) * ((((y m * (x * U * U')) : ℝ) : ℂ)⁻¹ *
                comparisonBilinear x q q₀ a u v Bc P A B φ φ' ψ ψ' G (ψ₁ m)
                  (y m * (x * U * U')) (2 * Real.pi * ξ))) := by
  have hκ0 : 0 < κ := by linarith
  filter_upwards [eventually_gt_atTop 0,
    Separation.eventually_mul_slotProduct_le c₀ C₀ vlo vhi κ hκ0 m₀] with x hx hU10
  intro ι _ _ P big hadm r d a u v Bc G Ψ J A B φ φ' ψ ψ' U U' hpat α hα hΨ hrep
  have hψ0 : ∀ m, ψ₁ m 0 = 0 := fun m => by
    by_contra h
    linarith [(hψ₁ m 0 h).1]
  have hy0 : ∀ m, 0 < y m := fun m => lt_of_lt_of_le (by positivity) (hy m).1
  have hDAB := slotProduct_union (fun g => (hpat.1 g).1)
  have hDle : ∀ l ∈ auxLabels P (fun g => A g ∪ B g),
      κ * slotProduct (fun g => A g ∪ B g) l ≤ x := fun l hl =>
    hU10 P big hadm J (fun g => A g ∪ B g) (fun g => (hpat.1 g).2)
      (fun g hg => by rw [(hpat.2.1 g hg).1, (hpat.2.1 g hg).2, Finset.empty_union]) l hl
  -- names for the pieces
  obtain ⟨z, hz⟩ : ∃ z : (ι → Fin J → ℕ) → ℕ → ℝ,
      z = fun l (w : ℕ) => (w : ℝ) / (x * slotProduct (fun g => A g ∪ B g) l) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : (ι → Fin J → ℕ) → ℕ → ℂ, R = fun l w =>
      ((∏ g, ∏ i ∈ A g ∪ B g, (harmonicMass (P g) * l g i)⁻¹ : ℝ) : ℂ) *
        φ (slotProduct A l) * φ' (slotProduct B l) * (centeredCore x q a u v Bc w : ℂ) *
        markedListWeight P q₀ (unsharedSlots fun g => A g ∪ B g)
          (fun p => ψ' (slotProduct B fun g i => p g i.castSucc)) w *
        ((G (w + slotProduct (fun g => A g ∪ B g) l) : ℂ) *
          markedListWeight P q₀ (unsharedSlots fun g => A g ∪ B g)
            (fun p => ψ (slotProduct A fun g i => p g i.castSucc))
            (w + slotProduct (fun g => A g ∪ B g) l)) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : Fin n → (ι → Fin J → ℕ) → ℕ → ℂ, K = fun m l (w : ℕ) =>
      (y m : ℂ) * ((((y m * (x * U * U')) : ℝ) : ℂ))⁻¹ * ψ₁ m (w / (y m * (x * U * U'))) *
        R l w := ⟨_, rfl⟩
  have hK0 : ∀ m l, K m l 0 = 0 := fun m l => by simp [hK, hψ0]
  -- step 1: the integrand is a finite combination of `a(ξ) z^{iσ}`
  have hexp : ∀ ξ : ℝ,
      α ξ * ((x : ℂ) ^ (-(((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) *
        ∑ m, (y m : ℂ) * ((((y m * (x * U * U')) : ℝ) : ℂ)⁻¹ *
          comparisonBilinear x q q₀ a u v Bc P A B φ φ' ψ ψ' G (ψ₁ m)
            (y m * (x * U * U')) (2 * Real.pi * ξ))) =
      ∑ m, ∑ l ∈ auxLabels P (fun g => A g ∪ B g),
        ∑ w ∈ Finset.Icc ⌈y m * (x * U * U')⌉₊ ⌊2 * (y m * (x * U * U'))⌋₊,
          K m l w * (α ξ * ((z l w : ℝ) : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) := by
    intro ξ
    simp only [comparisonBilinear, endpointCoeff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l hl =>
      Finset.sum_congr rfl fun w _ => ?_
    rcases Nat.eq_zero_or_pos w with hw | hw
    · subst hw
      rw [hK0]
      simp [hψ0]
    · rw [hz, hK, hR]
      dsimp only
      rw [hDAB l, Separation.cpow_div_mul_mul hx (slotProduct_pos hadm hl A)
        (slotProduct_pos hadm hl B) hw]
      ring
  -- step 2: integrate term by term
  have hzpos : ∀ l ∈ auxLabels P (fun g => A g ∪ B g), ∀ w : ℕ, 0 < w → 0 < z l w := by
    intro l hl w hw
    rw [hz]
    have := slotProduct_pos hadm hl (fun g => A g ∪ B g)
    positivity
  have hint : ∀ m, ∀ l ∈ auxLabels P (fun g => A g ∪ B g), ∀ w : ℕ,
      Integrable fun ξ : ℝ => K m l w *
        (α ξ * ((z l w : ℝ) : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) := by
    intro m l hl w
    rcases Nat.eq_zero_or_pos w with hw | hw
    · subst hw
      simp only [hK0, zero_mul]
      exact integrable_zero _ _ _
    · exact (integrable_mul_cpow hα (hzpos l hl w hw)).const_mul _
  have heval : ∫ ξ, (∑ m, ∑ l ∈ auxLabels P (fun g => A g ∪ B g),
        ∑ w ∈ Finset.Icc ⌈y m * (x * U * U')⌉₊ ⌊2 * (y m * (x * U * U'))⌋₊,
          K m l w * (α ξ * ((z l w : ℝ) : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I))) =
      ∑ m, ∑ l ∈ auxLabels P (fun g => A g ∪ B g),
        ∑ w ∈ Finset.Icc ⌈y m * (x * U * U')⌉₊ ⌊2 * (y m * (x * U * U'))⌋₊,
          K m l w * (Ψ (z l w) : ℂ) := by
    rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun l hl =>
      integrable_finsetSum _ fun w _ => hint m l hl w]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_finsetSum _ fun l hl => integrable_finsetSum _ fun w _ => hint m l hl w]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [integral_finsetSum _ fun w _ => hint m l hl w]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_const_mul]
    rcases Nat.eq_zero_or_pos w with hw | hw
    · subst hw
      simp [hK0]
    · rw [hrep _ (hzpos l hl w hw)]
  -- step 3: the pieces vanish off `[Y_m, 2Y_m]` and `Ψ` off `[κ⁻¹ x D_C, κ x D_C]`
  have hrange : ∀ m, ∀ l ∈ auxLabels P (fun g => A g ∪ B g),
      ∑ w ∈ Finset.Icc ⌈y m * (x * U * U')⌉₊ ⌊2 * (y m * (x * U * U'))⌋₊,
          K m l w * (Ψ (z l w) : ℂ) =
        ∑ w ∈ Finset.Icc 1 ⌊x ^ 2⌋₊, K m l w * (Ψ (z l w) : ℂ) := by
    intro m l hl
    have hsupp : ∀ w : ℕ, K m l w * (Ψ (z l w) : ℂ) ≠ 0 →
        w ∈ Finset.Icc ⌈y m * (x * U * U')⌉₊ ⌊2 * (y m * (x * U * U'))⌋₊ ∧
          w ∈ Finset.Icc 1 ⌊x ^ 2⌋₊ := by
      intro w hw
      have hψ : ψ₁ m (w / (y m * (x * U * U'))) ≠ 0 := by
        intro h
        apply hw
        rw [hK]
        simp [h]
      have hΨw : Ψ (z l w) ≠ 0 := by
        intro h
        apply hw
        simp [h]
      obtain ⟨h1, h2⟩ := hψ₁ m _ hψ
      have hY : 0 < y m * (x * U * U') := by
        by_contra hY
        have : (w : ℝ) / (y m * (x * U * U')) ≤ 0 :=
          div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (not_lt.1 hY)
        linarith
      rw [le_div_iff₀ hY, one_mul] at h1
      rw [div_le_iff₀ hY] at h2
      have hD' : (0 : ℝ) < slotProduct (fun g => A g ∪ B g) l := by
        exact_mod_cast slotProduct_pos hadm hl (fun g => A g ∪ B g)
      have hzκ := (hΨ _ hΨw).2
      rw [hz] at hzκ
      dsimp only at hzκ
      rw [div_le_iff₀ (by positivity)] at hzκ
      have hκD := hDle l hl
      have hκD' : κ * (slotProduct (fun g => A g ∪ B g) l : ℝ) ≤ x := by exact_mod_cast hκD
      refine ⟨Finset.mem_Icc.2 ⟨Nat.ceil_le.2 h1, Nat.le_floor (by linarith)⟩,
        Finset.mem_Icc.2 ⟨?_, Nat.le_floor ?_⟩⟩
      · have : (0 : ℝ) < w := by linarith
        have : 0 < w := by exact_mod_cast this
        omega
      · calc (w : ℝ) ≤ κ * (x * slotProduct (fun g => A g ∪ B g) l) := hzκ
          _ = x * (κ * slotProduct (fun g => A g ∪ B g) l) := by ring
          _ ≤ x * x := by gcongr
          _ = x ^ 2 := by ring
    rw [← Finset.sum_subset Finset.inter_subset_left fun w _ hwn => by
      by_contra h
      exact hwn (Finset.mem_inter.2 (hsupp w h))]
    exact Finset.sum_subset Finset.inter_subset_right fun w _ hwn => by
      by_contra h
      exact hwn (Finset.mem_inter.2 (hsupp w h))
  -- step 4: `∑_m y_m Y_m⁻¹ ψ_{1,m}(w/Y_m) = 1/w` where `Ψ(w/(x D_C)) ≠ 0`
  have hpt : ∀ l ∈ auxLabels P (fun g => A g ∪ B g), ∀ w ∈ Finset.Icc 1 ⌊x ^ 2⌋₊,
      ∑ m, K m l w * (Ψ (z l w) : ℂ) =
        ((∏ g, ∏ i ∈ A g ∪ B g, (harmonicMass (P g) * l g i)⁻¹ : ℝ) : ℂ) *
          φ (slotProduct A l) * φ' (slotProduct B l) *
          (((Ψ (w / (x * slotProduct (fun g => A g ∪ B g) l)) / w *
              centeredCore x q a u v Bc w * G (w + slotProduct (fun g => A g ∪ B g) l) : ℝ) :
              ℂ) *
            markedListWeight P q₀ (unsharedSlots fun g => A g ∪ B g)
              (fun p => ψ' (slotProduct B fun g i => p g i.castSucc)) w *
            markedListWeight P q₀ (unsharedSlots fun g => A g ∪ B g)
              (fun p => ψ (slotProduct A fun g i => p g i.castSucc))
              (w + slotProduct (fun g => A g ∪ B g) l)) := by
    intro l hl w hw
    have hw1 : 1 ≤ w := (Finset.mem_Icc.1 hw).1
    have hfac : ∀ m, K m l w * (Ψ (z l w) : ℂ) =
        ((y m : ℂ) * (((y m * (x * U * U')) : ℝ) : ℂ)⁻¹ * ψ₁ m (w / (y m * (x * U * U')))) *
          (R l w * Ψ (z l w)) := fun m => by
      rw [hK]
      ring
    rw [Finset.sum_congr rfl fun m _ => hfac m, ← Finset.sum_mul]
    by_cases hΨz : Ψ (z l w) = 0
    · rw [hz] at hΨz
      dsimp only at hΨz
      simp [hΨz, hz]
    by_cases hφ : φ (slotProduct A l) = 0
    · rw [hR]
      simp [hφ]
    by_cases hφ' : φ' (slotProduct B l) = 0
    · rw [hR]
      simp [hφ']
    -- the cells of `φ, φ'`
    obtain ⟨hA1, hA2⟩ := hpat.2.2.2.2.1 _ hφ
    obtain ⟨hB1, hB2⟩ := hpat.2.2.2.2.2 _ hφ'
    have hDA : (1 : ℝ) ≤ slotProduct A l := by
      exact_mod_cast slotProduct_pos hadm hl A
    have hDB : (1 : ℝ) ≤ slotProduct B l := by
      exact_mod_cast slotProduct_pos hadm hl B
    have he := Real.exp_pos 1
    have hU0 : 0 < U := by
      by_contra h
      nlinarith
    have hU0' : 0 < U' := by
      by_contra h
      nlinarith
    have hY₀ : 0 < x * U * U' := by positivity
    obtain ⟨hz1, hz2⟩ := hΨ _ hΨz
    rw [hz] at hz1 hz2
    dsimp only at hz1 hz2
    have hD : ((slotProduct (fun g => A g ∪ B g) l : ℕ) : ℝ) =
        (slotProduct A l : ℝ) * slotProduct B l := by
      rw [hDAB l]
      push_cast
      ring
    have hD0 : 0 < x * (slotProduct (fun g => A g ∪ B g) l : ℝ) := by
      rw [hD]
      positivity
    rw [le_div_iff₀ hD0] at hz1
    rw [div_le_iff₀ hD0] at hz2
    have hw1' : κ⁻¹ ≤ (w : ℝ) / (x * U * U') := by
      rw [le_div_iff₀ hY₀]
      calc κ⁻¹ * (x * U * U') = κ⁻¹ * x * (U * U') := by ring
        _ ≤ κ⁻¹ * x * ((slotProduct A l : ℝ) * slotProduct B l) := by
            gcongr
        _ = κ⁻¹ * (x * slotProduct (fun g => A g ∪ B g) l) := by rw [hD]; ring
        _ ≤ w := hz1
    have hw2' : (w : ℝ) / (x * U * U') ≤ κ * Real.exp 2 := by
      rw [div_le_iff₀ hY₀]
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      calc (w : ℝ) ≤ κ * (x * slotProduct (fun g => A g ∪ B g) l) := hz2
        _ = κ * x * ((slotProduct A l : ℝ) * slotProduct B l) := by rw [hD]; ring
        _ ≤ κ * x * ((Real.exp 1 * U) * (Real.exp 1 * U')) := by
            gcongr
        _ = κ * Real.exp 2 * (x * U * U') := by rw [he2]; ring
    have hS : ∑ m, (y m : ℂ) * (((y m * (x * U * U')) : ℝ) : ℂ)⁻¹ *
        ψ₁ m (w / (y m * (x * U * U'))) = (w : ℂ)⁻¹ := by
      have hm : ∀ m, (y m : ℂ) * (((y m * (x * U * U')) : ℝ) : ℂ)⁻¹ *
          ψ₁ m (w / (y m * (x * U * U'))) =
            (((x * U * U') : ℝ) : ℂ)⁻¹ * ψ₁ m (w / (x * U * U') / y m) := by
        intro m
        rw [show (w : ℝ) / (y m * (x * U * U')) = w / (x * U * U') / y m by
          rw [div_div, mul_comm (x * U * U')]]
        have h1 : (y m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hy0 m).ne'
        rw [Complex.ofReal_mul, mul_inv]
        field_simp
      rw [Finset.sum_congr rfl fun m _ => hm m, ← Finset.mul_sum, hsum _ hw1' hw2']
      have h1 : (((x * U * U') : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hY₀.ne'
      have h2 : (w : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      rw [Complex.ofReal_inv, Complex.ofReal_div, Complex.ofReal_natCast]
      field_simp
    rw [hS, hR, hz]
    dsimp only
    push_cast
    ring
  -- assembly
  symm
  calc _ = ∑ m, ∑ l ∈ auxLabels P (fun g => A g ∪ B g),
        ∑ w ∈ Finset.Icc ⌈y m * (x * U * U')⌉₊ ⌊2 * (y m * (x * U * U'))⌋₊,
          K m l w * (Ψ (z l w) : ℂ) := by
        simp only [hexp]
        exact heval
    _ = ∑ m, ∑ l ∈ auxLabels P (fun g => A g ∪ B g),
        ∑ w ∈ Finset.Icc 1 ⌊x ^ 2⌋₊, K m l w * (Ψ (z l w) : ℂ) :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l hl => hrange m l hl
    _ = ∑ l ∈ auxLabels P (fun g => A g ∪ B g),
        ∑ w ∈ Finset.Icc 1 ⌊x ^ 2⌋₊, ∑ m, K m l w * (Ψ (z l w) : ℂ) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = _ := by
        unfold strippedComparison
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w hw => hpt l hl w hw

/-! ### The endpoint energies -/

/-- **The endpoint energies (6.19), pointwise.** For `m₀` and a bound `M₀` of the pieces there
is `C₅` such that, eventually, for groups as in (6.1), all admissible data, every comparison
pattern, every piece `|ψ₁| ≤ M₀` supported in `[1, 2]`, every `y₀ ∈ [(4κ)⁻¹, 2κe²]` and every
`σ`, `|Y⁻¹ 𝔅| ≤ L^{C₅}` with `Y = y₀ x U U'`. The auxiliary labels have mass `1`,
`|b₁|, |b₂| ≤ 1`, `|𝒰| ≤ M₀ L^{1 + C_W}` and `|𝒱| ≤ L^{B₀ + C_W}` (crude U7, U9), and
`#[Y, 2Y] ≤ 2Y` for `Y ≥ 1`; if no label has `φ(D_A) φ'(D_B) ≠ 0`, then `𝔅 = 0`, and
otherwise `x/(4κe²) ≤ Y` and `2Y ≤ 4κe² x D_C ≤ x²` (U10). -/
theorem exists_norm_comparisonBilinear_le (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ)
    (CN c : ℝ) (d : ℕ) (B₀ κ : ℝ) (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1)
    (hvlo : 0 < vlo) (halo : 1 / 10 < alo) (hc : 0 < c) (hκ : 1 < κ) (m₀ : ℕ) (M₀ : ℝ) :
    ∃ C₅ : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ)
          (G : ℕ → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v →
          (∀ Q, |Bc Q| ≤ 1) → CoreAdmissible B₀ x P G →
        ∀ (J : ℕ) (A B : ι → Finset (Fin J)) (φ φ' ψ ψ' : ℕ → ℂ) (U U' : ℝ),
          ComparisonPattern m₀ big A B φ φ' ψ ψ' U U' →
        ∀ (ψ₁ : ℝ → ℂ) (y₀ σ : ℝ), (∀ z, ψ₁ z ≠ 0 → 1 ≤ z ∧ z ≤ 2) → (∀ z, ‖ψ₁ z‖ ≤ M₀) →
          (4 * κ)⁻¹ ≤ y₀ → y₀ ≤ 2 * κ * Real.exp 2 →
          ‖(((y₀ * (x * U * U')) : ℝ) : ℂ)⁻¹ *
              comparisonBilinear x q q₀ a u v Bc P A B φ φ' ψ ψ' G ψ₁ (y₀ * (x * U * U')) σ‖ ≤
            Real.log x ^ C₅ := by
  obtain ⟨CW, hW⟩ := exists_norm_markedListWeight_le_rpow q₀ c₀ C₀ vlo vhi hq₀ hq₀₁ hvlo m₀
  have hκ0 : 0 < κ := by linarith
  refine ⟨2 + 2 * |CW| + |B₀|, ?_⟩
  filter_upwards [hW,
    eventually_abs_centeredCore_le_log q alo ahi K₀ CN c d hq hq₁ halo hc,
    Separation.eventually_mul_slotProduct_le c₀ C₀ vlo vhi (4 * κ * Real.exp 2) (by positivity)
      m₀, eventually_ge_atTop (4 * κ * Real.exp 2),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * |M₀| + 1)] with x hWx hFx hU10 hx4 hL
  intro ι _ _ P big hadm r a u v Bc G hin hsl hBc hco J A B φ φ' ψ ψ' U U' hpat ψ₁ y₀ σ hψs hψb
    hy₁ hy₂
  set L := Real.log x with hLdef
  have hL1 : 1 ≤ L := by linarith [abs_nonneg M₀]
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx4
  have hDAB := slotProduct_union (fun g => (hpat.1 g).1)
  have hV : ∀ g, 0 < harmonicMass (P g) := fun g => lt_of_lt_of_le hvlo (hadm.2.2.2.2.2.1 g).1
  -- if no label meets the cells of `φ, φ'`, then `𝔅 = 0`
  by_cases hex : ∃ l ∈ auxLabels P (fun g => A g ∪ B g),
    φ (slotProduct A l) ≠ 0 ∧ φ' (slotProduct B l) ≠ 0
  swap
  · push Not at hex
    have h0 : comparisonBilinear x q q₀ a u v Bc P A B φ φ' ψ ψ' G ψ₁ (y₀ * (x * U * U')) σ =
        0 := by
      unfold comparisonBilinear
      refine Finset.sum_eq_zero fun l hl => ?_
      by_cases h : φ (slotProduct A l) = 0
      · simp [h]
      · simp [hex l hl h]
    rw [h0, mul_zero, norm_zero]
    positivity
  obtain ⟨l₀, hl₀, hφ, hφ'⟩ := hex
  -- the scale: `1 ≤ Y` and `2Y ≤ x²`
  obtain ⟨hA1, hA2⟩ := hpat.2.2.2.2.1 _ hφ
  obtain ⟨hB1, hB2⟩ := hpat.2.2.2.2.2 _ hφ'
  have hDA : (1 : ℝ) ≤ slotProduct A l₀ := by
    exact_mod_cast slotProduct_pos hadm hl₀ A
  have hDB : (1 : ℝ) ≤ slotProduct B l₀ := by
    exact_mod_cast slotProduct_pos hadm hl₀ B
  have he := Real.exp_pos 1
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have hU0 : 0 < U := by
    by_contra h
    nlinarith
  have hU0' : 0 < U' := by
    by_contra h
    nlinarith
  set Y := y₀ * (x * U * U') with hYdef
  have hY1 : 1 ≤ Y := by
    have h₁ : 1 ≤ x / (4 * κ * Real.exp 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have h₂ : 1 ≤ (Real.exp 1 * U) * (Real.exp 1 * U') :=
      one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    calc (1 : ℝ) ≤ x / (4 * κ * Real.exp 2) * ((Real.exp 1 * U) * (Real.exp 1 * U')) :=
          one_le_mul_of_one_le_of_one_le h₁ h₂
      _ = (4 * κ)⁻¹ * (x * U * U') := by
          rw [he2]
          field_simp
      _ ≤ Y := by
          rw [hYdef]
          gcongr
  have hY0 : 0 < Y := by linarith
  have hY2 : 2 * Y ≤ x ^ 2 := by
    have hD := hU10 P big hadm J (fun g => A g ∪ B g) (fun g => (hpat.1 g).2)
      (fun g hg => by rw [(hpat.2.1 g hg).1, (hpat.2.1 g hg).2, Finset.empty_union]) l₀ hl₀
    have hD' : 4 * κ * Real.exp 2 * ((slotProduct A l₀ : ℝ) * slotProduct B l₀) ≤ x := by
      have : ((slotProduct (fun g => A g ∪ B g) l₀ : ℕ) : ℝ) =
          (slotProduct A l₀ : ℝ) * slotProduct B l₀ := by
        rw [hDAB l₀]
        push_cast
        ring
      rw [← this]
      exact_mod_cast hD
    calc 2 * Y = 2 * y₀ * x * (U * U') := by rw [hYdef]; ring
      _ ≤ 2 * (2 * κ * Real.exp 2) * x * ((slotProduct A l₀ : ℝ) * slotProduct B l₀) := by
          gcongr
      _ = x * (4 * κ * Real.exp 2 * ((slotProduct A l₀ : ℝ) * slotProduct B l₀)) := by ring
      _ ≤ x * x := by gcongr
      _ = x ^ 2 := by ring
  -- pointwise bounds on the endpoints (U7, U9)
  have hcard : ∀ g, (unsharedSlots (fun g => A g ∪ B g) g).card ≤ m₀ + 1 := by
    intro g
    refine (Finset.card_insert_le _ _).trans ?_
    rw [Finset.card_map]
    exact Nat.succ_le_succ (hpat.1 g).2
  have hb₁ : ∀ p : ι → Fin (J + 1) → ℕ, ‖ψ' (slotProduct B fun g i => p g i.castSucc)‖ ≤ 1 :=
    fun p => (hpat.2.2.2.1 _).2.2.2
  have hb₂ : ∀ p : ι → Fin (J + 1) → ℕ, ‖ψ (slotProduct A fun g i => p g i.castSucc)‖ ≤ 1 :=
    fun p => (hpat.2.2.2.1 _).2.2.1
  have hcpow : ∀ (n : ℕ) (t : ℝ), 0 < n → ‖(n : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := by
    intro n t hn
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
    simp
  have hcpow' : ∀ (n : ℕ) (t : ℝ), 0 < n → ‖(n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ = 1 := by
    intro n t hn
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
    simp
  set Bw : ℝ := |M₀| * L * L ^ CW * (L ^ B₀ * L ^ CW) with hBw
  have hBw0 : 0 ≤ Bw := by positivity
  have hterm : ∀ l ∈ auxLabels P (fun g => A g ∪ B g),
      ∀ w ∈ Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊,
        ‖endpointCoeff x q q₀ a u v Bc P (fun g => A g ∪ B g)
            (fun p => ψ' (slotProduct B fun g i => p g i.castSucc)) ψ₁ Y σ w *
          ((G (w + slotProduct (fun g => A g ∪ B g) l) : ℂ) *
            markedListWeight P q₀ (unsharedSlots fun g => A g ∪ B g)
              (fun p => ψ (slotProduct A fun g i => p g i.castSucc))
              (w + slotProduct (fun g => A g ∪ B g) l))‖ ≤ Bw := by
    intro l hl w hw
    obtain ⟨hw1, hw2⟩ := Finset.mem_Icc.1 hw
    have hYw : Y ≤ w := Nat.ceil_le.1 hw1
    have hw0 : 0 < w := by
      have : (0 : ℝ) < w := by linarith
      exact_mod_cast this
    have hwx : (w : ℝ) ≤ x ^ 2 := le_trans (Nat.le_floor_iff (by linarith) |>.1 hw2) hY2
    unfold endpointCoeff
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hcpow w σ hw0, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hco.2 _).1]
    have hx1 : 1 ≤ x :=
      (one_le_mul_of_one_le_of_one_le (by linarith) (Real.one_le_exp (by norm_num))).trans hx4
    have h₁ := hFx r a u v Bc hin hsl hBc w hw0 (hwx.trans (pow_le_pow_right₀ hx1 (by norm_num)))
    have h₂ := hWx P big hadm (J + 1) _ _ hcard hb₁ w
    have h₃ := hWx P big hadm (J + 1) _ _ hcard hb₂ (w + slotProduct (fun g => A g ∪ B g) l)
    have h₄ := (hco.2 (w + slotProduct (fun g => A g ∪ B g) l)).2
    have h₅ : ‖ψ₁ (w / Y)‖ ≤ |M₀| := (hψb _).trans (le_abs_self _)
    rw [mul_one, hBw]
    gcongr
    exact mul_nonneg (hco.2 _).1 (norm_nonneg _)
  have hlabel : ∀ l ∈ auxLabels P (fun g => A g ∪ B g),
      ‖((∏ g, ∏ i ∈ A g ∪ B g, (harmonicMass (P g) * l g i)⁻¹ : ℝ) : ℂ) *
        (φ (slotProduct A l) * (slotProduct A l : ℂ) ^ (-((σ : ℂ) * Complex.I))) *
        (φ' (slotProduct B l) * (slotProduct B l : ℂ) ^ (-((σ : ℂ) * Complex.I))) *
        ∑ w ∈ Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊,
          endpointCoeff x q q₀ a u v Bc P (fun g => A g ∪ B g)
              (fun p => ψ' (slotProduct B fun g i => p g i.castSucc)) ψ₁ Y σ w *
            ((G (w + slotProduct (fun g => A g ∪ B g) l) : ℂ) *
              markedListWeight P q₀ (unsharedSlots fun g => A g ∪ B g)
                (fun p => ψ (slotProduct A fun g i => p g i.castSucc))
                (w + slotProduct (fun g => A g ∪ B g) l))‖ ≤
        (∏ g, ∏ i ∈ A g ∪ B g, (harmonicMass (P g) * l g i)⁻¹) *
          ((Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊).card * Bw) := by
    intro l hl
    have hmass : 0 ≤ ∏ g, ∏ i ∈ A g ∪ B g, (harmonicMass (P g) * (l g i : ℝ))⁻¹ :=
      Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ =>
        inv_nonneg.2 (mul_nonneg (hV g).le (Nat.cast_nonneg _))
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hmass, hcpow' _ σ (slotProduct_pos hadm hl A),
      hcpow' _ σ (slotProduct_pos hadm hl B), mul_one, mul_one]
    have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum (hterm l hl))
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have h₁ := (hpat.2.2.2.1 (slotProduct A l)).1
    have h₂ := (hpat.2.2.2.1 (slotProduct B l)).2.1
    calc _ ≤ (∏ g, ∏ i ∈ A g ∪ B g, (harmonicMass (P g) * (l g i : ℝ))⁻¹) * 1 * 1 *
          ((Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊).card * Bw) := by gcongr
      _ = _ := by ring
  -- the sum over labels, of total mass `1`
  have hB : ‖comparisonBilinear x q q₀ a u v Bc P A B φ φ' ψ ψ' G ψ₁ Y σ‖ ≤
      (Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊).card * Bw := by
    unfold comparisonBilinear
    refine ((norm_sum_le _ _).trans (Finset.sum_le_sum hlabel)).trans_eq ?_
    have hμ : ∑ l ∈ auxLabels P (fun g => A g ∪ B g),
        ∏ g, ∏ i ∈ A g ∪ B g, (harmonicMass (P g) * l g i)⁻¹ = 1 :=
      sum_labelMass (fun g => (hV g).ne') _
    rw [← Finset.sum_mul, hμ, one_mul]
  -- `#[Y, 2Y] ≤ Y + 1 ≤ 2Y`
  have hcardI : ((Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊).card : ℝ) ≤ 2 * Y := by
    rw [Nat.card_Icc]
    have hf : (⌊2 * Y⌋₊ : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
    have hc : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
    rcases le_total ⌈Y⌉₊ (⌊2 * Y⌋₊ + 1) with h | h
    · rw [Nat.cast_sub h]
      push_cast
      linarith
    · rw [Nat.sub_eq_zero_of_le h]
      push_cast
      linarith
  -- `2 Bw ≤ L^{C₅}`
  have hBw : 2 * Bw ≤ L ^ (2 + 2 * |CW| + |B₀|) := by
    have e : L * (L * L ^ |CW| * (L ^ |B₀| * L ^ |CW|)) = L ^ (2 + 2 * |CW| + |B₀|) := by
      rw [show L * (L * L ^ |CW| * (L ^ |B₀| * L ^ |CW|)) =
          L ^ (1 : ℝ) * (L ^ (1 : ℝ) * L ^ |CW| * (L ^ |B₀| * L ^ |CW|)) by rw [Real.rpow_one]]
      simp only [← Real.rpow_add hL0]
      congr 1
      ring
    rw [← e, hBw]
    have hCW : L ^ CW ≤ L ^ |CW| := Real.rpow_le_rpow_of_exponent_le hL1 (le_abs_self _)
    have hB₀ : L ^ B₀ ≤ L ^ |B₀| := Real.rpow_le_rpow_of_exponent_le hL1 (le_abs_self _)
    calc 2 * (|M₀| * L * L ^ CW * (L ^ B₀ * L ^ CW))
        = (2 * |M₀|) * (L * L ^ CW * (L ^ B₀ * L ^ CW)) := by ring
      _ ≤ L * (L * L ^ |CW| * (L ^ |B₀| * L ^ |CW|)) := by
          gcongr
          linarith
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hY0.le]
  calc Y⁻¹ * ‖comparisonBilinear x q q₀ a u v Bc P A B φ φ' ψ ψ' G ψ₁ Y σ‖
      ≤ Y⁻¹ * (2 * Y * Bw) := by
        gcongr
        exact hB.trans (mul_le_mul_of_nonneg_right hcardI hBw0)
    _ = 2 * Bw := by field_simp
    _ ≤ _ := hBw

end Erdos408.TwoSided
