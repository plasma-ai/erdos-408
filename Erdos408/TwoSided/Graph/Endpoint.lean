import Erdos408.TwoSided.Graph.BoundsLists

/-!
# The physical endpoints at a dyad

S1 of `blueprint/two_sided_correlation.md` §4.1 (PD §6.2, (6.12)). For a dyad `X = 2^m` with
`√x ≤ X ≤ x²`, a frequency `ξ` and `M = J + 1` slots, with the damping
`h(n) = √q₀^{ω_P(n) - M s_P}` (ℕ subtraction, as in `patternPairing`) and `N_F = L`:

* `f_{X,ξ}(n) = conj(N_F⁻¹ F(n) (n/x)^{2πiξ} (X/n) h(n)) 1[n ∈ [X, 2X)]`;
* `g_X(n') = G(n') h(n') 1[n' ∈ [X, 3X)]`.

Lemma G1: eventually `|f| ≤ 1`, `‖f‖²_phys ≤ 2X` and `‖g‖²_phys ≤ X L^{2C₃}` with
`C₃ = max B₀ 0 + 1`. The clipped core makes PD's divisor moments unnecessary (X4). The list
counts are in `Graph/BoundsLists.lean`, and the crude form `|F| ≤ L` of U7 in `Setup.lean`.
-/

namespace Erdos408.TwoSided

open Filter

/-- The dyads `X = 2^m` with `√x ≤ X ≤ x²`. -/
noncomputable def dyads (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊2 * Real.logb 2 x⌋₊ + 1)).filter fun m => √x ≤ 2 ^ m ∧ (2 : ℝ) ^ m ≤ x ^ 2

/-- The source positions `S_X = [X, 2X)`. -/
noncomputable def dyadSource (X : ℝ) : Finset ℕ :=
  Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊

/-- The target positions `S'_X = [X, 3X)`. -/
noncomputable def dyadTarget (X : ℝ) : Finset ℕ :=
  Finset.Ico ⌈X⌉₊ ⌈3 * X⌉₊

/-- The damping `h(n) = √q₀^{ω_P(n) - M s_P}` of a physical endpoint, with ℕ subtraction as
in `patternPairing`. -/
noncomputable def physicalDamping (q₀ : ℝ) {ι : Type} [Fintype ι] (P : ι → Finset ℕ)
    (M n : ℕ) : ℝ :=
  Real.sqrt q₀ ^ (groupPrimeCount P n - M * Fintype.card ι)

/-- The source endpoint `f_{X,ξ}(n) = conj(N_F⁻¹ F(n) (n/x)^{2πiξ} (X/n) h(n))` on `S_X`, with
`N_F = L`. -/
noncomputable def sourceEndpoint (x q₀ : ℝ) {ι : Type} [Fintype ι] (P : ι → Finset ℕ)
    (J : ℕ) (F : ℕ → ℝ) (X ξ : ℝ) (n : ℕ) : ℂ :=
  if n ∈ dyadSource X then
    starRingEnd ℂ (((Real.log x)⁻¹ * F n * (X / n) * physicalDamping q₀ P (J + 1) n : ℝ) *
      ((n / x : ℝ) : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I))
  else 0

/-- The target endpoint `g_X(n') = G(n') h(n')` on `S'_X`. -/
noncomputable def targetEndpoint (q₀ : ℝ) {ι : Type} [Fintype ι] (P : ι → Finset ℕ)
    (J : ℕ) (G : ℕ → ℝ) (X : ℝ) (n : ℕ) : ℂ :=
  if n ∈ dyadTarget X then ((G n * physicalDamping q₀ P (J + 1) n : ℝ) : ℂ) else 0

/-- The positions of `S_X` lie in `[X, 2X)`. -/
theorem mem_dyadSource {X : ℝ} {n : ℕ} (hn : n ∈ dyadSource X) : X ≤ n ∧ (n : ℝ) < 2 * X := by
  obtain ⟨h₁, h₂⟩ := Finset.mem_Ico.1 hn
  exact ⟨Nat.ceil_le.1 h₁, Nat.lt_ceil.1 h₂⟩

/-- `g_X` vanishes off `S'_X`. -/
theorem targetEndpoint_eq_zero (q₀ : ℝ) {ι : Type} [Fintype ι] (P : ι → Finset ℕ) (J : ℕ)
    (G : ℕ → ℝ) (X : ℝ) {n : ℕ} (hn : n ∉ dyadTarget X) : targetEndpoint q₀ P J G X n = 0 := by
  simp [targetEndpoint, hn]

/-- `‖g_X‖ ≤ L^{B₀}` for a clipped core: `0 ≤ G ≤ L^{B₀}` and `0 ≤ h ≤ 1`. -/
theorem norm_targetEndpoint_le {B₀ x q₀ : ℝ} (hx : 1 < x) (hq₀₁ : q₀ < 1) {ι : Type}
    [Fintype ι] {P : ι → Finset ℕ} {G : ℕ → ℝ} (hG : CoreAdmissible B₀ x P G) (J : ℕ)
    (X : ℝ) (n : ℕ) : ‖targetEndpoint q₀ P J G X n‖ ≤ Real.log x ^ B₀ := by
  have hL0 : 0 < Real.log x := Real.log_pos hx
  have hh0 : 0 ≤ physicalDamping q₀ P (J + 1) n := pow_nonneg (Real.sqrt_nonneg _) _
  have hh1 : physicalDamping q₀ P (J + 1) n ≤ 1 :=
    pow_le_one₀ (Real.sqrt_nonneg _) (Real.sqrt_le_one.2 hq₀₁.le)
  unfold targetEndpoint
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hG.2 n).1 hh0)]
    calc G n * physicalDamping q₀ P (J + 1) n ≤ Real.log x ^ B₀ * 1 :=
          mul_le_mul (hG.2 n).2 hh1 hh0 (Real.rpow_nonneg hL0.le _)
      _ = Real.log x ^ B₀ := mul_one _
  · rw [norm_zero]
    exact Real.rpow_nonneg hL0.le _

/-- A dyad `X = 2^m` satisfies `√x ≤ X ≤ x²`. -/
theorem mem_dyads {x : ℝ} {m : ℕ} (hm : m ∈ dyads x) : √x ≤ 2 ^ m ∧ (2 : ℝ) ^ m ≤ x ^ 2 :=
  (Finset.mem_filter.1 hm).2

/-- Eventually there are at most `4L` dyads. -/
theorem eventually_card_dyads_le : ∀ᶠ x : ℝ in atTop, ((dyads x).card : ℝ) ≤ 4 * Real.log x := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hL
  have hlog2 : (2 / 3 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hb : Real.logb 2 x ≤ 3 / 2 * Real.log x := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have h0 : 0 ≤ Real.logb 2 x := div_nonneg (by linarith) (by linarith)
  calc ((dyads x).card : ℝ) ≤ ((Finset.range (⌊2 * Real.logb 2 x⌋₊ + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = ⌊2 * Real.logb 2 x⌋₊ + 1 := by rw [Finset.card_range]; push_cast; ring
    _ ≤ 2 * Real.logb 2 x + 1 := by
        gcongr
        exact Nat.floor_le (by positivity)
    _ ≤ 4 * Real.log x := by linarith

/-- **Lemma G1 (endpoint bounds).** Eventually, uniformly in the groups, the bands, the
slots, `|B| ≤ 1` and the clipped core, for every dyad `X = 2^m` and frequency `ξ`:
`|f_{X,ξ}| ≤ 1`, `‖f_{X,ξ}‖²_phys ≤ 2X` on `S_X` and `‖g_X‖²_phys ≤ X L^{2C₃}` on `S'_X`, with
`C₃ = max B₀ 0 + 1`. The physical list count is `∑_p 1[Π(p) ∣ n]`, so on an interval of
length `Y + 1`, `∑_n #lists(n) ∏ V^{-M} ≤ Y + 2 ∏_g (|P_g|/V_g)^M`, which is (6.12) plus
`exp(O(J T L^{0.46})) ≤ √x ≤ X`. In place of U7 the proof uses the crude bound `|F| ≤ L`
(`eventually_abs_centeredCore_le_log`). -/
theorem eventually_endpoint_bounds (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ)
    (d : ℕ) (B₀ : ℝ) (hq : 0 < q) (hq₁ : q < 1) (hq₀₁ : q₀ < 1) (hvlo : 0 < vlo)
    (halo : 1 / 10 < alo) (hc : 0 < c) (J : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ)
          (G : ℕ → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v →
          (∀ Q, |Bc Q| ≤ 1) → CoreAdmissible B₀ x P G →
          ∀ m ∈ dyads x, ∀ ξ : ℝ,
            (∀ n, ‖sourceEndpoint x q₀ P J (centeredCore x q a u v Bc) (2 ^ m) ξ n‖ ≤ 1) ∧
            physicalNormSq P (J + 1) (dyadSource (2 ^ m))
                (sourceEndpoint x q₀ P J (centeredCore x q a u v Bc) (2 ^ m) ξ) ≤
              2 * 2 ^ m ∧
            physicalNormSq P (J + 1) (dyadTarget (2 ^ m)) (targetEndpoint q₀ P J G (2 ^ m)) ≤
              2 ^ m * Real.log x ^ (2 * (max B₀ 0 + 1)) := by
  filter_upwards [eventually_abs_centeredCore_le_log q alo ahi K₀ CN c d hq hq₁
      halo hc, GraphBounds.eventually_two_mul_prod_card_le_sqrt c₀ C₀ vlo vhi hvlo (J + 1),
    Real.tendsto_log_atTop.eventually_ge_atTop 2, eventually_ge_atTop 2]
    with x hF hcount hL2 hx2 ι _ _ P big hP r a u v Bc G ha hslot hB hG m hm ξ
  obtain ⟨hX₁, hX₂⟩ := mem_dyads hm
  set X : ℝ := 2 ^ m with hXdef
  set L := Real.log x
  have hX1 : 1 ≤ X := one_le_pow₀ (by norm_num)
  have hL0 : 0 < L := by linarith
  -- the groups are disjoint sets of primes of mass at least `v₋`
  have hdisj := hP.1
  have hprime : ∀ g, ∀ p ∈ P g, p.Prime := by
    intro g p hp
    by_cases hg : g ∈ big
    · exact (Finset.mem_filter.1 (hP.2.2.2.2.2.2.2.1 g hg hp)).2
    · exact (Finset.mem_filter.1 (hP.2.2.2.2.2.2.1 g hg hp)).2
  have hV : ∀ g, 0 < harmonicMass (P g) := fun g => hvlo.trans_le (hP.2.2.2.2.2.1 g).1
  have hcount' : 2 * ∏ g, ((Finset.card (P g) : ℝ) * (harmonicMass (P g))⁻¹) ^ (J + 1) ≤ X :=
    (hcount P big hP).trans hX₁
  -- the damping `0 ≤ h ≤ 1`
  have hh : ∀ n, 0 ≤ physicalDamping q₀ P (J + 1) n ∧ physicalDamping q₀ P (J + 1) n ≤ 1 :=
    fun n => ⟨pow_nonneg (Real.sqrt_nonneg _) _,
      pow_le_one₀ (Real.sqrt_nonneg _) (Real.sqrt_le_one.2 hq₀₁.le)⟩
  -- `|f| ≤ 1`
  have hf : ∀ n, ‖sourceEndpoint x q₀ P J (centeredCore x q a u v Bc) X ξ n‖ ≤ 1 := by
    intro n
    unfold sourceEndpoint
    split_ifs with hn
    · obtain ⟨hXn, hn2⟩ := mem_dyadSource hn
      have hn0 : (0 : ℝ) < n := by linarith
      have hn1 : 1 ≤ n := by exact_mod_cast hX1.trans hXn
      have hnx : (n : ℝ) ≤ x ^ 3 := by
        have : x ^ 3 = x * x ^ 2 := by ring
        nlinarith
      have hFn := hF r a u v Bc ha hslot hB n hn1 hnx
      rw [Complex.norm_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
        Complex.I_im, mul_one, sub_self, Real.rpow_zero]
      rw [show Real.log x = L from rfl, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hh n).1,
        abs_of_pos (inv_pos.2 hL0), abs_of_nonneg (div_nonneg (by linarith) hn0.le)]
      have hXn' : X / n ≤ 1 := (div_le_one hn0).2 hXn
      calc L⁻¹ * |centeredCore x q a u v Bc n| * (X / n) * physicalDamping q₀ P (J + 1) n
          ≤ L⁻¹ * L * 1 * 1 := by
            refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hFn (by positivity)) hXn'
              (div_nonneg (by linarith) hn0.le) (by positivity)) (hh n).2 (hh n).1
              (by positivity)
        _ = 1 := by field_simp
    · simp
  refine ⟨hf, ?_, ?_⟩
  · -- the source norm: `X + 2 ∏ (|P| V⁻¹)^M ≤ 2X`
    have hab : ⌈X⌉₊ ≤ ⌈2 * X⌉₊ := Nat.ceil_mono (by linarith)
    have hba : ((⌈2 * X⌉₊ : ℕ) : ℝ) - ⌈X⌉₊ ≤ X + 1 := by
      have h₁ := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * X by linarith)
      have h₂ := Nat.le_ceil X
      linarith
    have h := GraphBounds.physicalNormSq_Ico_le hdisj hprime hV (J + 1) hab hba
      (fun n _ => hf n)
    unfold dyadSource
    rw [one_pow, one_mul] at h
    linarith
  · -- the target norm: `L^{2B₀} (2X + 2 ∏ (|P| V⁻¹)^M) ≤ 3X L^{2B₀} ≤ X L^{2C₃}`
    have hab : ⌈X⌉₊ ≤ ⌈3 * X⌉₊ := Nat.ceil_mono (by linarith)
    have hba : ((⌈3 * X⌉₊ : ℕ) : ℝ) - ⌈X⌉₊ ≤ 2 * X + 1 := by
      have h₁ := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3 * X by linarith)
      have h₂ := Nat.le_ceil X
      linarith
    have h := GraphBounds.physicalNormSq_Ico_le hdisj hprime hV (J + 1) hab hba
      fun n _ => norm_targetEndpoint_le (by linarith) hq₀₁ hG J X n
    unfold dyadTarget
    have hL1 : 1 ≤ L := by linarith
    have hpow : (L ^ B₀) ^ 2 ≤ L ^ (2 * max B₀ 0) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
      rw [Nat.cast_ofNat]
      linarith [le_max_left B₀ 0]
    have hsplit : L ^ (2 * (max B₀ 0 + 1)) = L ^ (2 * max B₀ 0) * L ^ 2 := by
      rw [show 2 * (max B₀ 0 + 1) = 2 * max B₀ 0 + (2 : ℕ) by push_cast; ring,
        Real.rpow_add hL0, Real.rpow_natCast]
    have hL4 : 4 ≤ L ^ 2 := by nlinarith
    have hP0 : 0 ≤ L ^ (2 * max B₀ 0) := Real.rpow_nonneg hL0.le _
    have hprod0 : 0 ≤ ∏ g, ((Finset.card (P g) : ℝ) * (harmonicMass (P g))⁻¹) ^ (J + 1) :=
      Finset.prod_nonneg fun g _ =>
        pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 (hV g).le)) _
    refine h.trans ?_
    rw [hsplit]
    calc (L ^ B₀) ^ 2 * (2 * X + 2 * ∏ g, ((Finset.card (P g) : ℝ) *
          (harmonicMass (P g))⁻¹) ^ (J + 1))
        ≤ L ^ (2 * max B₀ 0) * (3 * X) :=
          mul_le_mul hpow (by linarith) (by linarith [hprod0]) hP0
      _ ≤ L ^ (2 * max B₀ 0) * (L ^ 2 * X) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hP0
      _ = X * (L ^ (2 * max B₀ 0) * L ^ 2) := by ring

end Erdos408.TwoSided
