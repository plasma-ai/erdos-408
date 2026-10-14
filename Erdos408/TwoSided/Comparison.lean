import Erdos408.TwoSided.Comparison.Arcs
import Erdos408.TwoSided.Endpoint
import Erdos408.TwoSided.Graph.Insertion

/-!
# The comparison bound

Interface C of `blueprint/two_sided_correlation.md` §3.3 (PD §6.3, S5–S10): each stripped
comparison correlation is `O(L^{-A''})` under the premises AP1 and AP2.

* §5.1 (`Comparison/Separation.lean`): a second Mellin separation and a partition of unity
  write `strippedComparison = ∫ a(ξ) x^{-iσ} ∑_m y_m Y_m⁻¹ 𝔅_m dξ`, and `|Y_m⁻¹ 𝔅_m| ≤ L^{C₅}`.
* §§5.2–5.4 (`Comparison/Multiplier.lean`, `Comparison/Arcs.lean`): for `|ξ| ≤ L^{C_f}`, the
  minor arcs and the local Mellin energy bound `|Y_m⁻¹ 𝔅_m|` by the mean square (6.24), which
  interface E (`Endpoint.lean`) bounds by `C_E L^{-A_SM}`.

The constants: `A_m = A'' + K_Ψ`, the arc exponents `(C_arc, C_cost)`,
`C_m = max(C_arc, C_f + 3)` (so `|σ| = 2π|ξ| ≤ L^{C_m}`), `A_SM = 2(A'' + K_Ψ + C_cost)`; the
witness `A'` is interface E's at `(m₀, C_m, A_SM, M₁)`, and none of them depends on `E` (§1.3).
-/

namespace Erdos408.TwoSided

open Filter MeasureTheory

/-- **Interface C.** For the fixed data, `m₀` and `A''` there are `A'` and `C_m` such that for
every `E, κ'` there is `C_C` with: eventually, under `PrimeTwistBound x A' E C_m κ'` and
`IntegerKernelBound x C_m κ'`, for groups as in (6.1), all admissible data and every
comparison pattern, `|strippedComparison| ≤ C_C L^{-A''}`. -/
theorem exists_comparison_bound
    (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ) (d : ℕ) (B₀ κ CΨ : ℝ) (M : ℕ → ℝ)
    (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1) (hc₀ : 0 < c₀)
    (hvlo : 0 < vlo) (halo : 1 / 10 < alo) (hal : alo ≤ ahi) (hahi : ahi < 1 / 5) (hc : 0 < c)
    (hκ : 1 < κ) (m₀ : ℕ) (A'' : ℝ) :
    ∃ A' Cm : ℝ, ∀ E κ' : ℝ, ∃ CC : ℝ, ∀ᶠ x : ℝ in atTop,
      PrimeTwistBound x A' E Cm κ' → IntegerKernelBound x Cm κ' →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ)
          (G : ℕ → ℝ) (Ψ : ℝ → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v → (∀ Q, |Bc Q| ≤ 1) →
          CoreAdmissible B₀ x P G → CutoffAdmissible κ CΨ M x Ψ →
          ∀ (J : ℕ) (Aν Bν : ι → Finset (Fin J)) (φ φ' ψ ψ' : ℕ → ℂ) (U U' : ℝ),
            ComparisonPattern m₀ big Aν Bν φ φ' ψ ψ' U U' →
            ‖strippedComparison x q₀ P Aν Bν φ φ' ψ ψ' (centeredCore x q a u v Bc) G Ψ‖ ≤
              CC * Real.log x ^ (-A'') := by
  obtain ⟨n, ψ₁, y, M₁, hψ, hy, hsum⟩ := exists_partition κ hκ
  obtain ⟨Cf, KΨ, -, hmel⟩ := exists_mellinCutoff κ CΨ M hκ
  obtain ⟨C₅, habs⟩ := exists_norm_comparisonBilinear_le q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN c d
    B₀ κ hq hq₁ hq₀ hq₀₁ hvlo halo hc hκ m₀ (M₁ 0)
  obtain ⟨Carc, Ccost, harc⟩ := exists_norm_comparisonBilinear_le_arcs q q₀ c₀ C₀ vlo vhi alo
    ahi K₀ CN c d B₀ κ hq hq₁ hq₀ hq₀₁ hvlo halo hc hκ m₀ M₁ (A'' + KΨ)
  set Cm : ℝ := max Carc (Cf + 3) with hCm
  obtain ⟨A', hE⟩ := exists_endpoint_meanSquare q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN c d hq hq₁ hq₀
    hq₀₁ hc₀ hvlo halo hal hahi hc m₀ Cm (2 * (A'' + KΨ + Ccost)) M₁
  refine ⟨A', Cm, fun E κ' => ?_⟩
  obtain ⟨CE, hEx⟩ := hE E κ'
  obtain ⟨Karc, harcx⟩ := harc Cm (le_max_left _ _) (A'' + KΨ + Ccost)
  obtain ⟨KA, hKA, hmelx⟩ := hmel (|A''| + |C₅| + 1) (by positivity)
  set yb : ℝ := 2 * κ * Real.exp 2 with hyb
  refine ⟨n * yb * (|Karc| * (2 + Real.sqrt |CE|) + KA), ?_⟩
  filter_upwards [hEx, harcx, habs, hmelx,
    eventually_strippedComparison_eq q q₀ c₀ C₀ vlo vhi κ hκ m₀ (fun m => (hψ m).2.1) hy hsum,
    Real.tendsto_log_atTop.eventually_ge_atTop 2, eventually_gt_atTop 0]
    with x hEx harcx habs hmelx hsep hL hx0
  intro hAP1 hAP2 ι _ _ P big hadm r a u v Bc G Ψ hin hsl hBc hco hcu J Aν Bν φ φ' ψ ψ' U U'
    hpat
  obtain ⟨α, hαi, hα₁, hαrep, hαt⟩ := hmelx Ψ hcu
  rw [hsep P big hadm a u v Bc G Ψ J Aν Bν φ φ' ψ ψ' U U' hpat α hαi hcu.2.1 hαrep]
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hyb0 : 0 ≤ yb := by positivity
  -- the source test reads only the big groups
  have hCcard : ∀ g, (Aν g ∪ Bν g).card ≤ m₀ := fun g => (hpat.1 g).2
  have hCbig : ∀ g ∉ big, Aν g ∪ Bν g = ∅ := fun g hg => by
    rw [(hpat.2.1 g hg).1, (hpat.2.1 g hg).2, Finset.empty_union]
  have hb₁ : ∀ p : ι → Fin (J + 1) → ℕ, ‖ψ' (slotProduct Bν fun g i => p g i.castSucc)‖ ≤ 1 :=
    fun p => (hpat.2.2.2.1 _).2.2.2
  have hbb : ∀ p p' : ι → Fin (J + 1) → ℕ, (∀ g ∈ big, p g = p' g) →
      ψ' (slotProduct Bν fun g i => p g i.castSucc) =
        ψ' (slotProduct Bν fun g i => p' g i.castSucc) := by
    intro p p' hpp
    congr 1
    refine Finset.prod_congr rfl fun g _ => ?_
    show ∏ i ∈ Bν g, p g i.castSucc = ∏ i ∈ Bν g, p' g i.castSucc
    by_cases hg : g ∈ big
    · rw [hpp g hg]
    · rw [(hpat.2.1 g hg).2, Finset.prod_empty, Finset.prod_empty]
  -- the bound at frequencies `|ξ| ≤ L^{C_f}`
  have hσL : ∀ ξ : ℝ, |ξ| ≤ L ^ Cf → |2 * Real.pi * ξ| ≤ L ^ Cm := by
    intro ξ hξ
    have hL3 : 2 * Real.pi ≤ L ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      nlinarith [Real.pi_le_four, pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL 3]
    rw [abs_mul, abs_of_pos Real.two_pi_pos]
    calc 2 * Real.pi * |ξ| ≤ L ^ (3 : ℝ) * L ^ Cf :=
          mul_le_mul hL3 hξ (abs_nonneg _) (by positivity)
      _ = L ^ (Cf + 3) := by rw [Real.rpow_add hL0]; ring
      _ ≤ L ^ Cm := Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _)
  have hsq : Real.sqrt (CE * L ^ (-(2 * (A'' + KΨ + Ccost)))) ≤
      Real.sqrt |CE| * L ^ (-(A'' + KΨ + Ccost)) := by
    calc Real.sqrt (CE * L ^ (-(2 * (A'' + KΨ + Ccost))))
        ≤ Real.sqrt (|CE| * L ^ (-(2 * (A'' + KΨ + Ccost)))) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      _ = Real.sqrt |CE| * L ^ (-(A'' + KΨ + Ccost)) := by
          rw [Real.sqrt_mul (abs_nonneg _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
            ← Real.rpow_mul hL0.le]
          congr 2
          ring
  have hpiece : ∀ ξ : ℝ, |ξ| ≤ L ^ Cf → ∀ m,
      ‖(((y m * (x * U * U')) : ℝ) : ℂ)⁻¹ *
          comparisonBilinear x q q₀ a u v Bc P Aν Bν φ φ' ψ ψ' G (ψ₁ m) (y m * (x * U * U'))
            (2 * Real.pi * ξ)‖ ≤
        |Karc| * (2 + Real.sqrt |CE|) * L ^ (-(A'' + KΨ)) := by
    intro ξ hξ m
    have h := harcx P big hadm r a u v Bc G hin hsl hBc hco J Aν Bν φ φ' ψ ψ' U U' hpat (ψ₁ m)
      (hψ m).1 (hψ m).2.1 (hψ m).2.2 (y m) (2 * Real.pi * ξ)
      (CE * L ^ (-(2 * (A'' + KΨ + Ccost)))) (hy m).1 (hy m).2
      (fun hY₁ hY₂ k h hk₁ hk₂ => hEx hAP1 hAP2 P big hadm r a u v Bc hin hsl hBc J
        (fun g => Aν g ∪ Bν g) (fun p => ψ' (slotProduct Bν fun g i => p g i.castSucc)) hCcard
        hCbig hb₁ hbb (ψ₁ m) (hψ m).1 (hψ m).2.1 (hψ m).2.2 (y m * (x * U * U'))
        (2 * Real.pi * ξ) k h hY₁ hY₂ (hσL ξ hξ) hk₁ hk₂)
    refine h.trans ?_
    have e₁ : L ^ Ccost * L ^ (-(A'' + KΨ + Ccost)) = L ^ (-(A'' + KΨ)) := by
      rw [← Real.rpow_add hL0]
      ring_nf
    have hp : 0 ≤ L ^ (-(A'' + KΨ)) := by positivity
    calc Karc * (L ^ (-(A'' + KΨ)) + L ^ Ccost * (Real.sqrt (CE * L ^ (-(2 * (A'' + KΨ +
          Ccost)))) + L ^ (-(A'' + KΨ + Ccost))))
        ≤ |Karc| * (L ^ (-(A'' + KΨ)) + L ^ Ccost * (Real.sqrt |CE| *
            L ^ (-(A'' + KΨ + Ccost)) + L ^ (-(A'' + KΨ + Ccost)))) := by
          refine mul_le_mul (le_abs_self _) ?_ (by positivity) (abs_nonneg _)
          gcongr
      _ = |Karc| * (2 + Real.sqrt |CE|) * L ^ (-(A'' + KΨ)) := by
          rw [show L ^ Ccost * (Real.sqrt |CE| * L ^ (-(A'' + KΨ + Ccost)) +
              L ^ (-(A'' + KΨ + Ccost))) = (Real.sqrt |CE| + 1) *
              (L ^ Ccost * L ^ (-(A'' + KΨ + Ccost))) by ring, e₁]
          ring
  -- the sum over the pieces
  have hxσ : ∀ ξ : ℝ, ‖(x : ℂ) ^ (-(((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I))‖ = 1 := by
    intro ξ
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp
  have hsum_le : ∀ ξ B : ℝ, 0 ≤ B →
      (∀ m, ‖(((y m * (x * U * U')) : ℝ) : ℂ)⁻¹ *
          comparisonBilinear x q q₀ a u v Bc P Aν Bν φ φ' ψ ψ' G (ψ₁ m) (y m * (x * U * U'))
            (2 * Real.pi * ξ)‖ ≤ B) →
      ‖(x : ℂ) ^ (-(((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) *
          ∑ m, (y m : ℂ) * ((((y m * (x * U * U')) : ℝ) : ℂ)⁻¹ *
            comparisonBilinear x q q₀ a u v Bc P Aν Bν φ φ' ψ ψ' G (ψ₁ m)
              (y m * (x * U * U')) (2 * Real.pi * ξ))‖ ≤ n * yb * B := by
    intro ξ B hB0 hB
    rw [norm_mul, hxσ, one_mul]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ m, ‖(y m : ℂ) * ((((y m * (x * U * U')) : ℝ) : ℂ)⁻¹ *
            comparisonBilinear x q q₀ a u v Bc P Aν Bν φ φ' ψ ψ' G (ψ₁ m)
              (y m * (x * U * U')) (2 * Real.pi * ξ))‖
        ≤ ∑ _m : Fin n, yb * B := by
          refine Finset.sum_le_sum fun m _ => ?_
          have hy0 : 0 ≤ y m := le_trans (by positivity) (hy m).1
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hy0]
          exact mul_le_mul (hy m).2 (hB m) (norm_nonneg _) hyb0
      _ = n * yb * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have h₁ : ∀ ξ : ℝ, |ξ| ≤ L ^ Cf →
      ‖(x : ℂ) ^ (-(((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) *
          ∑ m, (y m : ℂ) * ((((y m * (x * U * U')) : ℝ) : ℂ)⁻¹ *
            comparisonBilinear x q q₀ a u v Bc P Aν Bν φ φ' ψ ψ' G (ψ₁ m)
              (y m * (x * U * U')) (2 * Real.pi * ξ))‖ ≤
        n * yb * (|Karc| * (2 + Real.sqrt |CE|) * L ^ (-(A'' + KΨ))) :=
    fun ξ hξ => hsum_le ξ _ (by positivity) (hpiece ξ hξ)
  have h₂ : ∀ ξ : ℝ,
      ‖(x : ℂ) ^ (-(((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) *
          ∑ m, (y m : ℂ) * ((((y m * (x * U * U')) : ℝ) : ℂ)⁻¹ *
            comparisonBilinear x q q₀ a u v Bc P Aν Bν φ φ' ψ ψ' G (ψ₁ m)
              (y m * (x * U * U')) (2 * Real.pi * ξ))‖ ≤ n * yb * L ^ C₅ :=
    fun ξ => hsum_le ξ _ (by positivity) fun m => habs P big hadm r a u v Bc G hin hsl hBc hco
      J Aν Bν φ φ' ψ ψ' U U' hpat (ψ₁ m) (y m) (2 * Real.pi * ξ) (hψ m).2.1
      (fun z => by simpa using (hψ m).2.2 0 z) (hy m).1 (hy m).2
  refine (norm_integral_mul_le_of_split hαi (by positivity) h₁ h₂).trans ?_
  have e₁ : L ^ (-(A'' + KΨ)) * L ^ KΨ = L ^ (-A'') := by
    rw [← Real.rpow_add hL0]
    ring_nf
  have e₂ : L ^ C₅ * L ^ (-(|A''| + |C₅| + 1)) ≤ L ^ (-A'') := by
    rw [← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [le_abs_self A'', le_abs_self C₅])
  calc n * yb * (|Karc| * (2 + Real.sqrt |CE|) * L ^ (-(A'' + KΨ))) * (∫ ξ, ‖α ξ‖) +
        n * yb * L ^ C₅ * ∫ ξ in {ξ : ℝ | L ^ Cf < |ξ|}, ‖α ξ‖
      ≤ n * yb * (|Karc| * (2 + Real.sqrt |CE|) * L ^ (-(A'' + KΨ))) * L ^ KΨ +
          n * yb * L ^ C₅ * (KA * L ^ (-(|A''| + |C₅| + 1))) :=
        add_le_add (mul_le_mul_of_nonneg_left hα₁ (by positivity))
          (mul_le_mul_of_nonneg_left hαt (by positivity))
    _ = n * yb * (|Karc| * (2 + Real.sqrt |CE|) * (L ^ (-(A'' + KΨ)) * L ^ KΨ) +
          KA * (L ^ C₅ * L ^ (-(|A''| + |C₅| + 1)))) := by ring
    _ ≤ n * yb * (|Karc| * (2 + Real.sqrt |CE|) * L ^ (-A'') + KA * L ^ (-A'')) := by
        rw [e₁]
        gcongr
    _ = n * yb * (|Karc| * (2 + Real.sqrt |CE|) + KA) * L ^ (-A'') := by ring

end Erdos408.TwoSided
