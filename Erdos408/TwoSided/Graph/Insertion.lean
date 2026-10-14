module

public import Erdos408.TwoSided.Endpoint.Tuple.Exceptional
public import Erdos408.TwoSided.Graph.Absolute
public import Erdos408.TwoSided.Graph.Insertion.Identity
public import Erdos408.TwoSided.Graph.Insertion.MellinAdapter

/-!
# Mellin insertion, dyads and transference

S2 of `blueprint/two_sided_correlation.md` §4.2 (PD §6.2, (6.13); WD §5.2; X6).

* `exists_mellinCutoff`: the cutoff class has a Mellin density `a` with `∫ |a| ≤ L^{K_Ψ}`
  and tail `∫_{|ξ| > L^{C_f}} |a| ≤ K_A L^{-A_t}`, the cutoff frequency `C_f` fixed before the
  tail saving `A_t` (WD's upstream `MellinCutoffTask`).
* `cutoffPairing` is the pattern pairing with `f` replaced by `Ψ(n/(xD)) F(n) h(n)/n` and
  `ζ = 0`, the quantity `Π_C^Ψ` of Lemma G2; `comparisonKernel` is the coefficient of one
  comparison pattern of `GraphTransference`'s family.
* Lemma G2 (`eventually_cutoffPairing_eq`): `Π^Ψ` is `N_F ∑_X X⁻¹ ∫ a(ξ) ⟨f_{X,ξ}, 𝒜 g_X⟩ dξ`
  at `ζ = -2πξ`, exactly.
* Lemma G3 (`eventually_norm_cutoffPairing_family_le`): split each `ξ`-integral at
  `|ξ| = L^{C_f}`. Inside, `GraphTransference` applies by G1; the tail is bounded by G2a.
-/

@[expose] public section

namespace Erdos408.TwoSided

open Filter MeasureTheory

/-- **Mellin cutoff (X6).** For the cutoff class there are `C_f > 0` and `K_Ψ` such that,
for every tail saving `A_t > 0`, there is `K_A` with: eventually, every admissible `Ψ` has a
density `a` with `∫ |a| ≤ L^{K_Ψ}`, `Ψ(y) = ∫ a(ξ) y^{2πiξ} dξ` for `y > 0` and
`∫_{|ξ| > L^{C_f}} |a| ≤ K_A L^{-A_t}`. The class satisfies upstream's `CutoffBound` at
`C = 1`, `lo = κ⁻¹`, `hi = κ`, `bounds j = max (M j) 0` eventually, uniformly in `j`, since
`T^{C_Ψ j} ≤ L^{j+1}` once `max(C_Ψ, 0) log T ≤ T`. The densities are upstream's
(`mellinCutoffTask_proof`, from `blueprint_lem_fourier_separation`), transported from
`Fin 1 → ℝ` frequencies and `ℂ`-valued cutoffs. -/
theorem exists_mellinCutoff (κ CΨ : ℝ) (M : ℕ → ℝ) (hκ : 1 < κ) :
    ∃ Cf KΨ : ℝ, 0 < Cf ∧ ∀ At : ℝ, 0 < At → ∃ KA : ℝ, 0 < KA ∧ ∀ᶠ x : ℝ in atTop,
      ∀ Ψ : ℝ → ℝ, CutoffAdmissible κ CΨ M x Ψ →
        ∃ a : ℝ → ℂ, Integrable a ∧ (∫ ξ, ‖a ξ‖) ≤ Real.log x ^ KΨ ∧
          (∀ y : ℝ, 0 < y →
            (Ψ y : ℂ) = ∫ ξ, a ξ * (y : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) ∧
          (∫ ξ in {ξ : ℝ | Real.log x ^ Cf < |ξ|}, ‖a ξ‖) ≤ KA * Real.log x ^ (-At) := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨Cf, KΨ, hCf, -, hmel⟩ := Erdos821.P5Mellin.mellinCutoffTask_proof
    Erdos821.Classical.blueprint_lem_fourier_separation 1 κ⁻¹ κ (fun j => max (M j) 0)
    one_pos (inv_pos.2 hκ0) ((inv_lt_one_of_one_lt₀ hκ).trans hκ) (fun j => le_max_right _ _)
  refine ⟨Cf, KΨ, hCf, fun At hAt => ?_⟩
  obtain ⟨KA, hKA, hx⟩ := hmel At hAt
  refine ⟨KA, hKA, ?_⟩
  filter_upwards [hx, InsertionMellin.eventually_iteratedDeriv_bound CΨ M] with x hx hder
  intro Ψ hΨ
  obtain ⟨hsm, hsupp, hbd⟩ := hΨ
  obtain ⟨a, hai, ha₁, harep, hat⟩ := hx (fun y => (Ψ y : ℂ)) ⟨
    Complex.ofRealCLM.contDiff.comp hsm,
    fun y hy => by
      obtain ⟨h₁, h₂⟩ := hsupp y (by simpa using Function.mem_support.1 hy)
      exact ⟨h₁, h₂⟩,
    fun k y => by
      rw [InsertionMellin.norm_iteratedDeriv_ofReal hsm]
      exact hder Ψ k y (hbd k y)⟩
  -- transport along `t ↦ (fun _ => t)`
  set e := (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
  have hmp : MeasurePreserving e volume volume := (volume_preserving_funUnique (Fin 1) ℝ).symm
  have he₀ : ∀ t, e t 0 = t := fun t => rfl
  refine ⟨fun t => a (e t), (hmp.integrable_comp_emb e.measurableEmbedding).2 hai, ?_, ?_, ?_⟩
  · rw [hmp.integral_comp' (fun ξ => ‖a ξ‖)]
    exact ha₁
  · intro y hy
    rw [harep y hy, ← hmp.integral_comp' (fun ξ => a ξ * Erdos821.Blueprint.Analytic.mellin y
      (2 * Real.pi * ξ 0))]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [he₀, TupleHigh.mellin_eq_cpow hy]
  · have hpre : e ⁻¹' {ξ : Fin 1 → ℝ | Erdos821.Blueprint.Analytic.L x ^ Cf < ‖ξ‖} =
        {ξ : ℝ | Real.log x ^ Cf < |ξ|} := by
      ext t
      have : ‖e t‖ = |t| := by
        change ‖fun _ : Fin 1 => t‖ = |t|
        rw [pi_norm_const, Real.norm_eq_abs]
      change Real.log x ^ Cf < ‖e t‖ ↔ Real.log x ^ Cf < |t|
      rw [this]
    rw [← hpre, hmp.setIntegral_preimage_emb e.measurableEmbedding (fun ξ => ‖a ξ‖)]
    exact hat

/-- The coefficient `β φ(D_A) φ'(D_B) ψ(X_A) ψ'(X_B)` of one comparison pattern, as in
`GraphTransference`. -/
def comparisonKernel {ι : Type} [Fintype ι] {J : ℕ} (A B : ι → Finset (Fin J)) (β : ℂ)
    (φ φ' ψ ψ' : ℕ → ℂ) :
    (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ :=
  fun p p' a => β * φ (slotProduct A a) * φ' (slotProduct B a) *
    ψ (slotProduct A fun h i => p' h i.castSucc) * ψ' (slotProduct B fun h i => p h i.castSucc)

/-- The comparison coefficient is at most `|β|` when the tests are bounded by `1`. -/
theorem norm_comparisonKernel_le {ι : Type} [Fintype ι] {J : ℕ} {A B : ι → Finset (Fin J)}
    {β : ℂ} {φ φ' ψ ψ' : ℕ → ℂ} (h : ∀ n, ‖φ n‖ ≤ 1 ∧ ‖φ' n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖ψ' n‖ ≤ 1)
    (p p' : ι → Fin (J + 1) → ℕ) (a : ι → Fin J → ℕ) :
    ‖comparisonKernel A B β φ φ' ψ ψ' p p' a‖ ≤ ‖β‖ := by
  unfold comparisonKernel
  simp only [norm_mul]
  have h₁ := (h (slotProduct A a)).1
  have h₂ := (h (slotProduct B a)).2.1
  have h₃ := (h (slotProduct A fun h i => p' h i.castSucc)).2.2.1
  have h₄ := (h (slotProduct B fun h i => p h i.castSucc)).2.2.2
  calc ‖β‖ * ‖φ (slotProduct A a)‖ * ‖φ' (slotProduct B a)‖ *
        ‖ψ (slotProduct A fun h i => p' h i.castSucc)‖ *
        ‖ψ' (slotProduct B fun h i => p h i.castSucc)‖ ≤ ‖β‖ * 1 * 1 * 1 * 1 := by gcongr
    _ = ‖β‖ := by ring

/-- `Π_C^Ψ` of Lemma G2: the pattern pairing of `C` with kernel `K`, with the source endpoint
`Ψ(n/(xD)) F(n) h(n)/n`, the target endpoint `G(n') h(n')` and `ζ = 0`, over positions
`n ≤ x²`. The two dampings `h` and the pairing's `√q₀` factors combine to `q₀^{ω - M s_P}`. -/
noncomputable def cutoffPairing (x q₀ : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) {J : ℕ} (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
    (F G : ℕ → ℝ) (Ψ : ℝ → ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x ^ 2⌋₊, ∑ p ∈ physicalLists P (J + 1) n, ∑ a ∈ auxLabels P C,
    ∑ p' ∈ (physicalLists P (J + 1) (n + edgeProduct C p a)).filter (fun p' =>
        ∀ h, (∀ i, i ∉ C h → p' h i.castSucc = p h i.castSucc) ∧
          ∀ i ∈ C h, ∀ j, a h i ≠ p h j ∧ a h i ≠ p' h j),
      ((∏ h, (harmonicMass (P h))⁻¹ ^ (J + 1) *
          (∏ i ∈ C h, (harmonicMass (P h) * a h i)⁻¹) *
          (harmonicMass (P h))⁻¹ ^ ((C h).card + 1) : ℝ) : ℂ) * K p p' a *
        ((Ψ (n / (x * edgeProduct C p a)) / n * F n * G (n + edgeProduct C p a) *
          q₀ ^ (groupPrimeCount P n - (J + 1) * Fintype.card ι) *
          q₀ ^ (groupPrimeCount P (n + edgeProduct C p a) - (J + 1) * Fintype.card ι) : ℝ) :
          ℂ)

/-- **Lemma G2 (insertion identity, exact).** Eventually, for groups as in (6.1), every
family of patterns `(C_ν, K_ν)`, all `F, G` and every `Ψ` supported in `[κ⁻¹, κ]` with a
Mellin density `a`, the raw plus comparison cutoff pairings equal
`N_F ∑_{X dyadic} X⁻¹ ∫ a(ξ) (⟨f_{X,ξ}, 𝒜_raw g_X⟩ + ∑_ν ⟨f_{X,ξ}, 𝒜_ν g_X⟩) dξ` at
`ζ = -2πξ`, with `N_F = L`. The dyads `[X, 2X)` partition the support `n ∈ [x/κ, x²]`,
since `1 ≤ D ≤ x/κ` (U10); for such `n` every target `n + D` lies in `[X, 3X)`; and
`(n/x)^{2πiξ} D^{-2πiξ} = (n/(xD))^{2πiξ}`. -/
theorem eventually_cutoffPairing_eq (q₀ c₀ C₀ vlo vhi κ : ℝ) (hq₀ : 0 < q₀) (hκ : 1 < κ)
    (J : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (N : ℕ) (C : Fin N → ι → Finset (Fin J))
          (K : Fin N → (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
          (F G : ℕ → ℝ) (Ψ : ℝ → ℝ) (a : ℝ → ℂ),
          (∀ y, Ψ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) → Integrable a →
          (∀ y : ℝ, 0 < y →
            (Ψ y : ℂ) = ∫ ξ, a ξ * (y : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) →
          cutoffPairing x q₀ P (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1) F G Ψ +
              ∑ ν, cutoffPairing x q₀ P (C ν) (K ν) F G Ψ =
            (Real.log x : ℂ) * ∑ m ∈ dyads x, (((2 : ℝ) ^ m : ℝ) : ℂ)⁻¹ *
              ∫ ξ, a ξ *
                (patternPairing P q₀ (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1)
                    (-(2 * Real.pi * ξ)) (dyadSource (2 ^ m))
                    (sourceEndpoint x q₀ P J F (2 ^ m) ξ) (targetEndpoint q₀ P J G (2 ^ m)) +
                  ∑ ν, patternPairing P q₀ (C ν) (K ν) (-(2 * Real.pi * ξ)) (dyadSource (2 ^ m))
                    (sourceEndpoint x q₀ P J F (2 ^ m) ξ) (targetEndpoint q₀ P J G (2 ^ m))) :=
  InsertionIdentity.eventually_sum_cutoffTerm_eq q₀ c₀ C₀ vlo vhi κ hq₀ hκ J

/-- **Lemma G3 (residual pairing).** There are `m₀, J, C₁` (from `GraphTransference` at
`(E_G, C₃, C₄) = (A + 2C₃ + K_Ψ + 2, max B₀ 0 + 1, C_f + 3)`) and `C_res` such that,
eventually, for groups as in (6.1), the family supplied by `GraphTransference` satisfies
`|Π^Ψ_raw + ∑_ν Π^Ψ_ν| ≤ C_res L^{-A}` for all admissible data. By G2, split each
`ξ`-integral at `|ξ| = L^{C_f}`: inside, `|ζ| = 2π|ξ| ≤ L^{C₄}` and G1 gives the norm
hypotheses of `GraphTransference`; the tail is bounded by G2a and the Mellin tail at
`A_t = |A| + |C₁| + |C_abs| + 4`. There are at most `4L` dyads, and `N_F = L`. -/
theorem eventually_norm_cutoffPairing_family_le (hG : GraphTransference)
    (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ) (d : ℕ) (B₀ κ CΨ : ℝ)
    (M : ℕ → ℝ) (A : ℝ) (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1)
    (hc₀ : 0 < c₀) (hvlo : 0 < vlo) (halo : 1 / 10 < alo) (hc : 0 < c) (hκ : 1 < κ) :
    ∃ (m₀ J : ℕ) (C₁ Cres : ℝ), ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∃ (N : ℕ) (Aν Bν : Fin N → ι → Finset (Fin J)) (β : Fin N → ℂ)
          (φ φ' ψ ψ' : Fin N → ℕ → ℂ) (U U' : Fin N → ℝ),
          (∀ ν, ComparisonPattern m₀ big (Aν ν) (Bν ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν) (U ν)
            (U' ν)) ∧
          ∑ ν, ‖β ν‖ ≤ Real.log x ^ C₁ ∧
          ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ)
            (G : ℕ → ℝ) (Ψ : ℝ → ℝ),
            InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v →
            (∀ Q, |Bc Q| ≤ 1) → CoreAdmissible B₀ x P G → CutoffAdmissible κ CΨ M x Ψ →
            ‖cutoffPairing x q₀ P (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1)
                  (centeredCore x q a u v Bc) G Ψ +
                ∑ ν, cutoffPairing x q₀ P (fun h => Aν ν h ∪ Bν ν h)
                  (comparisonKernel (Aν ν) (Bν ν) (β ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν))
                  (centeredCore x q a u v Bc) G Ψ‖ ≤
              Cres * Real.log x ^ (-A) := by
  obtain ⟨Cf, KΨ, -, hmel⟩ := exists_mellinCutoff κ CΨ M hκ
  set C₃ : ℝ := max B₀ 0 + 1 with hC₃
  obtain ⟨m₀, J, C₁, Cgr, hGx⟩ :=
    hG q₀ c₀ C₀ vlo vhi hq₀ hq₀₁ hc₀ hvlo (A + 2 * C₃ + KΨ + 2) C₃ (Cf + 3)
  obtain ⟨Cabs, habs⟩ := exists_norm_patternPairing_le q₀ c₀ C₀ vlo vhi B₀ hq₀ hq₀₁ hvlo J
  obtain ⟨KA, hKA, hmelx⟩ := hmel (|A| + |C₁| + |Cabs| + 4) (by positivity)
  refine ⟨m₀, J, C₁, 4 * |Cgr| + 8 * KA, ?_⟩
  filter_upwards [hGx, habs, hmelx,
    eventually_endpoint_bounds q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN c d B₀ hq hq₁ hq₀₁ hvlo
      halo hc J,
    eventually_cutoffPairing_eq q₀ c₀ C₀ vlo vhi κ hq₀ hκ J, eventually_card_dyads_le,
    Real.tendsto_log_atTop.eventually_ge_atTop 2] with x hGx habs hmelx hG1 hG2 hcard hL
  intro ι _ _ P big hadm
  obtain ⟨hdisj, hs₁, hs₂, hb₁, hb₂, hV, hSm, hBg, hBi⟩ := hadm
  obtain ⟨N, Aν, Bν, β, φ, φ', ψ, ψ', U, U', hp₁, hp₂, hp₃, hp₄, hp₅, hp₆, hβ, hpair⟩ :=
    hGx P big hdisj hs₁ hs₂ hb₁ hb₂ hV hSm hBg hBi
  have hadm : GroupAdmissible c₀ C₀ vlo vhi x P big :=
    ⟨hdisj, hs₁, hs₂, hb₁, hb₂, hV, hSm, hBg, hBi⟩
  refine ⟨N, Aν, Bν, β, φ, φ', ψ, ψ', U, U',
    fun ν => ⟨fun g => hp₁ ν g, hp₂ ν, hp₃ ν, hp₄ ν, hp₅ ν, hp₆ ν⟩, hβ, ?_⟩
  intro r a u v Bc G Ψ hin hsl hBc hco hcu
  obtain ⟨α, hαi, hα₁, hαrep, hαt⟩ := hmelx Ψ hcu
  set F := centeredCore x q a u v Bc
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  -- the comparison kernels are bounded by `|β_ν|`
  have hK : ∀ ν p p' l, ‖comparisonKernel (Aν ν) (Bν ν) (β ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν) p p' l‖ ≤
      ‖β ν‖ := fun ν => norm_comparisonKernel_le (hp₄ ν)
  -- `2π L^{C_f} ≤ L^{C_f + 3}` and `2 ≤ L^{2 C₃}`
  have hL3 : 2 * Real.pi ≤ L ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith [Real.pi_le_four, pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL 3]
  have hL2C : 2 ≤ L ^ (2 * C₃) := by
    calc (2 : ℝ) ≤ L ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hL
      _ ≤ L ^ (2 * C₃) := Real.rpow_le_rpow_of_exponent_le hL1 (by
          have := le_max_right B₀ 0; linarith)
  -- the bound at one dyad
  set b₀ : ℝ := |Cgr| * L ^ (-A - 2) + 2 * KA * L ^ (-|A| - 4) with hb₀
  have hdy : ∀ m ∈ dyads x,
      ‖(((2 : ℝ) ^ m : ℝ) : ℂ)⁻¹ *
        ∫ ξ, α ξ *
          (patternPairing P q₀ (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1)
              (-(2 * Real.pi * ξ)) (dyadSource (2 ^ m))
              (sourceEndpoint x q₀ P J F (2 ^ m) ξ) (targetEndpoint q₀ P J G (2 ^ m)) +
            ∑ ν, patternPairing P q₀ (fun h => Aν ν h ∪ Bν ν h)
              (comparisonKernel (Aν ν) (Bν ν) (β ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν))
              (-(2 * Real.pi * ξ)) (dyadSource (2 ^ m))
              (sourceEndpoint x q₀ P J F (2 ^ m) ξ) (targetEndpoint q₀ P J G (2 ^ m)))‖ ≤
        b₀ := by
    intro m hm
    obtain ⟨hX₁, hX₂⟩ := mem_dyads hm
    have hX : (0 : ℝ) < 2 ^ m := by positivity
    have hend := fun ξ => hG1 P big hadm r a u v Bc G hin hsl hBc hco m hm ξ
    -- inside `|ξ| ≤ L^{C_f}`: the transference
    have hin₁ : ∀ ξ : ℝ, |ξ| ≤ L ^ Cf →
        ‖patternPairing P q₀ (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1)
              (-(2 * Real.pi * ξ)) (dyadSource (2 ^ m))
              (sourceEndpoint x q₀ P J F (2 ^ m) ξ) (targetEndpoint q₀ P J G (2 ^ m)) +
            ∑ ν, patternPairing P q₀ (fun h => Aν ν h ∪ Bν ν h)
              (comparisonKernel (Aν ν) (Bν ν) (β ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν))
              (-(2 * Real.pi * ξ)) (dyadSource (2 ^ m))
              (sourceEndpoint x q₀ P J F (2 ^ m) ξ) (targetEndpoint q₀ P J G (2 ^ m))‖ ≤
          |Cgr| * 2 ^ m * L ^ (-A - 2 - KΨ) := by
      intro ξ hξ
      obtain ⟨hf, hnf, hng⟩ := hend ξ
      have hζ : |-(2 * Real.pi * ξ)| ≤ L ^ (Cf + 3) := by
        rw [abs_neg, abs_mul, abs_of_pos Real.two_pi_pos, Real.rpow_add hL0]
        calc 2 * Real.pi * |ξ| ≤ L ^ (3 : ℝ) * L ^ Cf :=
              mul_le_mul hL3 hξ (abs_nonneg _) (by positivity)
          _ = L ^ Cf * L ^ (3 : ℝ) := mul_comm _ _
      have h := hpair (-(2 * Real.pi * ξ)) hζ (2 ^ m) hX₁ hX₂ (dyadSource (2 ^ m))
        (dyadTarget (2 ^ m)) (sourceEndpoint x q₀ P J F (2 ^ m) ξ)
        (targetEndpoint q₀ P J G (2 ^ m)) (fun n hn => mem_dyadSource hn) hf
        (fun n hn => targetEndpoint_eq_zero q₀ P J G _ hn)
        (hnf.trans (by nlinarith)) hng
      refine h.trans ?_
      rw [show -(A + 2 * C₃ + KΨ + 2) + 2 * C₃ = -A - 2 - KΨ by ring]
      gcongr
      exact le_abs_self _
    -- everywhere: the absolute bound
    have hin₂ : ∀ ξ : ℝ,
        ‖patternPairing P q₀ (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1)
              (-(2 * Real.pi * ξ)) (dyadSource (2 ^ m))
              (sourceEndpoint x q₀ P J F (2 ^ m) ξ) (targetEndpoint q₀ P J G (2 ^ m)) +
            ∑ ν, patternPairing P q₀ (fun h => Aν ν h ∪ Bν ν h)
              (comparisonKernel (Aν ν) (Bν ν) (β ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν))
              (-(2 * Real.pi * ξ)) (dyadSource (2 ^ m))
              (sourceEndpoint x q₀ P J F (2 ^ m) ξ) (targetEndpoint q₀ P J G (2 ^ m))‖ ≤
          2 * L ^ |C₁| * 2 ^ m * L ^ |Cabs| := by
      intro ξ
      have hf := (hend ξ).1
      have h₀ := habs P big hadm (fun _ => ∅) (fun _ _ _ => 1) 1 (fun _ _ _ => by simp) G hco
        m hm (-(2 * Real.pi * ξ)) _ hf
      have hν := fun ν => habs P big hadm (fun h => Aν ν h ∪ Bν ν h)
        (comparisonKernel (Aν ν) (Bν ν) (β ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν)) ‖β ν‖ (hK ν) G hco m
        hm (-(2 * Real.pi * ξ)) _ hf
      have hC₁ : L ^ C₁ ≤ L ^ |C₁| := Real.rpow_le_rpow_of_exponent_le hL1 (le_abs_self _)
      have hC₁' : 1 ≤ L ^ |C₁| := Real.one_le_rpow hL1 (abs_nonneg _)
      have hCa : L ^ Cabs ≤ L ^ |Cabs| := Real.rpow_le_rpow_of_exponent_le hL1 (le_abs_self _)
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ 1 * 2 ^ m * L ^ Cabs + ∑ ν, ‖β ν‖ * 2 ^ m * L ^ Cabs :=
            add_le_add h₀ ((norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => hν ν))
        _ = (1 + ∑ ν, ‖β ν‖) * (2 ^ m * L ^ Cabs) := by
            rw [add_mul, Finset.sum_mul]
            congr 1
            · ring
            · exact Finset.sum_congr rfl fun ν _ => by ring
        _ ≤ (L ^ |C₁| + L ^ |C₁|) * (2 ^ m * L ^ |Cabs|) := by
            gcongr
            exact hβ.trans hC₁
        _ = 2 * L ^ |C₁| * 2 ^ m * L ^ |Cabs| := by ring
    have hsplit := norm_integral_mul_le_of_split hαi (by positivity) hin₁ hin₂
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hX.le]
    calc (2 ^ m)⁻¹ * ‖∫ ξ, α ξ * _‖
        ≤ (2 ^ m)⁻¹ * (|Cgr| * 2 ^ m * L ^ (-A - 2 - KΨ) * L ^ KΨ +
            2 * L ^ |C₁| * 2 ^ m * L ^ |Cabs| * (KA * L ^ (-(|A| + |C₁| + |Cabs| + 4)))) := by
          gcongr
          refine hsplit.trans (add_le_add ?_ ?_)
          · exact mul_le_mul_of_nonneg_left hα₁ (by positivity)
          · exact mul_le_mul_of_nonneg_left hαt (by positivity)
      _ = |Cgr| * (L ^ (-A - 2 - KΨ) * L ^ KΨ) +
            2 * KA * (L ^ |C₁| * L ^ |Cabs| * L ^ (-(|A| + |C₁| + |Cabs| + 4))) := by
          field_simp
      _ = b₀ := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0, hb₀]
          congr 3 <;> ring
  rw [hG2 P big hadm N (fun ν h => Aν ν h ∪ Bν ν h)
    (fun ν => comparisonKernel (Aν ν) (Bν ν) (β ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν)) F G Ψ α
    hcu.2.1 hαi hαrep]
  have hb₀0 : 0 ≤ b₀ := by positivity
  have e₁ : L * L * L ^ (-A - 2) = L ^ (-A) := by
    have h := Real.rpow_add hL0 (-A - 2) 2
    rw [show -A - 2 + 2 = -A by ring, Real.rpow_two] at h
    rw [h]
    ring
  have e₂ : L * L * L ^ (-|A| - 4) = L ^ (-|A| - 2) := by
    have h := Real.rpow_add hL0 (-|A| - 4) 2
    rw [show -|A| - 4 + 2 = -|A| - 2 by ring, Real.rpow_two] at h
    rw [h]
    ring
  have hA : L ^ (-|A| - 2) ≤ L ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [le_abs_self A])
  calc _ ≤ L * ∑ m ∈ dyads x, b₀ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hL0.le]
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum hdy)
    _ = L * (dyads x).card * b₀ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ L * (4 * L) * b₀ := by gcongr
    _ = 4 * |Cgr| * (L * L * L ^ (-A - 2)) + 8 * KA * (L * L * L ^ (-|A| - 4)) := by
        rw [hb₀]; ring
    _ ≤ (4 * |Cgr| + 8 * KA) * L ^ (-A) := by
        rw [e₁, e₂]
        nlinarith [abs_nonneg Cgr]

end Erdos408.TwoSided
