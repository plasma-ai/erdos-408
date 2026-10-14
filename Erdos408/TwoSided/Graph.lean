import Erdos408.TwoSided.Graph.Restore

/-!
# The graph reduction

Interface G of `blueprint/two_sided_correlation.md` §3.2 (PD §§6.1–6.2, S0–S4): the raw
correlation plus the signed stripped comparison correlations of `GraphTransference`'s family
is `O(L^{-A})`. It combines

* Lemma G3 (`eventually_norm_cutoffPairing_family_le`, in `Graph/Insertion.lean`): the raw
  plus comparison cutoff pairings are `O(L^{-A})`, by the Mellin insertion, the dyads and the
  transference;
* Lemma G5 (`Graph/Restore.lean`): each cutoff pairing is its stripped correlation (`β` times
  it, for a comparison pattern) up to `L^{C_r} e^{-L^{0.27}}` (times `|β|`).

With `∑ |β| ≤ L^{C₁}`, the stripping errors are below `2 L^{-A}`.
-/

namespace Erdos408.TwoSided

open Filter

/-- **Interface G.** For the fixed data and every `A` there are `m₀, J, C₁, C_G` such that,
eventually, for groups as in (6.1) there is a family of comparison patterns with
`∑ |β| ≤ L^{C₁}` for which, for all admissible data,
`|S_raw + ∑_ν β_ν S_ν| ≤ C_G L^{-A}`. -/
theorem eventually_raw_add_comparison_le (hG : GraphTransference)
    (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ) (d : ℕ) (B₀ κ CΨ : ℝ)
    (M : ℕ → ℝ) (A : ℝ) (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1)
    (hc₀ : 0 < c₀) (hvlo : 0 < vlo) (halo : 1 / 10 < alo) (_hal : alo ≤ ahi)
    (hahi : ahi < 1 / 5) (hc : 0 < c) (hκ : 1 < κ) :
    ∃ (m₀ J : ℕ) (C₁ CG : ℝ), ∀ᶠ x : ℝ in atTop,
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
            ‖(twoSidedSum x q q₀ κ a u v Bc P G Ψ : ℂ) +
                ∑ ν, β ν * strippedComparison x q₀ P (Aν ν) (Bν ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν)
                  (centeredCore x q a u v Bc) G Ψ‖ ≤
              CG * Real.log x ^ (-A) := by
  obtain ⟨m₀, J, C₁, Cres, hres⟩ := eventually_norm_cutoffPairing_family_le hG q q₀ c₀ C₀ vlo
    vhi alo ahi K₀ CN c d B₀ κ CΨ M A hq hq₁ hq₀ hq₀₁ hc₀ hvlo halo hc hκ
  obtain ⟨Cr, hraw⟩ := exists_norm_cutoffPairing_raw_sub_le q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN
    c d B₀ κ CΨ M hq hq₁ hq₀ hq₀₁ hvlo halo hahi hc hκ J
  obtain ⟨Cr', hcmp⟩ := exists_norm_cutoffPairing_sub_le q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN c d
    B₀ κ CΨ M hq hq₁ hq₀ hq₀₁ hvlo halo hahi hc hκ m₀ J
  refine ⟨m₀, J, C₁, Cres + 2, ?_⟩
  filter_upwards [hres, hraw, hcmp,
    OneSided.eventually_mul_rpow_mul_exp_le (by norm_num : (0 : ℝ) < 0.27) 1 Cr A,
    OneSided.eventually_mul_rpow_mul_exp_le (by norm_num : (0 : ℝ) < 0.27) 1 (C₁ + Cr') A,
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with x hres hraw hcmp he₁ he₂ hL
  intro ι _ _ P big hadm
  obtain ⟨N, Aν, Bν, β, φ, φ', ψ, ψ', U, U', hpat, hβ, hbd⟩ := hres P big hadm
  refine ⟨N, Aν, Bν, β, φ, φ', ψ, ψ', U, U', hpat, hβ, ?_⟩
  intro r a u v Bc G Ψ hin hsl hBc hco hcu
  set F := centeredCore x q a u v Bc
  set L := Real.log x
  set e := Real.exp (-L ^ (0.27 : ℝ))
  have h₀ := hbd r a u v Bc G Ψ hin hsl hBc hco hcu
  have h₁ := hraw P big hadm r a u v Bc G Ψ hin hsl hBc hco hcu
  have h₂ := fun ν => hcmp P big hadm r a u v Bc G Ψ hin hsl hBc hco hcu (Aν ν) (Bν ν) (β ν)
    (φ ν) (φ' ν) (ψ ν) (ψ' ν) (U ν) (U' ν) (hpat ν)
  rw [one_mul] at he₁ he₂
  -- `S_raw + ∑ β S_ν = (Π_raw + ∑ Π_ν) - (Π_raw - S_raw) - ∑ (Π_ν - β S_ν)`
  have hid : (twoSidedSum x q q₀ κ a u v Bc P G Ψ : ℂ) +
        ∑ ν, β ν * strippedComparison x q₀ P (Aν ν) (Bν ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν) F G Ψ =
      (cutoffPairing x q₀ P (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1) F G Ψ +
          ∑ ν, cutoffPairing x q₀ P (fun h => Aν ν h ∪ Bν ν h)
            (comparisonKernel (Aν ν) (Bν ν) (β ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν)) F G Ψ) -
        (cutoffPairing x q₀ P (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1) F G Ψ -
          (twoSidedSum x q q₀ κ a u v Bc P G Ψ : ℂ)) -
        ∑ ν, (cutoffPairing x q₀ P (fun h => Aν ν h ∪ Bν ν h)
            (comparisonKernel (Aν ν) (Bν ν) (β ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν)) F G Ψ -
          β ν * strippedComparison x q₀ P (Aν ν) (Bν ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν) F G Ψ) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hid]
  calc _ ≤ ‖cutoffPairing x q₀ P (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1) F G Ψ +
            ∑ ν, cutoffPairing x q₀ P (fun h => Aν ν h ∪ Bν ν h)
              (comparisonKernel (Aν ν) (Bν ν) (β ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν)) F G Ψ‖ +
          ‖cutoffPairing x q₀ P (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1) F G Ψ -
            (twoSidedSum x q q₀ κ a u v Bc P G Ψ : ℂ)‖ +
          ∑ ν, ‖cutoffPairing x q₀ P (fun h => Aν ν h ∪ Bν ν h)
              (comparisonKernel (Aν ν) (Bν ν) (β ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν)) F G Ψ -
            β ν * strippedComparison x q₀ P (Aν ν) (Bν ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν) F G Ψ‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sum_le _ _))
    _ ≤ Cres * L ^ (-A) + L ^ Cr * e + ∑ ν, ‖β ν‖ * L ^ Cr' * e :=
        add_le_add (add_le_add h₀ h₁) (Finset.sum_le_sum fun ν _ => h₂ ν)
    _ = Cres * L ^ (-A) + L ^ Cr * e + (∑ ν, ‖β ν‖) * (L ^ Cr' * e) := by
        rw [Finset.sum_mul]
        exact congrArg _ (Finset.sum_congr rfl fun ν _ => by ring)
    _ ≤ Cres * L ^ (-A) + L ^ (-A) + L ^ C₁ * (L ^ Cr' * e) := by
        gcongr
    _ = Cres * L ^ (-A) + L ^ (-A) + L ^ (C₁ + Cr') * e := by
        rw [Real.rpow_add hL]
        ring
    _ ≤ Cres * L ^ (-A) + L ^ (-A) + L ^ (-A) := by gcongr
    _ = (Cres + 2) * L ^ (-A) := by ring

end Erdos408.TwoSided
