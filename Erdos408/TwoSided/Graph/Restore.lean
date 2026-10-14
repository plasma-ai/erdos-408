import Erdos408.TwoSided.Graph.Insertion
import Erdos408.TwoSided.Graph.Restore.Patterns

/-!
# Stripping the shared labels and restoring the restrictions

S3–S4 of `blueprint/two_sided_correlation.md` §§4.3–4.4 (PD §6.2, (6.14)–(6.16); WD §5.2),
Lemma G5 in its two cases. Write a source list as its shared part `s` (the slots
`Sh_g = {i.castSucc : i ∉ C g}`) and its unshared part. With `D_R = ∏ s` and `n = D_R w`,
the stripping bijection G4 turns `Π^Ψ` into `∑_s ∏ μ(s) Φ(s)`, where (6.14) gives the
damping, the masses and the invariance `F(D_R w) = F(w)`, `G(D_R w') = G(w')` (U8), and
`Ψ(n/(xD))/n = D_R⁻¹ Ψ(w/(x D_C))/w`. When `s` is injective, meets no prime of
`w (w + D_C)` and no free label, `Φ(s)` is the summand of the stripped correlation; the
suppressed restrictions have total mass `O(L) e^{-L^{0.27}}/v₋`. With the clipped core every
summand is bounded pointwise, so there are no divisor moments.

G4 is `Restore.physSum_eq_sum_strip` (`Graph/Restore/Strip.lean`): shared labels
`s ∈ auxLabels P (sharedSlots C)`, `1`-padded in the free slots, and unshared parts
`l ∈ unsharedLists P C`, `1`-padded in the shared `castSucc` slots, merged by `Restore.merge`.
Both cases are the general pattern `(C, K)` case
`Restore.exists_eventually_norm_physSum_sub_stripSum_le` (`Graph/Restore/Eventually.lean`), with
the identifications of `Graph/Restore/Patterns.lean`, a crude U7 (`|F| ≤ L`, `Setup.lean`)
and U8 (`Graph/Restore/Core.lean`).
-/

namespace Erdos408.TwoSided

open Filter

/-- **Lemma G5 (raw pattern).** For every `J` there is `C_r` such that, eventually, for
groups as in (6.1) and all admissible data, the raw cutoff pairing (no free slots, kernel `1`)
is the raw correlation up to `L^{C_r} e^{-L^{0.27}}`. With `C = ∅`, `D_C = 1` and
`t_g = 1`, the clean summand is exactly the summand of `twoSidedSum`, since
`W₁ = markedListWeight P q₀ (unsharedSlots ∅) 1` (one prime per group:
`∑_ℓ 1 = ∏_g ω_g`). The suppressed restrictions (two equal shared labels in a group, or a
shared label dividing `w (w + 1)`) have mass `O(s_P J² + J L) sup μ`. -/
theorem exists_norm_cutoffPairing_raw_sub_le (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ)
    (CN c : ℝ) (d : ℕ) (B₀ κ CΨ : ℝ) (M : ℕ → ℝ) (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀)
    (hq₀₁ : q₀ < 1) (hvlo : 0 < vlo) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5) (hc : 0 < c)
    (hκ : 1 < κ) (J : ℕ) :
    ∃ Cr : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ)
          (G : ℕ → ℝ) (Ψ : ℝ → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v →
          (∀ Q, |Bc Q| ≤ 1) → CoreAdmissible B₀ x P G → CutoffAdmissible κ CΨ M x Ψ →
          ‖cutoffPairing x q₀ P (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1)
                (centeredCore x q a u v Bc) G Ψ -
              (twoSidedSum x q q₀ κ a u v Bc P G Ψ : ℂ)‖ ≤
            Real.log x ^ Cr * Real.exp (-Real.log x ^ (0.27 : ℝ)) := by
  obtain ⟨Cr, hCr⟩ := Restore.exists_eventually_norm_physSum_sub_stripSum_le q₀ c₀ C₀ vlo vhi
    B₀ κ (M 0) hq₀ hq₀₁ hvlo hκ 0 J
  refine ⟨Cr, ?_⟩
  filter_upwards [hCr, eventually_abs_centeredCore_le_log q alo ahi K₀ CN c d hq hq₁
      halo hc, Restore.eventually_centeredCore_mul_prime q c₀ C₀ vlo vhi alo ahi K₀ CN c d hahi
      hc, eventually_ge_atTop κ]
    with x hx hF hFinv hxκ ι _ _ P big hadm r a u v Bc G Ψ hin hsl hBc hco hcu
  have hx0 : 0 < x := lt_of_lt_of_le (by linarith) hxκ
  have hΨ : ∀ y, |Ψ y| ≤ M 0 := fun y => by simpa using hcu.2.2 0 y
  have h := hx P big hadm (fun _ => ∅) (fun g => by simp) (fun _ _ _ => 1) 1
    (fun _ _ _ => by simp) (fun p p' a => Restore.pad_invariant_one p p' a)
    (centeredCore x q a u v Bc) G Ψ (hF r a u v Bc hin hsl hBc)
    (hFinv P big hadm r a u v Bc hin hsl) hco hΨ hcu.2.1
  rw [one_mul] at h
  have hraw : (twoSidedSum x q q₀ κ a u v Bc P G Ψ : ℂ) =
      Restore.stripSum x q₀ P (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1)
        (centeredCore x q a u v Bc) G Ψ :=
    (Restore.stripSum_raw_eq hx0 (by nlinarith) P _ G hcu.2.1).symm
  rw [hraw]
  exact h

/-- **Lemma G5 (comparison patterns).** For every `m₀, J` there is `C_r` such that,
eventually, for groups as in (6.1), all admissible data and every comparison pattern
`(A, B, φ, φ', ψ, ψ')` with coefficient `β`, the cutoff pairing of the pattern is
`β` times its stripped comparison correlation up to `|β| L^{C_r} e^{-L^{0.27}}`. Besides the
restrictions of the raw case, a shared label equal to a free label and the label ban (a free
label equal to an unshared endpoint label) are suppressed; a banned label divides `D_C` and one
endpoint, hence both. These restrictions have mass `O(J (L + m₀ s_P) + m₀ L) sup μ`. -/
theorem exists_norm_cutoffPairing_sub_le (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ)
    (CN c : ℝ) (d : ℕ) (B₀ κ CΨ : ℝ) (M : ℕ → ℝ) (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀)
    (hq₀₁ : q₀ < 1) (hvlo : 0 < vlo) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5) (hc : 0 < c)
    (hκ : 1 < κ) (m₀ J : ℕ) :
    ∃ Cr : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ)
          (G : ℕ → ℝ) (Ψ : ℝ → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v →
          (∀ Q, |Bc Q| ≤ 1) → CoreAdmissible B₀ x P G → CutoffAdmissible κ CΨ M x Ψ →
          ∀ (Aν Bν : ι → Finset (Fin J)) (β : ℂ) (φ φ' ψ ψ' : ℕ → ℂ) (U U' : ℝ),
            ComparisonPattern m₀ big Aν Bν φ φ' ψ ψ' U U' →
            ‖cutoffPairing x q₀ P (fun h => Aν h ∪ Bν h)
                  (comparisonKernel Aν Bν β φ φ' ψ ψ') (centeredCore x q a u v Bc) G Ψ -
                β * strippedComparison x q₀ P Aν Bν φ φ' ψ ψ' (centeredCore x q a u v Bc) G Ψ‖ ≤
              ‖β‖ * Real.log x ^ Cr * Real.exp (-Real.log x ^ (0.27 : ℝ)) := by
  obtain ⟨Cr, hCr⟩ := Restore.exists_eventually_norm_physSum_sub_stripSum_le q₀ c₀ C₀ vlo vhi
    B₀ κ (M 0) hq₀ hq₀₁ hvlo hκ m₀ J
  refine ⟨Cr, ?_⟩
  filter_upwards [hCr, eventually_abs_centeredCore_le_log q alo ahi K₀ CN c d hq hq₁
      halo hc, Restore.eventually_centeredCore_mul_prime q c₀ C₀ vlo vhi alo ahi K₀ CN c d hahi
      hc]
    with x hx hF hFinv ι _ _ P big hadm r a u v Bc G Ψ hin hsl hBc hco hcu Aν Bν β φ φ' ψ ψ'
      U U' hpat
  have hΨ : ∀ y, |Ψ y| ≤ M 0 := fun y => by simpa using hcu.2.2 0 y
  have h := hx P big hadm (fun h => Aν h ∪ Bν h) (fun g => (hpat.1 g).2)
    (comparisonKernel Aν Bν β φ φ' ψ ψ') ‖β‖ (norm_comparisonKernel_le hpat.2.2.2.1)
    (fun p p' a => Restore.pad_invariant_comparison Aν Bν β φ φ' ψ ψ' p p' a)
    (centeredCore x q a u v Bc) G Ψ (hF r a u v Bc hin hsl hBc)
    (hFinv P big hadm r a u v Bc hin hsl) hco hΨ hcu.2.1
  rw [← Restore.stripSum_comparison_eq]
  exact h

end Erdos408.TwoSided
