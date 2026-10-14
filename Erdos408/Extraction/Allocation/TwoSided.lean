module

public import Erdos408.Analytic.IntegerKernel
public import Erdos408.Analytic.PrimeTwist
public import Erdos408.Extraction.Allocation.Cutoff
public import Erdos408.Extraction.Allocation.Endpoint

/-!
# Applying the two-sided correlation

`TwoSidedCorrelation` holds for large `x` under its two analytic premises.
`eventually_primeTwistBound` and `eventually_integerKernelBound` supply them
at the precision `A'` and modulus exponent `C_m` it asks for, with the
larger of their two constants `κ'` (both premises are monotone in `κ'`).

Each term of the signed expansion is then a two-sided correlation with:
the active groups `S = P ∪ Q`, split into small and big; the bands of an
inert monomial, enumerated by `Fin |S|`; the given slots and coefficient;
the clipped core `min(G_j, L^{B₀})`, invariant under all candidate primes;
and the cutoff `Ψ(y) = y Φ(y)`, which turns `Ψ(w/x)/w` into `Φ(w/x)/x`.
-/

@[expose] public section

namespace Erdos408

open Finset Filter Real

noncomputable section

/-- The conclusion of `TwoSidedCorrelation` for large `x`, after its
premises. -/
def TwoSidedBody (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ) (d : ℕ) (B₀ κ CΨ : ℝ)
    (M : ℕ → ℝ) (A Cstar x : ℝ) : Prop :=
  ∀ (Sg Bg : Finset (Finset ℕ)) (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ)
    (Bc : (Fin d → ℕ) → ℝ) (G : ℕ → ℝ) (Ψ : ℝ → ℝ),
    Disjoint Sg Bg → (Sg ∪ Bg : Set (Finset ℕ)).PairwiseDisjoint id →
    c₀ * Real.log (Real.log x) ≤ Sg.card → (Sg.card : ℝ) ≤ C₀ * Real.log (Real.log x) →
    c₀ * Real.log (Real.log x) ≤ Bg.card → (Bg.card : ℝ) ≤ C₀ * Real.log (Real.log x) →
    (∀ P ∈ Sg ∪ Bg, vlo ≤ harmonicMass P ∧ harmonicMass P ≤ vhi) →
    (∀ P ∈ Sg, P ⊆ primesIcc (Real.exp (Real.log x ^ (0.27 : ℝ)))
      (Real.exp (Real.log x ^ (0.36 : ℝ)))) →
    (∀ P ∈ Bg, P ⊆ primesIcc (Real.exp (Real.log x ^ (0.39 : ℝ)))
      (Real.exp (Real.log x ^ (0.46 : ℝ)))) →
    (∀ P ∈ Bg, ∃ y z : ℝ, P = primesIcc y z) →
    (r : ℝ) ≤ K₀ + CN * Real.log (Real.log (Real.log x)) →
    (∀ i, alo ≤ a i ∧ a i ≤ ahi) →
    (∀ i j, i ≠ j → Disjoint (band x (a i)) (band x (a j))) →
    (∀ i, c / Real.log (Real.log x) ^ 20 ≤ u i) →
    ∑ i, v i ≤ 1 - c / Real.log (Real.log x) ^ 20 →
    (∀ Q, |Bc Q| ≤ 1) →
    (∀ n, G n = G (stripPrimes ((Sg ∪ Bg).biUnion id) n)) →
    (∀ n, 0 ≤ G n ∧ G n ≤ Real.log x ^ B₀) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → (∀ y, Ψ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) →
    (∀ (k : ℕ) (y : ℝ), |iteratedDeriv k Ψ y| ≤ M k * Real.log (Real.log x) ^ (CΨ * k)) →
    |∑ w ∈ Finset.Icc 1 ⌊κ * x⌋₊,
        Ψ (w / x) / w *
          (markedWeight Finset.univ q (fun i => band x (a i)) w *
            ((∑ Q ∈ slotTuples x u v with ∏ i, Q i ∣ w, Bc (Fin.init Q)) -
              ∑ Q ∈ slotTuples x u v, Bc (Fin.init Q) / ∏ i, (Q i : ℝ))) *
          G (w + 1) * markedWeight (Sg ∪ Bg) q₀ id w *
          markedWeight (Sg ∪ Bg) q₀ id (w + 1)| ≤
      Cstar * Real.log x ^ (-A)

/-- `PrimeTwistBound` is monotone in its constant when `L ≥ 0`. -/
lemma PrimeTwistBound.mono {x A E Cm κ κ' : ℝ} (h : PrimeTwistBound x A E Cm κ) (hκ : κ ≤ κ')
    (hx : 0 ≤ Real.log x) : PrimeTwistBound x A E Cm κ' :=
  fun H lo hi h1 h2 h3 h4 k hk1 hk2 χ u hu1 hu2 =>
    (h H lo hi h1 h2 h3 h4 k hk1 hk2 χ u hu1 hu2).trans
      (mul_le_mul_of_nonneg_right hκ (rpow_nonneg hx _))

/-- `IntegerKernelBound` is monotone in its constant. -/
lemma IntegerKernelBound.mono {x Cm κ κ' : ℝ} (h : IntegerKernelBound x Cm κ) (hκ : κ ≤ κ') :
    IntegerKernelBound x Cm κ' :=
  fun H lo hi h1 h2 h3 h4 k a hk1 hk2 u hu1 hu2 =>
    (h H lo hi h1 h2 h3 h4 k a hk1 hk2 u hu1 hu2).trans
      (mul_le_mul_of_nonneg_right hκ (by positivity))

/-- `TwoSidedCorrelation` with its premises discharged by
`eventually_primeTwistBound` and `eventually_integerKernelBound`. -/
theorem exists_twoSidedBody (h₂ : TwoSidedCorrelation) (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ)
    (K₀ : ℕ) (CN c : ℝ) (d : ℕ) (B₀ κ CΨ : ℝ) (M : ℕ → ℝ) (A : ℝ) (hq : 0 < q) (hq₁ : q < 1)
    (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1) (hc₀ : 0 < c₀) (hvlo : 0 < vlo) (halo : 1 / 10 < alo)
    (hal : alo ≤ ahi) (hahi : ahi < 1 / 5) (hc : 0 < c) (hd : d ≤ 2) (hκ : 1 < κ) :
    ∃ Cstar : ℝ, ∀ᶠ x : ℝ in atTop,
      TwoSidedBody q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN c d B₀ κ CΨ M A Cstar x := by
  obtain ⟨A', Cm, h⟩ := h₂ q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN c d B₀ κ CΨ M A hq hq₁ hq₀ hq₀₁
    hc₀ hvlo halo hal hahi hc hd hκ
  obtain ⟨E, κ₁, hP⟩ := eventually_primeTwistBound A' Cm
  obtain ⟨κ₂, hI⟩ := eventually_integerKernelBound Cm
  obtain ⟨Cstar, hC⟩ := h E (max κ₁ κ₂)
  refine ⟨Cstar, ?_⟩
  filter_upwards [hC, hP, hI, eventually_le_log 0] with x hC hP hI hx
  exact hC (hP.mono (le_max_left _ _) hx) (hI.mono (le_max_right _ _))

/-! ### The terms of the signed expansion -/

/-- The bands of the monomial `S`, enumerated by `Fin |S|`. -/
def monomialExponents (K : ℕ) (x : ℝ) (S : Finset (ℕ × ℕ)) (i : Fin S.card) : ℝ :=
  inertExponent K x (S.equivFin.symm i).1.1 (S.equivFin.symm i).1.2

/-- One term of the signed expansion: the two-sided correlation sum of the
active set `Act`, the bands of the monomial `S` and the core `G`. -/
def twoSidedSum (q : ℝ) (K : ℕ) (x κ : ℝ) (Φ : ℝ → ℝ) (S : Finset (ℕ × ℕ)) {k : ℕ}
    (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) (G : ℕ → ℝ) (Act : Finset (Finset ℕ)) : ℝ :=
  ∑ w ∈ Finset.Icc 1 ⌊κ * x⌋₊,
    (fun y => y * Φ y) (w / x) / w *
      (markedWeight Finset.univ q (fun i => band x (monomialExponents K x S i)) w *
        ((∑ Q ∈ slotTuples x u v with ∏ i, Q i ∣ w, B (Fin.init Q)) -
          ∑ Q ∈ slotTuples x u v, B (Fin.init Q) / ∏ i, (Q i : ℝ))) *
      G (w + 1) * markedWeight Act (1 / 2) id w * markedWeight Act (1 / 2) id (w + 1)

/-- The facts about the inert bands at a large `x` (`eventually_inertBands`). -/
def BandFacts (K : ℕ) (CN x : ℝ) : Prop :=
  (∀ p ∈ range K ×ˢ range (inertPerCluster K CN x),
      11 / 100 ≤ inertExponent K x p.1 p.2 ∧ inertExponent K x p.1 p.2 ≤ 39 / 200) ∧
    (∀ p ∈ range K ×ˢ range (inertPerCluster K CN x),
      ∀ p' ∈ range K ×ˢ range (inertPerCluster K CN x), p ≠ p' →
        Disjoint (band x (inertExponent K x p.1 p.2)) (band x (inertExponent K x p'.1 p'.2))) ∧
    ((K * inertPerCluster K CN x : ℕ) : ℝ) ≤ K + max CN 0 * logLogLog x

/-- Each term of the signed expansion is a two-sided correlation, so it is
at most `C* L^{-A}`. -/
theorem abs_twoSidedSum_le {q c₂ c B₀ κ CΦ A Cstar x γ CN : ℝ} {K d j : ℕ} {M : ℕ → ℝ}
    (hbody : TwoSidedBody q (1 / 2) c₂ 1 (1 / 2) 3 (11 / 100) (39 / 200) K (max CN 0) c d B₀ κ
      (max CΦ 0) (fun r => κ * M r + r * M (r - 1)) A Cstar x)
    (hgroups : GroupFacts x) (hbands : BandFacts K CN x) (hx : 1 < x) (hT : 1 ≤ logLog x)
    (hγ : 1 ≤ x ^ γ) (hj : 1 ≤ j) (hκ : 1 < κ) {u v : Fin (d + 1) → ℝ}
    (hadm : AdmissibleSlots c x u v) {B : (Fin d → ℕ) → ℝ} (hB : ∀ Q, 0 ≤ B Q ∧ B Q ≤ 1)
    {Φ : ℝ → ℝ} (hΦ : IsCutoff κ CΦ M x Φ) {Act : Finset (Finset ℕ)}
    (hAct : Act ⊆ candidateGroups x) (hS₁ : c₂ * logLog x ≤ (Act ∩ smallGroups x).card)
    (hS₂ : c₂ * logLog x ≤ (Act ∩ bigGroups x).card) {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ range K ×ˢ range (inertPerCluster K CN x)) :
    |twoSidedSum q K x κ Φ S u v B (fun n => min (proxyCore x γ j n) (Real.log x ^ B₀)) Act| ≤
      Cstar * Real.log x ^ (-A) := by
  obtain ⟨hmass, hdisj, hsmall, hbig, hcs, hcb, -⟩ := hgroups
  obtain ⟨hexp, hbdisj, hcount⟩ := hbands
  have hunion : Act ∩ smallGroups x ∪ Act ∩ bigGroups x = Act := by
    rw [← inter_union_distrib_left]
    exact inter_eq_left.2 hAct
  have hsub : Act ∩ smallGroups x ∪ Act ∩ bigGroups x ⊆ candidateGroups x := by
    rw [hunion]
    exact hAct
  have hL : 0 < Real.log x := Real.log_pos hx
  have hL1 : 1 ≤ Real.log x := by
    have := Real.log_le_sub_one_of_pos hL
    rw [logLog] at hT
    linarith
  have hcut := isCutoff_mul_id hκ hT hΦ
  have h := hbody (Act ∩ smallGroups x) (Act ∩ bigGroups x) S.card (monomialExponents K x S) u v
    B (fun n => min (proxyCore x γ j n) (Real.log x ^ B₀)) (fun y => y * Φ y)
    (disjoint_of_subset_left inter_subset_right (disjoint_of_subset_right inter_subset_right hdisj))
    (by
      exact (pairwiseDisjoint_candidateGroups hL1).subset
        (by rw [← coe_union]; exact coe_subset.2 hsub))
    (by simpa [logLog] using hS₁)
    (by
      have := (card_le_card (inter_subset_right (s₁ := Act) (s₂ := smallGroups x)))
      have : ((Act ∩ smallGroups x).card : ℝ) ≤ (smallGroups x).card := by exact_mod_cast this
      simp only [one_mul]
      exact this.trans hcs)
    (by simpa [logLog] using hS₂)
    (by
      have := (card_le_card (inter_subset_right (s₁ := Act) (s₂ := bigGroups x)))
      have : ((Act ∩ bigGroups x).card : ℝ) ≤ (bigGroups x).card := by exact_mod_cast this
      simp only [one_mul]
      exact this.trans hcb)
    (fun P hP => hmass P (hsub hP))
    (fun P hP => hsmall P (mem_inter.1 hP).2)
    (fun P hP => hbig P (mem_inter.1 hP).2)
    (fun P hP => exists_eq_primesIcc_of_mem_bigGroups (mem_inter.1 hP).2)
    (by
      have h1 : (S.card : ℝ) ≤ ((K * inertPerCluster K CN x : ℕ) : ℝ) := by
        have := card_le_card hS
        rw [card_product, card_range, card_range] at this
        exact_mod_cast this
      exact h1.trans hcount)
    (fun i => hexp _ (hS (S.equivFin.symm i).2))
    (fun i i' hii' => hbdisj _ (hS (S.equivFin.symm i).2) _ (hS (S.equivFin.symm i').2)
      fun h => hii' (S.equivFin.symm.injective (Subtype.ext h)))
    hadm.1 hadm.2 (fun Q => abs_le.2 ⟨by linarith [(hB Q).1], (hB Q).2⟩)
    (fun n => by
      rw [proxyCore_stripPrimes]
      intro p hp
      obtain ⟨g, hg, hpg⟩ := mem_biUnion.1 hp
      exact mem_biUnion.2 ⟨g, hsub hg, hpg⟩)
    (fun n => ⟨le_min (proxyCore_nonneg hj hγ n) (rpow_nonneg hL.le _), min_le_right _ _⟩)
    hcut.1 hcut.2.1 hcut.2.2
  rw [hunion] at h
  exact h

end

end Erdos408
