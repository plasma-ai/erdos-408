import Mathlib
import Erdos821.Prelim.SieveCalculus
import Erdos821.Prelim.BlockSieve

/-!
# Sieve expectations: independent-trial averaging for one block (`lem:sieve`)

For a block `B` with densities `g`, independent inclusion with `Prob(T)` gives
`S - a` between `0` and `e` from the pointwise `0 ≤ U - I ≤ E`
(`Prelim.SieveCalculus.blockUpper_*`, even truncation), and `e ≤ tailTerm` from
`esymm_le`. No alternating-series analysis: averaging preserves pointwise
bounds. Product factorization across disjoint blocks follows in the bridge.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
namespace Erdos821
namespace PrelimLemmas

/-- Independent-trial weight of `T ⊆ B`: each `p` included with prob `g p`. -/
noncomputable def trialProb (B : Finset ℕ) (g : ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  (∏ p ∈ T, g p) * (∏ p ∈ B \ T, (1 - g p))

theorem trialProb_nonneg (B : Finset ℕ) (g : ℕ → ℝ)
    (hg0 : ∀ p ∈ B, 0 ≤ g p) (hg1 : ∀ p ∈ B, g p ≤ 1)
    (T : Finset ℕ) (_hT : T ⊆ B) : 0 ≤ trialProb B g T := by
  unfold trialProb
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun p hp => hg0 p (by
      have := _hT hp
      exact this))
  · apply Finset.prod_nonneg
    intro p hp
    have hpmem : p ∈ B := (Finset.mem_sdiff.mp hp).1
    have := hg1 p hpmem
    linarith

/-- Weights sum to one: `∑_{T⊆B} Prob = ∏ (g + (1-g)) = 1`. -/
theorem trialProb_sum_one (B : Finset ℕ) (g : ℕ → ℝ) :
    ∑ T ∈ B.powerset, trialProb B g T = 1 := by
  induction B using Finset.induction with
  | empty =>
    simp [trialProb]
  | @insert q B₀ has ih =>
    have hps : (insert q B₀).powerset
        = B₀.powerset ∪ (B₀.powerset.image (insert q)) :=
      Finset.powerset_insert B₀ q
    have hdisj : Disjoint B₀.powerset (B₀.powerset.image (insert q)) := by
      rw [Finset.disjoint_left]
      intro T hT1 hT2
      obtain ⟨U, _, hUeq⟩ := Finset.mem_image.mp hT2
      have hqT : q ∈ T := hUeq ▸ Finset.mem_insert_self q U
      have hqB : q ∉ T := by
        have hTsub : T ⊆ B₀ := Finset.mem_powerset.mp hT1
        exact fun h => has (hTsub h)
      exact hqB hqT
    rw [hps, Finset.sum_union hdisj]
    have h1 : ∑ T ∈ B₀.powerset, trialProb (insert q B₀) g T
        = (1 - g q) * ∑ T ∈ B₀.powerset, trialProb B₀ g T := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      have hTsub : T ⊆ B₀ := Finset.mem_powerset.mp hT
      have hqT : q ∉ T := fun h => has (hTsub h)
      have hsdiff : (insert q B₀) \ T = insert q (B₀ \ T) := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hpm, hpT⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hpm, hpT⟩
        · rintro (rfl | ⟨hpm, hpT⟩)
          · exact ⟨Or.inl rfl, hqT⟩
          · exact ⟨Or.inr hpm, hpT⟩
      unfold trialProb
      rw [hsdiff, Finset.prod_insert (by
        intro hcon
        have := (Finset.mem_sdiff.mp hcon).1
        exact has this)]
      ring
    have hinj : Set.InjOn (insert q : Finset ℕ → Finset ℕ) (↑B₀.powerset : Set (Finset ℕ)) := by
      intro U hU V hV heq
      have hqU : q ∉ U := fun h => has ((Finset.mem_powerset.mp
        (Finset.mem_coe.mp hU)) h)
      have hqV : q ∉ V := fun h => has ((Finset.mem_powerset.mp
        (Finset.mem_coe.mp hV)) h)
      calc U = (insert q U).erase q := (Finset.erase_insert hqU).symm
        _ = (insert q V).erase q := by rw [heq]
        _ = V := Finset.erase_insert hqV
    have h2 : ∑ T ∈ B₀.powerset.image (insert q), trialProb (insert q B₀) g T
        = g q * ∑ U ∈ B₀.powerset, trialProb B₀ g U := by
      rw [Finset.sum_image hinj, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      have hUsub : U ⊆ B₀ := Finset.mem_powerset.mp hU
      have hqU : q ∉ U := fun h => has (hUsub h)
      have hsdiff : (insert q B₀) \ (insert q U) = B₀ \ U := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hpm, hpT⟩
          · exfalso
            exact hpT (Or.inl rfl)
          · simp only [not_or] at hpT
            exact ⟨hpm, hpT.2⟩
        · rintro ⟨hpm, hpU⟩
          have hpq : p ≠ q := fun heq => has (heq ▸ hpm)
          exact ⟨Or.inr hpm, by simp [hpq, hpU]⟩
      unfold trialProb
      rw [Finset.prod_insert hqU, hsdiff]
      ring
    rw [h1, h2, ih]
    ring

/-- Disjointness of `u` from the remainder `B \\ u`. -/
theorem disjoint_sdiff_rem (B u : Finset ℕ) (hu : u ⊆ B) :
    Disjoint u (B \ u) := by
  rw [Finset.disjoint_left]
  intro p hpu hpB
  have hpm := Finset.mem_sdiff.mp hpB
  exact hpm.2 hpu

/-- Superset averaging: `∑_{T⊇u} Prob(T) = ∏_{u} g`. -/
theorem trialProb_superset (B : Finset ℕ) (g : ℕ → ℝ)
    {u : Finset ℕ} (hu : u ⊆ B) :
    ∑ T ∈ B.powerset.filter (fun T => u ⊆ T), trialProb B g T
      = ∏ p ∈ u, g p := by
  have hdisj : Disjoint u (B \ u) := disjoint_sdiff_rem B u hu
  have hinj : Set.InjOn (fun V : Finset ℕ => u ∪ V)
      (↑(B \ u).powerset : Set (Finset ℕ)) := by
    intro V hV W hW heq
    have hVsub : V ⊆ B \ u :=
      Finset.mem_powerset.mp (Finset.mem_coe.mp hV)
    have hWsub : W ⊆ B \ u :=
      Finset.mem_powerset.mp (Finset.mem_coe.mp hW)
    have hVeq : (u ∪ V) \ u = V := by
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hpu | hpV, hpu2⟩
        · exact absurd hpu hpu2
        · exact hpV
      · intro hpV
        have hpu : p ∉ u := by
          intro hpu
          have hVB : p ∈ B \ u := hVsub hpV
          exact (Finset.disjoint_left.mp hdisj hpu) hVB
        exact ⟨Or.inr hpV, hpu⟩
    have hWeq : (u ∪ W) \ u = W := by
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hpu | hpW, hpu2⟩
        · exact absurd hpu hpu2
        · exact hpW
      · intro hpW
        have hpu : p ∉ u := by
          intro hpu
          have hWB : p ∈ B \ u := hWsub hpW
          exact (Finset.disjoint_left.mp hdisj hpu) hWB
        exact ⟨Or.inr hpW, hpu⟩
    have heq' : u ∪ V = u ∪ W := heq
    calc V = (u ∪ V) \ u := hVeq.symm
      _ = (u ∪ W) \ u := by rw [heq']
      _ = W := hWeq
  have himg : (B \ u).powerset.image (fun V => u ∪ V)
      = B.powerset.filter (fun T => u ⊆ T) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨V, hV, rfl⟩
      have hVsubB : V ⊆ B := Finset.Subset.trans hV Finset.sdiff_subset
      exact ⟨Finset.union_subset hu hVsubB, Finset.subset_union_left⟩
    · rintro ⟨hTsub, huT⟩
      refine ⟨T \ u, ?_, ?_⟩
      · intro p hp
        have hpm := Finset.mem_sdiff.mp hp
        exact Finset.mem_sdiff.mpr ⟨hTsub hpm.1, hpm.2⟩
      · ext p
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (hpu | ⟨hpm, -⟩)
          · exact huT hpu
          · exact hpm
        · intro hpm
          by_cases hpu : p ∈ u
          · exact Or.inl hpu
          · exact Or.inr ⟨hpm, hpu⟩
  have hsum : ∑ T ∈ B.powerset.filter (fun T => u ⊆ T), trialProb B g T
      = ∑ V ∈ (B \ u).powerset, trialProb B g (u ∪ V) := by
    rw [← himg, Finset.sum_image hinj]
  rw [hsum]
  have hprob : ∀ V ∈ (B \ u).powerset, trialProb B g (u ∪ V)
      = (∏ p ∈ u, g p) * trialProb (B \ u) g V := by
    intro V hV
    have hVsub : V ⊆ B \ u := Finset.mem_powerset.mp hV
    have hVsubB : V ⊆ B := Finset.Subset.trans hVsub Finset.sdiff_subset
    have hdisjUV : Disjoint u V := by
      rw [Finset.disjoint_left]
      intro p hpu hpV
      exact (Finset.disjoint_left.mp hdisj hpu) (hVsub hpV)
    have hprod : ∏ p ∈ u ∪ V, g p = (∏ p ∈ u, g p) * ∏ p ∈ V, g p :=
      Finset.prod_union hdisjUV
    have hsdiff : B \ (u ∪ V) = (B \ u) \ V := by
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
      tauto
    unfold trialProb
    rw [hprod, hsdiff]
    ring
  calc ∑ V ∈ (B \ u).powerset, trialProb B g (u ∪ V)
      = ∑ V ∈ (B \ u).powerset, (∏ p ∈ u, g p) * trialProb (B \ u) g V := by
        apply Finset.sum_congr rfl
        intro V hV
        exact hprob V hV
    _ = (∏ p ∈ u, g p) * ∑ V ∈ (B \ u).powerset, trialProb (B \ u) g V := by
        rw [Finset.mul_sum]
    _ = ∏ p ∈ u, g p := by
        rw [trialProb_sum_one, mul_one]

/-- One-block values from `Prelim.SieveCalculus.blockUpper` (as reals). -/
noncomputable def blockUval (h : ℕ) (T : Finset ℕ) : ℝ :=
  ((Prelim.SieveCalculus.blockUpper h T.card : ℤ) : ℝ)

/-- One-block avoidance indicator via cardinality (matches `blockUpper`). -/
noncomputable def blockIval (T : Finset ℕ) : ℝ :=
  if T.card = 0 then 1 else 0

/-- One-block error value `C(|T|, h+1)`. -/
noncomputable def blockEval (h : ℕ) (T : Finset ℕ) : ℝ :=
  ((T.card.choose (h + 1) : ℕ) : ℝ)

/-- Block expectations `S`, `A`, `E` under independent trials. -/
noncomputable def blockExpS (B : Finset ℕ) (g : ℕ → ℝ) (h : ℕ) : ℝ :=
  ∑ T ∈ B.powerset, trialProb B g T * blockUval h T

noncomputable def blockExpA (B : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  ∏ p ∈ B, (1 - g p)

noncomputable def blockExpE (B : Finset ℕ) (g : ℕ → ℝ) (h : ℕ) : ℝ :=
  ∑ T ∈ B.powerset, trialProb B g T * blockEval h T

/-- `A` equals the averaged indicator (only `∅` contributes). -/
theorem blockExpA_eq_sum (B : Finset ℕ) (g : ℕ → ℝ) :
    ∑ T ∈ B.powerset, trialProb B g T * blockIval T = blockExpA B g := by
  have hmem : (∅ : Finset ℕ) ∈ B.powerset := Finset.empty_mem_powerset B
  have hsingle : ∀ T ∈ B.powerset, T ≠ ∅ →
      trialProb B g T * blockIval T = 0 := by
    intro T _ hne
    have hcard : T.card ≠ 0 := fun h0 =>
      hne (Finset.card_eq_zero.mp h0)
    simp [blockIval, hcard]
  rw [Finset.sum_eq_single_of_mem ∅ hmem hsingle]
  simp [blockIval, trialProb, blockExpA]

/-- Averaged bounds `0 ≤ S - A ≤ E` for even truncation (pointwise
`0 ≤ U - I ≤ E` from `SieveCalculus`, preserved by `Prob ≥ 0`). -/
theorem blockExp_bounds (B : Finset ℕ) (g : ℕ → ℝ) (h : ℕ)
    (he : Even h)
    (hg0 : ∀ p ∈ B, 0 ≤ g p) (hg1 : ∀ p ∈ B, g p ≤ 1) :
    0 ≤ blockExpS B g h - blockExpA B g ∧
      blockExpS B g h - blockExpA B g ≤ blockExpE B g h := by
  have hA := blockExpA_eq_sum B g
  have hSsub : blockExpS B g h
      - (∑ T ∈ B.powerset, trialProb B g T * blockIval T)
      = ∑ T ∈ B.powerset,
        trialProb B g T * (blockUval h T - blockIval T) := by
    unfold blockExpS
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [hA] at hSsub
  -- pointwise `0 ≤ U - I ≤ E`
  have hpt0 : ∀ T ∈ B.powerset, 0 ≤ blockUval h T - blockIval T := by
    intro T _
    unfold blockUval blockIval
    have hle := Prelim.SieveCalculus.blockUpper_ge_indicator h T.card he
    have hcast : (0 : ℝ) ≤ ((Prelim.SieveCalculus.blockUpper h T.card : ℤ) : ℝ)
        - (if T.card = 0 then (1 : ℝ) else 0) := by
      have hleR : ((if T.card = 0 then (1 : ℤ) else 0) : ℝ)
          ≤ ((Prelim.SieveCalculus.blockUpper h T.card : ℤ) : ℝ) := by
        exact_mod_cast hle
      simp only [Int.cast_ite, Int.cast_one, Int.cast_zero] at hleR
      linarith
    exact hcast
  have hpt1 : ∀ T ∈ B.powerset,
      blockUval h T - blockIval T ≤ blockEval h T := by
    intro T _
    unfold blockUval blockIval blockEval
    have hle := Prelim.SieveCalculus.blockUpper_sub_indicator_le_error h T.card he
    have hleR : ((Prelim.SieveCalculus.blockUpper h T.card : ℤ) : ℝ)
        - ((if T.card = 0 then (1 : ℤ) else 0) : ℝ)
        ≤ (((T.card.choose (h + 1) : ℕ)) : ℝ) := by
      exact_mod_cast hle
    simp only [Int.cast_ite, Int.cast_one, Int.cast_zero] at hleR
    linarith
  constructor
  · rw [hSsub]
    apply Finset.sum_nonneg
    intro T hT
    have hP := trialProb_nonneg B g hg0 hg1 T (Finset.mem_powerset.mp hT)
    have hD := hpt0 T hT
    exact mul_nonneg hP hD
  · rw [hSsub]
    unfold blockExpE
    apply Finset.sum_le_sum
    intro T hT
    have hP := trialProb_nonneg B g hg0 hg1 T (Finset.mem_powerset.mp hT)
    have hD := hpt1 T hT
    exact mul_le_mul_of_nonneg_left hD hP

/-- `E` equals the symmetric sum (double counting via `sum_comm` +
`trialProb_superset`). -/
theorem blockExpE_eq_symm (B : Finset ℕ) (g : ℕ → ℝ) (h : ℕ) :
    blockExpE B g h
      = ∑ u ∈ B.powersetCard (h + 1), ∏ p ∈ u, g p := by
  have hfil : ∀ T ∈ B.powerset,
      (B.powersetCard (h + 1)).filter (· ⊆ T)
        = T.powersetCard (h + 1) := by
    intro T hT
    have hTsub : T ⊆ B := Finset.mem_powerset.mp hT
    ext u
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, huCard⟩, huT⟩
      exact ⟨huT, huCard⟩
    · rintro ⟨huT, huCard⟩
      exact ⟨⟨Finset.Subset.trans huT hTsub, huCard⟩, huT⟩
  have hcard : ∀ T ∈ B.powerset,
      trialProb B g T * blockEval h T
      = ∑ u ∈ B.powersetCard (h + 1),
        (if u ⊆ T then trialProb B g T else 0) := by
    intro T hT
    unfold blockEval
    have hE : ((T.card.choose (h + 1) : ℕ) : ℝ)
        = ((T.powersetCard (h + 1)).card : ℝ) := by
      rw [Finset.card_powersetCard]
    have hF : ((T.powersetCard (h + 1)).card : ℝ)
        = ∑ u ∈ B.powersetCard (h + 1),
          (if u ⊆ T then (1 : ℝ) else 0) := by
      have hFeq : T.powersetCard (h + 1)
          = (B.powersetCard (h + 1)).filter (· ⊆ T) := (hfil T hT).symm
      have hFnat : (T.powersetCard (h + 1)).card
          = ∑ u ∈ B.powersetCard (h + 1),
            (if u ⊆ T then 1 else 0 : ℕ) := by
        rw [hFeq, Finset.card_eq_sum_ones, Finset.sum_filter]
      exact_mod_cast hFnat
    rw [hE, hF, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases huT : u ⊆ T <;> simp [huT]
  calc blockExpE B g h
      = ∑ T ∈ B.powerset, ∑ u ∈ B.powersetCard (h + 1),
        (if u ⊆ T then trialProb B g T else 0) := by
        unfold blockExpE
        apply Finset.sum_congr rfl
        intro T hT
        exact hcard T hT
    _ = ∑ u ∈ B.powersetCard (h + 1), ∑ T ∈ B.powerset,
        (if u ⊆ T then trialProb B g T else 0) :=
        Finset.sum_comm
    _ = ∑ u ∈ B.powersetCard (h + 1), ∑ T ∈ B.powerset.filter (fun T => u ⊆ T),
        trialProb B g T := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_filter]
    _ = ∑ u ∈ B.powersetCard (h + 1), ∏ p ∈ u, g p := by
        apply Finset.sum_congr rfl
        intro u hu
        have huB : u ⊆ B := (Finset.mem_powersetCard.mp hu).1
        exact trialProb_superset B g huB

/-- `e ≤ C^{h+1}/(h+1)!` from `esymm_le` and total mass `≤ C`. -/
theorem blockExpE_le_tail (B : Finset ℕ) (g : ℕ → ℝ) (h : ℕ) (C : ℝ)
    (hg0 : ∀ p ∈ B, 0 ≤ g p)
    (hsum : ∑ p ∈ B, g p ≤ C) :
    blockExpE B g h ≤ Prelim.SieveCalculus.tailTerm C h := by
  rw [blockExpE_eq_symm]
  have hle := Prelim.SieveCalculus.esymm_le B g (h + 1) hg0
  have hfact_pos : (0 : ℝ) < (Nat.factorial (h + 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.factorial_ne_zero _))
  have hpow : (∑ p ∈ B, g p) ^ (h + 1) / (Nat.factorial (h + 1) : ℝ)
      ≤ C ^ (h + 1) / (Nat.factorial (h + 1) : ℝ) := by
    rw [div_le_div_iff_of_pos_right hfact_pos]
    exact pow_le_pow_left₀ (Finset.sum_nonneg (fun p hp => hg0 p hp)) hsum _
  calc ∑ u ∈ B.powersetCard (h + 1), ∏ p ∈ u, g p
      ≤ (∑ p ∈ B, g p) ^ (h + 1) / (Nat.factorial (h + 1) : ℝ) := hle
    _ ≤ C ^ (h + 1) / (Nat.factorial (h + 1) : ℝ) := hpow
    _ = Prelim.SieveCalculus.tailTerm C h := rfl

/-- `S` equals the signed symmetric sum (for product factorization). -/
theorem blockExpS_eq_symm (B : Finset ℕ) (g : ℕ → ℝ) (h : ℕ) :
    blockExpS B g h
      = ∑ u ∈ B.powerset.filter (fun u => u.card ≤ h),
        (-1 : ℝ) ^ u.card * ∏ p ∈ u, g p := by
  have hfil : ∀ T ∈ B.powerset,
      (B.powerset.filter (fun u => u.card ≤ h)).filter (· ⊆ T)
        = T.powerset.filter (fun u => u.card ≤ h) := by
    intro T hT
    have hTsub : T ⊆ B := Finset.mem_powerset.mp hT
    ext u
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨_, huCard⟩, huT⟩
      exact ⟨huT, huCard⟩
    · rintro ⟨huT, huCard⟩
      exact ⟨⟨Finset.Subset.trans huT hTsub, huCard⟩, huT⟩
  have hU : ∀ T ∈ B.powerset, blockUval h T
      = ∑ u ∈ B.powerset.filter (fun u => u.card ≤ h),
        (if u ⊆ T then (-1 : ℝ) ^ u.card else 0) := by
    intro T hT
    have hSubset := Prelim.BlockSieve.blockSubsetSum_eq h T
    have hcast : blockUval h T
        = ((∑ u ∈ T.powerset.filter (fun u => u.card ≤ h),
          (-1 : ℤ) ^ u.card : ℤ) : ℝ) := by
      unfold blockUval
      rw [← hSubset]
    have hFeq : T.powerset.filter (fun u => u.card ≤ h)
        = (B.powerset.filter (fun u => u.card ≤ h)).filter (· ⊆ T) :=
      (hfil T hT).symm
    calc blockUval h T
        = ((∑ u ∈ T.powerset.filter (fun u => u.card ≤ h),
          (-1 : ℤ) ^ u.card : ℤ) : ℝ) := hcast
      _ = ∑ u ∈ T.powerset.filter (fun u => u.card ≤ h),
          (-1 : ℝ) ^ u.card := by simp
      _ = ∑ u ∈ B.powerset.filter (fun u => u.card ≤ h),
          (if u ⊆ T then (-1 : ℝ) ^ u.card else 0) := by
          rw [hFeq, Finset.sum_filter]
  calc blockExpS B g h
      = ∑ T ∈ B.powerset, ∑ u ∈ B.powerset.filter (fun u => u.card ≤ h),
        (if u ⊆ T then trialProb B g T * ((-1 : ℝ) ^ u.card) else 0) := by
        unfold blockExpS
        apply Finset.sum_congr rfl
        intro T hT
        rw [hU T hT, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        by_cases huT : u ⊆ T <;> simp [huT]
    _ = ∑ u ∈ B.powerset.filter (fun u => u.card ≤ h),
        ∑ T ∈ B.powerset,
        (if u ⊆ T then trialProb B g T * ((-1 : ℝ) ^ u.card) else 0) :=
        Finset.sum_comm
    _ = ∑ u ∈ B.powerset.filter (fun u => u.card ≤ h),
        (-1 : ℝ) ^ u.card * ∑ T ∈ B.powerset.filter (fun T => u ⊆ T),
        trialProb B g T := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_filter]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T _
        by_cases huT : u ⊆ T <;> simp [huT, mul_comm]
    _ = ∑ u ∈ B.powerset.filter (fun u => u.card ≤ h),
        (-1 : ℝ) ^ u.card * ∏ p ∈ u, g p := by
        apply Finset.sum_congr rfl
        intro u hu
        have huB : u ⊆ B := Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
        rw [trialProb_superset B g huB]

end PrelimLemmas
end Erdos821
