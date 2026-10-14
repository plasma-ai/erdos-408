import Erdos821.P3Rare.Base
import Erdos821.P3Edge.LargeX
import Erdos821.P3Edge.Polylog
import Erdos821.P3Edge.PromoBound
import Erdos821.P3Edge.SmallFresh

set_option autoImplicit false

/-! Final assembly of the rare-transfer estimate `MemoryRareTask`
(source §2, `lem:memory-rare`): the promotion sector is sparse in source
omissions and the store-only sector is sparse in target omissions; each is
bounded by contextwise weighted Schur, and the context constants sum to the
pattern mass times a `J`-independent power of `L(x)`. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Rare

open Erdos821.Blueprint.Graph
open Erdos821.S2Core


/-- Projected sparse-row context Schur bound; the zero-support hypothesis is
only required on retained sources. -/
theorem normBound_sum_projected_contexts_sparseRows'
    {α Ω κ : Type*} [Fintype Ω] [Fintype κ]
    (mass w : α → ℝ) (keep : α → Prop)
    (K : κ → Ω → α → α → ℝ) (bad : κ → α → Ω → Prop)
    (R C : κ → ℝ) (B : ℕ)
    (hm : ∀ a, 0 ≤ mass a) (hw : ∀ a, 0 < w a)
    (hK : ∀ j ω a b, 0 ≤ K j ω a b)
    (hR : ∀ j, 0 ≤ R j) (hC : ∀ j, 0 ≤ C j)
    (hD : 0 < (Fintype.card Ω : ℝ))
    (hrow : ∀ j a ω t, ∑ b ∈ t, K j ω a b * w b ≤ R j * w a)
    (hcol : ∀ j b ω s, ∑ a ∈ s, mass a * K j ω a b * w a ≤ C j * mass b * w b)
    (hbad : ∀ j a, (Finset.univ.filter (fun ω => keep a ∧ bad j a ω)).card ≤ B)
    (hzero : ∀ j a ω, keep a → ¬ bad j a ω → ∀ b, K j ω a b = 0) :
    NormBound mass
      (fun a b => ∑ j,
        (((Fintype.card Ω : ℝ)⁻¹ * ∑ ω,
          (if keep a ∧ keep b then K j ω a b else 0) : ℝ) : ℂ))
      (∑ j, Real.sqrt ((R j * ((B : ℝ) / (Fintype.card Ω : ℝ))) * C j)) := by
  classical
  let K' : κ → Ω → α → α → ℝ := fun j ω a b =>
    if keep a ∧ keep b then K j ω a b else 0
  let bad' : κ → α → Ω → Prop := fun j a ω => keep a ∧ bad j a ω
  have hK' : ∀ j ω a b, 0 ≤ K' j ω a b := by
    intro j ω a b
    by_cases h : keep a ∧ keep b <;> simp [K', h, hK]
  have hrow' : ∀ j a ω t, ∑ b ∈ t, K' j ω a b * w b ≤ R j * w a := by
    intro j a ω t
    by_cases ha : keep a
    · simpa [K', ha, Finset.sum_filter] using hrow j a ω (t.filter keep)
    · simpa [K', ha] using mul_nonneg (hR j) (hw a).le
  have hcol' : ∀ j b ω s,
      ∑ a ∈ s, mass a * K' j ω a b * w a ≤ C j * mass b * w b := by
    intro j b ω s
    by_cases hb : keep b
    · simpa [K', hb, Finset.sum_filter] using hcol j b ω (s.filter keep)
    · simpa [K', hb] using mul_nonneg (mul_nonneg (hC j) (hm b)) (hw b).le
  have hbadConverted : ∀ j a,
      (@Finset.filter Ω (fun ω => bad' j a ω)
        (fun ω => Classical.propDecidable (bad' j a ω)) Finset.univ).card ≤ B := by
    intro j a
    have hf : (@Finset.filter Ω (fun ω => bad' j a ω)
        (fun ω => Classical.propDecidable (bad' j a ω)) Finset.univ) =
        Finset.univ.filter (fun ω => keep a ∧ bad j a ω) := by
      ext ω
      simp [bad']
    rw [hf]
    exact hbad j a
  have hzero' : ∀ j a ω, ¬ bad' j a ω → ∀ b, K' j ω a b = 0 := by
    intro j a ω hnot b
    by_cases ha : keep a
    · have hnb : ¬ bad j a ω := fun h => hnot (show keep a ∧ bad j a ω from ⟨ha, h⟩)
      by_cases hb : keep b
      · simp [K', ha, hb, hzero j a ω ha hnb b]
      · simp [K', ha, hb]
    · simp [K', ha]
  simpa [K'] using normBound_sum_contexts_sparseRows mass w K' bad' R C B
    hm hw hK' hR hC hD hrow' hcol' hbadConverted hzero'

/-- Projected sparse-column context Schur bound; the zero-support hypothesis
is only required on retained targets. -/
theorem normBound_sum_projected_contexts_sparseCols'
    {α Ω κ : Type*} [Fintype Ω] [Fintype κ]
    (mass w : α → ℝ) (keep : α → Prop)
    (K : κ → Ω → α → α → ℝ) (bad : κ → α → Ω → Prop)
    (R C : κ → ℝ) (B : ℕ)
    (hm : ∀ a, 0 ≤ mass a) (hw : ∀ a, 0 < w a)
    (hK : ∀ j ω a b, 0 ≤ K j ω a b)
    (hR : ∀ j, 0 ≤ R j) (hC : ∀ j, 0 ≤ C j)
    (hD : 0 < (Fintype.card Ω : ℝ))
    (hrow : ∀ j a ω t, ∑ b ∈ t, K j ω a b * w b ≤ R j * w a)
    (hcol : ∀ j b ω s, ∑ a ∈ s, mass a * K j ω a b * w a ≤ C j * mass b * w b)
    (hbad : ∀ j b, (Finset.univ.filter (fun ω => keep b ∧ bad j b ω)).card ≤ B)
    (hzero : ∀ j b ω, keep b → ¬ bad j b ω → ∀ a, K j ω a b = 0) :
    NormBound mass
      (fun a b => ∑ j,
        (((Fintype.card Ω : ℝ)⁻¹ * ∑ ω,
          (if keep a ∧ keep b then K j ω a b else 0) : ℝ) : ℂ))
      (∑ j, Real.sqrt (R j * (C j * ((B : ℝ) / (Fintype.card Ω : ℝ))))) := by
  classical
  let K' : κ → Ω → α → α → ℝ := fun j ω a b =>
    if keep a ∧ keep b then K j ω a b else 0
  let bad' : κ → α → Ω → Prop := fun j b ω => keep b ∧ bad j b ω
  have hK' : ∀ j ω a b, 0 ≤ K' j ω a b := by
    intro j ω a b
    by_cases h : keep a ∧ keep b <;> simp [K', h, hK]
  have hrow' : ∀ j a ω t, ∑ b ∈ t, K' j ω a b * w b ≤ R j * w a := by
    intro j a ω t
    by_cases ha : keep a
    · simpa [K', ha, Finset.sum_filter] using hrow j a ω (t.filter keep)
    · simpa [K', ha] using mul_nonneg (hR j) (hw a).le
  have hcol' : ∀ j b ω s,
      ∑ a ∈ s, mass a * K' j ω a b * w a ≤ C j * mass b * w b := by
    intro j b ω s
    by_cases hb : keep b
    · simpa [K', hb, Finset.sum_filter] using hcol j b ω (s.filter keep)
    · simpa [K', hb] using mul_nonneg (mul_nonneg (hC j) (hm b)) (hw b).le
  have hbadConverted : ∀ j b,
      (@Finset.filter Ω (fun ω => bad' j b ω)
        (fun ω => Classical.propDecidable (bad' j b ω)) Finset.univ).card ≤ B := by
    intro j b
    have hf : (@Finset.filter Ω (fun ω => bad' j b ω)
        (fun ω => Classical.propDecidable (bad' j b ω)) Finset.univ) =
        Finset.univ.filter (fun ω => keep b ∧ bad j b ω) := by
      ext ω
      simp [bad']
    rw [hf]
    exact hbad j b
  have hzero' : ∀ j b ω, ¬ bad' j b ω → ∀ a, K' j ω a b = 0 := by
    intro j b ω hnot a
    by_cases hb : keep b
    · have hnb : ¬ bad j b ω := fun h => hnot (show keep b ∧ bad j b ω from ⟨hb, h⟩)
      by_cases ha : keep a
      · simp [K', ha, hb, hzero j b ω hb hnb a]
      · simp [K', ha, hb]
    · simp [K', hb]
  simpa [K'] using normBound_sum_contexts_sparseCols mass w K' bad' R C B
    hm hw hK' hR hC hD hrow' hcol' hbadConverted hzero'

theorem promotionContextKernel_nonneg {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (r : MemoryParameters F) (theta : ℝ) (i : Fin n)
    (ctx : EdgeTransferContext A) (O : OmissionChoices P (J + F.ell) F.ell)
    (s t : P.MemoryState (J + F.ell)) :
    0 ≤ promotionContextKernel A r theta i ctx O s t := by
  unfold promotionContextKernel
  apply mul_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) (edgeSymmetryFactor_nonneg P _)
  · apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    apply Finset.sum_nonneg
    intro c _
    dsimp only
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl

theorem storeOnlyContextKernel_nonneg {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (r : MemoryParameters F) (theta : ℝ) (i : Fin n)
    (ctx : EdgeTransferContext A) (O : OmissionChoices P (J + F.ell) F.ell)
    (s t : P.MemoryState (J + F.ell)) :
    0 ≤ storeOnlyContextKernel A r theta i ctx O s t := by
  unfold storeOnlyContextKernel
  apply mul_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) (edgeSymmetryFactor_nonneg P _)
  · apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    apply Finset.sum_nonneg
    intro c _
    dsimp only
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl

theorem promotionOmissionAverage_projectedNormBound'
    {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    (A : Model F P J m) (r : MemoryParameters F) (theta : ℝ) (i : Fin n)
    (keep : P.MemoryState (J + F.ell) → Prop)
    (mass w : P.MemoryState (J + F.ell) → ℝ)
    (R C : EdgeTransferContext A → ℝ) (B : ℕ)
    (hm : ∀ s, 0 ≤ mass s) (hw : ∀ s, 0 < w s)
    (hD : 0 < (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ))
    (hR : ∀ ctx, 0 ≤ R ctx) (hC : ∀ ctx, 0 ≤ C ctx)
    (hrow : ∀ ctx O s T,
      ∑ t ∈ T, promotionContextKernel A r theta i ctx O s t * w t ≤ R ctx * w s)
    (hcol : ∀ ctx O t S,
      ∑ s ∈ S, mass s * promotionContextKernel A r theta i ctx O s t * w s ≤
        C ctx * mass t * w t)
    (hbad : ∀ ctx s,
      (Finset.univ.filter (fun O => keep s ∧ promotionContextBadOmission A i ctx s O)).card ≤ B) :
    NormBound mass
      (projectKernel keep (fun s t =>
        (promotionOmissionAverageKernel A r.rho theta i s t : ℂ)))
      (∑ ctx : EdgeTransferContext A,
        Real.sqrt ((R ctx * ((B : ℝ) /
          (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ))) * C ctx)) := by
  classical
  let Ω := OmissionChoices P (J + F.ell) F.ell
  let K : EdgeTransferContext A → Ω → P.MemoryState (J + F.ell) →
      P.MemoryState (J + F.ell) → ℝ := fun ctx O s t =>
    promotionContextKernel A r theta i ctx O s t
  let bad : EdgeTransferContext A → P.MemoryState (J + F.ell) → Ω → Prop :=
    fun ctx s O => promotionContextBadOmission A i ctx s O
  have hK' : ∀ ctx O s t, 0 ≤ K ctx O s t := by
    intro ctx O s t
    exact promotionContextKernel_nonneg A r theta i ctx O s t
  have hrow' : ∀ ctx s O T, ∑ t ∈ T, K ctx O s t * w t ≤ R ctx * w s := by
    intro ctx s O T
    simpa [K] using hrow ctx O s T
  have hcol' : ∀ ctx t O S,
      ∑ s ∈ S, mass s * K ctx O s t * w s ≤ C ctx * mass t * w t := by
    intro ctx t O S
    simpa [K] using hcol ctx O t S
  have hbad' : ∀ ctx s,
      (Finset.univ.filter (fun O : Ω => keep s ∧ bad ctx s O)).card ≤ B := by
    intro ctx s
    simpa [bad] using hbad ctx s
  have hzero' : ∀ ctx s O, keep s → ¬ bad ctx s O → ∀ t, K ctx O s t = 0 := by
    intro ctx s O _ hnot t
    exact promotionContextKernel_zero_of_not_bad A r theta i ctx O s t hnot
  have hbase := normBound_sum_projected_contexts_sparseRows' mass w keep K bad R C B
    hm hw hK' hR hC hD hrow' hcol' hbad' hzero'
  have hEq (s t : P.MemoryState (J + F.ell)) :
      projectKernel keep (fun s t =>
        (promotionOmissionAverageKernel A r.rho theta i s t : ℂ)) s t =
      ∑ ctx : EdgeTransferContext A,
        (((Fintype.card Ω : ℝ)⁻¹ * ∑ O : Ω,
          (if keep s ∧ keep t then K ctx O s t else 0) : ℝ) : ℂ) := by
    by_cases hs : keep s <;> by_cases ht : keep t
    · simp only [projectKernel, hs, ht, and_self, ite_true]
      rw [promotionOmissionAverageKernel_context_sum]
      simp [K, Ω, Finset.mul_sum]
    · simp [projectKernel, hs, ht, K]
    · simp [projectKernel, hs, ht, K]
    · simp [projectKernel, hs, ht, K]
  intro S T f g
  simpa only [hEq] using hbase S T f g

theorem storeOnlyOmissionAverage_projectedNormBound'
    {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    (A : Model F P J m) (r : MemoryParameters F) (theta : ℝ) (i : Fin n)
    (keep : P.MemoryState (J + F.ell) → Prop)
    (mass w : P.MemoryState (J + F.ell) → ℝ)
    (R C : EdgeTransferContext A → ℝ) (B : ℕ)
    (hm : ∀ s, 0 ≤ mass s) (hw : ∀ s, 0 < w s)
    (hD : 0 < (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ))
    (hR : ∀ ctx, 0 ≤ R ctx) (hC : ∀ ctx, 0 ≤ C ctx)
    (hrow : ∀ ctx O s T,
      ∑ t ∈ T, storeOnlyContextKernel A r theta i ctx O s t * w t ≤ R ctx * w s)
    (hcol : ∀ ctx O t S,
      ∑ s ∈ S, mass s * storeOnlyContextKernel A r theta i ctx O s t * w s ≤
        C ctx * mass t * w t)
    (hbad : ∀ ctx t,
      (Finset.univ.filter (fun O => keep t ∧ storeOnlyContextBadOmission A i ctx t O)).card ≤ B) :
    NormBound mass
      (projectKernel keep (fun s t =>
        (storeOnlyOmissionAverageKernel A r.rho theta i s t : ℂ)))
      (∑ ctx : EdgeTransferContext A,
        Real.sqrt (R ctx * (C ctx * ((B : ℝ) /
          (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ))))) := by
  classical
  let Ω := OmissionChoices P (J + F.ell) F.ell
  let K : EdgeTransferContext A → Ω → P.MemoryState (J + F.ell) →
      P.MemoryState (J + F.ell) → ℝ := fun ctx O s t =>
    storeOnlyContextKernel A r theta i ctx O s t
  let bad : EdgeTransferContext A → P.MemoryState (J + F.ell) → Ω → Prop :=
    fun ctx t O => storeOnlyContextBadOmission A i ctx t O
  have hK' : ∀ ctx O s t, 0 ≤ K ctx O s t := by
    intro ctx O s t
    exact storeOnlyContextKernel_nonneg A r theta i ctx O s t
  have hrow' : ∀ ctx s O T, ∑ t ∈ T, K ctx O s t * w t ≤ R ctx * w s := by
    intro ctx s O T
    simpa [K] using hrow ctx O s T
  have hcol' : ∀ ctx t O S,
      ∑ s ∈ S, mass s * K ctx O s t * w s ≤ C ctx * mass t * w t := by
    intro ctx t O S
    simpa [K] using hcol ctx O t S
  have hbad' : ∀ ctx t,
      (Finset.univ.filter (fun O : Ω => keep t ∧ bad ctx t O)).card ≤ B := by
    intro ctx t
    simpa [bad] using hbad ctx t
  have hzero' : ∀ ctx t O, keep t → ¬ bad ctx t O → ∀ s, K ctx O s t = 0 := by
    intro ctx t O _ hnot s
    exact storeOnlyContextKernel_zero_of_not_bad A r theta i ctx O s t hnot
  have hbase := normBound_sum_projected_contexts_sparseCols' mass w keep K bad R C B
    hm hw hK' hR hC hD hrow' hcol' hbad' hzero'
  have hEq (s t : P.MemoryState (J + F.ell)) :
      projectKernel keep (fun s t =>
        (storeOnlyOmissionAverageKernel A r.rho theta i s t : ℂ)) s t =
      ∑ ctx : EdgeTransferContext A,
        (((Fintype.card Ω : ℝ)⁻¹ * ∑ O : Ω,
          (if keep s ∧ keep t then K ctx O s t else 0) : ℝ) : ℂ) := by
    by_cases hs : keep s <;> by_cases ht : keep t
    · simp only [projectKernel, hs, ht, and_self, ite_true]
      rw [storeOnlyOmissionAverageKernel_context_sum]
      simp [K, Ω, Finset.mul_sum]
    · simp [projectKernel, hs, ht, K]
    · simp [projectKernel, hs, ht, K]
    · simp [projectKernel, hs, ht, K]
  intro S T f g
  simpa only [hEq] using hbase S T f g

/-- Projected dirty edge kernel from projected sector bounds. -/
theorem normBound_projected_dirty_of_sectorBounds {F : FixedData}
    {P : PrimeGroups} {J m n : ℕ} (A : Model F P J m) (rho theta : ℝ)
    (i : Fin n) (phi : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ)
    (hphi : ∀ s t c, ‖phi s t c‖ ≤ 1)
    (mass : P.MemoryState (J + F.ell) → ℝ) (keep : P.MemoryState (J + F.ell) → Prop)
    (c₁ c₂ : ℝ) (hmass : ∀ s, 0 ≤ mass s)
    (hprom : NormBound mass
      (projectKernel keep (fun s t => (promotionOmissionAverageKernel A rho theta i s t : ℂ))) c₁)
    (hstore : NormBound mass
      (projectKernel keep (fun s t => (storeOnlyOmissionAverageKernel A rho theta i s t : ℂ))) c₂) :
    NormBound mass (projectKernel keep (memoryEdgeKernel A n rho theta i .dirty phi))
      (c₁ + c₂) := by
  classical
  let K₁ : P.MemoryState (J + F.ell) → P.MemoryState (J + F.ell) → ℝ := fun s t =>
    if keep s ∧ keep t then promotionOmissionAverageKernel A rho theta i s t else 0
  let K₂ : P.MemoryState (J + F.ell) → P.MemoryState (J + F.ell) → ℝ := fun s t =>
    if keep s ∧ keep t then storeOnlyOmissionAverageKernel A rho theta i s t else 0
  have e₁ : (fun s t => ((K₁ s t : ℝ) : ℂ)) =
      projectKernel keep (fun s t => (promotionOmissionAverageKernel A rho theta i s t : ℂ)) := by
    funext s t
    simp only [K₁, projectKernel]
    split_ifs <;> simp
  have e₂ : (fun s t => ((K₂ s t : ℝ) : ℂ)) =
      projectKernel keep (fun s t => (storeOnlyOmissionAverageKernel A rho theta i s t : ℂ)) := by
    funext s t
    simp only [K₂, projectKernel]
    split_ifs <;> simp
  apply normBound_of_two_positive_dominations mass _ K₁ K₂ c₁ c₂ hmass
  · intro s t
    simp only [K₁]
    split_ifs
    · exact promotionOmissionAverageKernel_nonneg A rho theta i s t
    · exact le_rfl
  · intro s t
    simp only [K₂]
    split_ifs
    · exact storeOnlyOmissionAverageKernel_nonneg A rho theta i s t
    · exact le_rfl
  · intro s t
    simp only [K₁, K₂, projectKernel]
    split_ifs
    · simpa [promotionOmissionAverageKernel, storeOnlyOmissionAverageKernel] using
        memoryEdgeKernel_dirty_omission_domination A rho theta i phi hphi s t
    · simp
  · rw [e₁]
    exact hprom
  · rw [e₂]
    exact hstore

theorem normBound_mono' {α : Type*} {mass : α → ℝ} {K : α → α → ℂ} {c c' : ℝ}
    (h : NormBound mass K c) (hc : c ≤ c') : NormBound mass K c' := by
  intro S T f g
  refine le_trans (h S T f g) ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end Erdos821.P3Rare
