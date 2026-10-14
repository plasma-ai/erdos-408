import Erdos408.Graph.Assembly
import Erdos408.Graph.Family
import Erdos821.P3Final.Transference
import Erdos821.P3Rare.Proof
import Erdos821.S34.IdealInputs

/-!
# The graph transference input

`GraphTransference` from the vendored formalization of WD (Yao Xu's
totient-fibers-lean4): WD Corollary 3.11 (`TransferencePairing`) applied to the
residual family of WD Theorem 4.1 (`IdealConstruction`).

* Given `E`, `TransferencePairing` gives the ideal saving `E_id`;
  `IdealConstruction` at `E_id` and `C₄` gives the probe bound `m`, a slot
  threshold, the pattern-mass exponent `C₁` and the kernel exponents; and
  `TransferencePairing` at `m, C₁` gives the slot threshold `J₀`. Take `J` the
  larger threshold, `γ = 1/2`, `k = 1` and `C_f = 0`.
* The groups are reindexed by `Fin n` (`FamilyBound.reindex`) and encoded as
  upstream's admissible `PrimeGroups` (`admissible`).
* The comparison patterns are the cell-character terms of the residual
  family's comparison kernels (`pairing_eq_family`). Their weights sum to at
  most `ξ⁻² Q⁴` times the pattern mass, which is `L^{C₁ + 2ξ_exp + 4q_exp}`.
* Upstream's pairing and norms are `GraphTransference`'s for endpoints of the
  position alone (`pairing_eq_sum`, `normOn_extend`, `normOn_targets`).
-/

namespace Erdos408

open Filter _root_.Erdos408.Graph
open Erdos821.Blueprint.Graph (FixedData PrimeGroups Family intervalBigGroups)
open Erdos821.Blueprint.Analytic (cell)

/-- WD Corollary 3.11, from the vendored P3 package. -/
theorem transferencePairing : Erdos821.Blueprint.Graph.TransferencePairing :=
  (Erdos821.S2Core.transference_inputs_of_remaining
    Erdos821.S2Packet.AbsolutePhysicalPacketTask_proof
    Erdos821.S2Ltrans.LocalTransferenceAssemblyTask_proof
    (Erdos821.P3Final.remaining_of_rare Erdos821.S2Core.MemoryRareTask_proof)).pairing

/-- WD Theorem 4.1, from the vendored P4 package. -/
theorem idealConstruction : Erdos821.Blueprint.Graph.IdealConstruction :=
  (Erdos821.S34Core.ideal_inputs_of_cancellation_task
    Erdos821.P4Probe.FiniteProbeCancellationTask_proof).construction

/-- `√(L^{2C}) = L^C`. -/
private lemma sqrt_rpow_two_mul {L : ℝ} (hL : 0 ≤ L) (C : ℝ) :
    Real.sqrt (L ^ (2 * C)) = L ^ C := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL]
  ring_nf

/-- The graph transference input (PD Propositions 6.2 and 6.3). -/
theorem graphTransference : GraphTransference := by
  intro q₀ c₀ C₀ vlo vhi hq₀ hq₁ hc₀ hvlo E C₃ C₄
  obtain ⟨Eid, hEid, hTP⟩ := transferencePairing (fixedData q₀ c₀ C₀ vlo vhi hq₀ hq₁ hc₀ hvlo)
    (max E 1) (lt_max_of_lt_right one_pos)
  obtain ⟨m, J₀', C₁, qexp, hexp, ξexp, -, hhexp, -, hIC⟩ :=
    idealConstruction (fixedData q₀ c₀ C₀ vlo vhi hq₀ hq₁ hc₀ hvlo) Eid (max C₄ 0) hEid
      (le_max_right _ _)
  obtain ⟨J₀, hJ₀⟩ := hTP m C₁
  obtain ⟨K, hK, hev⟩ := hJ₀ (max J₀ J₀') (le_max_left _ _) (1 / 2) 1 C₃ 0 (by norm_num)
    one_pos
  refine ⟨m, max J₀ J₀', C₁ + 2 * ξexp + 4 * qexp, K, ?_⟩
  filter_upwards [hev, hIC (max J₀ J₀') (le_max_right _ _), eventually_ge_atTop (Real.exp 1)]
    with x hTPx hICx hx
  intro ι _ _ P big hdisj hs₁ hs₂ hb₁ hb₂ hV hsmall hbig hint
  show FamilyBound q₀ m (max J₀ J₀') (C₁ + 2 * ξexp + 4 * qexp) K E C₃ C₄ x P big
  refine FamilyBound.reindex (Fintype.equivFin ι) ?_
  -- the scales
  have hx₀ : 0 < x := (Real.exp_pos 1).trans_le hx
  have hL : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx₀).mpr hx
  have hL₀ : 0 < Real.log x := one_pos.trans_le hL
  have hT : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL
  -- the reindexed groups
  set e := Fintype.equivFin ι
  have hmem : ∀ k, k ∈ big.map e.toEmbedding ↔ e.symm k ∈ big := fun k => by
    rw [Finset.mem_map_equiv]
  have hcard : (big.map e.toEmbedding).card = big.card := Finset.card_map _
  have hcard' : (Finset.univ \ big.map e.toEmbedding).card = (Finset.univ \ big).card := by
    rw [Finset.card_univ_sdiff, Finset.card_univ_sdiff, hcard, Fintype.card_fin]
  have hprime : ∀ k p, p ∈ P (e.symm k) → p.Prime := fun k p hp => by
    by_cases hk : e.symm k ∈ big
    · exact (mem_primesIcc (hbig _ hk hp)).1
    · exact (mem_primesIcc (hsmall _ hk hp)).1
  have hdisj' : ∀ k k', k ≠ k' → Disjoint (P (e.symm k)) (P (e.symm k')) :=
    fun k k' hkk' => hdisj _ _ (e.symm.injective.ne hkk')
  set G := primeGroups (fun k => P (e.symm k)) (big.map e.toEmbedding) hprime hdisj'
  have hadm := admissible (hP := hprime) (hd := hdisj') (hq₀ := hq₀) (hq₁ := hq₁) (hc₀ := hc₀)
    (hvlo := hvlo) (C₀ := C₀) (vhi := vhi) hT (by rwa [hcard']) (by rwa [hcard'])
    (by rwa [hcard]) (by rwa [hcard]) (fun k => hV (e.symm k))
    (fun k hk => hsmall _ (by rwa [← hmem])) (fun k hk => hbig _ (by rwa [← hmem]))
  have hint' := intervalBigGroups_primeGroups (hP := hprime) (hd := hdisj')
    fun k hk => hint _ ((hmem k).mp hk)
  have hGV : ∀ g, G.V g ≠ 0 := fun g => by
    rw [V_primeGroups]
    exact (hvlo.trans_le (hV (e.symm g)).1).ne'
  -- the residual family
  obtain ⟨B, ⟨raw, block, hraw, hraw', hcomp⟩, hmass, hnorm⟩ := hICx G hadm hint'
  set Q := ⌊Real.log x ^ qexp⌋₊
  set w := Real.log x ^ (-hexp)
  set ξ := Real.log x ^ (-ξexp) with hξdef
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hL₀ _
  have hw₀ : 0 < w := Real.rpow_pos_of_pos hL₀ _
  have hw₁ : w ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (neg_nonpos.mpr hhexp.le)
  have hcoef := fun v hv => (hcomp v hv).2.2
  have hne : ∀ v, v ≠ raw → ∃ g, ((B.pattern v).changed g).Nonempty := fun v hv => by
    obtain ⟨g, -, hg⟩ := (hcomp v hv).2.1 false
    exact ⟨g.val, hg⟩
  -- each enumerated term belongs to a comparison pattern
  have hpt : ∀ ν, (famPoint B raw block Q w ξ ν).1 ≠ raw := fun ν =>
    Finset.ne_of_mem_erase (Finset.mem_sigma.mp ((famIndex B raw block Q w ξ).equivFin.symm
      ν).property).1
  have hside : ∀ (g : G.BigGroup) (ν : Fin (famIndex B raw block Q w ξ).card) (s : Bool),
      block g = s →
        blockSlots (B.pattern (famPoint B raw block Q w ξ ν).1) block s g.val =
          (B.pattern (famPoint B raw block Q w ξ ν).1).changed g.val := fun g ν s hs => by
    simp [blockSlots, side, g.property, hs]
  refine ⟨(famIndex B raw block Q w ξ).card,
    fun ν => blockSlots (B.pattern (famPoint B raw block Q w ξ ν).1) block false,
    fun ν => blockSlots (B.pattern (famPoint B raw block Q w ξ ν).1) block true,
    fun ν => termWeight (B.pattern (famPoint B raw block Q w ξ ν).1) block w
      (famPoint B raw block Q w ξ ν).2,
    fun ν => cellTest w (famPoint B raw block Q w ξ ν).2.1 (famPoint B raw block Q w ξ ν).2.2.1,
    fun ν => cellTest w (famPoint B raw block Q w ξ ν).2.2.2.1
      (famPoint B raw block Q w ξ ν).2.2.2.2,
    fun ν => cellMark w (famPoint B raw block Q w ξ ν).2.1 (famPoint B raw block Q w ξ ν).2.2.1,
    fun ν => cellMark w (famPoint B raw block Q w ξ ν).2.2.2.1
      (famPoint B raw block Q w ξ ν).2.2.2.2,
    fun ν => Real.exp ((famPoint B raw block Q w ξ ν).2.1 * w),
    fun ν => Real.exp ((famPoint B raw block Q w ξ ν).2.2.2.1 * w),
    fun ν g => ?_, fun ν g hg => ?_, fun ν => ?_, fun ν n => ?_, fun ν n hn => ?_,
    fun ν n hn => ?_, ?_, ?_⟩
  · -- disjoint blocks of at most `m` changed slots
    obtain ⟨h₁, h₂⟩ := blockSlots_disjoint_union (B.pattern (famPoint B raw block Q w ξ ν).1)
      block g
    exact ⟨h₁, h₂ ▸ (B.pattern _).bound g⟩
  · -- no changed slots in small groups
    have : (B.pattern (famPoint B raw block Q w ξ ν).1).changed g = ∅ :=
      (B.pattern _).small g (by simpa [G, primeGroups] using hg)
    simp [blockSlots, this]
  · -- both blocks are changed
    obtain ⟨g, hg, hg'⟩ := (hcomp _ (hpt ν)).2.1 false
    obtain ⟨g', hg₂, hg₂'⟩ := (hcomp _ (hpt ν)).2.1 true
    exact ⟨⟨g.val, by beta_reduce; rwa [hside g ν false hg]⟩,
      ⟨g'.val, by beta_reduce; rwa [hside g' ν true hg₂]⟩⟩
  · exact ⟨norm_cellTest_le _ _ _ _, norm_cellTest_le _ _ _ _, norm_cellMark_le _ _ _ _,
      norm_cellMark_le _ _ _ _⟩
  · -- the auxiliary tests live in log cells
    unfold cellTest at hn
    by_cases hc : 0 < n ∧ cell w n = (famPoint B raw block Q w ξ ν).2.1
    · exact mem_cell hw₀ hw₁ hc.1 hc.2
    · exact absurd (ite_eq_right hc) hn
  · unfold cellTest at hn
    by_cases hc : 0 < n ∧ cell w n = (famPoint B raw block Q w ξ ν).2.2.2.1
    · exact mem_cell hw₀ hw₁ hc.1 hc.2
    · exact absurd (ite_eq_right hc) hn
  · -- the term weights
    refine (sum_norm_termWeight_family_le B raw block Q hξ hcoef hne hGV).trans ?_
    have hQ : (Q : ℝ) ≤ Real.log x ^ qexp := Nat.floor_le (by positivity)
    have hξ' : ξ⁻¹ = Real.log x ^ ξexp := by
      rw [hξdef, Real.rpow_neg hL₀.le, inv_inv]
    have hmass' : (B.model 1 0).patternMass ≤ Real.log x ^ C₁ := hmass
    have hpm : 0 ≤ (B.model 1 0).patternMass :=
      Finset.sum_nonneg fun v _ => sSup_norm_nonneg (B.pattern v)
    calc ξ⁻¹ ^ 2 * (Q : ℝ) ^ 4 * (B.model 1 0).patternMass
        ≤ (Real.log x ^ ξexp) ^ 2 * (Real.log x ^ qexp) ^ 4 * Real.log x ^ C₁ := by
          rw [hξ']
          exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hQ 4)
            (by positivity)) hmass' hpm (by positivity)
      _ = Real.log x ^ (C₁ + 2 * ξexp + 4 * qexp) := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hL₀.le,
            ← Real.rpow_mul hL₀.le, ← Real.rpow_add hL₀, ← Real.rpow_add hL₀]
          ring_nf
  · -- the transferred pairing
    intro ζ hζ X hX₁ hX₂ S S' f g hS hf hg hnf hng
    have hX : 0 ≤ X := (Real.sqrt_nonneg x).trans hX₁
    have hbound := hTPx G (B.model 1 ζ) X (targets (B.model 1 ζ) S') (extend S f)
      (fun z => g z.1.toNat) hadm hmass (by simp [Family.model])
      (by simp [Family.model, Erdos821.Blueprint.Graph.L, hL])
      (fun θ => hnorm θ ζ (hζ.trans (Real.rpow_le_rpow_of_exponent_le hL (le_max_left _ _))))
      (by rwa [← Real.sqrt_eq_rpow]) (by norm_num; exact_mod_cast hX₂) (fun n _ => ?_) ?_ ?_
    · rw [pairing_eq_family B raw block Q hξ hraw hraw' hcoef hGV ζ X S S' f g hS hg] at hbound
      refine hbound.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact Real.rpow_le_rpow_of_exponent_le hL (by linarith [le_max_left E 1])
    · unfold extend
      split_ifs
      · simpa using hf _
      · simp
    · unfold Erdos821.Blueprint.Graph.L
      rw [normOn_extend _ X S f hS, ← sqrt_rpow_two_mul hL₀.le, ← Real.sqrt_mul hX]
      exact Real.sqrt_le_sqrt hnf
    · unfold Erdos821.Blueprint.Graph.L
      rw [normOn_targets, ← sqrt_rpow_two_mul hL₀.le, ← Real.sqrt_mul hX]
      exact Real.sqrt_le_sqrt hng

end Erdos408
