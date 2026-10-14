import Erdos821.P3High.Assignments
import Erdos821.S2Gpar.GhostAnalyticParameters

/-! Assembly of the high-rank equality contribution: conditional rows from the literal
ghost/edge choices, the analytic ghost parameters, and the empty boundary mass. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3High

open Erdos821.Blueprint.Graph hiding BirthAddress EdgeChoice GhostChoice MemoryHistory
  TransferChoice TransferMode absoluteMemoryEdgeKernel absoluteMemoryGhostKernel
  absoluteScaledMemoryGhostKernel deleteMemoryIndices distinctMemoryExpression
  edgeChoiceCoefficient edgeChoiceValid edgeDelta edgeForward edgeSymmetryFactor freshBigFactor
  ghostBirthCount ghostChoiceValid ghostChoiceWeight ghostReversalFactor memoryEdgeKernel
  memoryEntry memoryGhostKernel permuteActive rawEdgeValid rawEdgeWeight retrievedIndices
  smallDamping smallOmega smallTargetFactor storedMemory transferModeAccept translateMemory
  translateParticle translateSmallResidues zeroBirthBatch zeroMemoryIndices
open Erdos821.S2Core Erdos821.P3Lowrank Erdos821.S2High

/-- The scalar absorption into `L ^ (Ch * (N + 1))`. -/
theorem scalar_absorb (ℓ CG Cv Ca IBM X : ℝ) (N : ℕ) (hℓ : 2 ≤ ℓ) (hCG : 0 ≤ CG)
    (hCGle : CG ≤ ℓ ^ Cv) (hIBM0 : 0 ≤ IBM) (hIBM : IBM ≤ 2) (hX : 0 ≤ X) :
    CG ^ (N + 1) * (ℓ ^ Ca) ^ N * IBM * X ≤
      ℓ ^ ((Cv + max Ca 0 + 1) * ((N + 1 : ℕ) : ℝ)) * X := by
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ1 : 1 ≤ ℓ := by linarith
  apply mul_le_mul_of_nonneg_right _ hX
  have h1 : CG ^ (N + 1) ≤ (ℓ ^ Cv) ^ (N + 1) := pow_le_pow_left₀ hCG hCGle _
  have hCa' : 1 ≤ ℓ ^ (max Ca 0) := Real.one_le_rpow hℓ1 (le_max_right _ _)
  have h2 : (ℓ ^ Ca) ^ N ≤ (ℓ ^ (max Ca 0)) ^ (N + 1) :=
    calc (ℓ ^ Ca) ^ N ≤ (ℓ ^ (max Ca 0)) ^ N :=
          pow_le_pow_left₀ (Real.rpow_nonneg hℓ0.le _)
            (Real.rpow_le_rpow_of_exponent_le hℓ1 (le_max_left _ _)) _
      _ ≤ (ℓ ^ (max Ca 0)) ^ (N + 1) := pow_le_pow_right₀ hCa' (Nat.le_succ N)
  have h3 : IBM ≤ ℓ ^ (N + 1) :=
    calc IBM ≤ 2 := hIBM
      _ ≤ ℓ := hℓ
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ (N + 1) := pow_le_pow_right₀ hℓ1 (by omega)
  have hpowexp : ℓ ^ ((Cv + max Ca 0 + 1) * ((N + 1 : ℕ) : ℝ)) =
      (ℓ ^ Cv) ^ (N + 1) * (ℓ ^ (max Ca 0)) ^ (N + 1) * ℓ ^ (N + 1) := by
    rw [Real.rpow_mul hℓ0.le, Real.rpow_natCast, Real.rpow_add hℓ0, Real.rpow_add hℓ0,
      Real.rpow_one, mul_pow, mul_pow]
  rw [hpowexp]
  have hA0 : 0 ≤ (ℓ ^ Cv) ^ (N + 1) := pow_nonneg (Real.rpow_nonneg hℓ0.le _) _
  have hB0 : 0 ≤ (ℓ ^ Ca) ^ N := pow_nonneg (Real.rpow_nonneg hℓ0.le _) _
  calc CG ^ (N + 1) * (ℓ ^ Ca) ^ N * IBM
      ≤ (ℓ ^ Cv) ^ (N + 1) * (ℓ ^ (max Ca 0)) ^ (N + 1) * ℓ ^ (N + 1) := by
        apply mul_le_mul (mul_le_mul h1 h2 hB0 hA0) h3 hIBM0
        exact mul_nonneg hA0 (pow_nonneg (Real.rpow_nonneg hℓ0.le _) _)

/-- The high-rank task, given the empty-boundary mass estimate. -/
theorem highRank_of_boundary (F : FixedData) (r : MemoryParameters F)
    (hBd : EmptyBoundaryMassTask) : HighRankMemoryTask F r := by
  intro hGR hEA m C₁
  obtain ⟨Cv, hCv0, xG, hxG⟩ := Erdos821.S2Gpar.GhostAnalyticParametersTask_proof F r
  obtain ⟨Ca, hCa⟩ := hEA m C₁
  refine ⟨Cv + max Ca 0 + 1, by positivity, ?_⟩
  intro J
  obtain ⟨xE, hxE⟩ := hCa J
  obtain ⟨xB, hxB⟩ := hBd F J
  have hc : 0 < F.c := lt_trans F.a_pos (lt_trans F.ab F.bc)
  have hvmin := F.vMin_pos
  have ev1 := Erdos821.S2Gpar.eventually_N_plus_one_le_half_exp F
  have hε : 0 < F.vMin / (4 * (J : ℝ) + 4) := by positivity
  have ev2 := Erdos821.S34Core.eventually_power_le_label_scale 0 F.c
    (F.vMin / (4 * (J : ℝ) + 4)) hc hε
  have ev3 : ∀ᶠ x : ℝ in atTop, (2 : ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 2
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 (ev1.and (ev2.and ev3))
  refine ⟨16 / F.vMin, div_pos (by norm_num) hvmin, max (max xG xE) (max xB x₁), ?_⟩
  intro x hx P hP A hA theta pi hpi
  have hxG' : x ≥ xG := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxE' : x ≥ xE := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxB' : x ≥ xB := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1' : x ≥ x₁ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hN, h2, hL2⟩ := hx₁ x hx1'
  have hL2' : (2 : ℝ) ≤ L x := hL2
  set E : ℝ := Real.exp ((L x) ^ F.c) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hcut : ((N x : ℕ) + 1 : ℝ) ≤ E / 2 := by
    have : ((N x : ℕ) : ℝ) + 1 ≤ (1 / 2) * Real.exp ((L x) ^ F.c) := hN
    rw [hEdef]
    linarith
  have h1E : (1 : ℝ) ≤ F.vMin / (4 * (J : ℝ) + 4) * E := by
    have h2' := h2
    simp only [Real.rpow_zero] at h2'
    simpa [Erdos821.Blueprint.Analytic.L, Erdos821.Blueprint.Graph.L, hEdef] using h2'
  have h4J : 4 * (J : ℝ) + 4 ≤ F.vMin * E := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h1E
    linarith
  have hsmall : (J : ℝ) * (2 / (F.vMin * E)) ≤ 1 / 2 := by
    rw [show (J : ℝ) * (2 / (F.vMin * E)) = 2 * J / (F.vMin * E) by ring,
      div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨hV, hbase, hsum2, hCvb⟩ := hxG x hxG' P hP
  have hmb := tiltedMu_group_mass_bounds F P x (N x) hP hcut
  have hμ : ∀ (g : P.BigGroup) (q : P.Prime g.val), 0 < tiltedMu F P (N x) g.val q :=
    fun g q => ((hmb g).1 q).1
  have hmass1 : ∀ g : P.BigGroup, 1 ≤ ∑ q : P.Prime g.val, tiltedMu F P (N x) g.val q :=
    fun g => (hmb g).2.1
  have hmassJ : ∀ (g : P.BigGroup) (forb : Finset (P.Prime g.val)), forb.card ≤ J →
      (1 / 2 : ℝ) ≤ ∑ q ∈ Finset.univ.filter (fun q => q ∉ forb), tiltedMu F P (N x) g.val q :=
    fun g forb hcard => tiltedMass_avoiding_finite_set_ge_half F P x (N x) hP hcut g forb J
      hcard hsmall
  set CG : ℝ := (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card with hCGdef
  have hCG0 : 0 ≤ CG := pow_nonneg (Real.exp_pos _).le _
  have hL0 : 0 < L x := by linarith
  have hCE0 : 0 ≤ (L x) ^ Ca := Real.rpow_nonneg hL0.le _
  have hG : ∀ (i : Fin (N x + 1)) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteScaledMemoryGhostKernel F J (N x) r.rho 1 i s t *
        P.memoryWeight r.v t) ∧
      (∑' t, absoluteScaledMemoryGhostKernel F J (N x) r.rho 1 i s t * P.memoryWeight r.v t) ≤
        CG * P.memoryWeight r.v s := by
    intro i s
    have h := hGR F P J (N x) r hV hbase hsum2 1 (Or.inl rfl) i s
    exact ⟨h.1, h.2.1⟩
  have hEw := hxE x hxE' P hP (majorantModel A)
    (by rw [majorantModel_patternMass]; exact hA) theta
  have hE : ∀ (i : Fin (N x)) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteMemoryEdgeKernel (majorantModel A) (N x) r.rho theta i .all s t *
        P.memoryWeight r.v t) ∧
      (∑' t, absoluteMemoryEdgeKernel (majorantModel A) (N x) r.rho theta i .all s t *
        P.memoryWeight r.v t) ≤ (L x) ^ Ca * P.memoryWeight r.v s := by
    intro i s
    have h := (hEw i).1 s
    have heq : (fun t => ‖((absoluteMemoryEdgeKernel (majorantModel A) (N x) r.rho theta i .all
        s t : ℝ) : ℂ)‖ * P.memoryWeight r.v t) =
        (fun t => absoluteMemoryEdgeKernel (majorantModel A) (N x) r.rho theta i .all s t *
          P.memoryWeight r.v t) := by
      funext t
      rw [Complex.norm_real, Real.norm_of_nonneg
        (Erdos821.P3Tail.edgeKernel_nonneg _ _ _ _ _ _ _)]
    rw [heq] at h
    exact h
  have hIBM := hxB x hxB' P hP m A
  have hIBM0 : 0 ≤ initialMemoryBoundaryMass A (N x) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hv : 1 ≤ r.v := r.v_gt.le
  have hY0 : 0 ≤ (16 / (F.vMin * E)) ^ birthRank pi := by positivity
  calc highRankHistoryExpression A (N x) (memoryCutoff x) r.rho theta pi
      ≤ ∑ values : PivotAssignment pi hpi, ∑' H : MemoryHistory A (N x),
          (if H.Valid ∧ H.Truncated (memoryCutoff x) ∧
              Prescribed (memoryCutoff x) H (performedAddressSet pi) (blockTarget pi hpi values)
            then ‖H.Weight r.rho theta‖ else 0) :=
        highRank_le_assign A (N x) (memoryCutoff x) r.rho theta pi hpi
    _ ≤ ∑ values : PivotAssignment pi hpi,
          CG ^ (N x + 1) * ((L x) ^ Ca) ^ (N x) * initialMemoryBoundaryMass A (N x) *
            ∏ j ∈ performedAddressSet pi, 2 * muHat F P (N x)
              (birthAddressGroup ((Fintype.equivFin _).symm j)) (blockTarget pi hpi values j) :=
        Finset.sum_le_sum fun values _ => prescribed_sum_le A (N x) (memoryCutoff x) r.rho theta
          r.v CG ((L x) ^ Ca) hv hCG0 hCE0 hμ hmass1 hmassJ hG hE (performedAddressSet pi)
          (blockTarget pi hpi values)
    _ = CG ^ (N x + 1) * ((L x) ^ Ca) ^ (N x) * initialMemoryBoundaryMass A (N x) *
          ∑ values : PivotAssignment pi hpi, ∏ j ∈ performedAddressSet pi, 2 * muHat F P (N x)
              (birthAddressGroup ((Fintype.equivFin _).symm j)) (blockTarget pi hpi values j) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ CG ^ (N x + 1) * ((L x) ^ Ca) ^ (N x) * initialMemoryBoundaryMass A (N x) *
          (16 / (F.vMin * E)) ^ birthRank pi :=
        mul_le_mul_of_nonneg_left (assign_sum_le x hP hcut pi hpi)
          (mul_nonneg (mul_nonneg (pow_nonneg hCG0 _) (pow_nonneg hCE0 _)) hIBM0)
    _ ≤ (L x) ^ ((Cv + max Ca 0 + 1) * ((N x + 1 : ℕ) : ℝ)) *
          (16 / (F.vMin * E)) ^ birthRank pi :=
        scalar_absorb (L x) CG Cv Ca (initialMemoryBoundaryMass A (N x)) _ (N x) hL2' hCG0 hCvb
          hIBM0 hIBM hY0
    _ = _ := by rw [div_div]

end Erdos821.P3High

