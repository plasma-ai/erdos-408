import Erdos821.S2.TransferenceAssemblyTask
import Erdos821.S2.MemoryParameters
import Erdos821.S2.RootMemoryBound
import Erdos821.S2.NormTailAssembly
import Erdos821.P3Rows.GhostRows
import Erdos821.P3Edge.Absolute

noncomputable section

open Filter
open Erdos821.Blueprint.Graph hiding absoluteMemoryEdgeKernel absoluteMemoryGhostKernel
  absoluteScaledMemoryGhostKernel deleteMemoryIndices ghostBirthCount ghostChoiceValid
  ghostChoiceWeight ghostReversalFactor memoryEntry memoryGhostKernel residueExpression
  zeroBirthBatch zeroMemoryIndices

namespace Erdos821.S2Ltrans

private theorem rpow_nat_power (x a : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (x ^ a) ^ n = x ^ (a * (n : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

theorem LocalTransferenceAssemblyTask_proof :
    Erdos821.S2Core.LocalTransferenceAssemblyTask := by
  intro inputs F E hE
  obtain ⟨r⟩ := Erdos821.Blueprint.Graph.memory_parameters_exist_proof F
  have hEplus : 0 < E + 1 := by linarith
  obtain ⟨Eid, hEid, hFull⟩ := inputs.fullMemory F r (E + 1) hEplus
  refine ⟨Eid, hEid, ?_⟩
  intro m C₁
  obtain ⟨J₀, hJ₀⟩ := hFull m C₁
  refine ⟨J₀, ?_⟩
  intro J hJJ C₂ γ hγ
  obtain ⟨xMem, hMem⟩ := hJ₀ J hJJ C₂
  obtain ⟨Cv, hCv, xGhost, hGhost⟩ := inputs.ghostParameters F r
  obtain ⟨Ca, hCa⟩ := inputs.absoluteEdge F r m C₁
  obtain ⟨xEdge, hEdge⟩ := hCa J
  obtain ⟨xNondiv, hNondiv⟩ := inputs.nondiv F C₂
  obtain ⟨xBoundary, hBoundary⟩ := inputs.emptyBoundary F J

  let Cpath : ℝ := Cv + max Ca 0 + 1
  let Acrt : ℝ := 2 * Cpath + E + 4
  have hCpath : 0 ≤ Cpath := by dsimp [Cpath]; positivity
  have hAcrt : 0 < Acrt := by dsimp [Acrt]; linarith
  obtain ⟨xCRT, hCRT⟩ := inputs.crt F J Acrt γ hAcrt hγ

  have hLlarge : ∀ᶠ x : ℝ in atTop, 2 ≤ L x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 2
  obtain ⟨xLog, hLog⟩ := Filter.eventually_atTop.1 hLlarge
  have hAllLarge : ∀ᶠ x : ℝ in atTop,
      xMem ≤ x ∧ xGhost ≤ x ∧ xEdge ≤ x ∧ xNondiv ≤ x ∧ xBoundary ≤ x ∧
        xCRT ≤ x ∧ xLog ≤ x := by
    filter_upwards [eventually_ge_atTop xMem, eventually_ge_atTop xGhost,
      eventually_ge_atTop xEdge, eventually_ge_atTop xNondiv,
      eventually_ge_atTop xBoundary, eventually_ge_atTop xCRT,
      eventually_ge_atTop xLog] with x hMemX hGhostX hEdgeX hNondivX hBoundaryX hCRTX hLogX
    exact ⟨hMemX, hGhostX, hEdgeX, hNondivX, hBoundaryX, hCRTX, hLogX⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hAllLarge
  refine ⟨x₀, ?_⟩
  intro x hx P hP A hPattern hk hkBound hIdeal X hXlo hXhi
  rcases hx₀ x hx with ⟨hxMem, hxGhost, hxEdge, hxNondiv, hxBoundary, hxCRT, hxLog⟩
  have hL2 : 2 ≤ L x := hLog x hxLog
  have hLpos : 0 < L x := lt_of_lt_of_le (by norm_num) hL2
  have hLone : 1 ≤ L x := by linarith
  let n : ℕ := N x
  have hRpos : 0 < R x := by
    unfold R
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hLpos _)
  have hn : 0 < n := by
    dsimp [n, N]
    omega
  have hnReal : 1 ≤ (n : ℝ) := by exact_mod_cast hn

  have hMemAt := hMem x hxMem P hP A hPattern hk hkBound hIdeal
  rcases hGhost x hxGhost P hP with ⟨hV, hBaseline, hTilted, hGhostScale⟩
  have hNotDiv : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      ¬ (p.val : ℤ) ∣ A.k :=
    hNondiv x hxNondiv P hP A.k hk hkBound
  have hVne : ∀ g, P.V g ≠ 0 := fun g => (hV g).1.ne'
  have hBaselineNe : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      baselinePrime F n p.val ≠ 0 := fun g p => (hBaseline g p).ne'
  have hBaselineNonneg : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      0 ≤ baselinePrime F n p.val := fun g p => (hBaseline g p).le
  have hIdentity : ∀ theta : ℝ,
      Erdos821.S2Core.residueExpression A n theta =
        (bigBaseline F P n : ℂ) * Erdos821.S2Core.distinctMemoryExpression A n r.rho theta := by
    intro theta
    exact Erdos821.S2Core.memory_identity_of_tasks inputs.structureProofs
      inputs.ghostWeights inputs.markWeights inputs.spanSum inputs.residues A n hn
      hNotDiv hVne hBaselineNe r.rho theta r.rho_pos.ne'
  have hClosed :
      ‖Erdos821.S2Core.closedResidueExpression A n‖ ≤ (L x) ^ (-(E + 1) * (n : ℝ)) :=
    Erdos821.S2Core.closedResidueExpression_norm_le_memory_bound A n r.rho
      ((L x) ^ (-(E + 1) * (n : ℝ))) hIdentity hBaselineNonneg (by simpa [n] using hMemAt)

  obtain ⟨hVbound, hBase, hTiltedBound, hCGscale⟩ :=
    hGhost x hxGhost P hP
  let CG : ℝ := (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card
  let CE : ℝ := (L x) ^ Ca
  have hCGnn : 0 ≤ CG := by dsimp [CG]; positivity
  have hCEnn : 0 ≤ CE := by dsimp [CE]; positivity
  have hCEpos : 0 < CE := by dsimp [CE]; exact Real.rpow_pos_of_pos hLpos _
  have hCGscale : CG ≤ (L x) ^ Cv := by dsimp [CG]; exact hCGscale
  have hCEscale : CE ≤ (L x) ^ max Ca 0 := by
    dsimp [CE]
    exact Real.rpow_le_rpow_of_exponent_le hLone (le_max_left Ca 0)
  have hGRows : ∀ (i : Fin (n + 1)) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => Erdos821.S2Core.absoluteScaledMemoryGhostKernel F J n r.rho 2 i s t *
        P.memoryWeight r.v t) ∧
      (∑' t, Erdos821.S2Core.absoluteScaledMemoryGhostKernel F J n r.rho 2 i s t *
        P.memoryWeight r.v t) ≤ CG * P.memoryWeight r.v s := by
    intro i s
    have hrows := Erdos821.S2Core.GhostRowsTask_proof F P J n r hVbound hBase
      hTiltedBound 2 (Or.inr rfl) i s
    exact ⟨hrows.1, hrows.2.1⟩
  have hEdgeWB : ∀ (i : Fin n), WeightedBounds (P.memoryMass F J n) (P.memoryWeight r.v)
      (fun s t => (Erdos821.S2Core.absoluteMemoryEdgeKernel A n r.rho 0 i .all s t : ℂ)) CE := by
    intro i
    simpa [n, CE] using hEdge x hxEdge P hP A hPattern 0 i
  have hERows : ∀ (i : Fin n) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => Erdos821.S2Core.absoluteMemoryEdgeKernel A n r.rho 0 i .all s t *
        P.memoryWeight r.v t) ∧
      (∑' t, Erdos821.S2Core.absoluteMemoryEdgeKernel A n r.rho 0 i .all s t *
        P.memoryWeight r.v t) ≤ CE * P.memoryWeight r.v s := by
    intro i s
    have hrow := ((hEdgeWB i).1 s)
    simpa only [Erdos821.P3Edge.norm_cast_absolute] using hrow
  have hBoundaryMass : Erdos821.S2Core.initialMemoryBoundaryMass A n ≤ 2 :=
    hBoundary x hxBoundary P hP m A
  have hAbsRoot : Erdos821.S2Core.closedAbsoluteResidueExpression A n ≤
      CG ^ (n + 1) * CE ^ n * Erdos821.S2Core.initialMemoryBoundaryMass A n :=
    inputs.absoluteRoot inputs.structureProofs inputs.ghostWeights inputs.markWeights
      inputs.spanSum inputs.residues F P J m n A hn hNotDiv hVne hBaseline
      r.rho r.v CG CE r.rho_pos.ne' (by linarith [r.v_gt]) hCGnn hCEnn hGRows hERows

  have hMassNonneg : 0 ≤ Erdos821.S2Core.initialMemoryBoundaryMass A n := by
    unfold Erdos821.S2Core.initialMemoryBoundaryMass
    positivity
  have hCaPos : 0 ≤ max Ca 0 := le_max_right _ _
  have hLpow : (2 : ℝ) ≤ (L x) ^ ((n + 1 : ℕ) : ℝ) := by
    have hExp : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    calc
      2 ≤ L x := hL2
      _ = (L x) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (L x) ^ ((n + 1 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hLone hExp
  have hCostBound : CG ^ (n + 1) * CE ^ n * Erdos821.S2Core.initialMemoryBoundaryMass A n ≤
      (L x) ^ (Cpath * ((n + 1 : ℕ) : ℝ)) := by
    have hCGpow : CG ^ (n + 1) ≤ ((L x) ^ Cv) ^ (n + 1) :=
      pow_le_pow_left₀ hCGnn hCGscale _
    have hCEpow : CE ^ n ≤ ((L x) ^ max Ca 0) ^ n :=
      pow_le_pow_left₀ hCEnn hCEscale _
    have hfac : 0 ≤ ((L x) ^ Cv) ^ (n + 1) * ((L x) ^ max Ca 0) ^ n := by
      positivity
    calc
      _ ≤ ((L x) ^ Cv) ^ (n + 1) * CE ^ n *
          Erdos821.S2Core.initialMemoryBoundaryMass A n := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCGpow (pow_nonneg hCEnn _)) hMassNonneg
      _ ≤ ((L x) ^ Cv) ^ (n + 1) * ((L x) ^ max Ca 0) ^ n *
          Erdos821.S2Core.initialMemoryBoundaryMass A n := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCEpow (pow_nonneg (Real.rpow_nonneg hLpos.le _) _))
          hMassNonneg
      _ ≤ ((L x) ^ Cv) ^ (n + 1) * ((L x) ^ max Ca 0) ^ n *
          (L x) ^ ((n + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (hBoundaryMass.trans hLpow) hfac
      _ = (L x) ^ (Cv * ((n + 1 : ℕ) : ℝ)) *
          (L x) ^ (max Ca 0 * (n : ℝ)) * (L x) ^ ((n + 1 : ℕ) : ℝ) := by
        rw [rpow_nat_power (L x) Cv hLpos.le (n + 1),
          rpow_nat_power (L x) (max Ca 0) hLpos.le n]
      _ = (L x) ^ (Cv * ((n + 1 : ℕ) : ℝ) + max Ca 0 * (n : ℝ) +
          ((n + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
      _ ≤ (L x) ^ (Cpath * ((n + 1 : ℕ) : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hLone
        have hnle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ n
        dsimp [Cpath]
        push_cast
        nlinarith [mul_nonneg hCaPos (Nat.cast_nonneg n)]

  have hAbsBound : Erdos821.S2Core.closedAbsoluteResidueExpression A n ≤
      (L x) ^ (Cpath * ((n + 1 : ℕ) : ℝ)) := hAbsRoot.trans hCostBound
  let epsilon : ℝ := Real.exp (-Acrt * (n : ℝ) * T x)
  have hEpsilonNonneg : 0 ≤ epsilon := by dsimp [epsilon]; positivity
  have hEpsilonEq : epsilon = (L x) ^ (-Acrt * (n : ℝ)) := by
    rw [Real.rpow_def_of_pos hLpos]
    dsimp [epsilon, Acrt, T, L]
    congr 1
    ring
  have hError : epsilon * (L x) ^ (Cpath * ((n + 1 : ℕ) : ℝ)) ≤
      (L x) ^ (-(E + 1) * (n : ℝ)) := by
    calc
      _ = (L x) ^ (-Acrt * (n : ℝ)) *
          (L x) ^ (Cpath * ((n + 1 : ℕ) : ℝ)) := by rw [hEpsilonEq]
      _ = (L x) ^ (-Acrt * (n : ℝ) + Cpath * ((n + 1 : ℕ) : ℝ)) :=
        (Real.rpow_add hLpos _ _).symm
      _ ≤ (L x) ^ (-(E + 1) * (n : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hLone
        have hnplus : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
          push_cast
          linarith [hnReal]
        calc
          -Acrt * (n : ℝ) + Cpath * ((n + 1 : ℕ) : ℝ)
              ≤ -Acrt * (n : ℝ) + Cpath * (2 * (n : ℝ)) := by
                  have hCterm := mul_le_mul_of_nonneg_left hnplus hCpath
                  linarith
          _ = (-Acrt + 2 * Cpath) * (n : ℝ) := by ring
          _ ≤ -(E + 1) * (n : ℝ) := by
            have hcoef : -Acrt + 2 * Cpath ≤ -(E + 1) := by
              dsimp [Acrt]
              linarith
            exact mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n)

  have hreplacement : ∀ Q : Erdos821.S2Core.ResiduePath A (2 * R x), Q.Valid →
      |((dyad X).card : ℝ)⁻¹ * ∑ z ∈ dyad X,
          P.pathFactor (2 * R x) (visitQ F.q (2 * R x)) Q.offset Q.active z -
        P.residueExpectation (2 * R x) (visitQ F.q (2 * R x)) Q.offset Q.active| ≤
      epsilon * P.residueExpectation (2 * R x) (visitQ F.q (2 * R x)) Q.offset Q.active := by
    intro Q hQ
    have hActive : ∀ i, Q.active i ⊆ P.allPrimes ∧
        (Q.active i).card ≤ (J + F.ell) * P.count :=
      fun i => ⟨Q.active_subset i, Q.active_card_le i⟩
    exact hCRT x hxCRT P hP Q.offset Q.active hActive X hXlo hXhi
  have hMoment := Erdos821.S2Core.averagedMoment_le_of_bounds inputs.physicalPaths
    A (R x) hRpos X epsilon
    ((L x) ^ (-(E + 1) * (n : ℝ)))
    ((L x) ^ (Cpath * ((n + 1 : ℕ) : ℝ))) hEpsilonNonneg hreplacement
    (by simpa [n, N] using hClosed) (by simpa [n, N] using hAbsBound)
  have hTwoScale : 2 * (L x) ^ (-(E + 1) * (n : ℝ)) ≤
      (L x) ^ (-E * (n : ℝ)) := by
    calc
      2 * (L x) ^ (-(E + 1) * (n : ℝ)) ≤
          (L x) ^ (n : ℝ) * (L x) ^ (-(E + 1) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (by
            have : (2 : ℝ) ≤ (L x) ^ (n : ℝ) := by
              calc
                2 ≤ L x := hL2
                _ = (L x) ^ (1 : ℝ) := (Real.rpow_one _).symm
                _ ≤ (L x) ^ (n : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hLone hnReal
            exact this)
          (Real.rpow_nonneg hLpos.le _)
      _ = (L x) ^ (-(E + 1) * (n : ℝ) + (n : ℝ)) := by
        rw [← Real.rpow_add hLpos]
        congr 1
        ring
      _ = (L x) ^ (-E * (n : ℝ)) := by
        congr 1
        ring
  have hMomentFinal : A.averagedMoment (R x) X ≤ (L x) ^ (-E * (n : ℝ)) := by
    calc
      A.averagedMoment (R x) X ≤ (L x) ^ (-(E + 1) * (n : ℝ)) +
          epsilon * (L x) ^ (Cpath * ((n + 1 : ℕ) : ℝ)) := hMoment
      _ ≤ 2 * (L x) ^ (-(E + 1) * (n : ℝ)) := by
        have := hError
        linarith
      _ ≤ (L x) ^ (-E * (n : ℝ)) := hTwoScale
  have hdec : (52 : ℝ) / 100 = (0.52 : ℝ) := by norm_num
  simpa [Model.averageMoment, Model.averagedMoment, R, N, dyad, hdec,
    div_eq_mul_inv, mul_comm, n] using hMomentFinal

example : Erdos821.S2Core.LocalTransferenceAssemblyTask :=
  LocalTransferenceAssemblyTask_proof


end Erdos821.S2Ltrans
