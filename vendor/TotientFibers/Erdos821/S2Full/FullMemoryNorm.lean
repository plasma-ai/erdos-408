import Erdos821.S2.FullNormTask
import Erdos821.S2.NormTailAssembly
import Erdos821.P3Rows.GhostRows
import Erdos821.P3Edge.Absolute

noncomputable section

namespace Erdos821.S2Full

open Erdos821.Blueprint.Graph

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem FullMemoryNormTask_proof (F : FixedData) (r : MemoryParameters F) :
    Erdos821.S2Core.FullMemoryNormTask F r := by
  intro hGA hBoundary hEdge hTruncated hAbsorb
  intro E hE
  have hEplus : 0 < E + 1 := by linarith
  obtain ⟨Cv, hCv, xg, hGx⟩ := hGA
  obtain ⟨Eid, hEid, hTruncatedAt⟩ := hTruncated (E + 1) hEplus
  refine ⟨Eid, hEid, ?_⟩
  intro m C₁
  obtain ⟨J₀, hJ₀⟩ := hTruncatedAt m C₁
  obtain ⟨Ca, hCa⟩ := hEdge m C₁
  refine ⟨J₀, ?_⟩
  intro J hJ C₂
  obtain ⟨xtr, hxtr⟩ := hJ₀ J hJ C₂
  obtain ⟨xa, hxa⟩ := hCa J
  obtain ⟨xb, hxb⟩ := hBoundary F J

  let Ccap : ℝ := F.C₀ * ((J + F.ell : ℕ) : ℝ)
  let Cpath : ℝ := Cv + max Ca 0 + 1
  have hJellNat : 0 < J + F.ell := by
    have hell := F.ell_pos
    omega
  have hJell : 0 < ((J + F.ell : ℕ) : ℝ) := by exact_mod_cast hJellNat
  have hCcap : 0 < Ccap := by
    dsimp [Ccap]
    exact mul_pos F.C₀_pos hJell
  have hCpath : 0 ≤ Cpath := by
    dsimp [Cpath]
    have : 0 ≤ max Ca 0 := le_max_right _ _
    linarith [hCv]
  obtain ⟨xtail, hxtail⟩ := hAbsorb Ccap Cpath (E + 1) hCcap hCpath hEplus

  have hL_atTop : Filter.Tendsto (fun x : ℝ => L x) Filter.atTop Filter.atTop := by
    simpa [L] using Real.tendsto_log_atTop
  obtain ⟨xscale, hxscale⟩ :=
    Filter.eventually_atTop.1 (hL_atTop.eventually_ge_atTop (2 : ℝ))

  let x3 : ℝ := max xtail xscale
  let x2 : ℝ := max xtr x3
  let x1 : ℝ := max xa x2
  let xlower : ℝ := max xb x1
  let x₀ : ℝ := max xg xlower
  refine ⟨x₀, ?_⟩
  intro x hx P hP A hA hk0 hk hId theta
  have hxlower : xlower ≤ x := (le_max_right xg xlower).trans hx
  have hx1 : x1 ≤ x := (le_max_right xb x1).trans hxlower
  have hx2 : x2 ≤ x := (le_max_right xa x2).trans hx1
  have hx3 : x3 ≤ x := (le_max_right xtr x3).trans hx2
  have hxg : xg ≤ x := (le_max_left xg xlower).trans hx
  have hxbx : xb ≤ x := (le_max_left xb x1).trans hxlower
  have hxax : xa ≤ x := (le_max_left xa x2).trans hx1
  have hxtrx : xtr ≤ x := (le_max_left xtr x3).trans hx2
  have hxtailx : xtail ≤ x := (le_max_left xtail xscale).trans hx3
  have hxscalex : xscale ≤ x := (le_max_right xtail xscale).trans hx3
  have hLtwo : 2 ≤ L x := hxscale x hxscalex
  have hLone : 1 ≤ L x := by linarith
  have hLpos : 0 < L x := by linarith
  have hNpos : 1 ≤ N x := by
    have hR : 1 ≤ R x := by
      dsimp [R]
      exact Nat.one_le_ceil_iff.mpr
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
          (Real.one_le_rpow hLone (by norm_num : (0 : ℝ) ≤ (52 : ℝ) / 100)))
    dsimp [N]
    omega
  have hNreal : 1 ≤ (N x : ℝ) := by exact_mod_cast hNpos

  obtain ⟨hV, hBase, hMu, hCGle⟩ := hGx x hxg P hP
  let CG : ℝ :=
    (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card
  let CE : ℝ := (L x) ^ Ca
  let Cedge : ℝ := max Ca 0
  let U : ℝ := (L x) ^ (-(E + 1) * (N x : ℝ))
  let V : ℝ := (L x) ^ (Cpath * (N x + 1 : ℕ))
  have hCG0 : 0 ≤ CG := by
    dsimp [CG]
    exact pow_nonneg (Real.exp_pos _).le _
  have hCE0 : 0 ≤ CE := by
    dsimp [CE]
    exact Real.rpow_nonneg hLpos.le _
  have hCedge0 : 0 ≤ Cedge := le_max_right _ _
  have hCGbound : CG ≤ (L x) ^ Cv := by
    simpa [CG] using hCGle
  have hCEbound : CE ≤ (L x) ^ Cedge := by
    dsimp [CE, Cedge]
    exact Real.rpow_le_rpow_of_exponent_le hLone (le_max_left Ca 0)
  have hVpos : ∀ g, 0 < P.V g ∧ P.V g ≤ F.vMax := hV
  have hBasepos : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      0 < baselinePrime F (N x) p.val := hBase
  have hMuBound : ∀ g : P.BigGroup,
      (∑ p : P.Prime g.val, tiltedMu F P (N x) g.val p) ≤ 2 := hMu

  have hGhostRows :
      ∀ (i : Fin (N x + 1)) (s : P.MemoryState (J + F.ell)),
        Summable (fun t =>
          Erdos821.S2Core.absoluteScaledMemoryGhostKernel F J (N x) r.rho 2 i s t *
            P.memoryWeight r.v t) ∧
        (∑' t,
          Erdos821.S2Core.absoluteScaledMemoryGhostKernel F J (N x) r.rho 2 i s t *
            P.memoryWeight r.v t) ≤ CG * P.memoryWeight r.v s := by
    intro i s
    have hrow := Erdos821.S2Core.GhostRowsTask_proof F P J (N x) r
      hV hBase hMu (2 : ℝ) (Or.inr rfl) i s
    exact ⟨hrow.1, by simpa [CG] using hrow.2.1⟩

  have hEdgeRows :
      ∀ (i : Fin (N x)) (s : P.MemoryState (J + F.ell)),
        Summable (fun t =>
          Erdos821.S2Core.absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t *
            P.memoryWeight r.v t) ∧
        (∑' t,
          Erdos821.S2Core.absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t *
            P.memoryWeight r.v t) ≤ CE * P.memoryWeight r.v s := by
    intro i s
    have hW : WeightedBounds (P.memoryMass F J (N x)) (P.memoryWeight r.v)
        (fun s t => (Erdos821.S2Core.absoluteMemoryEdgeKernel A (N x) r.rho theta i
          .all s t : ℂ)) ((L x) ^ Ca) := hxa x hxax P hP A hA theta i
    have hrow := hW.1 s
    have hnorm (t : P.MemoryState (J + F.ell)) :
        ‖(Erdos821.S2Core.absoluteMemoryEdgeKernel A (N x) r.rho theta i
          .all s t : ℂ)‖ =
          Erdos821.S2Core.absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t :=
      Erdos821.P3Edge.norm_cast_absolute A (N x) r.rho theta i s t
    refine ⟨?_, ?_⟩
    · simpa only [hnorm] using hrow.1
    · simpa only [hnorm, CE] using hrow.2

  have hboundary :
      Erdos821.S2Core.initialMemoryBoundaryMass A (N x) ≤ 2 := hxb x hxbx P hP m A
  let cap : ℕ := N x * ((J + F.ell) * Fintype.card P.BigGroup)
  have hcard : (Fintype.card P.BigGroup : ℝ) = (P.bigGroups.card : ℝ) := by
    congr 1
    simp only [PrimeGroups.bigGroups, Fintype.card_subtype]
  have hbig : (Fintype.card P.BigGroup : ℝ) ≤ F.C₀ * T x := by
    rw [hcard]
    exact hP.2.2.2.1
  have hcap : (cap : ℝ) ≤ Ccap * (N x : ℝ) * T x := by
    calc
      (cap : ℝ) = (N x : ℝ) * ((J + F.ell : ℕ) : ℝ) *
          (Fintype.card P.BigGroup : ℝ) := by
            simp [cap, Nat.cast_mul, Nat.cast_add, mul_assoc]
      _ ≤ (N x : ℝ) * ((J + F.ell : ℕ) : ℝ) * (F.C₀ * T x) :=
        mul_le_mul_of_nonneg_left hbig (by positivity)
      _ = Ccap * (N x : ℝ) * T x := by
        dsimp [Ccap]
        ring

  have hgain :
      (2 : ℝ) ^ (((N x * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) -
        (memoryCutoff x : ℤ)) * V ≤ U := by
    simpa [cap, U, V] using hxtail x hxtailx cap hcap

  have htrunc :
      ‖Erdos821.S2Core.truncatedDistinctMemoryExpression A (N x) (memoryCutoff x)
        r.rho theta‖ ≤ U := by
    simpa [U] using hxtr x hxtrx P hP A hA hk0 hk hId theta

  have hpathcost : CG ^ (N x + 1) * CE ^ (N x) *
      Erdos821.S2Core.initialMemoryBoundaryMass A (N x) ≤ V := by
    have hCGpow : CG ^ (N x + 1) ≤ ((L x) ^ Cv) ^ (N x + 1) :=
      pow_le_pow_left₀ hCG0 hCGbound _
    have hCEpow : CE ^ (N x) ≤ ((L x) ^ Cedge) ^ (N x) :=
      pow_le_pow_left₀ hCE0 hCEbound _
    have hproduct : CG ^ (N x + 1) * CE ^ (N x) ≤
        ((L x) ^ Cv) ^ (N x + 1) * ((L x) ^ Cedge) ^ (N x) :=
      mul_le_mul hCGpow hCEpow (pow_nonneg hCE0 _)
        (pow_nonneg (Real.rpow_nonneg hLpos.le _) _)
    have hpower : ((L x) ^ Cv) ^ (N x + 1) * ((L x) ^ Cedge) ^ (N x) =
        (L x) ^ (Cv * (N x + 1 : ℕ) + Cedge * (N x : ℝ)) := by
      rw [← Real.rpow_natCast ((L x) ^ Cv) (N x + 1),
        ← Real.rpow_natCast ((L x) ^ Cedge) (N x)]
      rw [← Real.rpow_mul hLpos.le Cv (N x + 1 : ℕ),
        ← Real.rpow_mul hLpos.le Cedge (N x : ℝ)]
      rw [← Real.rpow_add hLpos]
    have halpha :
        Cv * (N x + 1 : ℕ) + Cedge * (N x : ℝ) + 1 ≤
          Cpath * (N x + 1 : ℕ) := by
      change Cv * (N x + 1 : ℕ) + Cedge * (N x : ℝ) + 1 ≤
        (Cv + Cedge + 1) * (N x + 1 : ℕ)
      push_cast
      have hn : 0 ≤ (N x : ℝ) := Nat.cast_nonneg _
      nlinarith [hCedge0]
    have htwo :
        2 * (L x) ^ (Cv * (N x + 1 : ℕ) + Cedge * (N x : ℝ)) ≤ V := by
      calc
        2 * (L x) ^ (Cv * (N x + 1 : ℕ) + Cedge * (N x : ℝ)) ≤
            (L x) ^ (Cv * (N x + 1 : ℕ) + Cedge * (N x : ℝ) + 1) := by
          let alpha : ℝ := Cv * (N x + 1 : ℕ) + Cedge * (N x : ℝ)
          have hnonneg : 0 ≤ (L x) ^ alpha := Real.rpow_nonneg hLpos.le _
          have hmul : 2 * (L x) ^ alpha ≤ (L x) * (L x) ^ alpha :=
            mul_le_mul_of_nonneg_right hLtwo hnonneg
          have hpowadd : (L x) ^ alpha * (L x) = (L x) ^ (alpha + 1) := by
            simpa only [Real.rpow_one] using (Real.rpow_add hLpos alpha 1).symm
          calc
            _ = 2 * (L x) ^ alpha := by dsimp [alpha]
            _ ≤ (L x) * (L x) ^ alpha := hmul
            _ = (L x) ^ alpha * (L x) := by ring
            _ = (L x) ^ (alpha + 1) := hpowadd
            _ = _ := by dsimp [alpha]
        _ ≤ V := by
          dsimp [V]
          exact Real.rpow_le_rpow_of_exponent_le hLone halpha
    have hfac0 : 0 ≤ CG ^ (N x + 1) * CE ^ (N x) :=
      mul_nonneg (pow_nonneg hCG0 _) (pow_nonneg hCE0 _)
    calc
      CG ^ (N x + 1) * CE ^ (N x) *
          Erdos821.S2Core.initialMemoryBoundaryMass A (N x) ≤
        CG ^ (N x + 1) * CE ^ (N x) * 2 :=
          mul_le_mul_of_nonneg_left hboundary hfac0
      _ = 2 * (CG ^ (N x + 1) * CE ^ (N x)) := by ring
      _ ≤ 2 * (((L x) ^ Cv) ^ (N x + 1) * ((L x) ^ Cedge) ^ (N x)) :=
        mul_le_mul_of_nonneg_left hproduct (by norm_num)
      _ = 2 * (L x) ^ (Cv * (N x + 1 : ℕ) + Cedge * (N x : ℝ)) := by rw [hpower]
      _ ≤ V := htwo

  have hfull := Erdos821.S2Core.full_memory_norm_le_two A (N x) (memoryCutoff x)
    r.rho r.v theta CG CE U V (by linarith [r.v_gt]) hCG0 hCE0 hGhostRows hEdgeRows
    htrunc hpathcost hgain

  have hLpow : 2 ≤ (L x) ^ (N x : ℝ) := by
    calc
      2 ≤ L x := hLtwo
      _ = (L x) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (L x) ^ (N x : ℝ) := Real.rpow_le_rpow_of_exponent_le hLone hNreal
  have hinv : (L x) ^ (-(N x : ℝ)) ≤ (1 / 2 : ℝ) := by
    rw [Real.rpow_neg hLpos.le]
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hLpow)
  have habsorb : 2 * U ≤ (L x) ^ (-E * (N x : ℝ)) := by
    have hexp : -(E + 1) * (N x : ℝ) =
        -E * (N x : ℝ) + (-(N x : ℝ)) := by ring
    change 2 * (L x) ^ (-(E + 1) * (N x : ℝ)) ≤ _
    rw [hexp, Real.rpow_add hLpos]
    calc
      2 * ((L x) ^ (-E * (N x : ℝ)) * (L x) ^ (-(N x : ℝ))) =
          (L x) ^ (-E * (N x : ℝ)) *
            (2 * (L x) ^ (-(N x : ℝ))) := by ring
      _ ≤ (L x) ^ (-E * (N x : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left (by nlinarith [hinv])
          (Real.rpow_nonneg hLpos.le _)
      _ = (L x) ^ (-E * (N x : ℝ)) := by ring
  exact hfull.trans habsorb


example : type_of% @FullMemoryNormTask_proof =
    ∀ (F : FixedData) (r : MemoryParameters F), Erdos821.S2Core.FullMemoryNormTask F r := rfl

end Erdos821.S2Full
