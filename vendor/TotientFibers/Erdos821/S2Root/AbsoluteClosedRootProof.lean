import Erdos821.S2Root.AbsoluteClosedRoot
import Erdos821.S2.RootMemoryBound

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Root

open Erdos821.Blueprint.Graph
  hiding MemoryHistory ResiduePath TransferMode absoluteMemoryEdgeKernel
    absoluteScaledMemoryGhostKernel
open Erdos821.S2Core

private theorem memoryHistory_norm_le_doubledWeight
    {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
    (H : MemoryHistory A n) (rho theta : ℝ) (hH : H.Valid) :
    ‖H.Weight rho theta‖ ≤ Erdos821.P3Tail.doubledWeight H rho theta := by
  have hp : 1 ≤ (2 : ℝ) ^ H.totalGhostBirths := one_le_pow₀ (by norm_num)
  calc
    ‖H.Weight rho theta‖ = ‖H.Weight rho theta‖ * 1 := (mul_one _).symm
    _ ≤ ‖H.Weight rho theta‖ * (2 : ℝ) ^ H.totalGhostBirths :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = Erdos821.P3Tail.doubledWeight H rho theta :=
      Erdos821.P3Tail.norm_weight_mul_pow H rho theta hH

private theorem reconstructed_batch_norm_sum
    {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
    (Q : ResiduePath A n) (S : LifespanAssignment P n) (hS : Q.lifespanValid S)
    (y : P.SmallResidues) (rho theta : ℝ) :
    (∑ sigma : (Q.reconstructedHistory S hS y).BatchOrders,
      ‖((Q.reconstructedHistory S hS y).reorderBatches sigma).Weight rho theta‖) =
      (∏ i : Fin (n + 1), ∏ g : P.BigGroup,
        ((Q.ghostBirthPrimes S i g).card.factorial : ℝ)) *
        ‖(Q.reconstructedHistory S hS y).Weight rho theta‖ := by
  let H := Q.reconstructedHistory S hS y
  have hweight (sigma : H.BatchOrders) :
      ‖(H.reorderBatches sigma).Weight rho theta‖ = ‖H.Weight rho theta‖ := by
    rw [H.reorderBatches_weight]
  have hcardNat : Fintype.card H.BatchOrders =
      ∏ i : Fin (n + 1), ∏ g : P.BigGroup,
        (Q.ghostBirthPrimes S i g).card.factorial := by
    rw [H.batchOrders_card]
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro g hg
    simp [H, ResiduePath.reconstructedHistory, ResiduePath.reconstructedGhostChoice]
  calc
    _ = ∑ sigma : H.BatchOrders, ‖H.Weight rho theta‖ :=
      Finset.sum_congr rfl (fun sigma _ => hweight sigma)
    _ = (Fintype.card H.BatchOrders : ℝ) * ‖H.Weight rho theta‖ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = _ := by
      rw [hcardNat]
      push_cast
      rfl

private theorem path_norm_le_configuration_fiber
    {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
    (hGhost : SpanGhostWeightTask) (hMark : SpanMarkWeightTask) (hSpan : SpanSumTask)
    (hRes : ResidueFactorizationTask)
    (hn : 0 < n)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (hV : ∀ g, P.V g ≠ 0)
    (hbp : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (rho : ℝ) (hrho : rho ≠ 0)
    (Q : {Q : ResiduePath A n // Q.Valid}) :
    ‖Q.val.Weight 0‖ ≤
      ∑ S : {S : LifespanAssignment P n // Q.val.lifespanValid S},
        ∑ y : {y : P.SmallResidues // Q.val.SmallCompatible y},
          ∑ sigma : (Q.val.reconstructedHistory S.val S.property y.val).BatchOrders,
            ‖((Q.val.reconstructedHistory S.val S.property y.val).reorderBatches sigma).Weight
              rho 0‖ := by
  have hbpne : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      baselinePrime F n p.val ≠ 0 := fun g p => (hbp g p).ne'
  have hId := Q.val.memory_fiber_sum hGhost hMark hSpan hRes hn Q.property hk hV hbpne
    rho 0 hrho
  have hbase : ‖(bigBaseline F P n : ℂ)‖ ≤ 1 :=
    bigBaseline_norm_le_one F P n (fun g p => (hbp g p).le)
  have htriangle :
      ‖∑ S : {S : LifespanAssignment P n // Q.val.lifespanValid S},
          ∑ y : {y : P.SmallResidues // Q.val.SmallCompatible y},
            ((∏ i : Fin (n + 1), ∏ g : P.BigGroup,
              (Q.val.ghostBirthPrimes S.val i g).card.factorial : ℕ) : ℂ) *
              (Q.val.reconstructedHistory S.val S.property y.val).Weight rho 0‖ ≤
        ∑ S : {S : LifespanAssignment P n // Q.val.lifespanValid S},
          ∑ y : {y : P.SmallResidues // Q.val.SmallCompatible y},
            ((∏ i : Fin (n + 1), ∏ g : P.BigGroup,
              (Q.val.ghostBirthPrimes S.val i g).card.factorial : ℝ) *
              ‖(Q.val.reconstructedHistory S.val S.property y.val).Weight rho 0‖) := by
    calc
      _ ≤ ∑ S : {S : LifespanAssignment P n // Q.val.lifespanValid S},
            ‖∑ y : {y : P.SmallResidues // Q.val.SmallCompatible y},
              ((∏ i : Fin (n + 1), ∏ g : P.BigGroup,
                (Q.val.ghostBirthPrimes S.val i g).card.factorial : ℕ) : ℂ) *
                (Q.val.reconstructedHistory S.val S.property y.val).Weight rho 0‖ :=
          norm_sum_le _ _
      _ ≤ ∑ S : {S : LifespanAssignment P n // Q.val.lifespanValid S},
            ∑ y : {y : P.SmallResidues // Q.val.SmallCompatible y},
              ‖((∏ i : Fin (n + 1), ∏ g : P.BigGroup,
                (Q.val.ghostBirthPrimes S.val i g).card.factorial : ℕ) : ℂ) *
                (Q.val.reconstructedHistory S.val S.property y.val).Weight rho 0‖ :=
          Finset.sum_le_sum fun S _ => norm_sum_le _ _
      _ = _ := by
          apply Finset.sum_congr rfl
          intro S hS
          apply Finset.sum_congr rfl
          intro y hy
          rw [norm_mul, Complex.norm_natCast]
          push_cast
          rfl
  have hsigma :
      ∑ S : {S : LifespanAssignment P n // Q.val.lifespanValid S},
        ∑ y : {y : P.SmallResidues // Q.val.SmallCompatible y},
          ((∏ i : Fin (n + 1), ∏ g : P.BigGroup,
            (Q.val.ghostBirthPrimes S.val i g).card.factorial : ℝ) *
            ‖(Q.val.reconstructedHistory S.val S.property y.val).Weight rho 0‖) =
      ∑ S : {S : LifespanAssignment P n // Q.val.lifespanValid S},
        ∑ y : {y : P.SmallResidues // Q.val.SmallCompatible y},
          ∑ sigma : (Q.val.reconstructedHistory S.val S.property y.val).BatchOrders,
            ‖((Q.val.reconstructedHistory S.val S.property y.val).reorderBatches sigma).Weight
              rho 0‖ := by
    apply Finset.sum_congr rfl
    intro S hS
    apply Finset.sum_congr rfl
    intro y hy
    exact (reconstructed_batch_norm_sum Q.val S.val S.property y.val rho 0).symm
  calc
    ‖Q.val.Weight 0‖ =
        ‖(bigBaseline F P n : ℂ) *
          (∑ S : {S : LifespanAssignment P n // Q.val.lifespanValid S},
            ∑ y : {y : P.SmallResidues // Q.val.SmallCompatible y},
              ((∏ i : Fin (n + 1), ∏ g : P.BigGroup,
                (Q.val.ghostBirthPrimes S.val i g).card.factorial : ℕ) : ℂ) *
                (Q.val.reconstructedHistory S.val S.property y.val).Weight rho 0)‖ := by
          rw [← hId]
    _ = ‖(bigBaseline F P n : ℂ)‖ *
          ‖∑ S : {S : LifespanAssignment P n // Q.val.lifespanValid S},
            ∑ y : {y : P.SmallResidues // Q.val.SmallCompatible y},
              ((∏ i : Fin (n + 1), ∏ g : P.BigGroup,
                (Q.val.ghostBirthPrimes S.val i g).card.factorial : ℕ) : ℂ) *
                (Q.val.reconstructedHistory S.val S.property y.val).Weight rho 0‖ := norm_mul _ _
    _ ≤ 1 * ‖∑ S : {S : LifespanAssignment P n // Q.val.lifespanValid S},
            ∑ y : {y : P.SmallResidues // Q.val.SmallCompatible y},
              ((∏ i : Fin (n + 1), ∏ g : P.BigGroup,
                (Q.val.ghostBirthPrimes S.val i g).card.factorial : ℕ) : ℂ) *
                (Q.val.reconstructedHistory S.val S.property y.val).Weight rho 0‖ :=
          mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
    _ = _ := one_mul _
    _ ≤ _ := htriangle.trans_eq hsigma

private theorem validHistory_norm_sum_le_doubled_bound
    {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
    (rho v CG CE : ℝ) (hv : 1 ≤ v) (hCG : 0 ≤ CG) (hCE : 0 ≤ CE)
    (hG : ∀ (i : Fin (n + 1)) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteScaledMemoryGhostKernel F J n rho 2 i s t *
        P.memoryWeight v t) ∧
      (∑' t, absoluteScaledMemoryGhostKernel F J n rho 2 i s t *
        P.memoryWeight v t) ≤ CG * P.memoryWeight v s)
    (hE : ∀ (i : Fin n) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteMemoryEdgeKernel A n rho 0 i .all s t *
        P.memoryWeight v t) ∧
      (∑' t, absoluteMemoryEdgeKernel A n rho 0 i .all s t *
        P.memoryWeight v t) ≤ CE * P.memoryWeight v s) :
    (∑ H : ValidDistinctHistory A n, ‖H.val.Weight rho 0‖) ≤
      CG ^ (n + 1) * CE ^ n * initialMemoryBoundaryMass A n := by
  classical
  let S : Finset (MemoryHistory A n) := Finset.univ.image (fun H : ValidDistinctHistory A n => H.val)
  have hS : ∀ H ∈ S, H.Valid := by
    intro H hH
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
    exact K.property.1
  have hsum :
      (∑ H : ValidDistinctHistory A n,
        Erdos821.P3Tail.doubledWeight H.val rho 0) =
      ∑ H ∈ S, Erdos821.P3Tail.doubledWeight H rho 0 := by
    unfold S
    symm
    rw [Finset.sum_image (fun H _ K _ h => Subtype.ext h)]
  calc
    _ ≤ ∑ H : ValidDistinctHistory A n,
          Erdos821.P3Tail.doubledWeight H.val rho 0 :=
        Finset.sum_le_sum fun H _ =>
          memoryHistory_norm_le_doubledWeight H.val rho 0 H.property.1
    _ = ∑ H ∈ S, Erdos821.P3Tail.doubledWeight H rho 0 := hsum
    _ ≤ CG ^ (n + 1) * CE ^ n * initialMemoryBoundaryMass A n :=
      Erdos821.P3Tail.finite_doubled_sum_le A n rho 0 v CG CE hv hCG hCE hG hE S hS

theorem AbsoluteClosedRootTask_proof : AbsoluteClosedRootTask := by
  intro hStructure hGhost hMark hSpan hRes
  intro F P J m n A hn hk hV hbp rho v CG CE hrho hv hCG hCE hG hE
  have hClosedTerm (Q : ResiduePath A n) :
      ‖closedPathCoefficient A n Q‖ *
          P.residueExpectation n (visitQ F.q n) Q.offset Q.active =
        if Q.Valid then
          if Q.offset (Fin.last n) = 0 then ‖Q.Weight 0‖ else 0
        else 0 := by
    by_cases hQ : Q.Valid
    · by_cases hc : Q.offset (Fin.last n) = 0
      · have hW : Q.Weight 0 =
            (closedPathCoefficient A n Q : ℂ) *
              (P.residueExpectation n (visitQ F.q n) Q.offset Q.active : ℂ) := by
          simp [Erdos821.S2Core.ResiduePath.Weight, closedPathCoefficient, hQ, hc]
        rw [hW]
        simp only [if_pos hQ, if_pos hc, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (residueExpectation_visitQ_nonneg Q)]
      · simp [closedPathCoefficient, hQ, hc]
    · simp [closedPathCoefficient, hQ]
  have hClosedSum :
      closedAbsoluteResidueExpression A n =
        ∑ Q : {Q : ResiduePath A n // Q.Valid},
          if Q.val.offset (Fin.last n) = 0 then ‖Q.val.Weight 0‖ else 0 := by
    unfold closedAbsoluteResidueExpression
    calc
      _ = ∑ Q : ResiduePath A n,
            if Q.Valid then
              if Q.offset (Fin.last n) = 0 then ‖Q.Weight 0‖ else 0
            else 0 := Finset.sum_congr rfl (fun Q _ => hClosedTerm Q)
      _ = _ := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype (Finset.univ.filter (fun Q : ResiduePath A n => Q.Valid))
          (by simp) (fun Q => if Q.offset (Fin.last n) = 0 then ‖Q.Weight 0‖ else 0)
  have hconfigs :
      (∑ Q : {Q : ResiduePath A n // Q.Valid},
        ∑ S : {S : LifespanAssignment P n // Q.val.lifespanValid S},
          ∑ y : {y : P.SmallResidues // Q.val.SmallCompatible y},
            ∑ sigma : (Q.val.reconstructedHistory S.val S.property y.val).BatchOrders,
              ‖((Q.val.reconstructedHistory S.val S.property y.val).reorderBatches sigma).Weight
                rho 0‖) =
      ∑ c : SpanConfiguration A n, ‖c.history.Weight rho 0‖ := by
    simp only [SpanConfiguration, Fintype.sum_sigma, SpanConfiguration.history]
  have hconfigHistory :
      (∑ c : SpanConfiguration A n, ‖c.history.Weight rho 0‖) =
        ∑ H : ValidDistinctHistory A n, ‖H.val.Weight rho 0‖ := by
    exact Fintype.sum_equiv (SpanConfiguration.historyEquiv hStructure hn hk)
      (fun c => ‖c.history.Weight rho 0‖)
      (fun H => ‖H.val.Weight rho 0‖) (fun _ => rfl)
  calc
    closedAbsoluteResidueExpression A n =
        ∑ Q : {Q : ResiduePath A n // Q.Valid},
          if Q.val.offset (Fin.last n) = 0 then ‖Q.val.Weight 0‖ else 0 := hClosedSum
    _ ≤ ∑ Q : {Q : ResiduePath A n // Q.Valid},
          ∑ S : {S : LifespanAssignment P n // Q.val.lifespanValid S},
            ∑ y : {y : P.SmallResidues // Q.val.SmallCompatible y},
              ∑ sigma : (Q.val.reconstructedHistory S.val S.property y.val).BatchOrders,
                ‖((Q.val.reconstructedHistory S.val S.property y.val).reorderBatches sigma).Weight
                  rho 0‖ := by
        apply Finset.sum_le_sum
        intro Q hQ
        by_cases hc : Q.val.offset (Fin.last n) = 0
        · simpa [hc] using path_norm_le_configuration_fiber hGhost hMark hSpan hRes
            hn hk hV hbp rho hrho Q
        · simp only [hc, if_false]
          apply Finset.sum_nonneg
          intro S hS
          apply Finset.sum_nonneg
          intro y hy
          apply Finset.sum_nonneg
          intro sigma hsigma
          exact norm_nonneg _
    _ = ∑ c : SpanConfiguration A n, ‖c.history.Weight rho 0‖ := hconfigs
    _ = ∑ H : ValidDistinctHistory A n, ‖H.val.Weight rho 0‖ := hconfigHistory
    _ ≤ CG ^ (n + 1) * CE ^ n * initialMemoryBoundaryMass A n :=
      validHistory_norm_sum_le_doubled_bound rho v CG CE hv hCG hCE hG hE

example : Erdos821.S2Core.AbsoluteClosedRootTask := AbsoluteClosedRootTask_proof


end Erdos821.S2Root
