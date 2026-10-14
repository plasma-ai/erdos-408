import Erdos821.S2.MemoryTailTask
import Erdos821.P3Tail.PathBound

/-! The doubled-ghost memory tail estimate on the literal cutoff tail.

An omitted valid history has `B < totalGhostBirths + n*M*#Big`, so its weight norm is at
most `2^(n*M*#Big - B)` times the weight with every original ghost birth doubled. Summing
the doubled weights over any finite set of valid histories is controlled by expanding the
local choices for a fixed state path and then eliminating the state path chronologically
with the explicit row bounds. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Tail

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- The local doubled absolute ghost factor of one choice. -/
def ghostTerm (F : FixedData) (n : ℕ) (rho : ℝ) (i : Fin (n + 1)) {M : ℕ}
    {s t : P.MemoryState M} (c : GhostChoice s t) : ℝ :=
  if ghostChoiceValid c then |ghostChoiceWeight F n rho i c| * (2 : ℝ) ^ ghostBirthCount c
  else 0

/-- The local absolute edge factor of one choice, including the symmetry factor. -/
def edgeTerm (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) : ℝ :=
  if edgeChoiceValid A .all i s t c then
    edgeSymmetryFactor P (J + F.ell) * ‖edgeChoiceCoefficient A n rho theta i s t c‖
  else 0

theorem ghostTerm_nonneg (F : FixedData) (n : ℕ) (rho : ℝ) (i : Fin (n + 1)) {M : ℕ}
    {s t : P.MemoryState M} (c : GhostChoice s t) : 0 ≤ ghostTerm F n rho i c := by
  unfold ghostTerm
  split_ifs <;> positivity

theorem edgeTerm_nonneg (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) :
    0 ≤ edgeTerm A n rho theta i s t c := by
  unfold edgeTerm
  split_ifs
  · exact mul_nonneg (edgeSymmetryFactor_nonneg P (J + F.ell)) (norm_nonneg _)
  · exact le_rfl

theorem ghostKernel_nonneg (F : FixedData) (J n : ℕ) (rho : ℝ) (i : Fin (n + 1))
    (s t : P.MemoryState (J + F.ell)) :
    0 ≤ absoluteScaledMemoryGhostKernel F J n rho 2 i s t := by
  unfold absoluteScaledMemoryGhostKernel
  split_ifs
  · exact Finset.sum_nonneg fun c _ => by split_ifs <;> positivity
  · exact le_rfl

theorem edgeKernel_nonneg (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) :
    0 ≤ absoluteMemoryEdgeKernel A n rho theta i .all s t := by
  unfold absoluteMemoryEdgeKernel
  apply mul_nonneg (edgeSymmetryFactor_nonneg P (J + F.ell))
  exact Finset.sum_nonneg fun c _ => by split_ifs <;> positivity

theorem sum_ghostTerm_eq (F : FixedData) (J n : ℕ) (rho : ℝ) (i : Fin (n + 1))
    (s t : P.MemoryState (J + F.ell)) (h : s.1 = t.1 ∧ s.2.1 = t.2.1) :
    ∑ c : GhostChoice s t, ghostTerm F n rho i c =
      absoluteScaledMemoryGhostKernel F J n rho 2 i s t := by
  simp only [absoluteScaledMemoryGhostKernel, if_pos h]
  rfl

theorem sum_edgeTerm_eq (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) :
    ∑ c : EdgeChoice A s, edgeTerm A n rho theta i s t c =
      absoluteMemoryEdgeKernel A n rho theta i .all s t := by
  unfold absoluteMemoryEdgeKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  unfold edgeTerm
  split_ifs <;> simp

/-- The absolute history weight with every original ghost birth multiplied by 2. -/
def doubledWeight {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n) (rho theta : ℝ) : ℝ :=
  |P.memoryMass F J n (H.before 0)| * (∏ i, ghostTerm F n rho i (H.ghost i)) *
    ∏ i, edgeTerm A n rho theta i (H.after i.castSucc) (H.before i.succ) (H.edge i)

theorem doubledWeight_nonneg {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)
    (rho theta : ℝ) : 0 ≤ doubledWeight H rho theta := by
  unfold doubledWeight
  apply mul_nonneg (mul_nonneg (abs_nonneg _)
    (Finset.prod_nonneg fun i _ => ghostTerm_nonneg F n rho i _))
  exact Finset.prod_nonneg fun i _ => edgeTerm_nonneg A n rho theta i _ _ _

theorem norm_weight_mul_pow {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)
    (rho theta : ℝ) (hH : H.Valid) :
    ‖H.Weight rho theta‖ * (2 : ℝ) ^ H.totalGhostBirths = doubledWeight H rho theta := by
  have hg : ∀ i, ghostTerm F n rho i (H.ghost i) =
      |ghostChoiceWeight F n rho i (H.ghost i)| * (2 : ℝ) ^ ghostBirthCount (H.ghost i) :=
    fun i => if_pos (hH.2.2.1 i).2.2
  have he : ∀ i, edgeTerm A n rho theta i (H.after i.castSucc) (H.before i.succ) (H.edge i) =
      edgeSymmetryFactor P (J + F.ell) *
        ‖edgeChoiceCoefficient A n rho theta i (H.after i.castSucc) (H.before i.succ) (H.edge i)‖ :=
    fun i => if_pos (hH.2.2.2 i)
  simp only [doubledWeight, hg, he, MemoryHistory.Weight, MemoryHistory.totalGhostBirths,
    norm_mul, norm_prod, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (edgeSymmetryFactor_nonneg P (J + F.ell)), Finset.prod_mul_distrib,
    ← Finset.prod_pow_eq_pow_sum]
  ring

/-- The cutoff tail bound for one omitted valid history. -/
theorem tail_norm_le {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n) (rho theta : ℝ)
    (B : ℕ) (hH : H.Valid) (htail : ¬ H.Truncated B) :
    ‖H.Weight rho theta‖ ≤
      (2 : ℝ) ^ (((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) - (B : ℤ)) *
        doubledWeight H rho theta := by
  have hlt := H.tail_requires_births B hH htail
  have hz : ((B : ℕ) : ℤ) < (H.totalGhostBirths : ℤ) +
      ((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) := by
    exact_mod_cast hlt
  rw [← norm_weight_mul_pow H rho theta hH]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) -
      (B : ℤ)) * (2 : ℝ) ^ H.totalGhostBirths := by
    rw [← zpow_natCast (2 : ℝ) H.totalGhostBirths, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    apply one_le_zpow₀ (by norm_num)
    linarith
  calc ‖H.Weight rho theta‖ = ‖H.Weight rho theta‖ * 1 := (mul_one _).symm
    _ ≤ ‖H.Weight rho theta‖ * ((2 : ℝ) ^ (((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) -
          (B : ℤ)) * (2 : ℝ) ^ H.totalGhostBirths) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = _ := by ring

/-- The sequence of `(before, after)` ghost states. -/
def statePath {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n) :
    Fin (n + 1) → P.MemoryState (J + F.ell) × P.MemoryState (J + F.ell) :=
  fun i => (H.before i, H.after i)

/-- Histories with a fixed valid state path: expanding the finite local choices gives the
product of literal kernel entries. -/
theorem fiber_sum_le (A : Model F P J m) (n : ℕ) (rho theta v : ℝ) (hv : 1 ≤ v)
    (S : Finset (MemoryHistory A n)) (H0 : MemoryHistory A n) (hH0 : H0.Valid) :
    ∑ H ∈ S.filter (fun H => statePath H = statePath H0), doubledWeight H rho theta ≤
      |P.memoryMass F J n (H0.before 0)| *
        pathWeight (P.memoryWeight v) n (fun i => absoluteScaledMemoryGhostKernel F J n rho 2 i)
          (fun i => absoluteMemoryEdgeKernel A n rho theta i .all) (statePath H0) := by
  letI : Fintype ((i : Fin (n + 1)) → GhostChoice (H0.before i) (H0.after i)) := Pi.instFintype
  letI : Fintype ((i : Fin n) → EdgeChoice A (H0.after i.castSucc)) := Pi.instFintype
  letI : Fintype (((i : Fin (n + 1)) → GhostChoice (H0.before i) (H0.after i)) ×
      ((i : Fin n) → EdgeChoice A (H0.after i.castSucc))) := instFintypeProd _ _
  let mk : ((i : Fin (n + 1)) → GhostChoice (H0.before i) (H0.after i)) ×
      ((i : Fin n) → EdgeChoice A (H0.after i.castSucc)) → MemoryHistory A n :=
    fun c => ⟨H0.before, H0.after, c.1, c.2⟩
  have hinj : Function.Injective mk := by
    intro c c' h
    simp only [mk, MemoryHistory.mk.injEq, heq_eq_eq, true_and] at h
    exact Prod.ext h.1 h.2
  have hsub : S.filter (fun H => statePath H = statePath H0) ⊆ Finset.univ.image mk := by
    intro H hH
    have hp := (Finset.mem_filter.1 hH).2
    have hb : H.before = H0.before := funext fun i => congrArg Prod.fst (congrFun hp i)
    have ha : H.after = H0.after := funext fun i => congrArg Prod.snd (congrFun hp i)
    rw [Finset.mem_image]
    obtain ⟨b, a, g, e⟩ := H
    simp only at hb ha
    subst hb
    subst ha
    exact ⟨(g, e), Finset.mem_univ _, rfl⟩
  have hK : ∀ i, (H0.before i).1 = (H0.after i).1 ∧ (H0.before i).2.1 = (H0.after i).2.1 :=
    fun i => ⟨(hH0.2.2.1 i).1, (hH0.2.2.1 i).2.1⟩
  have hPG : 0 ≤ ∏ i, absoluteScaledMemoryGhostKernel F J n rho 2 i (H0.before i) (H0.after i) :=
    Finset.prod_nonneg fun i _ => ghostKernel_nonneg F J n rho i _ _
  have hPE : 0 ≤ ∏ i : Fin n, absoluteMemoryEdgeKernel A n rho theta i .all
      (H0.after i.castSucc) (H0.before i.succ) :=
    Finset.prod_nonneg fun i _ => edgeKernel_nonneg A n rho theta i _ _
  have hw : 1 ≤ P.memoryWeight v (H0.after (Fin.last n)) := one_le_pow₀ hv
  have h1 : (∑ c1 : (i : Fin (n + 1)) → GhostChoice (H0.before i) (H0.after i),
      ∏ i, ghostTerm F n rho i (c1 i)) =
      ∏ i, absoluteScaledMemoryGhostKernel F J n rho 2 i (H0.before i) (H0.after i) := by
    rw [← Fintype.prod_sum (fun i c => ghostTerm F n rho i c)]
    exact Finset.prod_congr rfl fun i _ => sum_ghostTerm_eq F J n rho i _ _ (hK i)
  have h2 : (∑ c2 : (i : Fin n) → EdgeChoice A (H0.after i.castSucc),
      ∏ i, edgeTerm A n rho theta i (H0.after i.castSucc) (H0.before i.succ) (c2 i)) =
      ∏ i : Fin n, absoluteMemoryEdgeKernel A n rho theta i .all
        (H0.after i.castSucc) (H0.before i.succ) := by
    rw [← Fintype.prod_sum (fun i c =>
      edgeTerm A n rho theta i (H0.after i.castSucc) (H0.before i.succ) c)]
    exact Finset.prod_congr rfl fun i _ => sum_edgeTerm_eq A n rho theta i _ _
  calc ∑ H ∈ S.filter (fun H => statePath H = statePath H0), doubledWeight H rho theta
      ≤ ∑ H ∈ Finset.univ.image mk, doubledWeight H rho theta :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun H _ _ => doubledWeight_nonneg H rho theta
    _ = ∑ c, doubledWeight (mk c) rho theta :=
        Finset.sum_image fun c _ c' _ h => hinj h
    _ = |P.memoryMass F J n (H0.before 0)| *
          ((∑ c1 : (i : Fin (n + 1)) → GhostChoice (H0.before i) (H0.after i),
            ∏ i, ghostTerm F n rho i (c1 i)) *
          (∑ c2 : (i : Fin n) → EdgeChoice A (H0.after i.castSucc),
            ∏ i, edgeTerm A n rho theta i (H0.after i.castSucc) (H0.before i.succ) (c2 i))) := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c1 _
        apply Finset.sum_congr rfl
        intro c2 _
        simp only [doubledWeight, mk]
        ring
    _ = |P.memoryMass F J n (H0.before 0)| *
          ((∏ i, absoluteScaledMemoryGhostKernel F J n rho 2 i (H0.before i) (H0.after i)) *
          (∏ i : Fin n, absoluteMemoryEdgeKernel A n rho theta i .all
            (H0.after i.castSucc) (H0.before i.succ))) := by
        rw [h1, h2]
    _ ≤ |P.memoryMass F J n (H0.before 0)| *
          ((∏ i, absoluteScaledMemoryGhostKernel F J n rho 2 i (H0.before i) (H0.after i)) *
          (∏ i : Fin n, absoluteMemoryEdgeKernel A n rho theta i .all
            (H0.after i.castSucc) (H0.before i.succ)) *
          P.memoryWeight v (H0.after (Fin.last n))) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc _ = (∏ i, absoluteScaledMemoryGhostKernel F J n rho 2 i (H0.before i) (H0.after i)) *
              (∏ i : Fin n, absoluteMemoryEdgeKernel A n rho theta i .all
                (H0.after i.castSucc) (H0.before i.succ)) * 1 := (mul_one _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hw (mul_nonneg hPG hPE)
    _ = _ := rfl

/-- The initial boundary states of valid histories have empty memory. -/
theorem start_sum_le (A : Model F P J m) (n : ℕ) (T : Finset (P.MemoryState (J + F.ell)))
    (hT : ∀ s ∈ T, ∀ g, s.2.2 g = 0) :
    ∑ s ∈ T, |P.memoryMass F J n s| ≤ initialMemoryBoundaryMass A n := by
  let emb : P.SmallResidues × P.Labels (J + F.ell) → P.MemoryState (J + F.ell) :=
    fun p => (p.1, p.2, fun _ => 0)
  have hinj : Function.Injective emb := by
    intro p q h
    simp only [emb, Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1
  have hsub : T ⊆ Finset.univ.image emb := by
    intro s hs
    rw [Finset.mem_image]
    exact ⟨(s.1, s.2.1), Finset.mem_univ _,
      Prod.ext rfl (Prod.ext rfl (funext fun g => (hT s hs g).symm))⟩
  calc ∑ s ∈ T, |P.memoryMass F J n s|
      ≤ ∑ s ∈ Finset.univ.image emb, |P.memoryMass F J n s| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _
    _ = ∑ p, |P.memoryMass F J n (emb p)| := Finset.sum_image fun p _ q _ h => hinj h
    _ = initialMemoryBoundaryMass A n := by
        rw [Fintype.sum_prod_type]
        rfl

/-- A stronger finite-subset form: any finite set of valid histories has total doubled
absolute weight at most `CG^(n+1) * CE^n * initialMemoryBoundaryMass`. -/
theorem finite_doubled_sum_le (A : Model F P J m) (n : ℕ) (rho theta v CG CE : ℝ)
    (hv : 1 ≤ v) (hCG : 0 ≤ CG) (hCE : 0 ≤ CE)
    (hG : ∀ (i : Fin (n + 1)) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteScaledMemoryGhostKernel F J n rho 2 i s t *
        P.memoryWeight v t) ∧
      (∑' t, absoluteScaledMemoryGhostKernel F J n rho 2 i s t *
        P.memoryWeight v t) ≤ CG * P.memoryWeight v s)
    (hE : ∀ (i : Fin n) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteMemoryEdgeKernel A n rho theta i .all s t *
        P.memoryWeight v t) ∧
      (∑' t, absoluteMemoryEdgeKernel A n rho theta i .all s t *
        P.memoryWeight v t) ≤ CE * P.memoryWeight v s)
    (S : Finset (MemoryHistory A n)) (hS : ∀ H ∈ S, H.Valid) :
    ∑ H ∈ S, doubledWeight H rho theta ≤
      CG ^ (n + 1) * CE ^ n * initialMemoryBoundaryMass A n := by
  let G : Fin (n + 1) → P.MemoryState (J + F.ell) → P.MemoryState (J + F.ell) → ℝ :=
    fun i => absoluteScaledMemoryGhostKernel F J n rho 2 i
  let E : Fin n → P.MemoryState (J + F.ell) → P.MemoryState (J + F.ell) → ℝ :=
    fun i => absoluteMemoryEdgeKernel A n rho theta i .all
  let w := P.memoryWeight (M := J + F.ell) v
  have hw0 : ∀ t, 0 ≤ w t := fun t => pow_nonneg (by linarith) _
  let Z := S.image statePath
  let St := Z.image (fun z => (z 0).1)
  have hK : 0 ≤ CG ^ (n + 1) * CE ^ n := by positivity
  have hSt : ∀ s ∈ St, ∃ H ∈ S, H.before 0 = s := by
    intro s hs
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.1 hz
    exact ⟨H, hH, rfl⟩
  have hempty : ∀ s ∈ St, ∀ g, s.2.2 g = 0 := by
    intro s hs g
    obtain ⟨H, hH, rfl⟩ := hSt s hs
    exact (hS H hH).1 g
  have hw1 : ∀ s ∈ St, w s = 1 := by
    intro s hs
    have h0 : P.memorySize s = 0 := by
      simp [PrimeGroups.memorySize, hempty s hs]
    simp [w, PrimeGroups.memoryWeight, h0]
  calc ∑ H ∈ S, doubledWeight H rho theta
      = ∑ z ∈ Z, ∑ H ∈ S.filter (fun H => statePath H = z), doubledWeight H rho theta :=
        (Finset.sum_fiberwise_of_maps_to (fun H hH => Finset.mem_image_of_mem statePath hH) _).symm
    _ ≤ ∑ z ∈ Z, |P.memoryMass F J n (z 0).1| * pathWeight w n G E z := by
        apply Finset.sum_le_sum
        intro z hz
        obtain ⟨H0, hH0, rfl⟩ := Finset.mem_image.1 hz
        exact fiber_sum_le A n rho theta v hv S H0 (hS H0 hH0)
    _ = ∑ s ∈ St, ∑ z ∈ Z.filter (fun z => (z 0).1 = s),
          |P.memoryMass F J n (z 0).1| * pathWeight w n G E z :=
        (Finset.sum_fiberwise_of_maps_to
          (fun z hz => Finset.mem_image_of_mem (fun z => (z 0).1) hz) _).symm
    _ = ∑ s ∈ St, |P.memoryMass F J n s| *
          ∑ z ∈ Z.filter (fun z => (z 0).1 = s), pathWeight w n G E z := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        rw [(Finset.mem_filter.1 hz).2]
    _ ≤ ∑ s ∈ St, |P.memoryMass F J n s| * (CG ^ (n + 1) * CE ^ n * w s) := by
        apply Finset.sum_le_sum
        intro s _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact path_bound w hw0 CG CE hCG hCE n G E
          (fun i => ghostKernel_nonneg F J n rho i) (fun i => edgeKernel_nonneg A n rho theta i)
          hG hE _ s (fun z hz => (Finset.mem_filter.1 hz).2)
    _ = (CG ^ (n + 1) * CE ^ n) * ∑ s ∈ St, |P.memoryMass F J n s| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        rw [hw1 s hs]
        ring
    _ ≤ (CG ^ (n + 1) * CE ^ n) * initialMemoryBoundaryMass A n :=
        mul_le_mul_of_nonneg_left (start_sum_le A n St hempty) hK

end Erdos821.P3Tail

open Erdos821.Blueprint.Graph Erdos821.S2Core Erdos821.P3Tail in
theorem Erdos821.S2Core.MemoryTailTask_proof : Erdos821.S2Core.MemoryTailTask := by
  intro F P J m n A rho v theta CG CE hv hCG hCE hG hE B
  have h0 : Set.Finite {H : MemoryHistory A n | H.Valid ∧ H.DistinctBirths} :=
    @Set.toFinite (MemoryHistory A n) {H | H.Valid ∧ H.DistinctBirths}
      (MemoryHistory.valid_distinct_finite A n)
  have hfin : Set.Finite
      {H : MemoryHistory A n | H.Valid ∧ H.DistinctBirths ∧ ¬ H.Truncated B} :=
    h0.subset fun H hH => ⟨hH.1, hH.2.1⟩
  have hpow : 0 ≤ (2 : ℝ) ^ (((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) -
      (B : ℤ)) := zpow_nonneg (by norm_num) _
  rw [tsum_eq_sum (s := hfin.toFinset) (fun H hH => by
    rw [Set.Finite.mem_toFinset] at hH
    exact if_neg hH)]
  calc ∑ H ∈ hfin.toFinset,
        (if H.Valid ∧ H.DistinctBirths ∧ ¬ H.Truncated B then ‖H.Weight rho theta‖ else 0)
      = ∑ H ∈ hfin.toFinset, ‖H.Weight rho theta‖ :=
        Finset.sum_congr rfl fun H hH => if_pos (hfin.mem_toFinset.1 hH)
    _ ≤ ∑ H ∈ hfin.toFinset,
          (2 : ℝ) ^ (((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) - (B : ℤ)) *
            doubledWeight H rho theta :=
        Finset.sum_le_sum fun H hH =>
          tail_norm_le H rho theta B (hfin.mem_toFinset.1 hH).1 (hfin.mem_toFinset.1 hH).2.2
    _ = (2 : ℝ) ^ (((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) - (B : ℤ)) *
          ∑ H ∈ hfin.toFinset, doubledWeight H rho theta := (Finset.mul_sum _ _ _).symm
    _ ≤ (2 : ℝ) ^ (((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) - (B : ℤ)) *
          (CG ^ (n + 1) * CE ^ n * initialMemoryBoundaryMass A n) :=
        mul_le_mul_of_nonneg_left (finite_doubled_sum_le A n rho theta v CG CE hv hCG hCE hG hE
          hfin.toFinset fun H hH => (hfin.mem_toFinset.1 hH).1) hpow
    _ = _ := by ring

