import Erdos821.P3Edge.Absolute
import Erdos821.P3Edge.RowSummable
import Erdos821.P3Edge.RowSupport
import Erdos821.P3Edge.BigFibres
import Erdos821.P3Edge.Polylog

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- Per-pattern supremum of coefficient norms. -/
def patternSup (A : Model F P J m) (v : Fin A.patternCount) : ℝ :=
  sSup (Set.range (fun z : P.BigLabels (J + F.ell) × P.BigLabels (J + F.ell) × P.BigAux J =>
    ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖))

lemma patternSup_nonneg (A : Model F P J m) (v : Fin A.patternCount) :
    0 ≤ patternSup A v := by
  classical
  unfold patternSup
  rcases Set.eq_empty_or_nonempty (Set.range (fun z : P.BigLabels (J + F.ell) ×
      P.BigLabels (J + F.ell) × P.BigAux J =>
      ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖)) with h | h
  · rw [h]
    simp [csSup_empty]
  · obtain ⟨y, hy⟩ := h
    obtain ⟨z, rfl⟩ := Set.mem_range.mp hy
    exact le_trans (norm_nonneg _) (le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self z))

lemma sum_patternSup_eq (A : Model F P J m) :
    ∑ v : Fin A.patternCount, patternSup A v = A.patternMass := rfl

lemma patternMass_nonneg (A : Model F P J m) : 0 ≤ A.patternMass := by
  rw [← sum_patternSup_eq]
  exact Finset.sum_nonneg (fun v _ => patternSup_nonneg A v)

lemma coeff_le_patternSup (A : Model F P J m) (v : Fin A.patternCount)
    (a b : P.BigLabels (J + F.ell)) (u : P.BigAux J) :
    ‖(A.pattern v).coefficient a b u‖ ≤ patternSup A v := by
  classical
  unfold patternSup
  exact le_csSup (Set.finite_range _).bddAbove
    (Set.mem_range_self (⟨a, b, u⟩ : P.BigLabels (J + F.ell) × P.BigLabels (J + F.ell) × P.BigAux J))

lemma edgeChoiceCoefficient_norm_le_patternSup (A : Model F P J m) (n : ℕ) (rho theta : ℝ)
    (i : Fin n) (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) :
    ‖edgeChoiceCoefficient A n rho theta i s t c‖ ≤
      patternSup A c.2.2.1 * |rawEdgeWeight A n rho (A.pattern c.2.2.1) c.2.2.2.1
        (permuteActive c.1 s) (permuteActive c.2.1 t) c.2.2.2.2| := by
  classical
  unfold edgeChoiceCoefficient
  simp only []
  have hphase : ‖phase (theta * ((edgeDelta A (A.pattern c.2.2.1) (edgeForward i)
      (permuteActive c.1 s).2.1 c.2.2.2.1 : ℤ) : ℝ))‖ = 1 :=
    norm_phase _
  have hcoeff : ∀ (a b : P.BigLabels (J + F.ell)) (u : P.BigAux J),
      ‖(A.pattern c.2.2.1).coefficient a b u * imaginaryPower
        ((A.pattern c.2.2.1).D (permuteActive c.1 s).2.1 c.2.2.2.1) A.zeta‖ ≤
        patternSup A c.2.2.1 := by
    intro a b u
    calc ‖(A.pattern c.2.2.1).coefficient a b u * imaginaryPower _ _‖
        = ‖(A.pattern c.2.2.1).coefficient a b u‖ * 1 := by
          rw [norm_mul, norm_imaginaryPower, mul_one]
      _ ≤ patternSup A c.2.2.1 := by
          rw [mul_one]
          exact coeff_le_patternSup A c.2.2.1 a b u
  by_cases hf : edgeForward i = true
  · simp only [hf, ite_true] at ⊢
    rw [hf] at hphase
    have hz := hcoeff (P.restrictBig (permuteActive c.1 s).2.1)
      (P.restrictBig (permuteActive c.2.1 t).2.1) (fun g => c.2.2.2.1 g.val)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hphase, mul_one,
      mul_comm (patternSup A c.2.2.1) _]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  · rw [if_neg hf] at ⊢
    have hz := hcoeff (P.restrictBig (permuteActive c.2.1 t).2.1)
      (P.restrictBig (permuteActive c.1 s).2.1) (fun g => c.2.2.2.1 g.val)
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      hphase, mul_one, mul_comm (patternSup A c.2.2.1) _]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)

/-- Source dampings ≤ 1 for physical states. -/
lemma source_damp_le_one (F : FixedData) (r : MemoryParameters F)
    (J : ℕ) (y : P.SmallResidues) (a : P.Labels (J + F.ell))
    (hphys : P.smallPhysical y a) (Zs : ℕ) :
    smallDamping F J y * r.rho ^ Zs ≤ 1 := by
  have h1 : smallDamping F J y ≤ 1 := smallDamping_le_one y a hphys
  have h2 : r.rho ^ Zs ≤ 1 := pow_le_one₀ r.rho_pos.le r.rho_lt.le
  have hnn2 : 0 ≤ r.rho ^ Zs := pow_nonneg r.rho_pos.le _
  calc smallDamping F J y * r.rho ^ Zs ≤ 1 * 1 :=
        mul_le_mul h1 h2 hnn2 zero_le_one
    _ = 1 := mul_one 1

/-- Sum-product interchange over a finite dependent Pi type. -/
lemma sum_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ g, Fintype (α g)] [∀ g, DecidableEq (α g)]
    (h : (g : ι) → α g → ℝ) :
    (∑ x : (g : ι) → α g, ∏ g : ι, h g (x g)) = ∏ g : ι, ∑ x_g : α g, h g x_g := by
  classical
  have h1 := Finset.prod_univ_sum (fun g : ι => (Finset.univ : Finset (α g)))
    (fun g : ι => fun x_g : α g => h g x_g)
  rw [Fintype.piFinset_univ] at h1
  exact h1.symm

/-- Product over all groups splits into big groups and small groups. -/
lemma prod_group_split (H : P.Group → ℝ) :
    (∏ g : P.Group, H g) = (∏ g : P.BigGroup, H g.val) * (∏ g : P.SmallGroup, H g.val) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun g : P.Group => P.big g = true)]
  congr 1
  · symm
    apply Finset.prod_bij (fun (g : P.BigGroup) _ => g.val)
    · intro g _
      simp [g.property]
    · intro g₁ _ g₂ _ h
      exact Subtype.ext h
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      exact ⟨⟨g, hg⟩, Finset.mem_univ _, rfl⟩
    · intro g _
      rfl
  · symm
    apply Finset.prod_bij (fun (g : P.SmallGroup) _ => g.val)
    · intro g _
      simp [g.property]
    · intro g₁ _ g₂ _ h
      exact Subtype.ext h
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hg
      exact ⟨⟨g, hg⟩, Finset.mem_univ _, rfl⟩
    · intro g _
      rfl

/-- Sum over `b : P.Labels (J + F.ell)` of a product over big and small groups factorizes. -/
lemma sum_labels_split
    (F_big : (g : P.BigGroup) → (Fin (J + F.ell) → P.Prime g.val) → ℝ)
    (F_small : (g : P.SmallGroup) → (Fin (J + F.ell) → P.Prime g.val) → ℝ) :
    (∑ b : P.Labels (J + F.ell),
      (∏ g : P.BigGroup, F_big g (b g.val)) * (∏ g : P.SmallGroup, F_small g (b g.val))) =
    (∏ g : P.BigGroup, ∑ b_g : Fin (J + F.ell) → P.Prime g.val, F_big g b_g) *
    (∏ g : P.SmallGroup, ∑ b_g : Fin (J + F.ell) → P.Prime g.val, F_small g b_g) := by
  classical
  let F_all : (g : P.Group) → (Fin (J + F.ell) → P.Prime g) → ℝ :=
    fun g b_g => if h : P.big g = true then F_big ⟨g, h⟩ b_g
      else F_small ⟨g, Bool.eq_false_iff.mpr h⟩ b_g
  have hbig : ∀ (g : P.BigGroup) (b_g : Fin (J + F.ell) → P.Prime g.val),
      F_all g.val b_g = F_big g b_g := by
    intro g b_g
    dsimp [F_all]
    rw [dif_pos g.property]
  have hsmall : ∀ (g : P.SmallGroup) (b_g : Fin (J + F.ell) → P.Prime g.val),
      F_all g.val b_g = F_small g b_g := by
    intro g b_g
    dsimp [F_all]
    have hnot : ¬ P.big g.val = true := by rw [g.property]; decide
    rw [dif_neg hnot]
  have hterm : ∀ b : P.Labels (J + F.ell),
      (∏ g : P.BigGroup, F_big g (b g.val)) * (∏ g : P.SmallGroup, F_small g (b g.val)) =
      ∏ g : P.Group, F_all g (b g) := by
    intro b
    rw [prod_group_split (fun g => F_all g (b g))]
    congr 1
    · apply Finset.prod_congr rfl (fun g _ => (hbig g (b g.val)).symm)
    · apply Finset.prod_congr rfl (fun g _ => (hsmall g (b g.val)).symm)
  simp_rw [hterm]
  rw [sum_pi_prod F_all, prod_group_split (fun g => ∑ b_g, F_all g b_g)]
  congr 1
  · apply Finset.prod_congr rfl
    intro g _
    exact Finset.sum_congr rfl (fun b_g _ => hbig g b_g)
  · apply Finset.prod_congr rfl
    intro g _
    exact Finset.sum_congr rfl (fun b_g _ => hsmall g b_g)

/-- `rawEdgeWeight` is nonnegative when `V > 0` and `tiltedMu ≥ 0`. -/
lemma rawEdgeWeight_nonneg (r : MemoryParameters F) (n : ℕ)
    (A : Model F P J m) (ν : Pattern P J F.ell m) (u : P.Aux J)
    (ss tt : P.MemoryState (J + F.ell)) (tr : TransferChoice ss)
    (hV : ∀ g : P.Group, 0 < P.V g)
    (htilted : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p) :
    0 ≤ rawEdgeWeight A n r.rho ν u ss tt tr := by
  unfold rawEdgeWeight
  have haux : 0 ≤ ν.auxMass u := by
    unfold Pattern.auxMass
    exact Finset.prod_nonneg (fun g _ =>
      Finset.prod_nonneg (fun j _ => (mu_pos_of_V_pos g (hV g) (u g j)).le))
  have hfresh : 0 ≤ freshBigFactor F n ν tr.2.1 tt.2.1 := by
    unfold freshBigFactor
    apply Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun idx _ => ?_))
    split_ifs
    · exact zero_le_one
    · exact htilted g _
  have hVbig : 0 ≤ ∏ g : P.BigGroup, (P.V g.val) ^ (-((tr.2.1 g).card : ℤ)) :=
    Finset.prod_nonneg (fun g _ => zpow_nonneg (hV g.val).le _)
  have hVsmall : 0 ≤ smallTargetFactor (P := P) F :=
    Finset.prod_nonneg (fun g _ => zpow_nonneg (hV g.val).le _)
  have hd1 : 0 ≤ smallDamping F J ss.1 := Real.rpow_nonneg F.q_pos.le _
  have hd2 : 0 ≤ smallDamping F J tt.1 := Real.rpow_nonneg F.q_pos.le _
  have hrho : 0 ≤ r.rho ^ ((∑ g : P.BigGroup, (zeroMemoryIndices (ss.2.2 g)).card) +
      (∑ g : P.BigGroup, (zeroMemoryIndices (tt.2.2 g)).card)) :=
    pow_nonneg r.rho_pos.le _
  positivity

/-- Pointwise factorization and upper bound of `|rawEdgeWeight| * memoryWeight` on a valid raw edge. -/
lemma rawEdgeWeight_mul_weight_le (r : MemoryParameters F) (n : ℕ)
    (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool) (u : P.Aux J)
    (ss tt : P.MemoryState (J + F.ell)) (tr : TransferChoice ss)
    (hV : ∀ g : P.Group, 0 < P.V g)
    (htilted : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (hvalid : rawEdgeValid A ν forward u ss tt tr) :
    |rawEdgeWeight A n r.rho ν u ss tt tr| * P.memoryWeight r.v tt ≤
      ν.auxMass u * P.memoryWeight r.v ss *
        ((∏ g : P.BigGroup,
          if bigGroupValid ν (edgeDelta A ν forward ss.2.1 u) g (ss.2.1 g.val) (ss.2.2 g)
              (tr.1 g) (tr.2.1 g) (tr.2.2 g) (tt.2.1 g.val) then
            bigGroupWeight F r n ν (edgeDelta A ν forward ss.2.1 u) g (ss.2.1 g.val) (ss.2.2 g)
              (tr.1 g) (tr.2.1 g) (tr.2.2 g) (tt.2.1 g.val)
          else 0) *
        (∏ g : P.SmallGroup,
          if tt.2.1 g.val ∈ smallPrefixFibre J F.ell
              (translateSmallResidues (edgeDelta A ν forward ss.2.1 u) ss.1 g)
              (fun j => ss.2.1 g.val (Fin.castAdd F.ell j)) then
            smallGroupWeight F J g (translateSmallResidues (edgeDelta A ν forward ss.2.1 u) ss.1 g)
          else 0)) := by
  classical
  set delta := edgeDelta A ν forward ss.2.1 u
  have hbg : ∀ g : P.BigGroup,
      bigGroupValid ν delta g (ss.2.1 g.val) (ss.2.2 g)
        (tr.1 g) (tr.2.1 g) (tr.2.2 g) (tt.2.1 g.val) := by
    intro g
    obtain ⟨hphys_s, hphys_t, hcomp, hban, hsmall_eq, hg⟩ := hvalid
    obtain ⟨hB, hA, hinj, hprom, hmem⟩ := hg g
    refine ⟨fun idx hidx => (hB idx hidx).1, hA, ?_, ?_⟩
    · intro j hj
      exact (hcomp g.val (ν.slot j) ⟨j, rfl, hj⟩).symm
    · intro idx
      exact ⟨(hprom idx).1, (hprom idx).2.1⟩
  have hsg : ∀ g : P.SmallGroup,
      tt.2.1 g.val ∈ smallPrefixFibre J F.ell
        (translateSmallResidues delta ss.1 g)
        (fun j => ss.2.1 g.val (Fin.castAdd F.ell j)) := by
    intro g
    obtain ⟨hphys_s, hphys_t, hcomp, hban, hsmall_eq, hg⟩ := hvalid
    simp only [smallPrefixFibre, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(hphys_t g).1, ?_, ?_⟩
    · intro idx
      have h0 := (hphys_t g).2 idx
      rwa [hsmall_eq] at h0
    · intro j
      have hch : j ∉ ν.changed g.val := by
        rw [ν.small g.val g.property]
        exact Finset.notMem_empty j
      exact (hcomp g.val (ν.slot j) ⟨j, rfl, hch⟩).symm
  set B_prod := ∏ g : P.BigGroup,
    if bigGroupValid ν delta g (ss.2.1 g.val) (ss.2.2 g)
        (tr.1 g) (tr.2.1 g) (tr.2.2 g) (tt.2.1 g.val) then
      bigGroupWeight F r n ν delta g (ss.2.1 g.val) (ss.2.2 g)
        (tr.1 g) (tr.2.1 g) (tr.2.2 g) (tt.2.1 g.val)
    else 0
  set S_prod := ∏ g : P.SmallGroup,
    if tt.2.1 g.val ∈ smallPrefixFibre J F.ell
        (translateSmallResidues delta ss.1 g)
        (fun j => ss.2.1 g.val (Fin.castAdd F.ell j)) then
      smallGroupWeight F J g (translateSmallResidues delta ss.1 g)
    else 0
  have hbig_prod : B_prod =
      freshBigFactor F n ν tr.2.1 tt.2.1 *
        (∏ g : P.BigGroup, (P.V g.val) ^ (-((tr.2.1 g).card : ℤ))) *
        r.rho ^ (∑ g : P.BigGroup, (zeroMemoryIndices (tt.2.2 g)).card) *
        (∏ g : P.BigGroup, (r.v ^ (tr.1 g).card / r.v ^ (tr.2.1 g).card)) := by
    have h1 : B_prod =
        ∏ g : P.BigGroup,
          bigGroupWeight F r n ν delta g (ss.2.1 g.val) (ss.2.2 g)
            (tr.1 g) (tr.2.1 g) (tr.2.2 g) (tt.2.1 g.val) := by
      apply Finset.prod_congr rfl
      intro g _
      rw [if_pos (hbg g)]
    rw [h1]
    unfold bigGroupWeight freshBigFactor
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← Finset.prod_pow_eq_pow_sum]
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro g _
    have hmem : tt.2.2 g = translateMemory delta
        (deleteMemoryIndices (ss.2.2 g) (retrievedIndices tr g) +
          storedMemory (ss.2.1 g.val) (tr.1 g)) :=
      (hvalid.2.2.2.2.2 g).2.2.2.2
    rw [hmem]
    rfl
  have hsmall_prod : S_prod =
      smallTargetFactor (P := P) F * smallDamping F J tt.1 := by
    have h1 : S_prod = ∏ g : P.SmallGroup, smallGroupWeight F J g (tt.1 g) := by
      apply Finset.prod_congr rfl
      intro g _
      rw [if_pos (hsg g), hvalid.2.2.2.2.1]
    rw [h1, prod_smallGroupWeight_eq]
  have hw_eq : P.memoryWeight r.v tt =
      P.memoryWeight r.v ss * ∏ g : P.BigGroup, (r.v ^ (tr.1 g).card / r.v ^ (tr.2.1 g).card) := by
    unfold PrimeGroups.memoryWeight PrimeGroups.memorySize
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro g _
    have hcard := rawEdgeValid_memory_card A ν forward u ss tt tr hvalid g
    have hinj : Function.Injective (tr.2.2 g) := (hvalid.2.2.2.2.2 g).2.2.1
    have hle : (tr.2.1 g).card ≤ (ss.2.2 g).card := by
      have hc := Fintype.card_le_of_injective (tr.2.2 g) hinj
      simpa using hc
    have hvne : r.v ≠ 0 := ne_of_gt (lt_trans zero_lt_one r.v_gt)
    rw [hcard, pow_add]
    have hsub : r.v ^ ((ss.2.2 g).card - (tr.2.1 g).card) =
        r.v ^ (ss.2.2 g).card / r.v ^ (tr.2.1 g).card := by
      rw [eq_div_iff (pow_ne_zero _ hvne), ← pow_add, Nat.sub_add_cancel hle]
    rw [hsub]
    ring
  have hB_nn : 0 ≤ B_prod := by
    apply Finset.prod_nonneg (fun g _ => ?_)
    rw [if_pos (hbg g)]
    exact bigGroupWeight_nonneg F r n ν delta g (hV g.val) (htilted g) _ _ _ _ _ _
  have hS_nn : 0 ≤ S_prod := by
    apply Finset.prod_nonneg (fun g _ => ?_)
    rw [if_pos (hsg g)]
    exact smallGroupWeight_nonneg F J g (hV g.val) _
  have haux_nn : 0 ≤ ν.auxMass u := by
    unfold Pattern.auxMass
    exact Finset.prod_nonneg (fun g _ =>
      Finset.prod_nonneg (fun j _ => (mu_pos_of_V_pos g (hV g) (u g j)).le))
  have hdamp := source_damp_le_one F r J ss.1 ss.2.1 hvalid.1
    (∑ g : P.BigGroup, (zeroMemoryIndices (ss.2.2 g)).card)
  have hlhs_eq : |rawEdgeWeight A n r.rho ν u ss tt tr| * P.memoryWeight r.v tt =
      (ν.auxMass u * P.memoryWeight r.v ss * (B_prod * S_prod)) *
        (smallDamping F J ss.1 *
          r.rho ^ (∑ g : P.BigGroup, (zeroMemoryIndices (ss.2.2 g)).card)) := by
    rw [abs_of_nonneg (rawEdgeWeight_nonneg r n A ν u ss tt tr hV htilted), hw_eq,
      hbig_prod, hsmall_prod]
    unfold rawEdgeWeight
    rw [pow_add]
    ring
  rw [hlhs_eq]
  calc (ν.auxMass u * P.memoryWeight r.v ss * (B_prod * S_prod)) *
        (smallDamping F J ss.1 *
          r.rho ^ (∑ g : P.BigGroup, (zeroMemoryIndices (ss.2.2 g)).card))
      ≤ (ν.auxMass u * P.memoryWeight r.v ss * (B_prod * S_prod)) * 1 := by
        apply mul_le_mul_of_nonneg_left hdamp
        exact mul_nonneg (mul_nonneg haux_nn (memoryWeight_nonneg r ss)) (mul_nonneg hB_nn hS_nn)
    _ = ν.auxMass u * P.memoryWeight r.v ss * (B_prod * S_prod) := mul_one _

/-- Inner sum over target labels `b_g` for a single big group. -/
def bigChoiceLabelSum (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (ν : Pattern P J F.ell m) (delta : ℤ) (ss : P.MemoryState (J + F.ell))
    (g : P.BigGroup) (B_g A_g : Finset (Fin (J + F.ell)))
    (f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin (ss.2.2 g).card) : ℝ :=
  ∑ b_g : Fin (J + F.ell) → P.Prime g.val,
    if bigGroupValid ν delta g (ss.2.1 g.val) (ss.2.2 g) B_g A_g f_g b_g then
      bigGroupWeight F r n ν delta g (ss.2.1 g.val) (ss.2.2 g) B_g A_g f_g b_g
    else 0

/-- Sum over retrieval maps `f_g` and target labels `b_g` for a single big group. -/
def bigChoiceMapSum (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (ν : Pattern P J F.ell m) (delta : ℤ) (ss : P.MemoryState (J + F.ell))
    (g : P.BigGroup) (B_g A_g : Finset (Fin (J + F.ell))) : ℝ :=
  ∑ f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin (ss.2.2 g).card,
    bigChoiceLabelSum F r n ν delta ss g B_g A_g f_g

/-- Sum over retrieved sets `A_g`, retrieval maps `f_g`, and target labels `b_g` for a single big group. -/
def bigChoiceRetrSum (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (ν : Pattern P J F.ell m) (delta : ℤ) (ss : P.MemoryState (J + F.ell))
    (g : P.BigGroup) (B_g : Finset (Fin (J + F.ell))) : ℝ :=
  ∑ A_g : Finset (Fin (J + F.ell)),
    bigChoiceMapSum F r n ν delta ss g B_g A_g

lemma prod_le_const_pow {α : Type*} [Fintype α] (f : α → ℝ) (C : ℝ)
    (hf0 : ∀ a, 0 ≤ f a) (hfC : ∀ a, f a ≤ C) :
    ∏ a : α, f a ≤ C ^ Fintype.card α := by
  classical
  rw [← Finset.card_univ]
  have h : ∀ s : Finset α, ∏ a ∈ s, f a ≤ C ^ s.card := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
      exact mul_le_mul (hfC a) ih (Finset.prod_nonneg (fun x _ => hf0 x))
        (le_trans (hf0 a) (hfC a))
  exact h Finset.univ

/-- Sum over `(tr, b)` of the factorized group products is bounded by
`Cbig ^ card BigGroup * Csmall ^ card SmallGroup`. -/
lemma sum_transfer_labels_le (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (Cprom Csmall0 : ℝ) (hCsmall0_pos : 0 < Csmall0)
    (hCprom : ∀ Z' a : ℕ, a ≤ F.ell + m → (Z' : ℝ) ^ a * r.rho ^ (Z' - a) ≤ Cprom)
    (hCsmall0 : ∀ Y : ℕ, F.ell ≤ Y →
      (Y : ℝ) ^ F.ell * F.q ^ ((((Y - F.ell : ℕ)) : ℝ) / 2) ≤ Csmall0)
    (hVlo : ∀ g : P.Group, F.vMin ≤ P.V g)
    (htilted_nn : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (htilted_sum : ∀ g : P.BigGroup, ∑ p : P.Prime g.val, tiltedMu F P n g.val p ≤ 2)
    (ν : Pattern P J F.ell m) (delta : ℤ) (ss : P.MemoryState (J + F.ell)) :
    (∑ tr : TransferChoice ss,
      ∑ b : P.Labels (J + F.ell),
        (∏ g : P.BigGroup,
          if bigGroupValid ν delta g (ss.2.1 g.val) (ss.2.2 g)
              (tr.1 g) (tr.2.1 g) (tr.2.2 g) (b g.val) then
            bigGroupWeight F r n ν delta g (ss.2.1 g.val) (ss.2.2 g)
              (tr.1 g) (tr.2.1 g) (tr.2.2 g) (b g.val)
          else 0) *
        (∏ g : P.SmallGroup,
          if b g.val ∈ smallPrefixFibre J F.ell
              (translateSmallResidues delta ss.1 g)
              (fun j => ss.2.1 g.val (Fin.castAdd F.ell j)) then
            smallGroupWeight F J g (translateSmallResidues delta ss.1 g)
          else 0)) ≤
      (bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
        (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^ Fintype.card P.SmallGroup := by
  classical
  have hVpos : ∀ g : P.Group, 0 < P.V g := fun g => lt_of_lt_of_le F.vMin_pos (hVlo g)
  let F_small : (g : P.SmallGroup) → (Fin (J + F.ell) → P.Prime g.val) → ℝ :=
    fun g b_g =>
      if b_g ∈ smallPrefixFibre J F.ell
          (translateSmallResidues delta ss.1 g)
          (fun j => ss.2.1 g.val (Fin.castAdd F.ell j)) then
        smallGroupWeight F J g (translateSmallResidues delta ss.1 g)
      else 0
  let F_big : TransferChoice ss → (g : P.BigGroup) → (Fin (J + F.ell) → P.Prime g.val) → ℝ :=
    fun tr g b_g =>
      if bigGroupValid ν delta g (ss.2.1 g.val) (ss.2.2 g)
          (tr.1 g) (tr.2.1 g) (tr.2.2 g) b_g then
        bigGroupWeight F r n ν delta g (ss.2.1 g.val) (ss.2.2 g)
          (tr.1 g) (tr.2.1 g) (tr.2.2 g) b_g
      else 0
  have hinner : (∑ tr : TransferChoice ss,
      ∑ b : P.Labels (J + F.ell),
        (∏ g : P.BigGroup, F_big tr g (b g.val)) *
        (∏ g : P.SmallGroup, F_small g (b g.val))) =
      (∑ tr : TransferChoice ss,
        ∏ g : P.BigGroup, bigChoiceLabelSum F r n ν delta ss g (tr.1 g) (tr.2.1 g) (tr.2.2 g)) *
      (∏ g : P.SmallGroup, ∑ b_g : Fin (J + F.ell) → P.Prime g.val, F_small g b_g) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun tr _ => sum_labels_split (F_big tr) F_small)
  have hgoal_eq : (∑ tr : TransferChoice ss,
      ∑ b : P.Labels (J + F.ell),
        (∏ g : P.BigGroup,
          if bigGroupValid ν delta g (ss.2.1 g.val) (ss.2.2 g)
              (tr.1 g) (tr.2.1 g) (tr.2.2 g) (b g.val) then
            bigGroupWeight F r n ν delta g (ss.2.1 g.val) (ss.2.2 g)
              (tr.1 g) (tr.2.1 g) (tr.2.2 g) (b g.val)
          else 0) *
        (∏ g : P.SmallGroup,
          if b g.val ∈ smallPrefixFibre J F.ell
              (translateSmallResidues delta ss.1 g)
              (fun j => ss.2.1 g.val (Fin.castAdd F.ell j)) then
            smallGroupWeight F J g (translateSmallResidues delta ss.1 g)
          else 0)) =
      (∑ tr : TransferChoice ss,
        ∏ g : P.BigGroup, bigChoiceLabelSum F r n ν delta ss g (tr.1 g) (tr.2.1 g) (tr.2.2 g)) *
      (∏ g : P.SmallGroup, ∑ b_g : Fin (J + F.ell) → P.Prime g.val, F_small g b_g) := hinner
  rw [hgoal_eq]
  have htr_eq : (∑ tr : TransferChoice ss,
      ∏ g : P.BigGroup, bigChoiceLabelSum F r n ν delta ss g (tr.1 g) (tr.2.1 g) (tr.2.2 g)) =
      ∏ g : P.BigGroup, ∑ B_g : Finset (Fin (J + F.ell)),
        bigChoiceRetrSum F r n ν delta ss g B_g := by
    unfold TransferChoice
    rw [Fintype.sum_prod_type]
    have hstep1 : ∀ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
        (∑ p : (A : (g : P.BigGroup) → Finset (Fin (J + F.ell))) ×
            ((g : P.BigGroup) → (i : {i : Fin (J + F.ell) // i ∈ A g}) → Fin (ss.2.2 g).card),
          ∏ g : P.BigGroup, bigChoiceLabelSum F r n ν delta ss g (B g) (p.1 g) (p.2 g)) =
        ∏ g : P.BigGroup, bigChoiceRetrSum F r n ν delta ss g (B g) := by
      intro B
      rw [Fintype.sum_sigma]
      have hstep_f : (∑ a : P.BigGroup → Finset (Fin (J + F.ell)),
          ∑ f : (g : P.BigGroup) → {idx : Fin (J + F.ell) // idx ∈ a g} → Fin (ss.2.2 g).card,
            ∏ g : P.BigGroup, bigChoiceLabelSum F r n ν delta ss g (B g) (a g) (f g)) =
          ∑ a : P.BigGroup → Finset (Fin (J + F.ell)),
            ∏ g : P.BigGroup, bigChoiceMapSum F r n ν delta ss g (B g) (a g) :=
        Finset.sum_congr rfl (fun a _ =>
          sum_pi_prod (fun g f_g => bigChoiceLabelSum F r n ν delta ss g (B g) (a g) f_g))
      rw [hstep_f]
      exact sum_pi_prod (fun g A_g => bigChoiceMapSum F r n ν delta ss g (B g) A_g)
    have hstep2 : (∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
        ∑ p : (A : (g : P.BigGroup) → Finset (Fin (J + F.ell))) ×
            ((g : P.BigGroup) → (i : {i : Fin (J + F.ell) // i ∈ A g}) → Fin (ss.2.2 g).card),
          ∏ g : P.BigGroup, bigChoiceLabelSum F r n ν delta ss g (B g) (p.1 g) (p.2 g)) =
        ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
          ∏ g : P.BigGroup, bigChoiceRetrSum F r n ν delta ss g (B g) :=
      Finset.sum_congr rfl (fun B _ => hstep1 B)
    rw [hstep2]
    exact sum_pi_prod (fun g B_g => bigChoiceRetrSum F r n ν delta ss g B_g)
  rw [htr_eq]
  have hbig_prod_le : (∏ g : P.BigGroup,
      ∑ B_g : Finset (Fin (J + F.ell)), bigChoiceRetrSum F r n ν delta ss g B_g) ≤
      (bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup := by
    apply prod_le_const_pow
    · intro g
      unfold bigChoiceRetrSum bigChoiceMapSum bigChoiceLabelSum
      refine Finset.sum_nonneg (fun B_g _ => Finset.sum_nonneg (fun A_g _ =>
        Finset.sum_nonneg (fun f_g _ => Finset.sum_nonneg (fun b_g _ => ?_))))
      split_ifs
      · exact bigGroupWeight_nonneg F r n ν delta g (hVpos g.val) (htilted_nn g) _ _ _ _ _ _
      · exact le_refl 0
    · intro g
      unfold bigChoiceRetrSum bigChoiceMapSum bigChoiceLabelSum
      exact bigGroup_sum_le F r n Cprom hCprom ν delta g (hVlo g.val)
        (htilted_nn g) (htilted_sum g) (ss.2.1 g.val) (ss.2.2 g)
  have hsmall_prod_le : (∏ g : P.SmallGroup,
      ∑ b_g : Fin (J + F.ell) → P.Prime g.val, F_small g b_g) ≤
      (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^ Fintype.card P.SmallGroup := by
    apply prod_le_const_pow
    · intro g
      refine Finset.sum_nonneg (fun b_g _ => ?_)
      dsimp [F_small]
      split_ifs
      · exact smallGroupWeight_nonneg F J g (hVpos g.val) _
      · exact le_refl 0
    · intro g
      exact smallPrefixFibre_sum_le F J m Csmall0 hCsmall0_pos hCsmall0 g (hVlo g.val) _ _
  apply mul_le_mul hbig_prod_le hsmall_prod_le
  · refine Finset.prod_nonneg (fun g _ => Finset.sum_nonneg (fun b_g _ => ?_))
    dsimp [F_small]
    split_ifs
    · exact smallGroupWeight_nonneg F J g (hVpos g.val) _
    · exact le_refl 0
  · exact pow_nonneg (bigGroupConst_pos F r m Cprom).le _

/-- For a fixed choice `c : EdgeChoice A s`, summing over `t ∈ S` is bounded by the
sum over target labels `b : P.Labels (J + F.ell)`. -/
lemma sum_target_for_choice_le (r : MemoryParameters F) (n : ℕ) (theta : ℝ) (i : Fin n)
    (A : Model F P J m) (s : P.MemoryState (J + F.ell)) (c : EdgeChoice A s)
    (S : Finset (P.MemoryState (J + F.ell)))
    (hV : ∀ g : P.Group, 0 < P.V g)
    (htilted : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p) :
    (∑ t ∈ S,
      if edgeChoiceValid A .all i s t c then
        ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ * P.memoryWeight r.v t
      else 0) ≤
    patternSup A c.2.2.1 * (A.pattern c.2.2.1).auxMass c.2.2.2.1 * P.memoryWeight r.v s *
      (∑ b : P.Labels (J + F.ell),
        (∏ g : P.BigGroup,
          if bigGroupValid (A.pattern c.2.2.1)
              (edgeDelta A (A.pattern c.2.2.1) (edgeForward i) (permuteActive c.1 s).2.1 c.2.2.2.1)
              g ((permuteActive c.1 s).2.1 g.val) (s.2.2 g)
              (c.2.2.2.2.1 g) (c.2.2.2.2.2.1 g) (c.2.2.2.2.2.2 g) (b g.val) then
            bigGroupWeight F r n (A.pattern c.2.2.1)
              (edgeDelta A (A.pattern c.2.2.1) (edgeForward i) (permuteActive c.1 s).2.1 c.2.2.2.1)
              g ((permuteActive c.1 s).2.1 g.val) (s.2.2 g)
              (c.2.2.2.2.1 g) (c.2.2.2.2.2.1 g) (c.2.2.2.2.2.2 g) (b g.val)
          else 0) *
        (∏ g : P.SmallGroup,
          if b g.val ∈ smallPrefixFibre J F.ell
              (translateSmallResidues
                (edgeDelta A (A.pattern c.2.2.1) (edgeForward i) (permuteActive c.1 s).2.1 c.2.2.2.1)
                s.1 g)
              (fun j => (permuteActive c.1 s).2.1 g.val (Fin.castAdd F.ell j)) then
            smallGroupWeight F J g (translateSmallResidues
              (edgeDelta A (A.pattern c.2.2.1) (edgeForward i) (permuteActive c.1 s).2.1 c.2.2.2.1)
              s.1 g)
          else 0)) := by
  classical
  set ss := permuteActive c.1 s
  set ν := A.pattern c.2.2.1
  set u := c.2.2.2.1
  set tr := c.2.2.2.2
  set delta := edgeDelta A ν (edgeForward i) ss.2.1 u
  let Term : P.Labels (J + F.ell) → ℝ := fun b =>
    (∏ g : P.BigGroup,
      if bigGroupValid ν delta g (ss.2.1 g.val) (s.2.2 g)
          (tr.1 g) (tr.2.1 g) (tr.2.2 g) (b g.val) then
        bigGroupWeight F r n ν delta g (ss.2.1 g.val) (s.2.2 g)
          (tr.1 g) (tr.2.1 g) (tr.2.2 g) (b g.val)
      else 0) *
    (∏ g : P.SmallGroup,
      if b g.val ∈ smallPrefixFibre J F.ell
          (translateSmallResidues delta s.1 g)
          (fun j => ss.2.1 g.val (Fin.castAdd F.ell j)) then
        smallGroupWeight F J g (translateSmallResidues delta s.1 g)
      else 0)
  have hTerm_nn : ∀ b : P.Labels (J + F.ell), 0 ≤ Term b := by
    intro b
    apply mul_nonneg
    · apply Finset.prod_nonneg (fun g _ => ?_)
      split_ifs
      · exact bigGroupWeight_nonneg F r n ν delta g (hV g.val) (htilted g) _ _ _ _ _ _
      · exact le_refl 0
    · apply Finset.prod_nonneg (fun g _ => ?_)
      split_ifs
      · exact smallGroupWeight_nonneg F J g (hV g.val) _
      · exact le_refl 0
  have hpt : ∀ t ∈ S.filter (fun t => edgeChoiceValid A .all i s t c),
      ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ * P.memoryWeight r.v t ≤
        patternSup A c.2.2.1 * ν.auxMass u * P.memoryWeight r.v s * Term (P.act c.2.1 t.2.1) := by
    intro t ht
    have hval : edgeChoiceValid A .all i s t c := (Finset.mem_filter.mp ht).2
    have hcoeff := edgeChoiceCoefficient_norm_le_patternSup A n r.rho theta i s t c
    have hraw := rawEdgeWeight_mul_weight_le r n A ν (edgeForward i) u ss (permuteActive c.2.1 t)
      tr hV htilted hval.1
    have hwt_t : P.memoryWeight r.v (permuteActive c.2.1 t) = P.memoryWeight r.v t := rfl
    have hwt_s : P.memoryWeight r.v ss = P.memoryWeight r.v s := rfl
    rw [hwt_t, hwt_s] at hraw
    calc ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ * P.memoryWeight r.v t
        ≤ (patternSup A c.2.2.1 *
            |rawEdgeWeight A n r.rho ν u ss (permuteActive c.2.1 t) tr|) *
            P.memoryWeight r.v t :=
          mul_le_mul_of_nonneg_right hcoeff (memoryWeight_nonneg r t)
      _ = patternSup A c.2.2.1 *
          (|rawEdgeWeight A n r.rho ν u ss (permuteActive c.2.1 t) tr| *
            P.memoryWeight r.v t) := by ring
      _ ≤ patternSup A c.2.2.1 *
          (ν.auxMass u * P.memoryWeight r.v s * Term (P.act c.2.1 t.2.1)) :=
          mul_le_mul_of_nonneg_left hraw (patternSup_nonneg A c.2.2.1)
      _ = patternSup A c.2.2.1 * ν.auxMass u * P.memoryWeight r.v s *
          Term (P.act c.2.1 t.2.1) := by ring
  have hinj : Set.InjOn (fun t : P.MemoryState (J + F.ell) => P.act c.2.1 t.2.1)
      (S.filter (fun t => edgeChoiceValid A .all i s t c)) := by
    intro t₁ ht₁ t₂ ht₂ heq
    have hv₁ : edgeChoiceValid A .all i s t₁ c := (Finset.mem_filter.mp (Finset.mem_coe.mp ht₁)).2
    have hv₂ : edgeChoiceValid A .all i s t₂ c := (Finset.mem_filter.mp (Finset.mem_coe.mp ht₂)).2
    have h1 : t₁.1 = t₂.1 := (valid_target_small A i s t₁ c hv₁).trans
      (valid_target_small A i s t₂ c hv₂).symm
    have h2 : t₁.2.1 = t₂.2.1 := by
      funext g j
      have hj := congrArg (fun b : P.Labels (J + F.ell) => b g ((c.2.1 g).symm j)) heq
      simpa [PrimeGroups.act] using hj
    have h3 : t₁.2.2 = t₂.2.2 := by
      funext g
      exact (valid_target_mem A i s t₁ c hv₁ g).trans (valid_target_mem A i s t₂ c hv₂ g).symm
    cases t₁ with
    | mk y₁ p₁ =>
      cases p₁ with
      | mk a₁ m₁ =>
        cases t₂ with
        | mk y₂ p₂ =>
          cases p₂ with
          | mk a₂ m₂ =>
            dsimp at h1 h2 h3
            subst h1 h2 h3
            rfl
  have hsum_img : (∑ t ∈ S.filter (fun t => edgeChoiceValid A .all i s t c),
      Term (P.act c.2.1 t.2.1)) ≤ ∑ b : P.Labels (J + F.ell), Term b := by
    rw [← Finset.sum_image hinj]
    exact Finset.sum_le_univ_sum_of_nonneg hTerm_nn
  have hC_nn : 0 ≤ patternSup A c.2.2.1 * ν.auxMass u * P.memoryWeight r.v s := by
    apply mul_nonneg
    · apply mul_nonneg (patternSup_nonneg A c.2.2.1)
      unfold Pattern.auxMass
      exact Finset.prod_nonneg (fun g _ =>
        Finset.prod_nonneg (fun j _ => (mu_pos_of_V_pos g (hV g) (u g j)).le))
    · exact memoryWeight_nonneg r s
  calc (∑ t ∈ S,
        if edgeChoiceValid A .all i s t c then
          ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ * P.memoryWeight r.v t
        else 0)
      = ∑ t ∈ S.filter (fun t => edgeChoiceValid A .all i s t c),
          ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ * P.memoryWeight r.v t := by
        rw [← Finset.sum_filter]
    _ ≤ ∑ t ∈ S.filter (fun t => edgeChoiceValid A .all i s t c),
          patternSup A c.2.2.1 * ν.auxMass u * P.memoryWeight r.v s *
            Term (P.act c.2.1 t.2.1) :=
        Finset.sum_le_sum hpt
    _ = patternSup A c.2.2.1 * ν.auxMass u * P.memoryWeight r.v s *
          ∑ t ∈ S.filter (fun t => edgeChoiceValid A .all i s t c),
            Term (P.act c.2.1 t.2.1) := by
        rw [← Finset.mul_sum]
    _ ≤ patternSup A c.2.2.1 * ν.auxMass u * P.memoryWeight r.v s *
          ∑ b : P.Labels (J + F.ell), Term b :=
        mul_le_mul_of_nonneg_left hsum_img hC_nn

/-- Row bound: absolute row tsum dominated by `L^Ca` times weight. -/
theorem row_tsum_le (F : FixedData) (r : MemoryParameters F) (m : ℕ) (C₁ : ℝ) :
    ∃ Ca : ℝ, ∀ J : ℕ, ∃ x₀ : ℝ, ∀ x : ℝ, x ≥ x₀ → ∀ P : PrimeGroups,
      P.Admissible F x → ∀ A : Model F P J m, A.patternMass ≤ (L x) ^ C₁ →
      ∀ (theta : ℝ) (i : Fin (N x)) (s : P.MemoryState (J + F.ell)),
        ∑' t, ‖((absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t : ℝ) : ℂ)‖ *
          P.memoryWeight r.v t ≤
          (L x) ^ Ca * P.memoryWeight r.v s := by
  classical
  obtain ⟨Cprom, hCprom_pos, hCprom⟩ :=
    promo_allmaps_bound r.rho r.rho_pos r.rho_lt (F.ell + m)
  obtain ⟨Csmall0, hCsmall0_pos, hCsmall0⟩ :=
    small_count_damp F.q F.q_pos F.q_lt F.ell
  let Cbig := bigGroupConst F r m Cprom
  have hCbig_ge : 1 ≤ Cbig := bigGroupConst_ge_one F r m Cprom
  have hCbig_pos : 0 < Cbig := bigGroupConst_pos F r m Cprom
  let Csmall := max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)
  have hCsmall_ge : 1 ≤ Csmall := le_max_left _ _
  have hCsmall_pos : 0 < Csmall := lt_of_lt_of_le zero_lt_one hCsmall_ge
  let Kbig : ℝ := F.C₀ * Real.log Cbig
  let Ksmall : ℝ := F.C₀ * Real.log Csmall
  have hKbig_nn : 0 ≤ Kbig := mul_nonneg F.C₀_pos.le (Real.log_nonneg hCbig_ge)
  have hKsmall_nn : 0 ≤ Ksmall := mul_nonneg F.C₀_pos.le (Real.log_nonneg hCsmall_ge)
  refine ⟨C₁ + Kbig + Ksmall, fun J => ?_⟩
  let xfact : ℝ := 10 * ((taylorTerms F).factorial : ℝ)
  refine ⟨max 3 (Real.exp xfact), fun x hx P hP A hA theta i s => ?_⟩
  have hx3 : 3 ≤ x := le_trans (le_max_left _ _) hx
  have hxexp : Real.exp xfact ≤ x := le_trans (le_max_right _ _) hx
  have hL1 : 1 < L x := one_lt_L hx3
  have hLpos : 0 < L x := lt_trans zero_lt_one hL1
  have hLfact : xfact ≤ L x := by
    have hlog := Real.log_le_log (Real.exp_pos _) hxexp
    rwa [Real.log_exp] at hlog
  have hx1 : 1 ≤ L x := hL1.le
  have hL10 : 10 * ((taylorTerms F).factorial : ℝ) ≤ L x := hLfact
  have hVlo : ∀ g : P.Group, F.vMin ≤ P.V g := fun g => (hP.2.2.2.2.1 g).1
  have hVpos : ∀ g : P.Group, 0 < P.V g := fun g => V_pos_of_adm hP g
  have hVne : ∀ g : P.Group, P.V g ≠ 0 := fun g => ne_of_gt (hVpos g)
  have htilted_nn : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P (N x) g.val p :=
    fun g p => (tiltedMu_pos hx1 hP (N x) rfl hL10 g p).le
  have htilted_sum : ∀ g : P.BigGroup, ∑ p : P.Prime g.val, tiltedMu F P (N x) g.val p ≤ 2 :=
    fun g => tiltedMu_sum_le_two hx1 hP (N x) rfl hL10 g
  have hcard_big : ((Fintype.card P.BigGroup : ℕ) : ℝ) ≤ F.C₀ * Real.log (L x) := by
    have hle : (P.bigGroups.card : ℝ) ≤ F.C₀ * T x := hP.2.2.2.1
    have hcard_eq : (Fintype.card P.BigGroup : ℝ) = (P.bigGroups.card : ℝ) := by
      rw [PrimeGroups.bigGroups]
      simp [Fintype.card_subtype]
    rw [hcard_eq]
    exact hle
  have hcard_small : ((Fintype.card P.SmallGroup : ℕ) : ℝ) ≤ F.C₀ * Real.log (L x) := by
    have hle : (P.smallGroups.card : ℝ) ≤ F.C₀ * T x := hP.2.1
    have hcard_eq : (Fintype.card P.SmallGroup : ℝ) = (P.smallGroups.card : ℝ) := by
      rw [PrimeGroups.smallGroups]
      simp [Fintype.card_subtype]
    rw [hcard_eq]
    exact hle
  have hbig_pow : Cbig ^ Fintype.card P.BigGroup ≤ (L x) ^ Kbig :=
    pow_groups_le_rpow Cbig hCbig_pos _ F.C₀ (L x) Kbig
      F.C₀_pos hL1 hKbig_nn (le_refl _) hcard_big
  have hsmall_pow : Csmall ^ Fintype.card P.SmallGroup ≤ (L x) ^ Ksmall :=
    pow_groups_le_rpow Csmall hCsmall_pos _ F.C₀ (L x) Ksmall
      F.C₀_pos hL1 hKsmall_nn (le_refl _) hcard_small
  have hwpos : 0 < P.memoryWeight r.v s := memoryWeight_pos r s
  have hfin : Set.Finite {t : P.MemoryState (J + F.ell) |
      absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t ≠ 0} :=
    row_kernel_set_finite A r.rho theta i s
  have htsum_eq : (∑' t, ‖((absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t : ℝ) : ℂ)‖ *
        P.memoryWeight r.v t) =
      ∑ t ∈ hfin.toFinset,
        absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t * P.memoryWeight r.v t := by
    rw [tsum_eq_sum]
    · apply Finset.sum_congr rfl
      intro t _
      rw [norm_cast_absolute]
    · intro b hb
      have hnot : b ∉ {t : P.MemoryState (J + F.ell) |
          absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t ≠ 0} :=
        fun hcon => hb (hfin.mem_toFinset.mpr hcon)
      simp only [Set.mem_setOf_eq, ne_eq, not_not] at hnot
      rw [norm_cast_absolute, hnot, zero_mul]
  let P_all : ℝ := Cbig ^ Fintype.card P.BigGroup * Csmall ^ Fintype.card P.SmallGroup
  have hP_all_nn : 0 ≤ P_all :=
    mul_nonneg (pow_nonneg hCbig_pos.le _) (pow_nonneg hCsmall_pos.le _)
  have hrow_fin_le : ∑ t ∈ hfin.toFinset,
        absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t * P.memoryWeight r.v t ≤
      A.patternMass * (Cbig ^ Fintype.card P.BigGroup) *
        (Csmall ^ Fintype.card P.SmallGroup) * P.memoryWeight r.v s := by
    have hswap : (∑ t ∈ hfin.toFinset,
          absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t * P.memoryWeight r.v t) =
        edgeSymmetryFactor P (J + F.ell) *
          ∑ c : EdgeChoice A s,
            ∑ t ∈ hfin.toFinset,
              if edgeChoiceValid A .all i s t c then
                ‖edgeChoiceCoefficient A (N x) r.rho theta i s t c‖ * P.memoryWeight r.v t
              else 0 := by
      unfold absoluteMemoryEdgeKernel
      simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
    rw [hswap]
    have hc_sum : (∑ c : EdgeChoice A s,
          ∑ t ∈ hfin.toFinset,
            if edgeChoiceValid A .all i s t c then
              ‖edgeChoiceCoefficient A (N x) r.rho theta i s t c‖ * P.memoryWeight r.v t
            else 0) ≤
        ((Fintype.card (P.Permutations (J + F.ell)) : ℝ) ^ (2 : ℕ)) *
          (A.patternMass * P_all * P.memoryWeight r.v s) := by
      calc (∑ c : EdgeChoice A s,
            ∑ t ∈ hfin.toFinset,
              if edgeChoiceValid A .all i s t c then
                ‖edgeChoiceCoefficient A (N x) r.rho theta i s t c‖ * P.memoryWeight r.v t
              else 0)
          ≤ ∑ c : EdgeChoice A s,
              patternSup A c.2.2.1 * (A.pattern c.2.2.1).auxMass c.2.2.2.1 * P.memoryWeight r.v s *
                (∑ b : P.Labels (J + F.ell),
                  (∏ g : P.BigGroup,
                    if bigGroupValid (A.pattern c.2.2.1)
                        (edgeDelta A (A.pattern c.2.2.1) (edgeForward i) (permuteActive c.1 s).2.1 c.2.2.2.1)
                        g ((permuteActive c.1 s).2.1 g.val) (s.2.2 g)
                        (c.2.2.2.2.1 g) (c.2.2.2.2.2.1 g) (c.2.2.2.2.2.2 g) (b g.val) then
                      bigGroupWeight F r (N x) (A.pattern c.2.2.1)
                        (edgeDelta A (A.pattern c.2.2.1) (edgeForward i) (permuteActive c.1 s).2.1 c.2.2.2.1)
                        g ((permuteActive c.1 s).2.1 g.val) (s.2.2 g)
                        (c.2.2.2.2.1 g) (c.2.2.2.2.2.1 g) (c.2.2.2.2.2.2 g) (b g.val)
                    else 0) *
                  (∏ g : P.SmallGroup,
                    if b g.val ∈ smallPrefixFibre J F.ell
                        (translateSmallResidues
                          (edgeDelta A (A.pattern c.2.2.1) (edgeForward i) (permuteActive c.1 s).2.1 c.2.2.2.1)
                          s.1 g)
                        (fun j => (permuteActive c.1 s).2.1 g.val (Fin.castAdd F.ell j)) then
                      smallGroupWeight F J g (translateSmallResidues
                        (edgeDelta A (A.pattern c.2.2.1) (edgeForward i) (permuteActive c.1 s).2.1 c.2.2.2.1)
                        s.1 g)
                    else 0)) :=
            Finset.sum_le_sum (fun c _ => sum_target_for_choice_le r (N x) theta i A s c hfin.toFinset hVpos htilted_nn)
        _ = ∑ π : P.Permutations (J + F.ell),
              ∑ τ : P.Permutations (J + F.ell),
                ∑ v : Fin A.patternCount,
                  ∑ u : P.Aux J,
                    (patternSup A v * (A.pattern v).auxMass u * P.memoryWeight r.v s) *
                      ∑ tr : TransferChoice s,
                        ∑ b : P.Labels (J + F.ell),
                          (∏ g : P.BigGroup,
                            if bigGroupValid (A.pattern v)
                                (edgeDelta A (A.pattern v) (edgeForward i) (permuteActive π s).2.1 u)
                                g ((permuteActive π s).2.1 g.val) (s.2.2 g)
                                (tr.1 g) (tr.2.1 g) (tr.2.2 g) (b g.val) then
                              bigGroupWeight F r (N x) (A.pattern v)
                                (edgeDelta A (A.pattern v) (edgeForward i) (permuteActive π s).2.1 u)
                                g ((permuteActive π s).2.1 g.val) (s.2.2 g)
                                (tr.1 g) (tr.2.1 g) (tr.2.2 g) (b g.val)
                            else 0) *
                          (∏ g : P.SmallGroup,
                            if b g.val ∈ smallPrefixFibre J F.ell
                                (translateSmallResidues
                                  (edgeDelta A (A.pattern v) (edgeForward i) (permuteActive π s).2.1 u)
                                  s.1 g)
                                (fun j => (permuteActive π s).2.1 g.val (Fin.castAdd F.ell j)) then
                              smallGroupWeight F J g (translateSmallResidues
                                (edgeDelta A (A.pattern v) (edgeForward i) (permuteActive π s).2.1 u)
                                s.1 g)
                            else 0) := by
            unfold EdgeChoice
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl (fun π _ => ?_)
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl (fun τ _ => ?_)
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl (fun v _ => ?_)
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl (fun u _ => ?_)
            dsimp only []
            rw [← Finset.mul_sum]
        _ ≤ ∑ _π : P.Permutations (J + F.ell),
              ∑ _τ : P.Permutations (J + F.ell),
                ∑ v : Fin A.patternCount,
                  ∑ u : P.Aux J,
                    (patternSup A v * (A.pattern v).auxMass u * P.memoryWeight r.v s) * P_all := by
            apply Finset.sum_le_sum (fun π _ => Finset.sum_le_sum (fun τ _ =>
              Finset.sum_le_sum (fun v _ => Finset.sum_le_sum (fun u _ => ?_))))
            apply mul_le_mul_of_nonneg_left
              (sum_transfer_labels_le F r (N x) Cprom Csmall0 hCsmall0_pos hCprom hCsmall0
                hVlo htilted_nn htilted_sum (A.pattern v)
                (edgeDelta A (A.pattern v) (edgeForward i) (permuteActive π s).2.1 u)
                (permuteActive π s))
            apply mul_nonneg
            · apply mul_nonneg (patternSup_nonneg A v)
              unfold Pattern.auxMass
              exact Finset.prod_nonneg (fun g _ =>
                Finset.prod_nonneg (fun j _ => (mu_pos_of_V_pos g (hVpos g) (u g j)).le))
            · exact memoryWeight_nonneg r s
        _ = ((Fintype.card (P.Permutations (J + F.ell)) : ℝ) ^ (2 : ℕ)) *
              (A.patternMass * P_all * P.memoryWeight r.v s) := by
            have hu : ∀ v : Fin A.patternCount,
                (∑ u : P.Aux J, (patternSup A v * (A.pattern v).auxMass u * P.memoryWeight r.v s) * P_all) =
                patternSup A v * (P.memoryWeight r.v s * P_all) := by
              intro v
              have h1 : (∑ u : P.Aux J, (patternSup A v * (A.pattern v).auxMass u * P.memoryWeight r.v s) * P_all) =
                  patternSup A v * (∑ u : P.Aux J, (A.pattern v).auxMass u) * (P.memoryWeight r.v s * P_all) := by
                rw [Finset.mul_sum, Finset.sum_mul]
                apply Finset.sum_congr rfl (fun u _ => by ring)
              rw [h1, auxMass_sum_eq_one (A.pattern v) hVne, mul_one]
            simp_rw [hu, ← Finset.sum_mul, sum_patternSup_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
    calc (edgeSymmetryFactor P (J + F.ell) *
          ∑ c : EdgeChoice A s,
            ∑ t ∈ hfin.toFinset,
              if edgeChoiceValid A .all i s t c then
                ‖edgeChoiceCoefficient A (N x) r.rho theta i s t c‖ * P.memoryWeight r.v t
              else 0)
        ≤ edgeSymmetryFactor P (J + F.ell) *
            (((Fintype.card (P.Permutations (J + F.ell)) : ℝ) ^ (2 : ℕ)) *
              (A.patternMass * P_all * P.memoryWeight r.v s)) :=
          mul_le_mul_of_nonneg_left hc_sum (edgeSymmetryFactor_nonneg P (J + F.ell))
      _ = A.patternMass * (Cbig ^ Fintype.card P.BigGroup) *
            (Csmall ^ Fintype.card P.SmallGroup) * P.memoryWeight r.v s := by
          unfold edgeSymmetryFactor
          have hcard_pos : (0 : ℝ) < (Fintype.card (P.Permutations (J + F.ell)) : ℝ) ^ (2 : ℕ) := by
            positivity
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard_pos), one_mul]
          dsimp [P_all]
          ring
  rw [htsum_eq]
  calc ∑ t ∈ hfin.toFinset,
        absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t * P.memoryWeight r.v t
      ≤ A.patternMass * (Cbig ^ Fintype.card P.BigGroup) *
          (Csmall ^ Fintype.card P.SmallGroup) * P.memoryWeight r.v s := hrow_fin_le
    _ ≤ ((L x) ^ C₁) * ((L x) ^ Kbig) * ((L x) ^ Ksmall) * P.memoryWeight r.v s := by
        have hCb0 : 0 ≤ Cbig ^ Fintype.card P.BigGroup := pow_nonneg hCbig_pos.le _
        have hCs0 : 0 ≤ Csmall ^ Fintype.card P.SmallGroup := pow_nonneg hCsmall_pos.le _
        have hL10' : 0 ≤ (L x) ^ C₁ := Real.rpow_nonneg hLpos.le _
        have hL20 : 0 ≤ (L x) ^ Kbig := Real.rpow_nonneg hLpos.le _
        have hL30 : 0 ≤ (L x) ^ Ksmall := Real.rpow_nonneg hLpos.le _
        have hmid : A.patternMass * (Cbig ^ Fintype.card P.BigGroup) *
            (Csmall ^ Fintype.card P.SmallGroup) ≤
            ((L x) ^ C₁) * ((L x) ^ Kbig) * ((L x) ^ Ksmall) := by
          apply mul_le_mul _ hsmall_pow hCs0 (mul_nonneg hL10' hL20)
          exact mul_le_mul hA hbig_pow hCb0 hL10'
        exact mul_le_mul hmid (le_refl _) hwpos.le (mul_nonneg (mul_nonneg hL10' hL20) hL30)
    _ = (L x) ^ (C₁ + Kbig + Ksmall) * P.memoryWeight r.v s := by
        rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos]

end Erdos821.P3Edge

