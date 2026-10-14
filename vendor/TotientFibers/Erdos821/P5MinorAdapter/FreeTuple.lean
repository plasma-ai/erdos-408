import Erdos821.P5.ComparisonMinorArcAdapterTask
import Erdos821.P4Probe.SelectedTuples
import Erdos821.P4Probe.AuxTupleLaw
import Erdos821.S34.AtomProof

set_option autoImplicit false

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0

namespace Erdos821.P5Madapt
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

local instance graphPrimeFintype {G : Blueprint.Graph.PrimeGroups} (g : G.Group) :
    Fintype (G.Prime g) := by
  change Fintype {p : ℕ // p ∈ G.primes g}
  exact Fintype.ofFinset (G.primes g) (fun _ => Iff.rfl)

variable {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
variable (ν : Pattern G J ell m) (block : G.BigGroup → Bool)

local instance adapterTupleFintype (k : G.Group → ℕ) :
    Fintype (Blueprint.Analytic.Tuple (Erdos821.P4Probe.analyticGroups G) k) :=
  inferInstanceAs (Fintype (∀ g : G.Group, Fin (k g) → G.Prime g))

abbrev sideCoordinates (side : Bool) (g : G.BigGroup) : Finset (Fin J) :=
  Erdos821.P4Probe.patternAuxCoordinates ν block side g

abbrev sideCounts (side : Bool) : Fin G.count → ℕ :=
  Erdos821.P4Probe.selectedCounts (sideCoordinates ν block side)

abbrev SidePartial (side : Bool) :=
  Erdos821.P4Probe.BigRowPartial (sideCoordinates ν block side)

def sidePartial (side : Bool) (u : Erdos821.P5Core.FreeDraw ν) : SidePartial ν block side :=
  fun g i => by
    have hi : i.val ∈ ν.changed g.val := by
      by_cases hb : block g = side
      · simpa [sideCoordinates, Erdos821.P4Probe.patternAuxCoordinates, hb] using i.property
      · have hiEmpty : i.val ∈ (∅ : Finset (Fin J)) := by
          simpa [sideCoordinates, Erdos821.P4Probe.patternAuxCoordinates, hb] using i.property
        simp at hiEmpty
    exact u ⟨g.val, ⟨i.val, hi⟩⟩

def sideTuple (side : Bool) (u : Erdos821.P5Core.FreeDraw ν) :
    Blueprint.Analytic.Tuple (Erdos821.P4Probe.analyticGroups G)
      (sideCounts ν block side) :=
  Erdos821.P4Probe.rowPartialTuple (sideCoordinates ν block side)
    (sidePartial ν block side u)

theorem sideTuple_product (side : Bool) (u : Erdos821.P5Core.FreeDraw ν) :
    Blueprint.Analytic.product (Erdos821.P4Probe.analyticGroups G)
      (sideCounts ν block side) (sideTuple ν block side u) =
      ∏ g : G.BigGroup, ∏ i : {i // i ∈ sideCoordinates ν block side g},
        (sidePartial ν block side u g i).val := by
  exact Erdos821.P4Probe.rowPartialTuple_product _ _

theorem sideTuple_weight (side : Bool) (u : Erdos821.P5Core.FreeDraw ν) :
    Blueprint.Analytic.tupleWeight (Erdos821.P4Probe.analyticGroups G)
      (sideCounts ν block side) (sideTuple ν block side u) =
      ∏ g : G.BigGroup, ∏ i : {i // i ∈ sideCoordinates ν block side g},
        G.mu g.val (sidePartial ν block side u g i) := by
  exact Erdos821.P4Probe.rowPartialTuple_weight _ _

theorem sideTuple_product_eq (side : Bool) (u : Erdos821.P5Core.FreeDraw ν) :
    Blueprint.Analytic.product (Erdos821.P4Probe.analyticGroups G)
      (sideCounts ν block side) (sideTuple ν block side u) =
      Erdos821.P5Core.comparisonFreeProduct ν block side u := by
  rw [sideTuple_product]
  unfold Erdos821.P5Core.comparisonFreeProduct
  apply Finset.prod_congr rfl
  intro g _
  by_cases hb : block g = side
  · let f : Fin J → ℕ := fun i =>
      if hi : block g = side ∧ i ∈ ν.changed g.val then
        (u ⟨g.val, ⟨i, hi.2⟩⟩).val else 1
    have h1 : (∏ i : {i // i ∈ sideCoordinates ν block side g},
        (sidePartial ν block side u g i).val) =
        ∏ i : {i // i ∈ sideCoordinates ν block side g}, f i.val := by
      apply Finset.prod_congr rfl
      intro i _
      have hi : i.val ∈ ν.changed g.val := by
        simpa [sideCoordinates, Erdos821.P4Probe.patternAuxCoordinates, hb] using i.property
      have hcond : block g = side ∧ i.val ∈ ν.changed g.val := ⟨hb, hi⟩
      dsimp [f, sidePartial]
      rw [dite_eq_left hcond]
    rw [h1, Finset.prod_coe_sort (sideCoordinates ν block side g) f]
    have hcoord : sideCoordinates ν block side g = ν.changed g.val := by
      simp [sideCoordinates, Erdos821.P4Probe.patternAuxCoordinates, hb]
    rw [hcoord]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    have hcond : ¬(block g = side ∧ i ∈ ν.changed g.val) := fun h => hi h.2
    dsimp [f]
    exact dite_eq_right hcond
  · have hL : (∏ i : {i // i ∈ sideCoordinates ν block side g},
        (sidePartial ν block side u g i).val) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      have hiEmpty : i.val ∈ (∅ : Finset (Fin J)) := by
        simpa [sideCoordinates, Erdos821.P4Probe.patternAuxCoordinates, hb] using i.property
      exact False.elim (Finset.notMem_empty _ hiEmpty)
    have hR : (∏ i : Fin J,
        if hi : block g = side ∧ i ∈ ν.changed g.val then
          (u ⟨g.val, ⟨i, hi.2⟩⟩).val else 1) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      have hcond : ¬(block g = side ∧ i ∈ ν.changed g.val) := fun h => hb h.1
      exact dite_eq_right hcond
    rw [hL, hR]

theorem sideTuple_freeRestriction (side : Bool) (u : G.Aux J) :
    sideTuple ν block side (Erdos821.P5Core.freeRestriction ν u) =
      Erdos821.P4Probe.selectedAuxTuple ν block side
        (fun g i => u g.val i) := by
  rfl

theorem sum_univ_fintype_irrel {α : Type*} (s t : Fintype α) (f : α → ℂ) :
    Finset.sum (@Finset.univ α s) f = Finset.sum (@Finset.univ α t) f := by
  classical
  have h : (@Finset.univ α s) = (@Finset.univ α t) := by
    ext a
    simp
  exact congrArg (fun s : Finset α => Finset.sum s f) h

def groupRows (J : ℕ) (g : G.Group) := Fin J → G.Prime g

local instance groupRowsFintype (J : ℕ) (g : G.Group) : Fintype (groupRows J g) :=
  inferInstanceAs (Fintype (Fin J → G.Prime g))

def fullRowWeight (J : ℕ) (g : G.Group) (a : groupRows J g) : ℝ :=
  ∏ i : Fin J, G.mu g (a i)

def bigGroupSubtypeEquiv : {g : G.Group // g ∈ G.bigGroups} ≃ G.BigGroup where
  toFun g := ⟨g.val, by simpa [PrimeGroups.bigGroups] using g.property⟩
  invFun g := ⟨g.val, by simp [PrimeGroups.bigGroups, g.property]⟩
  left_inv g := by apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; rfl

def partialBigAuxEquiv :
    Erdos821.P4Probe.PartialSample G.bigGroups (groupRows (G := G) J) ≃ G.BigAux J where
  toFun a := fun g => a ((bigGroupSubtypeEquiv (G := G)).symm g)
  invFun z := fun g => z (bigGroupSubtypeEquiv (G := G) g)
  left_inv a := by
    funext g
    rfl
  right_inv z := by
    funext g
    rfl

theorem partialBigAuxEquiv_auxRestriction (u : G.Aux J) :
    partialBigAuxEquiv (G := G) (J := J)
        (fun g : {g : G.Group // g ∈ G.bigGroups} => u g.val) =
      (fun (g : G.BigGroup) (i : Fin J) => u g.val i) := by
  funext g i
  rfl

theorem partialBigAuxEquiv_weight
    (a : Erdos821.P4Probe.PartialSample G.bigGroups (groupRows (G := G) J)) :
    Erdos821.P4Probe.partialProductWeight (fullRowWeight (G := G) J)
        G.bigGroups a =
      Blueprint.Graph.Pattern.bigAuxMass ν (partialBigAuxEquiv (G := G) (J := J) a) := by
  unfold Erdos821.P4Probe.partialProductWeight fullRowWeight
    Blueprint.Graph.Pattern.bigAuxMass
  apply Fintype.prod_equiv (bigGroupSubtypeEquiv (G := G))
  intro g
  change (∏ i : Fin J, G.mu g.val (a g i)) =
    ∏ i : Fin J, G.mu g.val
      (a ((bigGroupSubtypeEquiv (G := G)).symm (bigGroupSubtypeEquiv (G := G) g)) i)
  apply Finset.prod_congr rfl
  intro i _
  have he : (bigGroupSubtypeEquiv (G := G)).symm
      (bigGroupSubtypeEquiv (G := G) g) = g := by
    apply Subtype.ext
    rfl
  cases he
  rfl

theorem fullRowWeight_sum (hV : ∀ g : G.Group, 0 < G.V g) (g : G.Group) :
    (∑ a : groupRows J g, fullRowWeight J g a) = 1 := by
  calc
    _ = ∏ i : Fin J, ∑ p : G.Prime g, G.mu g p := by
      unfold fullRowWeight
      exact (Fintype.prod_sum (fun _ : Fin J => fun p : G.Prime g => G.mu g p)).symm
    _ = 1 := by
      apply Finset.prod_eq_one
      intro i _
      exact Erdos821.P5Core.group_law_sum G g (ne_of_gt (hV g))

theorem freeDraw_pair_expect (hV : ∀ g : G.Group, 0 < G.V g)
    (H : Blueprint.Analytic.Tuple (Erdos821.P4Probe.analyticGroups G)
          (sideCounts ν block false) →
        Blueprint.Analytic.Tuple (Erdos821.P4Probe.analyticGroups G)
          (sideCounts ν block true) → ℂ) :
    (∑ u : Erdos821.P5Core.FreeDraw ν,
        (Erdos821.P5Core.freeDrawLaw ν u : ℂ) *
          H (sideTuple ν block false u) (sideTuple ν block true u)) =
      ∑ a : Blueprint.Analytic.Tuple (Erdos821.P4Probe.analyticGroups G)
          (sideCounts ν block false),
        ∑ b : Blueprint.Analytic.Tuple (Erdos821.P4Probe.analyticGroups G)
            (sideCounts ν block true),
          ((Blueprint.Analytic.tupleWeight (Erdos821.P4Probe.analyticGroups G)
              (sideCounts ν block false) a *
            Blueprint.Analytic.tupleWeight (Erdos821.P4Probe.analyticGroups G)
              (sideCounts ν block true) b : ℝ) : ℂ) * H a b := by
  let Hbig : G.BigAux J → ℂ := fun z =>
    H (Erdos821.P4Probe.selectedAuxTuple ν block false z)
      (Erdos821.P4Probe.selectedAuxTuple ν block true z)
  let Hpartial :
      Erdos821.P4Probe.PartialSample G.bigGroups (groupRows (G := G) J) → ℂ :=
    fun a => Hbig (partialBigAuxEquiv (G := G) (J := J) a)
  let Hfree : Erdos821.P5Core.FreeDraw ν → ℂ := fun u =>
    H (sideTuple ν block false u) (sideTuple ν block true u)
  let Hfull : G.Aux J → ℂ := fun u => Hfree (Erdos821.P5Core.freeRestriction ν u)
  have hfree := Erdos821.P5Core.sum_auxMass_free ν
    (fun g => (hV g).ne') Hfree
  have hrows (g : G.Group) :
      (∑ a : groupRows J g, fullRowWeight J g a) = 1 :=
    fullRowWeight_sum (G := G) (J := J) hV g
  have hpartial := Erdos821.P4Probe.partial_expectation_complex
    (fullRowWeight J) hrows G.bigGroups Hpartial
  have hpartialAux :
      (∑ u : G.Aux J, (ν.auxMass u : ℂ) * Hfull u) =
        ∑ a : Erdos821.P4Probe.PartialSample G.bigGroups (groupRows (G := G) J),
          (Erdos821.P4Probe.partialProductWeight
            (fullRowWeight J) G.bigGroups a : ℂ) *
            Hpartial a := by
    calc
      _ = ∑ u : G.Aux J,
          (Erdos821.P4Probe.productWeight (fullRowWeight J) u : ℂ) *
            Hpartial (fun g => u g.val) := by
        apply Finset.sum_congr rfl
        intro u _
        have hmass : ν.auxMass u =
            Erdos821.P4Probe.productWeight (fullRowWeight J) u := rfl
        have htest : Hfull u = Hpartial (fun g => u g.val) := by
          dsimp [Hfull, Hfree, Hpartial, Hbig]
          rw [partialBigAuxEquiv_auxRestriction]
          simp only [sideTuple_freeRestriction]
        rw [hmass, htest]
      _ = _ := by
        exact (sum_univ_fintype_irrel _ _
          (fun y : G.Aux J =>
            (Erdos821.P4Probe.productWeight (fullRowWeight J) y : ℂ) *
              Hpartial (fun g => y g.val))).trans
          (hpartial.trans (sum_univ_fintype_irrel _ _
            (fun a =>
              (Erdos821.P4Probe.partialProductWeight
                (fullRowWeight J) G.bigGroups a : ℂ) * Hpartial a)))
  have hbig :
      (∑ a : Erdos821.P4Probe.PartialSample G.bigGroups (groupRows (G := G) J),
          (Erdos821.P4Probe.partialProductWeight
            (fullRowWeight J) G.bigGroups a : ℂ) *
            Hpartial a) =
        ∑ z : G.BigAux J, (Blueprint.Graph.Pattern.bigAuxMass ν z : ℂ) * Hbig z := by
    apply Fintype.sum_equiv (partialBigAuxEquiv (G := G) (J := J))
    intro a
    rw [partialBigAuxEquiv_weight]
  calc
    _ = ∑ u : G.Aux J, (ν.auxMass u : ℂ) * Hfull u := hfree.symm
    _ = ∑ z : G.BigAux J, (Blueprint.Graph.Pattern.bigAuxMass ν z : ℂ) * Hbig z := by
      rw [hpartialAux, hbig]
    _ = _ := Erdos821.P4Probe.bigAux_selected_pair_expect ν block hV H

theorem sideCounts_bigSlots (side : Bool)
    (hne : ∃ g : G.BigGroup, block g = side ∧ (ν.changed g.val).Nonempty) :
    Blueprint.Analytic.bigSlots (Erdos821.P4Probe.analyticGroups G)
      (sideCounts ν block side) m := by
  rcases hne with ⟨g, hblock, hchanged⟩
  have hpos : 0 < sideCounts ν block side g.val := by
    simp [sideCounts, P4Probe.selectedCounts, sideCoordinates,
      P4Probe.patternAuxCoordinates, g.property, hblock,
      Finset.card_pos.mpr hchanged]
  refine ⟨?_, ?_⟩
  · exact lt_of_lt_of_le hpos
      (Finset.single_le_sum (fun g _ => Nat.zero_le _) (Finset.mem_univ _))
  · intro (g' : G.Group)
    constructor
    · by_cases hbig : G.big g' = true
      · unfold sideCounts P4Probe.selectedCounts sideCoordinates
        simp only [hbig, ↓reduceDIte]
        by_cases hb : block ⟨g', hbig⟩ = side
        · simp [P4Probe.patternAuxCoordinates, hb]
          exact ν.bound g'
        · simp [P4Probe.patternAuxCoordinates, hb]
      · simp [sideCounts, P4Probe.selectedCounts, hbig]
    · intro hs
      change g' ∈ G.smallGroups at hs
      have hiff : g' ∈ G.smallGroups ↔ G.big g' = false :=
        Finset.mem_filter.trans (by simp only [Finset.mem_univ, true_and])
      have hsmall : G.big g' = false := hiff.mp hs
      simp [sideCounts, P4Probe.selectedCounts, hsmall]

theorem analyticGroups_graph (G : Blueprint.Analytic.PrimeGroups) :
    Erdos821.P4Probe.analyticGroups G.graph = G := by
  cases G with
  | mk size primes small prime disjoint =>
    dsimp [Erdos821.P4Probe.analyticGroups, Blueprint.Analytic.PrimeGroups.graph]
    congr 1
    exact Blueprint.Analytic.graph_small ⟨size, primes, small, prime, disjoint⟩

end Erdos821.P5Madapt
