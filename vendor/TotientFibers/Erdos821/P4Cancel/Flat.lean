import Erdos821.P4Cancel.Symmetrize
import Erdos821.P4Probe.RowBridge
import Erdos821.P4Probe.ProbeContraction
import Erdos821.P4Probe.RawTailPairing
import Erdos821.P4Probe.PairingSums

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Cancel
open Blueprint.Graph P4Probe

noncomputable section

/-! Transport of big label tuples to the flat row world `Fin s × Fin M`
used by `SymmetricFullComponentTask` and `RowBridge`. -/

local instance (priority := high) rowSiteDecEq (s M : ℕ) : DecidableEq (RowSite s M) :=
  Classical.decEq _

variable (P : PrimeGroups) (M : ℕ)

abbrev rowCount : ℕ := Fintype.card P.BigGroup

def rowEquiv : Fin (rowCount P) ≃ P.BigGroup := (Fintype.equivFin P.BigGroup).symm
attribute [irreducible] rowEquiv

abbrev rowAlpha : Fin (rowCount P) → Type := fun g => P.Prime (rowEquiv P g).val

def rowW : ∀ g, rowAlpha P g → ℝ := fun g p => P.mu (rowEquiv P g).val p

abbrev FlatSample := ProductSample (FlatAlphabet (rowAlpha P) M)

abbrev flatW : ∀ z : RowSite (rowCount P) M, FlatAlphabet (rowAlpha P) M z → ℝ :=
  flatWeight (rowW P)

def toRows : P.BigLabels M ≃ ProbeSample (rowAlpha P) M :=
  (Equiv.piCongrLeft (fun h : P.BigGroup => Fin M → P.Prime h.val) (rowEquiv P)).symm

def toFlat : P.BigLabels M ≃ FlatSample P M := (toRows P M).trans flattenRows

variable {P M}

@[simp] lemma toRows_apply (a : P.BigLabels M) (g : Fin (rowCount P)) (i : Fin M) :
    toRows P M a g i = a (rowEquiv P g) i := by
  simp [toRows, Equiv.piCongrLeft_symm_apply]

@[simp] lemma toRows_symm_apply (x : ProbeSample (rowAlpha P) M) (g : Fin (rowCount P)) :
    (toRows P M).symm x (rowEquiv P g) = x g := by
  simp [toRows, Equiv.piCongrLeft_apply_apply]

@[simp] lemma toFlat_apply (a : P.BigLabels M) (z : RowSite (rowCount P) M) :
    toFlat P M a z = a (rowEquiv P z.1) z.2 := by
  simp [toFlat, flattenRows]

lemma rowW_nonneg (hV : ∀ g, 0 < P.V g) : ∀ g a, 0 ≤ rowW P g a :=
  fun g a => (graph_mu_pos P _ (hV _) a).le

lemma rowW_sum (hV : ∀ g, 0 < P.V g) : ∀ g, ∑ a, rowW P g a = 1 :=
  fun g => graph_mu_sum P _ (hV _)

lemma flatW_nonneg (hV : ∀ g, 0 < P.V g) : ∀ z a, 0 ≤ flatW P M z a :=
  fun z a => rowW_nonneg hV z.1 a

lemma flatW_sum (hV : ∀ g, 0 < P.V g) : ∀ z, ∑ a, flatW P M z a = 1 :=
  fun z => rowW_sum hV z.1

lemma rows_weight (a : P.BigLabels M) :
    sampleWeight (rowW P) (toRows P M a) = P.idealMass a := by
  unfold sampleWeight PrimeGroups.idealMass
  simp only [toRows_apply, rowW]
  exact Equiv.prod_comp (rowEquiv P) (fun g => ∏ i, P.mu g.val (a g i))

lemma flat_weight (a : P.BigLabels M) :
    productWeight (flatW P M) (toFlat P M a) = P.idealMass a := by
  rw [← rows_weight a, ← flatWeight_eq]
  rfl

/-- A test on big labels, viewed on the flat sample space. -/
def flatTest (F : P.BigLabels M → ℂ) : FlatSample P M → ℂ :=
  fun x => F ((toFlat P M).symm x)

@[simp] lemma flatTest_toFlat (F : P.BigLabels M → ℂ) (a : P.BigLabels M) :
    flatTest F (toFlat P M a) = F a := by
  simp [flatTest]

lemma flatTest_of (H : FlatSample P M → ℂ) :
    flatTest (fun a => H (toFlat P M a)) = H := by
  funext x
  simp [flatTest]

lemma flat_sqNorm (F : P.BigLabels M → ℂ) :
    productSqNorm (flatW P M) (flatTest F) = ∑ a, P.idealMass a * ‖F a‖ ^ 2 := by
  unfold productSqNorm
  symm
  exact Fintype.sum_equiv (toFlat P M) (fun a => P.idealMass a * ‖F a‖ ^ 2)
    (fun x => productWeight (flatW P M) x * ‖flatTest F x‖ ^ 2)
    (fun a => by rw [flat_weight, flatTest_toFlat])

lemma idealVectorNorm_flat (F : P.BigLabels M → ℂ) :
    idealVectorNorm P M F = Real.sqrt (productSqNorm (flatW P M) (flatTest F)) := by
  rw [flat_sqNorm]
  rfl

/-- Mix the coordinates of a flat site set. -/
def siteMix (T : Finset (RowSite (rowCount P) M)) (a b : P.BigLabels M) : P.BigLabels M :=
  fun h i => if ((rowEquiv P).symm h, i) ∈ T then b h i else a h i

lemma toFlat_mix (T : Finset (RowSite (rowCount P) M)) (a b : P.BigLabels M) :
    mixCoords T (toFlat P M a) (toFlat P M b) = toFlat P M (siteMix T a b) := by
  funext z
  by_cases hz : z ∈ T
  · have hz' : ((rowEquiv P).symm (rowEquiv P z.1), z.2) ∈ T := by simpa using hz
    simp [mixCoords, siteMix, hz, hz']
  · have hz' : ((rowEquiv P).symm (rowEquiv P z.1), z.2) ∉ T := by simpa using hz
    simp [mixCoords, siteMix, hz, hz']

/-- Average over a flat site set, on big labels. -/
def siteAvg (T : Finset (RowSite (rowCount P) M)) (F : P.BigLabels M → ℂ)
    (a : P.BigLabels M) : ℂ :=
  ∑ b, (P.idealMass b : ℂ) * F (siteMix T a b)

lemma flat_average (T : Finset (RowSite (rowCount P) M)) (F : P.BigLabels M → ℂ)
    (a : P.BigLabels M) :
    productAverage (flatW P M) T (flatTest F) (toFlat P M a) = siteAvg T F a := by
  unfold productAverage siteAvg
  symm
  apply Fintype.sum_equiv (toFlat P M)
  intro b
  rw [flat_weight, toFlat_mix, flatTest_toFlat]

/-- Flat site set of a big-coordinate selection. -/
def siteSet (S : P.BigGroup → Finset (Fin M)) : Finset (RowSite (rowCount P) M) :=
  Finset.univ.filter (fun z => z.2 ∈ S (rowEquiv P z.1))

lemma siteAvg_siteSet (S : P.BigGroup → Finset (Fin M)) (F : P.BigLabels M → ℂ) :
    siteAvg (siteSet S) F = bigCoordinateAverage P M S F := by
  funext a
  unfold siteAvg bigCoordinateAverage
  apply Finset.sum_congr rfl
  intro b _
  congr 2
  funext h i
  simp [siteMix, siteSet]

lemma siteAvg_empty (hV : ∀ g, 0 < P.V g) (F : P.BigLabels M → ℂ) (a : P.BigLabels M) :
    siteAvg ∅ F a = F a := by
  unfold siteAvg
  have hm : ∀ b, siteMix (∅ : Finset (RowSite (rowCount P) M)) a b = a := by
    intro b; funext h i; simp [siteMix]
  simp only [hm]
  rw [← Finset.sum_mul]
  have ht : (∑ y : P.BigLabels M, (P.idealMass y : ℂ)) = 1 := by
    exact_mod_cast idealMass_sum P M hV
  rw [ht, one_mul]

/-- Row symmetry of a big test transports to the flat row world. -/
lemma rows_symmetric (F : P.BigLabels M → ℂ)
    (hF : ∀ (π : P.BigPermutations M) a, F (P.actBig π a) = F a)
    (π : Fin (rowCount P) → Equiv.Perm (Fin M)) (x : ProbeSample (rowAlpha P) M) :
    F ((toRows P M).symm (fun g i => x g (π g i))) = F ((toRows P M).symm x) := by
  have h : (toRows P M).symm (fun g i => x g (π g i)) =
      P.actBig (fun h => π ((rowEquiv P).symm h)) ((toRows P M).symm x) := by
    apply (toRows P M).injective
    rw [Equiv.apply_symm_apply]
    funext g i
    simp [PrimeGroups.actBig]
  rw [h, hF]

/-! The two side sets and the tail set, in the exact form of
`SymmetricFullComponentTask`. -/

def blockSet (block : P.BigGroup → Bool) (side : Bool) : Finset (Fin (rowCount P)) :=
  Finset.univ.filter (fun g => block (rowEquiv P g) = side)

def sideSites (m : ℕ) (block : P.BigGroup → Bool) (side : Bool) :
    Finset (RowSite (rowCount P) M) :=
  Finset.univ.filter (fun z : RowSite (rowCount P) M => z.1 ∈ blockSet block side ∧ z.2.val < m)

def tailSites (J ell : ℕ) : Finset (RowSite (rowCount P) (J + ell)) :=
  Finset.univ.filter (fun z : RowSite (rowCount P) (J + ell) => J ≤ z.2.val)

lemma blockSet_card (block : P.BigGroup → Bool) (side : Bool) :
    (blockSet (P := P) block side).card =
      (Finset.univ.filter (fun g : P.BigGroup => block g = side)).card := by
  unfold blockSet
  apply Finset.card_bij (fun g _ => rowEquiv P g)
  · intro g hg; simpa using hg
  · intro g _ h _ hgh; exact (rowEquiv P).injective hgh
  · intro g hg
    exact ⟨(rowEquiv P).symm g, by simpa using hg, by simp⟩

lemma siteSet_tail (J ell : ℕ) :
    siteSet (P := P) (tailCoordinates P J ell) = tailSites J ell := by
  ext z
  simp [siteSet, tailSites, tailCoordinates]

/-- Alternating full component on one side, as a big-label test. -/
def sideFull (I : Finset (RowSite (rowCount P) M)) (F : P.BigLabels M → ℂ)
    (a : P.BigLabels M) : ℂ :=
  productFull (flatW P M) I (flatTest F) (toFlat P M a)

lemma flatTest_sideFull (I : Finset (RowSite (rowCount P) M)) (F : P.BigLabels M → ℂ) :
    flatTest (sideFull I F) = productFull (flatW P M) I (flatTest F) := by
  unfold sideFull
  exact flatTest_of _

lemma sub_sideFull (hV : ∀ g, 0 < P.V g) (I : Finset (RowSite (rowCount P) M))
    (F : P.BigLabels M → ℂ) (a : P.BigLabels M) :
    F a - sideFull I F a =
      ∑ U ∈ I.powerset.erase ∅, (-((-1 : ℂ) ^ U.card)) * siteAvg U F a := by
  unfold sideFull productFull
  simp_rw [flat_average]
  rw [← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset I)]
  simp only [Finset.card_empty, pow_zero, one_mul, siteAvg_empty hV]
  rw [sub_add_cancel_left, ← Finset.sum_neg_distrib]
  simp only [neg_mul]

lemma sub_sideFull_norm_le (hV : ∀ g, 0 < P.V g) (I : Finset (RowSite (rowCount P) M))
    (F : P.BigLabels M → ℂ) :
    idealVectorNorm P M (fun a => F a - sideFull I F a) ≤ idealVectorNorm P M F := by
  rw [idealVectorNorm_flat, idealVectorNorm_flat]
  apply Real.sqrt_le_sqrt
  have h : flatTest (fun a => F a - sideFull I F a) =
      fun x => flatTest F x - productFull (flatW P M) I (flatTest F) x := by
    rw [← flatTest_sideFull]
    rfl
  rw [h]
  exact productFull_complement_sqNorm_le (flatW P M) (flatW_nonneg hV) (flatW_sum hV) I _

lemma tail_sideFull (hV : ∀ g, 0 < P.V g) (J ell : ℕ)
    (I : Finset (RowSite (rowCount P) (J + ell))) (F : P.BigLabels (J + ell) → ℂ) :
    bigCoordinateAverage P (J + ell) (tailCoordinates P J ell) (sideFull I F) =
      fun a => productProbeProjection (flatW P (J + ell)) (tailSites J ell) I
        (flatTest F) (toFlat P (J + ell) a) := by
  funext a
  rw [← siteAvg_siteSet, siteSet_tail, ← flat_average, flatTest_sideFull]
  unfold productProbeProjection
  rw [productFull_average_commute (flatW P (J + ell)) (flatW_sum hV)]

end
end Erdos821.P4Cancel
