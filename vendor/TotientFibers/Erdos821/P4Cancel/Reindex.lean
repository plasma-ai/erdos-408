import Erdos821.P4Cancel.Flat

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Cancel
open Blueprint.Graph P4Probe

noncomputable section

local instance (priority := high) rowSiteDecEq' (s M : ℕ) : DecidableEq (RowSite s M) :=
  Classical.decEq _

variable {P : PrimeGroups} {J ell m : ℕ}

/-- Flat sites of one side of a probe choice. -/
def siteOf (hj : m ≤ J) (block : P.BigGroup → Bool) (c : P.BigGroup → Finset (Fin m))
    (side : Bool) : Finset (RowSite (rowCount P) (J + ell)) :=
  Finset.univ.filter (fun z : RowSite (rowCount P) (J + ell) =>
    block (rowEquiv P z.1) = side ∧
      z.2 ∈ (c (rowEquiv P z.1)).map (Fin.castLEEmb (hj.trans (Nat.le_add_right J ell))))

lemma mem_siteSet {M : ℕ} (S : P.BigGroup → Finset (Fin M)) (z : RowSite (rowCount P) M) :
    z ∈ siteSet (P := P) S ↔ z.2 ∈ S (rowEquiv P z.1) := by
  unfold siteSet
  rw [Finset.mem_filter]
  simp

lemma siteSet_patternSide (hj : m ≤ J) (block : P.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ)
    (c : ProbeChoice P m block) (side : Bool) :
    siteSet (P := P) (M := J + ell)
      (patternSideCoordinates (signedPattern hj block Q h ξ c : Pattern P J ell m) block side) =
      siteOf hj block c.val side := by
  ext z
  rw [mem_siteSet]
  simp only [siteOf, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold patternSideCoordinates
  by_cases hb : block (rowEquiv P z.1) = side
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
    simp only [hb, true_and]
    show z.2 ∈ (liftChoice hj c.val (rowEquiv P z.1).val).image _ ↔ _
    rw [liftChoice_big]
    simp only [Finset.mem_image, Finset.mem_map]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, hy⟩
      exact ⟨x, hx, by rw [← hy]; rfl⟩
    · rintro ⟨x, hx, hxz⟩
      exact ⟨_, ⟨x, hx, rfl⟩, by rw [← hxz]; rfl⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]
    simp [hb]

lemma card_filter_rows {s M : ℕ} (p : Fin s → Prop) (S : Fin s → Finset (Fin M))
    (q : RowSite s M → Prop) [DecidablePred q] (hq : ∀ z, q z ↔ p z.1 ∧ z.2 ∈ S z.1) :
    (Finset.univ.filter q).card = ∑ g, if p g then (S g).card else 0 := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hp : p g
  · simp only [hq, hp, true_and, ite_true]
    rw [← Finset.card_filter, Finset.filter_univ_mem]
  · simp [hq, hp]

lemma sign_card (hj : m ≤ J) (block : P.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ)
    (c : ProbeChoice P m block) :
    (∑ j, ((signedPattern hj block Q h ξ c : Pattern P J ell m).changed j).card) =
      (siteOf (ell := ell) hj block c.val false).card +
        (siteOf (ell := ell) hj block c.val true).card := by
  change (∑ j : P.Group, (liftChoice hj c.val j).card) = _
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j => P.big j = true)]
  have h0 : (∑ j : {j : P.Group // ¬ P.big j = true}, (liftChoice hj c.val j.val).card) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [liftChoice_small hj c.val j.val (by simpa using j.property)]
    rfl
  rw [h0, add_zero]
  have h1 : (∑ g : P.BigGroup, (liftChoice hj c.val g.val).card) =
      ∑ g : P.BigGroup, (c.val g).card := by
    apply Finset.sum_congr rfl
    intro g _
    rw [liftChoice_big, Finset.card_image_of_injective _ (Fin.castLE_injective hj)]
  refine h1.trans ?_
  unfold siteOf
  rw [card_filter_rows (fun g => block (rowEquiv P g) = false)
      (fun g => (c.val (rowEquiv P g)).map (Fin.castLEEmb (hj.trans (Nat.le_add_right J ell))))
      _ (fun z => Iff.rfl),
    card_filter_rows (fun g => block (rowEquiv P g) = true)
      (fun g => (c.val (rowEquiv P g)).map (Fin.castLEEmb (hj.trans (Nat.le_add_right J ell))))
      _ (fun z => Iff.rfl), ← Finset.sum_add_distrib]
  rw [← Equiv.sum_comp (rowEquiv P)]
  apply Finset.sum_congr rfl
  intro g _
  cases hb : block (rowEquiv P g) <;> simp

/-- Inverse of the site map: rebuild a choice from two site sets. -/
def choiceOf (hj : m ≤ J) (p : Finset (RowSite (rowCount P) (J + ell)) ×
    Finset (RowSite (rowCount P) (J + ell))) : P.BigGroup → Finset (Fin m) :=
  fun g => Finset.univ.filter (fun k : Fin m =>
    ((rowEquiv P).symm g, Fin.castLE (hj.trans (Nat.le_add_right J ell)) k) ∈ p.1 ∪ p.2)

lemma mem_siteOf (hj : m ≤ J) (block : P.BigGroup → Bool) (c : P.BigGroup → Finset (Fin m))
    (side : Bool) (z : RowSite (rowCount P) (J + ell)) :
    z ∈ siteOf hj block c side ↔ block (rowEquiv P z.1) = side ∧
      z.2 ∈ (c (rowEquiv P z.1)).map (Fin.castLEEmb (hj.trans (Nat.le_add_right J ell))) := by
  unfold siteOf
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

lemma mem_choiceOf (hj : m ≤ J) (p : Finset (RowSite (rowCount P) (J + ell)) ×
    Finset (RowSite (rowCount P) (J + ell))) (g : P.BigGroup) (k : Fin m) :
    k ∈ choiceOf hj p g ↔
      ((rowEquiv P).symm g, Fin.castLE (hj.trans (Nat.le_add_right J ell)) k) ∈ p.1 ∪ p.2 := by
  unfold choiceOf
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

lemma mem_sideSites {M : ℕ} (block : P.BigGroup → Bool) (side : Bool)
    (z : RowSite (rowCount P) M) :
    z ∈ sideSites (P := P) (M := M) m block side ↔
      block (rowEquiv P z.1) = side ∧ z.2.val < m := by
  unfold sideSites blockSet
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

lemma choice_sum (hj : m ≤ J) (block : P.BigGroup → Bool)
    (ψ : Finset (RowSite (rowCount P) (J + ell)) → Finset (RowSite (rowCount P) (J + ell)) → ℂ) :
    (∑ c : ProbeChoice P m block,
      ψ (siteOf hj block c.val false) (siteOf hj block c.val true)) =
      ∑ U ∈ (sideSites (P := P) (M := J + ell) m block false).powerset.erase ∅,
        ∑ V ∈ (sideSites (P := P) (M := J + ell) m block true).powerset.erase ∅, ψ U V := by
  have hmM : m ≤ J + ell := hj.trans (Nat.le_add_right J ell)
  rw [← Finset.sum_product']
  -- membership of the site sets
  have hsub : ∀ (c : ProbeChoice P m block) (side : Bool),
      siteOf (ell := ell) hj block c.val side ⊆ sideSites (P := P) (M := J + ell) m block side := by
    intro c side z hz
    rw [mem_siteOf, Finset.mem_map] at hz
    rw [mem_sideSites]
    obtain ⟨hb, x, _, hx⟩ := hz
    refine ⟨hb, ?_⟩
    rw [← hx]
    exact x.isLt
  have hne : ∀ (c : ProbeChoice P m block) (side : Bool),
      siteOf (ell := ell) hj block c.val side ≠ ∅ := by
    intro c side
    obtain ⟨g, hg, k, hk⟩ := c.property side
    apply Finset.nonempty_iff_ne_empty.mp
    refine ⟨((rowEquiv P).symm g, Fin.castLE hmM k), ?_⟩
    rw [mem_siteOf]
    simp only [Equiv.apply_symm_apply]
    exact ⟨hg, Finset.mem_map_of_mem _ hk⟩
  -- the inverse is a probe choice
  have hchoice : ∀ p ∈ ((sideSites (P := P) (M := J + ell) m block false).powerset.erase ∅) ×ˢ
      ((sideSites (P := P) (M := J + ell) m block true).powerset.erase ∅),
      ∀ side : Bool, ∃ g : P.BigGroup, block g = side ∧ (choiceOf hj p g).Nonempty := by
    intro p hp side
    simp only [Finset.mem_product, Finset.mem_erase, Finset.mem_powerset] at hp
    obtain ⟨⟨hU0, hU⟩, ⟨hV0, hV⟩⟩ := hp
    have key : ∀ (W : Finset (RowSite (rowCount P) (J + ell))), W ≠ ∅ →
        W ⊆ sideSites m block side → W ⊆ p.1 ∪ p.2 →
        ∃ g : P.BigGroup, block g = side ∧ (choiceOf hj p g).Nonempty := by
      intro W hW0 hW hWp
      obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hW0
      have hz' := (mem_sideSites block side z).mp (hW hz)
      refine ⟨rowEquiv P z.1, hz'.1, ⟨⟨z.2.val, hz'.2⟩, ?_⟩⟩
      rw [mem_choiceOf, Equiv.symm_apply_apply]
      have : (z.1, Fin.castLE hmM ⟨z.2.val, hz'.2⟩) = z := Prod.ext rfl (Fin.ext rfl)
      rw [this]
      exact hWp hz
    cases side
    · exact key p.1 hU0 hU Finset.subset_union_left
    · exact key p.2 hV0 hV Finset.subset_union_right
  refine Finset.sum_bij'
    (fun c _ => (siteOf hj block c.val false, siteOf hj block c.val true))
    (fun p hp => ⟨choiceOf hj p, hchoice p hp⟩) ?_ ?_ ?_ ?_ ?_
  · intro c _
    simp only [Finset.mem_product, Finset.mem_erase, Finset.mem_powerset]
    exact ⟨⟨hne c false, hsub c false⟩, ⟨hne c true, hsub c true⟩⟩
  · intro p _
    exact Finset.mem_univ _
  · intro c _
    apply Subtype.ext
    funext g
    ext k
    change k ∈ choiceOf hj (siteOf hj block c.val false, siteOf hj block c.val true) g ↔ k ∈ c.val g
    rw [mem_choiceOf, Finset.mem_union, mem_siteOf, mem_siteOf]
    simp only [Equiv.apply_symm_apply]
    have hk : Fin.castLE hmM k ∈ (c.val g).map (Fin.castLEEmb hmM) ↔ k ∈ c.val g := by
      rw [← Fin.castLEEmb_apply hmM k, Finset.mem_map']
    rw [hk]
    cases block g <;> simp
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_erase, Finset.mem_powerset] at hp
    obtain ⟨⟨_, hU⟩, ⟨_, hV⟩⟩ := hp
    have hside : ∀ (side : Bool) (W W' : Finset (RowSite (rowCount P) (J + ell))),
        W ⊆ sideSites m block side → W' ⊆ sideSites m block (!side) →
        ∀ z, (block (rowEquiv P z.1) = side ∧
          ∃ k : Fin m, ((rowEquiv P).symm (rowEquiv P z.1), Fin.castLE hmM k) ∈ W ∪ W' ∧
            Fin.castLE hmM k = z.2) ↔ z ∈ W := by
      intro side W W' hW hW' z
      simp only [Equiv.symm_apply_apply]
      constructor
      · rintro ⟨hb, k, hk, hkz⟩
        have hz : (z.1, Fin.castLE hmM k) = z := Prod.ext rfl hkz
        rw [hz] at hk
        rcases Finset.mem_union.mp hk with hk | hk
        · exact hk
        · have := (mem_sideSites block (!side) z).mp (hW' hk)
          rw [hb] at this
          cases side <;> simp at this
      · intro hz
        have hz' := (mem_sideSites block side z).mp (hW hz)
        refine ⟨hz'.1, ⟨z.2.val, hz'.2⟩, ?_, Fin.ext rfl⟩
        have : (z.1, Fin.castLE hmM ⟨z.2.val, hz'.2⟩) = z := Prod.ext rfl (Fin.ext rfl)
        rw [this]
        exact Finset.mem_union_left _ hz
    have hmem : ∀ side z, z ∈ siteOf (ell := ell) hj block (choiceOf hj p) side ↔
        (block (rowEquiv P z.1) = side ∧
          ∃ k : Fin m, ((rowEquiv P).symm (rowEquiv P z.1), Fin.castLE hmM k) ∈ p.1 ∪ p.2 ∧
            Fin.castLE hmM k = z.2) := by
      intro side z
      rw [mem_siteOf, Finset.mem_map]
      simp only [mem_choiceOf, Fin.castLEEmb_apply]
    apply Prod.ext
    · ext z
      change z ∈ siteOf (ell := ell) hj block (choiceOf hj p) false ↔ z ∈ p.1
      rw [hmem]
      exact hside false p.1 p.2 hU hV z
    · ext z
      change z ∈ siteOf (ell := ell) hj block (choiceOf hj p) true ↔ z ∈ p.2
      rw [hmem, Finset.union_comm]
      exact hside true p.2 p.1 hV hU z
  · intro c _
    rfl

/-- The signed all-choice correction is the pairing of the two side complements. -/
lemma correction_sum_eq (hV : ∀ g, 0 < P.V g) (hj : m ≤ J) (block : P.BigGroup → Bool)
    (Q : ℕ) (h ξ : ℝ) (K : P.BigLabels (J + ell) → P.BigLabels (J + ell) → ℂ)
    (F G : P.BigLabels (J + ell) → ℂ) :
    (∑ c : ProbeChoice P m block,
      (-1 : ℂ) ^ (∑ j, ((signedPattern hj block Q h ξ c : Pattern P J ell m).changed j).card) *
        idealFullPair K
          (bigCoordinateAverage P (J + ell)
            (patternSideCoordinates (signedPattern hj block Q h ξ c : Pattern P J ell m)
              block false) F)
          (bigCoordinateAverage P (J + ell)
            (patternSideCoordinates (signedPattern hj block Q h ξ c : Pattern P J ell m)
              block true) G)) =
      idealFullPair K
        (fun a => F a - sideFull (sideSites (P := P) (M := J + ell) m block false) F a)
        (fun b => G b - sideFull (sideSites (P := P) (M := J + ell) m block true) G b) := by
  have hl : ∀ c : ProbeChoice P m block,
      (-1 : ℂ) ^ (∑ j, ((signedPattern hj block Q h ξ c : Pattern P J ell m).changed j).card) *
        idealFullPair K
          (bigCoordinateAverage P (J + ell)
            (patternSideCoordinates (signedPattern hj block Q h ξ c : Pattern P J ell m)
              block false) F)
          (bigCoordinateAverage P (J + ell)
            (patternSideCoordinates (signedPattern hj block Q h ξ c : Pattern P J ell m)
              block true) G) =
      (fun U V => (-1 : ℂ) ^ (U.card + V.card) * idealFullPair K (siteAvg U F) (siteAvg V G))
        (siteOf hj block c.val false) (siteOf hj block c.val true) := by
    intro c
    rw [sign_card, ← siteAvg_siteSet, ← siteAvg_siteSet, siteSet_patternSide,
      siteSet_patternSide]
  rw [Finset.sum_congr rfl (fun c _ => hl c)]
  refine (choice_sum hj block (fun U V =>
    (-1 : ℂ) ^ (U.card + V.card) * idealFullPair K (siteAvg U F) (siteAvg V G))).trans ?_
  have hF : (fun a => F a - sideFull (sideSites (P := P) (M := J + ell) m block false) F a) =
      fun a => ∑ U ∈ (sideSites (P := P) (M := J + ell) m block false).powerset.erase ∅,
        (-((-1 : ℂ) ^ U.card)) * siteAvg U F a := by
    funext a; exact sub_sideFull hV _ F a
  have hG : (fun b => G b - sideFull (sideSites (P := P) (M := J + ell) m block true) G b) =
      fun b => ∑ V ∈ (sideSites (P := P) (M := J + ell) m block true).powerset.erase ∅,
        (-((-1 : ℂ) ^ V.card)) * siteAvg V G b := by
    funext b; exact sub_sideFull hV _ G b
  rw [hF, hG, idealFullPair_sum_both]
  apply Finset.sum_congr rfl
  intro U _
  apply Finset.sum_congr rfl
  intro V _
  simp only [star_neg, star_pow, star_one, pow_add]
  ring

end
end Erdos821.P4Cancel
