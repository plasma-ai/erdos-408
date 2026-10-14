import Erdos821.Blueprint.Ideal

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

variable {P : PrimeGroups} {J ell m : ℕ}

lemma selectedProduct_aux_ext (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (u v : P.BigAux J)
    (huv : ∀ g i, i ∈ ν.changed g.val → u g i = v g i) :
    selectedProduct ν block side u = selectedProduct ν block side v := by
  unfold selectedProduct
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  split_ifs with h
  · rw [huv g i h.2]
  · rfl

def ProbeChoice (P : PrimeGroups) (m : ℕ) (block : P.BigGroup → Bool) :=
  {c : P.BigGroup → Finset (Fin m) //
    ∀ side : Bool, ∃ g : P.BigGroup, block g = side ∧ (c g).Nonempty}

instance (P : PrimeGroups) (m : ℕ) (block : P.BigGroup → Bool) :
    Fintype (ProbeChoice P m block) :=
  inferInstanceAs (Fintype {c : P.BigGroup → Finset (Fin m) //
    ∀ side : Bool, ∃ g : P.BigGroup, block g = side ∧ (c g).Nonempty})

instance (P : PrimeGroups) (m : ℕ) (block : P.BigGroup → Bool) :
    DecidableEq (ProbeChoice P m block) := Classical.decEq _

def liftChoice (hj : m ≤ J) (c : P.BigGroup → Finset (Fin m))
    (g : P.Group) : Finset (Fin J) :=
  if hg : P.big g = true then (c ⟨g, hg⟩).image (Fin.castLE hj) else ∅

@[simp] lemma liftChoice_big (hj : m ≤ J) (c : P.BigGroup → Finset (Fin m))
    (g : P.BigGroup) :
    liftChoice hj c g.val = (c g).image (Fin.castLE hj) := by
  simp [liftChoice, g.property]

lemma liftChoice_small (hj : m ≤ J) (c : P.BigGroup → Finset (Fin m))
    (g : P.Group) (hg : P.big g = false) : liftChoice hj c g = ∅ := by
  simp [liftChoice, hg]

lemma liftChoice_bound (hj : m ≤ J) (c : P.BigGroup → Finset (Fin m))
    (g : P.Group) : (liftChoice hj c g).card ≤ m := by
  unfold liftChoice
  split_ifs
  · exact Finset.card_image_le.trans (by simpa using Finset.card_le_univ (c ⟨g, by assumption⟩))
  · simp

lemma liftChoice_probe (hj : m ≤ J) (c : P.BigGroup → Finset (Fin m))
    (g : P.Group) (i : Fin J) (hi : i ∈ liftChoice hj c g) : i.val < m := by
  unfold liftChoice at hi
  split_ifs at hi with hg
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact j.isLt
  · simp at hi

def rawPattern (P : PrimeGroups) (J ell m : ℕ) : Pattern P J ell m where
  changed := fun _ => ∅
  small := by intros; rfl
  bound := by intros; simp
  coefficient := fun _ _ _ => 1
  coefficient_aux_ext := by intros; rfl

def choiceBase (hj : m ≤ J) (c : P.BigGroup → Finset (Fin m)) :
    Pattern P J ell m where
  changed := liftChoice hj c
  small := liftChoice_small hj c
  bound := liftChoice_bound hj c
  coefficient := fun _ _ _ => 0
  coefficient_aux_ext := by intros; rfl

def signedPattern (hj : m ≤ J) (block : P.BigGroup → Bool)
    (Q : ℕ) (h ξ : ℝ) (c : ProbeChoice P m block) : Pattern P J ell m :=
  let ν : Pattern P J ell m := choiceBase hj c.val
  { ν with
    coefficient := fun a b u =>
      -((-1 : ℂ) ^ (∑ g, (ν.changed g).card)) *
      selectedKernel ν block false Q h ξ (selectedProduct ν block false u)
        (selectedEndpoint ν block false b) *
      selectedKernel ν block true Q h ξ (selectedProduct ν block true u)
        (selectedEndpoint ν block true a)
    coefficient_aux_ext := by
      intro a b u v huv
      rw [selectedProduct_aux_ext ν block false u v huv,
        selectedProduct_aux_ext ν block true u v huv] }

def probeFamily (F : FixedData) (P : PrimeGroups) (J m : ℕ) (hj : m ≤ J)
    (block : P.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ) : Family F P J m where
  count := Fintype.card (Option (ProbeChoice P m block))
  pattern := fun v =>
    match (Fintype.equivFin (Option (ProbeChoice P m block))).symm v with
    | none => rawPattern P J F.ell m
    | some c => signedPattern hj block Q h ξ c

theorem probeFamily_residual (F : FixedData) (P : PrimeGroups) (J m : ℕ)
    (hj : m ≤ J) (block : P.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ) :
    (probeFamily F P J m hj block Q h ξ).Residual Q h ξ := by
  let e := Fintype.equivFin (Option (ProbeChoice P m block))
  refine ⟨e none, block, ?_, ?_, ?_⟩
  · intro g
    simp [probeFamily, e, rawPattern]
  · intro a b u
    simp [probeFamily, e, rawPattern]
  · intro v hv
    have hn : e.symm v ≠ none := by
      intro he
      apply hv
      apply e.symm.injective
      simpa using he
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hn
    have hp : (probeFamily F P J m hj block Q h ξ).pattern v =
        signedPattern hj block Q h ξ c := by
      change (match e.symm v with
        | none => rawPattern P J F.ell m
        | some c => signedPattern hj block Q h ξ c) = _
      rw [hc]
    rw [hp]
    refine ⟨?_, ?_, ?_⟩
    · intro g i hi
      exact liftChoice_probe hj c.val g i hi
    · intro side
      obtain ⟨g, hg, hc⟩ := c.property side
      refine ⟨g, hg, ?_⟩
      simpa [signedPattern, choiceBase] using hc.image (Fin.castLE hj)
    · intro a b u
      rfl

end
end Erdos821.P4Probe
