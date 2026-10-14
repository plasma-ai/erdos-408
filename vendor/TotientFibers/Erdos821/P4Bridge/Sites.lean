import Erdos821.P4Probe.SelectedTuples

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos821.P4Bridge
open Blueprint.Graph P4Probe
noncomputable section
variable {P : PrimeGroups} {J ell m : ℕ}

-- Slot counts for the two sides (generic ell).
def kFalse (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (g : Fin P.count) : ℕ :=
  if h : P.big g = true then
    if block ⟨g, h⟩ = false then (ν.changed g).card else 0
  else 0

def kTrue (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (g : Fin P.count) : ℕ :=
  if h : P.big g = true then
    if block ⟨g, h⟩ = true then (ν.changed g).card else 0
  else 0

lemma kFalse_le (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (g : Fin P.count) : kFalse ν block g ≤ m := by
  unfold kFalse
  split_ifs with h1 h2
  · exact (ν.bound g).trans (by omega)
  · omega
  · omega

lemma kTrue_le (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (g : Fin P.count) : kTrue ν block g ≤ m := by
  unfold kTrue
  split_ifs with h1 h2
  · exact (ν.bound g).trans (by omega)
  · omega
  · omega

lemma kFalse_small (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (g : Fin P.count) (hs : g ∈ (P4Probe.analyticGroups P).small) :
    kFalse ν block g = 0 := by
  have hb : P.big g = false := by
    have hmem : g ∈ P.smallGroups := hs
    simpa [PrimeGroups.smallGroups] using hmem
  unfold kFalse
  simp [hb]

lemma kTrue_small (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (g : Fin P.count) (hs : g ∈ (P4Probe.analyticGroups P).small) :
    kTrue ν block g = 0 := by
  have hb : P.big g = false := by
    have hmem : g ∈ P.smallGroups := hs
    simpa [PrimeGroups.smallGroups] using hmem
  unfold kTrue
  simp [hb]

-- Nonempty changed for ProbeChoice witnesses (generic ell).
lemma choiceBase_changed_nonempty (hj : m ≤ J)
    (c : P.BigGroup → Finset (Fin m)) (g : P.BigGroup)
    (hne : (c g).Nonempty) :
    (((choiceBase hj c : Pattern P J ell m).changed g.val).Nonempty) := by
  have himg : ((c g).image (Fin.castLE hj)).Nonempty :=
    hne.image _
  have heq : (choiceBase hj c : Pattern P J ell m).changed g.val =
      (c g).image (Fin.castLE hj) := by
    simp [choiceBase, liftChoice, g.property]
  rw [heq]
  exact himg

lemma kFalse_pos (hj : m ≤ J) (block : P.BigGroup → Bool)
    (c : ProbeChoice P m block) (g : P.BigGroup)
    (hg : block g = false) (hne : (c.val g).Nonempty) :
    0 < kFalse (choiceBase hj c.val : Pattern P J ell m) block g.val := by
  have hb : P.big g.val = true := g.property
  have hg' : block ⟨g.val, hb⟩ = false := hg
  have hne' : ((choiceBase hj c.val : Pattern P J ell m).changed g.val).Nonempty :=
    choiceBase_changed_nonempty hj c.val g hne
  have hcard : 0 < (((choiceBase hj c.val : Pattern P J ell m).changed g.val).card) :=
    Finset.card_pos.mpr hne'
  have hkeq : kFalse (choiceBase hj c.val : Pattern P J ell m) block g.val =
      (((choiceBase hj c.val : Pattern P J ell m).changed g.val).card) := by
    unfold kFalse
    simp [hb, hg']
  rw [hkeq]
  exact hcard

lemma kTrue_pos (hj : m ≤ J) (block : P.BigGroup → Bool)
    (c : ProbeChoice P m block) (g : P.BigGroup)
    (hg : block g = true) (hne : (c.val g).Nonempty) :
    0 < kTrue (choiceBase hj c.val : Pattern P J ell m) block g.val := by
  have hb : P.big g.val = true := g.property
  have hg' : block ⟨g.val, hb⟩ = true := hg
  have hne' : ((choiceBase hj c.val : Pattern P J ell m).changed g.val).Nonempty :=
    choiceBase_changed_nonempty hj c.val g hne
  have hcard : 0 < (((choiceBase hj c.val : Pattern P J ell m).changed g.val).card) :=
    Finset.card_pos.mpr hne'
  have hkeq : kTrue (choiceBase hj c.val : Pattern P J ell m) block g.val =
      (((choiceBase hj c.val : Pattern P J ell m).changed g.val).card) := by
    unfold kTrue
    simp [hb, hg']
  rw [hkeq]
  exact hcard

lemma kFalse_bigSlots (hj : m ≤ J) (block : P.BigGroup → Bool)
    (c : ProbeChoice P m block) (g : P.BigGroup)
    (hg : block g = false) (hne : (c.val g).Nonempty) :
    Blueprint.Analytic.bigSlots (P4Probe.analyticGroups P)
      (kFalse (choiceBase hj c.val : Pattern P J ell m) block) m := by
  refine ⟨?_, fun g => ⟨kFalse_le _ _ g, fun hs => kFalse_small _ _ g hs⟩⟩
  have hpos : 0 < kFalse (choiceBase hj c.val : Pattern P J ell m) block g.val :=
    kFalse_pos hj block c g hg hne
  have hle : kFalse (choiceBase hj c.val : Pattern P J ell m) block g.val ≤
      ∑ g, kFalse (choiceBase hj c.val : Pattern P J ell m) block g := by
    apply Finset.single_le_sum (fun i _ => Nat.zero_le _)
    exact Finset.mem_univ _
  exact lt_of_lt_of_le hpos hle

lemma kTrue_bigSlots (hj : m ≤ J) (block : P.BigGroup → Bool)
    (c : ProbeChoice P m block) (g : P.BigGroup)
    (hg : block g = true) (hne : (c.val g).Nonempty) :
    Blueprint.Analytic.bigSlots (P4Probe.analyticGroups P)
      (kTrue (choiceBase hj c.val : Pattern P J ell m) block) m := by
  refine ⟨?_, fun g => ⟨kTrue_le _ _ g, fun hs => kTrue_small _ _ g hs⟩⟩
  have hpos : 0 < kTrue (choiceBase hj c.val : Pattern P J ell m) block g.val :=
    kTrue_pos hj block c g hg hne
  have hle : kTrue (choiceBase hj c.val : Pattern P J ell m) block g.val ≤
      ∑ g, kTrue (choiceBase hj c.val : Pattern P J ell m) block g := by
    apply Finset.single_le_sum (fun i _ => Nat.zero_le _)
    exact Finset.mem_univ _
  exact lt_of_lt_of_le hpos hle

lemma sideCounts_false_eq (ν : Pattern P J ell m) (block : P.BigGroup → Bool) :
    selectedCounts (patternAuxCoordinates ν block false) = kFalse ν block := by
  funext g
  unfold selectedCounts kFalse patternAuxCoordinates
  split_ifs <;> simp

lemma sideCounts_true_eq (ν : Pattern P J ell m) (block : P.BigGroup → Bool) :
    selectedCounts (patternAuxCoordinates ν block true) = kTrue ν block := by
  funext g
  unfold selectedCounts kTrue patternAuxCoordinates
  split_ifs <;> simp

end
end Erdos821.P4Bridge
