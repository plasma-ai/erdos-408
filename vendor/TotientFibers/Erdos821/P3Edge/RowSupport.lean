import Erdos821.S2.MemoryEdge
import Erdos821.S2.EdgeTasks

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def targetSmall (A : Model F P J m) {n : ℕ} (i : Fin n)
    (s : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) : P.SmallResidues :=
  translateSmallResidues
    (edgeDelta A (A.pattern c.2.2.1) (edgeForward i) (permuteActive c.1 s).2.1 c.2.2.2.1)
    (permuteActive c.1 s).1

def targetMem (A : Model F P J m) {n : ℕ} (i : Fin n)
    (s : P.MemoryState (J + F.ell)) (c : EdgeChoice A s)
    (g : P.BigGroup) : P.Memory (g : P.Group) :=
  translateMemory
    (edgeDelta A (A.pattern c.2.2.1) (edgeForward i) (permuteActive c.1 s).2.1 c.2.2.2.1)
    (deleteMemoryIndices ((permuteActive c.1 s).2.2 g) (retrievedIndices c.2.2.2.2 g) +
      storedMemory ((permuteActive c.1 s).2.1 (g : P.Group)) (c.2.2.2.2.1 g))

lemma valid_target_small (A : Model F P J m) {n : ℕ} (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s)
    (h : edgeChoiceValid A .all i s t c) :
    t.1 = targetSmall A i s c := by
  have h2 : rawEdgeValid A (A.pattern c.2.2.1) (edgeForward i) c.2.2.2.1
      (permuteActive c.1 s) (permuteActive c.2.1 t) c.2.2.2.2 := by
    simpa [edgeChoiceValid] using h.1
  have h3 := h2.2.2.2.2.1
  have ht : ((permuteActive c.2.1 t).1) = t.1 := rfl
  rw [ht] at h3
  unfold targetSmall
  exact h3

lemma valid_target_mem (A : Model F P J m) {n : ℕ} (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s)
    (h : edgeChoiceValid A .all i s t c) (g : P.BigGroup) :
    t.2.2 g = targetMem A i s c g := by
  have h2 : rawEdgeValid A (A.pattern c.2.2.1) (edgeForward i) c.2.2.2.1
      (permuteActive c.1 s) (permuteActive c.2.1 t) c.2.2.2.2 := by
    simpa [edgeChoiceValid] using h.1
  have hmem := ((h2.2.2.2.2.2 g).2.2.2.2)
  have ht : ((permuteActive c.2.1 t).2.2 g) = t.2.2 g := rfl
  rw [ht] at hmem
  unfold targetMem
  exact hmem

end Erdos821.P3Edge
