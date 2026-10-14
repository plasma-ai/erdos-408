import Erdos821.P3Clean.Coordinates
import Erdos821.P3Clean.Laws

/-! Literal clean patterns after separating small prefixes and big labels. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {P : PrimeGroups} {F : FixedData} {J ell m : ℕ}

def prefixPrimeProduct (J : ℕ) (d : SmallLabels P J) : ℕ :=
  ∏ g : P.SmallGroup, ∏ j : Fin J, (d g j).val

theorem prefixPrimeProduct_pos (J : ℕ) (d : SmallLabels P J) : 0 < prefixPrimeProduct J d := by
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro j _
  exact (P.prime g.val (d g j).val (d g j).property).pos

theorem D_pos (ν : Pattern P J ell m) (a : P.Labels (J + ell)) (u : P.Aux J) :
    0 < ν.D a u := by
  unfold Pattern.D
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact (P.prime g (u g i).val (u g i).property).pos
  · exact (P.prime g (a g (ν.slot i)).val (a g (ν.slot i)).property).pos

theorem DBig_pos (ν : Pattern P J ell m) (a : P.BigLabels (J + ell)) (u : P.BigAux J) :
    0 < ν.DBig a u := by
  unfold Pattern.DBig
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact (P.prime g.val (u g i).val (u g i).property).pos
  · exact (P.prime g.val (a g (ν.slot i)).val (a g (ν.slot i)).property).pos

theorem smallPrefixProduct_eq (J ell : ℕ) (a : SmallLabels P (J + ell)) :
    smallPrefixProduct J (Nat.le_add_right J ell) a =
      prefixPrimeProduct J (smallArrayPrefix J ell a) := rfl

theorem compatible_join (ν : Pattern P J ell m) (a c : SmallLabels P (J + ell))
    (b d : P.BigLabels (J + ell)) :
    ν.compatible (joinLabels a b) (joinLabels c d) ↔
      smallArrayPrefix J ell a = smallArrayPrefix J ell c ∧ ν.matchesBig b d := by
  rw [compatible_split]
  have hb : P.restrictBig (joinLabels a b) = b := by funext g; exact joinLabels_big a b g
  have hd : P.restrictBig (joinLabels c d) = d := by funext g; exact joinLabels_big c d g
  rw [hb, hd]
  simp only [joinLabels_small, smallArrayPrefix, funext_iff, Pattern.slot,
    Fin.castAdd, Fin.castLE]

def bigBan (ν : Pattern P J ell m) (a b : P.BigLabels (J + ell)) (u : P.BigAux J) : Prop :=
  ∀ g : P.BigGroup, ∀ i ∈ ν.changed g.val, ∀ j, u g i ≠ a g j ∧ u g i ≠ b g j

theorem ban_join (ν : Pattern P J ell m) (a c : SmallLabels P (J + ell))
    (b d : P.BigLabels (J + ell)) (v : SmallLabels P J) (u : P.BigAux J) :
    ν.ban (joinLabels a b) (joinLabels c d) (joinLabels v u) ↔ bigBan ν b d u := by
  rw [ban_split]
  simp only [bigBan, joinLabels_big]

theorem D_join (ν : Pattern P J ell m) (a : SmallLabels P (J + ell))
    (b : P.BigLabels (J + ell)) (v : SmallLabels P J) (u : P.BigAux J) :
    ν.D (joinLabels a b) (joinLabels v u) =
      prefixPrimeProduct J (smallArrayPrefix J ell a) * ν.DBig b u := by
  rw [D_split]
  have ha : restrictSmall (joinLabels a b) = a := by funext g; exact joinLabels_small a b g
  have hb : P.restrictBig (joinLabels a b) = b := by funext g; exact joinLabels_big a b g
  have hu : (fun g : P.BigGroup => joinLabels v u g.val) = u := by
    funext g
    exact joinLabels_big v u g
  rw [ha, hb, hu, smallPrefixProduct_eq]

def smallAuxMass {J : ℕ} (u : SmallLabels P J) : ℝ :=
  ∏ g : P.SmallGroup, ∏ i : Fin J, P.mu g.val (u g i)

theorem auxMass_join (ν : Pattern P J ell m) (v : SmallLabels P J) (u : P.BigAux J) :
    ν.auxMass (joinLabels v u) = smallAuxMass v * ν.bigAuxMass u := by
  unfold Pattern.auxMass Pattern.bigAuxMass smallAuxMass
  rw [prod_group_split]
  simp only [joinLabels_small, joinLabels_big]

theorem smallAuxMass_sum (J : ℕ) (hV : ∀ g : P.SmallGroup, P.V g.val ≠ 0) :
    (∑ v : SmallLabels P J, smallAuxMass v) = 1 := by
  classical
  unfold smallAuxMass
  rw [← Fintype.prod_sum (fun (g : P.SmallGroup) (a : Fin J → P.Prime g.val) =>
    ∏ i, P.mu g.val (a i))]
  simp only [← Fintype.prod_sum]
  simp only [mu_sum _ (hV _), Finset.prod_const_one]

def tiltedFreshMass (F : FixedData) (n : ℕ) (ν : Pattern P J ell m)
    (b : P.BigLabels (J + ell)) : ℝ :=
  ∏ g : P.BigGroup, ∏ i : Fin (J + ell), if ν.shared g.val i then 1 else tiltedMu F P n g.val (b g i)

theorem freshBigFactor_empty (F : FixedData) (n : ℕ) (ν : Pattern P J F.ell m)
    (a : SmallLabels P (J + F.ell)) (b : P.BigLabels (J + F.ell)) :
    freshBigFactor F n ν (fun _ => ∅) (joinLabels a b) = tiltedFreshMass F n ν b := by
  simp only [freshBigFactor, tiltedFreshMass, Finset.notMem_empty, or_false, joinLabels_big]

def bigStep (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (d : SmallLabels P J) (a : P.BigLabels (J + F.ell)) (u : P.BigAux J) : ℤ :=
  (if forward then A.k else -A.k) * (prefixPrimeProduct J d : ℤ) * (ν.DBig a u : ℤ)

theorem edgeDelta_join (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (a : SmallLabels P (J + F.ell)) (b : P.BigLabels (J + F.ell))
    (v : SmallLabels P J) (u : P.BigAux J) :
    edgeDelta A ν forward (joinLabels a b) (joinLabels v u) =
      bigStep A ν forward (smallArrayPrefix J F.ell a) b u := by
  simp only [edgeDelta, D_join, Nat.cast_mul, bigStep]
  split_ifs <;> ring

theorem rawEdgeValid_empty_join (A : Model F P J m) (ν : Pattern P J F.ell m)
    (forward : Bool) (a c : SmallLabels P (J + F.ell))
    (b d : P.BigLabels (J + F.ell)) (v : SmallLabels P J) (u : P.BigAux J)
    (s t : PendingState P) :
    rawEdgeValid A ν forward (joinLabels v u)
      (s.1, joinLabels a b, s.2) (t.1, joinLabels c d, t.2)
      (emptyTransfer (s.1, joinLabels a b, s.2)) ↔
      a ∈ smallArrayStates P (J + F.ell) s.1 ∧
      c ∈ smallArrayStates P (J + F.ell) t.1 ∧
      smallArrayPrefix J F.ell a = smallArrayPrefix J F.ell c ∧
      ν.matchesBig b d ∧ bigBan ν b d u ∧
      t = translatePending (bigStep A ν forward (smallArrayPrefix J F.ell a) b u) s := by
  rw [rawEdgeValid_empty]
  simp only [smallPhysical_join, compatible_join, ban_join, edgeDelta_join]
  have ht : t = translatePending (bigStep A ν forward (smallArrayPrefix J F.ell a) b u) s ↔
      t.1 = translateSmallResidues (bigStep A ν forward (smallArrayPrefix J F.ell a) b u) s.1 ∧
        ∀ g : P.BigGroup,
          t.2 g = translateMemory (bigStep A ν forward (smallArrayPrefix J F.ell a) b u) (s.2 g) := by
    simp only [translatePending, Prod.ext_iff, funext_iff]
  rw [ht]
  tauto

def rawCleanCoefficient (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool)
    (ν : Pattern P J F.ell m) (u : P.Aux J)
    (s t : P.MemoryState (J + F.ell)) : ℂ :=
  let D := ν.D s.2.1 u
  let z := ν.coefficient (P.restrictBig s.2.1) (P.restrictBig t.2.1) (fun g => u g.val) *
    imaginaryPower D A.zeta
  let zr := star (ν.coefficient (P.restrictBig t.2.1) (P.restrictBig s.2.1) (fun g => u g.val) *
    imaginaryPower D A.zeta)
  (rawEdgeWeight A n 1 ν u s t (emptyTransfer s) : ℂ) * (if forward then z else zr) *
    phase (theta * (edgeDelta A ν forward s.2.1 u : ℝ))

def rawCleanKernel (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool)
    (s t : P.MemoryState (J + F.ell)) : ℂ :=
  ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
    if rawEdgeValid A (A.pattern v) forward u s t (emptyTransfer s) then
      rawCleanCoefficient A n theta forward (A.pattern v) u s t else 0

theorem cleanEdgeKernel_one (A : Model F P J m) (n : ℕ) (theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) :
    cleanEdgeKernel A n 1 theta i s t =
      (edgeSymmetryFactor P (J + F.ell) : ℂ) *
        ∑ π : P.Permutations (J + F.ell), ∑ τ : P.Permutations (J + F.ell),
          rawCleanKernel A n theta (edgeForward i) (permuteActive π s) (permuteActive τ t) := by
  rfl


end Erdos821.P3Clean
