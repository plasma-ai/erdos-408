import Erdos821.P3Clean.Structure
import Erdos821.P3Clean.Contractions

/-! The damping factors of a literal clean edge. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {P : PrimeGroups} {F : FixedData}

theorem small_zero_count_ge {M : ℕ} (y : P.SmallResidues) (a : P.Labels M)
    (h : P.smallPhysical y a) (g : P.SmallGroup) :
    M ≤ (Finset.univ.filter (fun p : P.Prime g.val => y g p = 0)).card := by
  classical
  have hcard : (Finset.univ.image (a g.val)).card = M := by
    rw [Finset.card_image_of_injective _ (h g).1]
    simp
  rw [← hcard]
  apply Finset.card_le_card
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h g).2 i⟩

theorem smallOmega_ge {M : ℕ} (y : P.SmallResidues) (a : P.Labels M)
    (h : P.smallPhysical y a) : M * Fintype.card P.SmallGroup ≤ smallOmega y := by
  calc
    _ = ∑ g : P.SmallGroup, M := by simp [Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun g _ => small_zero_count_ge y a h g)

theorem smallDamping_le_one (J : ℕ) (y : P.SmallResidues) (a : P.Labels (J + F.ell))
    (h : P.smallPhysical y a) : smallDamping F J y ≤ 1 := by
  have hcount : ((J + F.ell : ℕ) : ℝ) * Fintype.card P.SmallGroup ≤
      (smallOmega y : ℝ) := by exact_mod_cast smallOmega_ge y a h
  unfold smallDamping
  apply Real.rpow_le_one F.q_pos.le F.q_lt.le
  exact div_nonneg (sub_nonneg.mpr (by simpa only [Nat.cast_add] using hcount))
    (by norm_num)

theorem smallDamping_pos (J : ℕ) (y : P.SmallResidues) : 0 < smallDamping F J y :=
  Real.rpow_pos_of_pos F.q_pos _

def pendingDamping {M : ℕ} (rho : ℝ) (s : P.MemoryState M) : ℝ :=
  rho ^ (∑ g : P.BigGroup, (zeroMemoryIndices (s.2.2 g)).card)

theorem pendingDamping_nonneg {M : ℕ} (r : MemoryParameters F) (s : P.MemoryState M) :
    0 ≤ pendingDamping r.rho s := pow_nonneg r.rho_pos.le _

theorem pendingDamping_le_one {M : ℕ} (r : MemoryParameters F) (s : P.MemoryState M) :
    pendingDamping r.rho s ≤ 1 := pow_le_one₀ r.rho_pos.le r.rho_lt.le

theorem rawEdgeWeight_rho {J m : ℕ} (A : Model F P J m) (n : ℕ) (rho : ℝ)
    (ν : Pattern P J F.ell m) (u : P.Aux J)
    (s t : P.MemoryState (J + F.ell)) (c : TransferChoice s) :
    rawEdgeWeight A n rho ν u s t c =
      pendingDamping rho s * rawEdgeWeight A n 1 ν u s t c * pendingDamping rho t := by
  simp only [rawEdgeWeight, one_pow, mul_one, pendingDamping, pow_add]
  ring

theorem edgeChoiceCoefficient_rho {J m : ℕ} (A : Model F P J m) (n : ℕ)
    (rho theta : ℝ) (i : Fin n) (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) :
    edgeChoiceCoefficient A n rho theta i s t c =
      (pendingDamping rho s : ℂ) * edgeChoiceCoefficient A n 1 theta i s t c *
        (pendingDamping rho t : ℂ) := by
  simp only [edgeChoiceCoefficient]
  rw [rawEdgeWeight_rho A n rho (A.pattern c.2.2.1) c.2.2.2.1
    (permuteActive c.1 s) (permuteActive c.2.1 t) c.2.2.2.2]
  simp only [Complex.ofReal_mul]
  change ((pendingDamping rho s : ℂ) * _ * (pendingDamping rho t : ℂ)) * _ * _ = _
  ring

theorem memoryEdgeKernel_rho {J m : ℕ} (A : Model F P J m) (n : ℕ)
    (rho theta : ℝ) (i : Fin n) (mode : TransferMode)
    (phi : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ)
    (s t : P.MemoryState (J + F.ell)) :
    memoryEdgeKernel A n rho theta i mode phi s t =
      (pendingDamping rho s : ℂ) * memoryEdgeKernel A n 1 theta i mode phi s t *
        (pendingDamping rho t : ℂ) := by
  classical
  have hc (c : EdgeChoice A s) :
      (if edgeChoiceValid A mode i s t c then
        edgeChoiceCoefficient A n rho theta i s t c * phi s t c else 0) =
      (pendingDamping rho s : ℂ) *
        (if edgeChoiceValid A mode i s t c then
          edgeChoiceCoefficient A n 1 theta i s t c * phi s t c else 0) *
        (pendingDamping rho t : ℂ) := by
    by_cases h : edgeChoiceValid A mode i s t c
    · rw [if_pos h, if_pos h, edgeChoiceCoefficient_rho]
      ring
    · simp only [if_neg h, mul_zero, zero_mul]
  simp only [memoryEdgeKernel]
  simp_rw [hc]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem normBound_memoryEdge_damping {J m n : ℕ} (A : Model F P J m)
    (r : MemoryParameters F) (theta : ℝ) (i : Fin n) (mode : TransferMode)
    (phi : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ)
    (mass : P.MemoryState (J + F.ell) → ℝ) (hm : ∀ s, 0 ≤ mass s)
    (C : ℝ) (hC : 0 ≤ C)
    (hK : NormBound mass (memoryEdgeKernel A n 1 theta i mode phi) C) :
    NormBound mass (memoryEdgeKernel A n r.rho theta i mode phi) C := by
  have h := normBound_mul_endpoints hm hC hK
    (fun s => (pendingDamping r.rho s : ℂ)) (fun s => (pendingDamping r.rho s : ℂ))
    (by intro s; simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pendingDamping_nonneg r s)] using pendingDamping_le_one r s)
    (by intro s; simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pendingDamping_nonneg r s)] using pendingDamping_le_one r s)
  simpa only [← memoryEdgeKernel_rho] using h

theorem memoryMass_nonneg (J n : ℕ)
    (hV : ∀ g, 0 < P.V g)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (s : P.MemoryState (J + F.ell)) : 0 ≤ P.memoryMass F J n s := by
  classical
  have ht (g : P.BigGroup) (p : P.Prime g.val) : 0 ≤ tiltedMu F P n g.val p := by
    unfold tiltedMu
    apply inv_nonneg.mpr
    exact (mul_pos (mul_pos (hV g.val)
      (by exact_mod_cast (P.prime g.val p.val p.property).pos)) (hb g p)).le
  have hg (g : P.BigGroup) : 0 ≤ P.groupMemoryMass F n g.val (s.2.2 g) := by
    unfold PrimeGroups.groupMemoryMass
    apply div_nonneg
    · apply Multiset.prod_nonneg
      intro z hz
      obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hz
      exact ht g p.1
    · positivity
  unfold PrimeGroups.memoryMass
  split_ifs
  · apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · exact Finset.prod_nonneg (fun g _ => zpow_nonneg (hV g.val).le _)
      · exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => ht g _))
    · exact Finset.prod_nonneg (fun g _ => hg g)
  · exact le_refl 0


end Erdos821.P3Clean
