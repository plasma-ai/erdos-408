import Erdos821.Blueprint.Graph

/-! A birth event is an average of products of local modulus-at-most-one multipliers.

Each block keeps a pivot; every other address of the block carries an additive character
of `Fin Q`, and the pivot carries the opposite total frequency.  The performed indicator
multiplies each local phase.  Distinct blocks use independent frequency families. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Lowrank

open Erdos821.Blueprint.Graph

theorem phase_eq_exp (t : ℝ) :
    phase t = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
  unfold phase
  push_cast
  ring_nf

theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 := by
  rw [phase_eq_exp, Complex.norm_exp_ofReal_mul_I]

theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_zero : phase 0 = 1 := by
  simp [phase]

theorem phase_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    phase (∑ i ∈ S, f i) = ∏ i ∈ S, phase (f i) := by
  induction S using Finset.induction_on with
  | empty => simp [phase_zero]
  | @insert i S hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, phase_add, ih]

theorem phase_nat_mul (k : ℕ) (t : ℝ) : phase (k * t) = phase t ^ k := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem phase_int (k : ℤ) : phase k = 1 := by
  unfold phase
  rw [Complex.exp_eq_one_iff]
  exact ⟨k, by push_cast; ring⟩

theorem phase_eq_one_imp (t : ℝ) (h : phase t = 1) : ∃ k : ℤ, t = k := by
  unfold phase at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (t : ℂ) = k := by
    apply mul_right_cancel₀ h2
    linear_combination hk
  exact_mod_cast this

/-- Orthogonality of the additive characters of `Fin Q`. -/
theorem sum_phase (Q : ℕ) (hQ : 0 < Q) (d : ℤ) :
    ∑ x : Fin Q, phase (((x : ℕ) : ℝ) * ((d : ℝ) / Q)) = if (Q : ℤ) ∣ d then (Q : ℂ) else 0 := by
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  simp_rw [phase_nat_mul]
  rw [Fin.sum_univ_eq_sum_range (fun x => phase ((d : ℝ) / Q) ^ x) Q]
  split_ifs with hd
  · obtain ⟨k, rfl⟩ := hd
    have : (((Q * k : ℤ) : ℝ)) / Q = (k : ℝ) := by
      push_cast
      field_simp
    rw [this, phase_int]
    simp
  · have hz : phase ((d : ℝ) / Q) ≠ 1 := by
      intro h
      obtain ⟨k, hk⟩ := phase_eq_one_imp _ h
      apply hd
      refine ⟨k, ?_⟩
      have : (d : ℝ) = Q * k := by
        rw [div_eq_iff hQ'] at hk
        rw [hk]
        ring
      exact_mod_cast this
    rw [geom_sum_eq hz, ← phase_nat_mul]
    have : (Q : ℝ) * ((d : ℝ) / Q) = (d : ℝ) := by field_simp
    rw [this, phase_int]
    simp

theorem dvd_sub_iff_eq (Q x y : ℕ) (hx : x < Q) (hy : y < Q) :
    (Q : ℤ) ∣ ((x : ℤ) - y) ↔ x = y := by
  constructor
  · intro h
    have h0 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_sub_lt_iff]; constructor <;> omega)
    omega
  · intro h
    subst h
    simp

/-- The averaged-product representation of a birth event. -/
def Represents {a : ℕ} (π : Finset (Finset (Fin a))) (Q : ℕ) (Ξ : Type) [Fintype Ξ]
    (m : Ξ → Fin a → Prop → ℕ → ℂ) : Prop :=
  (∀ ξ j p v, ‖m ξ j p v‖ ≤ 1) ∧ 0 < Fintype.card Ξ ∧
  ∀ (perf : Finset (Fin a)) (value : Fin a → ℕ), (∀ j, value j < Q) →
    (if birthEvent perf value π then (1 : ℂ) else 0) =
      (Fintype.card Ξ : ℂ)⁻¹ * ∑ ξ, ∏ j ∈ π.biUnion id, m ξ j (j ∈ perf) (value j)

theorem prod_ite_mem_univ {α M : Type*} [Fintype α] [CommMonoid M] (s : Finset α)
    [∀ k, Decidable (k ∈ s)] (f : α → M) :
    ∏ k, (if k ∈ s then f k else 1) = ∏ k ∈ s, f k := by
  rw [← Finset.prod_filter]
  congr 1
  ext k
  simp

/-- A performed-address gate, kept opaque so decidability instances never need to agree. -/
def gate (P : Prop) (z : ℂ) : ℂ := if P then z else 0

theorem gate_pos {P : Prop} (h : P) (z : ℂ) : gate P z = z := if_pos h

theorem gate_neg {P : Prop} (h : ¬ P) (z : ℂ) : gate P z = 0 := if_neg h

theorem norm_gate_le (P : Prop) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖gate P z‖ ≤ 1 := by
  by_cases h : P
  · rw [gate_pos h]
    exact hz
  · rw [gate_neg h, norm_zero]
    exact zero_le_one

/-- One block, with a chosen pivot. -/
theorem block_rep {a : ℕ} (Q : ℕ) (hQ : 0 < Q) (B : Finset (Fin a)) (hB : B.Nonempty) :
    ∃ m : (Fin a → Fin Q) → Fin a → Prop → ℕ → ℂ, (∀ ξ j p v, ‖m ξ j p v‖ ≤ 1) ∧
      ∀ (perf : Finset (Fin a)) (value : Fin a → ℕ), (∀ j, value j < Q) →
        (if B ⊆ perf ∧ ∀ i ∈ B, ∀ j ∈ B, value i = value j then (1 : ℂ) else 0) =
          ((Q : ℂ) ^ a)⁻¹ * ∑ ξ : Fin a → Fin Q, ∏ j ∈ B, m ξ j (j ∈ perf) (value j) := by
  obtain ⟨p, hp⟩ := hB
  let cf : (Fin a → Fin Q) → Fin a → ℤ := fun ξ j =>
    if j = p then -(∑ k ∈ B.erase p, ((ξ k : ℕ) : ℤ)) else ((ξ j : ℕ) : ℤ)
  refine ⟨fun ξ j P v => gate P (phase ((cf ξ j : ℝ) * v / Q)), ?_, ?_⟩
  · intro ξ j P v
    exact norm_gate_le P (le_of_eq (norm_phase _))
  intro perf value hv
  dsimp only
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  by_cases hsub : B ⊆ perf
  · let D : Fin a → ℝ := fun k => (((value k : ℤ) - (value p : ℤ) : ℤ) : ℝ) / Q
    have hprod : ∀ ξ : Fin a → Fin Q,
        ∏ j ∈ B, gate (j ∈ perf) (phase ((cf ξ j : ℝ) * (value j : ℝ) / Q)) =
          ∏ k, (if k ∈ B.erase p then phase (((ξ k : ℕ) : ℝ) * D k) else 1) := by
      intro ξ
      rw [Finset.prod_congr rfl (fun j hj => gate_pos (hsub hj) _), prod_ite_mem_univ,
        ← phase_sum, ← phase_sum]
      congr 1
      rw [← Finset.add_sum_erase B _ hp]
      have hcp : ((cf ξ p : ℤ) : ℝ) = -(∑ k ∈ B.erase p, ((ξ k : ℕ) : ℝ)) := by
        simp only [cf, if_pos rfl]
        push_cast
        rfl
      have hcf : ∀ k ∈ B.erase p, ((cf ξ k : ℤ) : ℝ) = ((ξ k : ℕ) : ℝ) := by
        intro k hk
        simp only [cf, if_neg (Finset.ne_of_mem_erase hk)]
        push_cast
        rfl
      have e1 : ∑ x ∈ B.erase p, ((cf ξ x : ℤ) : ℝ) * ((value x : ℕ) : ℝ) / (Q : ℝ) =
          ∑ x ∈ B.erase p, ((ξ x : ℕ) : ℝ) * ((value x : ℕ) : ℝ) / (Q : ℝ) :=
        Finset.sum_congr rfl (fun k hk => by rw [hcf k hk])
      rw [e1, hcp]
      simp only [D]
      push_cast
      rw [neg_mul, neg_div, Finset.sum_mul, Finset.sum_div, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hk : ∀ k : Fin a,
        ∑ x : Fin Q, (if k ∈ B.erase p then phase (((x : ℕ) : ℝ) * D k) else 1) =
          (Q : ℂ) * (if (k ∈ B.erase p → value k = value p) then 1 else 0) := by
      intro k
      by_cases hkB : k ∈ B.erase p
      · simp only [if_pos hkB, D]
        rw [sum_phase Q hQ]
        by_cases he : value k = value p
        · rw [if_pos ((dvd_sub_iff_eq Q _ _ (hv k) (hv p)).mpr he)]
          simp [he]
        · rw [if_neg (fun h => he ((dvd_sub_iff_eq Q _ _ (hv k) (hv p)).mp h))]
          simp [he, hkB]
      · simp [hkB]
    have hiff : (B ⊆ perf ∧ ∀ i ∈ B, ∀ j ∈ B, value i = value j) ↔
        ∀ k, k ∈ B.erase p → value k = value p := by
      constructor
      · intro h k hk
        exact h.2 k (Finset.mem_of_mem_erase hk) p hp
      · intro h
        refine ⟨hsub, fun i hi j hj => ?_⟩
        have hi' : value i = value p := by
          by_cases hip : i = p
          · rw [hip]
          · exact h i (Finset.mem_erase.mpr ⟨hip, hi⟩)
        have hj' : value j = value p := by
          by_cases hjp : j = p
          · rw [hjp]
          · exact h j (Finset.mem_erase.mpr ⟨hjp, hj⟩)
        rw [hi', hj']
    simp only [hprod]
    rw [← Fintype.prod_sum (fun (k : Fin a) (x : Fin Q) =>
      if k ∈ B.erase p then phase (((x : ℕ) : ℝ) * D k) else 1)]
    simp only [hk]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_boole]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero a hQ'), one_mul]
    by_cases hall : ∀ k, k ∈ B.erase p → value k = value p
    · rw [if_pos (hiff.mpr hall), if_pos (fun k _ => hall k)]
    · rw [if_neg (fun h => hall (hiff.mp h)),
        if_neg (fun h => hall (fun k => h k (Finset.mem_univ k)))]
  · obtain ⟨j, hjB, hjp⟩ := Finset.not_subset.mp hsub
    rw [if_neg (fun h => hsub h.1)]
    have h0 : ∀ ξ : Fin a → Fin Q,
        ∏ j ∈ B, gate (j ∈ perf) (phase ((cf ξ j : ℝ) * (value j : ℝ) / Q)) = 0 :=
      fun ξ => Finset.prod_eq_zero hjB (gate_neg hjp _)
    simp only [h0, Finset.sum_const_zero, mul_zero]

theorem exists_represents {a : ℕ} (Q : ℕ) (hQ : 0 < Q) (π : Finset (Finset (Fin a)))
    (hπ : BirthCollection π) :
    ∃ (Ξ : Type) (_ : Fintype Ξ) (m : Ξ → Fin a → Prop → ℕ → ℂ), Represents π Q Ξ m := by
  induction π using Finset.induction_on with
  | empty =>
      refine ⟨Unit, inferInstance, fun _ _ _ _ => 1, ?_, ?_, ?_⟩
      · intros
        simp
      · simp
      · intro perf value _
        simp [birthEvent]
  | @insert B π hB ih =>
      have hπ' : BirthCollection π :=
        ⟨fun B' hB' => hπ.1 B' (Finset.mem_insert_of_mem hB'),
          hπ.2.mono (Finset.coe_subset.mpr (Finset.subset_insert B π))⟩
      have hBcard := hπ.1 B (Finset.mem_insert_self B π)
      have hdisj : ∀ B' ∈ π, Disjoint B B' := fun B' hB' =>
        hπ.2 (Finset.mem_coe.mpr (Finset.mem_insert_self B π))
          (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hB')) (fun h => hB (h ▸ hB'))
      have hdU : Disjoint B (π.biUnion id) := (Finset.disjoint_biUnion_right _ _ _).mpr hdisj
      obtain ⟨Ξ, hΞ, m', hm', hcard', hrep'⟩ := ih hπ'
      obtain ⟨mB, hmB, hrepB⟩ := block_rep Q hQ B (Finset.card_pos.mp (by omega))
      refine ⟨(Fin a → Fin Q) × Ξ, inferInstance,
        fun ξ j P v => if j ∈ B then mB ξ.1 j P v else m' ξ.2 j P v, ?_, ?_, ?_⟩
      · intro ξ j P v
        dsimp only
        split_ifs
        · exact hmB _ _ _ _
        · exact hm' _ _ _ _
      · rw [Fintype.card_prod]
        exact Nat.mul_pos (by simp [hQ]) hcard'
      · intro perf value hv
        have hev : birthEvent perf value (insert B π) ↔
            (B ⊆ perf ∧ ∀ i ∈ B, ∀ j ∈ B, value i = value j) ∧ birthEvent perf value π := by
          simp only [birthEvent, Finset.forall_mem_insert]
        have hL : (if birthEvent perf value (insert B π) then (1 : ℂ) else 0) =
            (if B ⊆ perf ∧ ∀ i ∈ B, ∀ j ∈ B, value i = value j then (1 : ℂ) else 0) *
              (if birthEvent perf value π then (1 : ℂ) else 0) := by
          by_cases h1 : B ⊆ perf ∧ ∀ i ∈ B, ∀ j ∈ B, value i = value j
          · by_cases h2 : birthEvent perf value π
            · rw [if_pos (hev.mpr ⟨h1, h2⟩), if_pos h1, if_pos h2, one_mul]
            · rw [if_neg (fun h => h2 (hev.mp h).2), if_neg h2, mul_zero]
          · rw [if_neg (fun h => h1 (hev.mp h).1), if_neg h1, zero_mul]
        rw [hL, hrepB perf value hv, hrep' perf value hv]
        have hsplit : ∀ ξ : (Fin a → Fin Q) × Ξ,
            (∏ j ∈ B ∪ π.biUnion id,
              (if j ∈ B then mB ξ.1 j (j ∈ perf) (value j) else m' ξ.2 j (j ∈ perf) (value j))) =
            (∏ j ∈ B, mB ξ.1 j (j ∈ perf) (value j)) *
              ∏ j ∈ π.biUnion id, m' ξ.2 j (j ∈ perf) (value j) := by
          intro ξ
          rw [Finset.prod_union hdU]
          congr 1
          · exact Finset.prod_congr rfl fun j hj => if_pos hj
          · exact Finset.prod_congr rfl fun j hj =>
              if_neg (Finset.disjoint_right.mp hdU hj)
        rw [Finset.biUnion_insert, id_eq]
        simp only [hsplit]
        rw [Fintype.sum_prod_type]
        dsimp only
        rw [← Finset.sum_mul_sum, Fintype.card_prod, Fintype.card_fun]
        simp only [Fintype.card_fin]
        push_cast
        rw [mul_inv]
        ring

end Erdos821.P3Lowrank
