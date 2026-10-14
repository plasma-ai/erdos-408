import Erdos408.OneSided.Decomposition.LiftSum
import Erdos408.OneSided.Decomposition.Measure

/-!
# Shared labels and pad collisions

Label tuples and pads drawn independently with the harmonic laws `μ_i(p) = 1/(p V_i)`.

* Two label tuples share a prime with probability at most `K² ε`, where `ε` bounds every
  atom `μ_i(p)` (PD Lemma 1.2 and `mem:unshared-collisions`).
* The pads fail to be distinct and disjoint from the labels with probability at most
  `((KJ)² + 2KJ) ε` (PD §4.9).
-/

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

/-- The probability `∏_i μ_i(p_i)` of a label tuple. -/
noncomputable def labelWeight (x : ℝ) (d : Data K) (p : Fin K → ℕ) : ℝ :=
  ∏ i, 1 / ((p i : ℝ) * harmonicMass (band x (d.a i)))

/-- Each harmonic law has total mass one. -/
theorem sum_one_div_mul_harmonicMass {S : Finset ℕ} (hS : 0 < harmonicMass S) :
    ∑ y ∈ S, 1 / ((y : ℝ) * harmonicMass S) = 1 := by
  calc ∑ y ∈ S, 1 / ((y : ℝ) * harmonicMass S) = ∑ y ∈ S, 1 / (y : ℝ) * (harmonicMass S)⁻¹ :=
        sum_congr rfl fun y _ => by ring
    _ = harmonicMass S * (harmonicMass S)⁻¹ := by rw [← sum_mul]; rfl
    _ = 1 := mul_inv_cancel₀ hS.ne'

/-- The atoms of a harmonic law are nonnegative. -/
theorem one_div_mul_harmonicMass_nonneg {S : Finset ℕ} (hS : 0 < harmonicMass S) (y : ℕ) :
    0 ≤ 1 / ((y : ℝ) * harmonicMass S) := by
  positivity

/-- The label tuples have total mass one. -/
theorem sum_labelWeight {x : ℝ} {d : Data K} (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) :
    ∑ p ∈ d.labels x, labelWeight x d p = 1 := by
  unfold labelWeight Data.labels
  exact sum_piFinset_prod_eq_one fun i => sum_one_div_mul_harmonicMass (hV i)

/-- The pads have total mass one. -/
theorem sum_padWeight {x : ℝ} {d : Data K} (hV : ∀ i, 0 < harmonicMass (band x (d.a i)))
    (J : ℕ) : ∑ z ∈ padSet x d J, padWeight x d z = 1 := by
  have h := sum_piFinset_prod_eq_one (S := fun c : Fin K × Fin J => band x (d.a c.1))
    (w := fun c y => 1 / ((y : ℝ) * harmonicMass (band x (d.a c.1))))
    fun c => sum_one_div_mul_harmonicMass (hV c.1)
  exact h

open scoped Classical in
/-- **Shared labels.** Two independent label tuples share a prime with probability at most
`K² ε`. -/
theorem sum_labelWeight_shared_le {x : ℝ} {d : Data K}
    (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ i, ∀ y ∈ band x (d.a i), 1 / ((y : ℝ) * harmonicMass (band x (d.a i))) ≤ ε) :
    ∑ p ∈ d.labels x, ∑ p' ∈ d.labels x,
        (if Unshared p p' then 0 else labelWeight x d p * labelWeight x d p') ≤ K ^ 2 * ε := by
  have hw0 : ∀ p, 0 ≤ labelWeight x d p := fun p =>
    prod_nonneg fun i _ => one_div_mul_harmonicMass_nonneg (hV i) _
  -- a shared prime is some coincidence `p_i = p'_{i'}`
  have hind : ∀ p p' : Fin K → ℕ,
      (if Unshared p p' then 0 else labelWeight x d p * labelWeight x d p') ≤
        ∑ i, ∑ i', labelWeight x d p *
          (if p' i' = p i then labelWeight x d p' else 0) := by
    intro p p'
    split_ifs with hU
    · exact sum_nonneg fun i _ => sum_nonneg fun i' _ =>
        mul_nonneg (hw0 p) (by split_ifs <;> simp [hw0])
    · unfold Unshared at hU
      push Not at hU
      obtain ⟨i, i', hii⟩ := hU
      refine le_trans ?_ (single_le_sum (fun i _ => sum_nonneg fun i' _ =>
        mul_nonneg (hw0 p) (by split_ifs <;> simp [hw0])) (mem_univ i))
      refine le_trans ?_ (single_le_sum (f := fun i' => labelWeight x d p *
        (if p' i' = p i then labelWeight x d p' else 0)) (fun i' _ =>
          mul_nonneg (hw0 p) (by split_ifs <;> simp [hw0])) (mem_univ i'))
      rw [ite_eq_left hii.symm]
  calc ∑ p ∈ d.labels x, ∑ p' ∈ d.labels x,
        (if Unshared p p' then 0 else labelWeight x d p * labelWeight x d p')
      ≤ ∑ p ∈ d.labels x, ∑ p' ∈ d.labels x, ∑ i, ∑ i', labelWeight x d p *
          (if p' i' = p i then labelWeight x d p' else 0) :=
        sum_le_sum fun p _ => sum_le_sum fun p' _ => hind p p'
    _ = ∑ p ∈ d.labels x, labelWeight x d p * ∑ i, ∑ i',
          ∑ p' ∈ d.labels x, (if p' i' = p i then labelWeight x d p' else 0) := by
        refine sum_congr rfl fun p _ => ?_
        simp only [mul_sum]
        exact (sum_sum_sum_comm _ _ _ _).symm
    _ ≤ ∑ p ∈ d.labels x, labelWeight x d p * ∑ _i : Fin K, ∑ _i' : Fin K, ε := by
        refine sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (sum_le_sum fun i _ =>
          sum_le_sum fun i' _ => ?_) (hw0 p)
        exact sum_piFinset_ite_eq_le (fun i y _ => one_div_mul_harmonicMass_nonneg (hV i) y)
          (fun i => sum_one_div_mul_harmonicMass (hV i)) hε0 hε i' (p i)
    _ = K ^ 2 * ε := by
        rw [← sum_mul, sum_labelWeight hV, one_mul]
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

open scoped Classical in
/-- **Pad collisions.** The pads fail to be distinct and disjoint from the labels with
probability at most `((KJ)² + 2KJ) ε`. -/
theorem sum_padWeight_bad_le {x : ℝ} {d : Data K}
    (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ i, ∀ y ∈ band x (d.a i), 1 / ((y : ℝ) * harmonicMass (band x (d.a i))) ≤ ε)
    (J : ℕ) (p p' : Fin K → ℕ) :
    ∑ z ∈ padSet x d J, (if GoodPads p p' z then 0 else padWeight x d z) ≤
      ((K * J : ℕ) ^ 2 + 2 * (K * J : ℕ)) * ε := by
  set μ := padWeight x d (J := J)
  have hw0 : ∀ z, 0 ≤ μ z := fun z =>
    prod_nonneg fun c _ => one_div_mul_harmonicMass_nonneg (hV c.1) _
  have hite : ∀ (P : Prop) [Decidable P] (z : Fin K × Fin J → ℕ), 0 ≤ if P then μ z else 0 :=
    fun P _ z => by split_ifs <;> simp [hw0]
  -- a failure is a coincidence of two pads, or of a pad with a label
  have hind : ∀ z, (if GoodPads p p' z then 0 else μ z) ≤
      ∑ c, ∑ c', (if c ≠ c' then (if z c = z c' then μ z else 0) else 0) +
        ∑ c, (if z c = p c.1 then μ z else 0) + ∑ c, (if z c = p' c.1 then μ z else 0) := by
    intro z
    have h₁ : 0 ≤ ∑ c, ∑ c', (if c ≠ c' then (if z c = z c' then μ z else 0) else 0) :=
      sum_nonneg fun c _ => sum_nonneg fun c' _ => by split_ifs <;> simp [hw0]
    have h₂ : 0 ≤ ∑ c, (if z c = p c.1 then μ z else 0) := sum_nonneg fun c _ => hite _ z
    have h₃ : 0 ≤ ∑ c, (if z c = p' c.1 then μ z else 0) := sum_nonneg fun c _ => hite _ z
    split_ifs with hG
    · linarith
    · unfold GoodPads at hG
      rw [not_and_or] at hG
      rcases hG with hinj | hlab
      · obtain ⟨c, c', hzz, hcc⟩ : ∃ c c', z c = z c' ∧ c ≠ c' := by
          by_contra hno
          push Not at hno
          exact hinj fun c c' h => hno c c' h
        have : μ z ≤ ∑ c, ∑ c', (if c ≠ c' then (if z c = z c' then μ z else 0) else 0) := by
          refine le_trans ?_ (single_le_sum (fun c _ => sum_nonneg fun c' _ => by
            split_ifs <;> simp [hw0]) (mem_univ c))
          refine le_trans ?_ (single_le_sum (f := fun c' => if c ≠ c' then
            (if z c = z c' then μ z else 0) else 0) (fun c' _ => by
              split_ifs <;> simp [hw0]) (mem_univ c'))
          rw [ite_eq_left hcc, ite_eq_left hzz]
        linarith
      · push Not at hlab
        obtain ⟨c, hc⟩ := hlab
        by_cases hcp : z c = p c.1
        · have : μ z ≤ ∑ c, (if z c = p c.1 then μ z else 0) := by
            refine le_trans ?_ (single_le_sum (f := fun c => if z c = p c.1 then μ z else 0)
              (fun c _ => hite _ z) (mem_univ c))
            rw [ite_eq_left hcp]
          linarith
        · have : μ z ≤ ∑ c, (if z c = p' c.1 then μ z else 0) := by
            refine le_trans ?_ (single_le_sum (f := fun c => if z c = p' c.1 then μ z else 0)
              (fun c _ => hite _ z) (mem_univ c))
            rw [ite_eq_left (hc hcp)]
          linarith
  have hw0' : ∀ (c : Fin K × Fin J), ∀ y ∈ band x (d.a c.1),
      0 ≤ 1 / ((y : ℝ) * harmonicMass (band x (d.a c.1))) :=
    fun c y _ => one_div_mul_harmonicMass_nonneg (hV c.1) y
  have hw1 : ∀ c : Fin K × Fin J, ∑ y ∈ band x (d.a c.1),
      1 / ((y : ℝ) * harmonicMass (band x (d.a c.1))) = 1 :=
    fun c => sum_one_div_mul_harmonicMass (hV c.1)
  have hεc : ∀ (c : Fin K × Fin J), ∀ y ∈ band x (d.a c.1),
      1 / ((y : ℝ) * harmonicMass (band x (d.a c.1))) ≤ ε := fun c => hε c.1
  calc ∑ z ∈ padSet x d J, (if GoodPads p p' z then 0 else μ z)
      ≤ ∑ z ∈ padSet x d J,
          (∑ c, ∑ c', (if c ≠ c' then (if z c = z c' then μ z else 0) else 0) +
            ∑ c, (if z c = p c.1 then μ z else 0) + ∑ c, (if z c = p' c.1 then μ z else 0)) :=
        sum_le_sum fun z _ => hind z
    _ = ∑ c, ∑ c', (if c ≠ c' then ∑ z ∈ padSet x d J, (if z c = z c' then μ z else 0)
            else 0) +
          ∑ c, ∑ z ∈ padSet x d J, (if z c = p c.1 then μ z else 0) +
          ∑ c, ∑ z ∈ padSet x d J, (if z c = p' c.1 then μ z else 0) := by
        rw [sum_add_distrib, sum_add_distrib, sum_comm, sum_comm (s := padSet x d J),
          sum_comm (s := padSet x d J)]
        congr 2
        refine sum_congr rfl fun c _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun c' _ => ?_
        split_ifs <;> simp
    _ ≤ ∑ _c : Fin K × Fin J, ∑ _c' : Fin K × Fin J, ε + ∑ _c : Fin K × Fin J, ε +
          ∑ _c : Fin K × Fin J, ε := by
        gcongr with c _ c' _ c _ c _
        · split_ifs with hcc
          · exact sum_piFinset_ite_eq_eq_le hw0' hw1 hεc hcc
          · exact hε0
        · exact sum_piFinset_ite_eq_le hw0' hw1 hε0 hεc c (p c.1)
        · exact sum_piFinset_ite_eq_le hw0' hw1 hε0 hεc c (p' c.1)
    _ = ((K * J : ℕ) ^ 2 + 2 * (K * J : ℕ)) * ε := by
        simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end Erdos408.OneSided
