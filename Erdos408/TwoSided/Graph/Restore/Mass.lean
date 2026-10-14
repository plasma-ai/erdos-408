import Erdos408.TwoSided.Graph.Restore.Strip

/-!
# Label masses

Labels `a ∈ auxLabels P S` (a prime of `P g` in each slot of `S g`, `1` elsewhere) carry the
product mass `labelMass P S a = ∏_g ∏_{i ∈ S g} μ_g(a_{g,i})`, `μ_g(p) = 1/(V_g p)`, of total
mass `1` (both in `Setup.lean`). It is a product measure (`sum_auxLabels_prod`). Its one- and
two-slot marginals bound the suppressed restrictions of S4 (blueprint §4.4):

* a label in a given slot satisfies `Q` with mass `∑_{p ∈ P_g, Q p} μ_g(p)`
  (`sum_labelMass_mul_ite`);
* two given slots of a group coincide with mass `∑_p μ_g(p)²` (`sum_labelMass_mul_ite_eq`).
-/

namespace Erdos408.TwoSided

namespace Restore

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ}

/-- The factor of the label mass at one slot. -/
noncomputable def slotMass (P : ι → Finset ℕ) (S : ι → Finset (Fin J)) (g : ι) (i : Fin J)
    (v : ℕ) : ℝ :=
  if i ∈ S g then (harmonicMass (P g) * v)⁻¹ else 1

omit [DecidableEq ι] in
/-- The label mass is a product over all slots. -/
lemma labelMass_eq_prod (P : ι → Finset ℕ) (S : ι → Finset (Fin J)) (a : ι → Fin J → ℕ) :
    labelMass P S a = ∏ g, ∏ i, slotMass P S g i (a g i) := by
  unfold labelMass slotMass
  exact prod_congr rfl fun g _ => (Fintype.prod_ite_mem (S g) _).symm

/-- The label mass is a product measure. -/
lemma sum_auxLabels_prod (P : ι → Finset ℕ) (S : ι → Finset (Fin J))
    (f : ι → Fin J → ℕ → ℝ) :
    ∑ a ∈ auxLabels P S, ∏ g, ∏ i, f g i (a g i) =
      ∏ g, ∏ i, ∑ v ∈ (if i ∈ S g then P g else {1}), f g i v := by
  unfold auxLabels
  calc _ = ∏ g, ∑ y ∈ Fintype.piFinset (fun i => if i ∈ S g then P g else {1}),
        ∏ i, f g i (y i) := (prod_univ_sum _ _).symm
    _ = _ := prod_congr rfl fun g _ => (prod_univ_sum _ _).symm

omit [Fintype ι] [DecidableEq ι] in
/-- Each slot has mass `1`. -/
lemma sum_slotMass {P : ι → Finset ℕ} (hV : ∀ g, harmonicMass (P g) ≠ 0)
    (S : ι → Finset (Fin J)) (g : ι) (i : Fin J) :
    ∑ v ∈ (if i ∈ S g then P g else {1}), slotMass P S g i v = 1 := by
  unfold slotMass
  by_cases hi : i ∈ S g
  · simp only [hi, ite_true, mul_inv]
    rw [← mul_sum]
    have h : ∑ p ∈ P g, (p : ℝ)⁻¹ = harmonicMass (P g) := by simp [harmonicMass]
    rw [h]
    exact inv_mul_cancel₀ (hV g)
  · simp [hi]

/-- The mass of the labels equal to `p` in the slots `R ⊆ S g₀` is `μ_{g₀}(p)^{|R|}`. -/
lemma sum_labelMass_mul_prod_ite {P : ι → Finset ℕ} (hV : ∀ g, harmonicMass (P g) ≠ 0)
    (S : ι → Finset (Fin J)) {g₀ : ι} {R : Finset (Fin J)} (hR : R ⊆ S g₀) {p : ℕ}
    (hp : p ∈ P g₀) :
    ∑ a ∈ auxLabels P S, labelMass P S a * ∏ i ∈ R, (if a g₀ i = p then 1 else 0) =
      (harmonicMass (P g₀) * p)⁻¹ ^ R.card := by
  set e : ι → Fin J → ℕ → ℝ := fun g i v =>
    if g = g₀ ∧ i ∈ R then (if v = p then 1 else 0) else 1
  have hprod : ∀ a : ι → Fin J → ℕ,
      ∏ i ∈ R, (if a g₀ i = p then (1 : ℝ) else 0) = ∏ g, ∏ i, e g i (a g i) := by
    intro a
    rw [Fintype.prod_eq_single g₀ fun g hg => prod_eq_one fun i _ => by simp [e, hg]]
    rw [← Fintype.prod_ite_mem R]
    exact prod_congr rfl fun i _ => by by_cases hi : i ∈ R <;> simp [e, hi]
  simp_rw [hprod, labelMass_eq_prod, ← prod_mul_distrib]
  rw [sum_auxLabels_prod P S fun g i v => slotMass P S g i v * e g i v]
  rw [Fintype.prod_eq_single g₀ fun g hg => prod_eq_one fun i _ => by
    simp only [e, hg, false_and, ite_false, mul_one]; exact sum_slotMass hV S g i]
  rw [← prod_const, ← Fintype.prod_ite_mem R]
  refine prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ R
  · simp only [hi, ite_true, e, and_self, mul_ite, mul_one, mul_zero]
    rw [ite_eq_left (hR hi), sum_ite_eq' (P g₀) p, ite_eq_left hp, slotMass, ite_eq_left (hR hi)]
  · simp only [hi, ite_false, e, and_false, mul_one]
    exact sum_slotMass hV S g₀ i

/-- The mass of the labels satisfying `Q` in one slot `i₀ ∈ S g₀`. -/
lemma sum_labelMass_mul_ite {P : ι → Finset ℕ} (hV : ∀ g, harmonicMass (P g) ≠ 0)
    (S : ι → Finset (Fin J)) {g₀ : ι} {i₀ : Fin J} (hi₀ : i₀ ∈ S g₀) (Q : ℕ → Prop)
    [DecidablePred Q] :
    ∑ a ∈ auxLabels P S, labelMass P S a * (if Q (a g₀ i₀) then 1 else 0) =
      ∑ p ∈ (P g₀).filter Q, (harmonicMass (P g₀) * p)⁻¹ := by
  have hsplit : ∀ a ∈ auxLabels P S, (if Q (a g₀ i₀) then (1 : ℝ) else 0) =
      ∑ p ∈ (P g₀).filter Q, ∏ i ∈ {i₀}, (if a g₀ i = p then 1 else 0) := by
    intro a ha
    have hmem : a g₀ i₀ ∈ P g₀ := by
      have := mem_auxLabels.1 ha g₀ i₀
      rwa [ite_eq_left hi₀] at this
    simp only [prod_singleton]
    rw [sum_ite_eq]
    by_cases hQ : Q (a g₀ i₀)
    · rw [ite_eq_left hQ, ite_eq_left (mem_filter.2 ⟨hmem, hQ⟩)]
    · rw [ite_eq_right hQ, ite_eq_right fun h => hQ (mem_filter.1 h).2]
  rw [sum_congr rfl fun a ha => by rw [hsplit a ha], sum_congr rfl fun a _ => mul_sum _ _ _,
    sum_comm]
  refine sum_congr rfl fun p hp => ?_
  rw [sum_labelMass_mul_prod_ite hV S (singleton_subset_iff.2 hi₀) (mem_filter.1 hp).1,
    card_singleton, pow_one]

/-- The mass of the labels coinciding in two slots `i₀ ≠ j₀` of `S g₀`. -/
lemma sum_labelMass_mul_ite_eq {P : ι → Finset ℕ} (hV : ∀ g, harmonicMass (P g) ≠ 0)
    (S : ι → Finset (Fin J)) {g₀ : ι} {i₀ j₀ : Fin J} (hi₀ : i₀ ∈ S g₀) (hj₀ : j₀ ∈ S g₀)
    (hij : i₀ ≠ j₀) :
    ∑ a ∈ auxLabels P S, labelMass P S a * (if a g₀ i₀ = a g₀ j₀ then 1 else 0) =
      ∑ p ∈ P g₀, (harmonicMass (P g₀) * p)⁻¹ ^ 2 := by
  have hsplit : ∀ a ∈ auxLabels P S, (if a g₀ i₀ = a g₀ j₀ then (1 : ℝ) else 0) =
      ∑ p ∈ P g₀, ∏ i ∈ {i₀, j₀}, (if a g₀ i = p then 1 else 0) := by
    intro a ha
    have hmem : a g₀ j₀ ∈ P g₀ := by
      have := mem_auxLabels.1 ha g₀ j₀
      rwa [ite_eq_left hj₀] at this
    simp only [prod_pair hij, mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq, ite_eq_left hmem]
  rw [sum_congr rfl fun a ha => by rw [hsplit a ha], sum_congr rfl fun a _ => mul_sum _ _ _,
    sum_comm]
  refine sum_congr rfl fun p hp => ?_
  rw [sum_labelMass_mul_prod_ite hV S (by
    intro i hi
    rcases mem_insert.1 hi with rfl | hi
    · exact hi₀
    · rw [mem_singleton.1 hi]; exact hj₀) hp, card_pair hij]

end Restore

end Erdos408.TwoSided
