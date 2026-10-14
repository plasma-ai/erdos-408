module

public import Erdos408.OneSided.Moment.Phased.Edge
public import Erdos408.OneSided.Moment.Phased.Rows

/-!
# Edge rows with prescribed births

PD `mem:edge-atoms`: an edge row with prescribed fresh labels. Fix all labels first; the
targets then contribute the kernel bound of `sum_crudeKernel_le` uniformly in the labels. A
group whose label is prescribed to be the fresh prime `p` contributes the atom `ν(p)`, and a
free group contributes `∑_p (2 S(p, ·) + ν(p)) ≤ 2B + 4`.

* `memSize_chainEdgeOut_le`: an edge stores at most `K` particles, so the memory grows by at
  most `K`.
* `sum_chainEdge_pres_le`: the weighted row sums of the edge against the prescription
  indicators `∏_i [β_i = π_i]` of its labels, with weight `v₀^{size}`, are at most
  `v₀^K 2^K (2B + 4)^K 16 (1 + 52 L^{3A₀}) ∏_i atomCost(π_i) v₀^{size}`.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

section EdgeAtoms

variable {q A₀ x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- An edge stores at most `K` particles: the memory after the edge has size at most the size
before it plus `K`. -/
theorem memSize_chainEdgeOut_le (s : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r) :
    memSize (chainEdgeOut x d Y d₀ u v r B s c).2.2.1 ≤ memSize s.2.2.1 + K := by
  classical
  unfold chainEdgeOut
  split_ifs with hv
  · -- removals only decrease the size, and the stored particles number at most `|S| ≤ K`
    change memSize (edgeMem s c) ≤ _
    have hstored : ∑ xp : Particle x d, (c.2.1.filter fun i => edgeStored s c i = xp.1).card ≤
        K := by
      simp only [card_filter]
      rw [sum_comm]
      calc ∑ i ∈ c.2.1, ∑ xp : Particle x d, (if edgeStored s c i = xp.1 then 1 else 0)
          ≤ ∑ _i ∈ c.2.1, 1 := sum_le_sum fun i _ => by
            rw [← card_filter]
            exact card_le_one.2 fun a ha b hb =>
              Subtype.ext ((mem_filter.1 ha).2.symm.trans (mem_filter.1 hb).2)
        _ = c.2.1.card := by simp
        _ ≤ K := card_le_univ _ |>.trans_eq (Fintype.card_fin K)
    calc memSize (edgeMem s c)
        ≤ ∑ xp : Particle x d,
            (s.2.2.1 xp + (c.2.1.filter fun i => edgeStored s c i = xp.1).card) :=
          sum_le_sum fun xp _ => by unfold edgeMem; omega
      _ ≤ memSize s.2.2.1 + K := by
          rw [sum_add_distrib]
          exact Nat.add_le_add_left hstored _
  · exact Nat.le_add_right _ _

/-- **The edge rows with prescribed labels** (PD `mem:edge-atoms`): with weight `v₀^{size}`,
the absolute edge coefficients against `∏_i [β_i = π_i]` sum to at most
`v₀^K 2^K (2B + 4)^K 16 (1 + 52 L^{3A₀}) ∏_i atomCost(π_i)` times the weight of the source. A
group prescribed to the prime `p` is a fresh draw of `p`, of weight `ν(p)`. -/
theorem sum_chainEdge_pres_le (hq : 0 < q) (hq₁ : q < 1) (hd₀ : 0 < d₀) (hY : 1 ≤ Y)
    (hU : 0 < d₀ * Y * d.Hm) (hL : 0 < Real.log x) (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνi : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 4)
    (hV : ∀ i, ∀ p ∈ band x (d.a i), 1 / 2 ≤ primeMass x d p) {v₀ c₀ : ℝ} (hv₀ : 1 ≤ v₀)
    (hc₀ : 1 ≤ c₀) (π : Fin K → Option ℕ) (s : ChainState x d Y d₀ u v r B) :
    ∑ c ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ *
        (∏ i, presInd (π i) (if (c.2.2.2.1 i).2 then none else some (c.2.2.2.1 i).1)) *
        v₀ ^ memSize (chainEdgeOut x d Y d₀ u v r B s c).2.2.1 ≤
      v₀ ^ K * 2 ^ K * (2 * B + 4) ^ K * (16 * (1 + 52 * Real.log x ^ (3 * A₀))) *
        (∏ i, atomCost c₀ (primeWeight q x d N) (π i)) * v₀ ^ memSize s.2.2.1 := by
  classical
  set M := padCount x with hM
  set r₀ := (((M + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 with hr₀
  set Kz := 16 * (1 + 52 * Real.log x ^ (3 * A₀)) with hKz
  set ω : ℕ × Bool → ℝ := fun pf =>
    if pf.2 then 2 * primeMult x d s.2.2.1 pf.1 else primeWeight q x d N pf.1 with hω
  set β : ℕ × Bool → Option ℕ := fun pf => if pf.2 then none else some pf.1 with hβ
  set Dσ : (Fin K → Equiv.Perm (Fin (M + 1))) → ℕ :=
    fun σ => ∏ i, ∏ h : Fin M, s.2.1.1 i (σ i h.castSucc) with hDσ
  set bσ : (Fin K → Equiv.Perm (Fin (M + 1))) → ℕ :=
    fun σ => ∏ i, s.2.1.1 i (σ i (Fin.last M)) with hbσ
  set F : (Fin K → Equiv.Perm (Fin (M + 1))) → ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) →
      (Fin K → ℕ × Bool) → ℝ := fun σ z' lab =>
    r₀ * (∏ i, ω (lab i) * presInd (π i) (β (lab i))) *
      crudeKernel A₀ x Y (Dσ σ) (bσ σ) (∏ i, (lab i).1)
        (s.1.1.1 * z'.1.2 - s.1.1.2 * z'.1.1) with hF
  set W := v₀ ^ K * v₀ ^ memSize s.2.2.1 with hWdef
  have hv0 : 0 ≤ v₀ := by linarith
  have hW0 : 0 ≤ W := by positivity
  have hr0 : 0 ≤ r₀ := by positivity
  have hω0 : ∀ pf, 0 ≤ ω pf := fun pf => by
    simp only [hω]
    split_ifs
    exacts [mul_nonneg (by norm_num) (primeMult_nonneg _ _), hν _]
  have hD0 : ∀ σ, 0 < Dσ σ := fun σ =>
    prod_pos fun i _ => prod_pos fun h _ =>
      (TypeII.band_prime (mem_band_of_mem_lists s.2.1.2 i _)).pos
  -- the pointwise bound
  have hpt : ∀ c ∈ edgeChoices x d Y d₀ u v r,
      ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ *
          (∏ i, presInd (π i) (β (c.2.2.2.1 i))) *
          v₀ ^ memSize (chainEdgeOut x d Y d₀ u v r B s c).2.2.1 ≤
        W * F c.1 c.2.2.1 c.2.2.2.1 := by
    intro c hc
    have hpres0 : 0 ≤ ∏ i, presInd (π i) (β (c.2.2.2.1 i)) :=
      prod_nonneg fun i _ => presInd_nonneg _ _
    -- the crude weight is at most `∏_i ω`
    have hwt : crudeWeight q x d Y d₀ u v r B N s c ≤ ∏ i, ω (c.2.2.2.1 i) := by
      refine prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
      · split_ifs
        · exact div_nonneg (sum_nonneg fun xp _ => by split_ifs <;> positivity)
            (sum_nonneg fun i _ => by
              split_ifs
              · exact sum_nonneg fun p _ => by positivity
              · exact le_rfl)
        · exact hν _
      · have hVi := hV i _ (mem_band_of_mem_edgeChoices hc i)
        simp only [hω]
        split_ifs with hf
        · have hnum : (∑ xp : Particle x d,
              if xp.1 = edgePromoted c i then (s.2.2.1 xp : ℝ) else 0) ≤
                primeMult x d s.2.2.1 (c.2.2.2.1 i).1 := by
            refine sum_le_sum fun xp _ => ?_
            split_ifs with h₁ h₂ h₂
            · exact le_rfl
            · exact absurd (congrArg Prod.fst h₁) h₂
            · positivity
            · exact le_rfl
          rw [div_le_iff₀ (by linarith)]
          have hm0 := primeMult_nonneg s.2.2.1 (c.2.2.2.1 i).1
          calc (∑ xp : Particle x d,
                if xp.1 = edgePromoted c i then (s.2.2.1 xp : ℝ) else 0)
              ≤ primeMult x d s.2.2.1 (c.2.2.2.1 i).1 := hnum
            _ ≤ 2 * primeMult x d s.2.2.1 (c.2.2.2.1 i).1 * (1 / 2) := by linarith
            _ ≤ 2 * primeMult x d s.2.2.1 (c.2.2.2.1 i).1 * primeMass x d (c.2.2.2.1 i).1 :=
                mul_le_mul_of_nonneg_left hVi (by linarith)
        · exact le_rfl
    have hcoef := (norm_chainEdgeCoef_le_crude (A₀ := A₀) hq hq₁ hd₀ hν s c).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwt hr0)
        (crudeKernel_nonneg _ _ _ _ _ _ _))
    have hsize : v₀ ^ memSize (chainEdgeOut x d Y d₀ u v r B s c).2.2.1 ≤ W := by
      rw [hWdef, ← pow_add, add_comm]
      exact pow_le_pow_right₀ hv₀ (memSize_chainEdgeOut_le s c)
    calc ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ *
          (∏ i, presInd (π i) (β (c.2.2.2.1 i))) *
          v₀ ^ memSize (chainEdgeOut x d Y d₀ u v r B s c).2.2.1
        ≤ r₀ * (∏ i, ω (c.2.2.2.1 i)) *
            crudeKernel A₀ x Y (edgePad s c) (∏ i, edgeSrc s c i (Fin.last _))
              (∏ i, (c.2.2.2.1 i).1) (edgeDet s c) *
            (∏ i, presInd (π i) (β (c.2.2.2.1 i))) * W :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcoef hpres0) hsize (pow_nonneg hv0 _)
            (mul_nonneg (mul_nonneg (mul_nonneg hr0 (prod_nonneg fun i _ => hω0 _))
              (crudeKernel_nonneg _ _ _ _ _ _ _)) hpres0)
      _ = W * F c.1 c.2.2.1 c.2.2.2.1 := by
          have hD : edgePad s c = Dσ c.1 := rfl
          have hb : ∏ i, edgeSrc s c i (Fin.last _) = bσ c.1 := rfl
          have hdet : edgeDet s c = s.1.1.1 * c.2.2.1.1.2 - s.1.1.2 * c.2.2.1.1.1 := rfl
          rw [hD, hb, hdet]
          simp only [hF, prod_mul_distrib]
          ring
  -- each label sum is at most `(2B + 4) atomCost(π_i)`
  have hlab : ∀ i, ∑ pf ∈ band x (d.a i) ×ˢ (univ : Finset Bool),
      ω pf * presInd (π i) (β pf) ≤ (2 * B + 4) * atomCost c₀ (primeWeight q x d N) (π i) := by
    intro i
    cases hπ : π i with
    | none =>
      simp only [presInd_none, mul_one, atomCost, Option.elim]
      rw [sum_product]
      simp only [Fintype.sum_bool, hω, ite_true, Bool.false_eq_true, ite_false, sum_add_distrib,
        ← mul_sum]
      have h₁ := sum_primeMult_le s.2.2.1 (band x (d.a i))
      have h₂ : (memSize s.2.2.1 : ℝ) ≤ B := by exact_mod_cast mem_memStates.1 s.2.2.2
      linarith [hνi i]
    | some p =>
      -- only the fresh draw of `p` survives
      simp only [presInd_some, atomCost, Option.elim]
      rw [sum_product]
      simp only [Fintype.sum_bool, hβ, ite_true, Bool.false_eq_true, ite_false,
        reduceCtorEq, mul_zero, Option.some.injEq, hω, zero_add, mul_ite, mul_one,
        sum_ite_eq']
      have h1 : (1 : ℝ) ≤ (2 * B + 4) * c₀ :=
        one_le_mul_of_one_le_of_one_le (by linarith [(B.cast_nonneg : (0 : ℝ) ≤ B)]) hc₀
      calc (if p ∈ band x (d.a i) then primeWeight q x d N p else 0)
          ≤ primeWeight q x d N p := by
            split_ifs
            exacts [le_rfl, hν p]
        _ ≤ (2 * B + 4) * c₀ * primeWeight q x d N p := le_mul_of_one_le_left (hν p) h1
        _ = (2 * B + 4) * (c₀ * primeWeight q x d N p) := mul_assoc _ _ _
  -- the inner sum over the target, the labels and `σ'`
  have hinner : ∀ σ, ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
      ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i) ×ˢ (univ : Finset Bool)),
        ∑ _σ' : Fin K → Equiv.Perm (Fin (M + 1)), F σ z' lab ≤
          (((M + 1).factorial ^ K : ℕ) : ℝ) * (r₀ * ((2 * B + 4) ^ K * Kz *
            ∏ i, atomCost c₀ (primeWeight q x d N) (π i))) := by
    intro σ
    have hcard : (Fintype.card (Fin K → Equiv.Perm (Fin (M + 1))) : ℝ) =
        (((M + 1).factorial ^ K : ℕ) : ℝ) := by
      simp [Fintype.card_perm]
    simp only [sum_const, card_univ, nsmul_eq_mul, hcard]
    rw [sum_comm]
    simp only [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i) ×ˢ (univ : Finset Bool)),
          ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), F σ z' lab
        ≤ ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i) ×ˢ (univ : Finset Bool)),
            r₀ * (∏ i, ω (lab i) * presInd (π i) (β (lab i))) * Kz := by
          refine sum_le_sum fun lab _ => ?_
          simp only [hF, ← mul_sum]
          exact mul_le_mul_of_nonneg_left
            (sum_crudeKernel_le A₀ hL hY hU s.1.2 (hD0 σ) _ _)
            (mul_nonneg hr0 (prod_nonneg fun i _ =>
              mul_nonneg (hω0 _) (presInd_nonneg _ _)))
      _ = r₀ * Kz * ∏ i, ∑ pf ∈ band x (d.a i) ×ˢ (univ : Finset Bool),
            ω pf * presInd (π i) (β pf) := by
          rw [prod_univ_sum, mul_sum]
          exact sum_congr rfl fun lab _ => by ring
      _ ≤ r₀ * Kz * ∏ i, ((2 * (B : ℝ) + 4) * atomCost c₀ (primeWeight q x d N) (π i)) :=
          mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun i _ => sum_nonneg fun pf _ =>
            mul_nonneg (hω0 pf) (presInd_nonneg _ _)) fun i _ => hlab i)
            (mul_nonneg hr0 (by positivity))
      _ = r₀ * ((2 * B + 4) ^ K * Kz * ∏ i, atomCost c₀ (primeWeight q x d N) (π i)) := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
          ring
  calc ∑ c ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ *
        (∏ i, presInd (π i) (if (c.2.2.2.1 i).2 then none else some (c.2.2.2.1 i).1)) *
        v₀ ^ memSize (chainEdgeOut x d Y d₀ u v r B s c).2.2.1
      ≤ ∑ c ∈ edgeChoices x d Y d₀ u v r, W * F c.1 c.2.2.1 c.2.2.2.1 := sum_le_sum hpt
    _ = W * ∑ σ : Fin K → Equiv.Perm (Fin (M + 1)), ∑ _st : Finset (Fin K),
          ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
            ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i) ×ˢ (univ : Finset Bool)),
              ∑ _σ' : Fin K → Equiv.Perm (Fin (M + 1)), F σ z' lab := by
        rw [← mul_sum]
        simp only [edgeChoices, sum_product]
        rfl
    _ ≤ W * ∑ _σ : Fin K → Equiv.Perm (Fin (M + 1)), ∑ _st : Finset (Fin K),
          (((M + 1).factorial ^ K : ℕ) : ℝ) * (r₀ * ((2 * B + 4) ^ K * Kz *
            ∏ i, atomCost c₀ (primeWeight q x d N) (π i))) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun σ _ => sum_le_sum fun _ _ => hinner σ) hW0
    _ = v₀ ^ K * 2 ^ K * (2 * B + 4) ^ K * Kz *
          (∏ i, atomCost c₀ (primeWeight q x d N) (π i)) * v₀ ^ memSize s.2.2.1 := by
        have hf : (((M + 1).factorial ^ K : ℕ) : ℝ) ≠ 0 := by positivity
        simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_finset, Fintype.card_fin,
          hr₀, hWdef]
        rw [show (Fintype.card (Fin K → Equiv.Perm (Fin (M + 1))) : ℝ) =
          (((M + 1).factorial ^ K : ℕ) : ℝ) by simp [Fintype.card_perm]]
        field_simp
        push_cast
        ring

end EdgeAtoms

end Erdos408.OneSided
