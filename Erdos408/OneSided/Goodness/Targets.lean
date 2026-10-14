module

public import Erdos408.OneSided.Cauchy
public import Erdos408.OneSided.Decomposition.Lists
public import Erdos408.OneSided.Decomposition.Pair
public import Erdos408.OneSided.Goodness.RootBox
public import Erdos408.OneSided.Pairing.Geometry

/-!
# The targets of a source

The edge counts of `eventually_badMass_le` (`blueprint/one_sided_type_ii.md` §14, PD
`mem:neighbor`).

* `norm_rowOp_le`: an entry of `𝒯` is at most `∏ V_i^{-1} ([t = b - a] + 4 L^{3A₀}/Y)` on its
  support `RowEdge`: the cutoffs, `d₀/D` and the damping are at most one.
* `card_det_le`: a source has at most `17 (10Y + 1)` target positions `Q` with
  `D ∣ det(P, Q)` and `|det(P, Q)/D| < 5Y`: `Q` is fixed by `det(P, Q)` and `⌊Q₁/P₁⌋ ≤ 16`.
* `card_lists_dvd_le`: the target lists at a position `Q` with given pads number at most
  `(log₂ Q₁)^K`, since their last labels divide `Q₁`.
* `card_pairs_le`: the pairs `(P, Q)` with `G ∣ P₁`, `a ∣ Q₁` and `det(P, Q) = z` inject into
  `(P, k)` with `0 ≤ k ≤ 16`: `Q₁ = z c + (k - ⌊z r⌋) P₁` for the root `c` of `P`. This is the
  input of `exists_card_cong_le`.
* `squarefree_listProd_mul`: the labels of a source and the new labels of a target are
  distinct primes, so their product is squarefree.
-/

@[expose] public section

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

/-! ### The support of `𝒯` -/

/-- The support of `𝒯` from `(P, p)` to `(Q, p')`: the pads are copied, the new labels avoid
the source labels, `D ∈ [d₀, 2d₀)` divides `det(P, Q)`, `|det(P, Q)/D| < 5Y`, and the last
products `b` and `a` lie in `(Y, 4Y)`. -/
def RowEdge (Y d₀ : ℝ) {J : ℕ} (P : ℕ × ℕ) (p : Lists K J) (Q : ℕ × ℕ) (p' : Lists K J) :
    Prop :=
  (∀ i (h : Fin J), p' i h.castSucc = p i h.castSucc) ∧
    (∀ i i' h', p' i (Fin.last J) ≠ p i' h') ∧
    d₀ ≤ (padProd p : ℝ) ∧ (padProd p : ℝ) < 2 * d₀ ∧ (padProd p : ℤ) ∣ det P Q ∧
    |((det P Q / padProd p : ℤ) : ℝ)| < 5 * Y ∧
    Y < (lastProd p : ℝ) ∧ (lastProd p : ℝ) < 4 * Y ∧
    Y < (lastProd p' : ℝ) ∧ (lastProd p' : ℝ) < 4 * Y

/-- The raw condition `det(P, Q)/D = b - a`. -/
def RawEdge {J : ℕ} (P : ℕ × ℕ) (p : Lists K J) (Q : ℕ × ℕ) (p' : Lists K J) : Prop :=
  det P Q / padProd p = (lastProd p : ℤ) - lastProd p'

/-- A state has at least `K M` band primes in `P₁`: its labels. -/
theorem le_bandCount {x : ℝ} {d : Data K} {Y d₀ : ℝ} (s : State x d Y d₀) :
    K * (padCount x + 1) ≤ bandCount x d s.1.1.1 := by
  obtain ⟨-, hband, hinj, hdvd⟩ := state_props s
  unfold bandCount
  have h : ∀ i, padCount x + 1 ≤ primeCount (band x (d.a i)) s.1.1.1 := by
    intro i
    unfold primeCount
    have hsub : univ.image (s.1.2 i) ⊆ (band x (d.a i)).filter (· ∣ s.1.1.1) := by
      intro r hr
      obtain ⟨h, -, rfl⟩ := mem_image.1 hr
      exact mem_filter.2 ⟨hband i h, hdvd i h⟩
    have := card_le_card hsub
    rwa [card_image_of_injective _ (hinj i), card_univ, Fintype.card_fin] at this
  calc K * (padCount x + 1) = ∑ _i : Fin K, (padCount x + 1) := by
        rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ _ := sum_le_sum fun i _ => h i

open scoped Classical in
/-- An entry of `𝒯` is at most `∏ V_i^{-1} ([t = b - a] + 4 L^{3A₀}/Y)` on its support, and
zero off it. -/
theorem norm_rowOp_le {q A₀ x : ℝ} (hq : 0 < q) (hq₁ : q ≤ 1) (hL : 0 < Real.log x)
    {d : Data K} (hV : 0 < d.bandMass x) {Y d₀ : ℝ} (hY : 0 < Y) (hd₀ : 0 < d₀)
    (s s' : State x d Y d₀) :
    ‖rowOp q A₀ x d Y d₀ s s'‖ ≤
      if RowEdge Y d₀ s.1.1 s.1.2 s'.1.1 s'.1.2 then
        (d.bandMass x)⁻¹ * ((if RawEdge s.1.1 s.1.2 s'.1.1 s'.1.2 then 1 else 0) +
          4 * Real.log x ^ (3 * A₀) / Y)
      else 0 := by
  by_cases h0 : rowOp q A₀ x d Y d₀ s s' = 0
  · rw [h0, norm_zero]
    split_ifs <;> positivity
  have hne := h0
  obtain ⟨hD₁, hD₂, hdvd, hηb, hψ⟩ := rowOp_ne_zero hne
  unfold rowOp at h0
  rw [ite_eq_right_iff, not_forall] at h0
  obtain ⟨hc, h0⟩ := h0
  set D := padProd s.1.2
  set t := det s.1.1 s'.1.1 / D
  have hD0 : (0 : ℝ) < D := hd₀.trans_le hD₁
  have hηa : dyadicBump (lastProd s'.1.2 / Y) ≠ 0 := by
    intro h
    apply h0
    rw [h]
    simp
  have hb := lt_of_dyadicBump_ne_zero hηb
  have ha := lt_of_dyadicBump_ne_zero hηa
  rw [one_lt_div hY, div_lt_iff₀ hY] at hb ha
  have ht : |(t : ℝ)| < 5 * Y := by
    have := abs_lt_of_plateau_ne_zero hψ
    rwa [abs_div, abs_of_pos hY, div_lt_iff₀ hY] at this
  have hedge : RowEdge Y d₀ s.1.1 s.1.2 s'.1.1 s'.1.2 :=
    ⟨hc.1, hc.2.1, hD₁, hD₂, hdvd, ht, hb.1, by linarith, ha.1, by linarith⟩
  rw [ite_eq_left hedge]
  unfold rowOp
  rw [ite_eq_left hc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  -- the real factor is at most `∏ V_i^{-1}`
  have hdamp : 0 ≤ ((bandCount x d s.1.1.1 : ℝ) - K * (padCount x + 1)) / 2 +
      ((bandCount x d s'.1.1.1 : ℝ) - K * (padCount x + 1)) / 2 := by
    have h₁ : (K * (padCount x + 1) : ℝ) ≤ bandCount x d s.1.1.1 := by
      exact_mod_cast le_bandCount s
    have h₂ : (K * (padCount x + 1) : ℝ) ≤ bandCount x d s'.1.1.1 := by
      exact_mod_cast le_bandCount s'
    linarith
  have hreal : |(d.bandMass x)⁻¹ * (d₀ / D) * dyadicBump (lastProd s.1.2 / Y) *
      dyadicBump (lastProd s'.1.2 / Y) * plateau ((t : ℝ) / Y) *
      q ^ (((bandCount x d s.1.1.1 : ℝ) - K * (padCount x + 1)) / 2 +
        ((bandCount x d s'.1.1.1 : ℝ) - K * (padCount x + 1)) / 2)| ≤ (d.bandMass x)⁻¹ := by
    have hW : 0 ≤ (d.bandMass x)⁻¹ := inv_nonneg.2 hV.le
    have hdD : d₀ / D ≤ 1 := (div_le_one hD0).2 hD₁
    have hψ0 : 0 ≤ plateau ((t : ℝ) / Y) := smoothTransition.nonneg _
    have hψ1 : plateau ((t : ℝ) / Y) ≤ 1 := smoothTransition.le_one _
    have hq0 := Real.rpow_nonneg hq.le (((bandCount x d s.1.1.1 : ℝ) - K * (padCount x + 1)) / 2 +
        ((bandCount x d s'.1.1.1 : ℝ) - K * (padCount x + 1)) / 2)
    have hq1 := Real.rpow_le_one hq.le hq₁ hdamp
    have hb0 := dyadicBump_nonneg (lastProd s.1.2 / Y)
    have hb1 := dyadicBump_le_one (lastProd s.1.2 / Y)
    have ha0 := dyadicBump_nonneg (lastProd s'.1.2 / Y)
    have ha1 := dyadicBump_le_one (lastProd s'.1.2 / Y)
    rw [abs_of_nonneg (by positivity)]
    calc (d.bandMass x)⁻¹ * (d₀ / D) * dyadicBump (lastProd s.1.2 / Y) *
          dyadicBump (lastProd s'.1.2 / Y) * plateau ((t : ℝ) / Y) *
          q ^ (((bandCount x d s.1.1.1 : ℝ) - K * (padCount x + 1)) / 2 +
            ((bandCount x d s'.1.1.1 : ℝ) - K * (padCount x + 1)) / 2)
        ≤ (d.bandMass x)⁻¹ * 1 * 1 * 1 * 1 * 1 := by gcongr
      _ = (d.bandMass x)⁻¹ := by ring
  have hkernel : ‖(if t = (lastProd s.1.2 : ℤ) - lastProd s'.1.2 then (1 : ℂ) else 0) -
      arcIntegral A₀ x Y (t - lastProd s.1.2 + lastProd s'.1.2)‖ ≤
        (if RawEdge s.1.1 s.1.2 s'.1.1 s'.1.2 then 1 else 0) + 4 * Real.log x ^ (3 * A₀) / Y := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_arcIntegral_le A₀ hL hY _))
    unfold RawEdge
    split_ifs <;> simp
  exact mul_le_mul hreal hkernel (norm_nonneg _) (inv_nonneg.2 hV.le)

/-! ### Target positions -/

/-- A source `P` has at most `17 (10Y + 1)` target positions `Q` with `D ∣ det(P, Q)` and
`|det(P, Q)/D| < 5Y`: `Q ↦ (det(P, Q)/D, ⌊Q₁/P₁⌋)` is injective, since `det(P, Q)` fixes
`Q₁ mod P₁` and then `Q₂`. -/
theorem card_det_le {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) {P : ℕ × ℕ} (hP : U ≤ P.1)
    (hP0 : 0 < P.1) (hcop : Nat.Coprime P.1 P.2) (D : ℕ) {Y : ℝ} (hY : 0 ≤ Y) :
    (#{Q ∈ rootBox U V | (D : ℤ) ∣ det P Q ∧ |((det P Q / D : ℤ) : ℝ)| < 5 * Y} : ℝ) ≤
      17 * (10 * Y + 1) := by
  set m := ⌊5 * Y⌋₊
  set F : Finset (ℕ × ℕ) :=
    {Q ∈ rootBox U V | (D : ℤ) ∣ det P Q ∧ |((det P Q / D : ℤ) : ℝ)| < 5 * Y}
  set f : ℕ × ℕ → ℤ × ℕ := fun Q => (det P Q / D, Q.1 / P.1)
  have hmaps : ∀ Q ∈ F,
      f Q ∈ Icc (-(m : ℤ)) m ×ˢ range 17 := by
    intro Q hQ
    obtain ⟨hbox, -, ht⟩ := mem_filter.1 hQ
    have hQ1 := (mem_rootBox_bounds hU hV hbox).2.1
    simp only [f]
    rw [mem_product, mem_Icc, mem_range]
    have habs : (det P Q / D).natAbs ≤ m := by
      refine Nat.le_floor ?_
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact ht.le
    refine ⟨⟨by omega, by omega⟩, Nat.lt_succ_of_le (Nat.div_le_of_le_mul ?_)⟩
    have : (Q.1 : ℝ) ≤ P.1 * 16 := by linarith
    exact_mod_cast this
  have hinj : Set.InjOn f F := by
    intro Q hQ Q' hQ' hf
    obtain ⟨-, hdvd, -⟩ := mem_filter.1 (mem_coe.1 hQ)
    obtain ⟨-, hdvd', -⟩ := mem_filter.1 (mem_coe.1 hQ')
    have ht : det P Q / D = det P Q' / D := congrArg Prod.fst hf
    have hq : Q.1 / P.1 = Q'.1 / P.1 := congrArg Prod.snd hf
    have hdet : det P Q = det P Q' := by
      rw [← Int.mul_ediv_cancel' hdvd, ← Int.mul_ediv_cancel' hdvd', ht]
    unfold det at hdet
    -- `P₁ ∣ Q₁ - Q₁'`, and `Q₁, Q₁'` have the same quotient by `P₁`
    have hdvd₁ : (P.1 : ℤ) ∣ P.2 * ((Q.1 : ℤ) - Q'.1) := ⟨Q.2 - Q'.2, by linear_combination -hdet⟩
    have hdvd₂ : (P.1 : ℤ) ∣ (Q.1 : ℤ) - Q'.1 :=
      (Int.isCoprime_iff_gcd_eq_one.2 (by exact_mod_cast hcop)).dvd_of_dvd_mul_left hdvd₁
    have h₁ : Q.1 = Q'.1 := by
      have e₁ := Nat.div_add_mod Q.1 P.1
      have e₂ := Nat.div_add_mod Q'.1 P.1
      have hm₁ := Nat.mod_lt Q.1 hP0
      have hm₂ := Nat.mod_lt Q'.1 hP0
      obtain ⟨w, hw⟩ := hdvd₂
      have hw' : ((Q.1 % P.1 : ℕ) : ℤ) - (Q'.1 % P.1 : ℕ) = P.1 * w := by
        rw [← hw, hq] at *
        push_cast
        omega
      have : w = 0 := by
        by_contra hw0
        have : (P.1 : ℤ) ≤ |(P.1 : ℤ) * w| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hw0)
        rw [← hw'] at this
        have h₁ : ((Q.1 % P.1 : ℕ) : ℤ) < P.1 := by exact_mod_cast hm₁
        have h₂ : ((Q'.1 % P.1 : ℕ) : ℤ) < P.1 := by exact_mod_cast hm₂
        have h₃ : |((Q.1 % P.1 : ℕ) : ℤ) - (Q'.1 % P.1 : ℕ)| < P.1 :=
          abs_sub_lt_iff.2 ⟨by linarith [Int.natCast_nonneg (Q'.1 % P.1)],
            by linarith [Int.natCast_nonneg (Q.1 % P.1)]⟩
        linarith
      rw [this, mul_zero] at hw
      omega
    have h₂ : Q.2 = Q'.2 := by
      rw [h₁] at hdet
      have : (P.1 : ℤ) * Q.2 = P.1 * Q'.2 := by linarith
      exact_mod_cast mul_left_cancel₀ (by positivity : (P.1 : ℤ) ≠ 0) this
    exact Prod.ext h₁ h₂
  have hm : (m : ℝ) ≤ 5 * Y := Nat.floor_le (by positivity)
  calc (F.card : ℝ)
      ≤ ((Icc (-(m : ℤ)) m ×ˢ range 17).card : ℝ) := by
        exact_mod_cast card_le_card_of_injOn f hmaps hinj
    _ = (2 * m + 1) * 17 := by
        rw [card_product, card_range, Int.card_Icc]
        push_cast
        rw [show ((m : ℤ) + 1 - -(m : ℤ)).toNat = 2 * m + 1 by omega]
        push_cast
        ring
    _ ≤ 17 * (10 * Y + 1) := by linarith

/-! ### Target lists -/

/-- At most `log₂ n` primes divide `n ≠ 0`: their product divides `n`. -/
theorem card_primeFactors_le_log {n : ℕ} (hn : n ≠ 0) : n.primeFactors.card ≤ Nat.log 2 n := by
  refine Nat.le_log_of_pow_le one_lt_two ?_
  calc 2 ^ n.primeFactors.card ≤ ∏ r ∈ n.primeFactors, r :=
        pow_card_le_prod _ _ _ fun r hr => (Nat.prime_of_mem_primeFactors hr).two_le
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

/-- The lists with the pads of `p` whose last labels are primes dividing `n ≠ 0` number at
most `(log₂ n)^K`: they are fixed by their last labels. -/
theorem card_lists_dvd_le {x : ℝ} {d : Data K} {J : ℕ} (p : Lists K J) {n : ℕ} (hn : n ≠ 0) :
    #{p' ∈ lists x d J | (∀ i (h : Fin J), p' i h.castSucc = p i h.castSucc) ∧
      ∀ i, p' i (Fin.last J) ∣ n} ≤ Nat.log 2 n ^ K := by
  set F : Finset (Lists K J) :=
    {p' ∈ lists x d J | (∀ i (h : Fin J), p' i h.castSucc = p i h.castSucc) ∧
      ∀ i, p' i (Fin.last J) ∣ n}
  set f : Lists K J → Fin K → ℕ := fun p' i => p' i (Fin.last J)
  have hmaps : ∀ p' ∈ F, f p' ∈ Fintype.piFinset fun _ : Fin K => n.primeFactors := by
    intro p' hp'
    obtain ⟨hl, -, hdvd⟩ := mem_filter.1 hp'
    refine Fintype.mem_piFinset.2 fun i => Nat.mem_primeFactors.2 ⟨?_, hdvd i, hn⟩
    exact (mem_filter.1 (lists_slot_mem_band hl i _)).2
  have hinj : Set.InjOn f F := by
    intro p₁ hp₁ p₂ hp₂ hf
    obtain ⟨-, h₁, -⟩ := mem_filter.1 (mem_coe.1 hp₁)
    obtain ⟨-, h₂, -⟩ := mem_filter.1 (mem_coe.1 hp₂)
    funext i h
    refine Fin.lastCases ?_ (fun h => ?_) h
    · exact congrFun hf i
    · rw [h₁, h₂]
  calc _ ≤ (Fintype.piFinset fun _ : Fin K => n.primeFactors).card :=
        card_le_card_of_injOn f hmaps hinj
    _ = n.primeFactors.card ^ K := by
        rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
    _ ≤ Nat.log 2 n ^ K := Nat.pow_le_pow_left (card_primeFactors_le_log hn) K

/-! ### Pairs with a fixed determinant -/

/-- With `c` the root of `P`, `P₁ ∣ Q₁ - det(P, Q) c`. -/
theorem dvd_sub_det_mul_rootC {P Q : ℕ × ℕ} (hP0 : 0 < P.1) (hcop : Nat.Coprime P.1 P.2) :
    (P.1 : ℤ) ∣ Q.1 - det P Q * rootC P.1 P.2 := by
  obtain ⟨w, hw⟩ := RootResidue.dvd_rootC_mul_add_one hP0 hcop
  refine ⟨Q.1 * w - Q.2 * rootC P.1 P.2, ?_⟩
  have hw' : ((rootC P.1 P.2 : ℕ) : ℤ) * P.2 + 1 = P.1 * w := by exact_mod_cast hw
  unfold det
  linear_combination (Q.1 : ℤ) * hw'

/-- The pairs `(P, Q)` of the box with `G ∣ P₁`, `a ∣ Q₁`, `det(P, Q) = z` and `B P` inject into
the `(P, k)` with `0 ≤ k ≤ 16`, `G ∣ P₁`, `a ∣ z c + (k - ⌊z r⌋) P₁` and `B P`:
`Q₁ = z c + (k - ⌊z r⌋) P₁` with `Q₁/P₁ = z r + k - ⌊z r⌋ ∈ (0, 16]`. -/
theorem card_pairs_le {U V : ℝ} (hU : 0 < U) (hV : 0 ≤ V) (G a : ℕ) (z : ℤ)
    (B : ℕ × ℕ → Prop) [DecidablePred B] :
    #{PQ ∈ rootBox U V ×ˢ rootBox U V | (G : ℤ) ∣ PQ.1.1 ∧ (a : ℤ) ∣ PQ.2.1 ∧
        det PQ.1 PQ.2 = z ∧ B PQ.1} ≤
      ∑ k ∈ range 17, #{P ∈ rootBox U V | ((G : ℤ) ∣ P.1 ∧
        (a : ℤ) ∣ z * rootC P.1 P.2 + ((k : ℤ) - ⌊(z : ℝ) * rootRatio P⌋) * P.1) ∧ B P} := by
  set Φ : ℕ → ℕ × ℕ → Prop := fun k P => ((G : ℤ) ∣ P.1 ∧
    (a : ℤ) ∣ z * rootC P.1 P.2 + ((k : ℤ) - ⌊(z : ℝ) * rootRatio P⌋) * P.1) ∧ B P
  set k : (ℕ × ℕ) × (ℕ × ℕ) → ℕ := fun PQ =>
    (((PQ.2.1 : ℤ) - z * rootC PQ.1.1 PQ.1.2) / PQ.1.1 + ⌊(z : ℝ) * rootRatio PQ.1⌋).toNat
  set f : (ℕ × ℕ) × (ℕ × ℕ) → (ℕ × ℕ) × ℕ := fun PQ => (PQ.1, k PQ)
  set F : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    {PQ ∈ rootBox U V ×ˢ rootBox U V | (G : ℤ) ∣ PQ.1.1 ∧ (a : ℤ) ∣ PQ.2.1 ∧
      det PQ.1 PQ.2 = z ∧ B PQ.1}
  set T := (rootBox U V ×ˢ range 17).filter fun Pk => Φ Pk.2 Pk.1
  -- the quotient `z₁ = (Q₁ - z c)/P₁` and its shift `k ∈ [0, 16]`
  have hkey : ∀ PQ ∈ F,
      ((k PQ : ℕ) : ℤ) = ((PQ.2.1 : ℤ) - z * rootC PQ.1.1 PQ.1.2) / PQ.1.1 +
        ⌊(z : ℝ) * rootRatio PQ.1⌋ ∧ k PQ < 17 ∧
      (PQ.2.1 : ℤ) =
        z * rootC PQ.1.1 PQ.1.2 + ((k PQ : ℤ) - ⌊(z : ℝ) * rootRatio PQ.1⌋) * PQ.1.1 := by
    intro PQ hPQ
    obtain ⟨hmem, -, -, hz, -⟩ := mem_filter.1 hPQ
    obtain ⟨hP, hQ⟩ := mem_product.1 hmem
    obtain ⟨hP1, -, -, -, hcop⟩ := mem_rootBox_bounds hU.le hV hP
    obtain ⟨hQ1, hQ16, -, -, -⟩ := mem_rootBox_bounds hU.le hV hQ
    have hP0 : 0 < PQ.1.1 := by exact_mod_cast hU.trans_le hP1
    have hP0' : (0 : ℝ) < PQ.1.1 := by exact_mod_cast hP0
    set z₁ := ((PQ.2.1 : ℤ) - z * rootC PQ.1.1 PQ.1.2) / PQ.1.1
    have hdvd := dvd_sub_det_mul_rootC (Q := PQ.2) hP0 hcop
    rw [hz] at hdvd
    have hQ : (PQ.2.1 : ℤ) = z * rootC PQ.1.1 PQ.1.2 + z₁ * PQ.1.1 := by
      have := Int.ediv_mul_cancel hdvd
      linarith
    -- `Q₁/P₁ = z r + z₁`
    have hQr : (PQ.2.1 : ℝ) / PQ.1.1 = z * rootRatio PQ.1 + z₁ := by
      rw [rootRatio_eq]
      have : (PQ.2.1 : ℝ) = z * rootC PQ.1.1 PQ.1.2 + z₁ * PQ.1.1 := by exact_mod_cast hQ
      rw [this]
      field_simp
    have hlo : 0 < (PQ.2.1 : ℝ) / PQ.1.1 := div_pos (by linarith) hP0'
    have hhi : (PQ.2.1 : ℝ) / PQ.1.1 ≤ 16 := by
      rw [div_le_iff₀ hP0']
      linarith
    have hfl := Int.floor_le ((z : ℝ) * rootRatio PQ.1)
    have hfl' := Int.lt_floor_add_one ((z : ℝ) * rootRatio PQ.1)
    have h0 : 0 ≤ z₁ + ⌊(z : ℝ) * rootRatio PQ.1⌋ := by
      have : (-1 : ℝ) < z₁ + ⌊(z : ℝ) * rootRatio PQ.1⌋ := by linarith
      have : (-1 : ℤ) < z₁ + ⌊(z : ℝ) * rootRatio PQ.1⌋ := by exact_mod_cast this
      omega
    have h16 : z₁ + ⌊(z : ℝ) * rootRatio PQ.1⌋ ≤ 16 := by
      have : ((z₁ + ⌊(z : ℝ) * rootRatio PQ.1⌋ : ℤ) : ℝ) ≤ 16 := by push_cast; linarith
      exact_mod_cast this
    have hk : ((k PQ : ℕ) : ℤ) = z₁ + ⌊(z : ℝ) * rootRatio PQ.1⌋ := Int.toNat_of_nonneg h0
    refine ⟨hk, by omega, ?_⟩
    rw [hk, hQ]
    ring
  have hmaps : ∀ PQ ∈ F, f PQ ∈ T := by
    intro PQ hPQ
    obtain ⟨-, hk17, hQ⟩ := hkey PQ hPQ
    obtain ⟨hmem, hG, ha, -, hB⟩ := mem_filter.1 hPQ
    refine mem_filter.2 ⟨mem_product.2 ⟨(mem_product.1 hmem).1, mem_range.2 hk17⟩, ⟨hG, ?_⟩, hB⟩
    rw [← hQ]
    exact ha
  have hinj : Set.InjOn f F := by
    intro PQ hPQ PQ' hPQ' hf
    have hP : PQ.1 = PQ'.1 := (Prod.ext_iff.1 hf).1
    have hk : k PQ = k PQ' := (Prod.ext_iff.1 hf).2
    obtain ⟨-, -, hQ⟩ := hkey PQ hPQ
    obtain ⟨-, -, hQ'⟩ := hkey PQ' hPQ'
    obtain ⟨hmem, -, -, hz, -⟩ := mem_filter.1 (mem_coe.1 hPQ)
    obtain ⟨-, -, -, hz', -⟩ := mem_filter.1 (mem_coe.1 hPQ')
    have hP0 : 0 < PQ.1.1 := by
      have := (mem_rootBox_bounds hU.le hV (mem_product.1 hmem).1).1
      exact_mod_cast hU.trans_le this
    have h₁ : PQ.2.1 = PQ'.2.1 := by
      rw [← hP, ← hk] at hQ'
      exact_mod_cast hQ.trans hQ'.symm
    have h₂ : PQ.2.2 = PQ'.2.2 := by
      unfold det at hz hz'
      rw [← hP, ← h₁] at hz'
      have : (PQ.1.1 : ℤ) * PQ.2.2 = PQ.1.1 * PQ'.2.2 := by linarith
      exact_mod_cast mul_left_cancel₀ (by positivity : (PQ.1.1 : ℤ) ≠ 0) this
    exact Prod.ext hP (Prod.ext h₁ h₂)
  have hT : T.card = ∑ k ∈ range 17, #{P ∈ rootBox U V | Φ k P} := by
    rw [card_filter, sum_product, sum_comm]
    exact sum_congr rfl fun k _ => (card_filter _ _).symm
  exact (card_le_card_of_injOn f hmaps hinj).trans hT.le

/-! ### Squarefree products of labels -/

/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod_of_injective {ι : Type*} [Fintype ι] {f : ι → ℕ}
    (hf : Function.Injective f) (hp : ∀ i, (f i).Prime) : Squarefree (∏ i, f i) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun i _ j _ hij => ?_)
    fun i _ => (hp i).prime.squarefree
  exact Nat.coprime_iff_isRelPrime.1 ((Nat.coprime_primes (hp i) (hp j)).2 (hf.ne hij))

/-- The labels of a source and the new labels of a target are distinct primes, so
`G a = listProd p · lastProd p'` is squarefree. -/
theorem squarefree_listProd_mul_lastProd {x : ℝ} {d : Data K}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) {J : ℕ}
    {p p' : Lists K J} (hp : p ∈ lists x d J) (hp' : p' ∈ lists x d J)
    (hban : ∀ i i' h', p' i (Fin.last J) ≠ p i' h') :
    Squarefree (listProd p * lastProd p') := by
  set f : (Fin K × Fin (J + 1)) ⊕ Fin K → ℕ :=
    Sum.elim (fun ih => p ih.1 ih.2) fun i => p' i (Fin.last J)
  have hf : Function.Injective f := by
    have hinj := label_injective hdisj (fun i h => lists_slot_mem_band hp i h)
      (lists_group_injective hp)
    rintro (⟨i, h⟩ | i) (⟨i', h'⟩ | i') heq
    · exact congrArg Sum.inl (hinj heq)
    · exact absurd heq.symm (hban i' i h)
    · exact absurd heq (hban i i' h')
    · simp only [f, Sum.elim_inr] at heq
      by_contra hne
      have hii : i ≠ i' := fun h => hne (congrArg Sum.inr h)
      exact disjoint_left.1 (hdisj i i' hii) (lists_slot_mem_band hp' i _)
        (heq ▸ lists_slot_mem_band hp' i' _)
  have hprime : ∀ e, (f e).Prime := by
    rintro (⟨i, h⟩ | i)
    · exact (mem_filter.1 (lists_slot_mem_band hp i h)).2
    · exact (mem_filter.1 (lists_slot_mem_band hp' i _)).2
  have := squarefree_prod_of_injective hf hprime
  rwa [Fintype.prod_sum_type, Fintype.prod_prod_type] at this

end Erdos408.OneSided
