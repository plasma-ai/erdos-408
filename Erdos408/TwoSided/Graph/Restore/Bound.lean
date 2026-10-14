module

public import Erdos408.TwoSided.Graph.Restore.Clean

/-!
# Absolute bounds on the summands

The absolute summand of `blueprint/two_sided_correlation.md` §4.4: in every case, collision or
not, the summands at `(a, s, w)` of the cutoff pairing after G4 and of the stripped
correlation, summed over the unshared parts `l, l'`, are at most
`μ(s) μ(a) T² κ_K M₀ L_F L_G Λ(n) Λ(n') / w` at the endpoints `n, n'` (`D_R w, D_R (w + D_C)`,
resp. `w, w + D_C`). Here `T = ∏_g V_g^{-t_g}` and `Λ(n) = q₀^{ω(n) - M s} · #lists(n)` keeps
each damping with its list count (`listWeight`).
-/

@[expose] public section

namespace Erdos408.TwoSided

namespace Restore

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ}

/-- The number of unshared parts whose labels divide `n`. -/
noncomputable def listCount (P : ι → Finset ℕ) (C : ι → Finset (Fin J)) (n : ℕ) : ℕ :=
  ((unsharedLists P C).filter fun l => ∀ g, ∀ j ∈ unsharedSlots C g, l g j ∣ n).card

/-- `T = ∏_g V_g^{-t_g}`. -/
noncomputable def targetMass (P : ι → Finset ℕ) (C : ι → Finset (Fin J)) : ℝ :=
  ∏ g, (harmonicMass (P g))⁻¹ ^ (unsharedSlots C g).card

/-- `Λ(n) = q₀^{ω(n) - M s} · #lists(n)`, `M = J + 1`. -/
noncomputable def listWeight (P : ι → Finset ℕ) (q₀ : ℝ) (C : ι → Finset (Fin J)) (n : ℕ) :
    ℝ :=
  q₀ ^ ((groupPrimeCount P n : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) * listCount P C n

omit [DecidableEq ι] in
/-- `T ≥ 0`. -/
lemma targetMass_nonneg {P : ι → Finset ℕ} (hV : ∀ g, 0 < harmonicMass (P g))
    (C : ι → Finset (Fin J)) : 0 ≤ targetMass P C :=
  prod_nonneg fun g _ => pow_nonneg (inv_nonneg.2 (hV g).le) _

/-- `Λ ≥ 0`. -/
lemma listWeight_nonneg (P : ι → Finset ℕ) {q₀ : ℝ} (hq₀ : 0 < q₀) (C : ι → Finset (Fin J))
    (n : ℕ) : 0 ≤ listWeight P q₀ C n :=
  mul_nonneg (zpow_nonneg hq₀.le _) (Nat.cast_nonneg _)

/-- The ℕ-subtracted damping is at most the integer one. -/
private lemma pow_sub_le_zpow {q₀ : ℝ} (hq₀ : 0 < q₀) (hq₀₁ : q₀ ≤ 1) (k M : ℕ) :
    q₀ ^ (k - M) ≤ q₀ ^ ((k : ℤ) - (M : ℕ)) := by
  rw [← zpow_natCast]
  exact zpow_le_zpow_right_of_le_one₀ hq₀ hq₀₁ (by omega)

omit [DecidableEq ι] in
/-- The stripped damping is at most `T q₀^{ω(n) - M s}`. -/
lemma listDamping_le (P : ι → Finset ℕ) {q₀ : ℝ} (hq₀ : 0 < q₀) (hq₀₁ : q₀ ≤ 1)
    (C : ι → Finset (Fin J)) (n : ℕ) :
    listDamping P q₀ C n ≤
      targetMass P C * q₀ ^ ((groupPrimeCount P n : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) := by
  unfold listDamping targetMass
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left (zpow_le_zpow_right_of_le_one₀ hq₀ hq₀₁ ?_)
    (prod_nonneg fun g _ => pow_nonneg (inv_nonneg.2 ?_) _)
  · have h : ∑ g, (unsharedSlots C g).card ≤ (J + 1) * Fintype.card ι := by
      rw [mul_comm, ← smul_eq_mul, ← card_univ, ← sum_const]
      exact sum_le_sum fun g _ => by
        have := card_sharedSlots_add C g
        omega
    have h' : ((∑ g, (unsharedSlots C g).card : ℕ) : ℤ) ≤ ((J + 1) * Fintype.card ι : ℕ) := by
      exact_mod_cast h
    push_cast at h' ⊢
    linarith
  · unfold harmonicMass
    exact sum_nonneg fun p _ => by positivity

omit [DecidableEq ι] in
/-- The stripped damping is nonnegative. -/
lemma listDamping_nonneg (P : ι → Finset ℕ) {q₀ : ℝ} (hq₀ : 0 < q₀)
    (hV : ∀ g, 0 < harmonicMass (P g)) (C : ι → Finset (Fin J)) (n : ℕ) :
    0 ≤ listDamping P q₀ C n :=
  mul_nonneg (zpow_nonneg hq₀.le _) (prod_nonneg fun g _ => pow_nonneg (inv_nonneg.2
    (hV g).le) _)

/-- **The physical summand, absolutely.** -/
lemma norm_physTerm_le {x q₀ : ℝ} {P : ι → Finset ℕ} (hprime : ∀ g, ∀ p ∈ P g, p.Prime)
    (hV : ∀ g, 0 < harmonicMass (P g)) (hq₀ : 0 < q₀) (hq₀₁ : q₀ ≤ 1)
    {C : ι → Finset (Fin J)}
    {K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ} {κK : ℝ}
    (hK : ∀ p p' a, ‖K p p' a‖ ≤ κK) {F G : ℕ → ℝ} {Ψ : ℝ → ℝ} {M₀ LF LG : ℝ}
    (hΨ : ∀ y, |Ψ y| ≤ M₀) (hLF : 0 ≤ LF) (hF : ∀ n, 1 ≤ n → n ≤ ⌊x ^ 2⌋₊ → |F n| ≤ LF)
    (hG : ∀ n, |G n| ≤ LG) {a s : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C))
    {w : ℕ} (hw : 1 ≤ w) (l l' : ι → Fin (J + 1) → ℕ) :
    ‖if sharedProduct C s * w ≤ ⌊x ^ 2⌋₊ then
        physTerm x q₀ P C K F G Ψ (sharedProduct C s * w) (merge C s l) (merge C s l') a
      else 0‖ ≤
      (if ∀ g, ∀ j ∈ unsharedSlots C g, l g j ∣ sharedProduct C s * w then 1 else 0) *
        (if ∀ g, ∀ j ∈ unsharedSlots C g,
            l' g j ∣ sharedProduct C s * (w + slotProduct C a) then 1 else 0) *
        (labelMass P (sharedSlots C) s * labelMass P C a * targetMass P C ^ 2 * κK * M₀ *
          LF * LG / w *
          q₀ ^ ((groupPrimeCount P (sharedProduct C s * w) : ℤ) -
            ((J + 1) * Fintype.card ι : ℕ)) *
          q₀ ^ ((groupPrimeCount P (sharedProduct C s * (w + slotProduct C a)) : ℤ) -
            ((J + 1) * Fintype.card ι : ℕ))) := by
  set DR := sharedProduct C s
  set DC := slotProduct C a
  have hDR : 0 < DR := sharedProduct_pos hprime hs
  have hκ : 0 ≤ κK := (norm_nonneg _).trans (hK (fun _ _ => 0) (fun _ _ => 0) fun _ _ => 0)
  have hM : 0 ≤ M₀ := (abs_nonneg _).trans (hΨ 0)
  have hLG : 0 ≤ LG := (abs_nonneg _).trans (hG 0)
  have hμs := labelMass_nonneg P (sharedSlots C) s
  have hμa := labelMass_nonneg P C a
  have hT := targetMass_nonneg hV C
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hR : 0 ≤ labelMass P (sharedSlots C) s * labelMass P C a * targetMass P C ^ 2 * κK *
      M₀ * LF * LG / w *
      q₀ ^ ((groupPrimeCount P (DR * w) : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) *
      q₀ ^ ((groupPrimeCount P (DR * (w + DC)) : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) :=
    mul_nonneg (mul_nonneg (by positivity) (zpow_nonneg hq₀.le _)) (zpow_nonneg hq₀.le _)
  have hR' : ∀ c d : Prop, [Decidable c] → [Decidable d] →
      0 ≤ (if c then (1 : ℝ) else 0) * (if d then 1 else 0) *
        (labelMass P (sharedSlots C) s * labelMass P C a * targetMass P C ^ 2 * κK *
          M₀ * LF * LG / w *
          q₀ ^ ((groupPrimeCount P (DR * w) : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) *
          q₀ ^ ((groupPrimeCount P (DR * (w + DC)) : ℤ) - ((J + 1) * Fintype.card ι : ℕ))) :=
    fun c d _ _ => mul_nonneg (mul_nonneg (by split_ifs <;> norm_num)
      (by split_ifs <;> norm_num)) hR
  by_cases hN : DR * w ≤ ⌊x ^ 2⌋₊
  · rw [ite_eq_left hN]
    unfold physTerm
    by_cases hc : PhysCond C (DR * w) (merge C s l) (merge C s l') a
    · rw [ite_eq_left hc]
      obtain ⟨h₁, h₂, -⟩ := hc
      have hE : edgeProduct C (merge C s l) a = DR * DC := edgeProduct_merge C s l a
      have hl : ∀ g, ∀ j ∈ unsharedSlots C g, l g j ∣ DR * w := fun g j hj => by
        have := (h₁ g).2 j
        rwa [merge_of_mem hj] at this
      have hl' : ∀ g, ∀ j ∈ unsharedSlots C g, l' g j ∣ DR * (w + DC) := fun g j hj => by
        have := (h₂ g).2 j
        rwa [merge_of_mem hj, hE, ← mul_add] at this
      rw [ite_eq_left hl, ite_eq_left hl', one_mul, one_mul]
      have hLF : |F (DR * w)| ≤ LF :=
        hF _ (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hDR.ne' (by omega))) hN
      unfold physValue
      rw [hE, physWeight_eq hprime hs a, show DR * w + DR * DC = DR * (w + DC) by ring]
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have hW0 : 0 ≤ labelMass P (sharedSlots C) s * DR * labelMass P C a *
          targetMass P C ^ 2 := by positivity
      unfold targetMass at hW0 ⊢
      rw [abs_of_nonneg hW0]
      have hDRw : (0 : ℝ) < ((DR * w : ℕ) : ℝ) := by
        have : 0 < DR * w := Nat.mul_pos hDR hw
        exact_mod_cast this
      have hq₁ := pow_sub_le_zpow hq₀ hq₀₁ (groupPrimeCount P (DR * w))
        ((J + 1) * Fintype.card ι)
      have hq₂ := pow_sub_le_zpow hq₀ hq₀₁ (groupPrimeCount P (DR * (w + DC)))
        ((J + 1) * Fintype.card ι)
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_div, abs_of_pos hDRw,
        abs_of_nonneg (pow_nonneg hq₀.le _), abs_of_nonneg (pow_nonneg hq₀.le _)]
      calc _ ≤ labelMass P (sharedSlots C) s * DR * labelMass P C a *
            (∏ g, (harmonicMass (P g))⁻¹ ^ (unsharedSlots C g).card) ^ 2 * κK *
            (M₀ / ((DR * w : ℕ) : ℝ) * LF * LG *
              q₀ ^ ((groupPrimeCount P (DR * w) : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) *
              q₀ ^ ((groupPrimeCount P (DR * (w + DC)) : ℤ) -
                ((J + 1) * Fintype.card ι : ℕ))) := by
            gcongr
            · exact hK _ _ _
            · exact hΨ _
            · exact hG _
        _ = _ := by
            push_cast
            field_simp
    · rw [ite_eq_right hc, norm_zero]
      exact hR' _ _
  · rw [ite_eq_right hN, norm_zero]
    exact hR' _ _

/-- **The stripped summand, absolutely.** -/
lemma norm_stripTerm_le {x q₀ : ℝ} {P : ι → Finset ℕ} (hV : ∀ g, 0 < harmonicMass (P g))
    (hq₀ : 0 < q₀) (hq₀₁ : q₀ ≤ 1) {C : ι → Finset (Fin J)}
    {K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ} {κK : ℝ}
    (hK : ∀ p p' a, ‖K p p' a‖ ≤ κK) {F G : ℕ → ℝ} {Ψ : ℝ → ℝ} {M₀ LF LG : ℝ}
    (hΨ : ∀ y, |Ψ y| ≤ M₀) (hLF : 0 ≤ LF) (hF : ∀ n, 1 ≤ n → n ≤ ⌊x ^ 2⌋₊ → |F n| ≤ LF)
    (hG : ∀ n, |G n| ≤ LG) (a s : ι → Fin J → ℕ) {w : ℕ} (hw : w ∈ Icc 1 ⌊x ^ 2⌋₊)
    (l l' : ι → Fin (J + 1) → ℕ) :
    ‖stripTerm x q₀ P C K F G Ψ a s l l' w‖ ≤
      (if l ∈ slotLists P (unsharedSlots C) w then 1 else 0) *
        (if l' ∈ slotLists P (unsharedSlots C) (w + slotProduct C a) then 1 else 0) *
        (labelMass P (sharedSlots C) s * labelMass P C a * targetMass P C ^ 2 * κK * M₀ *
          LF * LG / w *
          q₀ ^ ((groupPrimeCount P w : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) *
          q₀ ^ ((groupPrimeCount P (w + slotProduct C a) : ℤ) -
            ((J + 1) * Fintype.card ι : ℕ))) := by
  have hκ : 0 ≤ κK := (norm_nonneg _).trans (hK (fun _ _ => 0) (fun _ _ => 0) fun _ _ => 0)
  have hM : 0 ≤ M₀ := (abs_nonneg _).trans (hΨ 0)
  have hLG : 0 ≤ LG := (abs_nonneg _).trans (hG 0)
  have hμs := labelMass_nonneg P (sharedSlots C) s
  have hμa := labelMass_nonneg P C a
  have hT := targetMass_nonneg hV C
  obtain ⟨hw₁, hwN⟩ := mem_Icc.1 hw
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw₁
  unfold stripTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hl : l ∈ slotLists P (unsharedSlots C) w ∧
      l' ∈ slotLists P (unsharedSlots C) (w + slotProduct C a)
  · rw [ite_eq_left hl, ite_eq_left hl.1, ite_eq_left hl.2, one_mul, one_mul]
    have hd₁ := listDamping_le P hq₀ hq₀₁ C w
    have hd₂ := listDamping_le P hq₀ hq₀₁ C (w + slotProduct C a)
    have hd₁' := listDamping_nonneg P hq₀ hV C w
    have hd₂' := listDamping_nonneg P hq₀ hV C (w + slotProduct C a)
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_div, abs_of_pos hw',
      abs_of_nonneg hμs, abs_of_nonneg hμa, abs_of_nonneg hd₁', abs_of_nonneg hd₂']
    calc _ ≤ labelMass P (sharedSlots C) s * labelMass P C a *
          (M₀ / w * LF * LG *
            ((targetMass P C *
                q₀ ^ ((groupPrimeCount P w : ℤ) - ((J + 1) * Fintype.card ι : ℕ))) *
              (targetMass P C * q₀ ^ ((groupPrimeCount P (w + slotProduct C a) : ℤ) -
                ((J + 1) * Fintype.card ι : ℕ))))) * κK := by
          gcongr
          · exact hΨ _
          · exact hF w hw₁ hwN
          · exact hG _
          · exact hK _ _ _
      _ = _ := by ring
  · rw [ite_eq_right hl, norm_zero, mul_zero]
    refine mul_nonneg (mul_nonneg ?_ ?_) (mul_nonneg (mul_nonneg (by positivity)
      (zpow_nonneg hq₀.le _)) (zpow_nonneg hq₀.le _)) <;> split_ifs <;> norm_num

end Restore

end Erdos408.TwoSided
