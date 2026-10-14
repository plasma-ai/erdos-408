import Erdos821.P3Rare.Sectors

set_option autoImplicit false

/-! The exact rare-transfer task `Erdos821.S2Core.MemoryRareTask`. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Rare

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

theorem memoryRareTask_holds (F : FixedData) (r : MemoryParameters F) :
    MemoryRareTask F r := by
  classical
  intro m C₁
  obtain ⟨Cprom, _hCprom_pos, hCprom⟩ :=
    Erdos821.P3Edge.promo_allmaps_bound r.rho r.rho_pos r.rho_lt (F.ell + m)
  obtain ⟨Csmall0, hCsmall0_pos, hCsmall0⟩ :=
    Erdos821.P3Edge.small_count_damp F.q F.q_pos F.q_lt F.ell
  have hCb_ge : 1 ≤ Erdos821.P3Edge.bigGroupConst F r m Cprom :=
    Erdos821.P3Edge.bigGroupConst_ge_one F r m Cprom
  have hCcol_ge : 1 ≤ Erdos821.P3Edge.colRevConst F m :=
    Erdos821.P3Edge.colRevConst_ge_one F m
  have hCs_ge : 1 ≤ max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0) := le_max_left _ _
  -- Group constants of the product of the row and column constants.
  let CB2 : ℝ := Erdos821.P3Edge.colRevConst F m *
    Erdos821.P3Edge.bigGroupConst F r m Cprom *
    Erdos821.P3Edge.bigGroupConst F r m Cprom
  let CS2 : ℝ := max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0) *
    max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)
  have hCB2_ge : 1 ≤ CB2 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hCcol_ge hCb_ge) hCb_ge
  have hCS2_ge : 1 ≤ CS2 := one_le_mul_of_one_le_of_one_le hCs_ge hCs_ge
  let Kbig : ℝ := F.C₀ * Real.log CB2
  let Ksmall : ℝ := F.C₀ * Real.log CS2
  have hKbig_nn : 0 ≤ Kbig := mul_nonneg F.C₀_pos.le (Real.log_nonneg hCB2_ge)
  have hKsmall_nn : 0 ≤ Ksmall := mul_nonneg F.C₀_pos.le (Real.log_nonneg hCS2_ge)
  refine ⟨C₁ + Kbig + Ksmall, fun J C₂ => ?_⟩
  obtain ⟨xp, hxp⟩ := promotionContextBadOmission_card_le_eventually F C₂ J m
  obtain ⟨xs, hxs⟩ := storeOnlyContextBadOmission_card_le_eventually F C₂ J m
  let xfact : ℝ := 10 * ((Erdos821.P3Edge.taylorTerms F).factorial : ℝ)
  refine ⟨max (max 3 (Real.exp xfact)) (max xp xs), ?_⟩
  intro x hx P hP A hA hk0 hk theta i phi hphi
  have hx_base : max 3 (Real.exp xfact) ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_max_left _ _) hx_base
  have hxexp : Real.exp xfact ≤ x := le_trans (le_max_right _ _) hx_base
  have hxps : max xp xs ≤ x := le_trans (le_max_right _ _) hx
  have hxp' : x ≥ xp := le_trans (le_max_left _ _) hxps
  have hxs' : x ≥ xs := le_trans (le_max_right _ _) hxps
  have hL1 : 1 < L x := Erdos821.P3Edge.one_lt_L hx3
  have hLpos : 0 < L x := lt_trans zero_lt_one hL1
  have hx1 : 1 ≤ L x := hL1.le
  have hL10 : 10 * ((Erdos821.P3Edge.taylorTerms F).factorial : ℝ) ≤ L x := by
    have hlog := Real.log_le_log (Real.exp_pos _) hxexp
    rwa [Real.log_exp] at hlog
  have hVlo : ∀ g : P.Group, F.vMin ≤ P.V g := fun g => (hP.2.2.2.2.1 g).1
  have hVhi : ∀ g : P.Group, P.V g ≤ F.vMax := fun g => (hP.2.2.2.2.1 g).2
  have hVpos : ∀ g : P.Group, 0 < P.V g := fun g => Erdos821.P3Edge.V_pos_of_adm hP g
  have hVne : ∀ g : P.Group, P.V g ≠ 0 := fun g => ne_of_gt (hVpos g)
  have htilted_nn : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      0 ≤ tiltedMu F P (N x) g.val p :=
    fun g p => (Erdos821.P3Edge.tiltedMu_pos hx1 hP (N x) rfl hL10 g p).le
  have htilted_sum : ∀ g : P.BigGroup, ∑ p : P.Prime g.val, tiltedMu F P (N x) g.val p ≤ 2 :=
    fun g => Erdos821.P3Edge.tiltedMu_sum_le_two hx1 hP (N x) rfl hL10 g
  have hcard_big : ((Fintype.card P.BigGroup : ℕ) : ℝ) ≤ F.C₀ * Real.log (L x) := by
    have hle : (P.bigGroups.card : ℝ) ≤ F.C₀ * T x := hP.2.2.2.1
    have hcard_eq : (Fintype.card P.BigGroup : ℝ) = (P.bigGroups.card : ℝ) := by
      rw [PrimeGroups.bigGroups]
      simp [Fintype.card_subtype]
    rw [hcard_eq]
    exact hle
  have hcard_small : ((Fintype.card P.SmallGroup : ℕ) : ℝ) ≤ F.C₀ * Real.log (L x) := by
    have hle : (P.smallGroups.card : ℝ) ≤ F.C₀ * T x := hP.2.1
    have hcard_eq : (Fintype.card P.SmallGroup : ℝ) = (P.smallGroups.card : ℝ) := by
      rw [PrimeGroups.smallGroups]
      simp [Fintype.card_subtype]
    rw [hcard_eq]
    exact hle
  have hbig_pow : CB2 ^ Fintype.card P.BigGroup ≤ (L x) ^ Kbig :=
    Erdos821.P3Edge.pow_groups_le_rpow CB2 (lt_of_lt_of_le zero_lt_one hCB2_ge) _
      F.C₀ (L x) Kbig F.C₀_pos hL1 hKbig_nn (le_refl _) hcard_big
  have hsmall_pow : CS2 ^ Fintype.card P.SmallGroup ≤ (L x) ^ Ksmall :=
    Erdos821.P3Edge.pow_groups_le_rpow CS2 (lt_of_lt_of_le zero_lt_one hCS2_ge) _
      F.C₀ (L x) Ksmall F.C₀_pos hL1 hKsmall_nn (le_refl _) hcard_small
  -- Context constants.
  let Gr : ℝ := Erdos821.P3Edge.bigGroupConst F r m Cprom ^ Fintype.card P.BigGroup *
    (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^ Fintype.card P.SmallGroup
  let Gc : ℝ := Erdos821.P3Edge.colRevConst F m ^ Fintype.card P.BigGroup *
    Erdos821.P3Edge.bigGroupConst F r m Cprom ^ Fintype.card P.BigGroup *
    (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^ Fintype.card P.SmallGroup
  have hGr : 1 ≤ Gr :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCb_ge) (one_le_pow₀ hCs_ge)
  have hGc : 1 ≤ Gc :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCcol_ge) (one_le_pow₀ hCb_ge))
      (one_le_pow₀ hCs_ge)
  have hGG : Gr * Gc = CB2 ^ Fintype.card P.BigGroup * CS2 ^ Fintype.card P.SmallGroup := by
    simp only [Gr, Gc, CB2, CS2, mul_pow]
    ring
  let BP : ℝ := (Fintype.card (P.BigPermutations (J + F.ell)) : ℝ)
  have hBP : 0 < BP := by
    have : Nonempty (P.BigPermutations (J + F.ell)) := ⟨fun _ => Equiv.refl _⟩
    exact Nat.cast_pos.mpr Fintype.card_pos
  have haux : ∀ (v : Fin A.patternCount) (u : P.Aux J), 0 ≤ (A.pattern v).auxMass u := by
    intro v u
    unfold Pattern.auxMass
    apply Finset.prod_nonneg
    intro g _
    apply Finset.prod_nonneg
    intro j _
    exact (Erdos821.P3Edge.mu_pos_of_V_pos g (hVpos g) (u g j)).le
  let a : EdgeTransferContext A → ℝ := fun ctx =>
    Erdos821.P3Edge.patternSup A ctx.1 * (A.pattern ctx.1).auxMass ctx.2.1 / BP
  have ha : ∀ ctx, 0 ≤ a ctx := fun ctx =>
    div_nonneg (mul_nonneg (Erdos821.P3Edge.patternSup_nonneg A ctx.1)
      (haux ctx.1 ctx.2.1)) hBP.le
  let R : EdgeTransferContext A → ℝ := fun ctx => a ctx * Gr
  let C : EdgeTransferContext A → ℝ := fun ctx => a ctx * Gc
  have hR : ∀ ctx, 0 ≤ R ctx := fun ctx => mul_nonneg (ha ctx) (by linarith)
  have hC : ∀ ctx, 0 ≤ C ctx := fun ctx => mul_nonneg (ha ctx) (by linarith)
  let keep : P.MemoryState (J + F.ell) → Prop := fun s => P.memorySize s ≤ memoryCutoff x
  have hm : ∀ s : P.MemoryState (J + F.ell), 0 ≤ P.memoryMass F J (N x) s := fun s =>
    Erdos821.P3Edge.memoryMass_nonneg F J (N x) hVpos htilted_nn s
  have hw : ∀ s : P.MemoryState (J + F.ell), 0 < P.memoryWeight r.v s := fun s => Erdos821.P3Edge.memoryWeight_pos r s
  let Ωc : ℝ := (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ)
  have hΩ : Ωc = (omissionNumber F P J : ℝ) := by
    simp only [Ωc]
    rw [omissionChoices_card_eq_number]
  have hΩpos : 0 < Ωc := by
    rw [hΩ]
    unfold omissionNumber
    exact_mod_cast pow_pos (Nat.choose_pos (Nat.le_add_left _ _)) _
  -- Promotion sector.
  have hprom := promotionOmissionAverage_projectedNormBound' A r theta i keep
    (P.memoryMass F J (N x)) (P.memoryWeight r.v) R C (memoryCutoff x) hm hw hΩpos hR hC
    (by
      intro ctx O s T
      have h := promotionContextKernel_rowCost_le A r theta i ctx O s T hVlo hVpos
        htilted_nn htilted_sum Cprom Csmall0 hCsmall0_pos hCprom hCsmall0
      refine le_trans h (le_of_eq ?_)
      simp only [R, a, Gr, BP]
      ring)
    (by
      intro ctx O t S
      have h := promotionContextKernel_columnCost_le A r theta i ctx O t S hVlo hVhi
        htilted_nn htilted_sum Cprom Csmall0 hCsmall0_pos hCprom hCsmall0
      refine le_trans h (le_of_eq ?_)
      simp only [C, a, Gc, BP]
      ring)
    (by
      intro ctx s
      by_cases hs : keep s
      · refine le_trans (Finset.card_le_card ?_) (hxp x hxp' P hP A hk0 hk (N x) i ctx s hs)
        intro O hO
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hO ⊢
        exact hO.2
      · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
        refine Finset.card_eq_zero.mpr ?_
        ext O
        simp [hs])
  -- Store-only sector.
  have hstore := storeOnlyOmissionAverage_projectedNormBound' A r theta i keep
    (P.memoryMass F J (N x)) (P.memoryWeight r.v) R C (memoryCutoff x) hm hw hΩpos hR hC
    (by
      intro ctx O s T
      have h := storeOnlyContextKernel_rowCost_le A r theta i ctx O s T hVlo hVpos
        htilted_nn htilted_sum Cprom Csmall0 hCsmall0_pos hCprom hCsmall0
      refine le_trans h (le_of_eq ?_)
      simp only [R, a, Gr, BP]
      ring)
    (by
      intro ctx O t S
      have h := storeOnlyContextKernel_columnCost_le A r theta i ctx O t S hVlo hVhi
        htilted_nn htilted_sum Cprom Csmall0 hCsmall0_pos hCprom hCsmall0
      refine le_trans h (le_of_eq ?_)
      simp only [C, a, Gc, BP]
      ring)
    (by
      intro ctx t
      by_cases ht : keep t
      · refine le_trans (Finset.card_le_card ?_) (hxs x hxs' P hP A hk0 hk (N x) i ctx t ht)
        intro O hO
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hO ⊢
        exact hO.2
      · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
        refine Finset.card_eq_zero.mpr ?_
        ext O
        simp [ht])
  have hdirty := normBound_projected_dirty_of_sectorBounds A r.rho theta i phi hphi
    (P.memoryMass F J (N x)) keep _ _ hm hprom hstore
  -- Evaluate the context constants.
  let X : ℝ := Real.sqrt (Gr * Gc * ((memoryCutoff x : ℝ) / Ωc))
  have hsqrtP : ∀ ctx, Real.sqrt ((R ctx * ((memoryCutoff x : ℝ) / Ωc)) * C ctx) =
      a ctx * X := by
    intro ctx
    have e : (R ctx * ((memoryCutoff x : ℝ) / Ωc)) * C ctx =
        (a ctx) ^ 2 * (Gr * Gc * ((memoryCutoff x : ℝ) / Ωc)) := by
      simp only [R, C]
      ring
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (ha ctx)]
  have hsqrtS : ∀ ctx, Real.sqrt (R ctx * (C ctx * ((memoryCutoff x : ℝ) / Ωc))) =
      a ctx * X := by
    intro ctx
    have e : R ctx * (C ctx * ((memoryCutoff x : ℝ) / Ωc)) =
        (a ctx) ^ 2 * (Gr * Gc * ((memoryCutoff x : ℝ) / Ωc)) := by
      simp only [R, C]
      ring
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (ha ctx)]
  have hsum_a : ∑ ctx, a ctx = A.patternMass := by
    rw [← Erdos821.P3Edge.sum_patternSup_eq]
    change ∑ ctx : Fin A.patternCount × P.Aux J × P.BigPermutations (J + F.ell),
        Erdos821.P3Edge.patternSup A ctx.1 * (A.pattern ctx.1).auxMass ctx.2.1 / BP = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro v _
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have e : ∀ u : P.Aux J,
        (Fintype.card (P.BigPermutations (J + F.ell)) : ℝ) *
          (Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u / BP) =
        Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u := by
      intro u
      change BP * (Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u / BP) = _
      field_simp
    simp_rw [e]
    rw [← Finset.mul_sum, Erdos821.P3Edge.auxMass_sum_eq_one (A.pattern v) hVne, mul_one]
  have hconstP : (∑ ctx : EdgeTransferContext A,
      Real.sqrt ((R ctx * ((memoryCutoff x : ℝ) / Ωc)) * C ctx)) = A.patternMass * X := by
    simp_rw [hsqrtP]
    rw [← Finset.sum_mul, hsum_a]
  have hconstS : (∑ ctx : EdgeTransferContext A,
      Real.sqrt (R ctx * (C ctx * ((memoryCutoff x : ℝ) / Ωc)))) = A.patternMass * X := by
    simp_rw [hsqrtS]
    rw [← Finset.sum_mul, hsum_a]
  -- The power of `L(x)`.
  have hGG1 : 1 ≤ Gr * Gc := one_le_mul_of_one_le_of_one_le hGr hGc
  have hsqrtGG : Real.sqrt (Gr * Gc) ≤ (L x) ^ Kbig * (L x) ^ Ksmall := by
    have h1 : Real.sqrt (Gr * Gc) ≤ Gr * Gc := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    calc Real.sqrt (Gr * Gc) ≤ Gr * Gc := h1
      _ = CB2 ^ Fintype.card P.BigGroup * CS2 ^ Fintype.card P.SmallGroup := hGG
      _ ≤ (L x) ^ Kbig * (L x) ^ Ksmall :=
        mul_le_mul hbig_pow hsmall_pow (pow_nonneg (by linarith) _)
          (Real.rpow_nonneg hLpos.le _)
  have hX : X = Real.sqrt (Gr * Gc) * Real.sqrt ((memoryCutoff x : ℝ) / Ωc) := by
    simp only [X]
    rw [Real.sqrt_mul (by linarith)]
  have hpm0 : 0 ≤ A.patternMass := Erdos821.P3Edge.patternMass_nonneg A
  have hmain : A.patternMass * X ≤
      (L x) ^ (C₁ + Kbig + Ksmall) *
        Real.sqrt ((memoryCutoff x : ℝ) / (omissionNumber F P J : ℝ)) := by
    rw [hX, ← hΩ, Real.rpow_add hLpos, Real.rpow_add hLpos]
    have hs0 : 0 ≤ Real.sqrt ((memoryCutoff x : ℝ) / Ωc) := Real.sqrt_nonneg _
    have hq0 : 0 ≤ Real.sqrt (Gr * Gc) := Real.sqrt_nonneg _
    calc A.patternMass * (Real.sqrt (Gr * Gc) * Real.sqrt ((memoryCutoff x : ℝ) / Ωc))
        = (A.patternMass * Real.sqrt (Gr * Gc)) * Real.sqrt ((memoryCutoff x : ℝ) / Ωc) := by
          ring
      _ ≤ ((L x) ^ C₁ * ((L x) ^ Kbig * (L x) ^ Ksmall)) *
            Real.sqrt ((memoryCutoff x : ℝ) / Ωc) := by
          apply mul_le_mul_of_nonneg_right _ hs0
          exact mul_le_mul hA hsqrtGG hq0 (Real.rpow_nonneg hLpos.le _)
      _ = (L x) ^ C₁ * (L x) ^ Kbig * (L x) ^ Ksmall *
            Real.sqrt ((memoryCutoff x : ℝ) / Ωc) := by ring
  rw [hconstP, hconstS] at hdirty
  refine normBound_mono' hdirty ?_
  linarith

end Erdos821.P3Rare

open Erdos821.Blueprint.Graph Erdos821.S2Core in
theorem Erdos821.S2Core.MemoryRareTask_proof (F : FixedData) (r : MemoryParameters F) :
    Erdos821.S2Core.MemoryRareTask F r :=
  Erdos821.P3Rare.memoryRareTask_holds F r

open Erdos821.Blueprint.Graph in
example (F : FixedData) (r : MemoryParameters F) : Erdos821.S2Core.MemoryRareTask F r :=
  Erdos821.S2Core.MemoryRareTask_proof F r

