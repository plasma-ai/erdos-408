module

public import Erdos408.OneSided.Bands
public import Erdos408.OneSided.Moment.RootReplacement.Bonferroni
public import Erdos408.OneSided.Moment.RootReplacement.Tube

/-!
# The combinatorial budgets of a configuration

The budgets of `blueprint/one_sided_type_ii.md` §5.4 that concern one configuration `ω`,
or the coefficients `c(ω)` together.

* `card_confActive_le`: at most `(N + 1) K (J + 1)` primes are active along a path.
* `eventually_dampMass_le`: the damping mass of the inactive primes is at most `K (N + 1)`.
  For an inactive prime, `1 - λ_p ≤ ∑_j η'_j [ℓ = [z_j]_p]`, whose average is at most
  `(N + 1)/(p + 1)`; and `∑_p 1/p ≤ ∑_i V_i ≤ K`.
* `eventually_sum_norm_confCoeff_le`: the live coefficients have total mass at most
  `exp(L^{0.74})` (the path budget `exp(C_K L^{0.73})` of PD's proof of Lemma 3.4). A live
  path with `c(ω) ≠ 0` stays in the tube `|z| ≤ 2560 N H + 16` (`det:tube`), where
  `H = d₀ Y < (∏ labels)²`. Crudely, each kernel entry is at most
  `|lists|² 2^K (1 + 4 L^{3A₀})`, since a row or column of `𝒮` has total mass at most
  `|lists|` (`norm_confKernel_le`). With `P = exp(L^{1/5})`, the bands have at most `P²`
  primes, all below `P²`, so the count of paths in the tube times the largest coefficient is a
  power `P^Z` with `Z L^{1/5} ≪_K L^{0.71}` (`sum_norm_confCoeff_le_of_bounds`,
  `budget_exponent_le`).
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

/-! ### Elementary facts -/

/-- The lists of a state of the square model are lists of band primes. -/
theorem mem_lists_of_state {x : ℝ} {d : Data K} {Y d₀ : ℝ}
    (s : (squareModel d Y d₀).State x d) : s.1.2 ∈ lists x d (padCount x) := by
  classical
  exact (mem_product.1 (mem_filter.1 s.2).1).2

/-- `1 - ∏ (1 - a_j) ≤ ∑ a_j` for `a_j ∈ [0, 1]`. -/
theorem one_sub_prod_one_sub_le_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h : ∀ j ∈ s, 0 ≤ a j ∧ a j ≤ 1) : 1 - ∏ j ∈ s, (1 - a j) ≤ ∑ j ∈ s, a j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj]
    have hP : ∏ k ∈ s, (1 - a k) ≤ 1 :=
      prod_le_one₀ (fun k hk => by linarith [(h k (mem_insert_of_mem hk)).2])
        fun k hk => by linarith [(h k (mem_insert_of_mem hk)).1]
    have ih' := ih fun k hk => h k (mem_insert_of_mem hk)
    have h₀ := (h j (mem_insert_self j s)).1
    nlinarith [mul_le_mul_of_nonneg_left hP h₀]

/-- A sum of nonnegative terms over a union is at most the sum of the sums. -/
theorem sum_biUnion_le_sum_sum {ι α : Type*} [DecidableEq α] (s : Finset ι)
    (t : ι → Finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [biUnion_insert, sum_insert hi]
    have h := sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := f)
    have h₀ : 0 ≤ ∑ a ∈ t i ∩ s.biUnion t, f a := sum_nonneg fun a _ => hf a
    linarith

/-- The active primes are band primes. -/
theorem confActive_subset {x : ℝ} {d : Data K} {Y d₀ : ℝ} (ω : Conf x d Y d₀) :
    confActive ω ⊆ bandPrimes x d := by
  intro p hp
  simp only [confActive, mem_biUnion, mem_image, mem_univ, true_and] at hp
  obtain ⟨j, i, h, rfl⟩ := hp
  exact mem_biUnion.2 ⟨i, mem_univ _, mem_band_of_mem_lists (mem_lists_of_state (ω j)) i h⟩

/-- At most `(N + 1) K (J + 1)` primes are active along a configuration. -/
theorem card_confActive_le {x : ℝ} {d : Data K} {Y d₀ : ℝ} (ω : Conf x d Y d₀) :
    (confActive ω).card ≤ (2 * momentPower x + 1) * (K * (padCount x + 1)) := by
  unfold confActive
  refine (card_biUnion_le_card_mul _ _ (K * (padCount x + 1)) fun j _ => ?_).trans (by simp)
  refine (card_biUnion_le_card_mul _ _ (padCount x + 1) fun i _ => ?_).trans (by simp)
  exact card_image_le.trans (by simp)

/-- At a prime outside the lists of a configuration, the line factor loses at most `N + 1`
in total over the lines: `1 - λ_p(l) ≤ ∑_j [l = [z_j]_p]`. -/
theorem sum_one_sub_confLineFactor_le {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) {x : ℝ}
    {d : Data K} {Y d₀ : ℝ} (ω : Conf x d Y d₀) {p : ℕ} (hp : p ∉ confActive ω) :
    ∑ l ∈ range (p + 1), (1 - confLineFactor q p ω l) ≤ 2 * momentPower x + 1 := by
  -- step: no visit is active at `p`
  have hact : activeSet p ω = ∅ := by
    refine eq_empty_of_forall_notMem fun j hj => hp ?_
    obtain ⟨j', hj', rfl⟩ := mem_map.1 hj
    obtain ⟨i, h, hih⟩ := (mem_filter.1 hj').2
    simp only [confActive, mem_biUnion, mem_image, mem_univ, true_and]
    exact ⟨j', i, h, hih⟩
  have hlam : ∀ l, 1 - confLineFactor q p ω l ≤
      ∑ j ∈ range (2 * momentPower x + 1),
        if l = confLines p ω j then (1 : ℝ) else 0 := by
    intro l
    unfold confLineFactor
    rw [hact, prod_empty, one_mul, filter_true_of_mem fun j _ => notMem_empty j]
    refine (one_sub_prod_one_sub_le_sum _ _ fun j _ => ?_).trans (sum_le_sum fun j _ => ?_)
    · obtain ⟨h₀, h₁⟩ := dampDefect_mem_Icc hq hq₁ (2 * momentPower x) j
      split_ifs <;> constructor <;> linarith
    · obtain ⟨h₀, h₁⟩ := dampDefect_mem_Icc hq hq₁ (2 * momentPower x) j
      split_ifs <;> linarith
  calc ∑ l ∈ range (p + 1), (1 - confLineFactor q p ω l)
      ≤ ∑ l ∈ range (p + 1), ∑ j ∈ range (2 * momentPower x + 1),
          if l = confLines p ω j then (1 : ℝ) else 0 := sum_le_sum fun l _ => hlam l
    _ = ∑ j ∈ range (2 * momentPower x + 1), ∑ l ∈ range (p + 1),
          if l = confLines p ω j then (1 : ℝ) else 0 := sum_comm
    _ ≤ ∑ j ∈ range (2 * momentPower x + 1), (1 : ℝ) := sum_le_sum fun j _ => by
          rw [sum_ite_eq']
          split_ifs <;> norm_num
    _ = 2 * momentPower x + 1 := by simp

/-- The damping mass of the inactive primes of a configuration is at most `K (N + 1)`,
eventually. -/
theorem eventually_dampMass_le {q alo ahi : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (halo : 1 / 10 < alo) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, (∀ i, alo ≤ d.a i ∧ d.a i ≤ ahi) → ∀ Y d₀ : ℝ,
      ∀ ω : Conf x d Y d₀,
        dampMass x d (confActive ω) (fun p l => confLineFactor q p ω l) ≤
          K * (2 * momentPower x + 1) := by
  filter_upwards [eventually_harmonicMass_band halo.le] with x hx d hd Y d₀ ω
  -- step: each inactive band prime contributes at most `(N + 1) / p`
  have hterm : ∀ p ∈ bandPrimes x d \ confActive ω,
      ((p : ℝ) + 1)⁻¹ * ∑ l ∈ range (p + 1), (1 - confLineFactor q p ω l) ≤
        (2 * momentPower x + 1) * (1 / (p : ℝ)) := by
    intro p hp
    obtain ⟨hpb, hpa⟩ := mem_sdiff.1 hp
    obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hpb
    have hp₀ : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_band hpi).pos
    have hinv : ((p : ℝ) + 1)⁻¹ ≤ 1 / (p : ℝ) := by
      rw [one_div]
      exact inv_anti₀ hp₀ (by linarith)
    have hs := sum_one_sub_confLineFactor_le hq hq₁ ω hpa
    have hs₀ : 0 ≤ ∑ l ∈ range (p + 1), (1 - confLineFactor q p ω l) :=
      sum_nonneg fun l _ => sub_nonneg.2 (confLineFactor_mem_Icc hq hq₁ p ω l).2
    calc ((p : ℝ) + 1)⁻¹ * ∑ l ∈ range (p + 1), (1 - confLineFactor q p ω l)
        ≤ (1 / (p : ℝ)) * (2 * momentPower x + 1) := mul_le_mul hinv hs hs₀ (by positivity)
      _ = (2 * momentPower x + 1) * (1 / (p : ℝ)) := mul_comm _ _
  -- step: `∑_p 1/p ≤ ∑_i V_i ≤ K`
  have hharm : ∑ p ∈ bandPrimes x d, 1 / (p : ℝ) ≤ K := by
    calc ∑ p ∈ bandPrimes x d, 1 / (p : ℝ)
        ≤ ∑ i, ∑ p ∈ band x (d.a i), 1 / (p : ℝ) :=
          sum_biUnion_le_sum_sum _ _ _ fun p => by positivity
      _ ≤ ∑ _i : Fin K, (1 : ℝ) := sum_le_sum fun i _ => (hx (d.a i) (hd i).1).2
      _ = K := by simp
  calc dampMass x d (confActive ω) (fun p l => confLineFactor q p ω l)
      ≤ ∑ p ∈ bandPrimes x d \ confActive ω, (2 * momentPower x + 1) * (1 / (p : ℝ)) :=
        sum_le_sum hterm
    _ ≤ ∑ p ∈ bandPrimes x d, (2 * momentPower x + 1) * (1 / (p : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg sdiff_subset fun p _ _ => by positivity
    _ = (2 * momentPower x + 1) * ∑ p ∈ bandPrimes x d, 1 / (p : ℝ) := by rw [mul_sum]
    _ ≤ (2 * momentPower x + 1) * K := by gcongr
    _ = K * (2 * momentPower x + 1) := mul_comm _ _

/-! ### Bounds on the kernel entries -/

/-- An entry of the slot symmetrization has norm at most `1`. -/
theorem PosModel.norm_symOp_le (M : PosModel) {x : ℝ} {d : Data K} (s t : M.State x d) :
    ‖M.symOp x d s t‖ ≤ 1 := by
  unfold PosModel.symOp
  split_ifs
  · rw [norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity))
  · simp

open scoped Classical in
/-- At most `|lists|` states sit at a given position. -/
theorem PosModel.card_filter_pos_le (M : PosModel) (x : ℝ) (d : Data K) (P : M.Pos) :
    (univ.filter fun t : M.State x d => t.1.1 = P).card ≤ (lists x d (padCount x)).card := by
  refine card_le_card_of_injOn (fun t => t.1.2) (fun t _ => ?_) fun t ht t' ht' h => ?_
  · exact (mem_product.1 (mem_filter.1 t.2).1).2
  · have hpos : t.1.1 = t'.1.1 := (mem_filter.1 ht).2.trans (mem_filter.1 ht').2.symm
    exact Subtype.ext (Prod.ext hpos h)

/-- A row of the slot symmetrization has total norm at most `|lists|`. -/
theorem PosModel.sum_norm_symOp_le (M : PosModel) {x : ℝ} {d : Data K} (s : M.State x d) :
    ∑ t, ‖M.symOp x d s t‖ ≤ (lists x d (padCount x)).card := by
  classical
  rw [← sum_filter_of_ne (p := fun t : M.State x d => t.1.1 = s.1.1) fun t _ h =>
    ((M.symOp_ne_zero_imp (norm_ne_zero_iff.1 h)).1).symm]
  calc ∑ t ∈ univ.filter (fun t : M.State x d => t.1.1 = s.1.1), ‖M.symOp x d s t‖
      ≤ ∑ t ∈ univ.filter (fun t : M.State x d => t.1.1 = s.1.1), (1 : ℝ) :=
        sum_le_sum fun t _ => M.norm_symOp_le s t
    _ ≤ (lists x d (padCount x)).card := by
        rw [sum_const, nsmul_one]
        exact_mod_cast M.card_filter_pos_le x d s.1.1

/-- A column of the slot symmetrization has total norm at most `|lists|`. -/
theorem PosModel.sum_norm_symOp_le' (M : PosModel) {x : ℝ} {d : Data K} (s : M.State x d) :
    ∑ t, ‖M.symOp x d t s‖ ≤ (lists x d (padCount x)).card := by
  classical
  rw [← sum_filter_of_ne (p := fun t : M.State x d => t.1.1 = s.1.1) fun t _ h =>
    (M.symOp_ne_zero_imp (norm_ne_zero_iff.1 h)).1]
  calc ∑ t ∈ univ.filter (fun t : M.State x d => t.1.1 = s.1.1), ‖M.symOp x d t s‖
      ≤ ∑ t ∈ univ.filter (fun t : M.State x d => t.1.1 = s.1.1), (1 : ℝ) :=
        sum_le_sum fun t _ => M.norm_symOp_le t s
    _ ≤ (lists x d (padCount x)).card := by
        rw [sum_const, nsmul_one]
        exact_mod_cast M.card_filter_pos_le x d s.1.1

/-- The arc integral is at most (number of arcs) × (arc length) `≤ Λ² · 4Λ / Y`,
`Λ = L^{A₀}`. -/
theorem norm_arcIntegral_le_cube {A₀ x Y : ℝ} (hL : 0 ≤ Real.log x) (hY : 0 < Y) (n : ℤ) :
    ‖arcIntegral A₀ x Y n‖ ≤
      Real.log x ^ A₀ * Real.log x ^ A₀ * (4 * Real.log x ^ A₀ / Y) := by
  unfold arcIntegral
  set Λ := Real.log x ^ A₀
  have hΛ : 0 ≤ Λ := Real.rpow_nonneg hL A₀
  have hF : (⌊Λ⌋₊ : ℝ) ≤ Λ := Nat.floor_le hΛ
  -- step: each arc integral is at most the arc length
  have hint : ∀ k h : ℕ, ‖∫ θ in (-(2 * Λ / Y))..(2 * Λ / Y),
      Complex.exp (2 * π * Complex.I * ((((h : ℝ) / k + θ) * n : ℝ) : ℂ))‖ ≤ 4 * Λ / Y := by
    intro k h
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) fun θ _ => ?_).trans ?_
    · have he : 2 * π * Complex.I * ((((h : ℝ) / k + θ) * n : ℝ) : ℂ) =
          ((2 * π * (((h : ℝ) / k + θ) * n) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [he, Complex.norm_exp_ofReal_mul_I]
    · have h₀ : 0 ≤ 2 * Λ / Y := by positivity
      rw [one_mul, abs_of_nonneg (by linarith)]
      exact le_of_eq (by ring)
  calc ‖∑ k ∈ Icc 1 ⌊Λ⌋₊, ∑ h ∈ (range k).filter (fun h => Nat.Coprime h k),
        ∫ θ in (-(2 * Λ / Y))..(2 * Λ / Y),
          Complex.exp (2 * π * Complex.I * ((((h : ℝ) / k + θ) * n : ℝ) : ℂ))‖
      ≤ ∑ k ∈ Icc 1 ⌊Λ⌋₊, ∑ h ∈ (range k).filter (fun h => Nat.Coprime h k), 4 * Λ / Y :=
        (norm_sum_le _ _).trans (sum_le_sum fun k _ =>
          (norm_sum_le _ _).trans (sum_le_sum fun h _ => hint k h))
    _ ≤ ∑ k ∈ Icc 1 ⌊Λ⌋₊, Λ * (4 * Λ / Y) := sum_le_sum fun k hk => by
        rw [sum_const, nsmul_eq_mul]
        have hk : ((((range k).filter fun h => Nat.Coprime h k).card : ℕ) : ℝ) ≤ Λ := by
          refine le_trans ?_ hF
          exact_mod_cast (card_filter_le _ _).trans ((card_range k).le.trans (mem_Icc.1 hk).2)
        gcongr
    _ ≤ Λ * Λ * (4 * Λ / Y) := by
        rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel, mul_assoc]
        gcongr

/-- The dyadic bump has absolute value at most `1`. -/
theorem abs_dyadicBump_le (y : ℝ) : |dyadicBump y| ≤ 1 := by
  unfold dyadicBump
  have h₁ := Real.smoothTransition.nonneg (y - 1)
  have h₂ := Real.smoothTransition.le_one (y - 1)
  have h₃ := Real.smoothTransition.nonneg (y / 2 - 1)
  have h₄ := Real.smoothTransition.le_one (y / 2 - 1)
  rw [abs_le]
  constructor <;> linarith

/-- The plateau has absolute value at most `1`. -/
theorem abs_plateau_le (t : ℝ) : |plateau t| ≤ 1 := by
  unfold plateau
  rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

/-- An entry of the row operation at `q = 1` is at most `(∏ V_i)⁻¹ (1 + max |arc|)`. -/
theorem PosModel.norm_rowOp_one_le (M : PosModel) {A₀ x : ℝ} {d : Data K} {Y d₀ Ar : ℝ}
    (hd₀ : 0 < d₀) (hb : 0 < d.bandMass x) (hAr : ∀ n, ‖arcIntegral A₀ x Y n‖ ≤ Ar)
    (s s' : M.State x d) :
    ‖M.rowOp 1 A₀ x d Y d₀ s s'‖ ≤ (d.bandMass x)⁻¹ * (1 + Ar) := by
  have hAr₀ : 0 ≤ Ar := (norm_nonneg _).trans (hAr 0)
  unfold PosModel.rowOp
  by_cases hc : (∀ i (h : Fin (padCount x)), s'.1.2 i h.castSucc = s.1.2 i h.castSucc) ∧
      (∀ i i' h', s'.1.2 i (Fin.last _) ≠ s.1.2 i' h') ∧
      d₀ ≤ (padProd s.1.2 : ℝ) ∧ (padProd s.1.2 : ℝ) < 2 * d₀ ∧
      (padProd s.1.2 : ℤ) ∣ M.det s.1.1 s'.1.1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    obtain ⟨-, -, hD₀, -, -⟩ := hc
    have hD : (0 : ℝ) < padProd s.1.2 := hd₀.trans_le hD₀
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
    · rw [Real.one_rpow, mul_one, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_pos (inv_pos.2 hb), abs_of_pos (div_pos hd₀ hD)]
      have hdD : d₀ / padProd s.1.2 ≤ 1 := (div_le_one hD).2 hD₀
      calc (d.bandMass x)⁻¹ * (d₀ / padProd s.1.2) * |dyadicBump (lastProd s.1.2 / Y)| *
            |dyadicBump (lastProd s'.1.2 / Y)| *
            |plateau ((M.det s.1.1 s'.1.1 / padProd s.1.2 : ℤ) / Y)|
          ≤ (d.bandMass x)⁻¹ * 1 * 1 * 1 * 1 := by
            gcongr
            exacts [abs_dyadicBump_le _, abs_dyadicBump_le _, abs_plateau_le _]
        _ = (d.bandMass x)⁻¹ := by ring
    · refine (norm_sub_le _ _).trans (add_le_add ?_ (hAr _))
      split_ifs <;> simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), norm_zero]
    positivity

/-- An entry of `𝒮 𝒯 𝒮` is at most `|lists|² max |𝒯|`. -/
theorem norm_confKernel_le {A₀ x : ℝ} {d : Data K} {Y d₀ Tm : ℝ}
    (hT : ∀ t t', ‖(squareModel d Y d₀).rowOp 1 A₀ x d Y d₀ t t'‖ ≤ Tm)
    (s s' : (squareModel d Y d₀).State x d) :
    ‖confKernel A₀ x d Y d₀ s s'‖ ≤ ((lists x d (padCount x)).card : ℝ) ^ 2 * Tm := by
  have hTm : 0 ≤ Tm := (norm_nonneg _).trans (hT s s)
  have hrow : ∀ t', ‖∑ t, (squareModel d Y d₀).symOp x d s t *
      (squareModel d Y d₀).rowOp 1 A₀ x d Y d₀ t t'‖ ≤
        Tm * ∑ t, ‖(squareModel d Y d₀).symOp x d s t‖ := fun t' => by
    rw [mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun t _ => ?_)
    rw [norm_mul, mul_comm Tm]
    exact mul_le_mul_of_nonneg_left (hT t t') (norm_nonneg _)
  have hS := (squareModel d Y d₀).sum_norm_symOp_le s
  have hS' := (squareModel d Y d₀).sum_norm_symOp_le' s'
  calc ‖confKernel A₀ x d Y d₀ s s'‖
      = ‖∑ t', (∑ t, (squareModel d Y d₀).symOp x d s t *
          (squareModel d Y d₀).rowOp 1 A₀ x d Y d₀ t t') *
          (squareModel d Y d₀).symOp x d t' s'‖ := by
        rw [confKernel, Matrix.mul_apply]
        simp only [Matrix.mul_apply]
    _ ≤ ∑ t', ‖∑ t, (squareModel d Y d₀).symOp x d s t *
          (squareModel d Y d₀).rowOp 1 A₀ x d Y d₀ t t'‖ *
          ‖(squareModel d Y d₀).symOp x d t' s'‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun _ _ => (norm_mul _ _).le)
    _ ≤ ∑ t', Tm * (∑ t, ‖(squareModel d Y d₀).symOp x d s t‖) *
          ‖(squareModel d Y d₀).symOp x d t' s'‖ :=
        sum_le_sum fun t' _ => mul_le_mul_of_nonneg_right (hrow t') (norm_nonneg _)
    _ = Tm * (∑ t, ‖(squareModel d Y d₀).symOp x d s t‖) *
          ∑ t', ‖(squareModel d Y d₀).symOp x d t' s'‖ := by rw [← mul_sum]
    _ ≤ Tm * (lists x d (padCount x)).card * (lists x d (padCount x)).card :=
        mul_le_mul (mul_le_mul_of_nonneg_left hS hTm) hS' (sum_nonneg fun _ _ => norm_nonneg _)
          (mul_nonneg hTm (Nat.cast_nonneg _))
    _ = ((lists x d (padCount x)).card : ℝ) ^ 2 * Tm := by ring

/-! ### Counting configurations in the tube -/

/-- With every band of size at most `E`, there are at most `E^{K(J+1)}` lists. -/
theorem card_lists_le {x : ℝ} {d : Data K} {J : ℕ} {E : ℝ}
    (hE : ∀ i, ((band x (d.a i)).card : ℝ) ≤ E) :
    ((lists x d J).card : ℝ) ≤ E ^ (K * (J + 1)) := by
  classical
  have h := card_filter_le (Fintype.piFinset fun i =>
    Fintype.piFinset fun _ : Fin (J + 1) => band x (d.a i))
    (fun p => ∀ i, Function.Injective (p i))
  calc ((lists x d J).card : ℝ)
      ≤ ((Fintype.piFinset fun i =>
          Fintype.piFinset fun _ : Fin (J + 1) => band x (d.a i)).card : ℝ) := by
        unfold lists
        exact_mod_cast h
    _ = ∏ i : Fin K, ∏ _h : Fin (J + 1), ((band x (d.a i)).card : ℝ) := by
        simp [Fintype.card_piFinset]
    _ ≤ ∏ _i : Fin K, ∏ _h : Fin (J + 1), E :=
        prod_le_prod₀ (fun _ _ => prod_nonneg fun _ _ => Nat.cast_nonneg _) fun i _ =>
          prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun _ _ => hE i
    _ = E ^ (K * (J + 1)) := by
        rw [prod_const, prod_const, card_univ, card_univ, Fintype.card_fin, Fintype.card_fin,
          ← pow_mul, mul_comm]

/-- With every band prime at most `E`, the product of the labels is at most `E^{K(J+1)}`. -/
theorem listProd_le {x : ℝ} {d : Data K} {J : ℕ} {E : ℝ}
    (hE : ∀ i, ∀ p ∈ band x (d.a i), (p : ℝ) ≤ E) {p : Lists K J} (hp : p ∈ lists x d J) :
    (listProd p : ℝ) ≤ E ^ (K * (J + 1)) := by
  unfold listProd
  push_cast
  calc ∏ i, ∏ h, (p i h : ℝ) ≤ ∏ _i : Fin K, ∏ _h : Fin (J + 1), E :=
        prod_le_prod₀ (fun _ _ => prod_nonneg fun _ _ => Nat.cast_nonneg _) fun i _ =>
          prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun h _ =>
            hE i _ (mem_band_of_mem_lists hp i h)
    _ = E ^ (K * (J + 1)) := by
        rw [prod_const, prod_const, card_univ, card_univ, Fintype.card_fin, Fintype.card_fin,
          ← pow_mul, mul_comm]

open scoped Classical in
/-- The coefficient budget for explicit bounds: with at most `W ≥ 1` lists, label products at
most `W`, and entries of `𝒯` at most `T`, the live coefficients have total mass at most
`((2B + 1)² W)^{N+1} · stateMass · (W² T)^N` for `B ≥ 2560 N W² + 16`. A live `ω` with
`c(ω) ≠ 0` has `d₀ Y < (∏ labels)² ≤ W²`, so it stays in the tube `|z| ≤ B`. -/
theorem sum_norm_confCoeff_le_of_bounds {A₀ x : ℝ} {d : Data K} {Y d₀ W Tm B : ℝ}
    (hY : 0 < Y) (hd₀ : 0 < d₀) (hHm : 0 < d.Hm) (hR : 0 < momentPower x)
    (hW : 1 ≤ W) (hcard : ((lists x d (padCount x)).card : ℝ) ≤ W)
    (hprod : ∀ p ∈ lists x d (padCount x), (listProd p : ℝ) ≤ W)
    (hT : ∀ t t', ‖(squareModel d Y d₀).rowOp 1 A₀ x d Y d₀ t t'‖ ≤ Tm)
    (hB : 2560 * (2 * momentPower x) * W ^ 2 + 16 ≤ B) :
    ∑ ω ∈ univ.filter (fun ω : Conf x d Y d₀ => ConfLive ω), ‖confCoeff A₀ x d Y d₀ ω‖ ≤
      ((2 * B + 1) ^ 2 * W) ^ (2 * momentPower x + 1) *
        (stateMass x d * (W ^ 2 * Tm) ^ (2 * momentPower x)) := by
  have hB₀ : 0 ≤ B := by
    have : 0 ≤ 2560 * (2 * (momentPower x : ℝ)) * W ^ 2 := by positivity
    linarith
  -- step: the states in the tube `|z₁|, |z₂| ≤ B`
  set T := univ.filter fun s : (squareModel d Y d₀).State x d =>
    |(s.1.1.1.1 : ℝ)| ≤ B ∧ |(s.1.1.1.2 : ℝ)| ≤ B
  set I := Icc (-⌊B⌋) ⌊B⌋
  have hI : (I.card : ℝ) ≤ 2 * B + 1 := by
    have hfl := Int.floor_nonneg.2 hB₀
    have h₁ : (I.card : ℤ) = ⌊B⌋ + 1 - -⌊B⌋ := Int.card_Icc_of_le _ _ (by omega)
    have h₂ : ((I.card : ℤ) : ℝ) = (I.card : ℝ) := Int.cast_natCast _
    rw [← h₂, h₁]
    push_cast
    linarith [Int.floor_le B]
  have hmemI : ∀ a : ℤ, |(a : ℝ)| ≤ B → a ∈ I := fun a ha => by
    obtain ⟨h₁, h₂⟩ := abs_le.1 ha
    have h₃ := Int.le_floor.2 (show ((-a : ℤ) : ℝ) ≤ B by push_cast; linarith)
    exact mem_Icc.2 ⟨by omega, Int.le_floor.2 h₂⟩
  have hcardT : (T.card : ℝ) ≤ (2 * B + 1) ^ 2 * W := by
    have hle : T.card ≤ ((I ×ˢ I) ×ˢ lists x d (padCount x)).card := by
      refine card_le_card_of_injOn (fun s => (s.1.1.1, s.1.2)) (fun s hs => ?_)
        fun s _ s' _ h => ?_
      · obtain ⟨h₁, h₂⟩ := (mem_filter.1 hs).2
        exact mem_product.2 ⟨mem_product.2 ⟨hmemI _ h₁, hmemI _ h₂⟩, mem_lists_of_state s⟩
      · obtain ⟨h₁, h₂⟩ := Prod.ext_iff.1 h
        exact Subtype.ext (Prod.ext (Subtype.ext h₁) h₂)
    rw [card_product, card_product] at hle
    calc (T.card : ℝ) ≤ ((I.card * I.card * (lists x d (padCount x)).card : ℕ) : ℝ) := by
          exact_mod_cast hle
      _ = I.card * I.card * (lists x d (padCount x)).card := by push_cast; ring
      _ ≤ (2 * B + 1) * (2 * B + 1) * W := by gcongr
      _ = (2 * B + 1) ^ 2 * W := by ring
  -- step: a live configuration with `c(ω) ≠ 0` stays in the tube
  have hsub : (univ.filter fun ω : Conf x d Y d₀ => ConfLive ω).filter
      (fun ω => ‖confCoeff A₀ x d Y d₀ ω‖ ≠ 0) ⊆ Fintype.piFinset fun _ => T := by
    intro ω hω
    obtain ⟨hω₁, hω₂⟩ := mem_filter.1 hω
    have hlive := (mem_filter.1 hω₁).2
    have hc := norm_ne_zero_iff.1 hω₂
    obtain ⟨-, -, hd₀l, hYl⟩ := confCoeff_ne_zero_imp hY hd₀ hR hc
    have hl := hprod _ (mem_lists_of_state (ω 0))
    have hH : d₀ * Y ≤ W ^ 2 := by
      rw [sq]
      exact mul_le_mul (hd₀l.trans hl) (hYl.le.trans hl) hY.le (by linarith)
    refine Fintype.mem_piFinset.2 fun j => mem_filter.2 ⟨mem_univ _, ?_⟩
    obtain ⟨h₂, h₁⟩ := tube_of_live hY hd₀ hHm hR hc hlive j
    have hNH : 2560 * (2 * (momentPower x : ℝ)) * (d₀ * Y) ≤
        2560 * (2 * momentPower x) * W ^ 2 := by gcongr
    constructor <;> linarith
  have hcardS : (((univ.filter fun ω : Conf x d Y d₀ => ConfLive ω).filter
      (fun ω => ‖confCoeff A₀ x d Y d₀ ω‖ ≠ 0)).card : ℝ) ≤
        ((2 * B + 1) ^ 2 * W) ^ (2 * momentPower x + 1) := by
    have h := card_le_card hsub
    rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin] at h
    calc _ ≤ ((T.card ^ (2 * momentPower x + 1) : ℕ) : ℝ) := by exact_mod_cast h
      _ = (T.card : ℝ) ^ (2 * momentPower x + 1) := by push_cast; ring
      _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) hcardT _
  -- step: each coefficient is at most `stateMass · (W² T)^N`
  have hsm : 0 ≤ stateMass x d := by
    unfold stateMass Data.bandMass harmonicMass
    positivity
  have hcoef : ∀ ω : Conf x d Y d₀,
      ‖confCoeff A₀ x d Y d₀ ω‖ ≤ stateMass x d * (W ^ 2 * Tm) ^ (2 * momentPower x) := by
    intro ω
    have hTm : 0 ≤ Tm := (norm_nonneg _).trans (hT (ω 0) (ω 0))
    have hκ : ∀ j : Fin (2 * momentPower x),
        ‖confKernel A₀ x d Y d₀ (ω j.castSucc) (ω j.succ)‖ ≤ W ^ 2 * Tm := fun j =>
      (norm_confKernel_le hT _ _).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) hTm)
    have hite : ‖(if (ω 0).1.1.1 = (1, 0) ∧ (ω (Fin.last _)).1.1.1 = (1, 0) then (1 : ℂ)
        else 0)‖ ≤ 1 := by
      split_ifs <;> simp
    unfold confCoeff
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsm, norm_prod]
    calc stateMass x d *
          ‖(if (ω 0).1.1.1 = (1, 0) ∧ (ω (Fin.last _)).1.1.1 = (1, 0) then (1 : ℂ) else 0)‖ *
          ∏ j : Fin (2 * momentPower x), ‖confKernel A₀ x d Y d₀ (ω j.castSucc) (ω j.succ)‖
        ≤ stateMass x d * 1 * ∏ _j : Fin (2 * momentPower x), W ^ 2 * Tm :=
          mul_le_mul (mul_le_mul_of_nonneg_left hite hsm)
            (prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => hκ j)
            (prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
      _ = stateMass x d * (W ^ 2 * Tm) ^ (2 * momentPower x) := by
          rw [prod_const, card_univ, Fintype.card_fin, mul_one]
  have hmax : 0 ≤ stateMass x d * (W ^ 2 * Tm) ^ (2 * momentPower x) :=
    mul_nonneg hsm ((even_two_mul _).pow_nonneg _)
  rw [← sum_filter_ne_zero]
  calc _ ≤ ((univ.filter fun ω : Conf x d Y d₀ => ConfLive ω).filter
          (fun ω => ‖confCoeff A₀ x d Y d₀ ω‖ ≠ 0)).card •
          (stateMass x d * (W ^ 2 * Tm) ^ (2 * momentPower x)) :=
        sum_le_card_nsmul _ _ _ fun ω _ => hcoef ω
    _ = _ := nsmul_eq_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hcardS hmax

/-! ### Asymptotics of the budget -/

/-- Every fixed multiple of a power of `L` is eventually below `exp(L^{1/5})`. -/
theorem eventually_mul_rpow_le_exp (c A : ℝ) :
    ∀ᶠ x : ℝ in atTop, c * Real.log x ^ A ≤ Real.exp (Real.log x ^ (1 / 5 : ℝ)) := by
  have hexp := (tendsto_exp_div_rpow_atTop (5 * A)).comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp Real.tendsto_log_atTop)
  filter_upwards [hexp.eventually_ge_atTop c, Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with x hx hL
  have hx' : c ≤ Real.exp (Real.log x ^ (1 / 5 : ℝ)) / (Real.log x ^ (1 / 5 : ℝ)) ^ (5 * A) :=
    hx
  -- step: `(L^{1/5})^{5A} = L^A`
  rw [← Real.rpow_mul (by linarith), show 1 / 5 * (5 * A) = A by ring,
    le_div_iff₀ (Real.rpow_pos_of_pos (by linarith) A)] at hx'
  exact hx'

/-- The exponent of the budget: with `N = 2R ≤ L^{1/2} + 2` and `J + 1 ≤ 2 L^{1/100}`, the
power `Z` of `exp(L^{1/5})` has `Z L^{1/5} ≤ 8 (16K + 3) L^{0.71} ≤ L^{0.74}`. -/
theorem budget_exponent_le {L : ℝ} (hL : 1 ≤ L) (K R J : ℕ)
    (hR : (R : ℝ) ≤ L ^ (1 / 2 : ℝ) / 2 + 1) (hJ : (J : ℝ) ≤ L ^ (1 / 100 : ℝ))
    (hK : 8 * (16 * (K : ℝ) + 3) ≤ L ^ (3 / 100 : ℝ)) :
    (((2 + 10 * (K * (J + 1))) * (2 * R + 1) +
        (K * (J + 1) + (4 * (K * (J + 1)) + K + 1) * (2 * R)) : ℕ) : ℝ) *
        L ^ (1 / 5 : ℝ) ≤ L ^ (74 / 100 : ℝ) := by
  have hL₀ : 0 < L := by linarith
  have ha := Real.one_le_rpow hL (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hb := Real.one_le_rpow hL (by norm_num : (0 : ℝ) ≤ 1 / 100)
  have hc := Real.rpow_nonneg hL₀.le (1 / 5 : ℝ)
  have hK₀ : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hR₀ : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hJ₀ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  push_cast
  -- step: `Z ≤ (N + 1) (J + 1) (16K + 3)`
  have hZ : (2 + 10 * (K * (J + 1 : ℝ))) * (2 * R + 1) +
      (K * (J + 1) + (4 * (K * (J + 1)) + K + 1) * (2 * R)) ≤
        (2 * R + 1) * (J + 1) * (16 * K + 3) := by
    nlinarith [mul_nonneg (mul_nonneg hK₀ hR₀) hJ₀, mul_nonneg hR₀ hJ₀, mul_nonneg hK₀ hJ₀,
      mul_nonneg hK₀ hR₀]
  have hN : (2 * R + 1 : ℝ) ≤ 4 * L ^ (1 / 2 : ℝ) := by linarith
  have hM : (J + 1 : ℝ) ≤ 2 * L ^ (1 / 100 : ℝ) := by linarith
  have hpow : L ^ (1 / 2 : ℝ) * L ^ (1 / 100 : ℝ) * L ^ (1 / 5 : ℝ) * L ^ (3 / 100 : ℝ) =
      L ^ (74 / 100 : ℝ) := by
    rw [← Real.rpow_add hL₀, ← Real.rpow_add hL₀, ← Real.rpow_add hL₀]
    norm_num
  calc ((2 + 10 * (K * (J + 1 : ℝ))) * (2 * R + 1) +
        (K * (J + 1) + (4 * (K * (J + 1)) + K + 1) * (2 * R))) * L ^ (1 / 5 : ℝ)
      ≤ ((2 * R + 1) * (J + 1) * (16 * K + 3)) * L ^ (1 / 5 : ℝ) := by gcongr
    _ ≤ (4 * L ^ (1 / 2 : ℝ) * (2 * L ^ (1 / 100 : ℝ)) * (16 * K + 3)) * L ^ (1 / 5 : ℝ) := by
        gcongr
    _ = L ^ (1 / 2 : ℝ) * L ^ (1 / 100 : ℝ) * L ^ (1 / 5 : ℝ) * (8 * (16 * K + 3)) := by ring
    _ ≤ L ^ (1 / 2 : ℝ) * L ^ (1 / 100 : ℝ) * L ^ (1 / 5 : ℝ) * L ^ (3 / 100 : ℝ) := by
        gcongr
    _ = L ^ (74 / 100 : ℝ) := hpow

open scoped Classical in
/-- **The coefficient budget**: the live coefficients have total mass at most
`exp(L^{0.74})`, eventually. -/
theorem eventually_sum_norm_confCoeff_le {C CX alo ahi g : ℝ} (halo : 1 / 10 < alo)
    (hahi : ahi < 1 / 5) (A₀ : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∑ ω ∈ univ.filter (fun ω : Conf x d (2 ^ j) (2 ^ k) => ConfLive ω),
          ‖confCoeff A₀ x d (2 ^ j) (2 ^ k) ω‖ ≤
        Real.exp (Real.log x ^ (74 / 100 : ℝ)) := by
  have hK3 := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 100)).comp
    Real.tendsto_log_atTop).eventually_ge_atTop (8 * (16 * (K : ℝ) + 3))
  filter_upwards [eventually_gt_atTop 0, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_harmonicMass_band halo.le, eventually_mul_rpow_le_exp 20000 (1 / 2),
    eventually_mul_rpow_le_exp 8 (3 * A₀), hK3] with x hx hL hmass hNP hAP hK d hd j k
  have hK' : 8 * (16 * (K : ℝ) + 3) ≤ Real.log x ^ (3 / 100 : ℝ) := hK
  have hL₀ : 0 < Real.log x := by linarith
  set P := Real.exp (Real.log x ^ (1 / 5 : ℝ)) with hPdef
  have hP₂ : 2 ≤ P := by
    have := Real.one_le_rpow hL (by norm_num : (0 : ℝ) ≤ 1 / 5)
    linarith [Real.add_one_le_exp (Real.log x ^ (1 / 5 : ℝ))]
  have hP₁ : 1 ≤ P := by linarith
  -- step: band primes and band sizes are at most `exp(2 L^{1/5}) = P²`
  have hexp : ∀ i, Real.exp (2 * Real.log x ^ d.a i) ≤ P ^ 2 := fun i => by
    have := Real.rpow_le_rpow_of_exponent_le hL ((hd.window i).2.trans hahi.le)
    rw [sq, hPdef, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hband : ∀ i, ∀ p ∈ band x (d.a i), (p : ℝ) ≤ P ^ 2 := fun i p hp =>
    (le_exp_of_mem_band hp).trans (hexp i)
  have hcardb : ∀ i, ((band x (d.a i)).card : ℝ) ≤ P ^ 2 := fun i =>
    (card_band_le x (d.a i)).trans (hexp i)
  set M := padCount x + 1
  set W := (P ^ 2) ^ (K * M)
  have hW : 1 ≤ W := one_le_pow₀ (by nlinarith)
  -- step: `∏ V_i ≥ 2^{-K}`
  have hb : (1 / 2 : ℝ) ^ K ≤ d.bandMass x := by
    calc (1 / 2 : ℝ) ^ K = ∏ _i : Fin K, (1 / 2 : ℝ) := by simp
      _ ≤ d.bandMass x := prod_le_prod₀ (fun _ _ => by norm_num) fun i _ =>
          (hmass (d.a i) (hd.window i).1).1
  have hbpos : 0 < d.bandMass x := lt_of_lt_of_le (by positivity) hb
  have hbinv : (d.bandMass x)⁻¹ ≤ P ^ K := by
    calc (d.bandMass x)⁻¹ ≤ ((1 / 2 : ℝ) ^ K)⁻¹ := inv_anti₀ (by positivity) hb
      _ = 2 ^ K := by rw [one_div, inv_pow, inv_inv]
      _ ≤ P ^ K := pow_le_pow_left₀ (by norm_num) hP₂ K
  -- step: the entries of `𝒯` are at most `P^K · P`
  have hY : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hd₀ : (0 : ℝ) < 2 ^ k := by positivity
  set Λ := Real.log x ^ A₀
  have hΛ : 0 ≤ Λ := Real.rpow_nonneg hL₀.le A₀
  have hΛ3 : Λ * Λ * Λ = Real.log x ^ (3 * A₀) := by
    rw [← Real.rpow_add hL₀, ← Real.rpow_add hL₀]
    ring_nf
  have hAr : Λ * Λ * (4 * Λ / 2 ^ j) ≤ 4 * Real.log x ^ (3 * A₀) := by
    rw [← hΛ3]
    have : 4 * Λ / 2 ^ j ≤ 4 * Λ := div_le_self (by positivity) hY
    calc Λ * Λ * (4 * Λ / 2 ^ j) ≤ Λ * Λ * (4 * Λ) := by gcongr
      _ = 4 * (Λ * Λ * Λ) := by ring
  have hT := fun t t' => (squareModel d (2 ^ j) (2 ^ k)).norm_rowOp_one_le hd₀ hbpos
    (fun n => norm_arcIntegral_le_cube (A₀ := A₀) hL₀.le (by positivity : (0 : ℝ) < 2 ^ j) n) t t'
  have hTm₀ : 0 ≤ (d.bandMass x)⁻¹ * (1 + Λ * Λ * (4 * Λ / 2 ^ j)) := by positivity
  have hTm : (d.bandMass x)⁻¹ * (1 + Λ * Λ * (4 * Λ / 2 ^ j)) ≤ P ^ K * P := by
    have : 1 + Λ * Λ * (4 * Λ / 2 ^ j) ≤ P := by linarith
    exact mul_le_mul hbinv this (by positivity) (by positivity)
  -- step: the budget for explicit bounds
  have hR : 0 < momentPower x := Nat.ceil_pos.2 (by positivity)
  have hHm : 0 < d.Hm := (Real.rpow_pos_of_pos hx _).trans_le hd.Hm_ge
  have hmain := sum_norm_confCoeff_le_of_bounds (A₀ := A₀) (by positivity) hd₀ hHm hR hW
    (card_lists_le hcardb) (fun p hp => listProd_le hband hp) hT
    (B := (2560 * (2 * momentPower x) + 16) * W ^ 2) (by nlinarith)
  refine hmain.trans ?_
  -- step: `2B + 1 ≤ P W²` and `stateMass ≤ P^{KM}`
  have hmp : (momentPower x : ℝ) ≤ Real.log x ^ (1 / 2 : ℝ) / 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hsqrt := Real.one_le_rpow hL (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hW2 : 1 ≤ W ^ 2 := one_le_pow₀ hW
  have h2B : 2 * ((2560 * (2 * momentPower x) + 16) * W ^ 2) + 1 ≤ P * W ^ 2 := by
    have : 10240 * (momentPower x : ℝ) + 33 ≤ P := by linarith
    nlinarith
  have hsm : stateMass x d ≤ (P ^ K) ^ M :=
    pow_le_pow_left₀ (inv_nonneg.2 hbpos.le) hbinv M
  have hZ : ((P * W ^ 2) ^ 2 * W) ^ (2 * momentPower x + 1) *
      ((P ^ K) ^ M * (W ^ 2 * (P ^ K * P)) ^ (2 * momentPower x)) =
        P ^ ((2 + 10 * (K * M)) * (2 * momentPower x + 1) +
          (K * M + (4 * (K * M) + K + 1) * (2 * momentPower x))) := by
    simp only [W]
    ring
  calc ((2 * ((2560 * (2 * momentPower x) + 16) * W ^ 2) + 1) ^ 2 * W) ^
        (2 * momentPower x + 1) * (stateMass x d *
          (W ^ 2 * ((d.bandMass x)⁻¹ * (1 + Λ * Λ * (4 * Λ / 2 ^ j)))) ^ (2 * momentPower x))
      ≤ ((P * W ^ 2) ^ 2 * W) ^ (2 * momentPower x + 1) *
          ((P ^ K) ^ M * (W ^ 2 * (P ^ K * P)) ^ (2 * momentPower x)) := by
        have hsm₀ : 0 ≤ stateMass x d := pow_nonneg (inv_nonneg.2 hbpos.le) _
        gcongr
    _ = P ^ ((2 + 10 * (K * M)) * (2 * momentPower x + 1) +
          (K * M + (4 * (K * M) + K + 1) * (2 * momentPower x))) := hZ
    _ = Real.exp (((2 + 10 * (K * M)) * (2 * momentPower x + 1) +
          (K * M + (4 * (K * M) + K + 1) * (2 * momentPower x)) : ℕ) *
            Real.log x ^ (1 / 5 : ℝ)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (Real.log x ^ (74 / 100 : ℝ)) :=
        Real.exp_le_exp.2 (budget_exponent_le hL K (momentPower x) (padCount x) hmp
          (Nat.floor_le (by positivity)) hK')

end Erdos408.OneSided
