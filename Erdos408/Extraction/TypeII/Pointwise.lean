module

public import Erdos408.Extraction.TypeII.Data

/-!
# The bound at one scale

At a fixed large `x`, `|Comp_j - Prox_j| ≤ j B₄ + j B₅`, with the explicit E4 bound `B₄` of
`abs_single_step_le` and E5 bound `B₅` of `abs_strip_step_le`, the factor sums bounded by
`Q_ρ = ρ ∑_{x^γ < p ≤ M} 1/p + ∏_{Y < p ≤ M} (1 - ρ/p)⁻¹`.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real

/-- `∑_{x^γ < p ≤ M} 1/p`. -/
noncomputable def recipSum (x γ : ℝ) (N : ℕ) : ℝ := ∑ p ∈ primesIoc (x ^ γ) N, (1 : ℝ) / p

/-- `∏_{Y < p ≤ M} (1 - ρ/p)⁻¹`. -/
noncomputable def highProd (x : ℝ) (N : ℕ) (ρ : ℝ) : ℝ :=
  ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - ρ / p)⁻¹

theorem recipSum_nonneg (x γ : ℝ) (N : ℕ) : 0 ≤ recipSum x γ N :=
  sum_nonneg fun _ _ => by positivity

theorem highProd_nonneg {x : ℝ} {N : ℕ} {ρ : ℝ} (hρ : ρ < proxyCutoff x) :
    0 ≤ highProd x N ρ :=
  prod_nonneg fun p hp => by
    have := (mem_primesIoc.1 hp).2.1
    have hY : 0 < proxyCutoff x := Real.exp_pos _
    have hp0 : 0 < (p : ℝ) := by linarith
    rw [inv_nonneg, sub_nonneg, div_le_one hp0]; linarith

section Factor

variable {x γ : ℝ} {j N : ℕ}

/-- The facts used to bound one factor of a companion. -/
structure ScaleFacts (x γ : ℝ) (j N : ℕ) : Prop where
  one_lt : 1 < x
  log_ge : 1 ≤ Real.log x
  gamma_pos : 0 < γ
  one_le_j : 1 ≤ j
  prodY : 1 ≤ (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x)
  cutoff_gt : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x
  cutoff_le_rpow : proxyCutoff x ≤ x ^ γ
  cutoff_le_N : proxyCutoff x ≤ N
  exp_le_rpow : Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ x ^ γ
  exp_le_cutoff : Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ proxyCutoff x
  j_lt_cutoff : (j : ℝ) < proxyCutoff x

/-- The weight family of an E4 step. -/
noncomputable def stepWeight4 (x γ : ℝ) (j : ℕ) {r : ℕ} (i : Fin (r + 1)) (k : Fin r) : ℕ → ℝ :=
  if i.succAbove k < i then unstrippedProxy x γ j else primeWeight x γ

/-- The weight family of an E5 step. -/
noncomputable def stepWeight5 (x γ : ℝ) (j : ℕ) {r : ℕ} (i : Fin (r + 1)) (k : Fin r) : ℕ → ℝ :=
  if i.succAbove k < i then strippedProxy x γ j else unstrippedProxy x γ j

theorem factorWeight_step4 (h : ScaleFacts x γ j N) {r : ℕ} (i : Fin (r + 1)) (k : Fin r) :
    FactorWeight x γ j (stepWeight4 x γ j i k) := by
  unfold stepWeight4
  split_ifs
  · exact factorWeight_unstripped h.one_lt h.log_ge h.gamma_pos h.one_le_j h.prodY
      h.exp_le_cutoff
  · exact factorWeight_prime h.log_ge h.cutoff_gt h.cutoff_le_rpow h.exp_le_rpow

/-- One factor sum against `g r^Ω / m`. -/
theorem sum_step4_sq_le (h : ScaleFacts x γ j N) {r : ℕ} (hrj : r + 1 = j) (i : Fin (r + 1))
    (k : Fin r) :
    ∑ m ∈ Icc 1 N, stepWeight4 x γ j i k m * cmul (fun p => proxyLoc x j p * r / p) m ≤
      r * recipSum x γ N + highProd x N r := by
  have hrY : (r : ℝ) < proxyCutoff x := by
    have : (r : ℝ) ≤ j := by exact_mod_cast (show r ≤ j by omega)
    linarith [h.j_lt_cutoff]
  have hrj' : (r : ℝ) ≤ j := by exact_mod_cast (show r ≤ j by omega)
  unfold stepWeight4
  split_ifs
  · exact (sum_unstrippedProxy_sq_le h.one_lt h.log_ge h.gamma_pos h.one_le_j h.prodY
      h.cutoff_gt h.cutoff_le_N (Nat.cast_nonneg r) hrj' hrY).trans
      (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg r) (recipSum_nonneg x γ N)))
  · exact (sum_primeWeight_le h.log_ge h.cutoff_gt h.cutoff_le_rpow N (Nat.cast_nonneg r)).trans
      (le_add_of_nonneg_right (highProd_nonneg hrY))

/-- One factor sum against `1/m`. -/
theorem sum_step4_div_le (h : ScaleFacts x γ j N) {r : ℕ} (i : Fin (r + 1)) (k : Fin r) :
    ∑ m ∈ Icc 1 N, stepWeight4 x γ j i k m * cmul (fun p => (p : ℝ)⁻¹) m ≤
      recipSum x γ N + highProd x N 1 := by
  have h1Y : (1 : ℝ) < proxyCutoff x := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast h.one_le_j
    linarith [h.j_lt_cutoff]
  unfold stepWeight4
  split_ifs
  · exact (sum_unstrippedProxy_div_le h.one_lt h.log_ge h.gamma_pos h.one_le_j h.prodY
      h.cutoff_gt h.cutoff_le_N).trans (le_add_of_nonneg_left (recipSum_nonneg x γ N))
  · exact (sum_primeWeight_div_le N).trans (le_add_of_nonneg_right (highProd_nonneg h1Y))

/-- A product of factor sums. -/
theorem prod_le_pow {r : ℕ} (f : Fin r → ℝ) (hf0 : ∀ k, 0 ≤ f k) {Q : ℝ} (hf : ∀ k, f k ≤ Q) :
    ∏ k, f k ≤ Q ^ r := by
  rw [show Q ^ r = ∏ _k : Fin r, Q by rw [prod_const, card_univ, Fintype.card_fin]]
  exact prod_le_prod₀ (fun k _ => hf0 k) fun k _ => hf k

end Factor

/-! ### The bound at one scale -/

/-- The E4 bound for one step, with `R = j - 1` companion factors. -/
noncomputable def bound4 (q : ℝ) (K : ℕ) (CN c E₂ κ CΦ C₂ : ℝ) (M : ℕ → ℝ) (x γ δ : ℝ)
    (A R : ℕ) : ℝ :=
  M 0 * endBound q K CN c E₂ x * (⌊κ * x + 1⌋₊ / Real.log x ^ (3 : ℝ)) *
      (R * recipSum x γ ⌊κ * x + 1⌋₊ + highProd x ⌊κ * x + 1⌋₊ R) ^ R +
    (A : ℝ) ^ 2 * (M 0 * (2 ^ (K * inertPerCluster K CN x) * normBound q K CN c E₂ x *
      (C₂ * (κ * x) * Real.log x ^ (-12 : ℝ)))) +
    M 1 * logLog x ^ (CΦ * 1) * ((3 * δ * (κ * x + 1) + 1) / x) * endBound q K CN c E₂ x *
      (4 * (κ * x + 1)) * (recipSum x γ ⌊κ * x + 1⌋₊ + highProd x ⌊κ * x + 1⌋₊ 1) ^ R

/-- The E5 bound for one step, with `r + 1 = j - 1` companion factors. -/
noncomputable def bound5 (q : ℝ) (K : ℕ) (CN c E₂ κ : ℝ) (M : ℕ → ℝ) (x γ cW SP c₃ : ℝ)
    (K' r : ℕ) : ℝ :=
  M 0 * endBound q K CN c E₂ x * cW * ⌊κ * x + 1⌋₊ * highProd x ⌊κ * x + 1⌋₊ 1 ^ r *
    (2 * cW * K' + 2 * SP * highProd x ⌊κ * x + 1⌋₊ 1 * (Real.log (proxyCutoff x) / c₃) /
      (γ ^ 2 * Real.log x ^ (19 / 10 : ℝ)))

/-- E4 at one scale: `|Comp_j - Prox_j^0| ≤ j B₄`. -/
theorem abs_comp_sub_prox0_le {q cw : ℝ} (hq₁ : q < 1) {K : ℕ} {CN c Ch Cj κ CΦ C₂ x E₂ δ : ℝ}
    {M : ℕ → ℝ} {Φ : ℝ → ℝ} {k : ℕ} {u v : Fin (k + 1) → ℝ} {B : (Fin k → ℕ) → ℝ}
    (hE : EndpointData q cw K CN x u v B (normBound q K CN c E₂ x))
    (hV : ∀ a : ℝ, 1 / 10 ≤ a → 1 / 2 ≤ harmonicMass (band x a))
    (hbox : BoxBound q K c Ch Cj κ C₂ x) (hC₂ : 0 ≤ C₂) (hΦ : IsCutoff κ CΦ M x Φ)
    (hκ : 1 < κ) (hxκ : κ ≤ x) (hsq : 4 * (κ * x + 1) ≤ x ^ 2) {R : ℕ} (hR : 1 ≤ R)
    (hsf : ScaleFacts x (presieveExponent c Ch x) (R + 1) ⌊κ * x + 1⌋₊)
    (hj2 : ((R + 1 : ℕ) : ℝ) ≤ Cj * logLogLog x + 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {A : ℕ}
    (hA : (⌊κ * x + 1⌋₊ : ℝ) ≤ gridPt x (presieveExponent c Ch x) δ A) :
    |∑ m ∈ Fintype.piFinset (fun _ : Fin (R + 1) => Icc 1 ⌊κ * x + 1⌋₊),
        cutPsi Φ (endpoint q cw K CN x u v B) x (∏ i, m i) *
          ∏ i, primeWeight x (presieveExponent c Ch x) (m i) -
      ∑ m ∈ Fintype.piFinset (fun _ : Fin (R + 1) => Icc 1 ⌊κ * x + 1⌋₊),
        cutPsi Φ (endpoint q cw K CN x u v B) x (∏ i, m i) *
          ∏ i, unstrippedProxy x (presieveExponent c Ch x) (R + 1) (m i)| ≤
      (R + 1) * bound4 q K CN c E₂ κ CΦ C₂ M x (presieveExponent c Ch x) δ A R := by
  set γ := presieveExponent c Ch x
  set N := ⌊κ * x + 1⌋₊
  have hx := hsf.one_lt
  have hxγ : 1 ≤ x ^ γ := Real.one_le_rpow hx.le hsf.gamma_pos.le
  have hSE0 : 0 ≤ endBound q K CN c E₂ x := by
    have := hE.norm_pos
    unfold endBound
    have : 0 < 1 - q := by linarith
    positivity
  have hSE : ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ x ^ 2 →
      |endpoint q cw K CN x u v B h| ≤ endBound q K CN c E₂ x :=
    fun h h1 hh => abs_endpoint_le hq₁ hE hV h1 hh
  have ha01 := fun m => unstrippedProxy_le_one hx hsf.log_ge hsf.gamma_pos hsf.one_le_j
    hsf.prodY (j := R + 1) m
  have hα : ∀ m, |primeProxyDiff x γ (R + 1) m| ≤ 1 := by
    intro m
    obtain ⟨h0, h1⟩ := ha01 m
    unfold primeProxyDiff
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hαs : ∀ m : ℕ, (m : ℝ) ≤ x ^ γ → primeProxyDiff x γ (R + 1) m = 0 := by
    intro m hm
    unfold primeProxyDiff
    rw [(proxies_eq_zero (j := R + 1) hx hsf.gamma_pos.le hm).1, sub_zero]
    exact ite_eq_right fun h => absurd h.2 (not_lt.2 hm)
  rw [sum_sub_sum_eq_steps]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [show ((R : ℝ) + 1) * bound4 q K CN c E₂ κ CΦ C₂ M x γ δ A R =
    ∑ _i : Fin (R + 1), bound4 q K CN c E₂ κ CΦ C₂ M x γ δ A R by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring]
  refine sum_le_sum fun i _ => ?_
  have hstep := abs_single_step_le hE hbox hC₂ hΦ hκ hx hxκ hxγ hsq hSE0 hSE hδ0 hδ1 hA
    hsf.one_le_j hj2 hα hαs hR (stepWeight4 x γ (R + 1) i) (factorWeight_step4 hsf i)
  have hprod2 := prod_le_pow _ (fun k => sum_nonneg fun m _ => mul_nonneg
      ((factorWeight_step4 hsf i k).nonneg m) (cmul_nonneg (fun p _ => by
        have := proxyLoc_nonneg x (R + 1) p; positivity) m))
    (fun k => sum_step4_sq_le hsf rfl i k)
  have hprod1 := prod_le_pow _ (fun k => sum_nonneg fun m _ => mul_nonneg
      ((factorWeight_step4 hsf i k).nonneg m) (cmul_nonneg (fun p _ => by positivity) m))
    (fun k => sum_step4_div_le hsf i k)
  refine le_trans (le_of_eq ?_) (hstep.trans ?_)
  · rfl
  unfold bound4
  have hM0 : 0 ≤ M 0 := (abs_nonneg _).trans (by simpa using hΦ.2.2.2 0 0)
  have hτ : 0 ≤ M 1 * logLog x ^ (CΦ * 1) * ((3 * δ * (κ * x + 1) + 1) / x) := by
    have := cutoff_deriv_bound_nonneg hΦ 1
    push_cast at this
    have : 0 ≤ κ * x := by positivity
    positivity
  have hL0 : 0 ≤ Real.log x := by linarith [hsf.log_ge]
  have hL3 : 0 ≤ (N : ℝ) / Real.log x ^ (3 : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hL0 _)
  have hcard := card_clusterSets_le K (inertPerCluster K CN x)
  have hNb := hE.norm_pos
  have hLr : 0 ≤ Real.log x ^ (-12 : ℝ) := Real.rpow_nonneg hL0 _
  have hC : 0 ≤ C₂ * (κ * x) * Real.log x ^ (-12 : ℝ) :=
    mul_nonneg (mul_nonneg hC₂ (by positivity)) hLr
  gcongr

/-- E5 at one scale: `|Prox_j^0 - Prox_j| ≤ j B₅`. -/
theorem abs_prox0_sub_prox_le {q cw : ℝ} (hq₁ : q < 1) {K : ℕ} {CN c Ch κ CΦ x E₂ : ℝ}
    {M : ℕ → ℝ} {Φ : ℝ → ℝ} {k : ℕ} {u v : Fin (k + 1) → ℝ} {B : (Fin k → ℕ) → ℝ}
    (hE : EndpointData q cw K CN x u v B (normBound q K CN c E₂ x))
    (hV : ∀ a : ℝ, 1 / 10 ≤ a → 1 / 2 ≤ harmonicMass (band x a)) (hΦ : IsCutoff κ CΦ M x Φ)
    (hκ : 1 < κ) (hxκ : κ ≤ x) (hκx : κ * x ≤ x ^ 2) {r : ℕ}
    (hsf : ScaleFacts x (presieveExponent c Ch x) (r + 2) ⌊κ * x + 1⌋₊)
    (hγ1 : presieveExponent c Ch x ≤ 1) {c₃ cW SP : ℝ} {K' : ℕ} (hc₃ : 0 < c₃)
    (hlogY : 0 < Real.log (proxyCutoff x))
    (hPiY : c₃ / Real.log (proxyCutoff x) ≤ ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p))
    (hcW : 0 ≤ cW)
    (hcount : ∀ w : ℝ, 0 ≤ w → ∑ m ∈ Icc 1 ⌊κ * x + 1⌋₊,
      (if (m : ℝ) ≤ w then proxyEnv x (presieveExponent c Ch x) (r + 2) m else 0) ≤ cW * w)
    (hSP : ∑ p ∈ candidatePrimes x, Real.log p / p ≤ SP)
    (hK' : Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ 2 ^ K') :
    |∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 2) => Icc 1 ⌊κ * x + 1⌋₊),
        cutPsi Φ (endpoint q cw K CN x u v B) x (∏ i, m i) *
          ∏ i, unstrippedProxy x (presieveExponent c Ch x) (r + 2) (m i) -
      ∑ m ∈ Fintype.piFinset (fun _ : Fin (r + 2) => Icc 1 ⌊κ * x + 1⌋₊),
        cutPsi Φ (endpoint q cw K CN x u v B) x (∏ i, m i) *
          ∏ i, strippedProxy x (presieveExponent c Ch x) (r + 2) (m i)| ≤
      (r + 2) * bound5 q K CN c E₂ κ M x (presieveExponent c Ch x) cW SP c₃ K' r := by
  set γ := presieveExponent c Ch x
  set N := ⌊κ * x + 1⌋₊
  have hx := hsf.one_lt
  have hx0 : 0 < x := by linarith
  have hκ0 : 0 < κ := by linarith
  have hSE0 : 0 ≤ endBound q K CN c E₂ x := by
    have := hE.norm_pos
    unfold endBound
    have : 0 < 1 - q := by linarith
    positivity
  have hSE : ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ x ^ 2 →
      |endpoint q cw K CN x u v B h| ≤ endBound q K CN c E₂ x :=
    fun h h1 hh => abs_endpoint_le hq₁ hE hV h1 hh
  have hΨ0 : ∀ h, N < h → cutPsi Φ (endpoint q cw K CN x u v B) x h = 0 :=
    fun h hh => cutPsi_eq_zero hΦ hx0 hκ0 hh
  have hΨ := abs_cutPsi_le (E := endpoint q cw K CN x u v B) hΦ hx0 hκ0 hκx hxκ hSE0 hSE
  have hδ := sum_abs_delta_le (N := N) (j := r + 2) hx hsf.log_ge hsf.gamma_pos hγ1
    hsf.one_le_j hsf.cutoff_gt hsf.cutoff_le_N hc₃ hlogY hPiY hcount hSP hK'
  rw [sum_sub_sum_eq_steps]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [show ((r : ℝ) + 2) * bound5 q K CN c E₂ κ M x γ cW SP c₃ K' r =
    ∑ _i : Fin (r + 1 + 1), bound5 q K CN c E₂ κ M x γ cW SP c₃ K' r by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring]
  refine sum_le_sum fun i _ => ?_
  have hU0 : ∀ k m, 0 ≤ stepWeight5 x γ (r + 2) i k m := by
    intro k m
    unfold stepWeight5
    split_ifs
    · exact (strippedProxy_le hx hsf.log_ge hsf.gamma_pos hsf.one_le_j m).1
    · exact (unstrippedProxy_le hx hsf.log_ge hsf.gamma_pos hsf.one_le_j m).1
  have hU : ∀ k m, stepWeight5 x γ (r + 2) i k m ≤ proxyEnv x γ (r + 2) m := by
    intro k m
    by_cases h : i.succAbove k < i
    · simp only [stepWeight5, h, ↓reduceIte]
      exact (strippedProxy_le hx hsf.log_ge hsf.gamma_pos hsf.one_le_j m).2
    · simp only [stepWeight5, h, ↓reduceIte]
      exact (unstrippedProxy_le hx hsf.log_ge hsf.gamma_pos hsf.one_le_j m).2
  have hstep := abs_strip_step_le hsf.log_ge hsf.gamma_pos hsf.one_le_j hsf.prodY
    hsf.cutoff_gt hsf.cutoff_le_N _ hΨ0 hΨ hcW hcount (stepWeight5 x γ (r + 2) i) hU0 hU
  refine le_trans (le_of_eq ?_) (hstep.trans ?_)
  · rfl
  unfold bound5 highProd
  have hM0 : 0 ≤ M 0 := (abs_nonneg _).trans (by simpa using hΦ.2.2.2 0 0)
  have hP1 : 0 ≤ ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹ :=
    highProd_nonneg (by
      have : (1 : ℝ) < proxyCutoff x := by
        have := hsf.j_lt_cutoff
        have : (1 : ℝ) ≤ ((r + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 2 by omega)
        linarith
      exact this)
  exact mul_le_mul_of_nonneg_left hδ (by positivity)

end Erdos408.TypeII
