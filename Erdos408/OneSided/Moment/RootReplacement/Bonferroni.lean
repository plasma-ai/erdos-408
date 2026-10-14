module

public import Erdos408.OneSided.Analysis.Bonferroni
public import Erdos408.OneSided.Moment.PathExpansion.Average
public import Erdos408.OneSided.Moment.RootReplacement.Residues

/-!
# Root replacement on one box: Bonferroni and the monomial expansion

Steps 2–4 of the assembly in `blueprint/one_sided_type_ii.md` §15, for one configuration and
one box. The line factor is `F(ℓ) = ∏_p λ_p(ℓ_p)` over the band primes, with every
`λ_p ∈ [0, 1]`. Split the primes into a set `act` (kept exactly) and the rest, where
`λ_p = 1 - X_p` with `X_p ∈ [0, 1]`. By Bonferroni at degree `T` (RR3),

`F = F_act · (∑_{I, |I| < T} (-1)^{|I|} ∏_{p ∈ I} X_p) + O(e_T(X))`

pointwise, with `e_T(X) = ∑_{|I| = T} ∏_{p ∈ I} X_p ≥ 0`. Each monomial depends on the lines at
`act ∪ I` only, so RR4 with RR5 (`RootEquidist`) replaces its root sum by `c₂ U V |box|` times
its line average. The model mean of the gap is `𝔼 e_T(X) ≤ σ^T / T!`, where
`σ = ∑_{p ∉ act} 𝔼 X_p`, since the lines are independent.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

/-- The damping mass `σ = ∑_{p ∉ act} 𝔼 (1 - λ_p)` of the band primes outside `act`. -/
def dampMass (x : ℝ) (d : Data K) (act : Finset ℕ) (lam : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ bandPrimes x d \ act, ((p : ℝ) + 1)⁻¹ * ∑ l ∈ range (p + 1), (1 - lam p l)

/-- The damping mass is nonnegative for line factors at most `1`. -/
theorem dampMass_nonneg {x : ℝ} {d : Data K} {act : Finset ℕ} {lam : ℕ → ℕ → ℝ}
    (hlam : ∀ p ∈ bandPrimes x d, ∀ l, lam p l ≤ 1) : 0 ≤ dampMass x d act lam :=
  sum_nonneg fun p hp => mul_nonneg (by positivity)
    (sum_nonneg fun l _ => sub_nonneg.2 (hlam p (mem_sdiff.1 hp).1 l))

/-- The line average of a real function is the real average over the line assignments. -/
theorem lineAverage_ofReal (x : ℝ) (d : Data K) (g : (ℕ → ℕ) → ℝ) :
    lineAverage x d (fun ℓ => (g ℓ : ℂ)) =
      (((lineAssignments x d).card : ℝ)⁻¹ * ∑ ℓ ∈ lineAssignments x d, g ℓ : ℝ) := by
  push_cast [lineAverage]
  rfl

/-- The lines at distinct band primes are independent: the real average of
`∏_{p ∈ I} f_p(ℓ p)` over the line assignments is `∏_{p ∈ I} (p + 1)⁻¹ ∑_{l ≤ p} f_p(l)`. -/
theorem lineAssignments_prod (x : ℝ) (d : Data K) {I : Finset ℕ} (hI : I ⊆ bandPrimes x d)
    (f : ℕ → ℕ → ℝ) :
    ((lineAssignments x d).card : ℝ)⁻¹ * ∑ ℓ ∈ lineAssignments x d, ∏ p ∈ I, f p (ℓ p) =
      ∏ p ∈ I, (((p : ℝ) + 1)⁻¹ * ∑ l ∈ range (p + 1), f p l) := by
  classical
  have h := lineAverage_prod x d fun p l => if p ∈ I then (f p l : ℂ) else 1
  -- step: the product over the band primes is the product over `I`
  have hl : (fun ℓ : ℕ → ℕ => ∏ p ∈ bandPrimes x d, if p ∈ I then (f p (ℓ p) : ℂ) else 1) =
      fun ℓ => ((∏ p ∈ I, f p (ℓ p) : ℝ) : ℂ) := by
    funext ℓ
    rw [prod_ite_mem, inter_eq_right.2 hI]
    push_cast
    rfl
  have hr : ∏ p ∈ bandPrimes x d,
      (((p : ℂ) + 1)⁻¹ * ∑ l ∈ range (p + 1), if p ∈ I then (f p l : ℂ) else 1) =
        ((∏ p ∈ I, (((p : ℝ) + 1)⁻¹ * ∑ l ∈ range (p + 1), f p l) : ℝ) : ℂ) := by
    have hp1 : ∀ p : ℕ, (p : ℂ) + 1 ≠ 0 := fun p => by exact_mod_cast Nat.succ_ne_zero p
    rw [prod_congr rfl fun (p : ℕ) _ => show ((p : ℂ) + 1)⁻¹ *
        ∑ l ∈ range (p + 1), (if p ∈ I then (f p l : ℂ) else 1) =
          if p ∈ I then ((p : ℂ) + 1)⁻¹ * ∑ l ∈ range (p + 1), (f p l : ℂ) else 1 by
        by_cases hp : p ∈ I <;> simp [hp, hp1], prod_ite_mem, inter_eq_right.2 hI]
    push_cast
    rfl
  rw [hl, hr, lineAverage_ofReal] at h
  exact_mod_cast h

/-- `RootEquidist` for a real function `g` of the lines at a set `S` of at most `k` band
primes, bounded by `1`, normalized by `UV`: the root average over the box is
`c₂ |box|` times the line average up to `C₀ p_max^{6k} min(U, V)^{-1/5}`. -/
theorem abs_boxRoots_sub_le {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hE : RootEquidist K C₀) (x : ℝ)
    (d : Data K) {U V : ℝ} (hU : 2 ≤ U) (hV : 2 ≤ V) {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (ha₁ : 1 ≤ a₁)
    (hab₁ : a₁ ≤ b₁) (hb₁ : b₁ ≤ 16) (ha₂ : 1 ≤ a₂) (hab₂ : a₂ ≤ b₂) (hb₂ : b₂ ≤ 2)
    (ha₃ : 0 ≤ a₃) (hab₃ : a₃ ≤ b₃) (hb₃ : b₃ ≤ 1) {S : Finset ℕ} (hS : S ⊆ bandPrimes x d)
    (g : (ℕ → ℕ) → ℝ) (hg : ∀ ℓ ℓ' : ℕ → ℕ, (∀ p ∈ S, ℓ p = ℓ' p) → g ℓ = g ℓ')
    (hg₁ : ∀ ℓ, |g ℓ| ≤ 1) {pmax : ℝ} (hpmax₁ : 1 ≤ pmax)
    (hpmax : ∀ p ∈ bandPrimes x d, (p : ℝ) ≤ pmax) {k : ℕ} (hk : S.card ≤ k) :
    |(U * V)⁻¹ * ∑ P₀ ∈ boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃, g (rootLines P₀) -
        primitiveDensity * ((b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃)) *
          (((lineAssignments x d).card : ℝ)⁻¹ * ∑ ℓ ∈ lineAssignments x d, g ℓ)| ≤
      C₀ * pmax ^ (6 * k) * min U V ^ (-(1 / 5 : ℝ)) := by
  have h := hE x d U V hU hV a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂ hb₂ ha₃ hab₃ hb₃ S hS
    (fun ℓ => (g ℓ : ℂ)) 1 (fun ℓ ℓ' h => by rw [hg ℓ ℓ' h])
    (fun ℓ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hg₁ ℓ)
  rw [lineAverage_ofReal] at h
  set L := ((lineAssignments x d).card : ℝ)⁻¹ * ∑ ℓ ∈ lineAssignments x d, g ℓ
  set R₀ := ∑ P₀ ∈ boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃, g (rootLines P₀)
  have hc : ∑ P₀ ∈ boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃, (g (rootLines P₀) : ℂ) -
      ((primitiveDensity * U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) : ℝ) : ℂ) * (L : ℂ) =
        ((R₀ - primitiveDensity * U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) * L : ℝ) : ℂ) := by
    simp only [R₀]
    push_cast
    rfl
  rw [hc, Complex.norm_real, Real.norm_eq_abs] at h
  -- step: the modulus `S⁶ ≤ p_max^{6k}`
  have hprod : ∏ p ∈ S, (p : ℝ) ≤ pmax ^ k :=
    calc ∏ p ∈ S, (p : ℝ) ≤ ∏ _p ∈ S, pmax :=
          prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun p hp => hpmax p (hS hp)
      _ = pmax ^ S.card := prod_const _
      _ ≤ pmax ^ k := pow_le_pow_right₀ hpmax₁ hk
  have hprod6 : (∏ p ∈ S, (p : ℝ)) ^ 6 ≤ pmax ^ (6 * k) := by
    rw [mul_comm, pow_mul]
    exact pow_le_pow_left₀ (prod_nonneg fun _ _ => Nat.cast_nonneg _) hprod 6
  have hUV : 0 < U * V := by positivity
  have hm : 0 ≤ C₀ * min U V ^ (-(1 / 5 : ℝ)) :=
    mul_nonneg hC₀ (Real.rpow_nonneg (le_min (by linarith) (by linarith)) _)
  have hid : (U * V)⁻¹ * R₀ - primitiveDensity * ((b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃)) * L =
      (U * V)⁻¹ * (R₀ - primitiveDensity * U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) * L) := by
    field_simp
  rw [hid, abs_mul, abs_of_pos (inv_pos.2 hUV)]
  calc (U * V)⁻¹ * |R₀ - primitiveDensity * U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) * L|
      ≤ (U * V)⁻¹ * (1 * (∏ p ∈ S, (p : ℝ)) ^ 6 * (C₀ * U * V * min U V ^ (-(1 / 5 : ℝ)))) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 hUV.le)
    _ = (∏ p ∈ S, (p : ℝ)) ^ 6 * (C₀ * min U V ^ (-(1 / 5 : ℝ))) := by
        field_simp
    _ ≤ pmax ^ (6 * k) * (C₀ * min U V ^ (-(1 / 5 : ℝ))) :=
        mul_le_mul_of_nonneg_right hprod6 hm
    _ = C₀ * pmax ^ (6 * k) * min U V ^ (-(1 / 5 : ℝ)) := by ring

/-- The subsets of `s` of size at most `T` number at most `(#s + 1)^T`. -/
theorem card_powerset_card_lt_add_le (s : Finset ℕ) (T : ℕ) :
    ((s.powerset.filter fun I => I.card < T).card + (s.powersetCard T).card : ℝ) ≤
      ((s.card : ℝ) + 1) ^ T := by
  -- step: sort the subsets by size
  have hlt : (s.powerset.filter fun I => I.card < T).card =
      ∑ k ∈ range T, (s.powersetCard k).card := by
    rw [card_eq_sum_card_fiberwise (f := card) (t := range T)
      (fun I hI => mem_range.2 (mem_filter.1 hI).2)]
    refine sum_congr rfl fun k hk => ?_
    rw [powersetCard_eq_filter, filter_filter]
    exact congrArg _ (filter_congr fun I _ => ⟨fun h => h.2, fun h => ⟨h ▸ mem_range.1 hk, h⟩⟩)
  have hnat : (s.powerset.filter fun I => I.card < T).card + (s.powersetCard T).card ≤
      (s.card + 1) ^ T := by
    rw [hlt, ← sum_range_succ (fun k => (s.powersetCard k).card), add_pow]
    refine sum_le_sum fun k hk => ?_
    rw [card_powersetCard, one_pow, mul_one]
    exact (Nat.choose_le_pow _ _).trans
      (Nat.le_mul_of_pos_right _ (Nat.choose_pos (Nat.lt_succ_iff.1 (mem_range.1 hk))))
  exact_mod_cast hnat

/-- **Root replacement on one box.** For a product `F = ∏_p λ_p` of line factors in `[0, 1]`,
`(UV)⁻¹ ∑_{P₀ ∈ box} F(ℓ(P₀))` is `c₂ |box| 𝔼_ℓ F` up to the Bonferroni gap
`4 |box| σ^T / T!` and the root-count errors of the at most `(n + 1)^T` monomials, each with
modulus at most `p_max^{|act| + T}`. Here `n` is the number of band primes. -/
theorem norm_boxRoots_prod_sub_le {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hE : RootEquidist K C₀) (x : ℝ)
    (d : Data K) {U V : ℝ} (hU : 2 ≤ U) (hV : 2 ≤ V) {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (ha₁ : 1 ≤ a₁)
    (hab₁ : a₁ ≤ b₁) (hb₁ : b₁ ≤ 16) (ha₂ : 1 ≤ a₂) (hab₂ : a₂ ≤ b₂) (hb₂ : b₂ ≤ 2)
    (ha₃ : 0 ≤ a₃) (hab₃ : a₃ ≤ b₃) (hb₃ : b₃ ≤ 1) (lam : ℕ → ℕ → ℝ)
    (hlam : ∀ p ∈ bandPrimes x d, ∀ l, 0 ≤ lam p l ∧ lam p l ≤ 1) (act : Finset ℕ)
    (hact : act ⊆ bandPrimes x d) (T : ℕ) {pmax : ℝ} (hpmax₁ : 1 ≤ pmax)
    (hpmax : ∀ p ∈ bandPrimes x d, (p : ℝ) ≤ pmax) :
    ‖((U * V : ℝ) : ℂ)⁻¹ * ∑ P₀ ∈ boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃,
          ∏ p ∈ bandPrimes x d, (lam p (rootLines P₀ p) : ℂ) -
        ((primitiveDensity * ((b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃)) : ℝ) : ℂ) *
          lineAverage x d (fun ℓ => ∏ p ∈ bandPrimes x d, (lam p (ℓ p) : ℂ))‖ ≤
      4 * ((b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃)) * dampMass x d act lam ^ T / T.factorial +
        (((bandPrimes x d).card : ℝ) + 1) ^ T * C₀ * pmax ^ (6 * (act.card + T)) *
          min U V ^ (-(1 / 5 : ℝ)) := by
  classical
  -- step: the line factor, the monomials and the gap monomials as real functions of the lines
  obtain ⟨F, hF⟩ : ∃ F : (ℕ → ℕ) → ℝ, F = fun ℓ => ∏ p ∈ bandPrimes x d, lam p (ℓ p) :=
    ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Finset ℕ → (ℕ → ℕ) → ℝ, g = fun I ℓ =>
      (-1) ^ I.card * ((∏ p ∈ act, lam p (ℓ p)) * ∏ p ∈ I, (1 - lam p (ℓ p))) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : Finset ℕ → (ℕ → ℕ) → ℝ, h = fun I ℓ => ∏ p ∈ I, (1 - lam p (ℓ p)) :=
    ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset ℕ, Q = bandPrimes x d \ act := ⟨_, rfl⟩
  have hQP : Q ⊆ bandPrimes x d := hQ ▸ sdiff_subset
  -- step: pass to real quantities
  have hgoal : ((U * V : ℝ) : ℂ)⁻¹ * ∑ P₀ ∈ boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃,
          ∏ p ∈ bandPrimes x d, (lam p (rootLines P₀ p) : ℂ) -
        ((primitiveDensity * ((b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃)) : ℝ) : ℂ) *
          lineAverage x d (fun ℓ => ∏ p ∈ bandPrimes x d, (lam p (ℓ p) : ℂ)) =
      (((U * V)⁻¹ * ∑ P₀ ∈ boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃, F (rootLines P₀) -
        primitiveDensity * ((b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃)) *
          (((lineAssignments x d).card : ℝ)⁻¹ * ∑ ℓ ∈ lineAssignments x d, F ℓ) : ℝ) : ℂ) := by
    subst hF
    push_cast [lineAverage]
    rfl
  rw [hgoal, Complex.norm_real, Real.norm_eq_abs]
  set box := boxRoots U V a₁ b₁ a₂ b₂ a₃ b₃ with hbox
  set LA := lineAssignments x d with hLA
  set w := (U * V)⁻¹ with hw
  set z := (LA.card : ℝ)⁻¹ with hz
  set vol := (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) with hvol
  set c := primitiveDensity with hc
  have hw0 : 0 ≤ w := inv_nonneg.2 (by positivity)
  have hz0 : 0 ≤ z := inv_nonneg.2 (Nat.cast_nonneg _)
  have hvol0 : 0 ≤ vol :=
    mul_nonneg (mul_nonneg (sub_nonneg.2 hab₁) (sub_nonneg.2 hab₂)) (sub_nonneg.2 hab₃)
  have hc2 : |c| ≤ 2 := RootResidue.abs_primitiveDensity_le
  have herr : 0 ≤ C₀ * pmax ^ (6 * (act.card + T)) * min U V ^ (-(1 / 5 : ℝ)) :=
    mul_nonneg (mul_nonneg hC₀ (pow_nonneg (by linarith) _))
      (Real.rpow_nonneg (le_min (by linarith) (by linarith)) _)
  -- step: the factors lie in `[0, 1]`
  have hact₀ : ∀ ℓ : ℕ → ℕ, 0 ≤ ∏ p ∈ act, lam p (ℓ p) := fun ℓ =>
    prod_nonneg fun p hp => (hlam p (hact hp) (ℓ p)).1
  have hact₁ : ∀ ℓ : ℕ → ℕ, ∏ p ∈ act, lam p (ℓ p) ≤ 1 := fun ℓ =>
    prod_le_one₀ (fun p hp => (hlam p (hact hp) (ℓ p)).1) fun p hp => (hlam p (hact hp) (ℓ p)).2
  have hX : ∀ ℓ : ℕ → ℕ, ∀ p ∈ Q, 0 ≤ 1 - lam p (ℓ p) ∧ 1 - lam p (ℓ p) ≤ 1 := fun ℓ p hp => by
    obtain ⟨h0, h1⟩ := hlam p (hQP hp) (ℓ p)
    constructor <;> linarith
  have hh₀ : ∀ ℓ, ∀ I ⊆ Q, 0 ≤ h I ℓ := fun ℓ I hI => by
    rw [hh]
    exact prod_nonneg fun p hp => (hX ℓ p (hI hp)).1
  have hh₁ : ∀ ℓ, ∀ I ⊆ Q, h I ℓ ≤ 1 := fun ℓ I hI => by
    rw [hh]
    exact prod_le_one₀ (fun p hp => (hX ℓ p (hI hp)).1) fun p hp => (hX ℓ p (hI hp)).2
  -- step: Bonferroni, pointwise
  have hFB : ∀ ℓ, |F ℓ - ∑ I ∈ Q.powerset.filter (fun I => I.card < T), g I ℓ| ≤
      ∑ I ∈ Q.powersetCard T, h I ℓ := by
    intro ℓ
    have hB := abs_prod_one_sub_sub_le Q (fun p => 1 - lam p (ℓ p)) (hX ℓ) T
    simp only [sub_sub_cancel] at hB
    have hid : F ℓ - ∑ I ∈ Q.powerset.filter (fun I => I.card < T), g I ℓ =
        (∏ p ∈ act, lam p (ℓ p)) * (∏ p ∈ Q, lam p (ℓ p) -
          ∑ I ∈ Q.powerset.filter (fun I => I.card < T),
            (-1) ^ I.card * ∏ p ∈ I, (1 - lam p (ℓ p))) := by
      simp only [hF, hg]
      rw [← prod_sdiff hact, ← hQ, mul_sub, mul_sum]
      congr 1
      · ring
      · exact sum_congr rfl fun I _ => by ring
    have hE₀ : 0 ≤ ∑ I ∈ Q.powersetCard T, h I ℓ :=
      sum_nonneg fun I hI => hh₀ ℓ I (mem_powersetCard.1 hI).1
    rw [hid, abs_mul, abs_of_nonneg (hact₀ ℓ)]
    calc (∏ p ∈ act, lam p (ℓ p)) * |∏ p ∈ Q, lam p (ℓ p) -
          ∑ I ∈ Q.powerset.filter (fun I => I.card < T),
            (-1) ^ I.card * ∏ p ∈ I, (1 - lam p (ℓ p))|
        ≤ (∏ p ∈ act, lam p (ℓ p)) * ∑ I ∈ Q.powersetCard T, h I ℓ := by
          rw [hh]
          exact mul_le_mul_of_nonneg_left hB (hact₀ ℓ)
      _ ≤ 1 * ∑ I ∈ Q.powersetCard T, h I ℓ := mul_le_mul_of_nonneg_right (hact₁ ℓ) hE₀
      _ = ∑ I ∈ Q.powersetCard T, h I ℓ := one_mul _
  -- step: root equidistribution for each monomial
  have hgI : ∀ I ∈ Q.powerset.filter (fun I => I.card < T),
      |w * ∑ P₀ ∈ box, g I (rootLines P₀) - c * vol * (z * ∑ ℓ ∈ LA, g I ℓ)| ≤
        C₀ * pmax ^ (6 * (act.card + T)) * min U V ^ (-(1 / 5 : ℝ)) := by
    intro I hI
    obtain ⟨hIQ, hIT⟩ := mem_filter.1 hI
    have hIQ' := mem_powerset.1 hIQ
    refine abs_boxRoots_sub_le hC₀ hE x d hU hV ha₁ hab₁ hb₁ ha₂ hab₂ hb₂ ha₃ hab₃ hb₃
      (union_subset hact (hIQ'.trans hQP)) (g I) (fun ℓ ℓ' hl => ?_) (fun ℓ => ?_) hpmax₁ hpmax
      ((card_union_le _ _).trans (by omega))
    · have h1 : ∏ p ∈ act, lam p (ℓ p) = ∏ p ∈ act, lam p (ℓ' p) :=
        prod_congr rfl fun p hp => by rw [hl p (mem_union_left _ hp)]
      have h2 : ∏ p ∈ I, (1 - lam p (ℓ p)) = ∏ p ∈ I, (1 - lam p (ℓ' p)) :=
        prod_congr rfl fun p hp => by rw [hl p (mem_union_right _ hp)]
      simp only [hg]
      rw [h1, h2]
    · have h0 := hh₀ ℓ I hIQ'
      have h1 := hh₁ ℓ I hIQ'
      rw [hh] at h0 h1
      simp only [hg]
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (mul_nonneg (hact₀ ℓ) h0)]
      calc (∏ p ∈ act, lam p (ℓ p)) * ∏ p ∈ I, (1 - lam p (ℓ p)) ≤ 1 * 1 :=
            mul_le_mul (hact₁ ℓ) h1 h0 zero_le_one
        _ = 1 := one_mul 1
  have hhI : ∀ I ∈ Q.powersetCard T,
      |w * ∑ P₀ ∈ box, h I (rootLines P₀) - c * vol * (z * ∑ ℓ ∈ LA, h I ℓ)| ≤
        C₀ * pmax ^ (6 * (act.card + T)) * min U V ^ (-(1 / 5 : ℝ)) := by
    intro I hI
    obtain ⟨hIQ, hIT⟩ := mem_powersetCard.1 hI
    refine abs_boxRoots_sub_le hC₀ hE x d hU hV ha₁ hab₁ hb₁ ha₂ hab₂ hb₂ ha₃ hab₃ hb₃
      (hIQ.trans hQP) (h I) (fun ℓ ℓ' hl => ?_) (fun ℓ => ?_) hpmax₁ hpmax (by omega)
    · simp only [hh]
      exact prod_congr rfl fun p hp => by rw [hl p hp]
    · rw [abs_of_nonneg (hh₀ ℓ I hIQ)]
      exact hh₁ ℓ I hIQ
  -- step: the root average and the line average are linear
  have hsum : ∀ (s : Finset (Finset ℕ)) (f : Finset ℕ → (ℕ → ℕ) → ℝ),
      w * ∑ P₀ ∈ box, ∑ I ∈ s, f I (rootLines P₀) - c * vol * (z * ∑ ℓ ∈ LA, ∑ I ∈ s, f I ℓ) =
        ∑ I ∈ s, (w * ∑ P₀ ∈ box, f I (rootLines P₀) - c * vol * (z * ∑ ℓ ∈ LA, f I ℓ)) := by
    intro s f
    rw [sum_comm, sum_comm (s := LA), mul_sum s, mul_sum s, mul_sum s, ← sum_sub_distrib]
  have hdev : ∀ (s : Finset (Finset ℕ)) (f : Finset ℕ → (ℕ → ℕ) → ℝ),
      (∀ I ∈ s, |w * ∑ P₀ ∈ box, f I (rootLines P₀) - c * vol * (z * ∑ ℓ ∈ LA, f I ℓ)| ≤
        C₀ * pmax ^ (6 * (act.card + T)) * min U V ^ (-(1 / 5 : ℝ))) →
      |w * ∑ P₀ ∈ box, ∑ I ∈ s, f I (rootLines P₀) - c * vol * (z * ∑ ℓ ∈ LA, ∑ I ∈ s, f I ℓ)| ≤
        s.card * (C₀ * pmax ^ (6 * (act.card + T)) * min U V ^ (-(1 / 5 : ℝ))) := by
    intro s f hf
    rw [hsum]
    calc _ ≤ ∑ I ∈ s, |w * ∑ P₀ ∈ box, f I (rootLines P₀) - c * vol * (z * ∑ ℓ ∈ LA, f I ℓ)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _I ∈ s, C₀ * pmax ^ (6 * (act.card + T)) * min U V ^ (-(1 / 5 : ℝ)) := sum_le_sum hf
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hdB := hdev _ g hgI
  have hdE := hdev _ h hhI
  -- step: the Bonferroni gap in the root average and the line average
  have hRgap : |w * ∑ P₀ ∈ box, (F (rootLines P₀) -
      ∑ I ∈ Q.powerset.filter (fun I => I.card < T), g I (rootLines P₀))| ≤
        w * ∑ P₀ ∈ box, ∑ I ∈ Q.powersetCard T, h I (rootLines P₀) := by
    rw [abs_mul, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_left
      ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun P₀ _ => hFB _)) hw0
  have hAgap : |z * ∑ ℓ ∈ LA, (F ℓ - ∑ I ∈ Q.powerset.filter (fun I => I.card < T), g I ℓ)| ≤
      z * ∑ ℓ ∈ LA, ∑ I ∈ Q.powersetCard T, h I ℓ := by
    rw [abs_mul, abs_of_nonneg hz0]
    exact mul_le_mul_of_nonneg_left
      ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ℓ _ => hFB _)) hz0
  -- step: the model mean of the gap is at most `σ^T / T!`
  have hAE₀ : 0 ≤ z * ∑ ℓ ∈ LA, ∑ I ∈ Q.powersetCard T, h I ℓ :=
    mul_nonneg hz0 (sum_nonneg fun ℓ _ => sum_nonneg fun I hI =>
      hh₀ ℓ I (mem_powersetCard.1 hI).1)
  have hAE : z * ∑ ℓ ∈ LA, ∑ I ∈ Q.powersetCard T, h I ℓ ≤
      dampMass x d act lam ^ T / T.factorial := by
    rw [sum_comm, mul_sum]
    have hσ : dampMass x d act lam =
        ∑ p ∈ Q, ((p : ℝ) + 1)⁻¹ * ∑ l ∈ range (p + 1), (1 - lam p l) := by
      rw [hQ]
      rfl
    rw [hσ]
    calc ∑ I ∈ Q.powersetCard T, z * ∑ ℓ ∈ LA, h I ℓ =
        ∑ I ∈ Q.powersetCard T,
          ∏ p ∈ I, (((p : ℝ) + 1)⁻¹ * ∑ l ∈ range (p + 1), (1 - lam p l)) := by
          refine sum_congr rfl fun I hI => ?_
          simp only [hh]
          exact lineAssignments_prod x d ((mem_powersetCard.1 hI).1.trans hQP)
            fun p l => 1 - lam p l
      _ ≤ _ := sum_powersetCard_prod_le Q _ (fun p hp => mul_nonneg (by positivity)
          (sum_nonneg fun l _ => sub_nonneg.2 (hlam p (hQP hp) l).2)) T
  -- step: count the monomials
  have hcard : ((Q.powerset.filter fun I => I.card < T).card + (Q.powersetCard T).card : ℝ) ≤
      (((bandPrimes x d).card : ℝ) + 1) ^ T :=
    (card_powerset_card_lt_add_le Q T).trans (pow_le_pow_left₀ (by positivity)
      (by gcongr) T)
  -- step: assemble
  have hsplitR : w * ∑ P₀ ∈ box, F (rootLines P₀) =
      w * ∑ P₀ ∈ box, (F (rootLines P₀) -
        ∑ I ∈ Q.powerset.filter (fun I => I.card < T), g I (rootLines P₀)) +
      w * ∑ P₀ ∈ box, ∑ I ∈ Q.powerset.filter (fun I => I.card < T), g I (rootLines P₀) := by
    rw [← mul_add, ← sum_add_distrib]
    simp only [sub_add_cancel]
  have hsplitA : z * ∑ ℓ ∈ LA, F ℓ =
      z * ∑ ℓ ∈ LA, (F ℓ - ∑ I ∈ Q.powerset.filter (fun I => I.card < T), g I ℓ) +
      z * ∑ ℓ ∈ LA, ∑ I ∈ Q.powerset.filter (fun I => I.card < T), g I ℓ := by
    rw [← mul_add, ← sum_add_distrib]
    simp only [sub_add_cancel]
  rw [hsplitR, hsplitA]
  set a := w * ∑ P₀ ∈ box, (F (rootLines P₀) -
    ∑ I ∈ Q.powerset.filter (fun I => I.card < T), g I (rootLines P₀))
  set b := z * ∑ ℓ ∈ LA, (F ℓ - ∑ I ∈ Q.powerset.filter (fun I => I.card < T), g I ℓ)
  set rB := w * ∑ P₀ ∈ box, ∑ I ∈ Q.powerset.filter (fun I => I.card < T), g I (rootLines P₀)
  set aB := z * ∑ ℓ ∈ LA, ∑ I ∈ Q.powerset.filter (fun I => I.card < T), g I ℓ
  set rE := w * ∑ P₀ ∈ box, ∑ I ∈ Q.powersetCard T, h I (rootLines P₀)
  set aE := z * ∑ ℓ ∈ LA, ∑ I ∈ Q.powersetCard T, h I ℓ
  set e := C₀ * pmax ^ (6 * (act.card + T)) * min U V ^ (-(1 / 5 : ℝ))
  have htri : |a + rB - c * vol * (b + aB)| ≤ |a| + |c * vol * b| + |rB - c * vol * aB| := by
    have := abs_add_three a (-(c * vol * b)) (rB - c * vol * aB)
    rw [abs_neg] at this
    convert this using 2
    ring
  have hcv : |c * vol| ≤ 2 * vol := by
    rw [abs_mul, abs_of_nonneg hvol0]
    exact mul_le_mul_of_nonneg_right hc2 hvol0
  have hb : |c * vol * b| ≤ 2 * vol * aE := by
    rw [abs_mul]
    exact mul_le_mul hcv hAgap (abs_nonneg _) (by positivity)
  have hcE : c * vol * aE ≤ 2 * vol * aE :=
    mul_le_mul_of_nonneg_right ((le_abs_self _).trans hcv) hAE₀
  have h4 : 4 * vol * aE ≤ 4 * vol * dampMass x d act lam ^ T / T.factorial := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hAE (by positivity)
  have hce : ((Q.powerset.filter fun I => I.card < T).card : ℝ) * e +
      (Q.powersetCard T).card * e ≤
        (((bandPrimes x d).card : ℝ) + 1) ^ T * C₀ * pmax ^ (6 * (act.card + T)) *
          min U V ^ (-(1 / 5 : ℝ)) := by
    rw [← add_mul]
    calc _ ≤ (((bandPrimes x d).card : ℝ) + 1) ^ T * e := mul_le_mul_of_nonneg_right hcard herr
      _ = _ := by simp only [e]; ring
  have hrE := abs_le.1 hdE
  linarith [abs_le.1 hRgap, abs_nonneg a]

end Erdos408.OneSided
