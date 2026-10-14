module

public import Erdos408.Extraction.TypeII.Bands

/-!
# Expanding the endpoint into monomials

Write `y_{c,i} = c_w w_{c,i}` for the band weights. Each cluster factor expands as

  `1 - ∏_i (1 - y_{c,i}) = ∑_{∅ ≠ S_c} -(-c_w)^{|S_c|} ∏_{i ∈ S_c} w_{c,i}`,

so `P = ∑_S coeff(S) ∏_c ∏_{i ∈ S_c} w_{c,i}` over choices `S = (S_c)` of nonempty sets
of bands, one per cluster. In each monomial the least band `i_c ∈ S_c` of each cluster is
distinguished. The product of the `K` distinguished weights is the marked weight of
`OneSidedTypeII`, and the rest, with `f_𝔟 - C_𝔟`, is the remainder `R_S`:

  `P (f_𝔟 - C_𝔟) = ∑_S 𝒲_S · R_S`,  `R_S = coeff(S) ∏_c ∏_{i ∈ S_c, i ≠ i_c} w_{c,i} (f_𝔟 - C_𝔟)`.

`R_S` is invariant under the primes of the distinguished bands, since the bands are disjoint
and the slot primes are large.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real

/-- The choices of a nonempty set of bands in each of `K` clusters of `N'` bands. -/
def clusterSets (K N' : ℕ) : Finset (Fin K → Finset ℕ) :=
  Fintype.piFinset fun _ => (range N').powerset.erase ∅

theorem mem_clusterSets {K N' : ℕ} {S : Fin K → Finset ℕ} :
    S ∈ clusterSets K N' ↔ ∀ c, (S c).Nonempty ∧ S c ⊆ range N' := by
  simp only [clusterSets, Fintype.mem_piFinset, mem_erase, mem_powerset,
    Finset.nonempty_iff_ne_empty]

/-- The distinguished (least) band of cluster `c`. -/
noncomputable def distIndex {K : ℕ} (S : Fin K → Finset ℕ) (c : Fin K) : ℕ :=
  if h : (S c).Nonempty then (S c).min' h else 0

/-- The exponent of the distinguished band of cluster `c`. -/
noncomputable def distExponent (K : ℕ) (x : ℝ) (S : Fin K → Finset ℕ) (c : Fin K) : ℝ :=
  inertExponent K x c (distIndex S c)

/-- The coefficient `∏_c -(-c_w)^{|S_c|}` of a monomial. -/
noncomputable def monoCoeff (cw : ℝ) {K : ℕ} (S : Fin K → Finset ℕ) : ℝ :=
  ∏ c, -(-cw) ^ (S c).card

/-- The remainder `R_S`: the coefficient, the non-distinguished band weights and the
centred slot statistic. -/
noncomputable def monoRest (q cw : ℝ) (K : ℕ) (x : ℝ) {k : ℕ} (u v : Fin (k + 1) → ℝ)
    (B : (Fin k → ℕ) → ℝ) (S : Fin K → Finset ℕ) (h : ℕ) : ℝ :=
  monoCoeff cw S *
    (∏ c, ∏ i ∈ (S c).erase (distIndex S c), bandWeight q x (inertExponent K x c i) h) *
      (slotCount x u v B h - slotMean x u v B)

theorem distIndex_mem {K : ℕ} {S : Fin K → Finset ℕ} {c : Fin K} (h : (S c).Nonempty) :
    distIndex S c ∈ S c := by
  simp only [distIndex, h, ↓reduceDIte]
  exact min'_mem _ _

/-- `1 - ∏_{i ∈ s} (1 - y_i) = ∑_{∅ ≠ t ⊆ s} -∏_{i ∈ t} (-y_i)`. -/
theorem one_sub_prod_one_sub (s : Finset ℕ) (y : ℕ → ℝ) :
    1 - ∏ i ∈ s, (1 - y i) = ∑ t ∈ s.powerset.erase ∅, -∏ i ∈ t, (-y i) := by
  have h := prod_one_add (f := fun i => -y i) s
  simp only [← sub_eq_add_neg] at h
  rw [h, ← add_sum_erase _ _ (empty_mem_powerset s), prod_empty, sum_neg_distrib]
  ring

/-- The monomial expansion `P (f_𝔟 - C_𝔟) = ∑_S 𝒲_S R_S`. -/
theorem endpoint_eq_sum (q cw : ℝ) (hq : q ≠ 0) (K : ℕ) (CN x : ℝ) {k : ℕ}
    (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) (h : ℕ) :
    endpoint q cw K CN x u v B h =
      ∑ S ∈ clusterSets K (inertPerCluster K CN x),
        markedWeight Finset.univ q (fun c => band x (distExponent K x S c)) h *
          monoRest q cw K x u v B S h := by
  set N' := inertPerCluster K CN x
  set w : ℕ → ℕ → ℝ := fun c i => bandWeight q x (inertExponent K x c i) h with hw
  have hP : inertPoly q cw K CN x h = ∏ c : Fin K, ∑ t ∈ (range N').powerset.erase ∅,
      -(-cw) ^ t.card * ∏ i ∈ t, w c i := by
    unfold inertPoly
    rw [← Fin.prod_univ_eq_prod_range]
    refine prod_congr rfl fun c _ => ?_
    rw [one_sub_prod_one_sub]
    refine sum_congr rfl fun t _ => ?_
    rw [show (fun i => -(cw * bandWeight q x (inertExponent K x c i) h)) =
      fun i => -cw * w c i from funext fun i => by simp [hw]]
    rw [prod_mul_distrib, prod_const]
    ring
  unfold endpoint
  rw [hP, prod_univ_sum, sum_mul]
  refine sum_congr rfl fun S hS => ?_
  have hne := fun c => ((mem_clusterSets.1 hS) c).1
  have hsplit : ∀ c, ∏ i ∈ S c, w c i = w c (distIndex S c) *
      ∏ i ∈ (S c).erase (distIndex S c), w c i := fun c =>
    (mul_prod_erase _ _ (distIndex_mem (hne c))).symm
  have hprod : (∏ c : Fin K, -(-cw) ^ (S c).card * ∏ i ∈ S c, w c i) =
      (∏ c, -(-cw) ^ (S c).card) * ((∏ c : Fin K, w c (distIndex S c)) *
        ∏ c : Fin K, ∏ i ∈ (S c).erase (distIndex S c), w c i) := by
    rw [prod_mul_distrib, ← prod_mul_distrib (f := fun c : Fin K => w c (distIndex S c))]
    congr 1
    exact prod_congr rfl fun c _ => hsplit c
  rw [hprod, markedWeight_eq_prod hq]
  unfold monoRest monoCoeff distExponent
  simp only [hw]
  ring

theorem card_clusterSets_le (K N' : ℕ) : ((clusterSets K N').card : ℝ) ≤ 2 ^ (K * N') := by
  unfold clusterSets
  rw [Fintype.card_piFinset_const, card_erase_of_mem (empty_mem_powerset _), card_powerset,
    card_range]
  push_cast
  rw [pow_mul']
  gcongr
  exact_mod_cast Nat.sub_le _ _

/-- The remainder is at most `(2/(1-q))^{K N'} |f_𝔟 - C_𝔟|` when every band has harmonic mass
at least `1/2`. -/
theorem abs_monoRest_le {q cw : ℝ} (hq : 0 < q) (hq₁ : q < 1) (hcw : 0 ≤ cw) (hcw₁ : cw ≤ 1)
    {K N' : ℕ} {x : ℝ} {k : ℕ} (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ)
    {S : Fin K → Finset ℕ} (hS : S ∈ clusterSets K N')
    (hV : ∀ (c : Fin K) i, i < N' → 1 / 2 ≤ harmonicMass (band x (inertExponent K x c i)))
    (h : ℕ) :
    |monoRest q cw K x u v B S h| ≤
      (2 / (1 - q)) ^ (K * N') * |slotCount x u v B h - slotMean x u v B| := by
  have hC1 : (1 : ℝ) ≤ 2 / (1 - q) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hcoeff : |monoCoeff cw S| ≤ 1 := by
    unfold monoCoeff
    rw [abs_prod]
    refine prod_le_one₀ (fun _ _ => abs_nonneg _) fun c _ => ?_
    rw [abs_neg, abs_pow, abs_neg, abs_of_nonneg hcw]
    exact pow_le_one₀ hcw hcw₁
  have hw : ∀ (c : Fin K) i, i < N' → 0 ≤ bandWeight q x (inertExponent K x c i) h ∧
      bandWeight q x (inertExponent K x c i) h ≤ 2 / (1 - q) := by
    intro c i hi
    refine ⟨bandWeight_nonneg hq _ _ _,
      (bandWeight_le hq hq₁ _ _ _ (by linarith [hV c i hi])).trans ?_⟩
    rw [div_le_div_iff₀ (by nlinarith [hV c i hi]) (by linarith)]
    nlinarith [hV c i hi]
  have hrest0 : 0 ≤ ∏ c, ∏ i ∈ (S c).erase (distIndex S c),
      bandWeight q x (inertExponent K x c i) h :=
    prod_nonneg fun c _ => prod_nonneg fun i _ => bandWeight_nonneg hq _ _ _
  have hrest : ∏ c, ∏ i ∈ (S c).erase (distIndex S c),
      bandWeight q x (inertExponent K x c i) h ≤ (2 / (1 - q)) ^ (K * N') := by
    rw [show (2 / (1 - q)) ^ (K * N') = ∏ _c : Fin K, (2 / (1 - q)) ^ N' by
      rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm]]
    refine prod_le_prod₀ (fun c _ => prod_nonneg fun i _ => bandWeight_nonneg hq _ _ _)
      fun c _ => ?_
    have hsub := ((mem_clusterSets.1 hS) c).2
    calc ∏ i ∈ (S c).erase (distIndex S c), bandWeight q x (inertExponent K x c i) h
        ≤ ∏ _i ∈ (S c).erase (distIndex S c), 2 / (1 - q) :=
          prod_le_prod₀ (fun i _ => bandWeight_nonneg hq _ _ _) fun i hi =>
            (hw c i (mem_range.1 (hsub (mem_of_mem_erase hi)))).2
      _ = (2 / (1 - q)) ^ ((S c).erase (distIndex S c)).card := prod_const _
      _ ≤ (2 / (1 - q)) ^ N' := by
          refine pow_le_pow_right₀ hC1 ?_
          calc ((S c).erase (distIndex S c)).card ≤ (S c).card := card_erase_le
            _ ≤ (range N').card := card_le_card hsub
            _ = N' := card_range N'
  unfold monoRest
  rw [abs_mul, abs_mul, abs_of_nonneg hrest0]
  have h1 := mul_le_mul hcoeff hrest hrest0 zero_le_one
  rw [one_mul] at h1
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

/-- The remainder is invariant under the primes of a distinguished band. -/
theorem monoRest_prime_mul {q cw : ℝ} {K N' : ℕ} {x : ℝ} {k : ℕ} (u v : Fin (k + 1) → ℝ)
    (B : (Fin k → ℕ) → ℝ) {S : Fin K → Finset ℕ} (hS : S ∈ clusterSets K N')
    (hdisj : ∀ (c c' : Fin K) (i i' : ℕ), i < N' → i' < N' → (c ≠ c' ∨ i ≠ i') →
      Disjoint (band x (inertExponent K x c i)) (band x (inertExponent K x c' i')))
    (c₀ : Fin K) {p : ℕ} (hp : p ∈ band x (distExponent K x S c₀))
    (hpu : ∀ i, (p : ℝ) ≤ x ^ u i) (h : ℕ) :
    monoRest q cw K x u v B S (p * h) = monoRest q cw K x u v B S h := by
  unfold monoRest
  rw [slotCount_prime_mul u v B (band_prime hp) hpu]
  congr 2
  refine prod_congr rfl fun c _ => prod_congr rfl fun i hi => ?_
  have hsub := ((mem_clusterSets.1 hS) c).2
  have hsub₀ := ((mem_clusterSets.1 hS) c₀).2
  have hi' : i < N' := mem_range.1 (hsub (mem_of_mem_erase hi))
  have hd₀ : distIndex S c₀ < N' :=
    mem_range.1 (hsub₀ (distIndex_mem ((mem_clusterSets.1 hS) c₀).1))
  refine bandWeight_prime_mul (hdisj c c₀ i (distIndex S c₀) hi' hd₀ ?_) hp h
  by_cases hc : c = c₀
  · subst hc; exact Or.inr (ne_of_mem_erase hi)
  · exact Or.inl hc

/-! ### The cluster layout -/

section Layout

variable {K : ℕ} {x : ℝ}

/-- Under `2 (N' + 1) K ≤ T / 25`, the band exponents lie in `[0.11, 0.19]`. -/
theorem inertExponent_mem (hK : 1 ≤ K) {N' : ℕ} (hT : 0 < logLog x)
    (hlay : 2 * ((N' : ℝ) + 1) * K ≤ 4 / 100 * logLog x) {c i : ℕ} (hc : c < K)
    (hi : i < N') :
    11 / 100 ≤ inertExponent K x c i ∧ inertExponent K x c i ≤ 19 / 100 := by
  unfold inertExponent
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hc' : (c : ℝ) + 1 ≤ K := by exact_mod_cast hc
  have hi' : (i : ℝ) ≤ N' := by exact_mod_cast hi.le
  have h1 : (i : ℝ) * (2 / logLog x) ≤ 4 / 100 / K := by
    rw [mul_div_assoc', div_le_div_iff₀ hT (by linarith)]
    nlinarith
  have h2 : (c : ℝ) * (8 / 100 / K) ≤ 8 / 100 - 8 / 100 / K := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith), sub_mul, div_mul_cancel₀ _ (by linarith)]
    nlinarith
  have h3 : 0 ≤ (c : ℝ) * (8 / 100 / K) := by positivity
  have h4 : 0 ≤ (i : ℝ) * (2 / logLog x) := by positivity
  have h5 : 4 / 100 / (K : ℝ) ≤ 8 / 100 / K :=
    div_le_div_of_nonneg_right (by norm_num) (by linarith)
  have h6 : 0 ≤ 4 / 100 / (K : ℝ) := by positivity
  constructor <;> linarith

/-- Distinct bands of the layout are separated by at least `1 / T`. -/
theorem inertExponent_sep (hK : 1 ≤ K) {N' : ℕ} (hT : 0 < logLog x)
    (hlay : 2 * ((N' : ℝ) + 1) * K ≤ 4 / 100 * logLog x) {c c' i i' : ℕ} (hi : i < N')
    (hi' : i' < N') (hne : c ≠ c' ∨ i ≠ i') :
    inertExponent K x c i + 1 / logLog x ≤ inertExponent K x c' i' ∨
      inertExponent K x c' i' + 1 / logLog x ≤ inertExponent K x c i := by
  unfold inertExponent
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hiN : (i : ℝ) ≤ N' := by exact_mod_cast hi.le
  have hiN' : (i' : ℝ) ≤ N' := by exact_mod_cast hi'.le
  -- `2 N' / T + 1 / T ≤ 0.08 / K`
  have hgap : 2 * (N' : ℝ) / logLog x + 1 / logLog x ≤ 8 / 100 / K := by
    rw [← add_div, div_le_div_iff₀ hT (by linarith)]
    nlinarith
  rcases eq_or_ne c c' with hcc | hcc
  · subst hcc
    have hii : i ≠ i' := hne.resolve_left (fun h => h rfl)
    rcases lt_or_gt_of_ne hii with h | h
    · left
      have : (i : ℝ) + 1 ≤ i' := by exact_mod_cast h
      have : (i : ℝ) * (2 / logLog x) + 1 / logLog x ≤ i' * (2 / logLog x) := by
        rw [mul_div_assoc', mul_div_assoc', ← add_div, div_le_div_iff_of_pos_right hT]
        linarith
      linarith
    · right
      have : (i' : ℝ) + 1 ≤ i := by exact_mod_cast h
      have : (i' : ℝ) * (2 / logLog x) + 1 / logLog x ≤ i * (2 / logLog x) := by
        rw [mul_div_assoc', mul_div_assoc', ← add_div, div_le_div_iff_of_pos_right hT]
        linarith
      linarith
  · have hiT : (i : ℝ) * (2 / logLog x) ≤ 2 * N' / logLog x := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (by linarith) hT.le
    have hiT' : (i' : ℝ) * (2 / logLog x) ≤ 2 * N' / logLog x := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (by linarith) hT.le
    have hi0 : 0 ≤ (i : ℝ) * (2 / logLog x) := by positivity
    have hi0' : 0 ≤ (i' : ℝ) * (2 / logLog x) := by positivity
    rcases lt_or_gt_of_ne hcc with h | h
    · left
      have hcc' : (c : ℝ) + 1 ≤ c' := by exact_mod_cast h
      have := mul_le_mul_of_nonneg_right hcc' (show (0 : ℝ) ≤ 8 / 100 / K by positivity)
      linarith
    · right
      have hcc' : (c' : ℝ) + 1 ≤ c := by exact_mod_cast h
      have := mul_le_mul_of_nonneg_right hcc' (show (0 : ℝ) ≤ 8 / 100 / K by positivity)
      linarith

/-- The distinguished exponents of distinct clusters are `0.04 / K` apart. -/
theorem distExponent_gap (hK : 1 ≤ K) {N' : ℕ} (hT : 0 < logLog x)
    (hlay : 2 * ((N' : ℝ) + 1) * K ≤ 4 / 100 * logLog x) {S : Fin K → Finset ℕ}
    (hS : S ∈ clusterSets K N') {c c' : Fin K} (h : c < c') :
    distExponent K x S c + 4 / 100 / K ≤ distExponent K x S c' := by
  unfold distExponent inertExponent
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hd : ∀ c, distIndex S c < N' := fun c =>
    mem_range.1 (((mem_clusterSets.1 hS) c).2 (distIndex_mem ((mem_clusterSets.1 hS) c).1))
  have hiT : (distIndex S c : ℝ) * (2 / logLog x) ≤ 4 / 100 / K := by
    have : (distIndex S c : ℝ) ≤ N' := by exact_mod_cast (hd c).le
    rw [mul_div_assoc', div_le_div_iff₀ hT (by linarith)]
    nlinarith
  have hi0 : 0 ≤ (distIndex S c' : ℝ) * (2 / logLog x) := by positivity
  have hcc : ((c : ℕ) : ℝ) + 1 ≤ ((c' : ℕ) : ℝ) := by exact_mod_cast Fin.lt_def.1 h
  have := mul_le_mul_of_nonneg_right hcc (show (0 : ℝ) ≤ 8 / 100 / K by positivity)
  rw [add_mul, one_mul] at this
  have h7 : 8 / 100 / (K : ℝ) = 2 * (4 / 100 / K) := by ring
  linarith

end Layout

/-! ### Clipping and the layout -/

/-- Clipping to `[-1, 1]`. -/
noncomputable def clampOne (y : ℝ) : ℝ := max (-1) (min 1 y)

theorem abs_clampOne_le (y : ℝ) : |clampOne y| ≤ 1 := by
  unfold clampOne
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clampOne_of_abs_le {y : ℝ} (h : |y| ≤ 1) : clampOne y = y := by
  unfold clampOne
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

/-- The primes of the band with exponent `a` are at most `exp(2 L^a)`. -/
theorem band_le {x a : ℝ} {p : ℕ} (hp : p ∈ band x a) :
    (p : ℝ) ≤ Real.exp (2 * Real.log x ^ a) := by
  unfold band at hp
  exact (Nat.le_floor_iff (by positivity)).1 (mem_Icc.1 (mem_filter.1 hp).1).2

/-- The bands of the layout are pairwise disjoint. -/
theorem layout_disjoint {K : ℕ} (hK : 1 ≤ K) {N' : ℕ} {x : ℝ} (hL : 1 < Real.log x)
    (hT : 0 < logLog x) (hlay : 2 * ((N' : ℝ) + 1) * K ≤ 4 / 100 * logLog x) :
    ∀ (c c' : Fin K) (i i' : ℕ), i < N' → i' < N' → (c ≠ c' ∨ i ≠ i') →
      Disjoint (band x (inertExponent K x c i)) (band x (inertExponent K x c' i')) := by
  intro c c' i i' hi hi' hne
  have hne' : (c : ℕ) ≠ c' ∨ i ≠ i' := by
    rcases hne with h | h
    · exact Or.inl fun h' => h (Fin.ext h')
    · exact Or.inr h
  rcases inertExponent_sep hK hT hlay hi hi' hne' with h | h
  · exact band_disjoint hL h
  · exact (band_disjoint hL h).symm

end Erdos408.TypeII
