import Erdos408.OneSided.Model
import Erdos408.OneSided.Bands

/-!
# Counting boundary cubes

The geometric counts behind RR6 (`Boundary.lean`, `blueprint/one_sided_type_ii.md` §15).

* Cells: the cells `[α + i λ, α + (i + 1) λ)` meeting a set of diameter `δ` number at most
  `δ / λ + 2` (`card_cells_le`).
* The transported ratio `ρ(r) = τ_r(w_z)/τ_r(z)` of a primitive `z` satisfies
  `ρ(r) - ρ(s) = (r - s)/(τ_r(z) τ_s(z))` (`tauRatio_sub`), so it is injective and
  `256`-Lipschitz where `τ ≥ 1/16`.
* Atoms: both good-state tests at a ratio `ρ` depend only on the comparisons of
  `‖m ρ‖` with `θ` for the finitely many atoms `(m, θ) ∈ goodAtoms`
  (`good_iff_of_atomsAgree`); a test changing between two ratios forces a breakpoint
  `‖m ρ(s)‖ = θ` in between (`exists_breakpoint`).
* Faces and breakpoints: if the indicator of one visit differs at two points of a cube, the
  cube meets a face `u τ = U, 16U` (`UFace`), a face `v τ + z₂/u = V, 2V` (`VFace`), or a
  breakpoint (`Breakpoint`) (`visitBad_of_ne`). Each kind is counted fiber by fiber, in
  `u`, `v` and `r` respectively (`card_filter_visitBad_le`).
* Sizes: with labels, band primes and band sizes at most `Λ = exp(2 L^{1/5})`, the atoms have
  total weight `O(S⁹)`, `S = Λ^{K(J+2)}` (`sum_goodAtoms_le`), so one visit makes at most
  `10⁷ N S⁹ n²` cubes bad (`card_filter_visitBad_le_pow`), and the `N + 1` visits together
  at most `n² exp(L^{1/2})`, eventually (`eventually_visits_le`).
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

/-! ### Counting cells -/

/-- A finite set of integers whose pairwise differences are at most `D ≥ 0` has at most
`D + 1` elements. -/
theorem card_le_of_sub_le {F : Finset ℤ} {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ a ∈ F, ∀ b ∈ F, ((a - b : ℤ) : ℝ) ≤ D) : (F.card : ℝ) ≤ D + 1 := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp only [card_empty, Nat.cast_zero]
    linarith
  -- step: `F` lies between its least and largest elements
  have hsub : F ⊆ Icc (F.min' hF) (F.max' hF) := fun a ha =>
    mem_Icc.2 ⟨min'_le F a ha, le_max' F a ha⟩
  have hmm : F.min' hF ≤ F.max' hF := min'_le_max' F hF
  have hcard : ((F.card : ℕ) : ℤ) ≤ ((F.max' hF + 1 - F.min' hF).toNat : ℤ) := by
    exact_mod_cast (card_le_card hsub).trans (Int.card_Icc _ _).le
  rw [Int.toNat_of_nonneg (by omega)] at hcard
  have hle := h _ (max'_mem F hF) _ (min'_mem F hF)
  have hcast : ((F.card : ℤ) : ℝ) ≤ ((F.max' hF - F.min' hF + 1 : ℤ) : ℝ) := by
    exact_mod_cast (by omega : (F.card : ℤ) ≤ F.max' hF - F.min' hF + 1)
  push_cast at hcast hle ⊢
  linarith

/-- The cells `[α + i λ, α + (i + 1) λ)` meeting a set of diameter at most `δ` number at most
`δ / λ + 2`. -/
theorem card_cells_le {F : Finset ℕ} {S : Set ℝ} {α lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hS : ∀ s ∈ S, ∀ t ∈ S, s - t ≤ δ)
    (hF : ∀ i ∈ F, ∃ s ∈ S, α + i * lam ≤ s ∧ s < α + (i + 1) * lam) :
    (F.card : ℝ) ≤ δ / lam + 2 := by
  have hcard : (F.image fun i : ℕ => (i : ℤ)).card = F.card :=
    card_image_of_injective _ Nat.cast_injective
  rw [← hcard]
  have hD : 0 ≤ δ / lam + 1 := by positivity
  refine (card_le_of_sub_le hD ?_).trans (by linarith)
  simp only [mem_image]
  rintro _ ⟨i, hi, rfl⟩ _ ⟨i', hi', rfl⟩
  obtain ⟨s, hs, hs₁, hs₂⟩ := hF i hi
  obtain ⟨t, ht, ht₁, ht₂⟩ := hF i' hi'
  have hst := hS s hs t ht
  -- step: `(i - i' - 1) λ < s - t ≤ δ`
  have key : ((i : ℝ) - i' - 1) * lam ≤ δ := by linarith
  have key' : (i : ℝ) - i' - 1 ≤ δ / lam := by rwa [le_div_iff₀ hlam]
  push_cast
  linarith

/-- A point lies in at most one cell `[i/n, (i + 1)/n)`. -/
theorem eq_of_mem_cell {n i i' : ℕ} (hn : 1 ≤ n) {s : ℝ} (hi : (i : ℝ) / n ≤ s)
    (hi' : s < ((i : ℝ) + 1) / n) (hj : (i' : ℝ) / n ≤ s) (hj' : s < ((i' : ℝ) + 1) / n) :
    i = i' := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn'] at hi hj
  rw [lt_div_iff₀ hn'] at hi' hj'
  have h₁ : (i : ℝ) < i' + 1 := by nlinarith
  have h₂ : (i' : ℝ) < i + 1 := by nlinarith
  have h₁' : i < i' + 1 := by exact_mod_cast h₁
  have h₂' : i' < i + 1 := by exact_mod_cast h₂
  omega

/-! ### The intermediate value theorem -/

/-- A continuous function on `[0, 1]` whose membership in `[lo, hi]` differs at the two ends
takes the value `lo` or `hi`. -/
theorem exists_eq_of_mem_Icc_ne {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) {lo hi : ℝ}
    (h : ¬((lo ≤ f 0 ∧ f 0 ≤ hi) ↔ (lo ≤ f 1 ∧ f 1 ≤ hi))) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, f t = lo ∨ f t = hi := by
  have hivt := intermediate_value_uIcc (a := (0 : ℝ)) (b := 1) (f := f)
    (by rwa [Set.uIcc_of_le zero_le_one])
  rw [Set.uIcc_of_le zero_le_one] at hivt
  -- step: `lo` or `hi` lies between the values at the ends
  have key : lo ∈ Set.uIcc (f 0) (f 1) ∨ hi ∈ Set.uIcc (f 0) (f 1) := by
    simp only [Set.mem_uIcc]
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := hcon
    refine h ⟨fun ⟨a, b⟩ => ⟨?_, ?_⟩, fun ⟨a, b⟩ => ⟨?_, ?_⟩⟩
    · by_contra hc
      linarith [h₂ (not_le.1 hc).le]
    · by_contra hc
      linarith [h₃ b]
    · by_contra hc
      linarith [h₁ (not_le.1 hc).le]
    · by_contra hc
      linarith [h₄ b]
  rcases key with hk | hk
  · obtain ⟨t, ht, hft⟩ := hivt hk
    exact ⟨t, ht, Or.inl hft⟩
  · obtain ⟨t, ht, hft⟩ := hivt hk
    exact ⟨t, ht, Or.inr hft⟩

/-- A continuous function on `[a, b]` which avoids `θ` is on the same side of `θ` at both
ends. -/
theorem lt_iff_lt_of_ne {f : ℝ → ℝ} {a b θ : ℝ} (hf : ContinuousOn f (Set.uIcc a b))
    (hne : ∀ s ∈ Set.uIcc a b, f s ≠ θ) : (θ < f a ↔ θ < f b) := by
  have hivt := intermediate_value_uIcc hf
  have ha := hne a Set.left_mem_uIcc
  have hb := hne b Set.right_mem_uIcc
  constructor
  · intro h
    by_contra hc
    obtain ⟨s, hs, hfs⟩ := hivt (Set.mem_uIcc.2 (Or.inr ⟨not_lt.1 hc, h.le⟩))
    exact hne s hs hfs
  · intro h
    by_contra hc
    obtain ⟨s, hs, hfs⟩ := hivt (Set.mem_uIcc.2 (Or.inl ⟨not_lt.1 hc, h.le⟩))
    exact hne s hs hfs

/-! ### The transported ratio -/

/-- `τ_r(z) - τ_s(z) = (r - s) z₂`. -/
theorem tau_sub_tau (r s : ℝ) (z : ℤ × ℤ) : tau r z - tau s z = (r - s) * z.2 := by
  unfold tau
  ring

/-- `τ` is affine along a segment. -/
theorem tau_lineMap (r r' t : ℝ) (z : ℤ × ℤ) :
    tau (r + t * (r' - r)) z = tau r z + t * (tau r' z - tau r z) := by
  unfold tau
  ring

/-- Between two ratios, `τ` is at least its smaller value at the ends. -/
theorem min_le_tau_of_mem_uIcc {r r' s : ℝ} (hs : s ∈ Set.uIcc r r') (z : ℤ × ℤ) :
    min (tau r z) (tau r' z) ≤ tau s z := by
  rw [Set.mem_uIcc] at hs
  -- step: `(τ_s - τ_r)(τ_s - τ_{r'}) = z₂² (s - r)(s - r') ≤ 0`
  have hprod : (tau s z - tau r z) * (tau s z - tau r' z) ≤ 0 := by
    rw [tau_sub_tau, tau_sub_tau]
    have h : (s - r) * (s - r') ≤ 0 := by
      rcases hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have : (s - r) * z.2 * ((s - r') * z.2) = (s - r) * (s - r') * ((z.2 : ℝ) ^ 2) := by ring
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg _)
  by_contra hc
  push Not at hc
  have h₁ : tau s z < tau r z := lt_of_lt_of_le hc (min_le_left _ _)
  have h₂ : tau s z < tau r' z := lt_of_lt_of_le hc (min_le_right _ _)
  nlinarith

/-- For primitive `z`, `ρ(r) - ρ(s) = (r - s)/(τ_r(z) τ_s(z))`, since `det(z, w_z) = 1`. -/
theorem tauRatio_sub {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) {r s : ℝ} (hr : tau r z ≠ 0)
    (hs : tau s z ≠ 0) :
    tau r (complement z) / tau r z - tau s (complement z) / tau s z =
      (r - s) / (tau r z * tau s z) := by
  have hgcd : ((z.1 * Int.gcdA z.1 z.2 + z.2 * Int.gcdB z.1 z.2 : ℤ) : ℝ) = 1 := by
    rw [← Int.gcd_eq_gcd_ab, hz, Nat.cast_one, Int.cast_one]
  push_cast at hgcd
  rw [div_sub_div _ _ hr hs]
  congr 1
  unfold tau complement
  push_cast
  linear_combination (r - s) * hgcd

/-- Where `τ ≥ 1/16`, the transported ratio is `256`-Lipschitz. -/
theorem abs_tauRatio_sub_le {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) {r s : ℝ}
    (hr : 1 / 16 ≤ tau r z) (hs : 1 / 16 ≤ tau s z) :
    |tau r (complement z) / tau r z - tau s (complement z) / tau s z| ≤ 256 * |r - s| := by
  have hr0 : 0 < tau r z := by linarith
  have hs0 : 0 < tau s z := by linarith
  rw [tauRatio_sub hz hr0.ne' hs0.ne', abs_div, abs_of_pos (mul_pos hr0 hs0),
    div_le_iff₀ (mul_pos hr0 hs0)]
  have h : 1 / 256 ≤ tau r z * tau s z := by nlinarith
  nlinarith [abs_nonneg (r - s)]

/-- Where `τ > 0`, the transported ratio is injective. -/
theorem eq_of_tauRatio_eq {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) {r s : ℝ}
    (hr : 0 < tau r z) (hs : 0 < tau s z)
    (h : tau r (complement z) / tau r z = tau s (complement z) / tau s z) : r = s := by
  have := tauRatio_sub hz hr.ne' hs.ne'
  rw [h, sub_self, eq_comm, div_eq_zero_iff] at this
  rcases this with h | h
  · linarith
  · exact absurd h (mul_pos hr hs).ne'

/-- The transported ratio is continuous where `τ` does not vanish. -/
theorem continuousOn_tauRatio (z : ℤ × ℤ) {S : Set ℝ} (hS : ∀ s ∈ S, tau s z ≠ 0) :
    ContinuousOn (fun s => tau s (complement z) / tau s z) S := by
  unfold tau
  exact ((continuous_const.add (continuous_id.mul continuous_const)).continuousOn).div
    ((continuous_const.add (continuous_id.mul continuous_const)).continuousOn) hS

/-- The circle distance is `1`-Lipschitz. -/
theorem abs_circleDist_sub_le (a b : ℝ) : |circleDist a - circleDist b| ≤ |a - b| := by
  unfold circleDist
  have h₁ : |a - round a| ≤ |a - b| + |b - round b| :=
    (round_le a (round b)).trans (abs_sub_le a b _)
  have h₂ : |b - round b| ≤ |a - b| + |a - round a| := by
    refine (round_le b (round a)).trans ((abs_sub_le b a _).trans ?_)
    rw [abs_sub_comm b a]
  rw [abs_le]
  constructor <;> linarith

/-- The circle distance is continuous. -/
theorem continuous_circleDist : Continuous circleDist :=
  (LipschitzWith.of_dist_le_mul fun a b => by
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    exact abs_circleDist_sub_le a b).continuous

/-! ### Atoms of the good-state tests -/

open scoped Classical in
/-- The atoms `(m, θ)` of the good-state tests of the lists `p`: test (i) compares
`‖l D ρ‖` with `Y^{-7/10}` for the omission products `D` and `l ≤ Y^{1/5}`, and test (ii)
compares `‖(D Z - D' Z') (∏ T) ρ‖` with `100 exp(-L^{a_i})`. -/
def goodAtoms (x : ℝ) (d : Data K) (Y : ℝ) {J : ℕ} (p : Lists K J) : Finset (ℤ × ℝ) :=
  ((univ ×ˢ range (⌊Y ^ (1 / 5 : ℝ)⌋₊ + 1)).image fun a : (Fin K → Fin (J + 1)) × ℕ =>
      (((a.2 * omitProd p a.1 : ℕ) : ℤ), Y ^ (-(7 / 10 : ℝ)))) ∪
    (univ : Finset (Finset (Fin K) × Fin K)).biUnion fun Ii =>
      (freshDraws x d Ii.1).biUnion fun T =>
        ((univ ×ˢ univ) ×ˢ (selections x d Ii.1 Ii.2 ×ˢ selections x d Ii.1 Ii.2)).image
          fun b : ((Fin K → Fin (J + 1)) × (Fin K → Fin (J + 1))) ×
              ((Fin K → ℕ) × (Fin K → ℕ)) =>
            ((((omitProd p b.1.1 * ∏ j, b.2.1 j : ℕ) : ℤ) -
                ((omitProd p b.1.2 * ∏ j, b.2.2 j : ℕ) : ℤ)) * ((∏ j, T j : ℕ) : ℤ),
              100 * Real.exp (-Real.log x ^ d.a Ii.2))

/-- Two ratios agree on the atoms `A` when every comparison `θ < ‖m ρ‖` and `θ ≤ ‖m ρ‖` is the
same at both. -/
def AtomsAgree (A : Finset (ℤ × ℝ)) (ρ ρ' : ℝ) : Prop :=
  ∀ a ∈ A, (a.2 < circleDist (a.1 * ρ) ↔ a.2 < circleDist (a.1 * ρ')) ∧
    (a.2 ≤ circleDist (a.1 * ρ) ↔ a.2 ≤ circleDist (a.1 * ρ'))

/-- Test (i) depends only on the comparisons at the atoms. -/
theorem goodFirst_iff_of_atomsAgree {x : ℝ} {d : Data K} {Y : ℝ} (d₀ : ℝ) {J : ℕ}
    {p : Lists K J} {ρ ρ' : ℝ} (h : AtomsAgree (goodAtoms x d Y p) ρ ρ') :
    GoodFirst Y d₀ ρ p ↔ GoodFirst Y d₀ ρ' p := by
  -- step: each comparison of test (i) is at an atom
  have key : ∀ (o : Fin K → Fin (J + 1)) (l : ℕ), (l : ℝ) ≤ Y ^ (1 / 5 : ℝ) →
      (Y ^ (-(7 / 10 : ℝ)) < circleDist (l * omitProd p o * ρ) ↔
        Y ^ (-(7 / 10 : ℝ)) < circleDist (l * omitProd p o * ρ')) := by
    intro o l hlY
    have hmem : (((l * omitProd p o : ℕ) : ℤ), Y ^ (-(7 / 10 : ℝ))) ∈ goodAtoms x d Y p :=
      mem_union_left _ (mem_image.2 ⟨(o, l), mem_product.2 ⟨mem_univ _,
        mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hlY))⟩, rfl⟩)
    have := (h _ hmem).1
    push_cast at this
    exact this
  unfold GoodFirst
  exact forall_congr' fun o => imp_congr_right fun _ => imp_congr_right fun _ =>
    forall_congr' fun l => imp_congr_right fun _ => imp_congr_right fun hlY => key o l hlY

/-- The separation of test (ii) depends only on the comparisons at the atoms. -/
theorem separated_iff_of_atomsAgree {x : ℝ} {d : Data K} {Y : ℝ} (d₀ : ℝ) {J : ℕ}
    {p : Lists K J} {ρ ρ' : ℝ} (h : AtomsAgree (goodAtoms x d Y p) ρ ρ') (I : Finset (Fin K))
    (i : Fin K) {T : Fin K → ℕ} (hT : T ∈ freshDraws x d I) :
    Separated x d d₀ I i ρ p T ↔ Separated x d d₀ I i ρ' p T := by
  classical
  -- step: each comparison of the separation is at an atom
  have key : ∀ (o o' : Fin K → Fin (J + 1)), ∀ Z ∈ selections x d I i,
      ∀ Z' ∈ selections x d I i,
      (100 * Real.exp (-Real.log x ^ d.a i) ≤
          circleDist (((omitProd p o * ∏ j, Z j : ℕ) - (omitProd p o' * ∏ j, Z' j : ℕ) : ℝ) *
            (∏ j, T j : ℕ) * ρ) ↔
        100 * Real.exp (-Real.log x ^ d.a i) ≤
          circleDist (((omitProd p o * ∏ j, Z j : ℕ) - (omitProd p o' * ∏ j, Z' j : ℕ) : ℝ) *
            (∏ j, T j : ℕ) * ρ')) := by
    intro o o' Z hZ Z' hZ'
    have hmem : (((((omitProd p o * ∏ j, Z j : ℕ) : ℤ) -
        ((omitProd p o' * ∏ j, Z' j : ℕ) : ℤ)) * ((∏ j, T j : ℕ) : ℤ)),
          100 * Real.exp (-Real.log x ^ d.a i)) ∈ goodAtoms x d Y p := by
      refine mem_union_right _ (mem_biUnion.2 ⟨(I, i), mem_univ _, mem_biUnion.2 ⟨T, hT,
        mem_image.2 ⟨((o, o'), (Z, Z')), ?_, rfl⟩⟩⟩)
      exact mem_product.2 ⟨mem_product.2 ⟨mem_univ _, mem_univ _⟩, mem_product.2 ⟨hZ, hZ'⟩⟩
    have := (h _ hmem).2
    push_cast at this ⊢
    exact this
  unfold Separated
  exact forall_congr' fun o => forall_congr' fun o' => forall_congr' fun Z =>
    imp_congr_right fun hZ => forall_congr' fun Z' => imp_congr_right fun hZ' =>
      imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
        imp_congr_right fun _ => imp_congr_right fun _ => key o o' Z hZ Z' hZ'

open scoped Classical in
/-- Test (ii) depends only on the comparisons at the atoms. -/
theorem goodSecond_iff_of_atomsAgree {x : ℝ} {d : Data K} {Y : ℝ} (d₀ : ℝ) {J : ℕ}
    {p : Lists K J} {ρ ρ' : ℝ} (h : AtomsAgree (goodAtoms x d Y p) ρ ρ') :
    GoodSecond x d d₀ ρ p ↔ GoodSecond x d d₀ ρ' p := by
  simp only [GoodSecond]
  refine forall_congr' fun I => forall_congr' fun hI => ?_
  rw [filter_congr fun T hT =>
    not_congr (separated_iff_of_atomsAgree d₀ h I (I.max' hI) hT)]

/-- Both tests depend only on the comparisons at the atoms. -/
theorem good_iff_of_atomsAgree {x : ℝ} {d : Data K} {Y : ℝ} (d₀ : ℝ) {J : ℕ}
    {p : Lists K J} {ρ ρ' : ℝ} (h : AtomsAgree (goodAtoms x d Y p) ρ ρ') :
    (GoodFirst Y d₀ ρ p ∧ GoodSecond x d d₀ ρ p) ↔
      (GoodFirst Y d₀ ρ' p ∧ GoodSecond x d d₀ ρ' p) :=
  and_congr (goodFirst_iff_of_atomsAgree d₀ h) (goodSecond_iff_of_atomsAgree d₀ h)

/-- **Breakpoints.** If the tests at the transported ratio differ at `r` and `r'`, where
`τ > 0` in between, then some atom has `‖m ρ(s)‖ = θ` at some `s` in between. -/
theorem exists_breakpoint {x : ℝ} {d : Data K} {Y : ℝ} (d₀ : ℝ) {J : ℕ} {p : Lists K J}
    {z : ℤ × ℤ} {r r' : ℝ} (hτ : ∀ s ∈ Set.uIcc r r', 0 < tau s z)
    (hne : ¬((GoodFirst Y d₀ (tau r (complement z) / tau r z) p ∧
        GoodSecond x d d₀ (tau r (complement z) / tau r z) p) ↔
      (GoodFirst Y d₀ (tau r' (complement z) / tau r' z) p ∧
        GoodSecond x d d₀ (tau r' (complement z) / tau r' z) p))) :
    ∃ a ∈ goodAtoms x d Y p, ∃ s ∈ Set.uIcc r r',
      circleDist (a.1 * (tau s (complement z) / tau s z)) = a.2 := by
  by_contra hno
  push Not at hno
  refine hne (good_iff_of_atomsAgree d₀ fun a ha => ?_)
  have hf : ContinuousOn (fun s => circleDist (a.1 * (tau s (complement z) / tau s z)))
      (Set.uIcc r r') :=
    continuous_circleDist.comp_continuousOn (continuousOn_const.mul
      (continuousOn_tauRatio z fun s hs => (hτ s hs).ne'))
  have hlt := lt_iff_lt_of_ne hf (hno a ha)
  refine ⟨hlt, ?_⟩
  rw [(Ne.symm (hno a ha r Set.left_mem_uIcc)).le_iff_lt,
    (Ne.symm (hno a ha r' Set.right_mem_uIcc)).le_iff_lt]
  exact hlt

/-! ### Faces and breakpoints -/

/-- The real cube `i` at the scales `U, V`: `u/U ∈ [1 + i₁/n, 1 + (i₁ + 1)/n)`,
`v/V ∈ [1 + i₂/n, 1 + (i₂ + 1)/n)` and `r ∈ [i₃/n, (i₃ + 1)/n)`. -/
def InCube (U V : ℝ) (n : ℕ) (i : ℕ × ℕ × ℕ) (u v r : ℝ) : Prop :=
  (1 + i.1 / n) * U ≤ u ∧ u < (1 + (i.1 + 1) / n) * U ∧
    (1 + i.2.1 / n) * V ≤ v ∧ v < (1 + (i.2.1 + 1) / n) * V ∧
    i.2.2 / n ≤ r ∧ r < (i.2.2 + 1) / n

/-- The cube `i` meets a face `u τ_r(z) ∈ {U, 16U}` of the box condition. -/
def UFace (U : ℝ) (n : ℕ) (z : ℤ × ℤ) (i : ℕ × ℕ × ℕ) : Prop :=
  ∃ u r : ℝ, (1 + i.1 / n) * U ≤ u ∧ u < (1 + (i.1 + 1) / n) * U ∧ i.2.2 / n ≤ r ∧
    r < (i.2.2 + 1) / n ∧ (u * tau r z = U ∨ u * tau r z = 16 * U)

/-- The cube `i` meets a face `v τ_r(z) + z₂/u ∈ {V, 2V}` of the box condition at a point
where `τ_r(z) ≥ 1/16`. -/
def VFace (U V : ℝ) (n : ℕ) (z : ℤ × ℤ) (i : ℕ × ℕ × ℕ) : Prop :=
  ∃ u v r : ℝ, InCube U V n i u v r ∧ 1 / 16 ≤ tau r z ∧
    (v * tau r z + z.2 / u = V ∨ v * tau r z + z.2 / u = 2 * V)

/-- The column of the cube `i` contains a breakpoint `‖m ρ(s)‖ = θ` of an atom of the tests
of the lists `p`, at a point where `τ_s(z) ≥ 1/16`. -/
def Breakpoint (x : ℝ) (d : Data K) (Y : ℝ) {J : ℕ} (p : Lists K J) (n : ℕ) (z : ℤ × ℤ)
    (i : ℕ × ℕ × ℕ) : Prop :=
  ∃ a ∈ goodAtoms x d Y p, ∃ s : ℝ, i.2.2 / n ≤ s ∧ s < (i.2.2 + 1) / n ∧
    1 / 16 ≤ tau s z ∧ circleDist (a.1 * (tau s (complement z) / tau s z)) = a.2

/-- A visit at `z` with the lists `p` can make the cube `i` bad: `z` is primitive and the cube
meets a face or a breakpoint. -/
def VisitBad (x : ℝ) (d : Data K) (Y U V : ℝ) {J : ℕ} (p : Lists K J) (n : ℕ) (z : ℤ × ℤ)
    (i : ℕ × ℕ × ℕ) : Prop :=
  Int.gcd z.1 z.2 = 1 ∧ (UFace U n z i ∨ VFace U V n z i ∨ Breakpoint x d Y p n z i)

/-- The upper end of a cell: `(i + 1)/n ≤ m` for `i < m n`. -/
theorem add_one_div_le {i m n : ℕ} (hn : 1 ≤ n) (hi : i < m * n) :
    ((i : ℝ) + 1) / n ≤ m := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  exact_mod_cast (show i + 1 ≤ m * n by omega)

/-- A convex combination of two points of `[a, b)` lies in `[a, b)`. -/
theorem lineMap_mem_Ico {a b y y' t : ℝ} (hy : a ≤ y) (hy' : y < b) (hz : a ≤ y')
    (hz' : y' < b) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : a ≤ y + t * (y' - y) ∧ y + t * (y' - y) < b := by
  constructor
  · nlinarith [mul_nonneg ht₀ (sub_nonneg.2 hz), mul_nonneg (sub_nonneg.2 ht₁) (sub_nonneg.2 hy)]
  · rcases ht₀.eq_or_lt with rfl | ht
    · linarith
    · nlinarith [mul_pos ht (sub_pos.2 hz'), mul_nonneg (sub_nonneg.2 ht₁) (sub_pos.2 hy').le]

/-- The real cubes are convex. -/
theorem inCube_lineMap {U V : ℝ} {n : ℕ} {i : ℕ × ℕ × ℕ} {u v r u' v' r' t : ℝ}
    (hP : InCube U V n i u v r) (hQ : InCube U V n i u' v' r') (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    InCube U V n i (u + t * (u' - u)) (v + t * (v' - v)) (r + t * (r' - r)) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hP
  obtain ⟨h₁', h₂', h₃', h₄', h₅', h₆'⟩ := hQ
  obtain ⟨hu, hu'⟩ := lineMap_mem_Ico h₁ h₂ h₁' h₂' ht.1 ht.2
  obtain ⟨hv, hv'⟩ := lineMap_mem_Ico h₃ h₄ h₃' h₄' ht.1 ht.2
  obtain ⟨hr, hr'⟩ := lineMap_mem_Ico h₅ h₆ h₅' h₆' ht.1 ht.2
  exact ⟨hu, hu', hv, hv', hr, hr'⟩

/-- The points of a cube of the grid lie in `[U, 16U] × [V, 2V] × [0, 1]`. -/
theorem inCube_bounds {U V : ℝ} (hU : 0 < U) (hV : 0 < V) {n : ℕ} (hn : 1 ≤ n)
    {i : ℕ × ℕ × ℕ} (hi₁ : i.1 < 15 * n) (hi₂ : i.2.1 < n) (hi₃ : i.2.2 < n) {u v r : ℝ}
    (hP : InCube U V n i u v r) :
    U ≤ u ∧ u ≤ 16 * U ∧ V ≤ v ∧ v ≤ 2 * V ∧ 0 ≤ r ∧ r ≤ 1 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hP
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e₁ := add_one_div_le hn hi₁
  have e₂ := add_one_div_le hn (show i.2.1 < 1 * n by omega)
  have e₃ := add_one_div_le hn (show i.2.2 < 1 * n by omega)
  have f₁ : (0 : ℝ) ≤ i.1 / n := by positivity
  have f₂ : (0 : ℝ) ≤ i.2.1 / n := by positivity
  have f₃ : (0 : ℝ) ≤ i.2.2 / n := by positivity
  push_cast at e₁ e₂ e₃
  refine ⟨?_, ?_, ?_, ?_, by linarith, by linarith⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- On the `u`-condition `U ≤ u τ ≤ 16 U` with `u ∈ [U, 16U]`, `τ ∈ [1/16, 16]`. -/
theorem tau_mem_of_uCond {U u τ : ℝ} (hU : 0 < U) (hu : U ≤ u) (hu' : u ≤ 16 * U)
    (h₁ : U ≤ u * τ) (h₂ : u * τ ≤ 16 * U) : 1 / 16 ≤ τ ∧ τ ≤ 16 := by
  have hu0 : 0 < u := by linarith
  constructor
  · by_contra hc
    push Not at hc
    nlinarith [mul_lt_mul_of_pos_left hc hu0]
  · by_contra hc
    push Not at hc
    nlinarith [mul_lt_mul_of_pos_left hc hu0]

/-- **Classification.** If the indicator of one visit at `z` differs at two points of a cube
of the grid, the visit makes the cube bad: the cube meets a face of the box condition, or a
breakpoint of the tests. -/
theorem visitBad_of_ne {x : ℝ} {d : Data K} {Y d₀ U V : ℝ} (hU : 0 < U) (hV : 0 < V) {J : ℕ}
    {p : Lists K J} {n : ℕ} (hn : 1 ≤ n) {i : ℕ × ℕ × ℕ} (hi₁ : i.1 < 15 * n)
    (hi₂ : i.2.1 < n) (hi₃ : i.2.2 < n) (z : ℤ × ℤ) {u v r u' v' r' : ℝ}
    (hP : InCube U V n i u v r) (hQ : InCube U V n i u' v' r')
    (hne : ¬((z ∈ rootPositions U V u v r ∧ GoodFirst Y d₀ (tau r (complement z) / tau r z) p ∧
        GoodSecond x d d₀ (tau r (complement z) / tau r z) p) ↔
      (z ∈ rootPositions U V u' v' r' ∧ GoodFirst Y d₀ (tau r' (complement z) / tau r' z) p ∧
        GoodSecond x d d₀ (tau r' (complement z) / tau r' z) p))) :
    VisitBad x d Y U V p n z i := by
  obtain ⟨hu₁, hu₂, -, -, -, -⟩ := inCube_bounds hU hV hn hi₁ hi₂ hi₃ hP
  obtain ⟨hu₁', hu₂', -, -, -, -⟩ := inCube_bounds hU hV hn hi₁ hi₂ hi₃ hQ
  -- step: membership is a constant condition, the `u`-condition and the `v`-condition
  have hmem : ∀ u v r, z ∈ rootPositions U V u v r ↔
      ((z ∈ Icc (-(rootBound U V : ℤ)) (rootBound U V) ×ˢ
          Icc (-(rootBound U V : ℤ)) (rootBound U V) ∧ Int.gcd z.1 z.2 = 1) ∧
        (U ≤ u * tau r z ∧ u * tau r z ≤ 16 * U) ∧
        (V ≤ v * tau r z + z.2 / u ∧ v * tau r z + z.2 / u ≤ 2 * V)) := by
    intro u v r
    simp only [rootPositions, mem_filter]
    tauto
  simp only [hmem] at hne
  by_cases hB : z ∈ Icc (-(rootBound U V : ℤ)) (rootBound U V) ×ˢ
      Icc (-(rootBound U V : ℤ)) (rootBound U V) ∧ Int.gcd z.1 z.2 = 1
  swap
  · exact absurd (iff_of_false (fun h => hB h.1.1) fun h => hB h.1.1) hne
  refine ⟨hB.2, ?_⟩
  by_cases hu : (U ≤ u * tau r z ∧ u * tau r z ≤ 16 * U) ↔
      (U ≤ u' * tau r' z ∧ u' * tau r' z ≤ 16 * U)
  swap
  · -- step: the `u`-condition changes along the segment, which meets a `u`-face
    left
    have hcont : ContinuousOn (fun t : ℝ => (u + t * (u' - u)) * tau (r + t * (r' - r)) z)
        (Set.Icc 0 1) := by
      unfold tau
      fun_prop
    obtain ⟨t, ht, hft⟩ := exists_eq_of_mem_Icc_ne hcont (lo := U) (hi := 16 * U)
      (by simpa using hu)
    obtain ⟨h₁, h₂, -, -, h₅, h₆⟩ := inCube_lineMap hP hQ ht
    exact ⟨_, _, h₁, h₂, h₅, h₆, hft⟩
  by_cases huc : U ≤ u * tau r z ∧ u * tau r z ≤ 16 * U
  swap
  · exact absurd (iff_of_false (fun h => huc h.1.2.1) fun h => huc (hu.2 h.1.2.1)) hne
  have huc' := hu.1 huc
  obtain ⟨hτ₁, hτ₂⟩ := tau_mem_of_uCond hU hu₁ hu₂ huc.1 huc.2
  obtain ⟨hτ₁', hτ₂'⟩ := tau_mem_of_uCond hU hu₁' hu₂' huc'.1 huc'.2
  by_cases hv : (V ≤ v * tau r z + z.2 / u ∧ v * tau r z + z.2 / u ≤ 2 * V) ↔
      (V ≤ v' * tau r' z + z.2 / u' ∧ v' * tau r' z + z.2 / u' ≤ 2 * V)
  swap
  · -- step: the `v`-condition changes along the segment, which meets a `v`-face
    right; left
    have hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, u + t * (u' - u) ≠ 0 := fun t ht => by
      obtain ⟨h₁, -, -, -, -, -⟩ := inCube_lineMap hP hQ ht
      obtain ⟨h₁', -⟩ := inCube_bounds hU hV hn hi₁ hi₂ hi₃ (inCube_lineMap hP hQ ht)
      linarith
    have hcont : ContinuousOn (fun t : ℝ => (v + t * (v' - v)) * tau (r + t * (r' - r)) z +
        z.2 / (u + t * (u' - u))) (Set.Icc 0 1) := by
      refine ContinuousOn.add ?_ (continuousOn_const.div (by fun_prop) hpos)
      unfold tau
      fun_prop
    obtain ⟨t, ht, hft⟩ := exists_eq_of_mem_Icc_ne hcont (lo := V) (hi := 2 * V)
      (by simpa using hv)
    refine ⟨_, _, _, inCube_lineMap hP hQ ht, ?_, hft⟩
    rw [tau_lineMap]
    nlinarith [ht.1, ht.2]
  by_cases hvc : V ≤ v * tau r z + z.2 / u ∧ v * tau r z + z.2 / u ≤ 2 * V
  swap
  · exact absurd (iff_of_false (fun h => hvc h.1.2.2) fun h => hvc (hv.2 h.1.2.2)) hne
  -- step: the box condition holds at both points, so the tests change: a breakpoint
  right; right
  have hne' := fun h => hne (and_congr (iff_of_true ⟨hB, huc, hvc⟩ ⟨hB, huc', hv.1 hvc⟩) h)
  have hτ : ∀ s ∈ Set.uIcc r r', 1 / 16 ≤ tau s z := fun s hs =>
    (le_min hτ₁ hτ₁').trans (min_le_tau_of_mem_uIcc hs z)
  obtain ⟨a, ha, s, hs, hbr⟩ := exists_breakpoint d₀ (fun s hs => by linarith [hτ s hs]) hne'
  obtain ⟨-, -, -, -, h₅, h₆⟩ := hP
  obtain ⟨-, -, -, -, h₅', h₆'⟩ := hQ
  rw [Set.mem_uIcc] at hs
  refine ⟨a, ha, s, ?_, ?_, hτ s (Set.mem_uIcc.2 hs), hbr⟩
  · rcases hs with ⟨hs, -⟩ | ⟨hs, -⟩ <;> linarith
  · rcases hs with ⟨-, hs⟩ | ⟨-, hs⟩ <;> linarith

/-! ### Counting fiber by fiber -/

open scoped Classical in
/-- The size of a subset of `[0, a) × [0, b) × [0, c)` as a triple sum. -/
theorem card_filter_prod_eq {a b c : ℕ} (P : ℕ × ℕ × ℕ → Prop) :
    (((range a ×ˢ range b ×ˢ range c).filter P).card : ℝ) =
      ∑ i₁ ∈ range a, ∑ i₂ ∈ range b, ∑ i₃ ∈ range c, if P (i₁, i₂, i₃) then 1 else 0 := by
  rw [card_filter, Nat.cast_sum, sum_product]
  refine sum_congr rfl fun i₁ _ => ?_
  rw [sum_product]
  push_cast
  rfl

open scoped Classical in
/-- Counting a subset of `[0, a) × [0, b) × [0, c)` along the first coordinate. -/
theorem card_filter_prod_le₁ {a b c : ℕ} {P : ℕ × ℕ × ℕ → Prop} {B : ℝ}
    (h : ∀ i₂ i₃, (((range a).filter fun i₁ => P (i₁, i₂, i₃)).card : ℝ) ≤ B) :
    (((range a ×ˢ range b ×ˢ range c).filter P).card : ℝ) ≤ b * c * B := by
  rw [card_filter_prod_eq, sum_comm]
  calc ∑ i₂ ∈ range b, ∑ i₁ ∈ range a, ∑ i₃ ∈ range c,
        (if P (i₁, i₂, i₃) then (1 : ℝ) else 0)
      = ∑ i₂ ∈ range b, ∑ i₃ ∈ range c,
          (((range a).filter fun i₁ => P (i₁, i₂, i₃)).card : ℝ) := by
        refine sum_congr rfl fun i₂ _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun i₃ _ => ?_
        rw [card_filter, Nat.cast_sum]
        push_cast
        rfl
    _ ≤ ∑ _i₂ ∈ range b, ∑ _i₃ ∈ range c, B := sum_le_sum fun i₂ _ => sum_le_sum fun i₃ _ => h i₂ i₃
    _ = b * c * B := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

open scoped Classical in
/-- Counting a subset of `[0, a) × [0, b) × [0, c)` along the second coordinate. -/
theorem card_filter_prod_le₂ {a b c : ℕ} {P : ℕ × ℕ × ℕ → Prop} {B : ℝ}
    (h : ∀ i₁ i₃, (((range b).filter fun i₂ => P (i₁, i₂, i₃)).card : ℝ) ≤ B) :
    (((range a ×ˢ range b ×ˢ range c).filter P).card : ℝ) ≤ a * c * B := by
  rw [card_filter_prod_eq]
  calc ∑ i₁ ∈ range a, ∑ i₂ ∈ range b, ∑ i₃ ∈ range c,
        (if P (i₁, i₂, i₃) then (1 : ℝ) else 0)
      = ∑ i₁ ∈ range a, ∑ i₃ ∈ range c,
          (((range b).filter fun i₂ => P (i₁, i₂, i₃)).card : ℝ) := by
        refine sum_congr rfl fun i₁ _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun i₃ _ => ?_
        rw [card_filter, Nat.cast_sum]
        push_cast
        rfl
    _ ≤ ∑ _i₁ ∈ range a, ∑ _i₃ ∈ range c, B := sum_le_sum fun i₁ _ => sum_le_sum fun i₃ _ => h i₁ i₃
    _ = a * c * B := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

open scoped Classical in
/-- Counting a subset of `[0, a) × [0, b) × [0, c)` along the third coordinate. -/
theorem card_filter_prod_le₃ {a b c : ℕ} {P : ℕ × ℕ × ℕ → Prop} {B : ℝ}
    (h : ∀ i₁ i₂, (((range c).filter fun i₃ => P (i₁, i₂, i₃)).card : ℝ) ≤ B) :
    (((range a ×ˢ range b ×ˢ range c).filter P).card : ℝ) ≤ a * b * B := by
  rw [card_filter_prod_eq]
  calc ∑ i₁ ∈ range a, ∑ i₂ ∈ range b, ∑ i₃ ∈ range c,
        (if P (i₁, i₂, i₃) then (1 : ℝ) else 0)
      = ∑ i₁ ∈ range a, ∑ i₂ ∈ range b,
          (((range c).filter fun i₃ => P (i₁, i₂, i₃)).card : ℝ) := by
        refine sum_congr rfl fun i₁ _ => sum_congr rfl fun i₂ _ => ?_
        rw [card_filter, Nat.cast_sum]
        push_cast
        rfl
    _ ≤ ∑ _i₁ ∈ range a, ∑ _i₂ ∈ range b, B := sum_le_sum fun i₁ _ => sum_le_sum fun i₂ _ => h i₁ i₂
    _ = a * b * B := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

/-! ### Counting the faces -/

/-- Two points of a cell `[i/n, (i + 1)/n)` are within `1/n`. -/
theorem abs_sub_le_of_mem_cell {n i : ℕ} {s t : ℝ} (hs : (i : ℝ) / n ≤ s)
    (hs' : s < ((i : ℝ) + 1) / n) (ht : (i : ℝ) / n ≤ t) (ht' : t < ((i : ℝ) + 1) / n) :
    |s - t| ≤ 1 / n := by
  have h : ((i : ℝ) + 1) / n = i / n + 1 / n := by ring
  rw [abs_le]
  constructor <;> linarith

/-- Two points of a cell `[(1 + i/n) U, (1 + (i + 1)/n) U)` are within `U/n`. -/
theorem abs_sub_le_of_mem_cell' {n i : ℕ} {U s t : ℝ} (hs : (1 + (i : ℝ) / n) * U ≤ s)
    (hs' : s < (1 + ((i : ℝ) + 1) / n) * U) (ht : (1 + (i : ℝ) / n) * U ≤ t)
    (ht' : t < (1 + ((i : ℝ) + 1) / n) * U) : |s - t| ≤ U / n := by
  have h : (1 + ((i : ℝ) + 1) / n) * U = (1 + i / n) * U + U / n := by ring
  rw [abs_le]
  constructor <;> linarith

/-- Within a column, `τ_r(z)` changes by at most `|z₂|/n`. -/
theorem abs_tau_sub_le_of_mem_cell {n i : ℕ} {s t : ℝ} (hs : (i : ℝ) / n ≤ s)
    (hs' : s < ((i : ℝ) + 1) / n) (ht : (i : ℝ) / n ≤ t) (ht' : t < ((i : ℝ) + 1) / n)
    (z : ℤ × ℤ) : |tau s z - tau t z| ≤ |(z.2 : ℝ)| / n := by
  rw [tau_sub_tau, abs_mul, div_eq_mul_one_div, mul_comm (|(z.2 : ℝ)|)]
  exact mul_le_mul_of_nonneg_right (abs_sub_le_of_mem_cell hs hs' ht ht') (abs_nonneg _)

open scoped Classical in
/-- For a fixed column, the cells in `u` meeting `u τ_r(z) = c U`, `c ≥ 1`, number at most
`256 |z₂| + 2`: there `u = c U/τ_r(z)` with `τ_r(z) ≥ c/16`. -/
theorem card_uFace_fiber_le {U : ℝ} (hU : 0 < U) {n : ℕ} (hn : 1 ≤ n) (z : ℤ × ℤ) {c : ℝ}
    (hc : 1 ≤ c) (i₃ : ℕ) :
    (((range (15 * n)).filter fun i₁ : ℕ => ∃ u r : ℝ, (1 + i₁ / n) * U ≤ u ∧
        u < (1 + (i₁ + 1) / n) * U ∧ i₃ / n ≤ r ∧ r < (i₃ + 1) / n ∧
        u * tau r z = c * U).card : ℝ) ≤ 256 * |(z.2 : ℝ)| + 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcU : 0 < c * U := by positivity
  set S : Set ℝ := {u | ∃ r : ℝ, (i₃ : ℝ) / n ≤ r ∧ r < ((i₃ : ℝ) + 1) / n ∧ 0 ≤ u ∧
    u ≤ 16 * U ∧ u * tau r z = c * U}
  refine le_trans (card_cells_le (S := S) (α := U) (lam := U / n)
    (δ := 256 * U * |(z.2 : ℝ)| / n) (div_pos hU hn') (by positivity) ?_ ?_) (le_of_eq ?_)
  rotate_left 2
  · field_simp
  · -- step: `u - u' = u u' (τ_{r'} - τ_r)/(c U)`
    rintro s ⟨r, hr₁, hr₂, hs₀, hs₁, hs⟩ t ⟨r', hr₁', hr₂', ht₀, ht₁, ht⟩
    have key : s - t = s * t * (tau r' z - tau r z) / (c * U) := by
      rw [eq_div_iff hcU.ne']
      linear_combination (-s) * ht + t * hs
    have hτ := abs_tau_sub_le_of_mem_cell hr₁' hr₂' hr₁ hr₂ z
    calc s - t ≤ |s - t| := le_abs_self _
      _ = s * t * |tau r' z - tau r z| / (c * U) := by
          rw [key, abs_div, abs_mul, abs_mul, abs_of_nonneg hs₀, abs_of_nonneg ht₀,
            abs_of_pos hcU]
      _ ≤ (16 * U) * (16 * U) * (|(z.2 : ℝ)| / n) / (1 * U) := by
          gcongr
      _ = 256 * U * |(z.2 : ℝ)| / n := by field_simp; ring
  · -- step: every counted cell contains a point of `S`
    intro i₁ hi₁
    obtain ⟨hi₁, u, r, h₁, h₂, h₃, h₄, h₅⟩ := mem_filter.1 hi₁
    have e₁ := add_one_div_le hn (mem_range.1 hi₁)
    push_cast at e₁
    have f₁ : (0 : ℝ) ≤ i₁ / n := by positivity
    refine ⟨u, ⟨r, h₃, h₄, by nlinarith, by nlinarith, h₅⟩, ?_, ?_⟩
    · calc U + i₁ * (U / n) = (1 + i₁ / n) * U := by ring
        _ ≤ u := h₁
    · calc u < (1 + (i₁ + 1) / n) * U := h₂
        _ = U + (i₁ + 1) * (U / n) := by ring

open scoped Classical in
/-- For fixed `u`-cell and column, the cells in `v` meeting `v τ_r(z) + z₂/u = c V` where
`τ_r(z) ≥ 1/16` number at most `48 |z₂| + 2`, when `U V ≥ 1`: there
`v = (c V - z₂/u)/τ_r(z)`. -/
theorem card_vFace_fiber_le {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (hUV : 1 ≤ U * V) {n : ℕ}
    (hn : 1 ≤ n) (z : ℤ × ℤ) (c : ℝ) (i₁ i₃ : ℕ) :
    (((range n).filter fun i₂ : ℕ => ∃ u v r : ℝ, InCube U V n (i₁, i₂, i₃) u v r ∧
        1 / 16 ≤ tau r z ∧ v * tau r z + z.2 / u = c * V).card : ℝ) ≤
      48 * |(z.2 : ℝ)| + 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have f₁ : (0 : ℝ) ≤ i₁ / n := by positivity
  set S : Set ℝ := {v | ∃ u r : ℝ, (1 + (i₁ : ℝ) / n) * U ≤ u ∧
    u < (1 + ((i₁ : ℝ) + 1) / n) * U ∧ (i₃ : ℝ) / n ≤ r ∧ r < ((i₃ : ℝ) + 1) / n ∧
    1 / 16 ≤ tau r z ∧ 0 ≤ v ∧ v ≤ 2 * V ∧ v * tau r z + z.2 / u = c * V}
  refine le_trans (card_cells_le (S := S) (α := V) (lam := V / n)
    (δ := 48 * V * |(z.2 : ℝ)| / n) (div_pos hV hn') (by positivity) ?_ ?_) (le_of_eq ?_)
  rotate_left 2
  · field_simp
  · -- step: `(v - v') τ_r = z₂/u' - z₂/u + v' (τ_{r'} - τ_r)`
    rintro s ⟨u, r, hu₁, hu₂, hr₁, hr₂, hτ, hs₀, hs₁, hs⟩
      t ⟨u', r', hu₁', hu₂', hr₁', hr₂', hτ', ht₀, ht₁, ht⟩
    have hu : U ≤ u := by nlinarith
    have hu' : U ≤ u' := by nlinarith
    have hu0 : 0 < u := by linarith
    have hu0' : 0 < u' := by linarith
    have key : (s - t) * tau r z = z.2 / u' - z.2 / u + t * (tau r' z - tau r z) := by
      linear_combination hs - ht
    have h₁ : |(z.2 : ℝ) / u' - z.2 / u| ≤ |(z.2 : ℝ)| / n * V := by
      have e : (z.2 : ℝ) / u' - z.2 / u = z.2 * (u - u') / (u * u') := by
        field_simp
      rw [e, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < u * u')]
      calc |(z.2 : ℝ)| * |u - u'| / (u * u') ≤ |(z.2 : ℝ)| * (U / n) / (U * U) := by
            gcongr
            exact abs_sub_le_of_mem_cell' hu₁ hu₂ hu₁' hu₂'
        _ = |(z.2 : ℝ)| / n * (1 / U) := by field_simp
        _ ≤ |(z.2 : ℝ)| / n * V := by
            gcongr
            rw [div_le_iff₀ hU]
            linarith
    have h₂ : |t * (tau r' z - tau r z)| ≤ 2 * V * (|(z.2 : ℝ)| / n) := by
      rw [abs_mul, abs_of_nonneg ht₀]
      exact mul_le_mul ht₁ (abs_tau_sub_le_of_mem_cell hr₁' hr₂' hr₁ hr₂ z) (abs_nonneg _)
        (by positivity)
    have h₃ : |s - t| ≤ 16 * |(s - t) * tau r z| := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < tau r z)]
      nlinarith [abs_nonneg (s - t)]
    calc s - t ≤ |s - t| := le_abs_self _
      _ ≤ 16 * |(s - t) * tau r z| := h₃
      _ ≤ 16 * (|(z.2 : ℝ)| / n * V + 2 * V * (|(z.2 : ℝ)| / n)) := by
          rw [key]
          gcongr
          exact (abs_add_le _ _).trans (add_le_add h₁ h₂)
      _ = 48 * V * |(z.2 : ℝ)| / n := by ring
  · -- step: every counted cell contains a point of `S`
    intro i₂ hi₂
    obtain ⟨hi₂, u, v, r, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩, hτ, hv⟩ := mem_filter.1 hi₂
    have e₂ := add_one_div_le hn (show i₂ < 1 * n by have := mem_range.1 hi₂; omega)
    push_cast at e₂
    have f₂ : (0 : ℝ) ≤ i₂ / n := by positivity
    refine ⟨v, ⟨u, r, h₁, h₂, h₅, h₆, hτ, by nlinarith, by nlinarith, hv⟩, ?_, ?_⟩
    · calc V + i₂ * (V / n) = (1 + i₂ / n) * V := by ring
        _ ≤ v := h₃
    · calc v < (1 + (i₂ + 1) / n) * V := h₄
        _ = V + (i₂ + 1) * (V / n) := by ring

/-! ### Counting the breakpoints -/

open scoped Classical in
/-- For a fixed offset `e ≠ 0`, the columns containing a point where `τ_s(z) ≥ 1/16` and
`m ρ(s) - round(m ρ(s)) = e` number at most `256 |m| + 1`: the point is determined by the
integer `round(m ρ(s))`, which varies by at most `256 |m|` over `[0, 1]`. -/
theorem card_breakpoint_fiber_offset_le {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) {n : ℕ}
    (hn : 1 ≤ n) (m : ℤ) {e : ℝ} (he : e ≠ 0) :
    (((range n).filter fun i₃ : ℕ => ∃ s : ℝ, (i₃ : ℝ) / n ≤ s ∧ s < ((i₃ : ℝ) + 1) / n ∧
        1 / 16 ≤ tau s z ∧ m * (tau s (complement z) / tau s z) -
          round (m * (tau s (complement z) / tau s z)) = e).card : ℝ) ≤
      256 * |(m : ℝ)| + 1 := by
  generalize hF : ((range n).filter fun i₃ : ℕ => ∃ s : ℝ, (i₃ : ℝ) / n ≤ s ∧
    s < ((i₃ : ℝ) + 1) / n ∧ 1 / 16 ≤ tau s z ∧ m * (tau s (complement z) / tau s z) -
      round (m * (tau s (complement z) / tau s z)) = e) = F
  -- step: choose a point in every counted column
  have hF' : ∀ i : ℕ, ∃ s : ℝ, i ∈ F → (i < n ∧ (i : ℝ) / n ≤ s ∧ s < ((i : ℝ) + 1) / n ∧
      1 / 16 ≤ tau s z ∧ m * (tau s (complement z) / tau s z) -
        round (m * (tau s (complement z) / tau s z)) = e) := fun i => by
    by_cases hi : i ∈ F
    · rw [← hF, mem_filter, mem_range] at hi
      obtain ⟨hin, s, hs⟩ := hi
      exact ⟨s, fun _ => ⟨hin, hs⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose s hs using hF'
  rcases F.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp only [card_empty, Nat.cast_zero]
    positivity
  have hm : (m : ℝ) ≠ 0 := by
    rintro hm
    have h := (hs i₀ hi₀).2.2.2.2
    rw [hm, zero_mul, round_zero, Int.cast_zero, sub_zero] at h
    exact he h.symm
  -- step: the integer `round(m ρ(s))` determines the column
  have hinj : Set.InjOn (fun i => round (m * (tau (s i) (complement z) / tau (s i) z)))
      (F : Set ℕ) := by
    intro i hi i' hi' hii'
    obtain ⟨-, h₁, h₂, h₃, h₄⟩ := hs i hi
    obtain ⟨-, h₁', h₂', h₃', h₄'⟩ := hs i' hi'
    have hcast : ((round (m * (tau (s i) (complement z) / tau (s i) z)) : ℤ) : ℝ) =
        ((round (m * (tau (s i') (complement z) / tau (s i') z)) : ℤ) : ℝ) := by
      exact_mod_cast hii'
    have hρ : (m : ℝ) * (tau (s i) (complement z) / tau (s i) z) =
        m * (tau (s i') (complement z) / tau (s i') z) := by linarith
    have hss := eq_of_tauRatio_eq hz (by linarith) (by linarith) (mul_left_cancel₀ hm hρ)
    rw [hss] at h₁ h₂
    exact eq_of_mem_cell hn h₁ h₂ h₁' h₂'
  rw [← card_image_of_injOn hinj]
  refine card_le_of_sub_le (by positivity) ?_
  simp only [mem_image]
  rintro _ ⟨i, hi, rfl⟩ _ ⟨i', hi', rfl⟩
  obtain ⟨hin, h₁, h₂, h₃, h₄⟩ := hs i hi
  obtain ⟨hin', h₁', h₂', h₃', h₄'⟩ := hs i' hi'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- step: `s, s' ∈ [0, 1]`, so `|m ρ(s) - m ρ(s')| ≤ 256 |m|`
  have e₁ := add_one_div_le hn (show i < 1 * n by omega)
  have e₁' := add_one_div_le hn (show i' < 1 * n by omega)
  push_cast at e₁ e₁'
  have f₁ : (0 : ℝ) ≤ i / n := by positivity
  have f₁' : (0 : ℝ) ≤ i' / n := by positivity
  have hss : |s i - s i'| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hρ := abs_tauRatio_sub_le hz h₃ h₃'
  have hdiff : ((round (m * (tau (s i) (complement z) / tau (s i) z)) -
      round (m * (tau (s i') (complement z) / tau (s i') z)) : ℤ) : ℝ) =
      m * (tau (s i) (complement z) / tau (s i) z - tau (s i') (complement z) / tau (s i') z) := by
    push_cast
    linarith
  rw [hdiff]
  calc (m : ℝ) * (tau (s i) (complement z) / tau (s i) z -
        tau (s i') (complement z) / tau (s i') z)
      ≤ |(m : ℝ)| * |tau (s i) (complement z) / tau (s i) z -
          tau (s i') (complement z) / tau (s i') z| := by
        rw [← abs_mul]
        exact le_abs_self _
    _ ≤ |(m : ℝ)| * (256 * 1) := by
        gcongr
        exact hρ.trans (by linarith)
    _ = 256 * |(m : ℝ)| := by ring

open scoped Classical in
/-- The columns containing a breakpoint `‖m ρ(s)‖ = θ > 0` where `τ_s(z) ≥ 1/16` number at
most `2 (256 |m| + 1)`. -/
theorem card_breakpoint_fiber_le {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) {n : ℕ}
    (hn : 1 ≤ n) (m : ℤ) {θ : ℝ} (hθ : 0 < θ) :
    (((range n).filter fun i₃ : ℕ => ∃ s : ℝ, (i₃ : ℝ) / n ≤ s ∧ s < ((i₃ : ℝ) + 1) / n ∧
        1 / 16 ≤ tau s z ∧ circleDist (m * (tau s (complement z) / tau s z)) = θ).card : ℝ) ≤
      2 * (256 * |(m : ℝ)| + 1) := by
  -- step: `‖y‖ = θ` means `y - round y = ±θ`
  have hsub : ((range n).filter fun i₃ : ℕ => ∃ s : ℝ, (i₃ : ℝ) / n ≤ s ∧
      s < ((i₃ : ℝ) + 1) / n ∧ 1 / 16 ≤ tau s z ∧
        circleDist (m * (tau s (complement z) / tau s z)) = θ) ⊆
      ((range n).filter fun i₃ : ℕ => ∃ s : ℝ, (i₃ : ℝ) / n ≤ s ∧ s < ((i₃ : ℝ) + 1) / n ∧
        1 / 16 ≤ tau s z ∧ m * (tau s (complement z) / tau s z) -
          round (m * (tau s (complement z) / tau s z)) = θ) ∪
      ((range n).filter fun i₃ : ℕ => ∃ s : ℝ, (i₃ : ℝ) / n ≤ s ∧ s < ((i₃ : ℝ) + 1) / n ∧
        1 / 16 ≤ tau s z ∧ m * (tau s (complement z) / tau s z) -
          round (m * (tau s (complement z) / tau s z)) = -θ) := by
    intro i hi
    obtain ⟨hi, s, h₁, h₂, h₃, h₄⟩ := mem_filter.1 hi
    unfold circleDist at h₄
    rcases (abs_eq hθ.le).1 h₄ with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨hi, s, h₁, h₂, h₃, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨hi, s, h₁, h₂, h₃, h⟩)
  have h₁ := card_breakpoint_fiber_offset_le hz hn m hθ.ne'
  have h₂ := card_breakpoint_fiber_offset_le hz hn m (neg_ne_zero.2 hθ.ne')
  have hcast := (Nat.cast_le (α := ℝ)).2 ((card_le_card hsub).trans (card_union_le _ _))
  push_cast at hcast
  linarith

/-- The thresholds of the atoms are positive. -/
theorem pos_of_mem_goodAtoms {x : ℝ} {d : Data K} {Y : ℝ} (hY : 0 < Y) {J : ℕ}
    {p : Lists K J} {a : ℤ × ℝ} (ha : a ∈ goodAtoms x d Y p) : 0 < a.2 := by
  unfold goodAtoms at ha
  rcases mem_union.1 ha with ha | ha
  · obtain ⟨b, -, rfl⟩ := mem_image.1 ha
    exact Real.rpow_pos_of_pos hY _
  · obtain ⟨Ii, -, ha⟩ := mem_biUnion.1 ha
    obtain ⟨T, -, ha⟩ := mem_biUnion.1 ha
    obtain ⟨b, -, rfl⟩ := mem_image.1 ha
    positivity

/-! ### One visit -/

open scoped Classical in
/-- **One visit.** The cubes of the grid that one visit at `z` with the lists `p` can make bad
number at most `n² (2 (256 |z₂| + 2) + 30 (48 |z₂| + 2) + 15 ∑_atoms 2 (256 |m| + 1))`: the
`u`-faces fiber by fiber in `u`, the `v`-faces in `v`, and the breakpoints in `r`. -/
theorem card_filter_visitBad_le {x : ℝ} {d : Data K} {Y U V : ℝ} (hY : 0 < Y) (hU : 0 < U)
    (hV : 0 < V) (hUV : 1 ≤ U * V) {J : ℕ} (p : Lists K J) {n : ℕ} (hn : 1 ≤ n)
    (z : ℤ × ℤ) :
    (((range (15 * n) ×ˢ range n ×ˢ range n).filter (VisitBad x d Y U V p n z)).card : ℝ) ≤
      (n : ℝ) ^ 2 * (2 * (256 * |(z.2 : ℝ)| + 2) + 30 * (48 * |(z.2 : ℝ)| + 2) +
        15 * ∑ a ∈ goodAtoms x d Y p, 2 * (256 * |(a.1 : ℝ)| + 1)) := by
  set A := range (15 * n) ×ˢ range n ×ˢ range n
  have hsum : 0 ≤ ∑ a ∈ goodAtoms x d Y p, 2 * (256 * |(a.1 : ℝ)| + 1) :=
    sum_nonneg fun a _ => by positivity
  by_cases hz : Int.gcd z.1 z.2 = 1
  swap
  · have : A.filter (VisitBad x d Y U V p n z) = ∅ :=
      filter_eq_empty_iff.2 fun i _ h => hz h.1
    rw [this, card_empty, Nat.cast_zero]
    positivity
  -- step: split into the faces and the breakpoints
  have hsub : A.filter (VisitBad x d Y U V p n z) ⊆ A.filter (UFace U n z) ∪
      A.filter (VFace U V n z) ∪ A.filter (Breakpoint x d Y p n z) := by
    intro i hi
    obtain ⟨hi, -, h | h | h⟩ := mem_filter.1 hi
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hi, h⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hi, h⟩))
    · exact mem_union_right _ (mem_filter.2 ⟨hi, h⟩)
  have hcard := (Nat.cast_le (α := ℝ)).2 ((card_le_card hsub).trans
    ((card_union_le _ _).trans (add_le_add (card_union_le _ _) le_rfl)))
  push_cast at hcard
  -- step: the `u`-faces, fiber by fiber in `u`
  have h₁ : ((A.filter (UFace U n z)).card : ℝ) ≤ n * n * (2 * (256 * |(z.2 : ℝ)| + 2)) := by
    refine card_filter_prod_le₁ fun i₂ i₃ => ?_
    have hsub₁ : ((range (15 * n)).filter fun i₁ => UFace U n z (i₁, i₂, i₃)) ⊆
        ((range (15 * n)).filter fun i₁ : ℕ => ∃ u r : ℝ, (1 + i₁ / n) * U ≤ u ∧
          u < (1 + (i₁ + 1) / n) * U ∧ i₃ / n ≤ r ∧ r < (i₃ + 1) / n ∧
          u * tau r z = 1 * U) ∪
        ((range (15 * n)).filter fun i₁ : ℕ => ∃ u r : ℝ, (1 + i₁ / n) * U ≤ u ∧
          u < (1 + (i₁ + 1) / n) * U ∧ i₃ / n ≤ r ∧ r < (i₃ + 1) / n ∧
          u * tau r z = 16 * U) := by
      intro i₁ hi₁
      obtain ⟨hi₁, u, r, h₁, h₂, h₃, h₄, h₅ | h₅⟩ := mem_filter.1 hi₁
      · exact mem_union_left _
          (mem_filter.2 ⟨hi₁, u, r, h₁, h₂, h₃, h₄, by rw [one_mul]; exact h₅⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨hi₁, u, r, h₁, h₂, h₃, h₄, h₅⟩)
    have e₁ := card_uFace_fiber_le hU hn z le_rfl i₃
    have e₂ := card_uFace_fiber_le hU hn z (by norm_num : (1 : ℝ) ≤ 16) i₃
    have hc := (Nat.cast_le (α := ℝ)).2 ((card_le_card hsub₁).trans (card_union_le _ _))
    push_cast at hc
    linarith
  -- step: the `v`-faces, fiber by fiber in `v`
  have h₂ : ((A.filter (VFace U V n z)).card : ℝ) ≤
      (15 * n : ℕ) * n * (2 * (48 * |(z.2 : ℝ)| + 2)) := by
    refine card_filter_prod_le₂ fun i₁ i₃ => ?_
    have hsub₂ : ((range n).filter fun i₂ => VFace U V n z (i₁, i₂, i₃)) ⊆
        ((range n).filter fun i₂ : ℕ => ∃ u v r : ℝ, InCube U V n (i₁, i₂, i₃) u v r ∧
          1 / 16 ≤ tau r z ∧ v * tau r z + z.2 / u = 1 * V) ∪
        ((range n).filter fun i₂ : ℕ => ∃ u v r : ℝ, InCube U V n (i₁, i₂, i₃) u v r ∧
          1 / 16 ≤ tau r z ∧ v * tau r z + z.2 / u = 2 * V) := by
      intro i₂ hi₂
      obtain ⟨hi₂, u, v, r, h₁, h₂, h₃ | h₃⟩ := mem_filter.1 hi₂
      · exact mem_union_left _
          (mem_filter.2 ⟨hi₂, u, v, r, h₁, h₂, by rw [one_mul]; exact h₃⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨hi₂, u, v, r, h₁, h₂, h₃⟩)
    have e₁ := card_vFace_fiber_le hU hV hUV hn z 1 i₁ i₃
    have e₂ := card_vFace_fiber_le hU hV hUV hn z 2 i₁ i₃
    have hc := (Nat.cast_le (α := ℝ)).2 ((card_le_card hsub₂).trans (card_union_le _ _))
    push_cast at hc
    linarith
  -- step: the breakpoints, fiber by fiber in `r`
  have h₃ : ((A.filter (Breakpoint x d Y p n z)).card : ℝ) ≤
      (15 * n : ℕ) * n * ∑ a ∈ goodAtoms x d Y p, 2 * (256 * |(a.1 : ℝ)| + 1) := by
    refine card_filter_prod_le₃ fun i₁ i₂ => ?_
    have hsub₃ : ((range n).filter fun i₃ => Breakpoint x d Y p n z (i₁, i₂, i₃)) ⊆
        (goodAtoms x d Y p).biUnion fun a => (range n).filter fun i₃ : ℕ => ∃ s : ℝ,
          (i₃ : ℝ) / n ≤ s ∧ s < ((i₃ : ℝ) + 1) / n ∧ 1 / 16 ≤ tau s z ∧
            circleDist (a.1 * (tau s (complement z) / tau s z)) = a.2 := by
      intro i₃ hi₃
      obtain ⟨hi₃, a, ha, s, hs⟩ := mem_filter.1 hi₃
      exact mem_biUnion.2 ⟨a, ha, mem_filter.2 ⟨hi₃, s, hs⟩⟩
    have hc := (Nat.cast_le (α := ℝ)).2 ((card_le_card hsub₃).trans card_biUnion_le)
    push_cast at hc
    exact hc.trans (sum_le_sum fun a ha =>
      card_breakpoint_fiber_le hz hn a.1 (pos_of_mem_goodAtoms hY ha))
  push_cast at h₂ h₃
  calc ((A.filter (VisitBad x d Y U V p n z)).card : ℝ)
      ≤ n * n * (2 * (256 * |(z.2 : ℝ)| + 2)) + 15 * n * n * (2 * (48 * |(z.2 : ℝ)| + 2)) +
          15 * n * n * ∑ a ∈ goodAtoms x d Y p, 2 * (256 * |(a.1 : ℝ)| + 1) := by
        linarith
    _ = _ := by ring

/-! ### The size of the atoms -/

/-- An omission product of labels at most `Λ ≥ 1` is at most `Λ^{K(J+1)}`. -/
theorem omitProd_le {J : ℕ} {p : Lists K J} {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hp : ∀ i h, (p i h : ℝ) ≤ Λ) (o : Fin K → Fin (J + 1)) :
    (omitProd p o : ℝ) ≤ Λ ^ (K * (J + 1)) := by
  unfold omitProd
  push_cast
  calc ∏ i, ∏ h ∈ univ.erase (o i), (p i h : ℝ) ≤ ∏ _i : Fin K, Λ ^ (J + 1) := by
        refine prod_le_prod₀ (fun i _ => prod_nonneg fun h _ => Nat.cast_nonneg _) fun i _ => ?_
        calc ∏ h ∈ univ.erase (o i), (p i h : ℝ) ≤ ∏ _h ∈ univ.erase (o i), Λ :=
              prod_le_prod₀ (fun h _ => Nat.cast_nonneg _) fun h _ => hp i h
          _ = Λ ^ J := by
              rw [prod_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
                Nat.add_sub_cancel]
          _ ≤ Λ ^ (J + 1) := pow_le_pow_right₀ hΛ (Nat.le_succ J)
    _ = Λ ^ (K * (J + 1)) := by
        rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

/-- The product of labels at most `Λ` is at most `Λ^{K(J+1)}`. -/
theorem listProd_le_pow {J : ℕ} {p : Lists K J} {Λ : ℝ} (hp : ∀ i h, (p i h : ℝ) ≤ Λ) :
    (listProd p : ℝ) ≤ Λ ^ (K * (J + 1)) := by
  unfold listProd
  push_cast
  calc ∏ i, ∏ h, (p i h : ℝ) ≤ ∏ _i : Fin K, ∏ _h : Fin (J + 1), Λ :=
        prod_le_prod₀ (fun i _ => prod_nonneg fun h _ => Nat.cast_nonneg _) fun i _ =>
          prod_le_prod₀ (fun h _ => Nat.cast_nonneg _) fun h _ => hp i h
    _ = Λ ^ (K * (J + 1)) := by
        simp only [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

/-- A product over the groups of factors each `1` or a band prime is at most `Λ^K`, when the
band primes are at most `Λ ≥ 1`. -/
theorem prod_le_pow_of_forall {x : ℝ} {d : Data K} {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hband : ∀ i, ∀ q ∈ band x (d.a i), (q : ℝ) ≤ Λ) {T : Fin K → ℕ}
    (hT : ∀ i, T i = 1 ∨ T i ∈ band x (d.a i)) : ((∏ i, T i : ℕ) : ℝ) ≤ Λ ^ K := by
  push_cast
  calc ∏ i, (T i : ℝ) ≤ ∏ _i : Fin K, Λ := by
        refine prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => ?_
        rcases hT i with h | h
        · rw [h, Nat.cast_one]
          exact hΛ
        · exact hband i _ h
    _ = Λ ^ K := by rw [prod_const, card_univ, Fintype.card_fin]

/-- The number of choices from sets each `{1}` or a band is at most `Λ^K`, when the bands
have at most `Λ ≥ 1` primes. -/
theorem card_piFinset_le {x : ℝ} {d : Data K} {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcard : ∀ i, ((band x (d.a i)).card : ℝ) ≤ Λ) (t : Fin K → Finset ℕ)
    (ht : ∀ i, t i = {1} ∨ t i = band x (d.a i)) :
    ((Fintype.piFinset t).card : ℝ) ≤ Λ ^ K := by
  rw [Fintype.card_piFinset, Nat.cast_prod]
  calc ∏ i, ((t i).card : ℝ) ≤ ∏ _i : Fin K, Λ := by
        refine prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => ?_
        rcases ht i with h | h
        · rw [h, card_singleton, Nat.cast_one]
          exact hΛ
        · rw [h]
          exact hcard i
    _ = Λ ^ K := by rw [prod_const, card_univ, Fintype.card_fin]

/-- The selections are `1` or a band prime in each group. -/
theorem eq_one_or_mem_band_of_mem_selections {x : ℝ} {d : Data K} {I : Finset (Fin K)}
    {i : Fin K} {Z : Fin K → ℕ} (hZ : Z ∈ selections x d I i) (j : Fin K) :
    Z j = 1 ∨ Z j ∈ band x (d.a j) := by
  have h := Fintype.mem_piFinset.1 hZ j
  split_ifs at h
  · exact Or.inr h
  · exact Or.inl (mem_singleton.1 h)

/-- The fresh draws are `1` or a band prime in each group. -/
theorem eq_one_or_mem_band_of_mem_freshDraws {x : ℝ} {d : Data K} {I : Finset (Fin K)}
    {T : Fin K → ℕ} (hT : T ∈ freshDraws x d I) (j : Fin K) :
    T j = 1 ∨ T j ∈ band x (d.a j) := by
  have h := Fintype.mem_piFinset.1 hT j
  split_ifs at h
  · exact Or.inl (mem_singleton.1 h)
  · exact Or.inr h

/-- The atoms have `|m| ≤ S²`, `S = Λ^{K(J+2)}`, when the labels and band primes are at most
`Λ ≥ 1` and `1 ≤ Y ≤ Λ^{K(J+1)}`. -/
theorem abs_le_of_mem_goodAtoms {x : ℝ} {d : Data K} {Y : ℝ} {J : ℕ} {p : Lists K J}
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (hp : ∀ i h, (p i h : ℝ) ≤ Λ)
    (hband : ∀ i, ∀ q ∈ band x (d.a i), (q : ℝ) ≤ Λ) (hY₁ : 1 ≤ Y)
    (hY : Y ≤ Λ ^ (K * (J + 1))) {a : ℤ × ℝ} (ha : a ∈ goodAtoms x d Y p) :
    |(a.1 : ℝ)| ≤ (Λ ^ (K * (J + 2))) ^ 2 := by
  classical
  have hMS : Λ ^ (K * (J + 1)) * Λ ^ K = Λ ^ (K * (J + 2)) := by
    rw [← pow_add, show K * (J + 1) + K = K * (J + 2) by ring]
  have hM₁ : 1 ≤ Λ ^ (K * (J + 1)) := one_le_pow₀ hΛ
  have hK₁ : 1 ≤ Λ ^ K := one_le_pow₀ hΛ
  have hMle : Λ ^ (K * (J + 1)) ≤ Λ ^ (K * (J + 2)) := by rw [← hMS]; nlinarith
  have hKle : Λ ^ K ≤ Λ ^ (K * (J + 2)) := by rw [← hMS]; nlinarith
  unfold goodAtoms at ha
  rcases mem_union.1 ha with ha | ha
  · -- step: test (i), `m = l D` with `l ≤ Y^{1/5} ≤ Y` and `D ≤ Λ^{K(J+1)}`
    obtain ⟨⟨o, l⟩, hl, rfl⟩ := mem_image.1 ha
    have hl' : (l : ℝ) ≤ Y := by
      have := Nat.lt_succ_iff.1 (mem_range.1 (mem_product.1 hl).2)
      calc (l : ℝ) ≤ ⌊Y ^ (1 / 5 : ℝ)⌋₊ := by exact_mod_cast this
        _ ≤ Y ^ (1 / 5 : ℝ) := Nat.floor_le (by positivity)
        _ ≤ Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY₁ (by norm_num)
        _ = Y := Real.rpow_one Y
    have hD := omitProd_le hΛ hp o
    push_cast
    rw [abs_of_nonneg (by positivity), sq]
    exact mul_le_mul ((hl'.trans hY).trans hMle) (hD.trans hMle) (by positivity) (by positivity)
  · -- step: test (ii), `m = (D Z - D' Z') ∏ T` with `D Z, D' Z' ≤ S` and `∏ T ≤ Λ^K`
    obtain ⟨⟨I, i⟩, -, ha⟩ := mem_biUnion.1 ha
    obtain ⟨T, hT, ha⟩ := mem_biUnion.1 ha
    obtain ⟨⟨⟨o, o'⟩, ⟨Z, Z'⟩⟩, hb, rfl⟩ := mem_image.1 ha
    simp only [mem_product] at hb
    have hZb : ((∏ j, Z j : ℕ) : ℝ) ≤ Λ ^ K :=
      prod_le_pow_of_forall hΛ hband (eq_one_or_mem_band_of_mem_selections hb.2.1)
    have hZb' : ((∏ j, Z' j : ℕ) : ℝ) ≤ Λ ^ K :=
      prod_le_pow_of_forall hΛ hband (eq_one_or_mem_band_of_mem_selections hb.2.2)
    have hTb : ((∏ j, T j : ℕ) : ℝ) ≤ Λ ^ K :=
      prod_le_pow_of_forall hΛ hband (eq_one_or_mem_band_of_mem_freshDraws hT)
    have hA : ((omitProd p o * ∏ j, Z j : ℕ) : ℝ) ≤ Λ ^ (K * (J + 2)) := by
      rw [Nat.cast_mul, ← hMS]
      exact mul_le_mul (omitProd_le hΛ hp o) hZb (Nat.cast_nonneg _) (by positivity)
    have hB : ((omitProd p o' * ∏ j, Z' j : ℕ) : ℝ) ≤ Λ ^ (K * (J + 2)) := by
      rw [Nat.cast_mul, ← hMS]
      exact mul_le_mul (omitProd_le hΛ hp o') hZb' (Nat.cast_nonneg _) (by positivity)
    have hAB : |((omitProd p o * ∏ j, Z j : ℕ) : ℝ) - ((omitProd p o' * ∏ j, Z' j : ℕ) : ℝ)|
        ≤ Λ ^ (K * (J + 2)) := by
      rw [abs_le]
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (omitProd p o * ∏ j, Z j),
        Nat.cast_nonneg (α := ℝ) (omitProd p o' * ∏ j, Z' j)]
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (∏ j, T j)), sq]
    exact mul_le_mul hAB (hTb.trans hKle) (Nat.cast_nonneg _) (by positivity)

/-- The atoms number at most `3 S⁷`, `S = Λ^{K(J+2)}`, when the bands have at most `Λ ≥ 2`
primes, `J + 1 ≤ Λ` and `1 ≤ Y ≤ Λ^{K(J+1)}`. -/
theorem card_goodAtoms_le {x : ℝ} {d : Data K} {Y : ℝ} {J : ℕ} (p : Lists K J) {Λ : ℝ}
    (hΛ : 2 ≤ Λ) (hcard : ∀ i, ((band x (d.a i)).card : ℝ) ≤ Λ) (hJ : (J : ℝ) + 1 ≤ Λ)
    (hY₁ : 1 ≤ Y) (hY : Y ≤ Λ ^ (K * (J + 1))) :
    ((goodAtoms x d Y p).card : ℝ) ≤ 3 * (Λ ^ (K * (J + 2))) ^ 7 := by
  classical
  have hΛ₁ : 1 ≤ Λ := by linarith
  have hMS : Λ ^ (K * (J + 1)) * Λ ^ K = Λ ^ (K * (J + 2)) := by
    rw [← pow_add, show K * (J + 1) + K = K * (J + 2) by ring]
  have hM₁ : 1 ≤ Λ ^ (K * (J + 1)) := one_le_pow₀ hΛ₁
  have hK₁ : 1 ≤ Λ ^ K := one_le_pow₀ hΛ₁
  have hMle : Λ ^ (K * (J + 1)) ≤ Λ ^ (K * (J + 2)) := by rw [← hMS]; nlinarith
  have hKle : Λ ^ K ≤ Λ ^ (K * (J + 2)) := by rw [← hMS]; nlinarith
  have hS₁ : 1 ≤ Λ ^ (K * (J + 2)) := hM₁.trans hMle
  have hJK : ((J : ℝ) + 1) ^ K ≤ Λ ^ K := pow_le_pow_left₀ (by positivity) hJ K
  -- step: the atoms of test (i) number at most `2 S²`
  have hfirst : (((univ ×ˢ range (⌊Y ^ (1 / 5 : ℝ)⌋₊ + 1) :
      Finset ((Fin K → Fin (J + 1)) × ℕ))).card : ℝ) ≤ 2 * (Λ ^ (K * (J + 2))) ^ 2 := by
    rw [card_product, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      card_range]
    push_cast
    have h₂ : (⌊Y ^ (1 / 5 : ℝ)⌋₊ : ℝ) + 1 ≤ 2 * Λ ^ (K * (J + 2)) := by
      have : (⌊Y ^ (1 / 5 : ℝ)⌋₊ : ℝ) ≤ Y :=
        (Nat.floor_le (by positivity)).trans ((Real.rpow_le_rpow_of_exponent_le hY₁
          (by norm_num : (1 / 5 : ℝ) ≤ 1)).trans (Real.rpow_one Y).le)
      linarith
    calc ((J : ℝ) + 1) ^ K * ((⌊Y ^ (1 / 5 : ℝ)⌋₊ : ℝ) + 1)
        ≤ Λ ^ (K * (J + 2)) * (2 * Λ ^ (K * (J + 2))) :=
          mul_le_mul (hJK.trans hKle) h₂ (by positivity) (by positivity)
      _ = 2 * (Λ ^ (K * (J + 2))) ^ 2 := by ring
  -- step: the atoms of test (ii) at one `(I, i)` number at most `(Λ^K)⁵`
  have hsecond : ∀ Ii : Finset (Fin K) × Fin K,
      (((freshDraws x d Ii.1).biUnion fun T =>
        ((univ ×ˢ univ) ×ˢ (selections x d Ii.1 Ii.2 ×ˢ selections x d Ii.1 Ii.2)).image
          fun b : ((Fin K → Fin (J + 1)) × (Fin K → Fin (J + 1))) ×
              ((Fin K → ℕ) × (Fin K → ℕ)) =>
            ((((omitProd p b.1.1 * ∏ j, b.2.1 j : ℕ) : ℤ) -
                ((omitProd p b.1.2 * ∏ j, b.2.2 j : ℕ) : ℤ)) * ((∏ j, T j : ℕ) : ℤ),
              100 * Real.exp (-Real.log x ^ d.a Ii.2))).card : ℝ) ≤ (Λ ^ K) ^ 5 := by
    intro Ii
    have hsel : ((selections x d Ii.1 Ii.2).card : ℝ) ≤ Λ ^ K :=
      card_piFinset_le hΛ₁ hcard _ fun j => by
        split_ifs
        · exact Or.inr rfl
        · exact Or.inl rfl
    have hfresh : ((freshDraws x d Ii.1).card : ℝ) ≤ Λ ^ K :=
      card_piFinset_le hΛ₁ hcard _ fun j => by
        split_ifs
        · exact Or.inl rfl
        · exact Or.inr rfl
    refine (Nat.cast_le.2 card_biUnion_le).trans ?_
    push_cast
    calc ∑ T ∈ freshDraws x d Ii.1, ((((univ ×ˢ univ) ×ˢ (selections x d Ii.1 Ii.2 ×ˢ
          selections x d Ii.1 Ii.2)).image _).card : ℝ)
        ≤ ∑ _T ∈ freshDraws x d Ii.1, (Λ ^ K) ^ 4 := by
          refine sum_le_sum fun T _ => (Nat.cast_le.2 card_image_le).trans ?_
          rw [card_product, card_product, card_product, card_univ, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_fin]
          push_cast
          calc ((J : ℝ) + 1) ^ K * ((J : ℝ) + 1) ^ K *
                ((selections x d Ii.1 Ii.2).card * (selections x d Ii.1 Ii.2).card)
              ≤ Λ ^ K * Λ ^ K * (Λ ^ K * Λ ^ K) := by gcongr
            _ = (Λ ^ K) ^ 4 := by ring
      _ ≤ Λ ^ K * (Λ ^ K) ^ 4 := by
          rw [sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hfresh (by positivity)
      _ = (Λ ^ K) ^ 5 := by ring
  -- step: the pairs `(I, i)` number at most `(Λ^K)²`
  have hpairs : ((univ : Finset (Finset (Fin K) × Fin K)).card : ℝ) ≤ (Λ ^ K) ^ 2 := by
    rw [card_univ, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin]
    push_cast
    have h₂ : (2 : ℝ) ^ K ≤ Λ ^ K := pow_le_pow_left₀ (by norm_num) hΛ K
    have hK : (K : ℝ) ≤ 2 ^ K := by exact_mod_cast Nat.lt_two_pow_self.le
    calc (2 : ℝ) ^ K * K ≤ Λ ^ K * Λ ^ K :=
          mul_le_mul h₂ (hK.trans h₂) (Nat.cast_nonneg _) (by positivity)
      _ = (Λ ^ K) ^ 2 := by ring
  have h7 : (Λ ^ K) ^ 2 * (Λ ^ K) ^ 5 ≤ (Λ ^ (K * (J + 2))) ^ 7 := by
    rw [← pow_add]
    exact pow_le_pow_left₀ (by positivity) hKle 7
  have h27 : (Λ ^ (K * (J + 2))) ^ 2 ≤ (Λ ^ (K * (J + 2))) ^ 7 :=
    pow_le_pow_right₀ hS₁ (by norm_num)
  have hprod : ((univ : Finset (Finset (Fin K) × Fin K)).card : ℝ) * (Λ ^ K) ^ 5 ≤
      (Λ ^ K) ^ 2 * (Λ ^ K) ^ 5 := mul_le_mul_of_nonneg_right hpairs (by positivity)
  unfold goodAtoms
  refine (Nat.cast_le.2 (card_union_le _ _)).trans ?_
  rw [Nat.cast_add]
  refine le_trans (b := 2 * (Λ ^ (K * (J + 2))) ^ 2 + (Λ ^ (K * (J + 2))) ^ 7)
    (add_le_add ((Nat.cast_le.2 card_image_le).trans hfirst)
      ((Nat.cast_le.2 card_biUnion_le).trans ?_)) (by linarith)
  rw [Nat.cast_sum]
  refine (sum_le_sum fun Ii _ => hsecond Ii).trans ?_
  rw [sum_const, nsmul_eq_mul]
  exact hprod.trans h7

/-- **The weight of the breakpoints**: under the hypotheses of `card_goodAtoms_le` and
labels and band primes at most `Λ`, `∑_atoms 2 (256 |m| + 1) ≤ 1542 S⁹`, `S = Λ^{K(J+2)}`. -/
theorem sum_goodAtoms_le {x : ℝ} {d : Data K} {Y : ℝ} {J : ℕ} {p : Lists K J} {Λ : ℝ}
    (hΛ : 2 ≤ Λ) (hp : ∀ i h, (p i h : ℝ) ≤ Λ) (hband : ∀ i, ∀ q ∈ band x (d.a i), (q : ℝ) ≤ Λ)
    (hcard : ∀ i, ((band x (d.a i)).card : ℝ) ≤ Λ) (hJ : (J : ℝ) + 1 ≤ Λ) (hY₁ : 1 ≤ Y)
    (hY : Y ≤ Λ ^ (K * (J + 1))) :
    ∑ a ∈ goodAtoms x d Y p, 2 * (256 * |(a.1 : ℝ)| + 1) ≤
      1542 * (Λ ^ (K * (J + 2))) ^ 9 := by
  have hΛ₁ : 1 ≤ Λ := by linarith
  have hS₁ : 1 ≤ Λ ^ (K * (J + 2)) := one_le_pow₀ hΛ₁
  have hS2 : 1 ≤ (Λ ^ (K * (J + 2))) ^ 2 := one_le_pow₀ hS₁
  calc ∑ a ∈ goodAtoms x d Y p, 2 * (256 * |(a.1 : ℝ)| + 1)
      ≤ ∑ _a ∈ goodAtoms x d Y p, 514 * (Λ ^ (K * (J + 2))) ^ 2 := by
        refine sum_le_sum fun a ha => ?_
        have := abs_le_of_mem_goodAtoms hΛ₁ hp hband hY₁ hY ha
        linarith
    _ = (goodAtoms x d Y p).card * (514 * (Λ ^ (K * (J + 2))) ^ 2) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 3 * (Λ ^ (K * (J + 2))) ^ 7 * (514 * (Λ ^ (K * (J + 2))) ^ 2) :=
        mul_le_mul_of_nonneg_right (card_goodAtoms_le p hΛ hcard hJ hY₁ hY) (by positivity)
    _ = 1542 * (Λ ^ (K * (J + 2))) ^ 9 := by ring

/-! ### The total -/

open scoped Classical in
/-- **One visit, in size.** With the hypotheses of `sum_goodAtoms_le` and
`|z₂| ≤ 2560 N S²`, `N ≥ 1`, a visit makes at most `10⁷ N S⁹ n²` cubes bad,
`S = Λ^{K(J+2)}`. -/
theorem card_filter_visitBad_le_pow {x : ℝ} {d : Data K} {Y U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hUV : 1 ≤ U * V) {J : ℕ} {p : Lists K J} {Λ : ℝ} (hΛ : 2 ≤ Λ) (hp : ∀ i h, (p i h : ℝ) ≤ Λ)
    (hband : ∀ i, ∀ q ∈ band x (d.a i), (q : ℝ) ≤ Λ)
    (hcard : ∀ i, ((band x (d.a i)).card : ℝ) ≤ Λ) (hJ : (J : ℝ) + 1 ≤ Λ) (hY₁ : 1 ≤ Y)
    (hY : Y ≤ Λ ^ (K * (J + 1))) {n : ℕ} (hn : 1 ≤ n) {z : ℤ × ℤ} {N : ℝ} (hN : 1 ≤ N)
    (hz : |(z.2 : ℝ)| ≤ 2560 * N * (Λ ^ (K * (J + 2))) ^ 2) :
    (((range (15 * n) ×ˢ range n ×ˢ range n).filter (VisitBad x d Y U V p n z)).card : ℝ) ≤
      (n : ℝ) ^ 2 * (10 ^ 7 * N * (Λ ^ (K * (J + 2))) ^ 9) := by
  have hS₁ : 1 ≤ Λ ^ (K * (J + 2)) := one_le_pow₀ (by linarith)
  have h29 : (Λ ^ (K * (J + 2))) ^ 2 ≤ (Λ ^ (K * (J + 2))) ^ 9 :=
    pow_le_pow_right₀ hS₁ (by norm_num)
  have hS9 : 1 ≤ (Λ ^ (K * (J + 2))) ^ 9 := one_le_pow₀ hS₁
  have hsum := sum_goodAtoms_le hΛ hp hband hcard hJ hY₁ hY
  refine (card_filter_visitBad_le (by linarith) hU hV hUV p hn z).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hNS : N * (Λ ^ (K * (J + 2))) ^ 2 ≤ N * (Λ ^ (K * (J + 2))) ^ 9 :=
    mul_le_mul_of_nonneg_left h29 (by linarith)
  have hN9 : (Λ ^ (K * (J + 2))) ^ 9 ≤ N * (Λ ^ (K * (J + 2))) ^ 9 := by nlinarith
  nlinarith [abs_nonneg (z.2 : ℝ)]

/-- Eventually `(N + 1) 10⁷ N exp(2 L^{1/5})^{9K(J+2)} ≤ exp(L^{1/2})`, `N = 2R`: with
`t = L^{1/100}`, `N + 1 ≤ t^{50} + 3`, `J ≤ t` and `L^{1/5} = t^{20}`. -/
theorem eventually_visits_le (K : ℕ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      ((2 * momentPower x : ℕ) + 1 : ℝ) * (10 ^ 7 * (2 * momentPower x : ℕ) *
          (Real.exp (2 * Real.log x ^ (1 / 5 : ℝ)) ^ (K * (padCount x + 2))) ^ 9) ≤
        Real.exp (Real.log x ^ (1 / 2 : ℝ)) := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp
    Real.tendsto_log_atTop
  filter_upwards [ht.eventually_ge_atTop (108 * K + 10 ^ 10),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hL
  set t := Real.log x ^ (1 / 100 : ℝ) with ht_def
  have hx' : 108 * K + 10 ^ 10 ≤ t := hx
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have ht₁ : 1 ≤ t := by linarith
  -- step: the powers of `L` as powers of `t`
  have hpow : ∀ k : ℕ, Real.log x ^ ((k : ℝ) / 100) = t ^ k := fun k => by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1
    ring
  have h50 : Real.log x ^ (1 / 2 : ℝ) = t ^ 50 := by
    rw [← hpow]
    norm_num
  have h20 : Real.log x ^ (1 / 5 : ℝ) = t ^ 20 := by
    rw [← hpow]
    norm_num
  -- step: `N ≤ t^{50} + 2` and `J ≤ t`
  have hR : (momentPower x : ℝ) < Real.log x ^ (1 / 2 : ℝ) / 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hN : ((2 * momentPower x : ℕ) : ℝ) ≤ t ^ 50 + 2 := by
    push_cast
    rw [h50] at hR
    linarith
  have hJ : (padCount x : ℝ) ≤ t := Nat.floor_le (by positivity)
  have hN0 : (0 : ℝ) ≤ ((2 * momentPower x : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht50 : 1 ≤ t ^ 50 := one_le_pow₀ ht₁
  -- step: the exponential factor is at most `exp(54 K t^{21})`
  have hexp : (Real.exp (2 * Real.log x ^ (1 / 5 : ℝ)) ^ (K * (padCount x + 2))) ^ 9 ≤
      Real.exp (t ^ 50 / 2) := by
    rw [← pow_mul, ← Real.exp_nat_mul, h20]
    refine Real.exp_le_exp.2 ?_
    push_cast
    have h21 : t ^ 21 ≤ t ^ 50 / (108 * K + 1) := by
      rw [le_div_iff₀ (by positivity)]
      have h29 : 108 * K + 1 ≤ t ^ 29 :=
        (by linarith : 108 * (K : ℝ) + 1 ≤ t).trans (le_self_pow₀ ht₁ (by norm_num))
      calc t ^ 21 * (108 * K + 1) ≤ t ^ 21 * t ^ 29 :=
            mul_le_mul_of_nonneg_left h29 (by positivity)
        _ = t ^ 50 := by ring
    have h21' : 108 * K * t ^ 21 ≤ t ^ 50 := by
      have := mul_le_mul_of_nonneg_left h21 (by positivity : (0 : ℝ) ≤ 108 * K + 1)
      rw [mul_div_cancel₀ _ (by positivity)] at this
      nlinarith [pow_pos (by linarith : (0 : ℝ) < t) 21]
    have hJ2 : (padCount x : ℝ) + 2 ≤ 3 * t := by linarith
    calc ((K : ℝ) * (padCount x + 2) * 9) * (2 * t ^ 20)
        ≤ (K * (3 * t) * 9) * (2 * t ^ 20) := by gcongr
      _ = 54 * K * t ^ 21 := by ring
      _ ≤ t ^ 50 / 2 := by linarith
  -- step: the polynomial factor is at most `exp(t^{50}/2)`
  have hpoly : ((2 * momentPower x : ℕ) + 1 : ℝ) * (10 ^ 7 * (2 * momentPower x : ℕ)) ≤
      Real.exp (t ^ 50 / 2) := by
    have hfac := Real.pow_div_factorial_le_exp (t ^ 50 / 2) (by positivity) 3
    have h3 : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h3] at hfac
    have hbig : 10 ^ 10 ≤ t ^ 50 := (by linarith : (10 : ℝ) ^ 10 ≤ t).trans
      (le_self_pow₀ ht₁ (by norm_num))
    have hy : (t ^ 50) ^ 2 * (4 * 10 ^ 7 * 48) ≤ (t ^ 50) ^ 2 * t ^ 50 :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    calc ((2 * momentPower x : ℕ) + 1 : ℝ) * (10 ^ 7 * (2 * momentPower x : ℕ))
        ≤ (2 * t ^ 50) * (10 ^ 7 * (2 * t ^ 50)) :=
          mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = 4 * 10 ^ 7 * (t ^ 50) ^ 2 := by ring
      _ ≤ (t ^ 50 / 2) ^ 3 / 6 := by nlinarith
      _ ≤ Real.exp (t ^ 50 / 2) := hfac
  rw [h50]
  calc ((2 * momentPower x : ℕ) + 1 : ℝ) * (10 ^ 7 * (2 * momentPower x : ℕ) *
        (Real.exp (2 * Real.log x ^ (1 / 5 : ℝ)) ^ (K * (padCount x + 2))) ^ 9)
      = (((2 * momentPower x : ℕ) + 1 : ℝ) * (10 ^ 7 * (2 * momentPower x : ℕ))) *
          (Real.exp (2 * Real.log x ^ (1 / 5 : ℝ)) ^ (K * (padCount x + 2))) ^ 9 := by ring
    _ ≤ Real.exp (t ^ 50 / 2) * Real.exp (t ^ 50 / 2) :=
        mul_le_mul hpoly hexp (by positivity) (by positivity)
    _ = Real.exp (t ^ 50) := by rw [← Real.exp_add]; ring_nf

end Erdos408.OneSided
