import Erdos408.Extraction.Allocation.Failure.VSide
import Mathlib.Data.Fin.Tuple.Finset

/-!
# Reduction to one free core factor

E6 begins with three reductions of `∑_w A_j(w + 1) F(w)`, all before any signed
expansion.

* `A_j = G_j ρ_j ≤ G_j`, since the allocation factor lies in `[0, 1]`, and the
  lower cutoff `w ≥ x/κ` is dropped.
* Chernoff: `F(w) ≤ e^{c₂ T} (Z_small(w) + Z_big(w))`, and
  `Z_F(w) = ∏_{g ∈ F} (1 - θ s_g(w)) ≤ ∏_{g ∈ F} (1 - α_g(v) ℓ(ω_g(u)))`.
* The core `G_j(v) = ∑_{e₁ ⋯ e_j = v̄} ∏ b(e_i)` is reparametrized by the
  candidate part `d = v_P` and the factors `e`, and the first factor `e₁` is
  made free: it runs over the rough `e₁ ∈ (⌊x^γ⌋, X / (r d)]` with
  `r = e₂ ⋯ e_j`. On the support `α_g(v) = α_g(d)`, as the factors carry no
  candidate prime.
-/

namespace Erdos408

open Finset Real

noncomputable section

/-- The weight `w(e) = 1/(D_j log e)` of a rough factor. -/
def roughWeight (x : ℝ) (j e : ℕ) : ℝ :=
  1 / (dampedDensity x j * Real.log e)

/-- The `u`-side product `Ψ_{F,d}(u) = ∏_{g ∈ F} (1 - α_g(d) ℓ(ω_g(u)))`. -/
def sideProd (c₁ : ℝ) (F : Finset (Finset ℕ)) (d u : ℕ) : ℝ :=
  ∏ g ∈ F, (1 - sideAlpha c₁ g d * ell (primeCount g u))

/-- The reduced sum over the candidate part `d`, the factors `e₂, …, e_j` and the free rough
factor `e₁`. -/
def freeFactorSum (x γ c₁ : ℝ) (j' X : ℕ) (F : Finset (Finset ℕ)) : ℝ :=
  ∑ d ∈ (Icc 1 X).filter (· ∈ Nat.factoredNumbers (candidatePrimes x)),
    ∑ e ∈ Fintype.piFinset (fun _ : Fin j' => Icc 1 X),
      (∏ i, coreFactor x γ (j' + 1) (e i)) *
        ∑ a ∈ Ioc ⌊x ^ γ⌋₊ (X / ((∏ i, e i) * d)),
          (if ∀ p ∈ primesIcc 2 (proxyCutoff x), ¬ p ∣ a then roughWeight x (j' + 1) a else 0) *
            sideProd c₁ F d (a * ((∏ i, e i) * d) - 1)

/-! ### Elementary facts -/

/-- Roughness: all prime factors exceed `Y` iff no prime `p ≤ Y` divides. -/
lemma forall_primeFactors_lt_iff {Y : ℝ} {a : ℕ} (ha : a ≠ 0) :
    (∀ p ∈ a.primeFactors, Y < p) ↔ ∀ p ∈ primesIcc 2 Y, ¬ p ∣ a := by
  constructor
  · intro h p hp hpa
    obtain ⟨hpr, -, hpY⟩ := mem_primesIcc.1 hp
    have := h p (Nat.mem_primeFactors.2 ⟨hpr, hpa, ha⟩)
    linarith
  · intro h p hp
    obtain ⟨hpr, hpa, -⟩ := Nat.mem_primeFactors.1 hp
    by_contra hY
    push Not at hY
    exact h p (mem_primesIcc.2 ⟨hpr, by exact_mod_cast hpr.two_le, hY⟩) hpa

/-- The primes of `g ⊆ P` see the same divisibility in `n` and in `n_P`. -/
lemma primeCount_keepPrimes_of_subset {g P : Finset ℕ} (hgP : g ⊆ P) (hg : ∀ p ∈ g, p.Prime)
    {n : ℕ} (hn : n ≠ 0) : primeCount g (keepPrimes P n) = primeCount g n := by
  unfold primeCount
  congr 1
  refine filter_congr fun p hp => ?_
  rw [(hg p hp).dvd_iff_one_le_factorization (keepPrimes_ne_zero P n),
    (hg p hp).dvd_iff_one_le_factorization hn, factorization_keepPrimes,
    Finsupp.filter_apply_pos _ _ (hgP hp)]

/-- The coefficient `α_g` only sees the primes of `g`. -/
lemma sideAlpha_congr {c₁ : ℝ} {g : Finset ℕ} {m n : ℕ} (h : primeCount g m = primeCount g n) :
    sideAlpha c₁ g m = sideAlpha c₁ g n := by
  unfold sideAlpha
  rw [markedWeight_singleton, markedWeight_singleton]
  simp only [id, h]

/-- `0 ≤ α_g ≤ 1` from `V_g ≥ 1/2` and `c₁ ≤ 1/4`. -/
lemma sideAlpha_mem_of_mass {c₁ : ℝ} (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1 / 4) {g : Finset ℕ}
    (hV : 1 / 2 ≤ harmonicMass g) (d : ℕ) : 0 ≤ sideAlpha c₁ g d ∧ sideAlpha c₁ g d ≤ 1 := by
  obtain ⟨h1, h2⟩ := markedWeight_half_mem hV d
  have hθ := chernoffTheta_pos
  have hθ1 := chernoffTheta_le_one
  unfold sideAlpha
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by linarith)]
  calc chernoffTheta * c₁ * markedWeight {g} (1 / 2) id d ≤ 1 * (1 / 4) * 2 := by gcongr
    _ ≤ harmonicMass g := by linarith

/-- `Ψ_{F,d} ≥ 0`. -/
lemma sideProd_nonneg {c₁ : ℝ} (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1 / 4) {F : Finset (Finset ℕ)}
    (hV : ∀ g ∈ F, 1 / 2 ≤ harmonicMass g) (d u : ℕ) : 0 ≤ sideProd c₁ F d u :=
  prod_nonneg fun g hg => by
    obtain ⟨h1, h2⟩ := sideAlpha_mem_of_mass hc₁ hc₁' (hV g hg) d
    have := ell_le_one (primeCount g u)
    nlinarith

/-- A sum over `(Fin (n + 1))`-tuples splits off the first coordinate. -/
lemma sum_piFinset_succ (I : Finset ℕ) (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℝ) :
    ∑ e ∈ Fintype.piFinset (fun _ : Fin (n + 1) => I), f e =
      ∑ a ∈ I, ∑ e' ∈ Fintype.piFinset (fun _ : Fin n => I), f (Fin.cons a e') := by
  have h := Finset.filter_piFinset_eq_map_consEquiv (S := fun _ : Fin (n + 1) => I)
    (fun _ => True)
  rw [filter_true_of_mem (fun _ _ => trivial), filter_true_of_mem (fun _ _ => trivial)] at h
  rw [h, sum_map, sum_product]
  rfl

/-! ### The reductions -/

/-- Chernoff with the depth-two bound, pointwise: `F(w) ≤ e^{c₂T} (Ψ_small(w) + Ψ_big(w))` with
`α_g` evaluated at `v = w + 1`. -/
lemma failureProb_le_sideProd {c₁ c₂ x : ℝ} (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1 / 4)
    (hV : ∀ g ∈ candidateGroups x, 1 / 2 ≤ harmonicMass g) (w : ℕ) :
    failureProb c₁ c₂ x w ≤ Real.exp (c₂ * logLog x) *
      (sideProd c₁ (smallGroups x) (w + 1) w + sideProd c₁ (bigGroups x) (w + 1) w) := by
  have hs : ∀ g ∈ candidateGroups x, 0 ≤ successCoin c₁ g w ∧ successCoin c₁ g w ≤ 1 :=
    fun g hg => successCoin_mem hc₁ hc₁' (hV g hg) w
  refine (failureProb_le_exp_mul hs).trans (mul_le_mul_of_nonneg_left ?_ (exp_pos _).le)
  have hZ : ∀ F ⊆ candidateGroups x, ∏ g ∈ F, (1 - chernoffTheta * successCoin c₁ g w) ≤
      sideProd c₁ F (w + 1) w := by
    intro F hF
    refine prod_le_prod₀ (fun g hg => ?_) fun g hg => ?_
    · have := (hs g (hF hg)).2
      have := chernoffTheta_le_one
      have := chernoffTheta_pos
      nlinarith [(hs g (hF hg)).1]
    · have hVg := hV g (hF hg)
      exact one_sub_mul_successCoin_le hc₁ (by linarith) w
  exact add_le_add (hZ _ subset_union_left) (hZ _ subset_union_right)

/-- The reparametrization: `∑_{w ≤ M} G_j(w + 1) Ψ_F(w)` is at most the sum over the candidate
part `d`, the factors `e` with `d ∏ e ≤ X`, of `∏ b(e_i) Ψ_{F,d}(d ∏ e - 1)`. -/
lemma sum_proxyCore_mul_sideProd_le {x γ c₁ : ℝ} (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1 / 4)
    (hγ : 1 ≤ x ^ γ) (hV : ∀ g ∈ candidateGroups x, 1 / 2 ≤ harmonicMass g) {j : ℕ}
    (hj : 1 ≤ j) {F : Finset (Finset ℕ)} (hF : F ⊆ candidateGroups x) (M : ℕ) :
    ∑ w ∈ Icc 1 M, proxyCore x γ j (w + 1) * sideProd c₁ F (w + 1) w ≤
      ∑ d ∈ (Icc 1 (M + 1)).filter (· ∈ Nat.factoredNumbers (candidatePrimes x)),
        ∑ e ∈ Fintype.piFinset (fun _ : Fin j => Icc 1 (M + 1)),
          (∏ i, coreFactor x γ j (e i)) *
            (if d * ∏ i, e i ≤ M + 1 then sideProd c₁ F d (d * ∏ i, e i - 1) else 0) := by
  classical
  set P := candidatePrimes x
  set D := (Icc 1 (M + 1)).filter (· ∈ Nat.factoredNumbers P)
  set I := Icc 1 (M + 1)
  set f : ℕ × (Fin j → ℕ) → ℝ := fun t => (∏ i, coreFactor x γ j (t.2 i)) *
    (if t.1 * ∏ i, t.2 i ≤ M + 1 then sideProd c₁ F t.1 (t.1 * ∏ i, t.2 i - 1) else 0)
  have hFV : ∀ g ∈ F, 1 / 2 ≤ harmonicMass g := fun g hg => hV g (hF hg)
  have hf0 : ∀ t, 0 ≤ f t := fun t => mul_nonneg
    (prod_nonneg fun i _ => coreFactor_nonneg hj hγ _)
    (by split_ifs; exacts [sideProd_nonneg hc₁ hc₁' hFV _ _, le_rfl])
  have hgP : ∀ g ∈ F, g ⊆ P := fun g hg p hp => mem_biUnion.2 ⟨g, hF hg, hp⟩
  have hgpr : ∀ g ∈ F, ∀ p ∈ g, p.Prime := fun g hg p hp =>
    prime_of_mem_candidatePrimes (hgP g hg hp)
  -- the left side as a sum over pairs `(w, e)` with `e₁ ⋯ e_j = (w + 1)‾`
  set Sw := (Icc 1 M).sigma fun w => Nat.finMulAntidiag j (stripPrimes P (w + 1))
  have hlhs : ∑ w ∈ Icc 1 M, proxyCore x γ j (w + 1) * sideProd c₁ F (w + 1) w =
      ∑ t ∈ Sw, (∏ i, coreFactor x γ j (t.2 i)) * sideProd c₁ F (t.1 + 1) t.1 := by
    rw [sum_sigma]
    refine sum_congr rfl fun w _ => ?_
    rw [proxyCore, sum_mul]
    rfl
  -- the injection `(w, e) ↦ (v_P, e)`
  set φ : (Σ _ : ℕ, Fin j → ℕ) → ℕ × (Fin j → ℕ) := fun t => (keepPrimes P (t.1 + 1), t.2)
  have hφ : ∀ t ∈ Sw, keepPrimes P (t.1 + 1) * ∏ i, t.2 i = t.1 + 1 := by
    intro t ht
    obtain ⟨-, he⟩ := mem_sigma.1 ht
    rw [Nat.prod_eq_of_mem_finMulAntidiag he, mul_comm, stripPrimes_mul_keepPrimes P (by omega)]
  have hinj : Set.InjOn φ Sw := by
    intro t ht t' ht' h
    simp only [φ, Prod.mk.injEq] at h
    have h1 : t.1 + 1 = t'.1 + 1 := by rw [← hφ t ht, ← hφ t' ht', h.1, h.2]
    exact Sigma.ext (by omega) (heq_of_eq h.2)
  have hmaps : ∀ t ∈ Sw, φ t ∈ D ×ˢ Fintype.piFinset (fun _ : Fin j => I) := by
    intro t ht
    obtain ⟨hw, he⟩ := mem_sigma.1 ht
    have hw' := mem_Icc.1 hw
    have hkd : keepPrimes P (t.1 + 1) ∣ t.1 + 1 := ⟨stripPrimes P (t.1 + 1), by
      rw [mul_comm, stripPrimes_mul_keepPrimes P (by omega)]⟩
    have hsd : stripPrimes P (t.1 + 1) ∣ t.1 + 1 := ⟨keepPrimes P (t.1 + 1), by
      rw [stripPrimes_mul_keepPrimes P (by omega)]⟩
    refine mem_product.2 ⟨mem_filter.2 ⟨mem_Icc.2 ⟨Nat.pos_of_ne_zero (keepPrimes_ne_zero _ _),
      (Nat.le_of_dvd (by omega) hkd).trans (by omega)⟩, ?_⟩, Fintype.mem_piFinset.2 fun i => ?_⟩
    · exact Nat.mem_factoredNumbers_of_primeFactors_subset (keepPrimes_ne_zero _ _)
        fun p hp => mem_of_mem_primeFactors_keepPrimes hp
    · exact mem_Icc.2 ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_finMulAntidiag he i),
        (Nat.le_of_dvd (by omega) ((Nat.dvd_of_mem_finMulAntidiag he i).trans hsd)).trans
          (by omega)⟩
  have hval : ∀ t ∈ Sw, (∏ i, coreFactor x γ j (t.2 i)) * sideProd c₁ F (t.1 + 1) t.1 =
      f (φ t) := by
    intro t ht
    have h1 := hφ t ht
    have hw := (mem_Icc.1 (mem_sigma.1 ht).1).2
    simp only [f, φ, h1, show t.1 + 1 ≤ M + 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
    congr 1
    unfold sideProd
    refine prod_congr rfl fun g hg => ?_
    rw [sideAlpha_congr (primeCount_keepPrimes_of_subset (hgP g hg) (hgpr g hg) (by omega))]
  rw [hlhs, sum_congr rfl hval, ← sum_image (f := f) hinj]
  refine (sum_le_sum_of_subset_of_nonneg (t := D ×ˢ Fintype.piFinset (fun _ : Fin j => I))
    (fun s hs => by obtain ⟨t, ht, rfl⟩ := mem_image.1 hs; exact hmaps t ht)
    fun s _ _ => hf0 s).trans (le_of_eq ?_)
  rw [sum_product]

/-- The first factor made free: the reparametrized sum is `freeFactorSum`. -/
lemma sum_tuples_eq_freeFactorSum {x γ c₁ : ℝ} (hγ : 0 ≤ x ^ γ) (j' X : ℕ)
    (F : Finset (Finset ℕ)) :
    ∑ d ∈ (Icc 1 X).filter (· ∈ Nat.factoredNumbers (candidatePrimes x)),
        ∑ e ∈ Fintype.piFinset (fun _ : Fin (j' + 1) => Icc 1 X),
          (∏ i, coreFactor x γ (j' + 1) (e i)) *
            (if d * ∏ i, e i ≤ X then sideProd c₁ F d (d * ∏ i, e i - 1) else 0) =
      freeFactorSum x γ c₁ j' X F := by
  unfold freeFactorSum
  refine sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (mem_Icc.1 (mem_filter.1 hd).1).1
  rw [sum_piFinset_succ, sum_comm]
  refine sum_congr rfl fun e he => ?_
  have hr1 : 1 ≤ ∏ i, e i := by
    rw [Nat.one_le_iff_ne_zero, prod_ne_zero_iff]
    exact fun i _ => by have := (mem_Icc.1 (Fintype.mem_piFinset.1 he i)).1; omega
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  generalize ∏ i, e i = r at hr1 ⊢
  have hrd : 0 < r * d := Nat.mul_pos (by omega) (by omega)
  rw [mul_sum]
  have hsub : Ioc ⌊x ^ γ⌋₊ (X / (r * d)) ⊆ Icc 1 X := by
    intro a ha
    obtain ⟨h1, h2⟩ := mem_Ioc.1 ha
    exact mem_Icc.2 ⟨by omega, h2.trans (Nat.div_le_self _ _)⟩
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun a ha => ?_
    obtain ⟨h1, h2⟩ := mem_Ioc.1 ha
    have hxa : x ^ γ < a := (Nat.floor_lt hγ).1 h1
    have hle : d * (a * r) ≤ X := by
      have := (Nat.le_div_iff_mul_le hrd).1 h2
      calc d * (a * r) = a * (r * d) := by ring
        _ ≤ X := this
    have heq : d * (a * r) - 1 = a * (r * d) - 1 := by ring_nf
    rw [ite_eq_left hle, heq]
    by_cases hr : ∀ p ∈ primesIcc 2 (proxyCutoff x), ¬ p ∣ a
    · have hr' := (forall_primeFactors_lt_iff (Y := proxyCutoff x) (by omega)).2 hr
      rw [coreFactor, ite_eq_left ⟨hxa, hr'⟩, ite_eq_left hr, roughWeight]
      ring
    · have hr' : ¬ (x ^ γ < a ∧ ∀ p ∈ a.primeFactors, proxyCutoff x < p) := fun h =>
        hr ((forall_primeFactors_lt_iff (by omega)).1 h.2)
      rw [coreFactor, ite_eq_right hr', ite_eq_right hr]
      ring
  · intro a ha hna
    rw [mem_Ioc, not_and_or] at hna
    rcases hna with h | h
    · have : ¬ (x ^ γ < a ∧ ∀ p ∈ a.primeFactors, proxyCutoff x < p) := fun h' =>
        h ((Nat.floor_lt hγ).2 h'.1)
      rw [coreFactor, ite_eq_right this]
      ring
    · have : ¬ d * (a * r) ≤ X := by
        intro h'
        apply h
        rw [Nat.le_div_iff_mul_le hrd]
        calc a * (r * d) = d * (a * r) := by ring
          _ ≤ X := h'
      rw [ite_eq_right this]
      ring

/-- The reductions of E6: `∑_{x/κ ≤ w ≤ κ x} A_j(w + 1) F(w)` is at most `e^{c₂ T}` times the
free-factor sums of the two families. -/
theorem sum_proxyCoeff_mul_failureProb_le {x γ c₁ c₂ κ : ℝ} (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1 / 4)
    (hγ : 1 ≤ x ^ γ) (hV : ∀ g ∈ candidateGroups x, 1 / 2 ≤ harmonicMass g) (j' : ℕ) :
    ∑ w ∈ Icc 1 ⌊κ * x⌋₊ with x / κ ≤ ((w : ℕ) : ℝ),
        proxyCoeff x γ (j' + 1) (w + 1) * failureProb c₁ c₂ x w ≤
      Real.exp (c₂ * logLog x) * (freeFactorSum x γ c₁ j' (⌊κ * x⌋₊ + 1) (smallGroups x) +
        freeFactorSum x γ c₁ j' (⌊κ * x⌋₊ + 1) (bigGroups x)) := by
  set M := ⌊κ * x⌋₊
  have hj : 1 ≤ j' + 1 := by omega
  have hs : ∀ w, ∀ g ∈ candidateGroups x, 0 ≤ successCoin c₁ g w ∧ successCoin c₁ g w ≤ 1 :=
    fun w g hg => successCoin_mem hc₁ hc₁' (hV g hg) w
  have hF0 : ∀ w, 0 ≤ failureProb c₁ c₂ x w := fun w => failureProb_nonneg (hs w)
  have hG0 : ∀ v, 0 ≤ proxyCore x γ (j' + 1) v := proxyCore_nonneg hj hγ
  have hAG : ∀ w, proxyCoeff x γ (j' + 1) (w + 1) ≤ proxyCore x γ (j' + 1) (w + 1) := by
    intro w
    rw [proxyCoeff_eq x γ _ (by omega)]
    exact mul_le_of_le_one_right (hG0 _) (allocationFactor_le_one x hj _)
  have hA0 : ∀ w, 0 ≤ proxyCoeff x γ (j' + 1) (w + 1) := by
    intro w
    rw [proxyCoeff_eq x γ _ (by omega)]
    exact mul_nonneg (hG0 _) (allocationFactor_nonneg x _ _)
  have hFV : ∀ F ⊆ candidateGroups x, ∀ g ∈ F, 1 / 2 ≤ harmonicMass g :=
    fun F hF g hg => hV g (hF hg)
  calc ∑ w ∈ Icc 1 M with x / κ ≤ ((w : ℕ) : ℝ),
        proxyCoeff x γ (j' + 1) (w + 1) * failureProb c₁ c₂ x w
      ≤ ∑ w ∈ Icc 1 M, proxyCoeff x γ (j' + 1) (w + 1) * failureProb c₁ c₂ x w :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun w _ _ =>
          mul_nonneg (hA0 w) (hF0 w)
    _ ≤ ∑ w ∈ Icc 1 M, proxyCore x γ (j' + 1) (w + 1) * (Real.exp (c₂ * logLog x) *
          (sideProd c₁ (smallGroups x) (w + 1) w + sideProd c₁ (bigGroups x) (w + 1) w)) :=
        sum_le_sum fun w _ => mul_le_mul (hAG w) (failureProb_le_sideProd hc₁ hc₁' hV w)
          (hF0 w) (hG0 _)
    _ = Real.exp (c₂ * logLog x) *
          (∑ w ∈ Icc 1 M, proxyCore x γ (j' + 1) (w + 1) * sideProd c₁ (smallGroups x) (w + 1) w +
            ∑ w ∈ Icc 1 M,
              proxyCore x γ (j' + 1) (w + 1) * sideProd c₁ (bigGroups x) (w + 1) w) := by
        rw [← sum_add_distrib, mul_sum]
        exact sum_congr rfl fun w _ => by ring
    _ ≤ _ := by
        gcongr
        · rw [← sum_tuples_eq_freeFactorSum (by linarith)]
          exact sum_proxyCore_mul_sideProd_le hc₁ hc₁' hγ hV hj subset_union_left M
        · rw [← sum_tuples_eq_freeFactorSum (by linarith)]
          exact sum_proxyCore_mul_sideProd_le hc₁ hc₁' hγ hV hj subset_union_right M

end

end Erdos408
