import Erdos408.OneSided.Decomposition.Lists
import Erdos408.OneSided.Decomposition.Pair

/-!
# The lift identity

PD Lemma 4.1 (`blueprint/one_sided_type_ii.md` §4). Index the coprime-pair error, weighted
by distinct pads disjoint from the labels, by `(p, p', z, m, n, r, s)`: label tuples
`p, p'` with products `a, b`, pads `z` with product `D`, and `m, n, r, s`. The change of
variables `P = (D b m, s)`, `Q = (D a r, n)` with lists `(z, p')` and `(z, p)` is a
bijection onto the pairs of states on which `⟨f, 𝒯 f⟩` has a nonzero term, and it matches
the terms of the pad dyad `[2^k, 2^{k+1})` containing `D` with those of
`2^{-k} ⟨f, 𝒯 f⟩_{2^k}`.

* `det(P, Q) = D (bmn - ars)`, so `det(P, Q)/D = t`.
* `2^{-k} ∏V^{-(J+1)} ∏V⁻¹ (2^k/D) = ∏V⁻² ∏_c μ(z_c)` with `μ_i(p) = 1/(p V_i)`.
* `m` and `r` are rough, so the damping is one and `P₁ / (list product) = m`.
* `P` and `Q` are primitive: a common prime of `m` and `s` exceeds `W ≥ 5Y > |t|` and
  divides `t ≠ 0`.
-/

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

/-! ### The index set and the terms -/

/-- The probability `∏_c μ(z_c)` of the pads, `μ_i(p) = 1/(p V_i)`. -/
noncomputable def padWeight (x : ℝ) (d : Data K) {J : ℕ} (z : Fin K × Fin J → ℕ) : ℝ :=
  ∏ c, 1 / ((z c : ℝ) * harmonicMass (band x (d.a c.1)))

/-- The label tuples share no prime. -/
def Unshared (p p' : Fin K → ℕ) : Prop := ∀ i i', p i ≠ p' i'

/-- The pads are distinct and differ from every label of `p` and `p'` in their group. -/
def GoodPads {J : ℕ} (p p' : Fin K → ℕ) (z : Fin K × Fin J → ℕ) : Prop :=
  Function.Injective z ∧ ∀ c, z c ≠ p c.1 ∧ z c ≠ p' c.1

/-- The index `(p, p', z, m, n, r, s)` of the lift. -/
abbrev LiftIndex (K J : ℕ) :=
  ((Fin K → ℕ) × (Fin K → ℕ)) × ((Fin K × Fin J → ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)))

open scoped Classical in
/-- The indices with unshared labels and good pads. -/
noncomputable def liftIndex (x : ℝ) (d : Data K) : Finset (LiftIndex K (padCount x)) :=
  ((d.labels x ×ˢ d.labels x) ×ˢ (padSet x d (padCount x) ×ˢ
      ((d.mRange ×ˢ d.nRange) ×ˢ (d.mRange ×ˢ d.nRange)))).filter
    fun a => Unshared a.1.1 a.1.2 ∧ GoodPads a.1.1 a.1.2 a.2.1

/-- The determinant `t = bmn - ars`. -/
def liftDet (p p' : Fin K → ℕ) (m n r s : ℕ) : ℤ :=
  (∏ i, p' i : ℕ) * m * n - (∏ i, p i : ℕ) * r * s

open scoped Classical in
/-- The term `∏V⁻² ∏μ(z) η(a/Y) η(b/Y) ψ(t/Y) α_m ᾱ_r β_n β̄_s ([t = b - a] - ∫_𝔐 e(θ(t - b + a)))`
of the weighted coprime-pair error. -/
noncomputable def liftTerm (A₀ x : ℝ) (d : Data K) (Y : ℝ) {J : ℕ} (a : LiftIndex K J) : ℂ :=
  (((d.bandMass x)⁻¹ ^ 2 * padWeight x d a.2.1 * dyadicBump ((∏ i, a.1.1 i : ℕ) / Y) *
      dyadicBump ((∏ i, a.1.2 i : ℕ) / Y) *
      plateau (liftDet a.1.1 a.1.2 a.2.2.1.1 a.2.2.1.2 a.2.2.2.1 a.2.2.2.2 / Y) : ℝ) : ℂ) *
    (d.α a.2.2.1.1 * star (d.α a.2.2.2.1) * d.β a.2.2.1.2 * star (d.β a.2.2.2.2) *
      ((if liftDet a.1.1 a.1.2 a.2.2.1.1 a.2.2.1.2 a.2.2.2.1 a.2.2.2.2 =
          (∏ i, a.1.2 i : ℕ) - (∏ i, a.1.1 i : ℕ) then 1 else 0) -
        arcIntegral A₀ x Y (liftDet a.1.1 a.1.2 a.2.2.1.1 a.2.2.1.2 a.2.2.2.1 a.2.2.2.2 -
          (∏ i, a.1.2 i : ℕ) + (∏ i, a.1.1 i : ℕ))))

/-- The source and target states `((D b m, s), (z, p'))` and `((D a r, n), (z, p))`. -/
def liftStates {J : ℕ} (a : LiftIndex K J) : ((ℕ × ℕ) × Lists K J) × ((ℕ × ℕ) × Lists K J) :=
  (((listProd (padList a.2.1 a.1.2) * a.2.2.1.1, a.2.2.2.2), padList a.2.1 a.1.2),
    ((listProd (padList a.2.1 a.1.1) * a.2.2.2.1, a.2.2.1.2), padList a.2.1 a.1.1))

/-- The term of `2^{-k} ⟨f, 𝒯 f⟩_{2^k}` at a pair of states. -/
noncomputable def stateTerm (q A₀ x : ℝ) (d : Data K) (Y : ℝ) (k : ℕ)
    (w : ((ℕ × ℕ) × Lists K (padCount x)) × ((ℕ × ℕ) × Lists K (padCount x))) : ℂ :=
  ((2 : ℂ) ^ k)⁻¹ * (stateMass x d : ℂ) *
    (star (star (d.α (w.1.1.1 / listProd w.1.2)) * d.β w.1.1.2) *
      (rowEntry q A₀ x d Y (2 ^ k) w.1 w.2 *
        (star (d.α (w.2.1.1 / listProd w.2.2)) * d.β w.2.1.2)))

/-- `2^{-k} ⟨f, 𝒯 f⟩_{2^k}` is the sum of `stateTerm` over pairs of states. -/
theorem inv_mul_rowPairing_eq (q A₀ x : ℝ) (d : Data K) (Y : ℝ) (k : ℕ) :
    ((2 : ℂ) ^ k)⁻¹ * rowPairing q A₀ x d Y (2 ^ k) =
      ∑ w ∈ states x d Y (2 ^ k) ×ˢ states x d Y (2 ^ k), stateTerm q A₀ x d Y k w := by
  rw [rowPairing_eq, ← mul_assoc, sum_product, mul_sum]
  simp only [mul_sum]
  rfl

/-! ### Support facts -/

/-- The label tuples are primes of their bands. -/
theorem mem_band_of_mem_labels {x : ℝ} {d : Data K} {p : Fin K → ℕ} (hp : p ∈ d.labels x)
    (i : Fin K) : p i ∈ band x (d.a i) :=
  Fintype.mem_piFinset.1 hp i

/-- The pads are primes of their bands. -/
theorem mem_band_of_mem_padSet {x : ℝ} {d : Data K} {J : ℕ} {z : Fin K × Fin J → ℕ}
    (hz : z ∈ padSet x d J) (c : Fin K × Fin J) : z c ∈ band x (d.a c.1) :=
  Fintype.mem_piFinset.1 hz c

/-- The labels of `padList z p` are primes of their bands. -/
theorem mem_band_padList {x : ℝ} {d : Data K} {J : ℕ} {z : Fin K × Fin J → ℕ}
    (hz : z ∈ padSet x d J) {p : Fin K → ℕ} (hp : p ∈ d.labels x) (i : Fin K)
    (h : Fin (J + 1)) : padList z p i h ∈ band x (d.a i) := by
  induction h using Fin.lastCases with
  | last => rw [padList_last]; exact mem_band_of_mem_labels hp i
  | cast h => rw [padList_castSucc]; exact mem_band_of_mem_padSet hz (i, h)

/-- Distinct pads differing from the last labels give lists in `lists`. -/
theorem padList_mem_lists {x : ℝ} {d : Data K} {J : ℕ} {z : Fin K × Fin J → ℕ}
    (hz : z ∈ padSet x d J) (hzinj : Function.Injective z) {p : Fin K → ℕ}
    (hp : p ∈ d.labels x) (hzp : ∀ c, z c ≠ p c.1) : padList z p ∈ lists x d J := by
  unfold lists
  refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun h =>
    mem_band_padList hz hp i h, fun i => ?_⟩
  refine Fin.snoc_injective_iff.2 ⟨fun h h' hh => ?_, ?_⟩
  · have := hzinj hh
    simp only [Prod.mk.injEq, true_and] at this
    exact this
  · rintro ⟨h, hh⟩
    exact hzp (i, h) hh

/-- The coprime labels and rough `m, n`: `bmn ≠ ars` once `a > 1`, since `a` is coprime to
`bmn`. -/
theorem liftDet_ne_zero {x : ℝ} {d : Data K}
    (hrough : ∀ i, ∀ r ∈ band x (d.a i), ∀ m : ℕ, m ≠ 0 → IsRough x m → ¬ r ∣ m)
    {p p' : Fin K → ℕ} (hp : p ∈ d.labels x) (hp' : p' ∈ d.labels x) (hU : Unshared p p')
    (ha : 1 < ∏ i, p i) {m n : ℕ} (hm : m ≠ 0) (hmr : IsRough x m) (hn : n ≠ 0)
    (hnr : IsRough x n) (r s : ℕ) : liftDet p p' m n r s ≠ 0 := by
  have hprime : ∀ i, (p i).Prime := fun i => (mem_filter.1 (mem_band_of_mem_labels hp i)).2
  have hprime' : ∀ i, (p' i).Prime := fun i => (mem_filter.1 (mem_band_of_mem_labels hp' i)).2
  -- `a` is coprime to `b`, `m` and `n`
  have hab : Nat.Coprime (∏ i, p i) (∏ i, p' i) :=
    Nat.Coprime.prod_left fun i _ => Nat.Coprime.prod_right fun i' _ =>
      (Nat.coprime_primes (hprime i) (hprime' i')).2 (hU i i')
  have hcop : ∀ k : ℕ, k ≠ 0 → IsRough x k → Nat.Coprime (∏ i, p i) k := fun k hk hkr =>
    Nat.Coprime.prod_left fun i _ =>
      (Nat.Prime.coprime_iff_not_dvd (hprime i)).2
        (hrough i _ (mem_band_of_mem_labels hp i) k hk hkr)
  intro h
  unfold liftDet at h
  have heq : (∏ i, p' i) * m * n = (∏ i, p i) * (r * s) := by
    rw [sub_eq_zero] at h
    rw [← mul_assoc]
    exact_mod_cast h
  have hdvd : (∏ i, p i) ∣ (∏ i, p' i) * m * n := ⟨r * s, heq⟩
  have := Nat.Coprime.eq_one_of_dvd ((hab.mul_right (hcop m hm hmr)).mul_right (hcop n hn hnr)) hdvd
  omega

/-- A source or target state `((D b m, s), (z, p))` of the lift is a state at the dyad
`2^k ∋ D`: its position lies in `Ω` by the supports, and it is primitive since every common
prime of `m` and `s` divides `t ≠ 0` with `|t| < W`. -/
theorem mem_states_of {C CX alo ahi g x : ℝ} {d : Data K} (hd : Admissible C CX alo ahi g x d)
    (hrough : ∀ i, ∀ r ∈ band x (d.a i), ∀ m : ℕ, m ≠ 0 → IsRough x m → ¬ r ∣ m)
    (hHm : 0 < d.Hm) (hHn : 0 < d.Hn) {Y : ℝ} (hY : 0 < Y) {k : ℕ}
    {z : Fin K × Fin (padCount x) → ℕ}
    (hz : z ∈ padSet x d (padCount x)) (hzinj : Function.Injective z)
    (hD : 2 ^ k ≤ ∏ c, z c ∧ ∏ c, z c < 2 ^ (k + 1)) {p : Fin K → ℕ} (hp : p ∈ d.labels x)
    (hzp : ∀ c, z c ≠ p c.1) (hpY : Y < (∏ i, p i : ℕ) ∧ ((∏ i, p i : ℕ) : ℝ) < 4 * Y)
    {m s : ℕ} (hm : d.α m ≠ 0) (hs : d.β s ≠ 0) (hsR : s ∈ d.nRange) {t : ℤ} (ht : t ≠ 0)
    (htW : |(t : ℝ)| < roughLevel x) (hms : ∀ r : ℕ, r.Prime → r ∣ m → r ∣ s → (r : ℤ) ∣ t) :
    ((listProd (padList z p) * m, s), padList z p) ∈ states x d Y (2 ^ k) := by
  set l := padList z p
  have hlb : ∀ i h, l i h ∈ band x (d.a i) := mem_band_padList hz hp
  have hlprime : ∀ i h, (l i h).Prime := fun i h => (mem_filter.1 (hlb i h)).2
  have hl : l ∈ lists x d (padCount x) := padList_mem_lists hz hzinj hp hzp
  obtain ⟨hmH, hm2, hmr, -⟩ := hd.α_supp m hm
  obtain ⟨hsH, -, hsr, -⟩ := hd.β_supp s hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at hsH
    linarith
  -- the position: `D b m ∈ [2^k Y H_m, 16 · 2^k Y H_m]`
  have hP : ((listProd l * m : ℕ) : ℝ) = (∏ c, z c : ℕ) * (∏ i, p i : ℕ) * m := by
    rw [listProd_padList]
    push_cast
    ring
  have hD₁ : (2 : ℝ) ^ k ≤ (∏ c, z c : ℕ) := by exact_mod_cast hD.1
  have hD₂ : ((∏ c, z c : ℕ) : ℝ) ≤ 2 * 2 ^ k := by
    have : ((∏ c, z c : ℕ) : ℝ) < 2 ^ (k + 1) := by exact_mod_cast hD.2
    rw [pow_succ] at this
    linarith
  have hm2' : (m : ℝ) ≤ 2 * d.Hm := hm2
  unfold states positions
  refine mem_filter.2 ⟨mem_product.2 ⟨mem_filter.2 ⟨mem_product.2 ⟨mem_Icc.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩,
    hl⟩, ?_⟩
  · rw [Nat.ceil_le, hP]
    gcongr
    exact hpY.1.le
  · refine Nat.le_floor ?_
    rw [hP]
    calc ((∏ c, z c : ℕ) : ℝ) * (∏ i, p i : ℕ) * m ≤ (2 * 2 ^ k) * (4 * Y) * (2 * d.Hm) := by
          gcongr
          exact hpY.2.le
      _ = 16 * (2 ^ k * Y * d.Hm) := by ring
  · exact hsR
  · refine coprime_mul_of_isRough (fun r hr hdvd => ?_) hs0 hsr ht htW hms
    obtain ⟨i, h, rfl⟩ := exists_eq_of_prime_dvd_listProd hlprime hr hdvd
    exact hrough i _ (hlb i h) s hs0 hsr
  · intro i h
    exact Dvd.dvd.mul_right ((dvd_prod_of_mem (l i) (mem_univ h)).trans
      (dvd_prod_of_mem (fun i => ∏ h, l i h) (mem_univ i))) _


/-- `∏_c μ(z_c) = D⁻¹ ∏V_i^{-J}`. -/
theorem padWeight_eq (x : ℝ) (d : Data K) {J : ℕ} (z : Fin K × Fin J → ℕ) :
    padWeight x d z = ((∏ c, z c : ℕ) : ℝ)⁻¹ * (d.bandMass x)⁻¹ ^ J := by
  simp [padWeight, Data.bandMass, Fintype.prod_prod_type, prod_mul_distrib, prod_inv_distrib,
    prod_pow]
  ring

open scoped Classical in
/-- **The terms match.** At an index in the dyad `k` with `α_m, α_r ≠ 0`, the term of the
weighted coprime-pair error equals the term of `2^{-k} ⟨f, 𝒯 f⟩_{2^k}` at the image. -/
theorem liftTerm_eq_stateTerm (q A₀ : ℝ) {C CX alo ahi g x : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hrough : ∀ i, ∀ r ∈ band x (d.a i), ∀ m : ℕ, m ≠ 0 → IsRough x m → ¬ r ∣ m)
    (hHm : 0 < d.Hm) (hV : 0 < d.bandMass x) (Y : ℝ) {k : ℕ} {a : LiftIndex K (padCount x)}
    (ha : a ∈ liftIndex x d) (hk : Nat.log 2 (∏ c, a.2.1 c) = k) (hm : d.α a.2.2.1.1 ≠ 0)
    (hr : d.α a.2.2.2.1 ≠ 0) :
    liftTerm A₀ x d Y a = stateTerm q A₀ x d Y k (liftStates a) := by
  obtain ⟨⟨p, p'⟩, z, ⟨m, n⟩, r, s⟩ := a
  simp only [liftIndex, mem_filter, mem_product] at ha
  obtain ⟨⟨⟨hp, hp'⟩, hz, -, -⟩, hU, hzinj, hzp⟩ := ha
  simp only at hk hm hr
  have hD0 : 0 < ∏ c, z c := prod_pos fun c _ => (mem_filter.1 (mem_band_of_mem_padSet hz c)).2.pos
  have hD₁ : (2 : ℝ) ^ k ≤ (∏ c, z c : ℕ) := by
    rw [← hk]
    exact_mod_cast Nat.pow_log_le_self 2 hD0.ne'
  have hD₂ : ((∏ c, z c : ℕ) : ℝ) < 2 * 2 ^ k := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (∏ c, z c)
    rw [hk, pow_succ] at this
    rw [mul_comm]
    exact_mod_cast this
  have hl := padList_mem_lists hz hzinj hp' fun c => (hzp c).2
  have hl' := padList_mem_lists hz hzinj hp fun c => (hzp c).1
  have hlpos := listProd_pos fun i h => (mem_filter.1 (mem_band_padList hz hp' i h)).2
  have hlpos' := listProd_pos fun i h => (mem_filter.1 (mem_band_padList hz hp i h)).2
  obtain ⟨hmH, -, hmr, -⟩ := hd.α_supp m hm
  obtain ⟨hrH, -, hrr, -⟩ := hd.α_supp r hr
  have hm0 : m ≠ 0 := by rintro rfl; rw [Nat.cast_zero] at hmH; linarith
  have hr0 : r ≠ 0 := by rintro rfl; rw [Nat.cast_zero] at hrH; linarith
  -- `det(P, Q) = D t`
  have hdet : det (listProd (padList z p') * m, s) (listProd (padList z p) * r, n) =
      ((∏ c, z c : ℕ) : ℤ) * liftDet p p' m n r s := by
    simp only [det, listProd_padList, liftDet]
    push_cast
    ring
  have hdiv : det (listProd (padList z p') * m, s) (listProd (padList z p) * r, n) /
      ((∏ c, z c : ℕ) : ℤ) =
      liftDet p p' m n r s := by
    rw [hdet, Int.mul_ediv_cancel_left _ (by exact_mod_cast hD0.ne')]
  -- the edge exists: pads copied, cross-edge ban, dyad, `D ∣ det`
  have hcond : (∀ i (h : Fin (padCount x)), padList z p i h.castSucc = padList z p' i h.castSucc) ∧
      (∀ i i' h', padList z p i (Fin.last _) ≠ padList z p' i' h') ∧
      (2 : ℝ) ^ k ≤ (padProd (padList z p') : ℝ) ∧
      (padProd (padList z p') : ℝ) < 2 * 2 ^ k ∧
      (padProd (padList z p') : ℤ) ∣
        det (listProd (padList z p') * m, s) (listProd (padList z p) * r, n) := by
    refine ⟨fun i h => by simp, fun i i' h' => ?_, by rwa [padProd_padList],
      by rwa [padProd_padList], by rw [padProd_padList, hdet]; exact dvd_mul_right _ _⟩
    rw [padList_last]
    induction h' using Fin.lastCases with
    | last => rw [padList_last]; exact hU i i'
    | cast h =>
      rw [padList_castSucc]
      by_cases hii : i = i'
      · subst hii
        exact fun h' => (hzp (i, h)).1 h'.symm
      · intro h'
        exact disjoint_left.1 (hdisj i i' hii) (mem_band_of_mem_labels hp i)
          (h' ▸ mem_band_of_mem_padSet hz (i', h))
  -- the damping is one
  have hq : (((bandCount x d (listProd (padList z p') * m) : ℝ) - K * (padCount x + 1)) / 2 +
      ((bandCount x d (listProd (padList z p) * r) : ℝ) - K * (padCount x + 1)) / 2) = 0 := by
    rw [bandCount_listProd_mul hdisj hrough hl hm0 hmr,
      bandCount_listProd_mul hdisj hrough hl' hr0 hrr]
    push_cast
    ring
  unfold stateTerm rowEntry liftTerm liftStates
  simp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), hq, Real.rpow_zero,
    Nat.mul_div_cancel_left _ hlpos, Nat.mul_div_cancel_left _ hlpos']
  simp only [padProd_padList, lastProd_padList, hdiv, padWeight_eq, stateMass]
  have hV0 : (d.bandMass x : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
  have hD0' : ((∏ c, z c : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hD0.ne'
  simp only [star_mul', star_star]
  push_cast
  have h2 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  simp only [inv_pow]
  field_simp
  ring

/-- The dyad of the pad product: `2^k ≤ D < 2^{k+1}` for `k = ⌊log₂ D⌋`, `D ≥ 1`. -/
theorem pow_le_and_lt_of_log_eq {D k : ℕ} (hD : 0 < D) (hk : Nat.log 2 D = k) :
    2 ^ k ≤ D ∧ D < 2 ^ (k + 1) := by
  subst hk
  exact ⟨Nat.pow_log_le_self 2 hD.ne', Nat.lt_pow_succ_log_self (by norm_num) D⟩

/-- A marked variable in the support of `α` lies in `[H_m, 2H_m]`. -/
theorem mem_mRange_of_α_ne_zero {C CX alo ahi g x : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d) {m : ℕ} (hm : d.α m ≠ 0) : m ∈ d.mRange := by
  obtain ⟨h₁, h₂, -, -⟩ := hd.α_supp m hm
  exact mem_Icc.2 ⟨Nat.ceil_le.2 h₁, Nat.le_floor h₂⟩

open scoped Classical in
/-- The image of an index with a nonzero term is a pair of states at the dyad `k`. -/
theorem liftStates_mem {C CX alo ahi g x : ℝ} {d : Data K} (A₀ : ℝ)
    (hd : Admissible C CX alo ahi g x d)
    (hrough : ∀ i, ∀ r ∈ band x (d.a i), ∀ m : ℕ, m ≠ 0 → IsRough x m → ¬ r ∣ m)
    (hHm : 0 < d.Hm) (hHn : 0 < d.Hn) {Y : ℝ} (hY : 1 ≤ Y)
    (hYW : ∀ p ∈ d.labels x, Y < (∏ i, p i : ℕ) → 5 * Y ≤ roughLevel x) {k : ℕ}
    {a : LiftIndex K (padCount x)} (ha : a ∈ liftIndex x d)
    (hk : Nat.log 2 (∏ c, a.2.1 c) = k) (hne : liftTerm A₀ x d Y a ≠ 0) :
    liftStates a ∈ states x d Y (2 ^ k) ×ˢ states x d Y (2 ^ k) := by
  obtain ⟨⟨p, p'⟩, z, ⟨m, n⟩, r, s⟩ := a
  simp only [liftIndex, mem_filter, mem_product] at ha
  obtain ⟨⟨⟨hp, hp'⟩, hz, ⟨-, hnR⟩, -, hsR⟩, hU, hzinj, hzp⟩ := ha
  simp only at hk
  -- the factors of the term are nonzero
  have hηa : dyadicBump ((∏ i, p i : ℕ) / Y) ≠ 0 := fun h0 =>
    hne (by simp only [liftTerm]; rw [h0]; simp)
  have hηb : dyadicBump ((∏ i, p' i : ℕ) / Y) ≠ 0 := fun h0 =>
    hne (by simp only [liftTerm]; rw [h0]; simp)
  have hψ : plateau (liftDet p p' m n r s / Y) ≠ 0 := fun h0 =>
    hne (by simp only [liftTerm]; rw [h0]; simp)
  have hm : d.α m ≠ 0 := fun h0 => hne (by simp only [liftTerm]; rw [h0]; simp)
  have hr : d.α r ≠ 0 := fun h0 => hne (by simp only [liftTerm]; rw [h0]; simp)
  have hn : d.β n ≠ 0 := fun h0 => hne (by simp only [liftTerm]; rw [h0]; simp)
  have hs : d.β s ≠ 0 := fun h0 => hne (by simp only [liftTerm]; rw [h0]; simp)
  have hY0 : 0 < Y := by linarith
  have hab : ∀ {b : ℕ}, dyadicBump (b / Y) ≠ 0 → Y < b ∧ (b : ℝ) < 4 * Y := by
    intro b hb
    obtain ⟨h₁, h₂⟩ := lt_of_dyadicBump_ne_zero hb
    rw [one_lt_div hY0] at h₁
    rw [div_lt_iff₀ hY0] at h₂
    exact ⟨h₁, h₂⟩
  have hpY := hab hηa
  have hp'Y := hab hηb
  obtain ⟨hmH, -, hmr, -⟩ := hd.α_supp m hm
  obtain ⟨hnH, -, hnr, -⟩ := hd.β_supp n hn
  have hm0 : m ≠ 0 := by rintro rfl; rw [Nat.cast_zero] at hmH; linarith
  have hn0 : n ≠ 0 := by rintro rfl; rw [Nat.cast_zero] at hnH; linarith
  -- `t ≠ 0` and `|t| < 5Y ≤ W`
  have ht : liftDet p p' m n r s ≠ 0 :=
    liftDet_ne_zero hrough hp hp' hU (by exact_mod_cast hY.trans_lt hpY.1) hm0 hmr hn0 hnr r s
  have htW : |(liftDet p p' m n r s : ℝ)| < roughLevel x := by
    have := abs_lt_of_plateau_ne_zero hψ
    rw [abs_div, abs_of_pos hY0, div_lt_iff₀ hY0] at this
    linarith [hYW p hp hpY.1]
  have hD := pow_le_and_lt_of_log_eq
    (prod_pos fun c _ => (mem_filter.1 (mem_band_of_mem_padSet hz c)).2.pos) hk
  refine mem_product.2 ⟨mem_states_of hd hrough hHm hHn hY0 hz hzinj hD hp'
    (fun c => (hzp c).2) hp'Y hm hs hsR ht htW fun l _ hlm hls => ?_,
    mem_states_of hd hrough hHm hHn hY0 hz hzinj hD hp (fun c => (hzp c).1) hpY hr hn hnR ht
      htW fun l _ hlr hln => ?_⟩
  · unfold liftDet
    exact dvd_sub (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.2 hlm) _) _)
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.2 hls) _)
  · unfold liftDet
    exact dvd_sub (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.2 hln) _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.2 hlr) _) _)

/-- The change of variables is injective. -/
theorem liftStates_injOn {x : ℝ} {d : Data K} {a₁ a₂ : LiftIndex K (padCount x)}
    (ha₁ : a₁ ∈ liftIndex x d) (ha₂ : a₂ ∈ liftIndex x d) (h : liftStates a₁ = liftStates a₂) :
    a₁ = a₂ := by
  obtain ⟨⟨p₁, p'₁⟩, z₁, ⟨m₁, n₁⟩, r₁, s₁⟩ := a₁
  obtain ⟨⟨p₂, p'₂⟩, z₂, ⟨m₂, n₂⟩, r₂, s₂⟩ := a₂
  simp only [liftIndex, mem_filter, mem_product] at ha₁
  obtain ⟨⟨⟨hp, hp'⟩, hz, -⟩, -⟩ := ha₁
  simp only [liftStates, Prod.mk.injEq] at h
  obtain ⟨⟨⟨hm, rfl⟩, hl⟩, ⟨hr, rfl⟩, hl'⟩ := h
  obtain ⟨hz₁, hp'₁⟩ := padList_eq_iff.1 hl
  obtain ⟨-, hp₁⟩ := padList_eq_iff.1 hl'
  have hzz : z₁ = z₂ := funext fun c => by rw [hz₁, padList_castSucc]
  have hpp : p₁ = p₂ := funext fun i => by rw [hp₁, padList_last]
  have hpp' : p'₁ = p'₂ := funext fun i => by rw [hp'₁, padList_last]
  subst hzz hpp hpp'
  have hpos := listProd_pos fun i h => (mem_filter.1 (mem_band_padList hz hp' i h)).2
  have hpos' := listProd_pos fun i h => (mem_filter.1 (mem_band_padList hz hp i h)).2
  rw [Nat.eq_of_mul_eq_mul_left hpos hm, Nat.eq_of_mul_eq_mul_left hpos' hr]

open scoped Classical in
/-- The change of variables is onto the pairs of states with a nonzero term, and `α_m, α_r`
do not vanish at the preimage. -/
theorem exists_liftStates_eq {C CX alo ahi g x : ℝ} {d : Data K} (q A₀ : ℝ)
    (hd : Admissible C CX alo ahi g x d)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) (Y : ℝ) {k : ℕ}
    {w : ((ℕ × ℕ) × Lists K (padCount x)) × ((ℕ × ℕ) × Lists K (padCount x))}
    (hw : w ∈ states x d Y (2 ^ k) ×ˢ states x d Y (2 ^ k))
    (hne : stateTerm q A₀ x d Y k w ≠ 0) :
    ∃ a ∈ (liftIndex x d).filter (fun a => Nat.log 2 (∏ c, a.2.1 c) = k),
      d.α a.2.2.1.1 ≠ 0 ∧ d.α a.2.2.2.1 ≠ 0 ∧ liftStates a = w := by
  obtain ⟨⟨⟨P₁, P₂⟩, l⟩, ⟨⟨Q₁, Q₂⟩, l'⟩⟩ := w
  simp only [states, positions, mem_product, mem_filter] at hw
  obtain ⟨⟨⟨⟨⟨-, hP₂⟩, -⟩, hl⟩, hlP⟩, ⟨⟨⟨⟨-, hQ₂⟩, -⟩, hl'⟩, hlQ⟩⟩ := hw
  -- the factors of the term are nonzero, and the edge exists
  have hm : d.α (P₁ / listProd l) ≠ 0 := fun h0 => hne (by simp [stateTerm, h0])
  have hr : d.α (Q₁ / listProd l') ≠ 0 := fun h0 => hne (by simp [stateTerm, h0])
  have hcond : (∀ i (h : Fin (padCount x)), l' i h.castSucc = l i h.castSucc) ∧
      (∀ i i' h', l' i (Fin.last _) ≠ l i' h') ∧
      (2 : ℝ) ^ k ≤ (padProd l : ℝ) ∧ (padProd l : ℝ) < 2 * 2 ^ k ∧
      (padProd l : ℤ) ∣ det (P₁, P₂) (Q₁, Q₂) := by
    by_contra hc
    exact hne (by simp only [stateTerm, rowEntry]; rw [ite_eq_right hc]; simp)
  obtain ⟨hcopy, hban, hD₁, hD₂, -⟩ := hcond
  have hpad : ∏ c : Fin K × Fin (padCount x), l c.1 c.2.castSucc = padProd l := by
    rw [Fintype.prod_prod_type]
    rfl
  refine ⟨((fun i => l' i (Fin.last _), fun i => l i (Fin.last _)),
    (fun c => l c.1 c.2.castSucc, ((P₁ / listProd l, Q₂), (Q₁ / listProd l', P₂)))),
    mem_filter.2 ⟨mem_filter.2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩, hm, hr, ?_⟩
  · refine mem_product.2 ⟨mem_product.2 ⟨Fintype.mem_piFinset.2 fun i =>
      lists_slot_mem_band hl' i _, Fintype.mem_piFinset.2 fun i =>
      lists_slot_mem_band hl i _⟩, mem_product.2 ⟨Fintype.mem_piFinset.2 fun c =>
      lists_slot_mem_band hl c.1 _, mem_product.2 ⟨mem_product.2
        ⟨mem_mRange_of_α_ne_zero hd hm, hQ₂⟩, mem_product.2
          ⟨mem_mRange_of_α_ne_zero hd hr, hP₂⟩⟩⟩⟩
  · exact fun i i' => hban i i' _
  · -- the pads are distinct: across groups by disjointness, within by injectivity
    rintro ⟨i, h⟩ ⟨i', h'⟩ hh
    simp only at hh
    have hii : i = i' := by
      by_contra hne'
      exact disjoint_left.1 (hdisj i i' hne') (lists_slot_mem_band hl i _)
        (hh ▸ lists_slot_mem_band hl i' _)
    subst hii
    rw [Fin.castSucc_inj.1 (lists_group_injective hl i hh)]
  · exact fun c => ⟨fun h => hban c.1 c.1 _ h.symm,
      fun h => (Fin.castSucc_lt_last c.2).ne (lists_group_injective hl c.1 h)⟩
  · simp only
    rw [hpad]
    refine Nat.log_eq_of_pow_le_of_lt_pow (by exact_mod_cast hD₁) ?_
    rw [pow_succ, mul_comm]
    exact_mod_cast hD₂
  · have hpl : padList (fun c => l c.1 c.2.castSucc) (fun i => l i (Fin.last _)) = l :=
      padList_eq_iff.2 ⟨fun c => rfl, fun i => rfl⟩
    have hpl' : padList (fun c => l c.1 c.2.castSucc) (fun i => l' i (Fin.last _)) = l' :=
      padList_eq_iff.2 ⟨fun c => (hcopy c.1 c.2).symm, fun i => rfl⟩
    simp only [liftStates]
    rw [hpl, hpl', Nat.mul_div_cancel' (listProd_dvd_of_mem_lists hdisj hl hlP),
      Nat.mul_div_cancel' (listProd_dvd_of_mem_lists hdisj hl' hlQ)]

/-! ### The lift identity -/

/-- **The lift identity at one pad dyad.** The weighted coprime-pair error over the pads
with `D ∈ [2^k, 2^{k+1})` is `2^{-k} ⟨f, 𝒯 f⟩_{2^k}`. -/
theorem sum_liftTerm_dyad_eq {C CX alo ahi g x : ℝ} {d : Data K} (q A₀ : ℝ)
    (hd : Admissible C CX alo ahi g x d)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hrough : ∀ i, ∀ r ∈ band x (d.a i), ∀ m : ℕ, m ≠ 0 → IsRough x m → ¬ r ∣ m)
    (hHm : 0 < d.Hm) (hHn : 0 < d.Hn) (hV : 0 < d.bandMass x) {Y : ℝ} (hY : 1 ≤ Y)
    (hYW : ∀ p ∈ d.labels x, Y < (∏ i, p i : ℕ) → 5 * Y ≤ roughLevel x) (k : ℕ) :
    ∑ a ∈ (liftIndex x d).filter (fun a => Nat.log 2 (∏ c, a.2.1 c) = k),
        liftTerm A₀ x d Y a = ((2 : ℂ) ^ k)⁻¹ * rowPairing q A₀ x d Y (2 ^ k) := by
  rw [inv_mul_rowPairing_eq]
  refine sum_bij_ne_zero (fun a _ _ => liftStates a) (fun a ha hne => ?_)
    (fun a₁ ha₁ _ a₂ ha₂ _ h => liftStates_injOn (mem_filter.1 ha₁).1 (mem_filter.1 ha₂).1 h)
    (fun w hw hne => ?_) (fun a ha hne => ?_)
  · exact liftStates_mem A₀ hd hrough hHm hHn hY hYW (mem_filter.1 ha).1 (mem_filter.1 ha).2 hne
  · obtain ⟨a, ha, hm, hr, rfl⟩ := exists_liftStates_eq q A₀ hd hdisj Y hw hne
    refine ⟨a, ha, ?_, rfl⟩
    rw [liftTerm_eq_stateTerm q A₀ hd hdisj hrough hHm hV Y (mem_filter.1 ha).1
      (mem_filter.1 ha).2 hm hr]
    exact hne
  · have hm : d.α a.2.2.1.1 ≠ 0 := fun h0 => hne (by simp only [liftTerm]; rw [h0]; simp)
    have hr : d.α a.2.2.2.1 ≠ 0 := fun h0 => hne (by simp only [liftTerm]; rw [h0]; simp)
    exact liftTerm_eq_stateTerm q A₀ hd hdisj hrough hHm hV Y (mem_filter.1 ha).1
      (mem_filter.1 ha).2 hm hr

/-- **The lift identity.** When every pad product is below `2^{N + 1}`, the weighted
coprime-pair error is `∑_{k ≤ N} 2^{-k} ⟨f, 𝒯 f⟩_{2^k}`: each pad product lies in exactly one
dyad. -/
theorem sum_liftTerm_eq {C CX alo ahi g x : ℝ} {d : Data K} (q A₀ : ℝ)
    (hd : Admissible C CX alo ahi g x d)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hrough : ∀ i, ∀ r ∈ band x (d.a i), ∀ m : ℕ, m ≠ 0 → IsRough x m → ¬ r ∣ m)
    (hHm : 0 < d.Hm) (hHn : 0 < d.Hn) (hV : 0 < d.bandMass x) {Y : ℝ} (hY : 1 ≤ Y)
    (hYW : ∀ p ∈ d.labels x, Y < (∏ i, p i : ℕ) → 5 * Y ≤ roughLevel x) {N : ℕ}
    (hN : ∀ z ∈ padSet x d (padCount x), ∏ c, z c < 2 ^ (N + 1)) :
    ∑ a ∈ liftIndex x d, liftTerm A₀ x d Y a =
      ∑ k ∈ range (N + 1), ((2 : ℂ) ^ k)⁻¹ * rowPairing q A₀ x d Y (2 ^ k) := by
  have hmaps : ∀ a ∈ liftIndex x d, Nat.log 2 (∏ c, a.2.1 c) ∈ range (N + 1) := by
    intro a ha
    simp only [liftIndex, mem_filter, mem_product] at ha
    have hz := ha.1.2.1
    have hD : ∏ c, a.2.1 c ≠ 0 :=
      (prod_pos fun c _ => (mem_filter.1 (mem_band_of_mem_padSet hz c)).2.pos).ne'
    exact mem_range.2 ((Nat.log_lt_iff_lt_pow (by norm_num) hD).2 (hN _ hz))
  rw [← sum_fiberwise_of_maps_to hmaps]
  exact sum_congr rfl fun k _ =>
    sum_liftTerm_dyad_eq q A₀ hd hdisj hrough hHm hHn hV hY hYW k

open scoped Classical in
/-- The coprime-pair error at fixed label tuples, with the plateau:
`∑_{m,n,r,s} ψ(t/Y) α_m ᾱ_r β_n β̄_s ([t = b - a] - ∫_𝔐 e(θ(t - b + a)))`. -/
noncomputable def liftError (A₀ x : ℝ) (d : Data K) (Y : ℝ) (p p' : Fin K → ℕ) : ℂ :=
  ∑ m ∈ d.mRange, ∑ n ∈ d.nRange, ∑ r ∈ d.mRange, ∑ s ∈ d.nRange,
    ((plateau (liftDet p p' m n r s / Y) : ℝ) : ℂ) *
      (d.α m * star (d.α r) * d.β n * star (d.β s) *
        ((if liftDet p p' m n r s = (∏ i, p' i : ℕ) - (∏ i, p i : ℕ) then 1 else 0) -
          arcIntegral A₀ x Y (liftDet p p' m n r s - (∏ i, p' i : ℕ) + (∏ i, p i : ℕ))))

open scoped Classical in
/-- The weighted coprime-pair error as an iterated sum: over unshared label tuples, and
over good pads with weight `∏_c μ(z_c)`. -/
theorem sum_liftTerm_eq_sum_labels (A₀ x : ℝ) (d : Data K) (Y : ℝ) :
    ∑ a ∈ liftIndex x d, liftTerm A₀ x d Y a =
      ((d.bandMass x)⁻¹ ^ 2 : ℝ) * ∑ p ∈ d.labels x, ∑ p' ∈ d.labels x,
        if Unshared p p' then
          (dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) : ℝ) *
            ∑ z ∈ padSet x d (padCount x),
              if GoodPads p p' z then (padWeight x d z : ℂ) * liftError A₀ x d Y p p' else 0
        else 0 := by
  rw [liftIndex, sum_filter]
  simp only [sum_product]
  rw [mul_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun p' _ => ?_
  by_cases hU : Unshared p p'
  · simp only [hU, true_and, ite_true, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    by_cases hG : GoodPads p p' z
    · simp only [hG, ite_true, liftError, mul_sum]
      refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => sum_congr rfl fun r _ =>
        sum_congr rfl fun s _ => ?_
      simp only [liftTerm]
      push_cast
      ring
    · simp [hG]
  · simp [hU]

end Erdos408.OneSided
