import Erdos408.OneSided.Bands
import Erdos408.OneSided.Lift

/-!
# Pads, lists and states

The bookkeeping for the change of variables of PD Lemma 4.1
(`blueprint/one_sided_type_ii.md` §4).

* Pads are a tuple `z` indexed by `Fin K × Fin J`, with `z (i, h)` in band `i`. Appending
  a label tuple `p` as the last slot gives the lists `padList z p`, with list product
  `D ∏ p_i`, where `D = ∏ z` is the pad product.
* The labels of a list divide `P₁` exactly when their product does, and for
  `P₁ = (list product) m` with `m` rough the band count is `KM`, so the damping is one.
* A position `(N m, s)` whose band part `N` divides no rough integer is primitive as soon
  as every common prime of `m` and `s` divides a nonzero `t` with `|t| < W`.
* `rowEntry` is the entry of `𝒯` as a function of the underlying positions and lists.
-/

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

/-! ### Pads and lists -/

/-- The pad tuples: a prime of band `i` at each slot `(i, h)`. -/
noncomputable def padSet (x : ℝ) (d : Data K) (J : ℕ) : Finset (Fin K × Fin J → ℕ) :=
  Fintype.piFinset fun c => band x (d.a c.1)

/-- The lists with pads `z` and last slots `p`. -/
def padList {J : ℕ} (z : Fin K × Fin J → ℕ) (p : Fin K → ℕ) : Lists K J :=
  fun i => Fin.snoc (fun h => z (i, h)) (p i)

@[simp]
theorem padList_castSucc {J : ℕ} (z : Fin K × Fin J → ℕ) (p : Fin K → ℕ) (i : Fin K)
    (h : Fin J) : padList z p i h.castSucc = z (i, h) :=
  Fin.snoc_castSucc (α := fun _ => ℕ) _ _ _

@[simp]
theorem padList_last {J : ℕ} (z : Fin K × Fin J → ℕ) (p : Fin K → ℕ) (i : Fin K) :
    padList z p i (Fin.last J) = p i :=
  Fin.snoc_last (α := fun _ => ℕ) _ _

/-- `padList z p = l` exactly when `z` and `p` are the slots of `l`. -/
theorem padList_eq_iff {J : ℕ} {z : Fin K × Fin J → ℕ} {p : Fin K → ℕ} {l : Lists K J} :
    padList z p = l ↔ (∀ c, z c = l c.1 c.2.castSucc) ∧ ∀ i, p i = l i (Fin.last J) := by
  constructor
  · rintro rfl
    exact ⟨fun c => (padList_castSucc z p c.1 c.2).symm, fun i => (padList_last z p i).symm⟩
  · rintro ⟨hz, hp⟩
    funext i h
    induction h using Fin.lastCases with
    | last => rw [padList_last, hp]
    | cast h => rw [padList_castSucc, hz]

/-- The pad product of `padList z p` is `∏ z`. -/
theorem padProd_padList {J : ℕ} (z : Fin K × Fin J → ℕ) (p : Fin K → ℕ) :
    padProd (padList z p) = ∏ c, z c := by
  simp [padProd, Fintype.prod_prod_type]

/-- The last product of `padList z p` is `∏ p`. -/
theorem lastProd_padList {J : ℕ} (z : Fin K × Fin J → ℕ) (p : Fin K → ℕ) :
    lastProd (padList z p) = ∏ i, p i := by
  simp [lastProd]

/-- The list product of `padList z p` is `(∏ z) ∏ p`. -/
theorem listProd_padList {J : ℕ} (z : Fin K × Fin J → ℕ) (p : Fin K → ℕ) :
    listProd (padList z p) = (∏ c, z c) * ∏ i, p i := by
  simp [listProd, Fin.prod_univ_castSucc, prod_mul_distrib, Fintype.prod_prod_type]

/-- A list product is positive when every label is prime. -/
theorem listProd_pos {J : ℕ} {l : Lists K J} (hl : ∀ i h, (l i h).Prime) : 0 < listProd l :=
  prod_pos fun i _ => prod_pos fun h _ => (hl i h).pos

/-- The labels of a list in `lists` are primes of their bands. -/
theorem lists_slot_mem_band {x : ℝ} {d : Data K} {J : ℕ} {l : Lists K J}
    (hl : l ∈ lists x d J) (i : Fin K) (h : Fin (J + 1)) : l i h ∈ band x (d.a i) := by
  unfold lists at hl
  rw [mem_filter, Fintype.mem_piFinset] at hl
  exact Fintype.mem_piFinset.1 (hl.1 i) h

/-- The lists in `lists` are injective in each group. -/
theorem lists_group_injective {x : ℝ} {d : Data K} {J : ℕ} {l : Lists K J}
    (hl : l ∈ lists x d J) (i : Fin K) : Function.Injective (l i) := by
  unfold lists at hl
  exact (mem_filter.1 hl).2 i

/-- A prime dividing a list product is one of the labels. -/
theorem exists_eq_of_prime_dvd_listProd {J : ℕ} {l : Lists K J} (hl : ∀ i h, (l i h).Prime)
    {r : ℕ} (hr : r.Prime) (hdvd : r ∣ listProd l) : ∃ i h, r = l i h := by
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hr.prime _).1 hdvd
  obtain ⟨h, -, hh⟩ := (Prime.dvd_finsetProd_iff hr.prime _).1 hi
  exact ⟨i, h, (Nat.prime_dvd_prime_iff_eq hr (hl i h)).1 hh⟩

/-- With disjoint bands, the labels of a list in `lists` are distinct primes, so they all
divide `N` exactly when their product does. -/
theorem listProd_dvd_of_mem_lists {x : ℝ} {d : Data K}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) {J : ℕ}
    {l : Lists K J} (hl : l ∈ lists x d J) {N : ℕ} (hN : ∀ i h, l i h ∣ N) :
    listProd l ∣ N := by
  have hprime : ∀ i h, (l i h).Prime := fun i h =>
    (mem_filter.1 (lists_slot_mem_band hl i h)).2
  -- the labels are injective on `Fin K × Fin (J + 1)`
  have hinj : Function.Injective fun c : Fin K × Fin (J + 1) => l c.1 c.2 := by
    rintro ⟨i, h⟩ ⟨i', h'⟩ heq
    simp only at heq
    have hii : i = i' := by
      by_contra hne
      exact disjoint_left.1 (hdisj i i' hne) (lists_slot_mem_band hl i h)
        (heq ▸ lists_slot_mem_band hl i' h')
    subst hii
    rw [lists_group_injective hl i heq]
  have himg : listProd l = ∏ r ∈ univ.image (fun c : Fin K × Fin (J + 1) => l c.1 c.2), r := by
    rw [prod_image fun c _ c' _ h => hinj h, listProd, ← Fintype.prod_prod_type']
  rw [himg]
  refine Finset.prod_primes_dvd N (fun r hr => ?_) fun r hr => ?_
  · obtain ⟨c, -, rfl⟩ := mem_image.1 hr
    exact (hprime c.1 c.2).prime
  · obtain ⟨c, -, rfl⟩ := mem_image.1 hr
    exact hN c.1 c.2

/-- With disjoint bands whose primes divide no rough integer, the band count of
`(list product) m` with `m` rough is `K (J + 1)`: in band `i` the primes dividing it are the
labels of group `i`. -/
theorem bandCount_listProd_mul {x : ℝ} {d : Data K}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hrough : ∀ i, ∀ r ∈ band x (d.a i), ∀ m : ℕ, m ≠ 0 → IsRough x m → ¬ r ∣ m) {J : ℕ}
    {l : Lists K J} (hl : l ∈ lists x d J) {m : ℕ} (hm : m ≠ 0) (hmr : IsRough x m) :
    bandCount x d (listProd l * m) = K * (J + 1) := by
  have hprime : ∀ i h, (l i h).Prime := fun i h =>
    (mem_filter.1 (lists_slot_mem_band hl i h)).2
  have hband : ∀ i, primeCount (band x (d.a i)) (listProd l * m) = J + 1 := by
    intro i
    unfold primeCount
    have hset : (band x (d.a i)).filter (· ∣ listProd l * m) = univ.image (l i) := by
      ext r
      simp only [mem_filter, mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨hr, hdvd⟩
        have hrp : r.Prime := (mem_filter.1 hr).2
        rcases (Nat.Prime.dvd_mul hrp).1 hdvd with hdl | hdm
        · obtain ⟨i', h, rfl⟩ := exists_eq_of_prime_dvd_listProd hprime hrp hdl
          by_cases hii : i = i'
          · subst hii
            exact ⟨h, rfl⟩
          · exact absurd (lists_slot_mem_band hl i' h) (disjoint_left.1 (hdisj i i' hii) hr)
        · exact absurd hdm (hrough i r hr m hm hmr)
      · rintro ⟨h, rfl⟩
        refine ⟨lists_slot_mem_band hl i h, Dvd.dvd.mul_right ?_ _⟩
        exact (dvd_prod_of_mem _ (mem_univ h)).trans (dvd_prod_of_mem _ (mem_univ i))
    rw [hset, card_image_of_injective _ (lists_group_injective hl i), card_univ,
      Fintype.card_fin]
  simp only [bandCount, hband, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-! ### Automatic primitivity -/

/-- `(N m, s)` is primitive when the band part `N` has no prime factor dividing `s`, `s` is
rough, and every common prime of `m` and `s` divides a nonzero `t` with `|t| < W`
(PD §3.2, after (3.18)). -/
theorem coprime_mul_of_isRough {x : ℝ} {N m s : ℕ} (hN : ∀ r, r.Prime → r ∣ N → ¬ r ∣ s)
    (hs : s ≠ 0) (hsr : IsRough x s) {t : ℤ} (ht : t ≠ 0) (htW : |(t : ℝ)| < roughLevel x)
    (hms : ∀ r : ℕ, r.Prime → r ∣ m → r ∣ s → (r : ℤ) ∣ t) : Nat.Coprime (N * m) s := by
  by_contra hcop
  obtain ⟨r, hr, hrNm, hrs⟩ := Nat.Prime.not_coprime_iff_dvd.1 hcop
  rcases (Nat.Prime.dvd_mul hr).1 hrNm with hrN | hrm
  · exact hN r hr hrN hrs
  -- a common prime of `m` and `s` exceeds `W > |t|` and divides `t`
  have hW : roughLevel x < r := hsr r (Nat.mem_primeFactors.2 ⟨hr, hrs, hs⟩)
  have hle : (r : ℤ) ≤ |t| := Int.le_of_dvd (abs_pos.2 ht) ((dvd_abs _ _).2 (hms r hr hrm hrs))
  have hle' : (r : ℝ) ≤ |(t : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hle
  linarith

/-! ### Entries of the row operation -/

open scoped Classical in
/-- The entry of `𝒯` from `(P, p)` to `(Q, p')`, as a function of the underlying positions
and lists. -/
noncomputable def rowEntry (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ)
    (u u' : (ℕ × ℕ) × Lists K (padCount x)) : ℂ :=
  if (∀ i (h : Fin (padCount x)), u'.2 i h.castSucc = u.2 i h.castSucc) ∧
      (∀ i i' h', u'.2 i (Fin.last _) ≠ u.2 i' h') ∧
      d₀ ≤ (padProd u.2 : ℝ) ∧ (padProd u.2 : ℝ) < 2 * d₀ ∧
      (padProd u.2 : ℤ) ∣ det u.1 u'.1 then
    (((d.bandMass x)⁻¹ * (d₀ / padProd u.2) * dyadicBump (lastProd u.2 / Y) *
        dyadicBump (lastProd u'.2 / Y) * plateau ((det u.1 u'.1 / padProd u.2 : ℤ) / Y) *
        q ^ (((bandCount x d u.1.1 : ℝ) - K * (padCount x + 1)) / 2 +
          ((bandCount x d u'.1.1 : ℝ) - K * (padCount x + 1)) / 2) : ℝ) : ℂ) *
      ((if det u.1 u'.1 / padProd u.2 = (lastProd u.2 : ℤ) - lastProd u'.2 then 1
          else 0) -
        arcIntegral A₀ x Y
          (det u.1 u'.1 / padProd u.2 - lastProd u.2 + lastProd u'.2))
  else 0

/-- `⟨f, 𝒯 f⟩` as a double sum over the underlying states. -/
theorem rowPairing_eq (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) :
    rowPairing q A₀ x d Y d₀ = (stateMass x d : ℂ) *
      ∑ u ∈ states x d Y d₀, ∑ u' ∈ states x d Y d₀,
        star (star (d.α (u.1.1 / listProd u.2)) * d.β u.1.2) *
          (rowEntry q A₀ x d Y d₀ u u' * (star (d.α (u'.1.1 / listProd u'.2)) * d.β u'.1.2)) := by
  unfold rowPairing stateInner
  congr 1
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [← sum_coe_sort (states x d Y d₀)]
  refine sum_congr rfl fun s _ => ?_
  rw [← sum_coe_sort (states x d Y d₀)]
  rfl

end Erdos408.OneSided
