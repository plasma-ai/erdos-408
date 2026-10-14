import Erdos408.OneSided.Bands
import Erdos408.OneSided.Moment.PathExpansion.Hermitian

/-!
# The anchor congruence

The arithmetic of PD §4 "Dirty raw edges" (`mem:anchor-congruence`), for M7
(`eventually_edgeRaw_normLe` in `Moment/Edge.lean`). Fix a source position `z` with lists `p`
and a promoted prime `p_*` with an anchor line `ℓ_*`. A raw dirty edge from `z` with omission
product `D`, other promoted primes `Z` and fresh primes `T` has a target `z'` with
`det(z, z') = P - D p_* Z T`, where `P` is the full source product, and `[z']_{p_*} = ℓ_*`.

* `dvd_det_of_lineOf_eq`: two positions with the same line at `p` have determinant divisible by
  `p`.
* `circleDist_le_of_anchor`: if `det(z, z_k) = P - p n_k` for two targets `z_1, z_2` of the box
  with the same line at `p ∤ P`, then `‖(n_1 - n_2) r_z‖ ≤ 15/p` with `r_z = τ(w_z)/τ(z)`. This
  is the pairwise form of `mem:anchor-congruence`.
* `eq_of_prod_eq_of_band`, `omitProd_injective`, `eq_of_mul_eq_of_coprime`: prime factorization
  separates the omission product `D` (source labels) from `Z` (not source labels, by the ban),
  `D` determines the omission tuple, and `Z` determines the other promoted primes.
* `anchor_unique`: under the phase separation of the second good-state test, the omission
  tuple and the other promoted primes are unique.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

/-! ### Lines and determinants -/

/-- Two positions with the same projective line at a prime `p` have determinant divisible by
`p`. -/
theorem dvd_det_of_lineOf_eq {p : ℕ} (hp : p.Prime) {z z' : ℤ × ℤ}
    (h : lineOf p z = lineOf p z') : (p : ℤ) ∣ z.1 * z'.2 - z.2 * z'.1 := by
  have := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  unfold lineOf at h
  by_cases h₁ : (z.1 : ZMod p) = 0 <;> by_cases h₂ : (z'.1 : ZMod p) = 0
  · rw [h₁, h₂]
    ring
  · simp only [h₁, h₂, ↓reduceIte] at h
    exact absurd h (ZMod.val_lt _).ne'
  · simp only [h₁, h₂, ↓reduceIte] at h
    exact absurd h (ZMod.val_lt _).ne
  · simp only [h₁, h₂, ↓reduceIte] at h
    have h' := ZMod.val_injective p h
    field_simp at h'
    linear_combination -h'

/-- **The anchor separation** (PD `mem:anchor-congruence`, pairwise): let `z, z_1, z_2` lie in
the root box, with `z` primitive. If `det(z, z_k) = P - p n_k` for a prime `p ∤ P`, and
`p ∣ det(z_1, z_2)` (the two targets have the same line at `p`), then
`‖(n_1 - n_2) r_z‖ ≤ 15/p` with `r_z = τ(w_z)/τ(z)`. In the basis `(z, w_z)` the targets are
`z_k = α_k z + det(z, z_k) w_z`, the line condition gives `p ∣ α_1 - α_2`, and
`τ(z_1)/τ(z), τ(z_2)/τ(z) ∈ [1/16, 16]`. -/
theorem circleDist_le_of_anchor {U V u v r : ℝ} (hU : 0 < U) (hu : 0 < u) {z z₁ z₂ : ℤ × ℤ}
    (hz : z ∈ rootPositions U V u v r) (hz₁ : z₁ ∈ rootPositions U V u v r)
    (hz₂ : z₂ ∈ rootPositions U V u v r) {p : ℕ} (hp : p.Prime) {P n₁ n₂ : ℤ}
    (hP : ¬ (p : ℤ) ∣ P) (h₁ : z.1 * z₁.2 - z.2 * z₁.1 = P - p * n₁)
    (h₂ : z.1 * z₂.2 - z.2 * z₂.1 = P - p * n₂)
    (hdvd : (p : ℤ) ∣ z₁.1 * z₂.2 - z₁.2 * z₂.1) :
    circleDist (((n₁ - n₂ : ℤ) : ℝ) * (tau r (complement z) / tau r z)) ≤ 15 / p := by
  unfold rootPositions at hz hz₁ hz₂
  simp only [mem_filter] at hz hz₁ hz₂
  obtain ⟨-, hgcd, hzU, hzU', -⟩ := hz
  obtain ⟨-, -, hz₁U, hz₁U', -⟩ := hz₁
  obtain ⟨-, -, hz₂U, hz₂U', -⟩ := hz₂
  set w := complement z with hwdef
  -- `det(z, w_z) = gcd(z₁, z₂) = 1`
  have hw : z.1 * w.2 - z.2 * w.1 = 1 := by
    have := Int.gcd_eq_gcd_ab z.1 z.2
    rw [hgcd] at this
    simp only [hwdef, complement]
    linear_combination -this
  -- the coordinates `α_k = det(z_k, w_z)` along `z`
  set α₁ := z₁.1 * w.2 - z₁.2 * w.1 with hα₁
  set α₂ := z₂.1 * w.2 - z₂.2 * w.1 with hα₂
  have hpl : z₁.1 * z₂.2 - z₁.2 * z₂.1 =
      α₁ * (z.1 * z₂.2 - z.2 * z₂.1) - (z.1 * z₁.2 - z.2 * z₁.1) * α₂ := by
    linear_combination (-(z₁.1 * z₂.2 - z₁.2 * z₂.1)) * hw
  -- the line condition: `p ∣ P (α₁ - α₂)`, so `p ∣ α₁ - α₂`
  have hpα : (p : ℤ) ∣ α₁ - α₂ := by
    have hPα : (p : ℤ) ∣ P * (α₁ - α₂) := by
      have : P * (α₁ - α₂) = (z₁.1 * z₂.2 - z₁.2 * z₂.1) + p * (α₁ * n₂ - n₁ * α₂) := by
        rw [hpl, h₁, h₂]
        ring
      rw [this]
      exact dvd_add hdvd (dvd_mul_right _ _)
    exact ((Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hPα).resolve_left hP
  obtain ⟨m, hm⟩ := hpα
  -- `τ(z_k) = α_k τ(z) + det(z, z_k) τ(w)`
  have hτ : ∀ y : ℤ × ℤ, tau r y = ((y.1 * w.2 - y.2 * w.1 : ℤ) : ℝ) * tau r z +
      ((z.1 * y.2 - z.2 * y.1 : ℤ) : ℝ) * tau r w := by
    intro y
    have hw' : (z.1 : ℝ) * w.2 - z.2 * w.1 = 1 := by exact_mod_cast hw
    unfold tau
    push_cast
    linear_combination (-(y.1 : ℝ) - r * y.2) * hw'
  have hτ₁ := hτ z₁
  have hτ₂ := hτ z₂
  rw [h₁] at hτ₁
  rw [h₂] at hτ₂
  have hm' : (α₁ : ℝ) - α₂ = p * m := by exact_mod_cast hm
  have hτz : 0 < tau r z := by
    by_contra h
    push Not at h
    nlinarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  -- `(n₁ - n₂) r_z = m - (τ(z₁) - τ(z₂)) / (p τ(z))`
  have hkey : ((n₁ - n₂ : ℤ) : ℝ) * (tau r w / tau r z) - m =
      -(tau r z₁ - tau r z₂) / (p * tau r z) := by
    have hd : tau r z₁ - tau r z₂ =
        p * (m * tau r z - ((n₁ - n₂ : ℤ) : ℝ) * tau r w) := by
      rw [hτ₁, hτ₂]
      change (α₁ : ℝ) * tau r z + _ - ((α₂ : ℝ) * tau r z + _) = _
      push_cast
      linear_combination tau r z * hm'
    rw [hd]
    field_simp
    ring
  -- `|τ(z₁) - τ(z₂)| ≤ 15 τ(z)`
  have hdiff : |tau r z₁ - tau r z₂| ≤ 15 * tau r z := by
    rw [abs_le]
    constructor <;> nlinarith
  calc circleDist (((n₁ - n₂ : ℤ) : ℝ) * (tau r w / tau r z))
      ≤ |((n₁ - n₂ : ℤ) : ℝ) * (tau r w / tau r z) - m| := round_le _ m
    _ = |tau r z₁ - tau r z₂| / (p * tau r z) := by
        rw [hkey, neg_div, abs_neg, abs_div, abs_of_pos (mul_pos hp0 hτz)]
    _ ≤ 15 * tau r z / (p * tau r z) := by gcongr
    _ = 15 / p := by field_simp

/-! ### Prime factorization -/

/-- **Products of band primes**: if `f i, g i` are both `1` or both primes of the band of
group `i`, with disjoint bands, then `∏ f = ∏ g` forces `f = g`. -/
theorem eq_of_prod_eq_of_band {x : ℝ} {d : Data K}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) {f g : Fin K → ℕ}
    (hfg : ∀ i, (f i = 1 ∧ g i = 1) ∨ (f i ∈ band x (d.a i) ∧ g i ∈ band x (d.a i)))
    (h : ∏ i, f i = ∏ i, g i) : f = g := by
  funext i
  rcases hfg i with ⟨hf, hg⟩ | ⟨hf, -⟩
  · rw [hf, hg]
  · have hfp := TypeII.band_prime hf
    have hdvd : f i ∣ ∏ j, g j := h ▸ dvd_prod_of_mem f (mem_univ i)
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hfp.prime g).1 hdvd
    rcases hfg j with ⟨-, hg1⟩ | ⟨-, hgj⟩
    · rw [hg1] at hj
      exact absurd (Nat.eq_one_of_dvd_one hj) hfp.one_lt.ne'
    · have hfj := (Nat.prime_dvd_prime_iff_eq hfp (TypeII.band_prime hgj)).1 hj
      have hij : i = j := by
        by_contra hij
        exact disjoint_left.1 (hdisj i j hij) hf (hfj ▸ hgj)
      rw [hfj, hij]

/-- The omission product times the omitted labels is the full product. -/
theorem omitProd_mul_prod {J : ℕ} (p : Lists K J) (o : Fin K → Fin (J + 1)) :
    omitProd p o * ∏ i, p i (o i) = listProd p := by
  unfold omitProd listProd
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun i _ => prod_erase_mul _ _ (mem_univ _)

/-- The full product of valid lists is positive. -/
theorem listProd_pos_of_mem_lists {x : ℝ} {d : Data K} {J : ℕ} {p : Lists K J}
    (hp : p ∈ lists x d J) :
    0 < listProd p :=
  prod_pos fun i _ => prod_pos fun h _ =>
    (TypeII.band_prime (mem_band_of_mem_lists hp i h)).pos

/-- With disjoint bands, the omission product of valid lists determines the omission tuple. -/
theorem omitProd_injective {x : ℝ} {d : Data K} {J : ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) {p : Lists K J}
    (hp : p ∈ lists x d J) {o o' : Fin K → Fin (J + 1)} (h : omitProd p o = omitProd p o') :
    o = o' := by
  have h₁ := omitProd_mul_prod p o
  have h₂ := omitProd_mul_prod p o'
  have hD : 0 < omitProd p o := by
    rcases Nat.eq_zero_or_pos (omitProd p o) with h0 | h0
    · rw [h0, zero_mul] at h₁
      exact absurd h₁.symm (listProd_pos_of_mem_lists hp).ne'
    · exact h0
  have hb' : ∏ i, p i (o i) = ∏ i, p i (o' i) := by
    rw [h] at h₁
    exact Nat.eq_of_mul_eq_mul_left (h ▸ hD) (h₁.trans h₂.symm)
  have := eq_of_prod_eq_of_band hdisj
    (fun i => Or.inr ⟨mem_band_of_mem_lists hp i _, mem_band_of_mem_lists hp i _⟩) hb'
  funext i
  exact injective_of_mem_lists hp i (congrFun this i)

/-- **Separating `D` and `Z`**: if `D₁ Z₁ = D₂ Z₂` with `D_k ∣ P` and `Z_k` coprime to `P`, then
`D₁ = D₂` and `Z₁ = Z₂`. -/
theorem eq_of_mul_eq_of_coprime {D₁ D₂ Z₁ Z₂ P : ℕ} (h : D₁ * Z₁ = D₂ * Z₂) (hD₁ : D₁ ∣ P)
    (hD₂ : D₂ ∣ P) (hZ₁ : Nat.Coprime Z₁ P) (hZ₂ : Nat.Coprime Z₂ P) (hpos : 0 < D₁) :
    D₁ = D₂ ∧ Z₁ = Z₂ := by
  have h₁ : D₁ ∣ D₂ := (hZ₂.coprime_dvd_right hD₁).symm.dvd_of_dvd_mul_right (h ▸ dvd_mul_right _ _)
  have h₂ : D₂ ∣ D₁ := (hZ₁.coprime_dvd_right hD₂).symm.dvd_of_dvd_mul_right (h ▸ dvd_mul_right _ _)
  have hD := Nat.dvd_antisymm h₁ h₂
  refine ⟨hD, ?_⟩
  rw [hD] at h
  exact Nat.eq_of_mul_eq_mul_left (hD ▸ hpos) h

/-! ### Uniqueness of the omission tuple -/

/-- **The anchor uniqueness** (PD §4, dirty raw edges): fix a source position `z` in the box
with lists `p`, a nonempty set `I` of promoted groups with `i_* = max I`, a fresh draw `T`
passing the phase separation of the second good-state test, and a promoted prime `p_*` of the
band `i_*` banned from the source lists. Then two raw dirty edges with omission tuples `o_k`,
other promoted primes `Z_k` (banned from the source lists) and targets `z_k` with the same line
at `p_*` have `o₁ = o₂` and `Z₁ = Z₂`. -/
theorem anchor_unique {x d₀ U V u v r : ℝ} {d : Data K} {J : ℕ} (hU : 0 < U) (hu : 0 < u)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {p : Lists K J} (hp : p ∈ lists x d J) {z : ℤ × ℤ} (hz : z ∈ rootPositions U V u v r)
    {I : Finset (Fin K)} (hI : I.Nonempty) {T : Fin K → ℕ}
    (hsep : Separated x d d₀ I (I.max' hI) (tau r (complement z) / tau r z) p T)
    {ps : ℕ} (hps : ps ∈ band x (d.a (I.max' hI))) (hpsban : ∀ i h, ps ≠ p i h)
    {o₁ o₂ : Fin K → Fin (J + 1)} {Z₁ Z₂ : Fin K → ℕ}
    (hZ₁ : Z₁ ∈ selections x d I (I.max' hI)) (hZ₂ : Z₂ ∈ selections x d I (I.max' hI))
    (hZban₁ : ∀ j i h, Z₁ j ≠ p i h) (hZban₂ : ∀ j i h, Z₂ j ≠ p i h)
    (hD₁ : d₀ ≤ (omitProd p o₁ : ℝ)) (hD₁' : (omitProd p o₁ : ℝ) < 2 * d₀)
    (hD₂ : d₀ ≤ (omitProd p o₂ : ℝ)) (hD₂' : (omitProd p o₂ : ℝ) < 2 * d₀)
    {z₁ z₂ : ℤ × ℤ} (hz₁ : z₁ ∈ rootPositions U V u v r) (hz₂ : z₂ ∈ rootPositions U V u v r)
    (hline : lineOf ps z₁ = lineOf ps z₂)
    (hdet₁ : z.1 * z₁.2 - z.2 * z₁.1 =
      (omitProd p o₁ : ℤ) * ((∏ i, p i (o₁ i) : ℕ) - (ps * (∏ j, Z₁ j) * ∏ j, T j : ℕ)))
    (hdet₂ : z.1 * z₂.2 - z.2 * z₂.1 =
      (omitProd p o₂ : ℤ) * ((∏ i, p i (o₂ i) : ℕ) - (ps * (∏ j, Z₂ j) * ∏ j, T j : ℕ))) :
    o₁ = o₂ ∧ Z₁ = Z₂ := by
  have hprime : ∀ i h, (p i h).Prime := fun i h =>
    TypeII.band_prime (mem_band_of_mem_lists hp i h)
  have hpsp := TypeII.band_prime hps
  set P := listProd p with hPdef
  -- `p_* ∤ P`, as `p_*` is banned from the source lists
  have hP : ¬ (ps : ℤ) ∣ (P : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    intro hdvd
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpsp.prime _).1 hdvd
    obtain ⟨h, -, hh⟩ := (Prime.dvd_finsetProd_iff hpsp.prime _).1 hi
    exact hpsban i h ((Nat.prime_dvd_prime_iff_eq hpsp (hprime i h)).1 hh)
  -- `det(z, z_k) = P - p_* (D_k Z_k T)`
  have hform : ∀ (o : Fin K → Fin (J + 1)) (Z : Fin K → ℕ) (y : ℤ × ℤ),
      z.1 * y.2 - z.2 * y.1 =
        (omitProd p o : ℤ) * ((∏ i, p i (o i) : ℕ) - (ps * (∏ j, Z j) * ∏ j, T j : ℕ)) →
      z.1 * y.2 - z.2 * y.1 = P - ps * ((omitProd p o * (∏ j, Z j) * ∏ j, T j : ℕ) : ℤ) := by
    intro o Z y hy
    rw [hy, hPdef, ← omitProd_mul_prod p o]
    push_cast
    ring
  have hanc := circleDist_le_of_anchor hU hu hz hz₁ hz₂ hpsp hP (hform o₁ Z₁ z₁ hdet₁)
    (hform o₂ Z₂ z₂ hdet₂) (dvd_det_of_lineOf_eq hpsp hline)
  -- `15/p_* < 100 e^{-L^{a_{i_*}}}`
  have hsmall : 15 / (ps : ℝ) < 100 * Real.exp (-Real.log x ^ d.a (I.max' hI)) := by
    have hle := exp_le_of_mem_band hps
    have hE := Real.exp_pos (Real.log x ^ d.a (I.max' hI))
    rw [Real.exp_neg, div_lt_iff₀ (hE.trans_le hle)]
    calc (15 : ℝ) < 100 * (Real.exp (Real.log x ^ d.a (I.max' hI)))⁻¹ *
          Real.exp (Real.log x ^ d.a (I.max' hI)) := by
          rw [mul_assoc, inv_mul_cancel₀ hE.ne']
          norm_num
      _ ≤ _ := by gcongr
  -- the phase separation forces `D₁ Z₁ = D₂ Z₂`
  have hDZ : omitProd p o₁ * ∏ j, Z₁ j = omitProd p o₂ * ∏ j, Z₂ j := by
    by_contra hne
    have h := hsep o₁ o₂ Z₁ hZ₁ Z₂ hZ₂ hD₁ hD₁' hD₂ hD₂' hne
    have heq : (((omitProd p o₁ * (∏ j, Z₁ j) * ∏ j, T j : ℕ) -
        (omitProd p o₂ * (∏ j, Z₂ j) * ∏ j, T j : ℕ) : ℤ) : ℝ) *
          (tau r (complement z) / tau r z) =
        (((omitProd p o₁ * ∏ j, Z₁ j : ℕ) : ℝ) - ((omitProd p o₂ * ∏ j, Z₂ j : ℕ) : ℝ)) *
          ((∏ j, T j : ℕ) : ℝ) * (tau r (complement z) / tau r z) := by
      push_cast
      ring
    rw [heq] at hanc
    linarith
  -- prime factorization separates `D` and `Z`
  have hcop : ∀ Z ∈ selections x d I (I.max' hI), (∀ j i h, Z j ≠ p i h) →
      Nat.Coprime (∏ j, Z j) P := by
    intro Z hZ hban
    refine Nat.Coprime.prod_left fun j _ => Nat.Coprime.prod_right fun i _ =>
      Nat.Coprime.prod_right fun h _ => ?_
    have hZj := Fintype.mem_piFinset.1 hZ j
    split_ifs at hZj with hj
    · exact (Nat.coprime_primes (TypeII.band_prime hZj) (hprime i h)).2 (hban j i h)
    · rw [mem_singleton.1 hZj]
      exact Nat.coprime_one_left _
  have hDpos : 0 < omitProd p o₁ := prod_pos fun i _ => prod_pos fun h _ => (hprime i h).pos
  obtain ⟨hD, hZ⟩ := eq_of_mul_eq_of_coprime hDZ (Dvd.intro _ (omitProd_mul_prod p o₁))
    (Dvd.intro _ (omitProd_mul_prod p o₂)) (hcop Z₁ hZ₁ hZban₁) (hcop Z₂ hZ₂ hZban₂) hDpos
  refine ⟨omitProd_injective hdisj hp hD, eq_of_prod_eq_of_band hdisj (fun j => ?_) hZ⟩
  have h₁ := Fintype.mem_piFinset.1 hZ₁ j
  have h₂ := Fintype.mem_piFinset.1 hZ₂ j
  split_ifs at h₁ h₂
  · exact Or.inr ⟨h₁, h₂⟩
  · exact Or.inl ⟨mem_singleton.1 h₁, mem_singleton.1 h₂⟩

end Erdos408.OneSided
