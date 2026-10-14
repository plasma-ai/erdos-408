module

public import Erdos408.OneSided.Bands
public import Erdos408.OneSided.Lift
public import Erdos408.OneSided.Pairing.Cells

/-!
# The endpoint vector

The facts about `f = ᾱ_m β_{P₂}` used in PD §3.3 (`blueprint/one_sided_type_ii.md` §4,
Lemma 4.2).

* With disjoint bands the labels of a state are distinct primes dividing `P₁`, so the list
  product divides `P₁`.
* `f` is constant on the lists at a position: if `f ≠ 0` at one list, then `m = P₁ / G` is
  rough, so every label of another list divides `G`, and the two lists have the same labels
  in each group.
* `|f|² ≤ L^{4C}`, and `‖f‖² ≤ 64 σ U V` whenever `|f|² ≤ σ`: at a fixed list with product
  `G` there are at most `32 U / G` first coordinates `P₁ = G m` with `α_m ≠ 0`, and
  `∏_i V_i^{-M} ∑_{lists} 1 / G ≤ 1`.
-/

@[expose] public section

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ} {x : ℝ} {d : Data K} {Y d₀ : ℝ}

/-- The defining properties of a state. -/
theorem state_props (s : State x d Y d₀) :
    s.1.1 ∈ positions d Y d₀ ∧ (∀ i h, s.1.2 i h ∈ band x (d.a i)) ∧
      (∀ i, Function.Injective (s.1.2 i)) ∧ ∀ i h, s.1.2 i h ∣ s.1.1.1 := by
  have hs : s.1 ∈ states x d Y d₀ := s.2
  unfold states lists at hs
  rw [mem_filter, mem_product, mem_filter, Fintype.mem_piFinset] at hs
  exact ⟨hs.1.1, fun i h => Fintype.mem_piFinset.1 (hs.1.2.1 i) h, hs.1.2.2, hs.2⟩

/-- With disjoint bands, the labels of a state are distinct across groups and slots. -/
theorem label_injective {J : ℕ} {p : Lists K J}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hband : ∀ i h, p i h ∈ band x (d.a i)) (hinj : ∀ i, Function.Injective (p i)) :
    Function.Injective fun ih : Fin K × Fin (J + 1) => p ih.1 ih.2 := by
  rintro ⟨i, h⟩ ⟨i', h'⟩ heq
  simp only at heq
  have hi : i = i' := by
    by_contra hne
    exact disjoint_left.1 (hdisj i i' hne) (hband i h) (heq ▸ hband i' h')
  subst hi
  rw [hinj i heq]

/-- With disjoint bands, the list product of distinct band primes dividing `n` divides `n`. -/
theorem listProd_dvd_of_dvd {J : ℕ} {p : Lists K J} {n : ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hband : ∀ i h, p i h ∈ band x (d.a i)) (hinj : ∀ i, Function.Injective (p i))
    (hdvd : ∀ i h, p i h ∣ n) : listProd p ∣ n := by
  have hg := label_injective hdisj hband hinj
  have himg : ∏ v ∈ univ.image fun ih : Fin K × Fin (J + 1) => p ih.1 ih.2, v =
      ∏ ih : Fin K × Fin (J + 1), p ih.1 ih.2 :=
    prod_image fun a _ b _ h => hg h
  unfold listProd
  rw [← Fintype.prod_prod_type' (fun i h => p i h), ← himg]
  refine prod_primes_dvd _ (fun a ha => ?_) fun a ha => ?_
  · obtain ⟨⟨i, h⟩, -, rfl⟩ := mem_image.1 ha
    exact (TypeII.band_prime (hband i h)).prime
  · obtain ⟨⟨i, h⟩, -, rfl⟩ := mem_image.1 ha
    exact hdvd i h

/-- With disjoint bands, the list product of a state divides `P₁`. -/
theorem listProd_dvd (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (s : State x d Y d₀) : listProd s.1.2 ∣ s.1.1.1 := by
  obtain ⟨-, hband, hinj, hdvd⟩ := state_props s
  exact listProd_dvd_of_dvd hdisj hband hinj hdvd

/-- If `α_{P₁ / G} ≠ 0` at one list with product `G`, then every list at the same position
has the product `G`. -/
theorem listProd_eq_of_alpha_ne_zero {C CX alo ahi g : ℝ} (hd : Admissible C CX alo ahi g x d)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hrough : ∀ i, ∀ p ∈ band x (d.a i), ∀ m : ℕ, m ≠ 0 → IsRough x m → ¬ p ∣ m)
    (hHm : 0 < d.Hm) {s s' : State x d Y d₀} (hpos : s.1.1 = s'.1.1)
    (hα : d.α (s.1.1.1 / listProd s.1.2) ≠ 0) : listProd s'.1.2 = listProd s.1.2 := by
  obtain ⟨-, hband, hinj, -⟩ := state_props s
  obtain ⟨-, hband', hinj', hdvd'⟩ := state_props s'
  set G := listProd s.1.2 with hG
  set m := s.1.1.1 / G
  obtain ⟨hm₁, -, hmr, -⟩ := hd.α_supp m hα
  have hm₀ : m ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hm₁
    linarith
  have hP : s.1.1.1 = G * m := (Nat.mul_div_cancel' (listProd_dvd hdisj s)).symm
  -- every label of `s'` in group `i` is a label of `s` in group `i`
  have hsub : ∀ i, univ.image (s'.1.2 i) ⊆ univ.image (s.1.2 i) := by
    intro i v hv
    obtain ⟨h, -, rfl⟩ := mem_image.1 hv
    have hpr := (TypeII.band_prime (hband' i h)).prime
    have hdvdG : s'.1.2 i h ∣ G := by
      have h₁ : s'.1.2 i h ∣ G * m := by rw [← hP, hpos]; exact hdvd' i h
      exact (hpr.dvd_or_dvd h₁).resolve_right (hrough i _ (hband' i h) m hm₀ hmr)
    obtain ⟨i', -, hi'⟩ := hpr.exists_mem_finset_dvd hdvdG
    obtain ⟨h', -, hh'⟩ := hpr.exists_mem_finset_dvd hi'
    have heq := (Nat.prime_dvd_prime_iff_eq (TypeII.band_prime (hband' i h))
      (TypeII.band_prime (hband i' h'))).1 hh'
    have hii : i' = i := by
      by_contra hne
      exact disjoint_left.1 (hdisj i' i hne) (hband i' h') (heq ▸ hband' i h)
    subst hii
    exact mem_image.2 ⟨h', mem_univ _, heq.symm⟩
  -- both images have `J + 1` elements, so they agree
  have himage : ∀ i, univ.image (s'.1.2 i) = univ.image (s.1.2 i) := by
    intro i
    refine eq_of_subset_of_card_le (hsub i) ?_
    rw [card_image_of_injective _ (hinj i), card_image_of_injective _ (hinj' i)]
  unfold listProd
  refine prod_congr rfl fun i _ => ?_
  have h₁ : ∏ v ∈ univ.image (s'.1.2 i), v = ∏ h, s'.1.2 i h :=
    prod_image fun a _ b _ h => hinj' i h
  have h₂ : ∏ v ∈ univ.image (s.1.2 i), v = ∏ h, s.1.2 i h :=
    prod_image fun a _ b _ h => hinj i h
  rw [← h₁, ← h₂, himage i]

/-- `f` is constant on the lists at a position. -/
theorem endVec_eq_of_pos_eq {C CX alo ahi g : ℝ} (hd : Admissible C CX alo ahi g x d)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hrough : ∀ i, ∀ p ∈ band x (d.a i), ∀ m : ℕ, m ≠ 0 → IsRough x m → ¬ p ∣ m)
    (hHm : 0 < d.Hm) {s s' : State x d Y d₀} (hpos : s.1.1 = s'.1.1) :
    endVec x d Y d₀ s = endVec x d Y d₀ s' := by
  unfold endVec
  by_cases hα : d.α (s.1.1.1 / listProd s.1.2) = 0
  · by_cases hα' : d.α (s'.1.1.1 / listProd s'.1.2) = 0
    · rw [hα, hα', star_zero, zero_mul, zero_mul]
    · rw [listProd_eq_of_alpha_ne_zero hd hdisj hrough hHm hpos.symm hα', hpos]
  · rw [listProd_eq_of_alpha_ne_zero hd hdisj hrough hHm hpos hα, hpos]

/-! ### Norms -/

/-- `|f|² ≤ L^{4C}`, from `|α|, |β| ≤ L^C`. -/
theorem norm_endVec_sq_le {C CX alo ahi g : ℝ} (hd : Admissible C CX alo ahi g x d)
    (hL : 0 < Real.log x) (s : State x d Y d₀) :
    ‖endVec x d Y d₀ s‖ ^ 2 ≤ Real.log x ^ (4 * C) := by
  have hα : ∀ m, ‖d.α m‖ ≤ Real.log x ^ C := by
    intro m
    by_cases h : d.α m = 0
    · rw [h, norm_zero]
      positivity
    · exact (hd.α_supp m h).2.2.2
  have hβ : ∀ n, ‖d.β n‖ ≤ Real.log x ^ C := by
    intro n
    by_cases h : d.β n = 0
    · rw [h, norm_zero]
      positivity
    · exact (hd.β_supp n h).2.2.2
  unfold endVec
  rw [norm_mul, norm_star]
  calc (‖d.α (s.1.1.1 / listProd s.1.2)‖ * ‖d.β s.1.1.2‖) ^ 2
      ≤ (Real.log x ^ C * Real.log x ^ C) ^ 2 :=
        pow_le_pow_left₀ (by positivity)
          (mul_le_mul (hα _) (hβ _) (norm_nonneg _) (by positivity)) 2
    _ = Real.log x ^ (4 * C) := by
        rw [← Real.rpow_add hL, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
        congr 1
        push_cast
        ring

/-- `∏_i V_i ≥ 0`. -/
theorem bandMass_nonneg (x : ℝ) (d : Data K) : 0 ≤ d.bandMass x :=
  prod_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity

/-- The state measure is nonnegative. -/
theorem stateMass_nonneg (x : ℝ) (d : Data K) : 0 ≤ stateMass x d :=
  pow_nonneg (inv_nonneg.2 (bandMass_nonneg x d)) _

/-- `∏_i V_i^{-M} ∑_{lists} 1 / G ≤ 1`: dropping distinctness, the sum is `∏_i V_i^M`. -/
theorem stateMass_mul_sum_inv_listProd_le (x : ℝ) (d : Data K) :
    stateMass x d * ∑ p ∈ lists x d (padCount x), ((listProd p : ℕ) : ℝ)⁻¹ ≤ 1 := by
  set J := padCount x
  have hsum : ∑ p ∈ lists x d J, ((listProd p : ℕ) : ℝ)⁻¹ ≤ d.bandMass x ^ (J + 1) := by
    calc ∑ p ∈ lists x d J, ((listProd p : ℕ) : ℝ)⁻¹
        ≤ ∑ p ∈ Fintype.piFinset (fun i => Fintype.piFinset fun _ : Fin (J + 1) =>
            band x (d.a i)), ∏ i, ∏ h, ((p i h : ℕ) : ℝ)⁻¹ := by
          refine (sum_congr rfl fun p _ => ?_).trans_le
            (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ => by positivity)
          unfold listProd
          push_cast
          simp_rw [prod_inv_distrib]
      _ = ∏ i, ∑ q ∈ Fintype.piFinset (fun _ : Fin (J + 1) => band x (d.a i)),
            ∏ h, ((q h : ℕ) : ℝ)⁻¹ :=
          (prod_univ_sum (fun i => Fintype.piFinset fun _ : Fin (J + 1) => band x (d.a i))
            fun _ q => ∏ h, ((q h : ℕ) : ℝ)⁻¹).symm
      _ = ∏ i, ∏ _h : Fin (J + 1), ∑ r ∈ band x (d.a i), ((r : ℕ) : ℝ)⁻¹ :=
          prod_congr rfl fun i _ =>
            (prod_univ_sum (fun _ : Fin (J + 1) => band x (d.a i))
              fun _ r => ((r : ℕ) : ℝ)⁻¹).symm
      _ = d.bandMass x ^ (J + 1) := by
          unfold Data.bandMass harmonicMass
          rw [← prod_pow]
          simp [one_div]
  calc stateMass x d * ∑ p ∈ lists x d J, ((listProd p : ℕ) : ℝ)⁻¹
      ≤ (d.bandMass x)⁻¹ ^ (J + 1) * d.bandMass x ^ (J + 1) :=
        mul_le_mul_of_nonneg_left hsum (stateMass_nonneg x d)
    _ = ((d.bandMass x)⁻¹ * d.bandMass x) ^ (J + 1) := (mul_pow _ _ _).symm
    _ ≤ 1 := by
        rcases eq_or_ne (d.bandMass x) 0 with h | h
        · rw [h, inv_zero, zero_mul, zero_pow (Nat.succ_ne_zero _)]
          exact zero_le_one
        · rw [inv_mul_cancel₀ h, one_pow]

/-- `#(ℕ ∩ [a, b]) ≤ b - a + 1`. -/
theorem card_Icc_ceil_floor_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((Icc ⌈a⌉₊ ⌊b⌋₊).card : ℝ) ≤ b - a + 1 := by
  have h := Nat.card_Icc ⌈a⌉₊ ⌊b⌋₊
  rcases (show (Icc ⌈a⌉₊ ⌊b⌋₊).card + ⌈a⌉₊ ≤ ⌊b⌋₊ + 1 ∨ (Icc ⌈a⌉₊ ⌊b⌋₊).card = 0 by omega)
    with h₁ | h₁
  · have h₂ : ((Icc ⌈a⌉₊ ⌊b⌋₊).card : ℝ) + ⌈a⌉₊ ≤ ⌊b⌋₊ + 1 := by exact_mod_cast h₁
    linarith [Nat.le_ceil a, Nat.floor_le (ha.trans hab)]
  · rw [h₁, Nat.cast_zero]
    linarith

/-- PD (3.18): `‖f‖² ≤ 64 σ U V` when `|f|² ≤ σ`, with `U = d₀ Y H_m` and `V = H_n`. -/
theorem stateMass_mul_sqNorm_endVec_le {C CX alo ahi g : ℝ}
    (hd : Admissible C CX alo ahi g x d)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hHm : 1 ≤ d.Hm) (hHn : 1 ≤ d.Hn) (hd₀Y : 0 < d₀ * Y) {σ : ℝ} (hσ : 0 ≤ σ)
    (hfσ : ∀ s, ‖endVec x d Y d₀ s‖ ^ 2 ≤ σ) :
    stateMass x d * sqNorm (endVec x d Y d₀) ≤ 64 * σ * (d₀ * Y * d.Hm * d.Hn) := by
  set U := d₀ * Y * d.Hm with hU
  have hU₀ : 0 < U := mul_pos hd₀Y (by linarith)
  set e : (ℕ × ℕ) × Lists K (padCount x) → ℝ :=
    fun s => if d.α (s.1.1 / listProd s.2) ≠ 0 then σ else 0 with he
  have he₀ : ∀ s, 0 ≤ e s := fun s => by
    simp only [he]
    split_ifs
    · exact hσ
    · exact le_rfl
  -- pointwise, `|f|² ≤ σ` where `α_m ≠ 0`
  have h₁ : sqNorm (endVec x d Y d₀) ≤ ∑ s ∈ states x d Y d₀, e s := by
    unfold sqNorm
    rw [← sum_coe_sort (states x d Y d₀) e]
    refine sum_le_sum fun s _ => ?_
    by_cases hα : d.α (s.1.1.1 / listProd s.1.2) = 0
    · have h₀ : endVec x d Y d₀ s = 0 := by
        unfold endVec
        rw [hα, star_zero, zero_mul]
      rw [h₀, norm_zero, zero_pow two_ne_zero]
      exact he₀ _
    · simp only [he]
      rw [ite_eq_left hα]
      exact hfσ s
  -- at a fixed list with product `G`, at most `(32 U / G) (2 V)` positions contribute
  have h₂ : ∀ p ∈ lists x d (padCount x), ∑ P ∈ positions d Y d₀,
      (if ∀ i h, p i h ∣ P.1 then e (P, p) else 0) ≤
        64 * σ * (U * d.Hn) * ((listProd p : ℕ) : ℝ)⁻¹ := by
    intro p hp
    unfold lists at hp
    rw [mem_filter, Fintype.mem_piFinset] at hp
    have hband : ∀ i h, p i h ∈ band x (d.a i) := fun i h => Fintype.mem_piFinset.1 (hp.1 i) h
    set G := listProd p with hG
    have hG₀ : 0 < G := prod_pos fun i _ => prod_pos fun h _ =>
      (TypeII.band_prime (hband i h)).pos
    have hG₀' : (0 : ℝ) < G := Nat.cast_pos.2 hG₀
    set A₁ := (Icc ⌈U⌉₊ ⌊16 * U⌋₊).filter fun n => G ∣ n ∧ d.α (n / G) ≠ 0 with hA₁
    set A₂ := Icc ⌈d.Hn⌉₊ ⌊2 * d.Hn⌋₊ with hA₂
    -- the contributing positions lie in `A₁ × A₂`
    have hcount : ∑ P ∈ positions d Y d₀, (if ∀ i h, p i h ∣ P.1 then e (P, p) else 0) ≤
        σ * ((A₁.card : ℝ) * A₂.card) := by
      calc ∑ P ∈ positions d Y d₀, (if ∀ i h, p i h ∣ P.1 then e (P, p) else 0)
          ≤ ∑ P ∈ positions d Y d₀, (if P ∈ A₁ ×ˢ A₂ then σ else 0) := by
            refine sum_le_sum fun P hP => ?_
            unfold positions at hP
            rw [mem_filter, mem_product] at hP
            by_cases hQ : ∀ i h, p i h ∣ P.1
            · rw [ite_eq_left hQ]
              simp only [he]
              by_cases hα : d.α (P.1 / G) = 0
              · rw [ite_eq_right (not_not.2 hα)]
                split_ifs
                · exact hσ
                · exact le_rfl
              · rw [ite_eq_left hα, ite_eq_left]
                rw [mem_product, hA₁, mem_filter]
                exact ⟨⟨hP.1.1, listProd_dvd_of_dvd hdisj hband hp.2 hQ, hα⟩, hP.1.2⟩
            · rw [ite_eq_right hQ]
              split_ifs
              · exact hσ
              · exact le_rfl
        _ = σ * ((positions d Y d₀ ∩ A₁ ×ˢ A₂).card : ℝ) := by
            rw [sum_ite_mem, sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ σ * ((A₁.card : ℝ) * A₂.card) := by
            refine mul_le_mul_of_nonneg_left ?_ hσ
            rw [← Nat.cast_mul, ← card_product]
            exact_mod_cast card_le_card inter_subset_right
    -- `#A₂ ≤ 2V`
    have hA₂card : (A₂.card : ℝ) ≤ 2 * d.Hn := by
      have := card_Icc_ceil_floor_le (by linarith : 0 ≤ d.Hn) (by linarith : d.Hn ≤ 2 * d.Hn)
      linarith
    -- `#A₁ G ≤ 32 U`: `n ↦ n / G` is injective into `[H_m, 2H_m]`, and `G H_m ≤ 16 U`
    have hA₁card : (A₁.card : ℝ) * G ≤ 32 * U := by
      rcases A₁.eq_empty_or_nonempty with h | ⟨n₀, hn₀⟩
      · rw [h, card_empty, Nat.cast_zero, zero_mul]
        positivity
      have hmaps : ∀ n ∈ A₁, n / G ∈ Icc ⌈d.Hm⌉₊ ⌊2 * d.Hm⌋₊ := by
        intro n hn
        obtain ⟨h₁, h₂, -, -⟩ := hd.α_supp _ (mem_filter.1 hn).2.2
        rw [mem_Icc]
        exact ⟨Nat.ceil_le.2 h₁, Nat.le_floor h₂⟩
      have hinj : Set.InjOn (· / G) A₁ := by
        intro n hn n' hn' h
        simp only at h
        rw [← Nat.div_mul_cancel (mem_filter.1 hn).2.1,
          ← Nat.div_mul_cancel (mem_filter.1 hn').2.1, h]
      have hcard : (A₁.card : ℝ) ≤ (Icc ⌈d.Hm⌉₊ ⌊2 * d.Hm⌋₊).card := by
        exact_mod_cast card_le_card_of_injOn _ (fun n hn => hmaps n hn) hinj
      have hIcc := card_Icc_ceil_floor_le (by linarith : 0 ≤ d.Hm) (by linarith : d.Hm ≤ 2 * d.Hm)
      have hGHm : (G : ℝ) * d.Hm ≤ 16 * U := by
        obtain ⟨hn₀I, hn₀G, hn₀α⟩ := mem_filter.1 hn₀
        obtain ⟨h₁, -, -, -⟩ := hd.α_supp _ hn₀α
        have hn₀16 : (n₀ : ℝ) ≤ 16 * U :=
          (Nat.le_floor_iff (by positivity)).1 (mem_Icc.1 hn₀I).2
        have hn₀eq : (n₀ : ℝ) = G * (n₀ / G : ℕ) := by
          exact_mod_cast (Nat.mul_div_cancel' hn₀G).symm
        nlinarith
      nlinarith
    calc ∑ P ∈ positions d Y d₀, (if ∀ i h, p i h ∣ P.1 then e (P, p) else 0)
        ≤ σ * ((A₁.card : ℝ) * A₂.card) := hcount
      _ ≤ σ * ((32 * U * (G : ℝ)⁻¹) * (2 * d.Hn)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ hA₂card (Nat.cast_nonneg _)
            (by positivity)) hσ
          rw [← div_eq_mul_inv, le_div_iff₀ hG₀']
          exact hA₁card
      _ = 64 * σ * (U * d.Hn) * ((listProd p : ℕ) : ℝ)⁻¹ := by ring
  -- sum over the lists
  have h₃ : ∑ s ∈ states x d Y d₀, e s ≤
      64 * σ * (U * d.Hn) * ∑ p ∈ lists x d (padCount x), ((listProd p : ℕ) : ℝ)⁻¹ := by
    unfold states
    rw [sum_filter, sum_product_right, mul_sum]
    exact sum_le_sum h₂
  calc stateMass x d * sqNorm (endVec x d Y d₀)
      ≤ stateMass x d * (64 * σ * (U * d.Hn) *
          ∑ p ∈ lists x d (padCount x), ((listProd p : ℕ) : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (h₁.trans h₃) (stateMass_nonneg x d)
    _ = 64 * σ * (U * d.Hn) *
          (stateMass x d * ∑ p ∈ lists x d (padCount x), ((listProd p : ℕ) : ℝ)⁻¹) := by ring
    _ ≤ 64 * σ * (U * d.Hn) * 1 :=
        mul_le_mul_of_nonneg_left (stateMass_mul_sum_inv_listProd_le x d) (by positivity)
    _ = 64 * σ * (d₀ * Y * d.Hm * d.Hn) := by rw [hU]; ring

end Erdos408.OneSided
