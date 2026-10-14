module

public import Erdos408.OneSided.Major.Characters
public import Erdos408.TwoSided.Endpoint.Tuple.Energy
public import Erdos408.TwoSided.Endpoint.Tuple.Sparse
public import Erdos821.P5MarkedEnergy.Factorization

/-!
# Boxes, classes, characters and separation (tuple part)

E6 of `blueprint/two_sided_correlation.md` §6.3 (PD (6.32); WD §§5.4–5.5).
The twisted polynomial of the tuple part is a sum over `w = p_s p_l u` (`twistedSum_eq`); fix
the dyadic boxes `p_s ∈ (2^i, 2^{i+1}]`, `p_l ∈ (2^j, 2^{j+1}]`, `u ∈ (2^l, 2^{l+1}]` and the
classes `p_s ≡ α`, `u ≡ β` mod `k`, and expand `e(hαβ p_l/k)` over the characters of `p_l`
with the vendored `Erdos821.P5Marked.e_eq_sum_cchi` (`phase_eq_sum_boxSet`,
`tripleSum_eq_sum_boxSet`). The cutoff `ψ₁(p_s p_l u/Y)` is
separated by its Mellin density (`boxSum_eq_integral`).
-/

@[expose] public section

namespace Erdos408.TwoSided.TupleHigh

open Filter Finset MeasureTheory

/-! ### The tuple sum -/

/-- `w ↦ (w/p_s/p_l)` is a bijection from the `w ∈ [⌈Y⌉, ⌊2Y⌋]` with `p_s ∣ w`, `p_l ∣ w/p_s`
onto the `u ∈ (1, ⌊2Y⌋]` with `p_s p_l u ∈ [⌈Y⌉, ⌊2Y⌋]`, when `p_s p_l < Y`. -/
theorem sum_filter_dvd_eq {Y : ℝ} {ps pl : ℕ} (hps : 0 < ps) (hpl : 0 < pl)
    (hY : ((ps * pl : ℕ) : ℝ) < Y) (G : ℕ → ℕ → ℂ) :
    ∑ w ∈ Icc ⌈Y⌉₊ ⌊2 * Y⌋₊, (if ps ∣ w ∧ pl ∣ w / ps then G w (w / ps / pl) else 0) =
      ∑ u ∈ (Ioc 1 ⌊2 * Y⌋₊).filter (fun u => ps * pl * u ∈ Icc ⌈Y⌉₊ ⌊2 * Y⌋₊),
        G (ps * pl * u) u := by
  rw [← sum_filter]
  refine sum_nbij' (fun w => w / ps / pl) (fun u => ps * pl * u) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_Icc] at hw
    obtain ⟨⟨hw₁, hw₂⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hw
    have hb' : w / ps / pl = b := by
      rw [hb, Nat.mul_div_cancel_left _ hpl]
    have hw : w = ps * pl * b := by
      rw [ha, Nat.mul_div_cancel_left _ hps] at hb
      rw [ha, hb]
      ring
    simp only [mem_filter, mem_Ioc, mem_Icc, hb']
    have hYw : Y ≤ w := (Nat.ceil_le.1 hw₁)
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · by_contra h
      have hb1 : b ≤ 1 := by omega
      have : ((ps * pl * b : ℕ) : ℝ) ≤ ((ps * pl : ℕ) : ℝ) := by
        have := Nat.mul_le_mul_left (ps * pl) hb1
        rw [mul_one] at this
        exact_mod_cast this
      rw [← hw] at this
      linarith
    · calc b ≤ ps * pl * b := Nat.le_mul_of_pos_left b (Nat.mul_pos hps hpl)
        _ = w := hw.symm
        _ ≤ ⌊2 * Y⌋₊ := hw₂
    · rw [← hw]; exact hw₁
    · rw [← hw]; exact hw₂
  · intro u hu
    simp only [mem_filter] at hu ⊢
    refine ⟨hu.2, dvd_mul_of_dvd_left (dvd_mul_right ps pl) u, ?_⟩
    rw [mul_assoc, Nat.mul_div_cancel_left _ hps]
    exact dvd_mul_right pl u
  · intro w hw
    simp only [mem_filter] at hw
    obtain ⟨-, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hw
    rw [ha, Nat.mul_div_cancel_left _ hps] at hb ⊢
    rw [hb, Nat.mul_div_cancel_left _ hpl]
    ring
  · intro u _
    rw [mul_assoc, Nat.mul_div_cancel_left _ hps, Nat.mul_div_cancel_left _ hpl]
  · intro w hw
    simp only [mem_filter] at hw
    obtain ⟨-, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hw
    have hb' : w / ps / pl = b := by rw [hb, Nat.mul_div_cancel_left _ hpl]
    have hw : w = ps * pl * b := by
      rw [ha, Nat.mul_div_cancel_left _ hps] at hb
      rw [ha, hb]
      ring
    rw [hb', ← hw]

/-- **The tuple sum.** For a cutoff `ψ₁` supported in `[1, 2]`, sets `s`, `sp` of positive
integers with `p_s p_l < Y`:
`∑_{w ∈ [⌈Y⌉, ⌊2Y⌋]} ψ₁(w/Y) F(w) ∑_{p_s ∣ w} ∑_{p_l ∣ w/p_s} c(w/p_s/p_l) =
∑_{p_s, p_l} ∑_{u ∈ (1, ⌊2Y⌋]} ψ₁(p_s p_l u/Y) F(p_s p_l u) c(u)`. -/
theorem twistedSum_eq {Y : ℝ} (s sp : Finset ℕ) (hs : ∀ p ∈ s, 0 < p) (hsp : ∀ p ∈ sp, 0 < p)
    (hsmall : ∀ ps ∈ s, ∀ pl ∈ sp, ((ps * pl : ℕ) : ℝ) < Y) (ψ₁ : ℝ → ℂ)
    (hψ : ∀ y, ψ₁ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) (F cf : ℕ → ℂ) (hY : 0 < Y) :
    ∑ w ∈ Icc ⌈Y⌉₊ ⌊2 * Y⌋₊, ψ₁ (w / Y) * F w *
        ∑ ps ∈ s.filter (· ∣ w), ∑ pl ∈ sp.filter (· ∣ w / ps), cf (w / ps / pl) =
      ∑ ps ∈ s, ∑ pl ∈ sp, ∑ u ∈ Ioc 1 ⌊2 * Y⌋₊,
        ψ₁ ((ps * pl * u : ℕ) / Y) * F (ps * pl * u) * cf u := by
  have h₁ : ∀ w : ℕ, ψ₁ (w / Y) * F w *
      ∑ ps ∈ s.filter (· ∣ w), ∑ pl ∈ sp.filter (· ∣ w / ps), cf (w / ps / pl) =
      ∑ ps ∈ s, ∑ pl ∈ sp, if ps ∣ w ∧ pl ∣ w / ps then
        ψ₁ ((ps * pl * (w / ps / pl) : ℕ) / Y) * F (ps * pl * (w / ps / pl)) *
          cf (w / ps / pl) else 0 := by
    intro w
    rw [mul_sum, sum_filter]
    refine sum_congr rfl fun ps _ => ?_
    split_ifs with hps
    · rw [mul_sum, sum_filter]
      refine sum_congr rfl fun pl _ => ?_
      by_cases hpl : pl ∣ w / ps
      · rw [ite_eq_left hpl, ite_eq_left ⟨hps, hpl⟩]
        have hw : ps * pl * (w / ps / pl) = w := by
          rw [mul_assoc, Nat.mul_div_cancel' hpl, Nat.mul_div_cancel' hps]
        rw [hw]
      · rw [ite_eq_right hpl, ite_eq_right fun h => hpl h.2]
    · exact (sum_eq_zero fun pl _ => ite_eq_right fun h => hps h.1).symm
  simp_rw [h₁]
  rw [sum_comm]
  refine sum_congr rfl fun ps hps => ?_
  rw [sum_comm]
  refine sum_congr rfl fun pl hpl => ?_
  rw [sum_filter_dvd_eq (hs ps hps) (hsp pl hpl) (hsmall ps hps pl hpl)
    (fun _ u => ψ₁ ((ps * pl * u : ℕ) / Y) * F (ps * pl * u) * cf u)]
  rw [sum_filter]
  refine sum_congr rfl fun u _ => ?_
  split_ifs with hu
  · rfl
  · -- outside `[⌈Y⌉, ⌊2Y⌋]` the cutoff vanishes
    have hψ0 : ψ₁ ((ps * pl * u : ℕ) / Y) = 0 := by
      by_contra h
      obtain ⟨h₁, h₂⟩ := hψ _ h
      apply hu
      rw [mem_Icc]
      constructor
      · exact Nat.ceil_le.2 (by rwa [le_div_iff₀ hY, one_mul] at h₁)
      · exact Nat.le_floor (by rwa [div_le_iff₀ hY] at h₂)
    rw [hψ0, zero_mul, zero_mul]

/-! ### Boxes, classes and characters -/

/-- The dyadic box of `p ≥ 2`: `p ∈ (2^i, 2^{i+1}]` for `i = boxIndex p`. -/
def boxIndex (p : ℕ) : ℕ := Nat.log 2 (p - 1)

/-- `boxIndex p = i` iff `p ∈ (2^i, 2^{i+1}]`, for `p ≥ 2`. -/
theorem boxIndex_eq_iff {p i : ℕ} (hp : 2 ≤ p) : boxIndex p = i ↔ 2 ^ i < p ∧ p ≤ 2 ^ (i + 1) := by
  rw [boxIndex, Nat.log_eq_iff (Or.inr ⟨one_lt_two, by omega⟩)]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by omega, by omega⟩

/-- The boxes below `N₀ ≥ 1` cover `[1, 2^{N₀}]`. -/
theorem boxIndex_lt {p N₀ : ℕ} (hN₀ : 1 ≤ N₀) (hp : p ≤ 2 ^ N₀) : boxIndex p < N₀ := by
  rw [boxIndex]
  rcases Nat.eq_zero_or_pos (p - 1) with h | h
  · rw [h, Nat.log_zero_right]
    omega
  · exact Nat.log_lt_of_lt_pow h.ne' (by omega)

/-- The index set of boxes, classes and characters. -/
noncomputable def boxSet (N₀ k : ℕ) :
    Finset (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × DirichletCharacter ℂ k)) :=
  ((range N₀ ×ˢ range N₀) ×ˢ range N₀) ×ˢ ((range k ×ˢ range k) ×ˢ univ)

/-- There are at most `N₀³ k³` boxes, classes and characters. -/
theorem card_boxSet_le (N₀ k : ℕ) [NeZero k] : #(boxSet N₀ k) ≤ N₀ ^ 3 * k ^ 3 := by
  rw [boxSet, card_product, card_product, card_product, card_product, card_product,
    card_range, card_range, card_univ]
  have := OneSided.card_dirichletCharacter_le k
  calc N₀ * N₀ * N₀ * (k * k * Fintype.card (DirichletCharacter ℂ k)) ≤
      N₀ * N₀ * N₀ * (k * k * k) := by gcongr
    _ = N₀ ^ 3 * k ^ 3 := by ring

/-- The condition that `(p_s, p_l, u)` lies in the box and classes of `m`. -/
def InBox {k : ℕ} (m : ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × DirichletCharacter ℂ k))
    (ps pl u : ℕ) : Prop :=
  (boxIndex ps = m.1.1.1 ∧ ps % k = m.2.1.1) ∧ boxIndex pl = m.1.1.2 ∧
    (boxIndex u = m.1.2 ∧ u % k = m.2.1.2)

/-- `InBox` is decidable. -/
instance {k : ℕ} (m : ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × DirichletCharacter ℂ k)) (ps pl u : ℕ) :
    Decidable (InBox m ps pl u) := by
  unfold InBox
  infer_instance

/-- The rational phase by boxes, classes and characters: for `p_l` coprime to `k` and
`p_s, p_l, u` in the boxes below `N₀`,
`e(h p_s p_l u/k) = ∑_m [(p_s, p_l, u) ∈ m] c_χ(h, αβ) χ(p_l)`. -/
theorem phase_eq_sum_boxSet {k : ℕ} (hk : 1 ≤ k) (h : ℤ) {N₀ ps pl u : ℕ}
    (hps : boxIndex ps < N₀) (hpl : boxIndex pl < N₀) (hu : boxIndex u < N₀)
    (hcop : Nat.Coprime pl k) :
    Erdos821.Blueprint.Analytic.e (h * (ps * pl * u : ℕ) / k) =
      ∑ m ∈ boxSet N₀ k, if InBox m ps pl u then
        Erdos821.P5Marked.cchi k h m.2.2 (m.2.1.1 * m.2.1.2) * m.2.2 pl else 0 := by
  rw [← sum_filter]
  have hfil : (boxSet N₀ k).filter (fun m => InBox m ps pl u) =
      (({boxIndex ps} ×ˢ {boxIndex pl}) ×ˢ {boxIndex u}) ×ˢ
        (({ps % k} ×ˢ {u % k}) ×ˢ univ) := by
    ext ⟨⟨⟨i, j⟩, l⟩, ⟨⟨α, β⟩, χ⟩⟩
    rw [mem_filter]
    simp only [boxSet, InBox, mem_product, mem_range, mem_singleton, mem_univ, and_true]
    have h₁ : ps % k < k := Nat.mod_lt _ (by omega)
    have h₂ : u % k < k := Nat.mod_lt _ (by omega)
    constructor
    · rintro ⟨-, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
      exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl, rfl⟩
    · rintro ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl, rfl⟩
      exact ⟨⟨⟨⟨hps, hpl⟩, hu⟩, h₁, h₂⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
  rw [hfil, singleton_product_singleton, singleton_product_singleton,
    singleton_product_singleton, sum_product, sum_singleton, sum_product, sum_singleton]
  rw [← Erdos821.P5Marked.e_eq_sum_cchi k hk h pl (ps % k * (u % k)) hcop]
  -- periodicity: `p_s u ≡ αβ mod k`
  set a := ps * u
  set b := ps % k * (u % k)
  have hab : a % k = b % k := Nat.mul_mod ps u k
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hdecomp : (h : ℝ) * ((ps * pl * u : ℕ) : ℝ) / k =
      (h : ℝ) * ((pl * b : ℕ) : ℝ) / k +
        ((h * pl * (((a / k : ℕ) : ℤ) - ((b / k : ℕ) : ℤ)) : ℤ) : ℝ) := by
    have ha : (a : ℝ) = ((a % k : ℕ) : ℝ) + k * ((a / k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_add_div a k).symm
    have hb : (b : ℝ) = ((b % k : ℕ) : ℝ) + k * ((b / k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_add_div b k).symm
    have hn : ((ps * pl * u : ℕ) : ℝ) = (pl : ℝ) * a := by
      simp only [a]
      push_cast
      ring
    have hq : ((h * pl * (((a / k : ℕ) : ℤ) - ((b / k : ℕ) : ℤ)) : ℤ) : ℝ) =
        (h : ℝ) * pl * (((a / k : ℕ) : ℝ) - ((b / k : ℕ) : ℝ)) := by
      simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast]
    rw [hq, hn, ha, hab, Nat.cast_mul pl b, hb]
    field_simp
    ring
  rw [hdecomp, Erdos821.P5Marked.e_periodic]

/-- Splitting a triple sum by boxes, classes and characters. -/
theorem tripleSum_eq_sum_boxSet {ι : Type*} (M : Finset ι) (C : ι → ℕ → ℕ → ℕ → Prop)
    [∀ m ps pl u, Decidable (C m ps pl u)] (γ : ι → ℂ) (χ : ι → ℕ → ℂ) (s sp U : Finset ℕ)
    (Φ : ℕ → ℕ → ℕ → ℂ) :
    ∑ ps ∈ s, ∑ pl ∈ sp, ∑ u ∈ U,
        Φ ps pl u * ∑ m ∈ M, (if C m ps pl u then γ m * χ m pl else 0) =
      ∑ m ∈ M, γ m * ∑ ps ∈ s, ∑ pl ∈ sp, ∑ u ∈ U,
        if C m ps pl u then χ m pl * Φ ps pl u else 0 := by
  have h₁ : ∀ ps pl u, Φ ps pl u * ∑ m ∈ M, (if C m ps pl u then γ m * χ m pl else 0) =
      ∑ m ∈ M, γ m * (if C m ps pl u then χ m pl * Φ ps pl u else 0) := by
    intro ps pl u
    rw [mul_sum]
    refine sum_congr rfl fun m _ => ?_
    split_ifs
    · ring
    · ring
  calc ∑ ps ∈ s, ∑ pl ∈ sp, ∑ u ∈ U,
        Φ ps pl u * ∑ m ∈ M, (if C m ps pl u then γ m * χ m pl else 0)
      = ∑ ps ∈ s, ∑ pl ∈ sp, ∑ u ∈ U, ∑ m ∈ M,
          γ m * (if C m ps pl u then χ m pl * Φ ps pl u else 0) :=
        sum_congr rfl fun ps _ => sum_congr rfl fun pl _ => sum_congr rfl fun u _ => h₁ ps pl u
    _ = ∑ ps ∈ s, ∑ pl ∈ sp, ∑ m ∈ M, ∑ u ∈ U,
          γ m * (if C m ps pl u then χ m pl * Φ ps pl u else 0) :=
        sum_congr rfl fun ps _ => sum_congr rfl fun pl _ => sum_comm
    _ = ∑ ps ∈ s, ∑ m ∈ M, ∑ pl ∈ sp, ∑ u ∈ U,
          γ m * (if C m ps pl u then χ m pl * Φ ps pl u else 0) :=
        sum_congr rfl fun ps _ => sum_comm
    _ = ∑ m ∈ M, ∑ ps ∈ s, ∑ pl ∈ sp, ∑ u ∈ U,
          γ m * (if C m ps pl u then χ m pl * Φ ps pl u else 0) := sum_comm
    _ = _ := sum_congr rfl fun m _ => by simp only [mul_sum]

/-! ### Separation and Cauchy–Schwarz -/

/-- `(y : ℂ)^{is} = exp(i s log y)` for `y > 0`. -/
theorem ofReal_cpow_mul_I {y : ℝ} (hy : 0 < y) (s : ℝ) :
    (y : ℂ) ^ ((s : ℂ) * Complex.I) = Complex.exp (((Real.log y * s : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), ← Complex.ofReal_log hy.le]
  push_cast
  ring_nf

/-- `(n/Y)^{iξ} n^{iτ} = Y^{-iξ} n^{i(τ + ξ)}` for `n, Y > 0`. -/
theorem div_cpow_mul_cpow {n : ℕ} (hn : 0 < n) {Y : ℝ} (hY : 0 < Y) (ξ τ : ℝ) :
    (((n : ℝ) / Y : ℝ) : ℂ) ^ ((ξ : ℂ) * Complex.I) * (n : ℂ) ^ ((τ : ℂ) * Complex.I) =
      (Y : ℂ) ^ (((-ξ : ℝ) : ℂ) * Complex.I) * (n : ℂ) ^ (((τ + ξ : ℝ) : ℂ) * Complex.I) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e₁ : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; rfl
  rw [e₁, ofReal_cpow_mul_I (div_pos hn' hY), ofReal_cpow_mul_I hn', ofReal_cpow_mul_I hY,
    ofReal_cpow_mul_I hn', ← Complex.exp_add, ← Complex.exp_add, Real.log_div hn'.ne' hY.ne']
  congr 1
  push_cast
  ring

/-- `(∑ f)(z (∑ g)(∑ h)) = ∑∑∑ f (z (g h))`. -/
theorem sum_mul_mul_sum_mul_sum (A B C : Finset ℕ) (f g h : ℕ → ℂ) (z : ℂ) :
    (∑ a ∈ A, f a) * (z * ((∑ b ∈ B, g b) * ∑ c ∈ C, h c)) =
      ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a * (z * (g b * h c)) := by
  rw [Finset.sum_mul]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]

/-- The box polynomial as a triple sum: `G(τ) = (YV)⁻¹ ∑ χ(p_l) c_u (p_s p_l u)^{iτ}`. -/
theorem boxPoly_eq_tripleSum {Y P V : ℝ} (hP : P ≠ 0) (sP spN uR : Finset ℕ) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (c : ℕ → ℂ) (τ : ℝ) :
    boxPoly Y P V sP spN uR χ c τ =
      (((Y * V)⁻¹ : ℝ) : ℂ) * ∑ ps ∈ sP, ∑ pl ∈ spN, ∑ u ∈ uR,
        χ pl * (c u * ((ps * pl * u : ℕ) : ℂ) ^ ((τ : ℂ) * Complex.I)) := by
  rw [boxPoly, sum_mul_mul_sum_mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun ps _ => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun pl _ => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [Nat.cast_mul (ps * pl) u, Complex.natCast_mul_natCast_cpow, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  have hP' : (P : ℂ) ≠ 0 := by exact_mod_cast hP
  push_cast
  field_simp

/-- The integral of a triple sum of integrable functions is the triple sum of the
integrals. -/
theorem integral_tripleSum {A B C : Finset ℕ} {f : ℕ → ℕ → ℕ → ℝ → ℂ}
    (hf : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, Integrable (f a b c)) :
    ∫ ξ, ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c ξ = ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∫ ξ, f a b c ξ := by
  rw [integral_finsetSum _ fun a ha => integrable_finsetSum _ fun b hb =>
    integrable_finsetSum _ fun c hc => hf a ha b hb c hc]
  refine sum_congr rfl fun a ha => ?_
  rw [integral_finsetSum _ fun b hb => integrable_finsetSum _ fun c hc => hf a ha b hb c hc]
  refine sum_congr rfl fun b hb => ?_
  rw [integral_finsetSum _ fun c hc => hf a ha b hb c hc]

/-- **Separation.** With a Mellin density `a` of `ψ₁`,
`(YV)⁻¹ ∑ χ(p_l) ψ₁(p_s p_l u/Y) c_u (p_s p_l u)^{i(t + σ)} =
∫ a(ξ) Y^{-2πiξ} G(t + σ + 2πξ) dξ`. -/
theorem boxSum_eq_integral {a : ℝ → ℂ} (ha : Integrable a) {ψ₁ : ℝ → ℂ}
    (hrep : ∀ y : ℝ, 0 < y →
      ψ₁ y = ∫ ξ, a ξ * (y : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I))
    {Y P V : ℝ} (hY : 0 < Y) (hP : P ≠ 0) {sP spN uR : Finset ℕ} (hsP : ∀ n ∈ sP, 0 < n)
    (hspN : ∀ n ∈ spN, 0 < n) (huR : ∀ n ∈ uR, 0 < n) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (c : ℕ → ℂ) (σ t : ℝ) :
    (((Y * V)⁻¹ : ℝ) : ℂ) * ∑ ps ∈ sP, ∑ pl ∈ spN, ∑ u ∈ uR,
        χ pl * (ψ₁ ((ps * pl * u : ℕ) / Y) *
          (c u * ((ps * pl * u : ℕ) : ℂ) ^ (((t + σ : ℝ) : ℂ) * Complex.I))) =
      ∫ ξ, a ξ * (Y : ℂ) ^ (((-(2 * Real.pi * ξ) : ℝ) : ℂ) * Complex.I) *
        boxPoly Y P V sP spN uR χ c (t + σ + 2 * Real.pi * ξ) := by
  -- each term is integrable
  have hterm : ∀ (z : ℂ) (n : ℕ), 0 < n → Integrable fun ξ : ℝ =>
      z * (a ξ * ((n / Y : ℝ) : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) := by
    intro z n hn
    refine Integrable.const_mul ?_ z
    have hcont : Continuous fun ξ : ℝ =>
        ((n / Y : ℝ) : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) := by
      simp_rw [ofReal_cpow_mul_I (div_pos (Nat.cast_pos.2 hn) hY)]
      fun_prop
    have h := ha.bdd_mul (c := 1) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by
        rw [ofReal_cpow_mul_I (div_pos (Nat.cast_pos.2 hn) hY), Complex.norm_exp_ofReal_mul_I])
    simpa only [mul_comm] using h
  have hn : ∀ ps ∈ sP, ∀ pl ∈ spN, ∀ u ∈ uR, 0 < ps * pl * u := fun ps hps pl hpl u hu =>
    Nat.mul_pos (Nat.mul_pos (hsP ps hps) (hspN pl hpl)) (huR u hu)
  -- expand `ψ₁` and exchange the sums with the integral
  have h₁ : (((Y * V)⁻¹ : ℝ) : ℂ) * ∑ ps ∈ sP, ∑ pl ∈ spN, ∑ u ∈ uR,
        χ pl * (ψ₁ ((ps * pl * u : ℕ) / Y) *
          (c u * ((ps * pl * u : ℕ) : ℂ) ^ (((t + σ : ℝ) : ℂ) * Complex.I))) =
      ∑ ps ∈ sP, ∑ pl ∈ spN, ∑ u ∈ uR, ∫ ξ,
        ((((Y * V)⁻¹ : ℝ) : ℂ) * χ pl * c u *
          ((ps * pl * u : ℕ) : ℂ) ^ (((t + σ : ℝ) : ℂ) * Complex.I)) *
        (a ξ * ((((ps * pl * u : ℕ) : ℝ) / Y : ℝ) : ℂ) ^
          (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) := by
    rw [mul_sum]
    refine sum_congr rfl fun ps hps => ?_
    rw [mul_sum]
    refine sum_congr rfl fun pl hpl => ?_
    rw [mul_sum]
    refine sum_congr rfl fun u hu => ?_
    rw [integral_const_mul, ← hrep _ (div_pos (by exact_mod_cast hn ps hps pl hpl u hu) hY)]
    ring
  rw [h₁]
  have h₂ : ∀ ps ∈ sP, ∀ pl ∈ spN, ∀ u ∈ uR, Integrable fun ξ : ℝ =>
      ((((Y * V)⁻¹ : ℝ) : ℂ) * χ pl * c u *
          ((ps * pl * u : ℕ) : ℂ) ^ (((t + σ : ℝ) : ℂ) * Complex.I)) *
        (a ξ * ((((ps * pl * u : ℕ) : ℝ) / Y : ℝ) : ℂ) ^
          (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) :=
    fun ps hps pl hpl u hu => hterm _ _ (hn ps hps pl hpl u hu)
  rw [← integral_tripleSum h₂]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [boxPoly_eq_tripleSum hP]
  simp only [Finset.mul_sum]
  refine sum_congr rfl fun ps hps => sum_congr rfl fun pl hpl => sum_congr rfl fun u hu => ?_
  have h₃ := div_cpow_mul_cpow (hn ps hps pl hpl u hu) hY (2 * Real.pi * ξ) (t + σ)
  push_cast at h₃ ⊢
  rw [show ((t : ℂ) + σ + 2 * Real.pi * ξ) = (t + σ + 2 * Real.pi * ξ) by ring]
  linear_combination ((Y : ℂ)⁻¹ * (V : ℂ)⁻¹ * χ pl * c u * a ξ) * h₃

end Erdos408.TwoSided.TupleHigh
