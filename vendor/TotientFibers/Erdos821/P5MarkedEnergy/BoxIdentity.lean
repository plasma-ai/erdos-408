import Erdos821.P5MarkedEnergy.Factorization
import Erdos821.P5MarkedEnergy.Collapse
import Erdos821.P5.MellinVectors

/-! The Mellin box identity: a smoothly cut four-fold convolution, as a Dirichlet
polynomial, is `Y` times a finite sum over relevant dyadic boxes of
Mellin-separated products of four dyadic polynomials. Irrelevant boxes vanish
exactly before separation. -/

noncomputable section
open scoped BigOperators
open MeasureTheory Classical

namespace Erdos821.P5Marked
open Blueprint.Analytic

abbrev Q4 := ℕ × ℕ × ℕ × ℕ

def prod4 (z : Q4) : ℕ := z.1 * z.2.1 * z.2.2.1 * z.2.2.2

def box4 (β : Q4) : Finset Q4 := dyad β.1 ×ˢ dyad β.2.1 ×ˢ dyad β.2.2.1 ×ˢ dyad β.2.2.2

def allBoxes (K : ℕ) : Finset Q4 :=
  Finset.range (K + 1) ×ˢ Finset.range (K + 1) ×ˢ Finset.range (K + 1) ×ˢ Finset.range (K + 1)

def icc4 (N : ℕ) : Finset Q4 :=
  Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N

def bsize (β : Q4) : ℕ := β.1 + β.2.1 + β.2.2.1 + β.2.2.2

/-- The box polynomial. -/
def boxPoly (f1 f2 f3 f4 : ℕ → ℂ) (β : Q4) (τ : ℝ) : ℂ :=
  hpoly f1 β.1 τ * hpoly f2 β.2.1 τ * hpoly f3 β.2.2.1 τ * hpoly f4 β.2.2.2 τ

/-- The relevant boxes for a piece supported in `[α, 2α]`. -/
def relBoxes (K : ℕ) (αY : ℝ) : Finset Q4 :=
  (allBoxes K).filter fun β => αY < 16 * (2 : ℝ) ^ bsize β ∧ (2 : ℝ) ^ bsize β ≤ 2 * αY

theorem quad_eq_sum_icc4 (f1 f2 f3 f4 : ℕ → ℂ) (N n : ℕ) :
    quad f1 f2 f3 f4 N n = ∑ z ∈ icc4 N,
      if prod4 z = n then f1 z.1 * f2 z.2.1 * f3 z.2.2.1 * f4 z.2.2.2 else 0 := by
  unfold quad icc4 prod4
  simp only [Finset.sum_product]

theorem dyad_disjoint {i j : ℕ} (hij : i ≠ j) : Disjoint (dyad i) (dyad j) := by
  rw [Finset.disjoint_left]
  intro m hi hj
  have h1 := Nat.log_eq_of_pow_le_of_lt_pow (mem_dyad.mp hi).1 (mem_dyad.mp hi).2
  have h2 := Nat.log_eq_of_pow_le_of_lt_pow (mem_dyad.mp hj).1 (mem_dyad.mp hj).2
  exact hij (h1.symm.trans h2)

theorem mem_dyad_log {m : ℕ} (hm : 1 ≤ m) : m ∈ dyad (Nat.log 2 m) :=
  mem_dyad.mpr ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) m⟩

theorem box4_disjoint {K : ℕ} : (allBoxes K : Set Q4).PairwiseDisjoint box4 := by
  intro β _ β' _ hne
  simp only [Function.onFun]
  unfold box4
  rw [Finset.disjoint_left]
  intro z hz hz'
  simp only [Finset.mem_product] at hz hz'
  apply hne
  have e1 : β.1 = β'.1 := by
    by_contra h; exact Finset.disjoint_left.mp (dyad_disjoint h) hz.1 hz'.1
  have e2 : β.2.1 = β'.2.1 := by
    by_contra h; exact Finset.disjoint_left.mp (dyad_disjoint h) hz.2.1 hz'.2.1
  have e3 : β.2.2.1 = β'.2.2.1 := by
    by_contra h; exact Finset.disjoint_left.mp (dyad_disjoint h) hz.2.2.1 hz'.2.2.1
  have e4 : β.2.2.2 = β'.2.2.2 := by
    by_contra h; exact Finset.disjoint_left.mp (dyad_disjoint h) hz.2.2.2 hz'.2.2.2
  exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))

/-- Decomposition of the tuple range into dyadic boxes. -/
theorem sum_icc4_eq_boxes (N : ℕ) (hN : 1 ≤ N) (Gf : Q4 → ℂ)
    (hG : ∀ z, 1 ≤ z.1 → 1 ≤ z.2.1 → 1 ≤ z.2.2.1 → 1 ≤ z.2.2.2 → N < prod4 z → Gf z = 0) :
    ∑ z ∈ icc4 N, Gf z = ∑ β ∈ allBoxes (Nat.log 2 N), ∑ z ∈ box4 β, Gf z := by
  set K := Nat.log 2 N
  rw [← Finset.sum_biUnion (box4_disjoint (K := K))]
  apply Finset.sum_subset
  · intro z hz
    simp only [icc4, Finset.mem_product, Finset.mem_Icc] at hz
    apply Finset.mem_biUnion.mpr
    refine ⟨(Nat.log 2 z.1, Nat.log 2 z.2.1, Nat.log 2 z.2.2.1, Nat.log 2 z.2.2.2), ?_, ?_⟩
    · simp only [allBoxes, Finset.mem_product, Finset.mem_range]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Nat.lt_succ_of_le <;> apply Nat.log_mono_right <;> omega
    · simp only [box4, Finset.mem_product]
      exact ⟨mem_dyad_log hz.1.1, mem_dyad_log hz.2.1.1, mem_dyad_log hz.2.2.1.1,
        mem_dyad_log hz.2.2.2.1⟩
  · intro z hz hnot
    obtain ⟨β, hβ, hzβ⟩ := Finset.mem_biUnion.mp hz
    simp only [box4, Finset.mem_product] at hzβ
    have h1 := dyad_pos hzβ.1
    have h2 := dyad_pos hzβ.2.1
    have h3 := dyad_pos hzβ.2.2.1
    have h4 := dyad_pos hzβ.2.2.2
    apply hG z h1 h2 h3 h4
    by_contra hle
    rw [not_lt] at hle
    apply hnot
    have c1 : z.1 ≤ prod4 z := by
      unfold prod4; rw [mul_assoc, mul_assoc]; exact Nat.le_mul_of_pos_right _ (by positivity)
    have c2 : z.2.1 ≤ prod4 z := by
      unfold prod4
      calc z.2.1 ≤ z.1 * z.2.1 := Nat.le_mul_of_pos_left _ h1
        _ ≤ z.1 * z.2.1 * z.2.2.1 := Nat.le_mul_of_pos_right _ h3
        _ ≤ _ := Nat.le_mul_of_pos_right _ h4
    have c3 : z.2.2.1 ≤ prod4 z := by
      unfold prod4
      calc z.2.2.1 ≤ z.1 * z.2.1 * z.2.2.1 := Nat.le_mul_of_pos_left _ (by positivity)
        _ ≤ _ := Nat.le_mul_of_pos_right _ h4
    have c4 : z.2.2.2 ≤ prod4 z := by
      unfold prod4; exact Nat.le_mul_of_pos_left _ (by positivity)
    simp only [icc4, Finset.mem_product, Finset.mem_Icc]
    omega

theorem box4_prod_bounds (β : Q4) (z : Q4) (hz : z ∈ box4 β) :
    2 ^ bsize β ≤ prod4 z ∧ prod4 z < 16 * 2 ^ bsize β := by
  simp only [box4, Finset.mem_product] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have a1 := mem_dyad.mp h1; have a2 := mem_dyad.mp h2
  have a3 := mem_dyad.mp h3; have a4 := mem_dyad.mp h4
  unfold bsize prod4
  constructor
  · rw [pow_add, pow_add, pow_add]
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul a1.1 a2.1) a3.1) a4.1
  · have : 16 * 2 ^ (β.1 + β.2.1 + β.2.2.1 + β.2.2.2) =
        2 ^ (β.1 + 1) * 2 ^ (β.2.1 + 1) * 2 ^ (β.2.2.1 + 1) * 2 ^ (β.2.2.2 + 1) := by
      rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
    rw [this]
    exact Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (Nat.mul_lt_mul'' a1.2 a2.2) a3.2) a4.2

theorem sum_mul_sum_product {α β : Type*} (A : Finset α) (B : Finset β) (f : α → ℂ) (g : β → ℂ) :
    (∑ x ∈ A, f x) * (∑ y ∈ B, g y) = ∑ w ∈ A ×ˢ B, f w.1 * g w.2 := by
  rw [Finset.sum_product, Finset.sum_mul_sum]

theorem term4_eq (a b c d M1 M2 M3 M4 : ℂ) (m s p k : ℕ) (hm : 0 < m) (hs : 0 < s)
    (hp : 0 < p) (hk : 0 < k) :
    a / (m : ℂ) * M1 * (b / (s : ℂ) * M2 * (c / (p : ℂ) * M3 * (d / (k : ℂ) * M4))) =
      a * b * c * d / ((m * s * p * k : ℕ) : ℂ) * (M1 * M2 * M3 * M4) := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp

theorem boxPoly_eq_sum (f1 f2 f3 f4 : ℕ → ℂ) (β : Q4) (τ : ℝ) :
    boxPoly f1 f2 f3 f4 β τ = ∑ z ∈ box4 β,
      f1 z.1 * f2 z.2.1 * f3 z.2.2.1 * f4 z.2.2.2 / (prod4 z : ℂ) * mellin (prod4 z : ℕ) τ := by
  have h1 : boxPoly f1 f2 f3 f4 β τ =
      hpoly f1 β.1 τ * (hpoly f2 β.2.1 τ * (hpoly f3 β.2.2.1 τ * hpoly f4 β.2.2.2 τ)) := by
    unfold boxPoly; ring
  rw [h1]
  unfold hpoly dp box4
  rw [sum_mul_sum_product, sum_mul_sum_product, sum_mul_sum_product]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [Finset.mem_product] at hz
  have hm0 := dyad_pos hz.1; have hs0 := dyad_pos hz.2.1
  have hp0 := dyad_pos hz.2.2.1; have hk0 := dyad_pos hz.2.2.2
  have hmel : mellin ((prod4 z : ℕ) : ℝ) τ =
      mellin (z.1 : ℝ) τ * mellin (z.2.1 : ℝ) τ * mellin (z.2.2.1 : ℝ) τ *
        mellin (z.2.2.2 : ℝ) τ := by
    unfold prod4
    push_cast
    rw [P5Core.mellin_mul _ _ _ (by positivity) (by positivity),
      P5Core.mellin_mul _ _ _ (by positivity) (by positivity),
      P5Core.mellin_mul _ _ _ (by positivity) (by positivity)]
  rw [hmel]
  exact term4_eq _ _ _ _ _ _ _ _ _ _ _ _ hm0 hs0 hp0 hk0

theorem continuous_mellin_freq (y : ℝ) : Continuous (fun ξ : Fin 1 → ℝ => Blueprint.Analytic.mellin y (2 * Real.pi * ξ 0)) := by
  unfold Blueprint.Analytic.mellin; fun_prop

theorem integrable_mul_mellin {a : (Fin 1 → ℝ) → ℂ} (ha : Integrable a) (y : ℝ) (h : (Fin 1 → ℝ) → ℂ)
    (hh : Continuous h) (C : ℝ) (hC : ∀ ξ, ‖h ξ‖ ≤ C) :
    Integrable (fun ξ => a ξ * h ξ) :=
  ha.mul_bdd hh.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- The Mellin box identity. -/
theorem mellin_box_identity (f1 f2 f3 f4 : ℕ → ℂ) (Ψi : ℝ → ℂ) (a : (Fin 1 → ℝ) → ℂ)
    (ha : Integrable a) (Y α v : ℝ) (hY : 0 < Y) (hα : 0 < α)
    (hsupp : ∀ y, Ψi y ≠ 0 → α ≤ y ∧ y ≤ 2 * α)
    (hrep : ∀ y : ℝ, 0 < y → (y : ℂ) * Ψi y = ∫ ξ, a ξ * Blueprint.Analytic.mellin y (2 * Real.pi * ξ 0))
    (N : ℕ) (hN : 1 ≤ N) (S : Finset ℕ) (hS : ∀ n : ℕ, Ψi (n / Y) ≠ 0 → n ∈ S)
    (hSN : S ⊆ Finset.Icc 1 N) (t : ℝ) :
    dp S (fun n => Ψi (n / Y) * Blueprint.Analytic.mellin n v * quad f1 f2 f3 f4 N n) t =
      (Y : ℂ) * ∑ β ∈ relBoxes (Nat.log 2 N) (α * Y),
        ∫ ξ, (a ξ * Blueprint.Analytic.mellin (1 / Y) (2 * Real.pi * ξ 0)) *
          boxPoly f1 f2 f3 f4 β (t + v + 2 * Real.pi * ξ 0) := by
  set F : Q4 → ℂ := fun z => f1 z.1 * f2 z.2.1 * f3 z.2.2.1 * f4 z.2.2.2 with hF
  set g : ℕ → ℂ := fun n => Ψi (n / Y) * Blueprint.Analytic.mellin n (t + v) with hg
  have hgS : ∀ n, n ∉ S → g n = 0 := by
    intro n hn
    simp only [hg]
    by_contra h
    exact hn (hS n (left_ne_zero_of_mul h))
  -- Step A, B
  have hA : dp S (fun n => Ψi (n / Y) * Blueprint.Analytic.mellin n v * quad f1 f2 f3 f4 N n) t =
      ∑ n ∈ Finset.Icc 1 N, g n * quad f1 f2 f3 f4 N n := by
    unfold dp
    rw [← Finset.sum_subset hSN]
    · apply Finset.sum_congr rfl
      intro n _
      simp only [hg]
      rw [P5Core.mellin_add (n : ℝ) t v]
      ring
    · intro n _ hn
      rw [hgS n hn, zero_mul]
  -- Step C
  have hC : ∑ n ∈ Finset.Icc 1 N, g n * quad f1 f2 f3 f4 N n =
      ∑ z ∈ icc4 N, g (prod4 z) * F z := by
    simp_rw [quad_eq_sum_icc4, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z hz
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hmem
    · rfl
    · symm
      have : prod4 z ∉ S := fun h => hmem (hSN h)
      rw [hgS _ this, zero_mul]
  -- Step D
  have hD : ∑ z ∈ icc4 N, g (prod4 z) * F z =
      ∑ β ∈ allBoxes (Nat.log 2 N), ∑ z ∈ box4 β, g (prod4 z) * F z := by
    apply sum_icc4_eq_boxes N hN
    intro z _ _ _ _ hz
    have : prod4 z ∉ S := fun h => by
      have := (Finset.mem_Icc.mp (hSN h)).2; omega
    rw [hgS _ this, zero_mul]
  -- Step E
  have hE : ∑ β ∈ allBoxes (Nat.log 2 N), ∑ z ∈ box4 β, g (prod4 z) * F z =
      ∑ β ∈ relBoxes (Nat.log 2 N) (α * Y), ∑ z ∈ box4 β, g (prod4 z) * F z := by
    unfold relBoxes
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro β _
    split_ifs with hrel
    · rfl
    · apply Finset.sum_eq_zero
      intro z hz
      have hb := box4_prod_bounds β z hz
      have hzero : Ψi (prod4 z / Y) = 0 := by
        by_contra hne
        have h := hsupp _ hne
        apply hrel
        have hb1 : (2 : ℝ) ^ bsize β ≤ prod4 z := by exact_mod_cast hb.1
        have hb2 : (prod4 z : ℝ) < 16 * 2 ^ bsize β := by exact_mod_cast hb.2
        have e1 : α * Y ≤ prod4 z := by
          have := h.1; rw [le_div_iff₀ hY] at this; linarith
        have e2 : (prod4 z : ℝ) ≤ 2 * (α * Y) := by
          have := h.2; rw [div_le_iff₀ hY] at this; linarith
        constructor <;> linarith
      simp only [hg, hzero, zero_mul]
  -- Step F
  have hF' : ∀ β, ∑ z ∈ box4 β, g (prod4 z) * F z =
      (Y : ℂ) * ∫ ξ, (a ξ * Blueprint.Analytic.mellin (1 / Y) (2 * Real.pi * ξ 0)) *
        boxPoly f1 f2 f3 f4 β (t + v + 2 * Real.pi * ξ 0) := by
    intro β
    have hterm : ∀ z ∈ box4 β, g (prod4 z) * F z = (Y : ℂ) * ∫ ξ,
        (a ξ * Blueprint.Analytic.mellin (1 / Y) (2 * Real.pi * ξ 0)) *
          (F z / (prod4 z : ℂ) * Blueprint.Analytic.mellin (prod4 z : ℕ) (t + v + 2 * Real.pi * ξ 0)) := by
      intro z hz
      have hpos : 0 < prod4 z := lt_of_lt_of_le (Nat.two_pow_pos _) (box4_prod_bounds β z hz).1
      have hposR : (0 : ℝ) < prod4 z := by exact_mod_cast hpos
      set y : ℝ := prod4 z / Y with hy
      have hy0 : 0 < y := div_pos hposR hY
      have hΨ : Ψi y = (Y / prod4 z : ℂ) * ∫ ξ, a ξ * Blueprint.Analytic.mellin y (2 * Real.pi * ξ 0) := by
        rw [← hrep y hy0]
        have hyc : (y : ℂ) = (prod4 z : ℂ) / Y := by rw [hy]; push_cast; ring
        rw [hyc]
        have : (prod4 z : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
        have : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
        field_simp
      have hmy : ∀ s : ℝ, Blueprint.Analytic.mellin y s = Blueprint.Analytic.mellin (prod4 z : ℕ) s * Blueprint.Analytic.mellin (1 / Y) s := by
        intro s
        rw [hy, div_eq_mul_one_div]
        exact P5Core.mellin_mul _ _ _ hposR (by positivity)
      have hpc : (prod4 z : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      calc g (prod4 z) * F z
          = (Y / prod4 z : ℂ) * (∫ ξ, a ξ * Blueprint.Analytic.mellin y (2 * Real.pi * ξ 0)) *
              (Blueprint.Analytic.mellin (prod4 z : ℕ) (t + v) * F z) := by
            simp only [hg]; rw [hΨ]; ring
        _ = ∫ ξ, (Y / prod4 z : ℂ) * (a ξ * Blueprint.Analytic.mellin y (2 * Real.pi * ξ 0)) *
              (Blueprint.Analytic.mellin (prod4 z : ℕ) (t + v) * F z) := by
            rw [integral_mul_const, integral_const_mul]
        _ = ∫ ξ, (Y : ℂ) * ((a ξ * Blueprint.Analytic.mellin (1 / Y) (2 * Real.pi * ξ 0)) *
              (F z / (prod4 z : ℂ) * Blueprint.Analytic.mellin (prod4 z : ℕ)
                (t + v + 2 * Real.pi * ξ 0))) := by
            congr 1; funext ξ
            rw [hmy, P5Core.mellin_add (prod4 z : ℕ) (t + v) (2 * Real.pi * ξ 0)]
            field_simp
        _ = _ := integral_const_mul _ _
    have hint : ∀ z ∈ box4 β, Integrable (fun ξ : Fin 1 → ℝ =>
        (a ξ * Blueprint.Analytic.mellin (1 / Y) (2 * Real.pi * ξ 0)) *
          (F z / (prod4 z : ℂ) * Blueprint.Analytic.mellin (prod4 z : ℕ)
            (t + v + 2 * Real.pi * ξ 0))) := by
      intro z _
      have h1 : Integrable (fun ξ : Fin 1 → ℝ =>
          a ξ * Blueprint.Analytic.mellin (1 / Y) (2 * Real.pi * ξ 0)) :=
        ha.mul_bdd (continuous_mellin_freq _).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ξ => (P5Core.norm_mellin _ _).le)
      refine h1.mul_bdd (c := ‖F z / (prod4 z : ℂ)‖) ?_ (Filter.Eventually.of_forall fun ξ => ?_)
      · apply Continuous.aestronglyMeasurable
        unfold Blueprint.Analytic.mellin; fun_prop
      · rw [norm_mul, P5Core.norm_mellin, mul_one]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← integral_finset_sum _ hint]
    congr 1
    congr 1
    funext ξ
    rw [← Finset.mul_sum, boxPoly_eq_sum]
  rw [hA, hC, hD, hE, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun β _ => hF' β)

end Erdos821.P5Marked
