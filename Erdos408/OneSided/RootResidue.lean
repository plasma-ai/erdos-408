module

public import Erdos408.OneSided.Analysis.Kloosterman
public import Erdos408.OneSided.RootResidue.Hyperbola
public import Erdos408.OneSided.RootResidue.Progression
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Root residues

PD Lemma 3.3 (`blueprint/one_sided_type_ii.md` §5.2). Count the primitive `(u, v)` in a box
`u/U ∈ [a₁, b₁)`, `v/V ∈ [a₂, b₂)` whose completion `g = (u c; v d)`, with `ud - vc = 1` and
`0 ≤ c < u`, has `c/u ∈ [a₃, b₃)` and `g ≡ g₀ (mod S)`. The count is
`c₂ UV |I₁||I₂||I₃| / |SL₂(ℤ/S)| + O(UV S² min(U, V)^{-1/5})`, uniformly in the intervals
and in `g₀`, where `c₂ = ∑ μ(l)/l² = 1/ζ(2)`.

The proof follows PD with the discrepancy step of the blueprint. Suppose `U ≤ V`; the other
case swaps roles, as at the end of PD's proof of Lemma 3.3 (`rootCount_le_swap`,
`swap_le_rootCount`).

* Fix `u ≡ u₀ (S)` and put `S₁ = (u, S)`, `S₂ = S / S₁`. The roots over `u` are the points
  `(c, v)` of the box `[a₃ u, b₃ u) × [a₂ V, b₂ V)` with `c ≡ c₀`, `v ≡ v₀ (mod S₂)` whose
  residues mod `m₁ = u S₁` lie on the twisted hyperbola `c v = u d₀ - 1`, `c ≡ c₀ (mod S₁)`
  (`fibreCount_eq_card`).
* Completion on `(ℤ/m₁)²` (`RootResidue/Fourier.lean`) counts these with error
  `X τ(m₁) (2 + log m₁)²`, whatever the length of the `v`-range, once the hyperbola sums
  satisfy `|Ŝ(h, k)| ≤ X (k, m₁)` for `k ≠ 0`. By `det:CRT-Fourier` they are averages of
  `K_{m₁}(h + j u, k a')`, so the weak Kloosterman bound gives `X ≪ m₁^{3/4 + 1/100}`
  (`RootResidue/Hyperbola.lean`). The main term is the column count
  `#{c ∈ [a₃ u, b₃ u) : c ≡ c₀ (S), (c, u) = 1}`, by Möbius inversion
  `(b₃ - a₃) u/S · ∑_{l ∣ u, (l, S) = 1} μ(l)/l + O(τ(u))` (`abs_fibreCount_sub_le`).
* Sum over `u`, and average the Euler factor over `u ≡ u₀ (S)`
  (`RootResidue/Progression.lean`). This gives the main term
  `U V |I₁||I₂||I₃| ∑_{(l, S) = 1} μ(l)/l² / S³` with error `O(U^{4/5} V S²)`.
* The constant is identified without computing `|SL₂(ℤ/S)|`: the counts over all
  `g₀ ∈ SL₂(ℤ/S)` add up to the count for `S = 1`, and comparing main terms as
  `U = V → ∞` gives `∑_{(l, S) = 1} μ(l)/l² / S³ = c₂ / |SL₂(ℤ/S)|`
  (`coprimeDensity_div_eq`).
-/

@[expose] public section

namespace Erdos408.OneSided

open Finset

/-- `c₂ = ∑_l μ(l)/l² = 1/ζ(2)`, the density of primitive vectors. -/
noncomputable def primitiveDensity : ℝ := ∑' l : ℕ, (ArithmeticFunction.moebius l : ℝ) / l ^ 2

/-- The completion `c ∈ [0, u)` of a primitive `(u, v)`: `c ≡ -v⁻¹ (mod u)`. -/
def rootC (u v : ℕ) : ℕ := (-(v : ZMod u)⁻¹ : ZMod u).val

/-- `d = (1 + v c)/u`, so that `u d - v c = 1`. -/
def rootD (u v : ℕ) : ℕ := (1 + v * rootC u v) / u

/-- The number of primitive `(u, v)` with `u/U ∈ [a₁, b₁)`, `v/V ∈ [a₂, b₂)`,
`c/u ∈ [a₃, b₃)` and `(u c; v d) ≡ g₀ (mod S)`. -/
noncomputable def rootCount (U V a₁ b₁ a₂ b₂ a₃ b₃ : ℝ) (S : ℕ)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) : ℕ :=
  ((Icc ⌈a₁ * U⌉₊ ⌊b₁ * U⌋₊ ×ˢ Icc ⌈a₂ * V⌉₊ ⌊b₂ * V⌋₊).filter fun P =>
    Nat.Coprime P.1 P.2 ∧ (P.1 : ℝ) < b₁ * U ∧ (P.2 : ℝ) < b₂ * V ∧
      a₃ ≤ (rootC P.1 P.2 : ℝ) / P.1 ∧ (rootC P.1 P.2 : ℝ) / P.1 < b₃ ∧
      !![(P.1 : ZMod S), (rootC P.1 P.2 : ZMod S); (P.2 : ZMod S), (rootD P.1 P.2 : ZMod S)] =
        g₀).card

namespace RootResidue

/-! ### The completion -/

/-- `0 ≤ c < u`. -/
theorem rootC_lt {u : ℕ} (hu : 0 < u) (v : ℕ) : rootC u v < u := by
  have : NeZero u := ⟨hu.ne'⟩
  exact ZMod.val_lt _

/-- For `(u, v) = 1`, `u ∣ c v + 1`. -/
theorem dvd_rootC_mul_add_one {u v : ℕ} (hu : 0 < u) (huv : u.Coprime v) :
    u ∣ rootC u v * v + 1 := by
  have : NeZero u := ⟨hu.ne'⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [rootC, ZMod.natCast_zmod_val, neg_mul, mul_comm, ZMod.coe_mul_inv_eq_one v huv.symm,
    neg_add_cancel]

/-- `c` is the unique residue in `[0, u)` with `u ∣ c v + 1`; this also forces `(u, v) = 1`. -/
theorem rootC_eq_of_dvd {u v c : ℕ} (hc : c < u) (h : u ∣ c * v + 1) :
    u.Coprime v ∧ rootC u v = c := by
  have : NeZero u := ⟨(c.zero_le.trans_lt hc).ne'⟩
  have h' : (c : ZMod u) * v = -1 := by
    rw [← ZMod.natCast_eq_zero_iff] at h
    push_cast at h
    linear_combination h
  have hunit : (v : ZMod u) * (-(c : ZMod u)) = 1 := by linear_combination -h'
  refine ⟨((ZMod.isUnit_iff_coprime v u).1 (Units.mkOfMulEqOne _ _ hunit).isUnit).symm, ?_⟩
  rw [rootC, ZMod.inv_eq_of_mul_eq_one _ _ _ hunit, neg_neg, ZMod.val_natCast,
    Nat.mod_eq_of_lt hc]

/-- `u d = 1 + v c`. -/
theorem mul_rootD {u v : ℕ} (hu : 0 < u) (huv : u.Coprime v) :
    u * rootD u v = 1 + v * rootC u v := by
  rw [rootD, Nat.mul_div_cancel']
  rw [add_comm, mul_comm]
  exact dvd_rootC_mul_add_one hu huv

/-- `!![a, b; c, d] = g` entrywise. -/
theorem matrix_eq_iff {R : Type*} (a b c d : R) (g : Matrix (Fin 2) (Fin 2) R) :
    !![a, b; c, d] = g ↔ a = g 0 0 ∧ b = g 0 1 ∧ c = g 1 0 ∧ d = g 1 1 := by
  rw [← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  tauto

/-! ### The congruences at fixed `u` -/

/-- With `S₁ = (u, S)` and `S₂ = S / S₁` for squarefree `S`: `S₁ S₂ = S`, `(S₁, S₂) = 1` and
`(u, S₂) = 1`. -/
theorem gcd_facts {S : ℕ} (hS : Squarefree S) (u : ℕ) :
    Nat.gcd u S * (S / Nat.gcd u S) = S ∧ (Nat.gcd u S).Coprime (S / Nat.gcd u S) ∧
      u.Coprime (S / Nat.gcd u S) := by
  have h₁ : Nat.gcd u S * (S / Nat.gcd u S) = S := Nat.mul_div_cancel' (Nat.gcd_dvd_right u S)
  have h₂ : (Nat.gcd u S).Coprime (S / Nat.gcd u S) :=
    Nat.coprime_of_squarefree_mul (by rw [h₁]; exact hS)
  refine ⟨h₁, h₂, ?_⟩
  -- a common divisor of `u` and `S₂` divides both `S₁` and `S₂`
  refine Nat.coprime_of_dvd' fun p hp hpu hpS₂ => ?_
  have hpS : p ∣ S := hpS₂.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right u S))
  have := Nat.dvd_gcd (Nat.dvd_gcd hpu hpS) hpS₂
  rwa [h₂.gcd_eq_one] at this

/-- PD (3.25)–(3.26), in congruences. Fix `u ≡ u₀ (mod S)` and `g₀ = (u₀ c₀; v₀ d₀)` with
`u₀ d₀ ≡ c₀ v₀ + 1 (mod S)`; put `S₁ = (u, S)`, `S₂ = S / S₁`. For `0 ≤ c < u`, the pair
`(c, v)` is a root `c = c(u, v)` with `g ≡ g₀ (mod S)` exactly when
`c v + 1 ≡ u d₀ (mod u S₁)`, `c ≡ c₀ (mod S)` and `v ≡ v₀ (mod S₂)`. -/
theorem fixedU_modEq_iff {S u u₀ c₀ v₀ d₀ c v : ℕ} (hS : Squarefree S) (hu : 0 < u)
    (huu₀ : u ≡ u₀ [MOD S]) (hdet : u₀ * d₀ ≡ c₀ * v₀ + 1 [MOD S]) (hc : c < u) :
    (c * v + 1 ≡ u * d₀ [MOD u * Nat.gcd u S] ∧ c ≡ c₀ [MOD Nat.gcd u S] ∧
        c ≡ c₀ [MOD S / Nat.gcd u S] ∧ v ≡ v₀ [MOD S / Nat.gcd u S]) ↔
      (u.Coprime v ∧ rootC u v = c ∧ v ≡ v₀ [MOD S] ∧ c ≡ c₀ [MOD S] ∧
        rootD u v ≡ d₀ [MOD S]) := by
  obtain ⟨hS₁₂, hcop, huS₂⟩ := gcd_facts hS u
  set S₁ := Nat.gcd u S
  set S₂ := S / S₁
  have hS₁u : S₁ ∣ u := Nat.gcd_dvd_left u S
  have hS₁S : S₁ ∣ S := Nat.gcd_dvd_right u S
  have hS₂S : S₂ ∣ S := Nat.div_dvd_of_dvd hS₁S
  -- the CRT for `S = S₁ S₂`
  have hcrt : ∀ {a b : ℕ}, a ≡ b [MOD S₁] → a ≡ b [MOD S₂] → a ≡ b [MOD S] := fun h₁ h₂ => by
    rw [← hS₁₂]; exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h₁, h₂⟩
  -- `u ≡ 0 (mod S₁)`, so `c₀ v₀ + 1 ≡ 0 (mod S₁)` and `c₀` is a unit mod `S₁`
  have hu₀ : u₀ ≡ 0 [MOD S₁] :=
    (huu₀.of_dvd hS₁S).symm.trans (Nat.modEq_zero_iff_dvd.2 hS₁u)
  have hcv₀ : c₀ * v₀ + 1 ≡ 0 [MOD S₁] := by
    have := (hdet.of_dvd hS₁S).symm.trans (hu₀.mul_right d₀)
    rwa [zero_mul] at this
  have hc₀ : Nat.gcd S₁ c₀ = 1 := by
    refine Nat.eq_one_of_dvd_one ?_
    have h₁ : Nat.gcd S₁ c₀ ∣ c₀ * v₀ + 1 :=
      (Nat.gcd_dvd_left _ _).trans (Nat.modEq_zero_iff_dvd.1 hcv₀)
    exact (Nat.dvd_add_right ((Nat.gcd_dvd_right _ _).mul_right v₀)).1 h₁
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    -- reduce mod `u`: `u ∣ c v + 1`
    have hdvd : u ∣ c * v + 1 := by
      have := h₁.of_mul_right S₁
      exact (Nat.modEq_zero_iff_dvd.1 (this.trans (Nat.modEq_zero_iff_dvd.2 (dvd_mul_right u d₀))))
    obtain ⟨huv, hroot⟩ := rootC_eq_of_dvd hc hdvd
    have hcS := hcrt h₂ h₃
    refine ⟨huv, hroot, hcrt ?_ h₄, hcS, ?_⟩
    · -- `c₀ v + 1 ≡ c v + 1 ≡ u d₀ ≡ 0 ≡ c₀ v₀ + 1 (mod S₁)`
      have hcv : c * v + 1 ≡ 0 [MOD S₁] :=
        (h₁.of_mul_left u).trans (Nat.modEq_zero_iff_dvd.2 (hS₁u.mul_right d₀))
      have : c₀ * v + 1 ≡ c₀ * v₀ + 1 [MOD S₁] :=
        ((h₂.symm.mul_right v).add_right 1).trans (hcv.trans hcv₀.symm)
      exact Nat.ModEq.cancel_left_of_coprime hc₀ (Nat.ModEq.add_right_cancel' 1 this)
    · -- `u d = c v + 1 ≡ u d₀` mod `u S₁` and mod `S₂`, hence mod `u S`
      have hud := mul_rootD hu huv
      rw [hroot, add_comm, mul_comm v] at hud
      have hS₂ : c * v + 1 ≡ u * d₀ [MOD S₂] :=
        ((((h₃.mul_right v).trans (h₄.mul_left c₀)).add_right 1).trans
          (hdet.symm.of_dvd hS₂S)).trans ((huu₀.symm.of_dvd hS₂S).mul_right d₀)
      have hmod : u * rootD u v ≡ u * d₀ [MOD u * S] := by
        rw [hud, ← hS₁₂, ← mul_assoc]
        exact (Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.mul_left huS₂ hcop)).1 ⟨h₁, hS₂⟩
      exact Nat.ModEq.mul_left_cancel' hu.ne' hmod
  · rintro ⟨huv, hroot, hv, hcS, hd⟩
    have hud := mul_rootD hu huv
    rw [hroot, add_comm, mul_comm v] at hud
    have hmod : c * v + 1 ≡ u * d₀ [MOD u * S] := hud ▸ hd.mul_left' u
    exact ⟨hmod.of_dvd (Nat.mul_dvd_mul_left u hS₁S), hcS.of_dvd hS₁S, hcS.of_dvd hS₂S,
      hv.of_dvd hS₂S⟩

/-- `(x : ZMod S) = z` exactly when `x ≡ z.val (mod S)`. -/
theorem natCast_eq_iff_modEq {S : ℕ} [NeZero S] (x : ℕ) (z : ZMod S) :
    (x : ZMod S) = z ↔ x ≡ z.val [MOD S] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]

/-- The determinant condition on the lifts: `u₀ d₀ ≡ c₀ v₀ + 1 (mod S)`. -/
theorem det_modEq {S : ℕ} [NeZero S] {g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)} (hg : g₀.det = 1) :
    (g₀ 0 0).val * (g₀ 1 1).val ≡ (g₀ 0 1).val * (g₀ 1 0).val + 1 [MOD S] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  simp only [ZMod.natCast_zmod_val]
  rw [Matrix.det_fin_two] at hg
  linear_combination hg

/-! ### The count at fixed `u` -/

/-- The fibre of `rootCount` over `u`: the `v ∈ [α, β)` with `(u, v) = 1`,
`c/u ∈ [a₃, b₃)` and `g ≡ g₀ (mod S)`. -/
noncomputable def fibreCount (S : ℕ) (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S))
    (α β a₃ b₃ : ℝ) (u : ℕ) : ℕ :=
  #{v ∈ Ico ⌈α⌉₊ ⌈β⌉₊ | u.Coprime v ∧ a₃ ≤ (rootC u v : ℝ) / u ∧ (rootC u v : ℝ) / u < b₃ ∧
    !![(u : ZMod S), (rootC u v : ZMod S); (v : ZMod S), (rootD u v : ZMod S)] = g₀}

/-- The admissible residues `(c, v) mod u S₁`, `S₁ = (u, S)`: the twisted hyperbola
`c v = u d₀ - 1`, `c ≡ c₀ (mod S₁)`. -/
noncomputable def fibreSet (S u : ℕ) (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S))
    [NeZero (u * Nat.gcd u S)] : Finset (ZMod (u * Nat.gcd u S) × ZMod (u * Nat.gcd u S)) :=
  hyperbola (u * Nat.gcd u S) ((u : ZMod (u * Nat.gcd u S)) * ((g₀ 1 1).val : ZMod _) - 1)
    u ((g₀ 0 1).val : ZMod _)

/-- Membership in `fibreSet` in congruences: `c v + 1 ≡ u d₀ (mod u S₁)` and
`c ≡ c₀ (mod S₁)`. -/
theorem mem_fibreSet_iff {S u : ℕ} (hu : 0 < u) (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S))
    [NeZero (u * Nat.gcd u S)] (c v : ℕ) :
    ((c : ZMod (u * Nat.gcd u S)), (v : ZMod (u * Nat.gcd u S))) ∈ fibreSet S u g₀ ↔
      c * v + 1 ≡ u * (g₀ 1 1).val [MOD u * Nat.gcd u S] ∧
        c ≡ (g₀ 0 1).val [MOD Nat.gcd u S] := by
  rw [fibreSet, hyperbola, mem_filter]
  simp only [mem_univ, true_and]
  refine and_congr ?_ ?_
  · rw [eq_sub_iff_add_eq, ← ZMod.natCast_eq_natCast_iff]
    push_cast
    rfl
  · rw [← Nat.ModEq.mul_left_cancel_iff' hu.ne', ← ZMod.natCast_eq_natCast_iff]
    push_cast
    rfl

/-- PD (3.25)–(3.26): the fibre over `u ≡ u₀ (mod S)` is the number of points `(c, v)` of the
box `[a₃ u, b₃ u) × [α, β)`, restricted to the progressions `c ≡ c₀`, `v ≡ v₀ (mod S₂)`,
whose residues mod `u S₁` lie in `fibreSet`. -/
theorem fibreCount_eq_card {S u : ℕ} [NeZero S] (hS : Squarefree S)
    {g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)} (hg : g₀.det = 1) (hu : 0 < u)
    (hu₀ : (u : ZMod S) = g₀ 0 0) {α β a₃ b₃ : ℝ} (hb₃ : b₃ ≤ 1)
    [NeZero (u * Nat.gcd u S)] :
    fibreCount S g₀ α β a₃ b₃ u =
      #{p ∈ prog (a₃ * u) (b₃ * u) (S / Nat.gcd u S) ((g₀ 0 1).val % (S / Nat.gcd u S)) ×ˢ
          prog α β (S / Nat.gcd u S) ((g₀ 1 0).val % (S / Nat.gcd u S)) |
        ((p.1 : ZMod (u * Nat.gcd u S)), (p.2 : ZMod (u * Nat.gcd u S))) ∈ fibreSet S u g₀} := by
  set S₂ := S / Nat.gcd u S
  have hS₂ : 0 < S₂ := Nat.div_pos (Nat.le_of_dvd (NeZero.pos S) (Nat.gcd_dvd_right u S))
    (Nat.gcd_pos_of_pos_left S hu)
  have hu' : (0 : ℝ) < u := Nat.cast_pos.2 hu
  have hdet := det_modEq hg
  have huu₀ : u ≡ (g₀ 0 0).val [MOD S] := (natCast_eq_iff_modEq _ _).1 hu₀
  have key := fun c v (hc : c < u) => fixedU_modEq_iff (v := v) hS hu huu₀ hdet hc
  have hmemA : ∀ c, c ∈ prog (a₃ * u) (b₃ * u) S₂ ((g₀ 0 1).val % S₂) ↔
      c ≡ (g₀ 0 1).val [MOD S₂] ∧ a₃ ≤ (c : ℝ) / u ∧ (c : ℝ) / u < b₃ := fun c => by
    rw [mem_prog hS₂ (Nat.mod_lt _ hS₂), le_div_iff₀ hu', div_lt_iff₀ hu']
    rfl
  have hmemB : ∀ v, v ∈ prog α β S₂ ((g₀ 1 0).val % S₂) ↔
      v ≡ (g₀ 1 0).val [MOD S₂] ∧ v ∈ Ico ⌈α⌉₊ ⌈β⌉₊ := fun v => by
    rw [mem_prog hS₂ (Nat.mod_lt _ hS₂), mem_Ico_ceil]
    rfl
  have hmat : ∀ v, !![(u : ZMod S), (rootC u v : ZMod S); (v : ZMod S), (rootD u v : ZMod S)] =
      g₀ ↔ rootC u v ≡ (g₀ 0 1).val [MOD S] ∧ v ≡ (g₀ 1 0).val [MOD S] ∧
        rootD u v ≡ (g₀ 1 1).val [MOD S] := fun v => by
    simp only [matrix_eq_iff, natCast_eq_iff_modEq]
    exact ⟨fun h => h.2, fun h => ⟨huu₀, h⟩⟩
  -- a point of the box gives a root, with `c = c(u, v)`
  have hback : ∀ p ∈ ({p ∈ prog (a₃ * u) (b₃ * u) S₂ ((g₀ 0 1).val % S₂) ×ˢ
      prog α β S₂ ((g₀ 1 0).val % S₂) | ((p.1 : ZMod (u * Nat.gcd u S)),
        (p.2 : ZMod (u * Nat.gcd u S))) ∈ fibreSet S u g₀} : Finset (ℕ × ℕ)),
      rootC u p.2 = p.1 ∧ p.2 ∈ ({v ∈ Ico ⌈α⌉₊ ⌈β⌉₊ | u.Coprime v ∧
        a₃ ≤ (rootC u v : ℝ) / u ∧ (rootC u v : ℝ) / u < b₃ ∧
        !![(u : ZMod S), (rootC u v : ZMod S); (v : ZMod S), (rootD u v : ZMod S)] = g₀} :
          Finset ℕ) := by
    rintro ⟨c, v⟩ hp
    obtain ⟨hp, hG⟩ := mem_filter.1 hp
    obtain ⟨hc, hv⟩ := mem_product.1 hp
    obtain ⟨hc₂, hc₁, hc₃⟩ := (hmemA c).1 hc
    obtain ⟨hv₂, hv⟩ := (hmemB v).1 hv
    obtain ⟨h₁, h₂⟩ := (mem_fibreSet_iff hu g₀ c v).1 hG
    have hcu : c < u := by
      have h := (div_lt_iff₀ hu').1 hc₃
      have : (c : ℝ) < u := by nlinarith
      exact_mod_cast this
    obtain ⟨huv, hroot, hvS, hcS, hd⟩ := (key c v hcu).1 ⟨h₁, h₂, hc₂, hv₂⟩
    refine ⟨hroot, mem_filter.2 ⟨hv, huv, ?_, ?_, (hmat v).2 ⟨hroot ▸ hcS, hvS, hd⟩⟩⟩
    · rw [hroot]; exact hc₁
    · rw [hroot]; exact hc₃
  refine card_nbij' (fun v => (rootC u v, v)) Prod.snd (fun v hv => ?_)
    (fun p hp => (hback p hp).2) (fun v _ => rfl) (fun p hp => ?_)
  · obtain ⟨hv, huv, hc₁, hc₃, hM⟩ := mem_filter.1 hv
    obtain ⟨hcS, hvS, hd⟩ := (hmat v).1 hM
    obtain ⟨h₁, h₂, h₃, h₄⟩ := (key (rootC u v) v (rootC_lt hu v)).2 ⟨huv, rfl, hvS, hcS, hd⟩
    refine mem_filter.2 ⟨mem_product.2 ⟨(hmemA _).2 ⟨h₃, hc₁, hc₃⟩, (hmemB v).2 ⟨h₄, hv⟩⟩,
      (mem_fibreSet_iff hu g₀ _ v).2 ⟨h₁, h₂⟩⟩
  · exact Prod.ext (hback p hp).1 rfl

/-- `u d₀ - 1` is a unit mod `u S₁`: `u² ≡ 0`, so `(u d₀ - 1)(-(u d₀ + 1)) = 1`. -/
theorem isUnit_mul_sub_one {S u : ℕ} [NeZero (u * Nat.gcd u S)] (d : ZMod (u * Nat.gcd u S)) :
    IsUnit ((u : ZMod (u * Nat.gcd u S)) * d - 1) := by
  have hsq : (u : ZMod (u * Nat.gcd u S)) * u = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact Nat.mul_dvd_mul_left u (Nat.gcd_dvd_left u S)
  refine (Units.mkOfMulEqOne _ (-((u : ZMod (u * Nat.gcd u S)) * d + 1)) ?_).isUnit
  linear_combination (-(d * d)) * hsq

/-- For a unit `a`, the equation `x y = a` has one solution `y` if `x` is a unit, else none. -/
theorem card_filter_mul_eq {n : ℕ} [NeZero n] {a : ZMod n} (ha : IsUnit a) (x : ZMod n) :
    #{y : ZMod n | x * y = a} = if IsUnit x then 1 else 0 := by
  split_ifs with hx
  · rw [card_eq_one]
    refine ⟨(hx.unit⁻¹ : (ZMod n)ˣ) * a, ?_⟩
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro rfl
      rw [← mul_assoc, hx.val_inv_mul, one_mul]
    · rintro rfl
      rw [← mul_assoc, hx.mul_val_inv, one_mul]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro y _ hxy
    exact hx (isUnit_of_mul_isUnit_left (hxy ▸ ha))

/-- The column count of the box identity: each admissible `c` has exactly one `v mod u S₁`,
so `Mc = #{c ∈ [a₃ u, b₃ u) : c ≡ c₀ (mod S), (c, u) = 1}`. -/
theorem card_fibreSet_column_eq {S u : ℕ} [NeZero S] (hS : Squarefree S)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (hu : 0 < u) (a₃ b₃ : ℝ)
    [NeZero (u * Nat.gcd u S)] :
    #{p ∈ prog (a₃ * u) (b₃ * u) (S / Nat.gcd u S) ((g₀ 0 1).val % (S / Nat.gcd u S)) ×ˢ
        (univ : Finset (ZMod (u * Nat.gcd u S))) |
        ((p.1 : ZMod (u * Nat.gcd u S)), p.2) ∈ fibreSet S u g₀} =
      #{c ∈ Ico ⌈a₃ * u⌉₊ ⌈b₃ * u⌉₊ | c ≡ (g₀ 0 1).val [MOD S] ∧ c.Coprime u} := by
  obtain ⟨hS₁₂, hcop, -⟩ := gcd_facts hS u
  set S₂ := S / Nat.gcd u S
  have hS₂ : 0 < S₂ := Nat.div_pos (Nat.le_of_dvd (NeZero.pos S) (Nat.gcd_dvd_right u S))
    (Nat.gcd_pos_of_pos_left S hu)
  have ha := isUnit_mul_sub_one (S := S) (u := u) ((g₀ 1 1).val : ZMod _)
  -- count the `y` over each `c`
  rw [card_filter, sum_product]
  simp only [← card_filter]
  have hcol : ∀ c : ℕ, #{y : ZMod (u * Nat.gcd u S) | ((c : ZMod _), y) ∈ fibreSet S u g₀} =
      if c.Coprime u ∧ c ≡ (g₀ 0 1).val [MOD Nat.gcd u S] then 1 else 0 := by
    intro c
    have hP : (u : ZMod (u * Nat.gcd u S)) * (c : ZMod (u * Nat.gcd u S)) =
        u * ((g₀ 0 1).val : ZMod (u * Nat.gcd u S)) ↔
        c ≡ (g₀ 0 1).val [MOD Nat.gcd u S] := by
      rw [← Nat.ModEq.mul_left_cancel_iff' hu.ne', ← ZMod.natCast_eq_natCast_iff]
      push_cast
      rfl
    have hunit : IsUnit (c : ZMod (u * Nat.gcd u S)) ↔ c.Coprime u := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right]
      exact ⟨fun h => h.1, fun h => ⟨h, h.coprime_dvd_right (Nat.gcd_dvd_left u S)⟩⟩
    simp only [fibreSet, hyperbola, mem_filter, mem_univ, true_and]
    rw [← filter_filter]
    by_cases hc : (u : ZMod (u * Nat.gcd u S)) * (c : ZMod (u * Nat.gcd u S)) =
        u * ((g₀ 0 1).val : ZMod (u * Nat.gcd u S))
    · rw [filter_true_of_mem fun _ _ => hc, card_filter_mul_eq ha]
      simp only [hunit, hP.1 hc, and_true]
    · rw [filter_false_of_mem fun _ _ => hc, card_empty]
      rw [ite_eq_right_iff.2 fun h => absurd (hP.2 h.2) hc]
  simp only [hcol]
  rw [sum_boole, Nat.cast_id]
  congr 1
  ext c
  have hcrt : ∀ a b : ℕ, a ≡ b [MOD S] ↔ a ≡ b [MOD Nat.gcd u S] ∧ a ≡ b [MOD S₂] :=
    fun a b => by rw [Nat.modEq_and_modEq_iff_modEq_mul hcop, hS₁₂]
  rw [mem_filter, mem_filter, mem_prog hS₂ (Nat.mod_lt _ hS₂), mem_Ico_ceil, hcrt]
  change (c ≡ (g₀ 0 1).val [MOD S₂] ∧ _) ∧ _ ↔ _
  tauto

/-- `c₀` is a unit mod `S₁ = (u, S)`: `S₁ ∣ u₀`, so `c₀ v₀ ≡ -1 (mod S₁)`. -/
theorem coprime_entry_gcd {S u : ℕ} [NeZero S] {g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)}
    (hg : g₀.det = 1) (hu₀ : (u : ZMod S) = g₀ 0 0) : (g₀ 0 1).val.Coprime (Nat.gcd u S) := by
  have hS₁S : Nat.gcd u S ∣ S := Nat.gcd_dvd_right u S
  have h₀ : (g₀ 0 0).val ≡ 0 [MOD Nat.gcd u S] :=
    (((natCast_eq_iff_modEq _ _).1 hu₀).of_dvd hS₁S).symm.trans
      (Nat.modEq_zero_iff_dvd.2 (Nat.gcd_dvd_left u S))
  have hcv : (g₀ 0 1).val * (g₀ 1 0).val + 1 ≡ 0 [MOD Nat.gcd u S] := by
    have := ((det_modEq hg).of_dvd hS₁S).symm.trans (h₀.mul_right _)
    rwa [zero_mul] at this
  refine Nat.coprime_comm.1 (Nat.eq_one_of_dvd_one ?_)
  have h₁ : Nat.gcd (Nat.gcd u S) (g₀ 0 1).val ∣ (g₀ 0 1).val * (g₀ 1 0).val + 1 :=
    (Nat.gcd_dvd_left _ _).trans (Nat.modEq_zero_iff_dvd.1 hcv)
  exact (Nat.dvd_add_right ((Nat.gcd_dvd_right _ _).mul_right _)).1 h₁

/-- `m^{3/4 + 1/100} τ(m) (2 + log m)² ≤ K m^{4/5}`, from `τ(m) ≤ D m^{1/100}` and
`log m ≤ 100 m^{1/100}`. -/
theorem rpow_mul_card_divisors_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, 1 ≤ m →
      (m : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) * m.divisors.card * (2 + Real.log m) ^ 2 ≤
        K * (m : ℝ) ^ (4 / 5 : ℝ) := by
  obtain ⟨D, hD⟩ := card_divisors_le_rpow (ε := 1 / 100) (by norm_num)
  have hD0 : 0 ≤ D := by
    have := hD 1 le_rfl
    simp only [Nat.divisors_one, card_singleton, Nat.cast_one, Real.one_rpow, mul_one] at this
    linarith
  refine ⟨D * 102 ^ 2, by positivity, fun m hm => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set e := (m : ℝ) ^ (1 / 100 : ℝ)
  have he1 : 1 ≤ e := Real.one_le_rpow hm1 (by norm_num)
  -- `2 + log m ≤ 102 m^{1/100}`
  have hlog : 2 + Real.log m ≤ 102 * e := by
    have := Real.log_le_rpow_div hm0.le (ε := 1 / 100) (by norm_num)
    have h' : (m : ℝ) ^ (1 / 100 : ℝ) / (1 / 100) = 100 * e := by simp only [e]; ring
    rw [h'] at this
    linarith
  have hlog0 : 0 ≤ 2 + Real.log m := by linarith [Real.log_nonneg hm1]
  calc (m : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) * m.divisors.card * (2 + Real.log m) ^ 2
      ≤ (m : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) * (D * e) * (102 * e) ^ 2 := by
        gcongr
        exact hD m hm
    _ = D * 102 ^ 2 * ((m : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) * e * e * e) := by ring
    _ = D * 102 ^ 2 * (m : ℝ) ^ (79 / 100 : ℝ) := by
        simp only [e, ← Real.rpow_add hm0]
        norm_num
    _ ≤ D * 102 ^ 2 * (m : ℝ) ^ (4 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num))
          (by positivity)

/-- **The count at fixed `u`.** For `u ≡ u₀ (mod S)`,
`fibreCount = (β - α)(b₃ - a₃) ∏_{p ∣ u, p ∤ S}(1 - 1/p) / S²
  + O((u S)^{4/5} + (β - α + 1) τ(u)/u + τ(u))`. The first error is the box bound with the
hyperbola sums, the others come from the column count and the length of the `v`-range. -/
theorem abs_fibreCount_sub_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : ℕ) [NeZero S], Squarefree S →
      ∀ g₀ : Matrix (Fin 2) (Fin 2) (ZMod S), g₀.det = 1 →
      ∀ u : ℕ, 0 < u → (u : ZMod S) = g₀ 0 0 →
      ∀ α β a₃ b₃ : ℝ, 0 ≤ α → α ≤ β → 0 ≤ a₃ → a₃ ≤ b₃ → b₃ ≤ 1 →
        |(fibreCount S g₀ α β a₃ b₃ u : ℝ) - (β - α) * (b₃ - a₃) * eulerFactor S u / S ^ 2| ≤
          K * ((u * S : ℝ) ^ (4 / 5 : ℝ) + (β - α + 1) * u.divisors.card / u +
            u.divisors.card) := by
  obtain ⟨C, hC0, hC⟩ := norm_pairSum_hyperbola_le
  obtain ⟨K₁, hK₁0, hK₁⟩ := rpow_mul_card_divisors_le
  refine ⟨C * K₁ + 1, by positivity, fun S _ hS g₀ hg u hu hu₀ α β a₃ b₃ hα hαβ ha₃ hab₃ hb₃ =>
    ?_⟩
  obtain ⟨hS₁₂, hcop, huS₂⟩ := gcd_facts hS u
  have hS₁ : 0 < Nat.gcd u S := Nat.gcd_pos_of_pos_left S hu
  have : NeZero (u * Nat.gcd u S) := ⟨(Nat.mul_pos hu hS₁).ne'⟩
  set S₁ := Nat.gcd u S
  set S₂ := S / S₁
  set m := u * S₁
  set r := (g₀ 0 1).val % S₂
  set r' := (g₀ 1 0).val % S₂
  have hS₂ : 0 < S₂ := Nat.div_pos (Nat.le_of_dvd (NeZero.pos S) (Nat.gcd_dvd_right u S)) hS₁
  have hu' : (0 : ℝ) < u := Nat.cast_pos.2 hu
  have hm : (u : ℝ) ≤ m := by
    simp only [m]; push_cast; nlinarith [(show (1 : ℝ) ≤ S₁ by exact_mod_cast hS₁)]
  -- the box bound
  have hq : IsUnit (S₂ : ZMod m) :=
    (ZMod.isUnit_iff_coprime _ _).2 (Nat.Coprime.mul_right huS₂.symm hcop.symm)
  have hAu : #(prog (a₃ * u) (b₃ * u) S₂ r) ≤ u := by
    refine (card_le_card fun c hc => ?_).trans (card_range u).le
    obtain ⟨-, -, hc₃⟩ := (mem_prog hS₂ (Nat.mod_lt _ hS₂)).1 hc
    have : (c : ℝ) < u := by nlinarith
    exact mem_range.2 (by exact_mod_cast this)
  have hA : ⌈(b₃ * u - r) / S₂⌉₊ - ⌈(a₃ * u - r) / S₂⌉₊ ≤ m := by
    have : #(prog (a₃ * u) (b₃ * u) S₂ r) = ⌈(b₃ * u - r) / S₂⌉₊ - ⌈(a₃ * u - r) / S₂⌉₊ := by
      rw [prog, card_image_of_injective _ fun i j hij => by simpa [hS₂.ne'] using hij,
        Nat.card_Ico]
    rw [← this]
    exact hAu.trans (Nat.le_mul_of_pos_right u hS₁)
  have hX : ∀ h k : ZMod m, k ≠ 0 → ‖pairSum (fibreSet S u g₀) h k‖ ≤
      C * (m : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) * Nat.gcd k.val m := fun h k _ =>
    hC m _ _ _ (isUnit_mul_sub_one _) h k
  have hbox : |(#{p ∈ prog (a₃ * u) (b₃ * u) S₂ r ×ˢ prog α β S₂ r' |
        ((p.1 : ZMod m), (p.2 : ZMod m)) ∈ fibreSet S u g₀} : ℝ) -
      (#(prog α β S₂ r') : ℝ) / m * #{p ∈ prog (a₃ * u) (b₃ * u) S₂ r ×ˢ (univ : Finset (ZMod m)) |
        ((p.1 : ZMod m), p.2) ∈ fibreSet S u g₀}| ≤
      C * (m : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) * m.divisors.card * (2 + Real.log m) ^ 2 :=
    abs_card_filter_mem_prog_sub_le _ hq hq r r' _ _ _ _ hA (by positivity) hX
  rw [← fibreCount_eq_card hS hg hu hu₀ hb₃, card_fibreSet_column_eq hS g₀ hu] at hbox
  set X := (fibreCount S g₀ α β a₃ b₃ u : ℝ)
  set Bc := (#(prog α β S₂ r') : ℝ)
  set Mc := (#{c ∈ Ico ⌈a₃ * u⌉₊ ⌈b₃ * u⌉₊ | c ≡ (g₀ 0 1).val [MOD S] ∧ c.Coprime u} : ℝ)
  set E := eulerFactor S u
  set T := (u.divisors.card : ℝ)
  set Y := (b₃ * u - a₃ * u) / S * E
  set Z := (β - α) / S₂
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast NeZero.one_le
  have hS₂1 : (1 : ℝ) ≤ S₂ := by exact_mod_cast hS₂
  have hT0 : 0 ≤ T := Nat.cast_nonneg _
  -- the three estimates
  have hbox' : |X - Bc / m * Mc| ≤ C * K₁ * (u * S : ℝ) ^ (4 / 5 : ℝ) := by
    refine hbox.trans ?_
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
    have hS₁S : (S₁ : ℝ) ≤ S := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos S) (Nat.gcd_dvd_right u S)
    have hmS : (m : ℝ) ≤ u * S := by
      simp only [m]; push_cast
      exact mul_le_mul_of_nonneg_left hS₁S hu'.le
    calc C * (m : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) * m.divisors.card * (2 + Real.log m) ^ 2
        = C * ((m : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) * m.divisors.card * (2 + Real.log m) ^ 2) := by
          ring
      _ ≤ C * (K₁ * (m : ℝ) ^ (4 / 5 : ℝ)) := mul_le_mul_of_nonneg_left (hK₁ m hm1) hC0
      _ ≤ C * (K₁ * (u * S : ℝ) ^ (4 / 5 : ℝ)) := by
          gcongr
      _ = _ := by ring
  have hB : |Bc - Z| ≤ 1 := abs_card_prog_sub_le hS₂ (Nat.mod_lt _ hS₂) hα hαβ
  have hM : |Mc - Y| ≤ T := abs_card_coprime_sub_le (by positivity) (by nlinarith)
    (NeZero.pos S) hu (coprime_entry_gcd hg hu₀)
  have hE : |E| ≤ T := abs_eulerFactor_le S u
  -- the main term is `Z Y / m`
  have hmain : (β - α) * (b₃ - a₃) * E / S ^ 2 = Z / m * Y := by
    have hS₁₂' : (S : ℝ) = S₁ * S₂ := by exact_mod_cast hS₁₂.symm
    have hS₁0 : (0 : ℝ) < S₁ := by exact_mod_cast hS₁
    simp only [Z, Y, m]
    rw [hS₁₂']
    push_cast
    field_simp
  have hsplit : X - Z / m * Y = (X - Bc / m * Mc) + Bc / m * (Mc - Y) + (Bc - Z) / m * Y := by
    ring
  have hBc : Bc ≤ β - α + 1 := by
    have h₁ : Z ≤ β - α := div_le_self (by linarith) hS₂1
    linarith [(abs_le.1 hB).2]
  have hm0 : (0 : ℝ) < m := hu'.trans_le hm
  have h₂ : |Bc / m * (Mc - Y)| ≤ (β - α + 1) * T / u := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Bc / m), mul_div_assoc]
    calc Bc / m * |Mc - Y| ≤ (β - α + 1) / u * T := by
          gcongr
      _ = (β - α + 1) * (T / u) := by ring
  have hY : |Y| ≤ u * T := by
    simp only [Y]
    rw [abs_mul, abs_div, abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ b₃ * u - a₃ * u),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ S)]
    calc (b₃ * u - a₃ * u) / S * |E| ≤ (u : ℝ) / 1 * T := by
          gcongr
          · nlinarith
      _ = u * T := by ring
  have h₃ : |(Bc - Z) / m * Y| ≤ T := by
    rw [abs_mul, abs_div, abs_of_pos hm0]
    calc |Bc - Z| / m * |Y| ≤ 1 / u * (u * T) := by gcongr
      _ = T := by field_simp
  rw [hmain, hsplit]
  have hrpow : 0 ≤ (u * S : ℝ) ^ (4 / 5 : ℝ) := by positivity
  have hterm : 0 ≤ (β - α + 1) * T / u := by
    have : 0 ≤ β - α + 1 := by linarith
    positivity
  calc |(X - Bc / m * Mc) + Bc / m * (Mc - Y) + (Bc - Z) / m * Y|
      ≤ |X - Bc / m * Mc| + |Bc / m * (Mc - Y)| + |(Bc - Z) / m * Y| := abs_add_three _ _ _
    _ ≤ C * K₁ * (u * S : ℝ) ^ (4 / 5 : ℝ) + (β - α + 1) * T / u + T := by
        linarith
    _ ≤ (C * K₁ + 1) * ((u * S : ℝ) ^ (4 / 5 : ℝ) + (β - α + 1) * T / u + T) := by
        nlinarith [mul_nonneg (mul_nonneg hC0 hK₁0) hterm, mul_nonneg (mul_nonneg hC0 hK₁0) hT0]

/-! ### Summing over `u` -/

/-- `n ∈ [⌈x⌉, ⌊y⌋]` with `n < y` exactly when `n ∈ [⌈x⌉, ⌈y⌉)`, for `y ≥ 0`. -/
theorem mem_Icc_and_lt_iff {x y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    (n ∈ Icc ⌈x⌉₊ ⌊y⌋₊ ∧ (n : ℝ) < y) ↔ n ∈ Ico ⌈x⌉₊ ⌈y⌉₊ := by
  rw [mem_Icc, mem_Ico, Nat.le_floor_iff hy, Nat.lt_ceil]
  constructor
  · rintro ⟨⟨h₁, -⟩, h₂⟩
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁, h₂.le⟩, h₂⟩

/-- `rootCount` is the sum of the fibres over `u ∈ [a₁ U, b₁ U)`, `u ≡ u₀ (mod S)`. -/
theorem rootCount_eq_sum_fibreCount {U V a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (hU : 0 ≤ b₁ * U)
    (hV : 0 ≤ b₂ * V) (S : ℕ) (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) :
    rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ S g₀ = ∑ u ∈ (Ico ⌈a₁ * U⌉₊ ⌈b₁ * U⌉₊ : Finset ℕ) with
      ((u : ℕ) : ZMod S) = g₀ 0 0, fibreCount S g₀ (a₂ * V) (b₂ * V) a₃ b₃ u := by
  -- the half-open box, then the fibres over `u`
  have hbox : rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ S g₀ =
      #{P ∈ Ico ⌈a₁ * U⌉₊ ⌈b₁ * U⌉₊ ×ˢ Ico ⌈a₂ * V⌉₊ ⌈b₂ * V⌉₊ | P.1.Coprime P.2 ∧
        a₃ ≤ (rootC P.1 P.2 : ℝ) / P.1 ∧ (rootC P.1 P.2 : ℝ) / P.1 < b₃ ∧
        !![(P.1 : ZMod S), (rootC P.1 P.2 : ZMod S); (P.2 : ZMod S), (rootD P.1 P.2 : ZMod S)] =
          g₀} := by
    rw [rootCount]
    congr 1
    ext ⟨u, v⟩
    simp only [mem_filter, mem_product, ← mem_Icc_and_lt_iff hU, ← mem_Icc_and_lt_iff hV]
    tauto
  rw [hbox, card_filter, sum_product, sum_filter]
  refine sum_congr rfl fun u _ => ?_
  rw [fibreCount, card_filter]
  split_ifs with hu
  · rfl
  · refine sum_eq_zero fun v _ => ?_
    rw [ite_eq_right_iff]
    rintro ⟨-, -, -, hM⟩
    exact absurd ((matrix_eq_iff _ _ _ _ _).1 hM).1 hu

/-- `x^p ≤ x` for `x ≥ 1` and `p ≤ 1`. -/
theorem rpow_le_self_of_one_le {x p : ℝ} (hx : 1 ≤ x) (hp : p ≤ 1) : x ^ p ≤ x := by
  simpa using Real.rpow_le_rpow_of_exponent_le hx hp

/-- `log(17 U) + 3 ≤ 25 U^{4/5}` for `U ≥ 1`. -/
theorem three_add_log_le {U : ℝ} (hU : 1 ≤ U) : 3 + Real.log (17 * U) ≤ 25 * U ^ (4 / 5 : ℝ) := by
  have hw : 1 ≤ U ^ (4 / 5 : ℝ) := Real.one_le_rpow hU (by norm_num)
  have h := Real.log_le_rpow_div (x := 17 * U) (by positivity) (ε := 4 / 5) (by norm_num)
  rw [Real.mul_rpow (by norm_num) (by linarith)] at h
  have h17 : (17 : ℝ) ^ (4 / 5 : ℝ) ≤ 17 := rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have : (17 : ℝ) ^ (4 / 5 : ℝ) * U ^ (4 / 5 : ℝ) / (4 / 5) ≤ 22 * U ^ (4 / 5 : ℝ) := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- **The root count with the coprime density** (PD Lemma 3.3 for `U ≤ V`, before the
density is identified): `rootCount = U V |I₁||I₂||I₃| ∑_{(l, S) = 1} μ(l)/l² / S³
  + O(U^{4/5} V S²)`. -/
theorem abs_rootCount_sub_coprimeDensity_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U V : ℝ, 2 ≤ U → U ≤ V → ∀ (S : ℕ) [NeZero S], Squarefree S →
      ∀ g₀ : Matrix (Fin 2) (Fin 2) (ZMod S), g₀.det = 1 → ∀ a₁ b₁ a₂ b₂ a₃ b₃ : ℝ,
      1 ≤ a₁ → a₁ ≤ b₁ → b₁ ≤ 16 → 1 ≤ a₂ → a₂ ≤ b₂ → b₂ ≤ 16 → 0 ≤ a₃ → a₃ ≤ b₃ → b₃ ≤ 1 →
        |(rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ S g₀ : ℝ) -
            U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) * coprimeDensity S / S ^ 3| ≤
          C * U ^ (4 / 5 : ℝ) * V * S ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := abs_fibreCount_sub_le
  obtain ⟨D, hD⟩ := card_divisors_le_rpow (ε := 1 / 100) (by norm_num)
  have hD0 : 0 ≤ D := by
    have := hD 1 le_rfl
    simp only [Nat.divisors_one, card_singleton, Nat.cast_one, Real.one_rpow, mul_one] at this
    linarith
  refine ⟨256 * K + 4096 * K * D + 256 * K * D + 400, by positivity, fun U V hU hUV S _ hS g₀ hg
    a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂ hb₂ ha₃ hab₃ hb₃ => ?_⟩
  have hU1 : 1 ≤ U := by linarith
  have hU0 : 0 < U := by linarith
  have hV1 : 1 ≤ V := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hb₁U16 : b₁ * U ≤ 16 * U := mul_le_mul_of_nonneg_right hb₁ hU0.le
  have ha₁U : U ≤ a₁ * U := le_mul_of_one_le_left hU0.le ha₁
  have hab₁U : a₁ * U ≤ b₁ * U := mul_le_mul_of_nonneg_right hab₁ hU0.le
  have hb₂V16 : b₂ * V ≤ 16 * V := mul_le_mul_of_nonneg_right hb₂ hV0
  have ha₂V : V ≤ a₂ * V := le_mul_of_one_le_left hV0 ha₂
  have hab₂V : a₂ * V ≤ b₂ * V := mul_le_mul_of_nonneg_right hab₂ hV0
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast NeZero.one_le
  set w := U ^ (4 / 5 : ℝ)
  set e := U ^ (1 / 100 : ℝ)
  have hw1 : 1 ≤ w := Real.one_le_rpow hU1 (by norm_num)
  have hew : e ≤ w := Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
  have he1 : 1 ≤ e := Real.one_le_rpow hU1 (by norm_num)
  set Us := ({u ∈ (Ico ⌈a₁ * U⌉₊ ⌈b₁ * U⌉₊ : Finset ℕ) | ((u : ℕ) : ZMod S) = g₀ 0 0} :
    Finset ℕ)
  set m : ℕ → ℝ := fun u => (b₂ * V - a₂ * V) * (b₃ - a₃) * eulerFactor S u / S ^ 2
  -- the uniform bound on the fibre errors
  set B := K * (16 * w * S + 256 * D * V * e / U + 16 * D * e)
  have hfib : ∀ u ∈ Us, |(fibreCount S g₀ (a₂ * V) (b₂ * V) a₃ b₃ u : ℝ) - m u| ≤ B := by
    intro u hu
    obtain ⟨hu, hu₀⟩ := mem_filter.1 hu
    obtain ⟨hu₁, hu₂⟩ := mem_Ico_ceil.1 hu
    have hUu : U ≤ u := ha₁U.trans hu₁
    have hu16 : (u : ℝ) ≤ 16 * U := hu₂.le.trans hb₁U16
    have hu0 : 0 < u := by exact_mod_cast hU0.trans_le hUu
    have h := hK S hS g₀ hg u hu0 hu₀ (a₂ * V) (b₂ * V) a₃ b₃ (by linarith) hab₂V ha₃
      hab₃ hb₃
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hK0)
    -- the divisor bound `τ(u) ≤ 16 D U^{1/100}`
    have hτ : (u.divisors.card : ℝ) ≤ 16 * D * e := by
      refine (hD u hu0).trans ?_
      calc D * (u : ℝ) ^ (1 / 100 : ℝ) ≤ D * (16 * U) ^ (1 / 100 : ℝ) := by gcongr
        _ = D * ((16 : ℝ) ^ (1 / 100 : ℝ) * e) := by rw [Real.mul_rpow (by norm_num) hU0.le]
        _ ≤ D * (16 * e) := by
            gcongr
            exact rpow_le_self_of_one_le (by norm_num) (by norm_num)
        _ = 16 * D * e := by ring
    have hτ0 : (0 : ℝ) ≤ u.divisors.card := Nat.cast_nonneg _
    have h₁ : (u * S : ℝ) ^ (4 / 5 : ℝ) ≤ 16 * w * S := by
      calc (u * S : ℝ) ^ (4 / 5 : ℝ) ≤ (16 * U * S) ^ (4 / 5 : ℝ) := by gcongr
        _ = (16 : ℝ) ^ (4 / 5 : ℝ) * w * (S : ℝ) ^ (4 / 5 : ℝ) := by
            rw [Real.mul_rpow (by positivity) (by positivity),
              Real.mul_rpow (by norm_num) hU0.le]
        _ ≤ 16 * w * S := by
            gcongr
            · exact rpow_le_self_of_one_le (by norm_num) (by norm_num)
            · exact rpow_le_self_of_one_le hS1 (by norm_num)
    have h₂ : (b₂ * V - a₂ * V + 1) * u.divisors.card / u ≤ 256 * D * V * e / U := by
      have hlen : b₂ * V - a₂ * V + 1 ≤ 16 * V := by linarith
      calc (b₂ * V - a₂ * V + 1) * u.divisors.card / u ≤ 16 * V * (16 * D * e) / U := by
            gcongr
        _ = 256 * D * V * e / U := by ring
    linarith
  -- the Euler average
  have hUs : Us = ({u ∈ (Ico ⌈a₁ * U⌉₊ ⌈b₁ * U⌉₊ : Finset ℕ) | u ≡ (g₀ 0 0).val [MOD S]} :
      Finset ℕ) := filter_congr fun u _ => natCast_eq_iff_modEq u _
  have hEul := abs_sum_eulerFactor_sub_le (α := a₁ * U) (β := b₁ * U) (by linarith)
    hab₁U (NeZero.pos S) (g₀ 0 0).val
  rw [← hUs] at hEul
  have hlog : 3 + Real.log (b₁ * U + 1) ≤ 25 * w := by
    refine le_trans ?_ (three_add_log_le hU1)
    have := Real.log_le_log (by linarith : 0 < b₁ * U + 1) (by linarith : b₁ * U + 1 ≤ 17 * U)
    linarith
  have hmsum : ∑ u ∈ Us, m u =
      (b₂ * V - a₂ * V) * (b₃ - a₃) / S ^ 2 * ∑ u ∈ Us, eulerFactor S u := by
    rw [mul_sum]
    exact sum_congr rfl fun u _ => by simp only [m]; ring
  have hmain : U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) * coprimeDensity S / S ^ 3 =
      (b₂ * V - a₂ * V) * (b₃ - a₃) / S ^ 2 * ((b₁ * U - a₁ * U) / S * coprimeDensity S) := by
    field_simp
  have hcoef0 : 0 ≤ (b₂ * V - a₂ * V) * (b₃ - a₃) / S ^ 2 := by
    have : 0 ≤ b₂ * V - a₂ * V := by linarith
    have : 0 ≤ b₃ - a₃ := by linarith
    positivity
  have hcoef : (b₂ * V - a₂ * V) * (b₃ - a₃) / S ^ 2 ≤ 15 * V := by
    have h₀ : 0 ≤ b₂ * V - a₂ * V := by linarith
    have h₁ : (b₂ * V - a₂ * V) * (b₃ - a₃) ≤ 15 * V * 1 :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
    rw [mul_one] at h₁
    exact (div_le_self (by positivity) (one_le_pow₀ hS1)).trans h₁
  -- the number of `u`
  have hcard : (#Us : ℝ) ≤ 16 * U := by
    have h₁ : (#Us : ℝ) ≤ ⌈b₁ * U⌉₊ - ⌈a₁ * U⌉₊ := by
      rw [← Nat.cast_sub (Nat.ceil_mono hab₁U), ← Nat.card_Ico]
      exact_mod_cast card_filter_le _ _
    have h₂ := Nat.ceil_lt_add_one (show 0 ≤ b₁ * U by linarith)
    have h₃ := Nat.le_ceil (a₁ * U)
    linarith
  have hb₁U : 0 ≤ b₁ * U := by linarith
  have hb₂V : 0 ≤ b₂ * V := by linarith
  rw [rootCount_eq_sum_fibreCount hb₁U hb₂V, hmain, Nat.cast_sum]
  have hsplit : ∑ u ∈ Us, ((fibreCount S g₀ (a₂ * V) (b₂ * V) a₃ b₃ u : ℕ) : ℝ) -
      (b₂ * V - a₂ * V) * (b₃ - a₃) / S ^ 2 * ((b₁ * U - a₁ * U) / S * coprimeDensity S) =
      ∑ u ∈ Us, ((fibreCount S g₀ (a₂ * V) (b₂ * V) a₃ b₃ u : ℝ) - m u) +
        (b₂ * V - a₂ * V) * (b₃ - a₃) / S ^ 2 *
          (∑ u ∈ Us, eulerFactor S u - (b₁ * U - a₁ * U) / S * coprimeDensity S) := by
    rw [sum_sub_distrib, hmsum]
    ring
  rw [hsplit]
  have hE₁ : |∑ u ∈ Us, ((fibreCount S g₀ (a₂ * V) (b₂ * V) a₃ b₃ u : ℝ) - m u)| ≤ 16 * U * B :=
    calc _ ≤ ∑ u ∈ Us, |(fibreCount S g₀ (a₂ * V) (b₂ * V) a₃ b₃ u : ℝ) - m u| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _u ∈ Us, B := sum_le_sum hfib
      _ = #Us * B := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 16 * U * B := by
          have : 0 ≤ B := by positivity
          gcongr
  have hE₂ : |(b₂ * V - a₂ * V) * (b₃ - a₃) / S ^ 2 *
      (∑ u ∈ Us, eulerFactor S u - (b₁ * U - a₁ * U) / S * coprimeDensity S)| ≤
        15 * V * (25 * w) := by
    rw [abs_mul, abs_of_nonneg hcoef0]
    exact mul_le_mul hcoef (hEul.trans hlog) (abs_nonneg _) (by positivity)
  -- compare each error with `U^{4/5} V S²`
  have hS2 : (S : ℝ) ≤ S ^ 2 := le_self_pow₀ hS1 two_ne_zero
  have hwV : 0 ≤ w * V := by positivity
  have hb₁ : 16 * U * B ≤ (256 * K + 4096 * K * D + 256 * K * D) * w * V * S ^ 2 := by
    have h₁ : 16 * U * B = K * (256 * U * w * S + 4096 * D * V * e + 256 * D * U * e) := by
      simp only [B]
      field_simp
      ring
    rw [h₁]
    have h₂ : U * w * S ≤ w * V * S ^ 2 := by
      calc U * w * S ≤ V * w * S ^ 2 := by gcongr
        _ = w * V * S ^ 2 := by ring
    have h₃ : V * e ≤ w * V * S ^ 2 := by
      calc V * e ≤ V * w * 1 := by rw [mul_one]; gcongr
        _ ≤ V * w * S ^ 2 := by gcongr; exact one_le_pow₀ hS1
        _ = w * V * S ^ 2 := by ring
    have h₄ : U * e ≤ w * V * S ^ 2 := by
      calc U * e ≤ V * w * 1 := by rw [mul_one]; gcongr
        _ ≤ V * w * S ^ 2 := by gcongr; exact one_le_pow₀ hS1
        _ = w * V * S ^ 2 := by ring
    have hKD : 0 ≤ K * D := mul_nonneg hK0 hD0
    have P₂ := mul_le_mul_of_nonneg_left h₂ hK0
    have P₃ := mul_le_mul_of_nonneg_left h₃ hKD
    have P₄ := mul_le_mul_of_nonneg_left h₄ hKD
    have e₁ : K * (256 * U * w * S + 4096 * D * V * e + 256 * D * U * e) =
        256 * (K * (U * w * S)) + 4096 * (K * D * (V * e)) + 256 * (K * D * (U * e)) := by ring
    have e₂ : (256 * K + 4096 * K * D + 256 * K * D) * w * V * S ^ 2 =
        256 * (K * (w * V * S ^ 2)) + 4096 * (K * D * (w * V * S ^ 2)) +
          256 * (K * D * (w * V * S ^ 2)) := by ring
    rw [e₁, e₂]
    linarith
  have hb₂ : 15 * V * (25 * w) ≤ 400 * w * V * S ^ 2 := by
    have : w * V ≤ w * V * S ^ 2 := le_mul_of_one_le_right hwV (one_le_pow₀ hS1)
    linarith
  calc _ ≤ |∑ u ∈ Us, ((fibreCount S g₀ (a₂ * V) (b₂ * V) a₃ b₃ u : ℝ) - m u)| +
        |(b₂ * V - a₂ * V) * (b₃ - a₃) / S ^ 2 *
          (∑ u ∈ Us, eulerFactor S u - (b₁ * U - a₁ * U) / S * coprimeDensity S)| :=
        abs_add_le _ _
    _ ≤ _ := by linarith

/-! ### The density -/

/-- `u d - c v = 1` in `ZMod S` for a primitive `(u, v)`. -/
theorem det_root_matrix {S u v : ℕ} (hu : 0 < u) (huv : u.Coprime v) :
    (!![(u : ZMod S), (rootC u v : ZMod S); (v : ZMod S), (rootD u v : ZMod S)]).det = 1 := by
  have h := congrArg (fun n : ℕ => (n : ZMod S)) (mul_rootD hu huv)
  push_cast at h
  rw [Matrix.det_fin_two_of]
  linear_combination h

/-- Each primitive root lies over exactly one `g₀ ∈ SL₂(ℤ/S)`, so the counts over all `g₀` add
up to the count without congruence condition (`S = 1`). -/
theorem sum_rootCount_eq {U V a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (ha₁ : 0 < a₁ * U) (S : ℕ) [NeZero S]
    (g₁ : Matrix (Fin 2) (Fin 2) (ZMod 1)) :
    ∑ g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
        rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ S g₀ = rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ 1 g₁ := by
  set box := Icc ⌈a₁ * U⌉₊ ⌊b₁ * U⌋₊ ×ˢ Icc ⌈a₂ * V⌉₊ ⌊b₂ * V⌋₊
  set M : ℕ × ℕ → Matrix (Fin 2) (Fin 2) (ZMod S) := fun P =>
    !![(P.1 : ZMod S), (rootC P.1 P.2 : ZMod S); (P.2 : ZMod S), (rootD P.1 P.2 : ZMod S)]
  set f : ℕ × ℕ → Matrix.SpecialLinearGroup (Fin 2) (ZMod S) := fun P =>
    if h : (M P).det = 1 then ⟨M P, h⟩ else 1
  set Q : ℕ × ℕ → Prop := fun P => P.1.Coprime P.2 ∧ (P.1 : ℝ) < b₁ * U ∧ (P.2 : ℝ) < b₂ * V ∧
    a₃ ≤ (rootC P.1 P.2 : ℝ) / P.1 ∧ (rootC P.1 P.2 : ℝ) / P.1 < b₃
  -- on the box, `M P ∈ SL₂`
  have hdet : ∀ P ∈ box, Q P → (M P).det = 1 := by
    intro P hP hQ
    have h₁ : ⌈a₁ * U⌉₊ ≤ P.1 := (mem_Icc.1 (mem_product.1 hP).1).1
    have h₂ : 0 < ⌈a₁ * U⌉₊ := Nat.ceil_pos.2 ha₁
    exact det_root_matrix (h₂.trans_le h₁) hQ.1
  have h₁ : rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ 1 g₁ = #{P ∈ box | Q P} := by
    rw [rootCount]
    congr 1
    refine filter_congr fun P _ => ?_
    simp only [Q, Subsingleton.elim _ g₁, and_true]
  rw [h₁, card_eq_sum_card_fiberwise (f := f) (t := univ) fun _ _ => mem_univ _]
  refine sum_congr rfl fun g₀ _ => ?_
  rw [rootCount, filter_filter]
  congr 1
  refine filter_congr fun P hP => ?_
  simp only [Q]
  constructor
  · rintro ⟨huv, h₁, h₂, h₃, h₄, hM⟩
    refine ⟨⟨huv, h₁, h₂, h₃, h₄⟩, ?_⟩
    have hd := hdet P hP ⟨huv, h₁, h₂, h₃, h₄⟩
    simp only [f, hd, ↓reduceDIte]
    exact Subtype.ext hM
  · rintro ⟨⟨huv, h₁, h₂, h₃, h₄⟩, hf⟩
    have hd := hdet P hP ⟨huv, h₁, h₂, h₃, h₄⟩
    simp only [f, hd, ↓reduceDIte] at hf
    exact ⟨huv, h₁, h₂, h₃, h₄, congrArg Subtype.val hf⟩

/-- A number with `|a| N ≤ K` for all `N ≥ 2` vanishes. -/
theorem eq_zero_of_abs_mul_le {a K : ℝ} (h : ∀ N : ℕ, 2 ≤ N → |a| * N ≤ K) : a = 0 := by
  by_contra ha
  have ha' : 0 < |a| := abs_pos.2 ha
  obtain ⟨N, hN⟩ := exists_nat_gt (max 2 (K / |a|))
  have h₁ := h N (by exact_mod_cast (le_max_left _ _).trans hN.le)
  have h₂ : K / |a| < N := (le_max_right _ _).trans_lt hN
  rw [div_lt_iff₀ ha'] at h₂
  linarith

/-- **The density.** `∑_{(l, S) = 1} μ(l)/l² / S³ = c₂ / |SL₂(ℤ/S)|`. Summing the root count
over `g₀ ∈ SL₂(ℤ/S)` gives the count for `S = 1`; comparing the two main terms at
`U = V = N⁵ → ∞` identifies the constants. -/
theorem coprimeDensity_div_eq (S : ℕ) [NeZero S] (hS : Squarefree S) :
    coprimeDensity S / (S : ℝ) ^ 3 =
      primitiveDensity / Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) := by
  obtain ⟨C, hC0, hC⟩ := abs_rootCount_sub_coprimeDensity_le
  set n := (Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)
  have hn : 0 < n := Nat.cast_pos.2 Fintype.card_pos
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast NeZero.one_le
  have hσ₁ : coprimeDensity 1 = primitiveDensity := by
    simp [coprimeDensity, densityTerm, primitiveDensity]
  -- `a = n σ_S / S³ - σ₁` satisfies `|a| N ≤ C (n S² + 1)`
  have hzero : n * (coprimeDensity S / (S : ℝ) ^ 3) - coprimeDensity 1 = 0 := by
    refine eq_zero_of_abs_mul_le (K := C * (n * S ^ 2 + 1)) fun N hN => ?_
    set U := (N : ℝ) ^ 5
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hU2 : 2 ≤ U := by
      calc (2 : ℝ) ≤ N := hN2
        _ ≤ (N : ℝ) ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
    have hUw : U ^ (4 / 5 : ℝ) * U = (N : ℝ) ^ 9 := by
      simp only [U]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
      ring
    have hcount := sum_rootCount_eq (U := U) (V := U) (a₁ := 1) (b₁ := 2) (a₂ := 1) (b₂ := 2)
      (a₃ := 0) (b₃ := 1) (by linarith) S (1 : Matrix (Fin 2) (Fin 2) (ZMod 1))
    have h₁ := hC U U hU2 le_rfl 1 squarefree_one 1 Matrix.det_one 1 2 1 2 0 1 le_rfl
      (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) le_rfl (by norm_num) le_rfl
    have hg : ∀ g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
        |(rootCount U U 1 2 1 2 0 1 S g₀ : ℝ) - U * U * coprimeDensity S / S ^ 3| ≤
          C * U ^ (4 / 5 : ℝ) * U * S ^ 2 := fun g₀ => by
      have := hC U U hU2 le_rfl S hS g₀ g₀.2 1 2 1 2 0 1 le_rfl (by norm_num) (by norm_num)
        le_rfl (by norm_num) (by norm_num) le_rfl (by norm_num) le_rfl
      norm_num at this ⊢
      exact this
    norm_num at h₁
    -- sum the errors over `g₀`
    have hsum : |(∑ g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
        (rootCount U U 1 2 1 2 0 1 S g₀ : ℝ)) - n * (U * U * coprimeDensity S / S ^ 3)| ≤
          n * (C * U ^ (4 / 5 : ℝ) * U * S ^ 2) := by
      have : n * (U * U * coprimeDensity S / S ^ 3) = ∑ _g₀ : Matrix.SpecialLinearGroup (Fin 2)
          (ZMod S), U * U * coprimeDensity S / S ^ 3 := by
        rw [sum_const, card_univ, nsmul_eq_mul]
      rw [this, ← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine (sum_le_sum fun g₀ _ => hg g₀).trans ?_
      rw [sum_const, card_univ, nsmul_eq_mul]
    rw [← Nat.cast_sum, hcount] at hsum
    set a := n * (coprimeDensity S / (S : ℝ) ^ 3) - coprimeDensity 1
    set R := (rootCount U U 1 2 1 2 0 1 1 1 : ℝ)
    have hUU : U * U = (N : ℝ) ^ 9 * N := by simp only [U]; ring
    have hN0 : (0 : ℝ) < (N : ℝ) ^ 9 := by positivity
    -- `|a| U² ≤ C (n S² + 1) U^{9/5}`
    have key : |a| * (U * U) ≤ C * (n * S ^ 2 + 1) * (U ^ (4 / 5 : ℝ) * U) := by
      have e : a * (U * U) = (R - U * U * coprimeDensity 1) -
          (R - n * (U * U * coprimeDensity S / S ^ 3)) := by
        simp only [a]
        ring
      rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ U * U), ← abs_mul, e]
      refine (abs_sub _ _).trans ?_
      have : C * (n * S ^ 2 + 1) * (U ^ (4 / 5 : ℝ) * U) =
          C * U ^ (4 / 5 : ℝ) * U + n * (C * U ^ (4 / 5 : ℝ) * U * S ^ 2) := by ring
      rw [this]
      exact add_le_add h₁ hsum
    rw [hUw, hUU] at key
    have : |a| * N * (N : ℝ) ^ 9 ≤ C * (n * S ^ 2 + 1) * (N : ℝ) ^ 9 := by
      calc |a| * N * (N : ℝ) ^ 9 = |a| * ((N : ℝ) ^ 9 * N) := by ring
        _ ≤ _ := key
    exact le_of_mul_le_mul_right this hN0
  have := hzero
  rw [hσ₁, sub_eq_zero] at this
  field_simp
  rw [← this]
  field_simp

/-- **PD Lemma 3.3 for `U ≤ V`**: `rootCount = c₂ U V |I₁||I₂||I₃| / |SL₂(ℤ/S)| +
O(U^{4/5} V S²)`, for intervals in `[1, 16] × [1, 16] × [0, 1]`. -/
theorem abs_rootCount_sub_le_of_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U V : ℝ, 2 ≤ U → U ≤ V → ∀ (S : ℕ) [NeZero S], Squarefree S →
      ∀ (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (a₁ b₁ a₂ b₂ a₃ b₃ : ℝ),
      1 ≤ a₁ → a₁ ≤ b₁ → b₁ ≤ 16 → 1 ≤ a₂ → a₂ ≤ b₂ → b₂ ≤ 16 → 0 ≤ a₃ → a₃ ≤ b₃ → b₃ ≤ 1 →
        |(rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ S g₀ : ℝ) -
            primitiveDensity * U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) /
              Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S))| ≤
          C * U ^ (4 / 5 : ℝ) * V * S ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := abs_rootCount_sub_coprimeDensity_le
  refine ⟨C, hC0, fun U V hU hUV S _ hS g₀ a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂ hb₂ ha₃ hab₃
    hb₃ => ?_⟩
  have h := hC U V hU hUV S hS g₀ g₀.2 a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂ hb₂ ha₃ hab₃ hb₃
  have hmain : U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) * coprimeDensity S / (S : ℝ) ^ 3 =
      primitiveDensity * U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) /
        Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) := by
    rw [mul_div_assoc, coprimeDensity_div_eq S hS]
    ring
  rwa [hmain] at h

/-- `|c₂| ≤ 2`. -/
theorem abs_primitiveDensity_le : |primitiveDensity| ≤ 2 := by
  have h := abs_coprimeDensity_sub_le 1 one_pos
  simp only [range_one, sum_singleton, densityTerm, Nat.cast_zero, ArithmeticFunction.map_zero,
    Int.cast_zero, zero_div, ite_self, sub_zero, Nat.cast_one, div_one] at h
  have hσ : coprimeDensity 1 = primitiveDensity := by
    simp [coprimeDensity, densityTerm, primitiveDensity]
  rwa [hσ] at h

/-! ### Swapping the coordinates -/

/-- The end of PD's proof of Lemma 3.3: the completion of `(v, u)` is `c' = v - d`,
`d' = u - c`, for `u ≥ 1` and `v ≥ 2`. -/
theorem rootC_rootD_swap {u v : ℕ} (hu : 0 < u) (hv : 2 ≤ v) (huv : u.Coprime v) :
    rootD u v ≤ v ∧ rootC v u = v - rootD u v ∧ rootD v u = u - rootC u v := by
  have hud := mul_rootD hu huv
  have hc := rootC_lt hu v
  set c := rootC u v
  set d := rootD u v
  -- `d < v`, from `u d = 1 + v c ≤ 1 + v (u - 1) < u v`
  have hdv : d < v := by
    by_contra h
    push Not at h
    have h₁ : u * v ≤ u * d := Nat.mul_le_mul_left u h
    have h₂ : v * c ≤ v * (u - 1) := Nat.mul_le_mul_left v (by omega)
    have h₃ : v * (u - 1) + v = u * v := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hu, mul_comm]
    omega
  have hkey : (v - d) * u + 1 = v * (u - c) := by
    zify [hdv.le, hc.le]
    have : ((u * d : ℕ) : ℤ) = ((1 + v * c : ℕ) : ℤ) := by rw [hud]
    push_cast at this
    linear_combination -this
  obtain ⟨-, hroot⟩ := rootC_eq_of_dvd (Nat.sub_lt (by omega) (by
    by_contra h; push Not at h
    have : d = 0 := by omega
    rw [this, mul_zero] at hud; omega)) ⟨u - c, hkey⟩
  refine ⟨hdv.le, hroot, ?_⟩
  have h₁ := mul_rootD (by omega) huv.symm
  rw [hroot, mul_comm u, add_comm, hkey] at h₁
  exact Nat.eq_of_mul_eq_mul_left (by omega) h₁

/-- The swapped residue class `g₀' = (v₀, v₀ - d₀; u₀, u₀ - c₀) ∈ SL₂(ℤ/S)`. -/
def swapSL {S : ℕ} (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod S) :=
  ⟨!![(g : Matrix (Fin 2) (Fin 2) (ZMod S)) 1 0, g 1 0 - g 1 1; g 0 0, g 0 0 - g 0 1], by
    have h := g.2
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

/-- `g(v, u) ≡ g₀' (mod S)` exactly when `g(u, v) ≡ g₀ (mod S)`. -/
theorem matrix_swap_iff {S u v : ℕ} (hu : 0 < u) (hv : 2 ≤ v) (huv : u.Coprime v)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) :
    !![(v : ZMod S), (rootC v u : ZMod S); (u : ZMod S), (rootD v u : ZMod S)] = swapSL g ↔
      !![(u : ZMod S), (rootC u v : ZMod S); (v : ZMod S), (rootD u v : ZMod S)] = g := by
  obtain ⟨hdv, hc', hd'⟩ := rootC_rootD_swap hu hv huv
  have hc : rootC u v ≤ u := (rootC_lt hu v).le
  rw [matrix_eq_iff, matrix_eq_iff, hc', hd', Nat.cast_sub hdv, Nat.cast_sub hc]
  simp only [swapSL, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₃, by linear_combination h₃ - h₄, h₁, by linear_combination h₁ - h₂⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₃, by rw [h₃, h₄], h₁, by rw [h₁, h₂]⟩

/-- `c'/v = 1 - c/u - 1/(u v)` for the swapped completion. -/
theorem rootC_swap_div {u v : ℕ} (hu : 0 < u) (hv : 2 ≤ v) (huv : u.Coprime v) :
    (rootC v u : ℝ) / v = 1 - (rootC u v : ℝ) / u - 1 / (u * v) := by
  obtain ⟨hdv, hc', -⟩ := rootC_rootD_swap hu hv huv
  have hud := congrArg (fun n : ℕ => (n : ℝ)) (mul_rootD hu huv)
  push_cast at hud
  have hu' : (0 : ℝ) < u := Nat.cast_pos.2 hu
  have hv' : (0 : ℝ) < v := by exact_mod_cast (by omega : 0 < v)
  rw [hc', Nat.cast_sub hdv]
  field_simp
  linear_combination (-1 : ℝ) * hud

/-- The coordinates of a point counted by `rootCount` with `a₁, a₂ ≥ 1`, `U > 0`, `V ≥ 2`:
`u ≥ U`, `u ≥ 1`, `v ≥ V` and `v ≥ 2`. -/
theorem bounds_of_mem_box {U V a₁ b₁ a₂ b₂ : ℝ} (hU : 0 < U) (hV : 2 ≤ V) (ha₁ : 1 ≤ a₁)
    (ha₂ : 1 ≤ a₂) {P : ℕ × ℕ} (hP : P ∈ Icc ⌈a₁ * U⌉₊ ⌊b₁ * U⌋₊ ×ˢ Icc ⌈a₂ * V⌉₊ ⌊b₂ * V⌋₊) :
    U ≤ P.1 ∧ 0 < P.1 ∧ V ≤ P.2 ∧ 2 ≤ P.2 := by
  obtain ⟨h₁, h₂⟩ := mem_product.1 hP
  have hu : U ≤ P.1 := (le_mul_of_one_le_left hU.le ha₁).trans
    (Nat.ceil_le.1 (mem_Icc.1 h₁).1)
  have hv : V ≤ P.2 := (le_mul_of_one_le_left (by linarith) ha₂).trans
    (Nat.ceil_le.1 (mem_Icc.1 h₂).1)
  refine ⟨hu, by exact_mod_cast hU.trans_le hu, hv, by exact_mod_cast hV.trans hv⟩

/-- Upper count after the swap: `c/u ∈ [a₃, b₃)` gives
`c'/v ∈ [max(0, 1 - b₃ - 1/(U V)), 1 - a₃)`. -/
theorem rootCount_le_swap {U V a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (hU : 0 < U) (hV : 2 ≤ V) (ha₁ : 1 ≤ a₁)
    (ha₂ : 1 ≤ a₂) (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) :
    rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ S g₀ ≤
      rootCount V U a₂ b₂ a₁ b₁ (max 0 (1 - b₃ - 1 / (U * V))) (1 - a₃) S (swapSL g₀) := by
  refine card_le_card_of_injOn Prod.swap (fun P hP => ?_) Prod.swap_injective.injOn
  obtain ⟨hP, huv, hu, hv, h₁, h₂, hM⟩ := mem_filter.1 hP
  obtain ⟨hUu, hu0, hVv, hv2⟩ := bounds_of_mem_box hU hV ha₁ ha₂ hP
  have hswap := rootC_swap_div hu0 hv2 huv
  have huv' : U * V ≤ P.1 * P.2 := mul_le_mul hUu hVv (by linarith) (Nat.cast_nonneg _)
  have hinv : 1 / ((P.1 : ℝ) * P.2) ≤ 1 / (U * V) :=
    one_div_le_one_div_of_le (by positivity) huv'
  have hinv0 : 0 < 1 / ((P.1 : ℝ) * P.2) := by
    have : (0 : ℝ) < P.2 := by exact_mod_cast (by omega : 0 < P.2)
    have : (0 : ℝ) < P.1 := by exact_mod_cast hu0
    positivity
  refine mem_filter.2 ⟨mem_product.2 ⟨(mem_product.1 hP).2, (mem_product.1 hP).1⟩, huv.symm, hv,
    hu, ?_, ?_, (matrix_swap_iff hu0 hv2 huv g₀).2 hM⟩
  · refine max_le (by positivity) ?_
    change 1 - b₃ - 1 / (U * V) ≤ (rootC P.2 P.1 : ℝ) / P.2
    rw [hswap]
    linarith
  · change (rootC P.2 P.1 : ℝ) / P.2 < 1 - a₃
    rw [hswap]
    linarith

/-- Lower count after the swap: `c'/v ∈ [1 - b₃, max(1 - b₃, 1 - a₃ - 1/(U V)))` gives
`c/u ∈ [a₃, b₃)`. -/
theorem swap_le_rootCount {U V a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (hU : 0 < U) (hV : 2 ≤ V)
    (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) :
    rootCount V U a₂ b₂ a₁ b₁ (1 - b₃) (max (1 - b₃) (1 - a₃ - 1 / (U * V))) S (swapSL g₀) ≤
      rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ S g₀ := by
  refine card_le_card_of_injOn Prod.swap (fun P hP => ?_) Prod.swap_injective.injOn
  obtain ⟨hP, hvu, hv, hu, h₁, h₂, hM⟩ := mem_filter.1 hP
  have hP' : P.swap ∈ Icc ⌈a₁ * U⌉₊ ⌊b₁ * U⌋₊ ×ˢ Icc ⌈a₂ * V⌉₊ ⌊b₂ * V⌋₊ :=
    mem_product.2 ⟨(mem_product.1 hP).2, (mem_product.1 hP).1⟩
  obtain ⟨hUu, hu0, hVv, hv2⟩ := bounds_of_mem_box hU hV ha₁ ha₂ hP'
  have huv : P.2.Coprime P.1 := hvu.symm
  have hswap := rootC_swap_div hu0 hv2 huv
  simp only [Prod.fst_swap, Prod.snd_swap] at hUu hu0 hVv hv2 hswap
  have huv' : U * V ≤ P.2 * P.1 := mul_le_mul hUu hVv (by linarith) (Nat.cast_nonneg _)
  have hinv : 1 / ((P.2 : ℝ) * P.1) ≤ 1 / (U * V) :=
    one_div_le_one_div_of_le (by positivity) huv'
  have hinv0 : 0 < 1 / ((P.2 : ℝ) * P.1) := by
    have : (0 : ℝ) < P.1 := by exact_mod_cast (by omega : 0 < P.1)
    have : (0 : ℝ) < P.2 := by exact_mod_cast hu0
    positivity
  change 1 - b₃ ≤ (rootC P.1 P.2 : ℝ) / P.1 at h₁
  change (rootC P.1 P.2 : ℝ) / P.1 < max (1 - b₃) (1 - a₃ - 1 / (U * V)) at h₂
  rw [hswap] at h₁ h₂
  have h₂' : 1 - (rootC P.2 P.1 : ℝ) / P.2 - 1 / (P.2 * P.1) < 1 - a₃ - 1 / (U * V) := by
    rcases lt_max_iff.1 h₂ with h | h
    · linarith
    · exact h
  refine mem_filter.2 ⟨hP', huv, hu, hv, ?_, ?_, (matrix_swap_iff hu0 hv2 huv g₀).1 hM⟩
  · change a₃ ≤ (rootC P.2 P.1 : ℝ) / P.2
    linarith
  · change (rootC P.2 P.1 : ℝ) / P.2 < b₃
    linarith

/-- Moving the third interval by `O(1/(U V))` moves the main term by at most `30`. -/
theorem abs_main_sub_le {c₂ n U V Δ₁ Δ₂ x y : ℝ} (hc : |c₂| ≤ 2) (hn : 1 ≤ n) (hU : 0 < U)
    (hV : 0 < V) (h₁ : 0 ≤ Δ₁) (h₁' : Δ₁ ≤ 15) (h₂ : 0 ≤ Δ₂) (h₂' : Δ₂ ≤ 1)
    (hxy : |x - y| ≤ 1 / (U * V)) :
    |c₂ * V * U * Δ₂ * Δ₁ * x / n - c₂ * U * V * Δ₁ * Δ₂ * y / n| ≤ 30 := by
  have hUV : 0 < U * V := mul_pos hU hV
  have h₃ : |U * V * (x - y)| ≤ 1 := by
    rw [abs_mul, abs_of_pos hUV]
    calc U * V * |x - y| ≤ U * V * (1 / (U * V)) := by gcongr
      _ = 1 := by field_simp
  rw [show c₂ * V * U * Δ₂ * Δ₁ * x / n - c₂ * U * V * Δ₁ * Δ₂ * y / n =
      c₂ * Δ₁ * Δ₂ * (U * V * (x - y)) / n by ring, abs_div, abs_of_pos (by linarith : 0 < n),
    abs_mul, abs_mul, abs_mul, abs_of_nonneg h₁, abs_of_nonneg h₂]
  calc |c₂| * Δ₁ * Δ₂ * |U * V * (x - y)| / n ≤ |c₂| * Δ₁ * Δ₂ * |U * V * (x - y)| :=
        div_le_self (by positivity) hn
    _ ≤ 2 * 15 * 1 * 1 := by gcongr
    _ = 30 := by norm_num

/-- `x^{4/5} = x · x^{-1/5}` for `x > 0`. -/
theorem rpow_four_fifths {x : ℝ} (hx : 0 < x) : x ^ (4 / 5 : ℝ) = x * x ^ (-(1 / 5 : ℝ)) := by
  rw [← Real.rpow_one_add' hx.le (by norm_num)]
  norm_num

end RootResidue

/-- PD Lemma 3.3: for `U, V ≥ 2`, squarefree `S` with `S² ≤ min(U, V)^{1/100}`, any
`g₀ ∈ SL₂(ℤ/S)` and intervals inside `[1, 16] × [1, 2] × [0, 1]`,
`rootCount = c₂ UV |I₁||I₂||I₃| / |SL₂(ℤ/S)| + O(UV S² min(U, V)^{-1/5})`. -/
theorem abs_rootCount_sub_le : ∃ C₀ : ℝ, ∀ (U V : ℝ), 2 ≤ U → 2 ≤ V →
    ∀ (S : ℕ) [NeZero S], Squarefree S →
    ∀ (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (a₁ b₁ a₂ b₂ a₃ b₃ : ℝ),
      1 ≤ a₁ → a₁ ≤ b₁ → b₁ ≤ 16 → 1 ≤ a₂ → a₂ ≤ b₂ → b₂ ≤ 2 → 0 ≤ a₃ → a₃ ≤ b₃ → b₃ ≤ 1 →
      |(rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ S g₀ : ℝ) -
          primitiveDensity * U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) /
            Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S))| ≤
        C₀ * U * V * (S : ℝ) ^ 2 * min U V ^ (-(1 / 5 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := RootResidue.abs_rootCount_sub_le_of_le
  refine ⟨C + 30, fun U V hU hV S _ hS g₀ a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂ hb₂ ha₃
    hab₃ hb₃ => ?_⟩
  set n := (Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)
  have hn : 1 ≤ n := Nat.one_le_cast.2 Fintype.card_pos
  have hS1 : (1 : ℝ) ≤ (S : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast NeZero.one_le)
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < V := by linarith
  rcases le_total U V with hUV | hVU
  · -- `U ≤ V`: the bound as proved
    have h := hC U V hU hUV S hS g₀ a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂ (by linarith) ha₃
      hab₃ hb₃
    rw [min_eq_left hUV]
    refine h.trans (le_of_eq_of_le (by rw [RootResidue.rpow_four_fifths hU0]) ?_)
    have : 0 ≤ U * V * (S : ℝ) ^ 2 * U ^ (-(1 / 5 : ℝ)) := by positivity
    nlinarith
  · -- `V ≤ U`: swap the coordinates, with the third interval moved by `1/(U V)`
    set δ := 1 / (U * V)
    have hδ : 0 < δ := by positivity
    have hout := hC V U hV hVU S hS (RootResidue.swapSL g₀) a₂ b₂ a₁ b₁ (max 0 (1 - b₃ - δ))
      (1 - a₃) ha₂ hab₂ (by linarith) ha₁ hab₁ hb₁ (le_max_left _ _)
      (max_le (by linarith) (by linarith)) (by linarith)
    have hin := hC V U hV hVU S hS (RootResidue.swapSL g₀) a₂ b₂ a₁ b₁ (1 - b₃)
      (max (1 - b₃) (1 - a₃ - δ)) ha₂ hab₂ (by linarith) ha₁ hab₁ hb₁ (by linarith)
      (le_max_left _ _) (max_le (by linarith) (by linarith))
    have hle := RootResidue.rootCount_le_swap (a₃ := a₃) (b₃ := b₃) (b₁ := b₁) (b₂ := b₂) hU0 hV
      ha₁ ha₂ S g₀
    have hge := RootResidue.swap_le_rootCount (a₃ := a₃) (b₃ := b₃) (b₁ := b₁) (b₂ := b₂) hU0 hV
      ha₁ ha₂ S g₀
    -- the moved intervals have lengths within `δ` of `b₃ - a₃`
    have hJout : |((1 - a₃) - max 0 (1 - b₃ - δ)) - (b₃ - a₃)| ≤ δ := by
      rcases le_total 0 (1 - b₃ - δ) with h | h
      · rw [max_eq_right h, abs_le]; constructor <;> linarith
      · rw [max_eq_left h, abs_le]; constructor <;> linarith
    have hJin : |(max (1 - b₃) (1 - a₃ - δ) - (1 - b₃)) - (b₃ - a₃)| ≤ δ := by
      rcases le_total (1 - b₃) (1 - a₃ - δ) with h | h
      · rw [max_eq_right h, abs_le]; constructor <;> linarith
      · rw [max_eq_left h, abs_le]; constructor <;> linarith
    have hmout := RootResidue.abs_main_sub_le RootResidue.abs_primitiveDensity_le hn hU0 hV0
      (by linarith : 0 ≤ b₁ - a₁) (by linarith) (by linarith : 0 ≤ b₂ - a₂) (by linarith) hJout
    have hmin := RootResidue.abs_main_sub_le RootResidue.abs_primitiveDensity_le hn hU0 hV0
      (by linarith : 0 ≤ b₁ - a₁) (by linarith) (by linarith : 0 ≤ b₂ - a₂) (by linarith) hJin
    have hle' : (rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ S g₀ : ℝ) ≤
        rootCount V U a₂ b₂ a₁ b₁ (max 0 (1 - b₃ - δ)) (1 - a₃) S (RootResidue.swapSL g₀) := by
      exact_mod_cast hle
    have hge' : (rootCount V U a₂ b₂ a₁ b₁ (1 - b₃) (max (1 - b₃) (1 - a₃ - δ)) S
        (RootResidue.swapSL g₀) : ℝ) ≤ rootCount U V a₁ b₁ a₂ b₂ a₃ b₃ S g₀ := by
      exact_mod_cast hge
    rw [min_eq_right hVU]
    have hE : C * V ^ (4 / 5 : ℝ) * U * (S : ℝ) ^ 2 + 30 ≤
        (C + 30) * U * V * (S : ℝ) ^ 2 * V ^ (-(1 / 5 : ℝ)) := by
      have hw : 1 ≤ V ^ (4 / 5 : ℝ) * U := by
        have : 1 ≤ V ^ (4 / 5 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
        nlinarith
      have e : (C + 30) * U * V * (S : ℝ) ^ 2 * V ^ (-(1 / 5 : ℝ)) =
          (C + 30) * (V ^ (4 / 5 : ℝ) * U) * (S : ℝ) ^ 2 := by
        rw [RootResidue.rpow_four_fifths hV0]; ring
      rw [e]
      have : 0 ≤ C * (V ^ (4 / 5 : ℝ) * U) * (S : ℝ) ^ 2 := by positivity
      nlinarith
    rw [abs_le] at hout hin hmout hmin ⊢
    constructor <;> nlinarith

end Erdos408.OneSided
