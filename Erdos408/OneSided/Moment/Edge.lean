import Erdos408.OneSided.Moment.Chain
import Erdos408.OneSided.Moment.Edge.Measure
import Erdos408.OneSided.Moment.Edge.Clean
import Erdos408.OneSided.Moment.Edge.DirtyRaw
import Erdos408.OneSided.Moment.Edge.DirtyComp

/-!
# The signed edge bound

M5–M9 of `blueprint/one_sided_type_ii.md` §5.5 and §16 (PD §4, `mem:clean-bound`,
`mem:raw-dirty-norm`, `mem:comparison-small`, `mem:signed-edge`). The edge coefficient is
`w(s, c) ([t - b + a = 0] - ∫_𝔐 e(θ(t - b + a)))` with a real amplitude `w = edgeAmp`. Split the
edge choices by the set `S` of stored groups and the set `I` of promoted groups:

* the *clean* piece `S = I = ∅` keeps both kernel terms, whose difference is the minor-arc
  integral `∫_{𝕋 ∖ 𝔐}`, and has norm at most `L^{-G - 1/2}` (M6, by the lattice shape M5 and
  the bilinear Gram bound);
* each *dirty* piece is split into its raw part `w [t - b + a = 0]` and its comparison part
  `-w ∫_𝔐`, each of norm at most `L^{-G - 1}`: the raw parts by the second good-state test
  and the anchor congruence (M7, needs `K ≥ K₀`), the comparison parts by the line count
  (M8).

There are at most `4^K` dirty pieces, so `‖ℰ‖ ≤ L^{-G}` (`eventually_chainEdge_normLe_of_parts`,
which gives M9 in `Moment/Phased.lean`).
-/

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

section Parts

variable (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

variable {x d Y d₀ u v r B} in
/-- The kernel shift `t - b + a` of an edge, with `t = det/D`. -/
def edgeShift (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℤ :=
  edgeDet s c / edgePad s c - (∏ i, edgeSrc s c i (Fin.last _) : ℕ) + (∏ i, (c.2.2.2.1 i).1 : ℕ)

open scoped Classical in
/-- The real amplitude of the edge coefficient: everything but the kernel
`[t - b + a = 0] - ∫_𝔐 e(θ(t - b + a))`; zero unless the choice is admissible. -/
def edgeAmp (N : ℕ) (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℝ :=
  if EdgeValid x d Y d₀ u v r B s c then
    ((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
      pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
      pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
      (∏ i, if (c.2.2.2.1 i).2 then
        (∑ xp : Particle x d, if xp.1 = edgePromoted c i then (s.2.2.1 xp : ℝ) else 0) /
          primeMass x d (c.2.2.2.1 i).1
      else primeWeight q x d N (c.2.2.2.1 i).1) *
      (d₀ / edgePad s c) * dyadicBump ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y) *
      dyadicBump ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y) * plateau ((edgeDet s c / edgePad s c : ℤ) / Y))
  else 0

/-- The edge coefficient is the amplitude times the kernel. -/
theorem chainEdgeCoef_eq (N : ℕ) (s : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r) :
    chainEdgeCoef q A₀ x d Y d₀ u v r B N s c =
      (edgeAmp q x d Y d₀ u v r B N s c : ℂ) *
        ((if edgeShift s c = 0 then 1 else 0) - arcIntegral A₀ x Y (edgeShift s c)) := by
  unfold chainEdgeCoef edgeAmp edgeShift
  by_cases hv : EdgeValid x d Y d₀ u v r B s c
  · -- `t = b - a ↔ t - b + a = 0`
    have hk : ∀ t b a : ℤ, (t = b - a) = (t - b + a = 0) := fun t b a => propext (by omega)
    simp only [hv, ↓reduceIte, hk]
  · simp [hv]

/-- The edge choices with stored groups `S` and promoted groups `I`. -/
def edgePartChoices (S I : Finset (Fin K)) : Finset (EdgeChoice x d Y d₀ u v r) :=
  (edgeChoices x d Y d₀ u v r).filter fun c =>
    c.2.1 = S ∧ univ.filter (fun i => (c.2.2.2.1 i).2 = true) = I

/-- The clean edge: no stores and no promotions, with the full kernel. -/
def edgeClean (N : ℕ) :
    (ChainState x d Y d₀ u v r B → ℂ) → ChainState x d Y d₀ u v r B → ℂ :=
  choiceOp (edgePartChoices x d Y d₀ u v r ∅ ∅) (chainEdgeCoef q A₀ x d Y d₀ u v r B N)
    (chainEdgeOut x d Y d₀ u v r B)

/-- The raw part `w [t - b + a = 0]` of the edge piece `(S, I)`. -/
def edgeRaw (N : ℕ) (S I : Finset (Fin K)) :
    (ChainState x d Y d₀ u v r B → ℂ) → ChainState x d Y d₀ u v r B → ℂ :=
  choiceOp (edgePartChoices x d Y d₀ u v r S I)
    (fun s c => (edgeAmp q x d Y d₀ u v r B N s c : ℂ) * if edgeShift s c = 0 then 1 else 0)
    (chainEdgeOut x d Y d₀ u v r B)

/-- The comparison part `-w ∫_𝔐 e(θ(t - b + a))` of the edge piece `(S, I)`. -/
def edgeComp (N : ℕ) (S I : Finset (Fin K)) :
    (ChainState x d Y d₀ u v r B → ℂ) → ChainState x d Y d₀ u v r B → ℂ :=
  choiceOp (edgePartChoices x d Y d₀ u v r S I)
    (fun s c => -((edgeAmp q x d Y d₀ u v r B N s c : ℂ) * arcIntegral A₀ x Y (edgeShift s c)))
    (chainEdgeOut x d Y d₀ u v r B)

/-- The edge is the clean edge plus the raw and comparison parts of the dirty pieces. -/
theorem chainEdge_eq_parts (N : ℕ) (f : ChainState x d Y d₀ u v r B → ℂ) :
    chainEdge q A₀ x d Y d₀ u v r B N f =
      edgeClean q A₀ x d Y d₀ u v r B N f +
        ∑ SI ∈ (univ : Finset (Finset (Fin K) × Finset (Fin K))).erase (∅, ∅),
          (edgeRaw q x d Y d₀ u v r B N SI.1 SI.2 f +
            edgeComp q A₀ x d Y d₀ u v r B N SI.1 SI.2 f) := by
  classical
  funext s
  -- regroup the choices by their stored and promoted groups
  have hfib : chainEdge q A₀ x d Y d₀ u v r B N f s =
      ∑ SI : Finset (Fin K) × Finset (Fin K), ∑ c ∈ edgePartChoices x d Y d₀ u v r SI.1 SI.2,
        chainEdgeCoef q A₀ x d Y d₀ u v r B N s c * f (chainEdgeOut x d Y d₀ u v r B s c) := by
    rw [chainEdge, choiceOp, ← sum_fiberwise (edgeChoices x d Y d₀ u v r)
      (fun c => (c.2.1, univ.filter fun i => (c.2.2.2.1 i).2 = true))]
    refine sum_congr rfl fun SI _ => ?_
    rw [edgePartChoices, filter_congr fun c _ => Prod.ext_iff]
  -- the clean piece keeps the full kernel; each dirty piece splits into raw and comparison
  rw [hfib, ← add_sum_erase _ _ (mem_univ (∅, ∅))]
  simp only [Pi.add_apply, Finset.sum_apply]
  congr 1
  refine sum_congr rfl fun SI _ => ?_
  simp only [edgeRaw, edgeComp, choiceOp, ← sum_add_distrib]
  refine sum_congr rfl fun c _ => ?_
  rw [chainEdgeCoef_eq]
  ring

end Parts

/-- The weighted square norm is the square of a Euclidean norm, with weights `√μ`. -/
theorem wnormSq_eq_norm_sq {ι : Type*} [Fintype ι] {μ : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i)
    (g : ι → ℂ) :
    wnormSq μ g =
      ‖(WithLp.toLp 2 fun i => (Real.sqrt (μ i) : ℂ) * g i : EuclideanSpace ℂ ι)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, wnormSq]
  refine sum_congr rfl fun i _ => ?_
  rw [PiLp.toLp_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (hμ i)]

/-- Norm bounds add (Minkowski): `‖∑_k T_k f‖ ≤ ∑_k c_k ‖f‖`. -/
theorem NormLe.sum {ι κ γ : Type*} [Fintype ι] [Fintype κ] {μ : ι → ℝ} {ν : κ → ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (s : Finset γ) {T : γ → (κ → ℂ) → ι → ℂ} {c : γ → ℝ}
    (hc : ∀ k ∈ s, 0 ≤ c k) (hT : ∀ k ∈ s, NormLe μ ν (T k) (c k)) :
    NormLe μ ν (fun f => ∑ k ∈ s, T k f) (∑ k ∈ s, c k) := by
  intro f
  set φ : (ι → ℂ) → EuclideanSpace ℂ ι :=
    fun g => WithLp.toLp 2 fun i => (Real.sqrt (μ i) : ℂ) * g i with hφ
  -- each piece has Euclidean norm at most `c_k ‖f‖_ν`
  have hk : ∀ k ∈ s, ‖φ (T k f)‖ ≤ c k * Real.sqrt (wnormSq ν f) := by
    intro k hk
    rw [← Real.sqrt_sq (norm_nonneg _), hφ, ← wnormSq_eq_norm_sq hμ, ← Real.sqrt_sq (hc k hk),
      ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (hT k hk f)
  -- the embedding is additive, so Minkowski is the triangle inequality
  have hsum : ‖φ (∑ k ∈ s, T k f)‖ ≤ (∑ k ∈ s, c k) * Real.sqrt (wnormSq ν f) := by
    have : φ (∑ k ∈ s, T k f) = ∑ k ∈ s, φ (T k f) := by
      rw [hφ, ← WithLp.toLp_sum]
      refine congrArg (WithLp.toLp 2) (funext fun i => ?_)
      simp [Finset.sum_apply, Finset.mul_sum]
    rw [this, Finset.sum_mul]
    exact (norm_sum_le _ _).trans (sum_le_sum hk)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hsum 2
  rw [hφ, ← wnormSq_eq_norm_sq hμ, mul_pow] at hsq
  by_cases hW : 0 ≤ wnormSq ν f
  · rwa [Real.sq_sqrt hW] at hsq
  · -- a negative `‖f‖²_ν` forces every `c_k = 0`
    push Not at hW
    have hc0 : ∀ k ∈ s, c k = 0 := by
      intro k hk
      have h0 : 0 ≤ c k ^ 2 * wnormSq ν f :=
        (sum_nonneg fun i _ => mul_nonneg (hμ i) (sq_nonneg _)).trans (hT k hk f)
      have : c k ^ 2 ≤ 0 := nonpos_of_mul_nonneg_left h0 hW
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
    rw [sum_eq_zero hc0] at hsq ⊢
    simpa using hsq

/-- Norm bounds add: `‖(S + T) f‖ ≤ (a + b) ‖f‖`. -/
theorem NormLe.add {ι κ : Type*} [Fintype ι] [Fintype κ] {μ : ι → ℝ} {ν : κ → ℝ}
    (hμ : ∀ i, 0 ≤ μ i) {S T : (κ → ℂ) → ι → ℂ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hS : NormLe μ ν S a) (hT : NormLe μ ν T b) :
    NormLe μ ν (fun f => S f + T f) (a + b) := by
  have h := NormLe.sum hμ (univ : Finset Bool) (T := fun k => bif k then S else T)
    (c := fun k => bif k then a else b) (fun k _ => by cases k <;> assumption)
    (fun k _ => by cases k <;> assumption)
  simpa [Fintype.sum_bool] using h

/-- A norm bound can be raised, for a nonnegative input measure. -/
theorem NormLe.mono {ι κ : Type*} [Fintype ι] [Fintype κ] {μ : ι → ℝ} {ν : κ → ℝ}
    (hν : ∀ j, 0 ≤ ν j) {T : (κ → ℂ) → ι → ℂ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hT : NormLe μ ν T a) : NormLe μ ν T b := fun f =>
  (hT f).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 2)
    (sum_nonneg fun j _ => mul_nonneg (hν j) (sq_nonneg _)))

/-- M6, the clean edge: for `B ≤ L³`, its norm is at most `L^{-G - 1/2}`, uniformly in the root
box. -/
theorem eventually_edgeClean_normLe {q C CX alo ahi Dstar g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (hC : 0 < C) (hD : 0 < Dstar) (hCX : 1 ≤ CX) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5)
    (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∀ u v r : ℝ, (2 : ℝ) ^ k * 2 ^ j * d.Hm ≤ u → u ≤ 16 * ((2 : ℝ) ^ k * 2 ^ j * d.Hm) →
        d.Hn ≤ v → v ≤ 2 * d.Hn → 0 ≤ r → r ≤ 1 →
      ∀ B N : ℕ, (B : ℝ) ≤ Real.log x ^ 3 → N = 2 * momentPower x →
        NormLe (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (edgeClean q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B N)
          (Real.log x ^ (-(edgePrec Dstar C + 1 / 2))) :=
  eventually_cleanOp_normLe hq hq₁ hC hD hCX halo hahi hg

/-- M7, the dirty raw parts: for `K ≥ K₀` and `B ≤ L³`, each has norm at most `L^{-G - 1}`. -/
theorem eventually_edgeRaw_normLe {q C CX alo ahi Dstar g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (hC : 0 < C) (hD : 0 < Dstar) (halo : 1 / 10 < alo) (hK : bandThreshold Dstar C ≤ K)
    (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∀ u v r : ℝ, (2 : ℝ) ^ k * 2 ^ j * d.Hm ≤ u → u ≤ 16 * ((2 : ℝ) ^ k * 2 ^ j * d.Hm) →
        d.Hn ≤ v → v ≤ 2 * d.Hn → 0 ≤ r → r ≤ 1 →
      ∀ B N : ℕ, (B : ℝ) ≤ Real.log x ^ 3 → N = 2 * momentPower x →
      ∀ S I : Finset (Fin K), (S, I) ≠ (∅, ∅) →
        NormLe (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (edgeRaw q x d (2 ^ j) (2 ^ k) u v r B N S I)
          (Real.log x ^ (-(edgePrec Dstar C + 1))) := by
  -- the raw part is the choice operator of `rawCoef` on the piece (`Moment/Edge/DirtyRaw.lean`)
  filter_upwards [eventually_rawChoiceOp_normLe (CX := CX) (ahi := ahi) hq hq₁ hC hD halo hK hg]
    with x hx d hd j k u v r hu _ _ _ _ _ B N hB hN S I hSI
  exact hx d hd j k u v r hu B N hB hN S I hSI

/-- M8, the dirty comparison parts: for `B ≤ L³`, each has norm at most `L^{-G - 1}`. -/
theorem eventually_edgeComp_normLe {q C CX alo ahi Dstar g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (halo : 1 / 10 < alo) (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∀ u v r : ℝ, (2 : ℝ) ^ k * 2 ^ j * d.Hm ≤ u → u ≤ 16 * ((2 : ℝ) ^ k * 2 ^ j * d.Hm) →
        d.Hn ≤ v → v ≤ 2 * d.Hn → 0 ≤ r → r ≤ 1 →
      ∀ B N : ℕ, (B : ℝ) ≤ Real.log x ^ 3 → N = 2 * momentPower x →
      ∀ S I : Finset (Fin K), (S, I) ≠ (∅, ∅) →
        NormLe (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (edgeComp q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B N S I)
          (Real.log x ^ (-(edgePrec Dstar C + 1))) := by
  -- `edgeComp` is `compOp` of `Moment/Edge/DirtyComp.lean`, with `Y = 2^j ≥ 1`, `d₀ = 2^k > 0`
  filter_upwards [eventually_compOp_normLe (K := K) (C := C) (CX := CX) (ahi := ahi)
    (A₀ := arcExp Dstar C) (G := edgePrec Dstar C) hq hq₁ halo hg]
    with x hx d hd j k u v r _ _ _ _ _ _ B N hB hN S I hSI
  subst hN
  exact hx d hd (2 ^ j) (2 ^ k) u v r B (one_le_pow₀ (by norm_num)) (by positivity) hB S I hSI

/-- The final comparison: for `M` dirty pieces, eventually
`L^{-G - 1/2} + M · 2 L^{-G - 1} ≤ L^{-G}`, since `L^{-1/2} ≤ 1/2` and `2M L^{-1} ≤ 1/2`. -/
private theorem eventually_edgeParts_le (G M : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ (-(G + 1 / 2)) + M * (2 * Real.log x ^ (-(G + 1))) ≤
      Real.log x ^ (-G) := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (max 4 (4 * M))] with x hL
  set L := Real.log x with hLdef
  have hL4 : 4 ≤ L := le_of_max_le_left hL
  have hLM : 4 * M ≤ L := le_of_max_le_right hL
  have hL0 : 0 < L := by linarith
  -- `L^{-1/2} ≤ 1/2`, as `√L ≥ 2`
  have hhalf : L ^ (-(1 / 2 : ℝ)) ≤ 1 / 2 := by
    have h2 : 2 ≤ L ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le (by linarith)
    rw [Real.rpow_neg hL0.le]
    calc (L ^ (1 / 2 : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
      _ = 1 / 2 := by norm_num
  -- `M L^{-1} ≤ 1/4`
  have hone : M * L ^ (-1 : ℝ) ≤ 1 / 4 := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ hL0]
    linarith
  rw [neg_add, Real.rpow_add hL0, neg_add, Real.rpow_add hL0]
  calc L ^ (-G) * L ^ (-(1 / 2 : ℝ)) + M * (2 * (L ^ (-G) * L ^ (-1 : ℝ)))
      = L ^ (-G) * (L ^ (-(1 / 2 : ℝ)) + 2 * (M * L ^ (-1 : ℝ))) := by ring
    _ ≤ L ^ (-G) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hL0.le _)
    _ = L ^ (-G) := mul_one _

/-- M9 from M6–M8: for `K ≥ K₀` and `B ≤ L³`, the edge has norm at most `L^{-G}`. Split it by
`chainEdge_eq_parts` into the clean edge and the raw and comparison parts of the `4^K - 1`
dirty pieces, and add their bounds by Minkowski. -/
theorem eventually_chainEdge_normLe_of_parts {q C CX alo ahi Dstar g : ℝ} (hq : 0 < q)
    (hq₁ : q < 1) (hC : 0 < C) (hD : 0 < Dstar) (hCX : 1 ≤ CX) (halo : 1 / 10 < alo)
    (hahi : ahi < 1 / 5) (hK : bandThreshold Dstar C ≤ K) (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∀ u v r : ℝ, (2 : ℝ) ^ k * 2 ^ j * d.Hm ≤ u → u ≤ 16 * ((2 : ℝ) ^ k * 2 ^ j * d.Hm) →
        d.Hn ≤ v → v ≤ 2 * d.Hn → 0 ≤ r → r ≤ 1 →
      ∀ B N : ℕ, (B : ℝ) ≤ Real.log x ^ 3 → N = 2 * momentPower x →
        NormLe (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (chainEdge q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B N)
          (Real.log x ^ (-edgePrec Dstar C)) := by
  set G := edgePrec Dstar C
  set dirty := (univ : Finset (Finset (Fin K) × Finset (Fin K))).erase (∅, ∅)
  filter_upwards [eventually_edgeClean_normLe hq hq₁ hC hD hCX halo hahi hg,
    eventually_edgeRaw_normLe (CX := CX) (ahi := ahi) hq hq₁ hC hD halo hK hg,
    eventually_edgeComp_normLe (C := C) (CX := CX) (ahi := ahi) (Dstar := Dstar) hq hq₁ halo hg,
    eventually_chainMeasure_nonneg (C := C) (CX := CX) (ahi := ahi) (g := g) hq halo,
    eventually_edgeParts_le G dirty.card,
    Real.tendsto_log_atTop.eventually_ge_atTop 0]
    with x hclean hraw hcomp hμ hfin hL d hd j k u v r hu₁ hu₂ hv₁ hv₂ hr₀ hr₁ B N hB hN
  have hμ' := hμ d hd (2 ^ j) (2 ^ k) u v r B
  subst hN
  have hc₁ : 0 ≤ Real.log x ^ (-(G + 1)) := Real.rpow_nonneg hL _
  -- each dirty piece has norm at most `2 L^{-G - 1}`
  have hdirty : ∀ SI ∈ dirty, NormLe (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B _ s)
      (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B _ s)
      (fun f => edgeRaw q x d (2 ^ j) (2 ^ k) u v r B _ SI.1 SI.2 f +
        edgeComp q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B _ SI.1 SI.2 f)
      (Real.log x ^ (-(G + 1)) + Real.log x ^ (-(G + 1))) := fun SI hSI =>
    NormLe.add hμ' hc₁ hc₁
      (hraw d hd j k u v r hu₁ hu₂ hv₁ hv₂ hr₀ hr₁ B _ hB rfl SI.1 SI.2 (ne_of_mem_erase hSI))
      (hcomp d hd j k u v r hu₁ hu₂ hv₁ hv₂ hr₀ hr₁ B _ hB rfl SI.1 SI.2 (ne_of_mem_erase hSI))
  -- add the clean edge and the dirty pieces by Minkowski
  have hsum := NormLe.add hμ' (Real.rpow_nonneg hL _)
    (sum_nonneg fun SI _ => add_nonneg hc₁ hc₁)
    (hclean d hd j k u v r hu₁ hu₂ hv₁ hv₂ hr₀ hr₁ B _ hB rfl)
    (NormLe.sum hμ' dirty (fun SI _ => add_nonneg hc₁ hc₁) hdirty)
  rw [sum_const, nsmul_eq_mul, ← two_mul] at hsum
  rw [show chainEdge q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B (2 * momentPower x) =
      fun f => _ from funext (chainEdge_eq_parts q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B _)]
  exact NormLe.mono hμ' (add_nonneg (Real.rpow_nonneg hL _)
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg zero_le_two hc₁))) hfin hsum

end Erdos408.OneSided
