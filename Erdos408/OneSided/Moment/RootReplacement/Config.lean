module

public import Erdos408.OneSided.Moment.PathExpansion

/-!
# Configurations: the path expansion over a root-independent index set

RR2 of `blueprint/one_sided_type_ii.md` §15, in the form used by the root replacement. The
fixed-line path expansion `rootMoment_eq_sum_lineFactor` sums over paths of states of
`freeRootModel` at the root `ϱ = (u, v, r)`, whose positions depend on `ϱ`. All of them lie
in the square `|z₁|, |z₂| ≤ rootBound U V`, which depends only on `U = d₀ Y H_m` and
`V = H_n`. A *configuration* is a path of `N + 1` states over this square
(`squareModel`). Then

`rootMoment(ϱ, ℓ) = ∑_ω c(ω) · A(ω, ϱ) · ∏_p λ_p(ω, ℓ_p)`  (`rootMoment_eq_sum_conf`),

where

* `confCoeff` is the root-independent coefficient `c(ω)`: the state mass, the endpoint
  condition `z₀ = z_N = e₁`, and the kernel `𝒮 𝒯 𝒮` at `q = 1` along the path;
* `confInd` is the archimedean indicator `A(ω, ϱ)`: every visit is a position at `ϱ`
  (the box) and passes both good-state tests at the transported ratio `τ(w_z)/τ(z)`;
* `confLineFactor` is the line factor `λ_p`, as `lineFactor`.

The primes of the lists along `ω` are `confActive ω`; at every other band prime the line
factor is the damping `∏_j (1 - η'_j [ℓ = [z_j]_p])`.

The line-free states at `ϱ` include into the square states (`toSquare`), onto the states at a
position at `ϱ`. Along the inclusion, the line-free edge operator is `g (𝒮 𝒯 𝒮) g`, with `g`
the visit indicator (`freeRootModel_edgeOp_eq`), so the weight of a path is `c(ω) A(ω, ϱ)`
up to the mass and endpoint condition (`pathWeight_eq_prod_confKernel`). The configurations
with a visit off the positions at `ϱ` have `A(ω, ϱ) = 0`.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset Real
open scoped Matrix

variable {K : ℕ}

/-- The square `|z₁|, |z₂| ≤ rootBound U V`, which contains the positions at every root. -/
def rootSquare (U V : ℝ) : Finset (ℤ × ℤ) :=
  Icc (-(rootBound U V : ℤ)) (rootBound U V) ×ˢ Icc (-(rootBound U V : ℤ)) (rootBound U V)

/-- The square model: the points of `rootSquare`, with every prime dividing. Its ratio is
never used. -/
def squareModel (d : Data K) (Y d₀ : ℝ) : PosModel where
  Pos := ↥(rootSquare (d₀ * Y * d.Hm) d.Hn)
  det z z' := z.1.1 * z'.1.2 - z.1.2 * z'.1.1
  FirstDvd _ _ := True
  ratio _ := 0

/-- The configurations: paths of `N + 1` states of the square model, `N = 2R`. -/
abbrev Conf (x : ℝ) (d : Data K) (Y d₀ : ℝ) :=
  Fin (2 * momentPower x + 1) → (squareModel d Y d₀).State x d

/-- The root-free kernel `𝒮 𝒯 𝒮` of the square model at `q = 1`. -/
def confKernel (A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) :
    Matrix ((squareModel d Y d₀).State x d) ((squareModel d Y d₀).State x d) ℂ :=
  (squareModel d Y d₀).symOp x d * (squareModel d Y d₀).rowOp 1 A₀ x d Y d₀ *
    (squareModel d Y d₀).symOp x d

/-- The coefficient `c(ω)`: the state mass, the endpoint condition `z₀ = z_N = e₁`, and the
kernel `𝒮 𝒯 𝒮` along the path. It does not depend on the root. -/
def confCoeff (A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) (ω : Conf x d Y d₀) : ℂ :=
  (stateMass x d : ℂ) *
    (if (ω 0).1.1.1 = (1, 0) ∧ (ω (Fin.last _)).1.1.1 = (1, 0) then 1 else 0) *
    ∏ j : Fin (2 * momentPower x), confKernel A₀ x d Y d₀ (ω j.castSucc) (ω j.succ)

/-- The transported ratio `τ(w_z)/τ(z)` at the ratio `r`, the ratio of `rootModel`. -/
def rootRatioAt (r : ℝ) (z : ℤ × ℤ) : ℝ := tau r (complement z) / tau r z

open scoped Classical in
/-- The indicator of one visit at the root `ϱ = (u, v, r)`: the point is a position at `ϱ`
and the state passes both good-state tests at the transported ratio. -/
def visitInd (x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (s : (squareModel d Y d₀).State x d) : ℝ :=
  if s.1.1.1 ∈ rootPositions (d₀ * Y * d.Hm) d.Hn u v r ∧
      GoodFirst Y d₀ (rootRatioAt r s.1.1.1) s.1.2 ∧
      GoodSecond x d d₀ (rootRatioAt r s.1.1.1) s.1.2 then 1
  else 0

/-- The archimedean indicator `A(ω, ϱ)`: the product of the visit indicators. -/
def confInd (x : ℝ) (d : Data K) (Y d₀ : ℝ) (ω : Conf x d Y d₀) (u v r : ℝ) : ℝ :=
  ∏ j, visitInd x d Y d₀ u v r (ω j)

/-- The lines `[z_j]_p` along a configuration, extended by `0` past the end. -/
def confLines {x : ℝ} {d : Data K} {Y d₀ : ℝ} (p : ℕ) (ω : Conf x d Y d₀) (j : ℕ) : ℕ :=
  if h : j < 2 * momentPower x + 1 then lineOf p (ω ⟨j, h⟩).1.1.1 else 0

/-- The line factor `λ_p(ω, l)` of a configuration, as `lineFactor`:
`∏_{j active} [l = [z_j]_p] ∏_{j inactive} (1 - η'_j [l = [z_j]_p])`. -/
def confLineFactor {x : ℝ} {d : Data K} {Y d₀ : ℝ} (q : ℝ) (p : ℕ) (ω : Conf x d Y d₀)
    (l : ℕ) : ℝ :=
  (∏ j ∈ activeSet p ω, if l = confLines p ω j then 1 else 0) *
    ∏ j ∈ (range (2 * momentPower x + 1)).filter (· ∉ activeSet p ω),
      (1 - dampDefect q (2 * momentPower x) j * if l = confLines p ω j then 1 else 0)

/-- The primes in the lists along a configuration. -/
def confActive {x : ℝ} {d : Data K} {Y d₀ : ℝ} (ω : Conf x d Y d₀) : Finset ℕ :=
  univ.biUnion fun j => univ.biUnion fun i => univ.image fun h => (ω j).1.2 i h

/-- A configuration is live when its indicator is nonzero at some root of the box
`[U, 16U] × [V, 2V] × [0, 1]`. Only live configurations contribute to the root
replacement. -/
def ConfLive {x : ℝ} {d : Data K} {Y d₀ : ℝ} (ω : Conf x d Y d₀) : Prop :=
  ∃ u v r : ℝ, d₀ * Y * d.Hm ≤ u ∧ u ≤ 16 * (d₀ * Y * d.Hm) ∧ d.Hn ≤ v ∧ v ≤ 2 * d.Hn ∧
    0 ≤ r ∧ r ≤ 1 ∧ confInd x d Y d₀ ω u v r ≠ 0

/-! ### Elementary bounds -/

/-- A visit indicator is `0` or `1`. -/
theorem visitInd_mem_Icc (x : ℝ) (d : Data K) (Y d₀ u v r : ℝ)
    (s : (squareModel d Y d₀).State x d) :
    0 ≤ visitInd x d Y d₀ u v r s ∧ visitInd x d Y d₀ u v r s ≤ 1 := by
  unfold visitInd
  split_ifs <;> norm_num

/-- The archimedean indicator lies in `[0, 1]`. -/
theorem confInd_mem_Icc (x : ℝ) (d : Data K) (Y d₀ : ℝ) (ω : Conf x d Y d₀) (u v r : ℝ) :
    0 ≤ confInd x d Y d₀ ω u v r ∧ confInd x d Y d₀ ω u v r ≤ 1 :=
  ⟨prod_nonneg fun j _ => (visitInd_mem_Icc x d Y d₀ u v r (ω j)).1,
    prod_le_one₀ (fun j _ => (visitInd_mem_Icc x d Y d₀ u v r (ω j)).1)
      fun j _ => (visitInd_mem_Icc x d Y d₀ u v r (ω j)).2⟩

/-- The damping defect lies in `[0, 1]` for `q ∈ (0, 1)`. -/
theorem dampDefect_mem_Icc {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) (N j : ℕ) :
    0 ≤ dampDefect q N j ∧ dampDefect q N j ≤ 1 := by
  unfold dampDefect
  have h₁ : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq₁.le
  have h₀ : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  split_ifs <;> constructor <;> linarith

/-- The line factor lies in `[0, 1]` for `q ∈ (0, 1)`. -/
theorem confLineFactor_mem_Icc {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) {x : ℝ} {d : Data K}
    {Y d₀ : ℝ} (p : ℕ) (ω : Conf x d Y d₀) (l : ℕ) :
    0 ≤ confLineFactor q p ω l ∧ confLineFactor q p ω l ≤ 1 := by
  have hind : ∀ j, (0 : ℝ) ≤ (if l = confLines p ω j then 1 else 0) ∧
      (if l = confLines p ω j then (1 : ℝ) else 0) ≤ 1 := fun j => by
    split_ifs <;> norm_num
  have hfac : ∀ j, 0 ≤ 1 - dampDefect q (2 * momentPower x) j *
        (if l = confLines p ω j then (1 : ℝ) else 0) ∧
      1 - dampDefect q (2 * momentPower x) j *
        (if l = confLines p ω j then (1 : ℝ) else 0) ≤ 1 := fun j => by
    obtain ⟨h₀, h₁⟩ := dampDefect_mem_Icc hq hq₁ (2 * momentPower x) j
    obtain ⟨i₀, i₁⟩ := hind j
    constructor <;> nlinarith
  unfold confLineFactor
  have hA := prod_le_one₀ (s := activeSet p ω) (fun j _ => (hind j).1) fun j _ => (hind j).2
  have hB := prod_le_one₀ (s := (range (2 * momentPower x + 1)).filter (· ∉ activeSet p ω))
    (fun j _ => (hfac j).1) fun j _ => (hfac j).2
  have hB₀ := prod_nonneg (s := (range (2 * momentPower x + 1)).filter (· ∉ activeSet p ω))
    fun j _ => (hfac j).1
  refine ⟨mul_nonneg (prod_nonneg fun j _ => (hind j).1) hB₀,
    (mul_le_mul_of_nonneg_right hA hB₀).trans (by rw [one_mul]; exact hB)⟩

/-! ### The line-free states among the square states -/

section Square

variable {d : Data K} {Y d₀ u v r x : ℝ}

/-- The positions at a root lie in the square. -/
theorem rootPositions_subset_rootSquare (U V u v r : ℝ) :
    rootPositions U V u v r ⊆ rootSquare U V :=
  filter_subset _ _

/-- The inclusion of the line-free states at a root into the square states: keep the position
and the lists. -/
def toSquare (s : (freeRootModel d Y d₀ u v r).State x d) : (squareModel d Y d₀).State x d :=
  ⟨(⟨s.1.1.1, rootPositions_subset_rootSquare _ _ u v r s.1.1.2⟩, s.1.2), by
    classical
    exact mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, (mem_product.1 (mem_filter.1 s.2).1).2⟩,
      fun _ _ => trivial⟩⟩

/-- The inclusion of the line-free states is injective. -/
theorem toSquare_injective :
    Function.Injective (toSquare (d := d) (Y := Y) (d₀ := d₀) (u := u) (v := v) (r := r)
      (x := x)) := fun _ _ h =>
  Subtype.ext (Prod.ext (Subtype.ext (congrArg (fun t => t.1.1.1) h))
    (congrArg (fun t => t.1.2) h))

/-- The image of the line-free states is the square states at a position at the root. -/
theorem mem_range_toSquare_iff (t : (squareModel d Y d₀).State x d) :
    t ∈ Set.range (toSquare (d := d) (Y := Y) (d₀ := d₀) (u := u) (v := v) (r := r)
      (x := x)) ↔ t.1.1.1 ∈ rootPositions (d₀ * Y * d.Hm) d.Hn u v r := by
  classical
  constructor
  · rintro ⟨s, rfl⟩
    exact s.1.1.2
  · intro ht
    exact ⟨⟨(⟨t.1.1.1, ht⟩, t.1.2), mem_filter.2 ⟨mem_product.2 ⟨mem_univ _,
      (mem_product.1 (mem_filter.1 t.2).1).2⟩, fun _ _ => trivial⟩⟩, rfl⟩

open scoped Classical in
/-- The indicator of the square states at a position at the root `ϱ = (u, v, r)`. -/
def rootPosInd (u v r : ℝ) (t : (squareModel d Y d₀).State x d) : ℂ :=
  if t.1.1.1 ∈ rootPositions (d₀ * Y * d.Hm) d.Hn u v r then 1 else 0

/-- The indicator commutes with `𝒮` of the square model, which keeps the position. -/
theorem symOp_mul_rootPosInd :
    (squareModel d Y d₀).symOp x d * Matrix.diagonal (rootPosInd u v r) =
      Matrix.diagonal (rootPosInd u v r) * (squareModel d Y d₀).symOp x d := by
  classical
  ext t t'
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : t.1.1 = t'.1.1 ∧
      ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)), ∀ i, t'.1.2 i = t.1.2 i ∘ σ i
  · have hw : rootPosInd u v r t' = rootPosInd u v r t := by
      simp only [rootPosInd, h.1]
    rw [hw, mul_comm]
  · simp only [PosModel.symOp, h, ite_false, zero_mul, mul_zero]

/-- `𝒮` of the line-free model is the restriction of `𝒮` of the square model. -/
theorem symOp_toSquare (s s' : (freeRootModel d Y d₀ u v r).State x d) :
    (freeRootModel d Y d₀ u v r).symOp x d s s' =
      (squareModel d Y d₀).symOp x d (toSquare s) (toSquare s') := by
  refine if_congr (and_congr ⟨fun h => Subtype.ext ?_, fun h => Subtype.ext ?_⟩ Iff.rfl) rfl rfl
  · have h' := Subtype.ext_iff.1 h
    exact h'
  · have h' := Subtype.ext_iff.1 h
    exact h'

/-- `𝒯` of the line-free model is the restriction of `𝒯` of the square model. -/
theorem rowOp_toSquare (A₀ : ℝ) (s s' : (freeRootModel d Y d₀ u v r).State x d) :
    (freeRootModel d Y d₀ u v r).rowOp 1 A₀ x d Y d₀ s s' =
      (squareModel d Y d₀).rowOp 1 A₀ x d Y d₀ (toSquare s) (toSquare s') :=
  rfl

/-- `𝒢` of the line-free model is diagonal with the visit indicators of the included
states. -/
theorem goodOp_eq_diagonal_visitInd :
    (freeRootModel d Y d₀ u v r).goodOp x d Y d₀ =
      Matrix.diagonal fun s => (visitInd x d Y d₀ u v r (toSquare s) : ℂ) := by
  classical
  refine congrArg Matrix.diagonal (funext fun s => ?_)
  have hmem : (toSquare s).1.1.1 ∈ rootPositions (d₀ * Y * d.Hm) d.Hn u v r := s.1.1.2
  simp only [visitInd, hmem, true_and, apply_ite (fun t : ℝ => (t : ℂ)), Complex.ofReal_one,
    Complex.ofReal_zero]
  exact if_congr Iff.rfl rfl rfl

/-- `A⁰(s, s') = g(s) (𝒮 𝒯 𝒮)(s, s') g(s')` along the inclusion, where `g` is the visit
indicator and `𝒮 𝒯 𝒮` is the kernel of the square model. -/
theorem freeRootModel_edgeOp_eq (A₀ : ℝ) (s s' : (freeRootModel d Y d₀ u v r).State x d) :
    (freeRootModel d Y d₀ u v r).edgeOp 1 A₀ x d Y d₀ s s' =
      (visitInd x d Y d₀ u v r (toSquare s) : ℂ) *
        confKernel A₀ x d Y d₀ (toSquare s) (toSquare s') *
        (visitInd x d Y d₀ u v r (toSquare s') : ℂ) := by
  classical
  have hι := toSquare_injective (d := d) (Y := Y) (d₀ := d₀) (u := u) (v := v) (r := r)
    (x := x)
  have hv : ∀ s : (freeRootModel d Y d₀ u v r).State x d, rootPosInd u v r (toSquare s) = 1 :=
    fun s => ite_eq_left s.1.1.2
  have hv₀ : ∀ t ∉ Set.range (toSquare (d := d) (Y := Y) (d₀ := d₀) (u := u) (v := v) (r := r)
      (x := x)), rootPosInd u v r t = 0 := fun t ht =>
    ite_eq_right (mt (mem_range_toSquare_iff t).2 ht)
  -- step: restrict `𝒮 𝒯 𝒮`, with the indicator between the factors
  have h₁ := mul_apply_eq_restrict hι hv hv₀ symOp_toSquare (rowOp_toSquare A₀)
  have h₂ := mul_apply_eq_restrict hι hv hv₀ h₁ symOp_toSquare
  -- step: the indicators commute out past `𝒮`
  have hk : (squareModel d Y d₀).symOp x d * Matrix.diagonal (rootPosInd u v r) *
      (squareModel d Y d₀).rowOp 1 A₀ x d Y d₀ * Matrix.diagonal (rootPosInd u v r) *
      (squareModel d Y d₀).symOp x d =
      Matrix.diagonal (rootPosInd u v r) * confKernel A₀ x d Y d₀ *
        Matrix.diagonal (rootPosInd u v r) := by
    rw [confKernel, symOp_mul_rootPosInd]
    simp only [mul_assoc]
    rw [← symOp_mul_rootPosInd]
  have he : (freeRootModel d Y d₀ u v r).edgeOp 1 A₀ x d Y d₀ =
      (freeRootModel d Y d₀ u v r).goodOp x d Y d₀ *
        ((freeRootModel d Y d₀ u v r).symOp x d *
          (freeRootModel d Y d₀ u v r).rowOp 1 A₀ x d Y d₀ *
          (freeRootModel d Y d₀ u v r).symOp x d) *
        (freeRootModel d Y d₀ u v r).goodOp x d Y d₀ := by
    simp only [PosModel.edgeOp, mul_assoc]
  rw [he, goodOp_eq_diagonal_visitInd, Matrix.mul_diagonal, Matrix.diagonal_mul, h₂, hk,
    Matrix.mul_diagonal, Matrix.diagonal_mul, hv, hv, one_mul, mul_one]

/-- A visit indicator other than `1` is `0`. -/
theorem visitInd_eq_zero_of_ne_one {t : (squareModel d Y d₀).State x d}
    (ht : visitInd x d Y d₀ u v r t ≠ 1) : visitInd x d Y d₀ u v r t = 0 := by
  unfold visitInd at ht ⊢
  split_ifs at ht ⊢ with h
  · exact (ht rfl).elim
  · rfl

/-- The line-free weight of a path is the kernel `𝒮 𝒯 𝒮` along the included path, times the
visit indicators: every visit carries `g` once or twice, and `g² = g`. -/
theorem pathWeight_eq_prod_confKernel {A₀ : ℝ} {N : ℕ} (hN : 0 < N)
    (path : Fin (N + 1) → (freeRootModel d Y d₀ u v r).State x d) :
    pathWeight A₀ x d Y d₀ u v r path =
      (∏ j : Fin N, confKernel A₀ x d Y d₀ (toSquare (path j.castSucc))
        (toSquare (path j.succ))) * ∏ j, (visitInd x d Y d₀ u v r (toSquare (path j)) : ℂ) := by
  simp only [pathWeight, freeRootModel_edgeOp_eq]
  by_cases h : ∀ j, visitInd x d Y d₀ u v r (toSquare (path j)) = 1
  · simp [h]
  -- step: a visit with `g = 0` kills both sides
  push Not at h
  obtain ⟨k, hk⟩ := h
  have hk₀ := visitInd_eq_zero_of_ne_one hk
  rw [prod_eq_zero (mem_univ k) (by rw [hk₀, Complex.ofReal_zero]), mul_zero]
  by_cases hl : k = Fin.last N
  · have hk0 : k ≠ 0 := by
      rw [hl]
      exact Fin.ext_iff.not.2 (by simp; omega)
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hk0
    exact prod_eq_zero (mem_univ j) (by rw [hk₀, Complex.ofReal_zero, mul_zero])
  · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hl
    exact prod_eq_zero (mem_univ j) (by rw [hk₀, Complex.ofReal_zero, zero_mul, zero_mul])

end Square

/-! ### The expansion over configurations -/

/-- **RR2 over configurations**: with disjoint bands, the root moment at any root and lines
is `∑_ω c(ω) A(ω, ϱ) ∏_p λ_p(ω, ℓ_p)`. The paths of `freeRootModel` at `ϱ` are the
configurations whose visits are all positions at `ϱ`; along them the edge operator is
`𝒢 (𝒮 𝒯 𝒮) 𝒢`, with `𝒮 𝒯 𝒮` independent of the root. -/
theorem rootMoment_eq_sum_conf {q A₀ x : ℝ} (hq : 0 < q) {d : Data K} {Y d₀ : ℝ}
    (hR : 0 < momentPower x)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) (u v r : ℝ)
    (ℓ : ℕ → ℕ) :
    rootMoment q A₀ x d Y d₀ u v r ℓ =
      ∑ ω : Conf x d Y d₀, confCoeff A₀ x d Y d₀ ω * (confInd x d Y d₀ ω u v r : ℂ) *
        ∏ p ∈ bandPrimes x d, (confLineFactor q p ω (ℓ p) : ℂ) := by
  have hι := toSquare_injective (d := d) (Y := Y) (d₀ := d₀) (u := u) (v := v) (r := r)
    (x := x)
  rw [rootMoment_eq_sum_lineFactor hq hR hdisj ℓ, mul_sum]
  refine Fintype.sum_of_injective (fun path => toSquare ∘ path)
    (fun _ _ h => funext fun j => hι (congrFun h j)) _ _ (fun ω hω => ?_) fun path => ?_
  · -- step: a configuration with a visit off the positions at the root has `A(ω, ϱ) = 0`
    obtain ⟨j, hj⟩ : ∃ j, ω j ∉ Set.range (toSquare (d := d) (Y := Y) (d₀ := d₀) (u := u)
        (v := v) (r := r) (x := x)) := by
      by_contra h
      push Not at h
      choose path hpath using h
      exact hω ⟨path, funext hpath⟩
    have h0 : visitInd x d Y d₀ u v r (ω j) = 0 :=
      ite_eq_right fun h => hj ((mem_range_toSquare_iff (ω j)).2 h.1)
    rw [confInd, prod_eq_zero (mem_univ j) h0, Complex.ofReal_zero, mul_zero, zero_mul]
  · -- step: along an included path, the weight splits into `c(ω)` and `A(ω, ϱ)`
    have hline : ∀ p, lineFactor q p path (ℓ p) = confLineFactor q p (toSquare ∘ path) (ℓ p) :=
      fun p => rfl
    have hends : (if ((toSquare ∘ path) 0).1.1.1 = (1, 0) ∧
        ((toSquare ∘ path) (Fin.last _)).1.1.1 = (1, 0) then (1 : ℂ) else 0) =
        if (path 0).1.1.1 = (1, 0) ∧ (path (Fin.last _)).1.1.1 = (1, 0) then 1 else 0 :=
      rfl
    rw [pathWeight_eq_prod_confKernel (by omega), confCoeff, hends, confInd, Complex.ofReal_prod]
    simp only [hline, Function.comp_apply]
    ring

end Erdos408.OneSided
