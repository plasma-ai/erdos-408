import Erdos408.OneSided.Moment.Chain
import Mathlib.Algebra.Field.ZMod

/-!
# The line-free part of the chain edge

The chain edge `ℰ` (`Moment/Chain.lean`) chooses a source symmetrization `σ`, the stored
groups, a target `z'`, a new label per group with a promotion flag, and a target
symmetrization `σ'`. Forgetting the stored groups and the flags leaves a *free choice*
`(σ, z', labels, σ')`, and the line-free operator `A⁰` of S1 (`freeRootModel.edgeOp` at
`q = 1`) is the choice operator over free choices:

* `freeCoef` is the coefficient `M!^{-2K} ∏_i V_i⁻¹ κ` of a free choice, zero unless the
  choice is admissible (`FreeValid`: the restrictions of `EdgeValid` that do not involve the
  memory);
* `sum_edgeOp_mul_eq` expands `∑_{s'} A⁰(s, s') F(s')` as `∑_c freeCoef(s, c) F(freeOut(s, c))`.
  The two symmetrizations become the sums over `σ` and `σ'` (the lists are injective), and
  the row operation becomes the sum over the target and the new labels.

The chain coefficient is the free coefficient times the memory weights
(`chainEdgeCoef_eq_mul`). The admissible free choices keep the line of every pad prime
(`lineOf_eq_of_dvd_det`), since `p ∣ D ∣ det(z, z')` with `z, z'` primitive.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real
open scoped Matrix

variable {K : ℕ}

section Free

variable (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

/-- The line-free states at the root. -/
abbrev FreeState := (freeRootModel d Y d₀ u v r).State x d

/-- A free choice: the source symmetrization, the target, a new label per group, and the
target symmetrization. -/
abbrev FreeChoice :=
  (Fin K → Equiv.Perm (Fin (padCount x + 1))) × ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) ×
    (Fin K → ℕ) × (Fin K → Equiv.Perm (Fin (padCount x + 1)))

/-- The free choices: the new label of group `i` is a prime of `𝒫_i`. -/
def freeChoices : Finset (FreeChoice x d Y d₀ u v r) :=
  univ ×ˢ univ ×ˢ Fintype.piFinset (fun i => band x (d.a i)) ×ˢ univ

variable {x d Y d₀ u v r B}

/-- The edge choice with the free choice `c`, the stored groups `St` and the flags `fl`. -/
def toEdge (c : FreeChoice x d Y d₀ u v r) (St : Finset (Fin K)) (fl : Fin K → Bool) :
    EdgeChoice x d Y d₀ u v r :=
  (c.1, St, c.2.1, fun i => (c.2.2.1 i, fl i), c.2.2.2)

/-- The edge choice with the free choice `c`, nothing stored and nothing promoted. -/
abbrev toEdge₀ (c : FreeChoice x d Y d₀ u v r) : EdgeChoice x d Y d₀ u v r :=
  toEdge c ∅ fun _ => false

/-- The position and the lists of a chain state, as a line-free state. -/
def chainFree (s : ChainState x d Y d₀ u v r B) : FreeState x d Y d₀ u v r :=
  ⟨(s.1, s.2.1.1), by
    classical
    exact mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, s.2.1.2⟩, fun _ _ => trivial⟩⟩

variable (x d Y d₀ u v r B) in
/-- The restrictions of `EdgeValid` that do not involve the memory: valid target lists, the
cross-edge ban, the pad dyad, `D ∣ det`, and goodness at both ends. -/
def FreeValid (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : Prop :=
  edgeTgt s c ∈ lists x d (padCount x) ∧
    (∀ i i' h, (c.2.2.2.1 i).1 ≠ s.2.1.1 i' h) ∧
    d₀ ≤ (edgePad s c : ℝ) ∧ (edgePad s c : ℝ) < 2 * d₀ ∧ (edgePad s c : ℤ) ∣ edgeDet s c ∧
    (GoodFirst Y d₀ (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1 ∧
      GoodSecond x d d₀ (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1) ∧
    (GoodFirst Y d₀ (tau r (complement c.2.2.1.1) / tau r c.2.2.1.1) (edgeTgt s c) ∧
      GoodSecond x d d₀ (tau r (complement c.2.2.1.1) / tau r c.2.2.1.1) (edgeTgt s c))

variable (x d Y d₀ u v r B) in
/-- The restrictions of `EdgeValid` that involve the memory. -/
def MemValid (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : Prop :=
  (∀ i, (c.2.2.2.1 i).2 = true → ∃ xp : Particle x d, xp.1 = edgePromoted c i ∧
      1 ≤ s.2.2.1 xp) ∧
    (∀ i ∈ c.2.1, edgeStored s c i ∈ particles x d) ∧
    edgeMem s c ∈ memStates B

/-- `EdgeValid` splits into its free and memory restrictions. -/
theorem edgeValid_iff (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    EdgeValid x d Y d₀ u v r B s c ↔
      FreeValid x d Y d₀ u v r B s c ∧ MemValid x d Y d₀ u v r B s c := by
  simp only [EdgeValid, FreeValid, MemValid, and_assoc]

/-- The free restrictions do not see the stored groups or the flags. -/
theorem freeValid_toEdge (s : ChainState x d Y d₀ u v r B) (c : FreeChoice x d Y d₀ u v r)
    (St : Finset (Fin K)) (fl : Fin K → Bool) :
    FreeValid x d Y d₀ u v r B s (toEdge c St fl) ↔ FreeValid x d Y d₀ u v r B s (toEdge₀ c) :=
  Iff.rfl

/-- The free restrictions only see the position and the lists. -/
theorem freeValid_congr {s s' : ChainState x d Y d₀ u v r B} (h₁ : s'.1 = s.1) (h₂ : s'.2.1 = s.2.1)
    (c : EdgeChoice x d Y d₀ u v r) :
    FreeValid x d Y d₀ u v r B s' c ↔ FreeValid x d Y d₀ u v r B s c := by
  have ht : edgeTgt s' c = edgeTgt s c := by
    unfold edgeTgt edgeSrc
    rw [h₂]
  simp only [FreeValid, ht, edgeSrc, edgePad, edgeDet, h₁, h₂]

/-- The line-free kernel `(d₀/D) η(b/Y) η(a/Y) ψ(t/Y) {[t = b - a] - ∫_𝔐 e(θ(t - b + a))}`. -/
def freeKernel (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℂ :=
  ((d₀ / edgePad s c * dyadicBump ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y) *
      dyadicBump ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y) *
      plateau ((edgeDet s c / edgePad s c : ℤ) / Y) : ℝ) : ℂ) *
    ((if edgeDet s c / edgePad s c = ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) : ℤ) -
        (∏ i, (c.2.2.2.1 i).1 : ℕ) then 1 else 0) -
      arcIntegral A₀ x Y (edgeDet s c / edgePad s c -
        (∏ i, edgeSrc s c i (Fin.last _) : ℕ) + (∏ i, (c.2.2.2.1 i).1 : ℕ)))

open scoped Classical in
/-- The coefficient `M!^{-2K} ∏_i V_i⁻¹ κ` of a free choice; zero unless it is admissible. -/
def freeCoef (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℂ :=
  if FreeValid x d Y d₀ u v r B s c then
    (((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 * (d.bandMass x)⁻¹ : ℝ) : ℂ) *
      freeKernel A₀ s c
  else 0

/-- The free coefficient only sees the position and the lists. -/
theorem freeCoef_congr {s s' : ChainState x d Y d₀ u v r B} (h₁ : s'.1 = s.1) (h₂ : s'.2.1 = s.2.1)
    (c : EdgeChoice x d Y d₀ u v r) : freeCoef A₀ s' c = freeCoef A₀ s c := by
  obtain ⟨z, a, m⟩ := s
  obtain ⟨z', a', m'⟩ := s'
  simp only at h₁ h₂
  subst h₁ h₂
  rfl

open scoped Classical in
/-- The target of a free choice, as a line-free state (the source if it is not admissible). -/
def freeOut (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    FreeState x d Y d₀ u v r :=
  if h : FreeValid x d Y d₀ u v r B s c then
    ⟨(c.2.2.1, edgeTgt s c), by
      classical
      exact mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, h.1⟩, fun _ _ => trivial⟩⟩
  else chainFree s

/-! ### The symmetrization and the row operation as sums over choices -/

/-- A line-free state with its lists reordered by `σ`. -/
def permFree (a : FreeState x d Y d₀ u v r) (σ : Fin K → Equiv.Perm (Fin (padCount x + 1))) :
    FreeState x d Y d₀ u v r :=
  ⟨(a.1.1, fun i => a.1.2 i ∘ σ i), by
    classical
    have ha := (freeRootModel d Y d₀ u v r).mem_lists a
    refine mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, mem_filter.2 ⟨?_, fun i => ?_⟩⟩,
      fun _ _ => trivial⟩
    · simp only [Fintype.mem_piFinset, Function.comp_apply]
      exact fun i h => mem_band_of_mem_lists ha i _
    · exact (injective_of_mem_lists ha i).comp (σ i).injective⟩

/-- `∑_b 𝒮(a, b) H(b) = M!^{-K} ∑_σ H(a ∘ σ)`: the lists are injective, so every reordering
appears once. -/
theorem sum_freeSymOp_mul (a : FreeState x d Y d₀ u v r) (H : FreeState x d Y d₀ u v r → ℂ) :
    ∑ b, (freeRootModel d Y d₀ u v r).symOp x d a b * H b =
      (((padCount x + 1).factorial ^ K : ℕ) : ℂ)⁻¹ * ∑ σ, H (permFree a σ) := by
  classical
  have ha := (freeRootModel d Y d₀ u v r).mem_lists a
  -- step: the reorderings of `a` are the image of `σ ↦ a ∘ σ`, which is injective
  have hinj : Function.Injective (permFree a) := by
    intro σ σ' h
    funext i
    have h' := congrArg (fun b : FreeState x d Y d₀ u v r => b.1.2 i) h
    exact Equiv.ext fun k => injective_of_mem_lists ha i (congrFun h' k)
  have himage : univ.filter (fun b : FreeState x d Y d₀ u v r => a.1.1 = b.1.1 ∧
      ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)), ∀ i, b.1.2 i = a.1.2 i ∘ σ i) =
      univ.image (permFree a) := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨hz, σ, hσ⟩
      exact ⟨σ, Subtype.ext (Prod.ext hz (funext fun i => (hσ i).symm))⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨rfl, σ, fun i => rfl⟩
  simp only [PosModel.symOp, ite_mul, zero_mul]
  rw [← sum_filter, himage, sum_image fun σ _ σ' _ h => hinj h, mul_sum]

/-- The lists `p` with the last slot of each group replaced by the new labels. -/
def replaceLast {J : ℕ} (p : Lists K J) (lab : Fin K → ℕ) : Lists K J :=
  fun i h => if h = Fin.last _ then lab i else p i h

/-- A line-free state from a position and valid lists. -/
def mkFree (z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) (l : Lists K (padCount x))
    (hl : l ∈ lists x d (padCount x)) : FreeState x d Y d₀ u v r :=
  ⟨(z, l), by
    classical
    exact mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, hl⟩, fun _ _ => trivial⟩⟩

/-- `∑_k 𝒯(m, k) H(k)` is the sum over the target and the new labels: the row operation
copies the pads, so its target is determined by them. -/
theorem sum_rowOp_mul (A₀ : ℝ) (m : FreeState x d Y d₀ u v r)
    (H : FreeState x d Y d₀ u v r → ℂ) :
    ∑ k, (freeRootModel d Y d₀ u v r).rowOp 1 A₀ x d Y d₀ m k * H k =
      ∑ z', ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i)),
        if h : replaceLast m.1.2 lab ∈ lists x d (padCount x) then
          (freeRootModel d Y d₀ u v r).rowOp 1 A₀ x d Y d₀ m (mkFree z' _ h) *
            H (mkFree z' _ h)
        else 0 := by
  classical
  -- step: a target with nonzero row coefficient copies the pads of `m`
  have hpad : ∀ k, (freeRootModel d Y d₀ u v r).rowOp 1 A₀ x d Y d₀ m k ≠ 0 →
      replaceLast m.1.2 (fun i => k.1.2 i (Fin.last _)) = k.1.2 := by
    intro k hk
    have hc : ∀ i (h : Fin (padCount x)), k.1.2 i h.castSucc = m.1.2 i h.castSucc := by
      by_contra hc
      exact hk (by simp only [PosModel.rowOp, hc, false_and, ite_false])
    funext i h
    induction h using Fin.lastCases with
    | last => simp [replaceLast]
    | cast h => simp [replaceLast, (Fin.castSucc_lt_last h).ne, hc i h]
  rw [← sum_product']
  refine sum_bij_ne_zero (fun k _ _ => (k.1.1, fun i => k.1.2 i (Fin.last _))) ?_ ?_ ?_ ?_
  · intro k _ _
    simp only [mem_product, Fintype.mem_piFinset]
    exact ⟨mem_univ _, fun i =>
      mem_band_of_mem_lists ((freeRootModel d Y d₀ u v r).mem_lists k) i _⟩
  · intro k _ hk k' _ hk' h
    have hz := congrArg Prod.fst h
    have hl := congrArg Prod.snd h
    simp only at hz hl
    refine Subtype.ext (Prod.ext hz ?_)
    rw [← hpad k (left_ne_zero_of_mul hk), ← hpad k' (left_ne_zero_of_mul hk'), hl]
  · rintro ⟨z', lab⟩ _ hne
    by_cases h : replaceLast m.1.2 lab ∈ lists x d (padCount x)
    · refine ⟨mkFree z' _ h, mem_univ _, ?_, ?_⟩
      · simpa only [dite_eq_left h] using hne
      · simp [mkFree, replaceLast]
    · exact absurd (dite_eq_right h) hne
  · intro k _ hk
    have hk' := hpad k (left_ne_zero_of_mul hk)
    have hl : replaceLast m.1.2 (fun i => k.1.2 i (Fin.last _)) ∈ lists x d (padCount x) := by
      rw [hk']
      exact (freeRootModel d Y d₀ u v r).mem_lists k
    simp only [dite_eq_left hl]
    congr 2 <;> exact Subtype.ext (Prod.ext rfl hk'.symm)

/-- The lists of a permuted state are valid exactly when the unpermuted ones are. -/
theorem comp_perm_mem_lists_iff {J : ℕ} (l : Lists K J) (σ : Fin K → Equiv.Perm (Fin (J + 1))) :
    (fun i => l i ∘ σ i) ∈ lists x d J ↔ l ∈ lists x d J := by
  classical
  simp only [lists, mem_filter, Fintype.mem_piFinset, Function.comp_apply]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun i h => by simpa using h₁ i ((σ i).symm h), fun i => ?_⟩
    have := (h₂ i).comp (σ i).symm.injective
    simpa [Function.comp_def] using this
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun i h => h₁ i _, fun i => (h₂ i).comp (σ i).injective⟩

/-- A sandwich `𝒢 S T S 𝒢` with diagonal `𝒢` applied to a vector. -/
theorem sum_diagonal_sandwich_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ℂ)
    (S T : Matrix ι ι ℂ) (F : ι → ℂ) (a : ι) :
    ∑ b, (Matrix.diagonal g * S * T * S * Matrix.diagonal g) a b * F b =
      g a * ∑ m, S a m * ∑ k, T m k * ∑ b, S k b * (g b * F b) := by
  have hD : Matrix.diagonal g *ᵥ F = fun b => g b * F b :=
    funext fun b => Matrix.mulVec_diagonal g F b
  change ((Matrix.diagonal g * S * T * S * Matrix.diagonal g) *ᵥ F) a = _
  rw [← Matrix.mulVec_mulVec, hD, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
  rfl

open scoped Classical in
/-- The goodness indicator of a line-free state. -/
theorem goodOp_apply (a b : FreeState x d Y d₀ u v r) :
    (freeRootModel d Y d₀ u v r).goodOp x d Y d₀ a b =
      if a = b then (if GoodFirst Y d₀ (tau r (complement a.1.1.1) / tau r a.1.1.1) a.1.2 ∧
        GoodSecond x d d₀ (tau r (complement a.1.1.1) / tau r a.1.1.1) a.1.2 then 1 else 0)
      else 0 := by
  classical
  simp only [PosModel.goodOp, Matrix.diagonal_apply]
  rfl

/-- **The free expansion of `A⁰`**: `∑_{s'} A⁰(s, s') F(s') = ∑_c freeCoef(s, c) F(freeOut(s, c))`
over the free choices. -/
theorem sum_edgeOp_mul_eq (s : ChainState x d Y d₀ u v r B) (F : FreeState x d Y d₀ u v r → ℂ) :
    ∑ s', (freeRootModel d Y d₀ u v r).edgeOp 1 A₀ x d Y d₀ (chainFree s) s' * F s' =
      ∑ c ∈ freeChoices x d Y d₀ u v r, freeCoef A₀ s (toEdge₀ c) * F (freeOut s (toEdge₀ c)) := by
  classical
  set g : FreeState x d Y d₀ u v r → ℂ := fun b =>
    if GoodFirst Y d₀ (tau r (complement b.1.1.1) / tau r b.1.1.1) b.1.2 ∧
      GoodSecond x d d₀ (tau r (complement b.1.1.1) / tau r b.1.1.1) b.1.2 then 1 else 0 with hg
  -- step: `𝒢 𝒮 𝒯 𝒮 𝒢` with the diagonal `𝒢` at both ends
  have hG : (freeRootModel d Y d₀ u v r).goodOp x d Y d₀ = Matrix.diagonal g := by
    ext b b'
    rw [goodOp_apply, Matrix.diagonal_apply]
  have hexp := sum_diagonal_sandwich_mul g ((freeRootModel d Y d₀ u v r).symOp x d)
    ((freeRootModel d Y d₀ u v r).rowOp 1 A₀ x d Y d₀) F (chainFree s)
  rw [← hG] at hexp
  -- step: the two symmetrizations and the row operation as sums over choices
  rw [PosModel.edgeOp, hexp, sum_freeSymOp_mul (chainFree s)]
  simp only [sum_freeSymOp_mul, sum_rowOp_mul]
  simp only [freeChoices, sum_product, mul_sum]
  refine sum_congr rfl fun σ _ => sum_congr rfl fun z' _ => sum_congr rfl fun lab _ => ?_
  by_cases hl : replaceLast (permFree (chainFree s) σ).1.2 lab ∈ lists x d (padCount x)
  · rw [dite_eq_left hl]
    simp only [mul_sum]
    refine sum_congr rfl fun σ' _ => ?_
    set ec := toEdge₀ (σ, z', lab, σ')
    -- the target state is the free output
    have htgt : edgeTgt s ec = fun i => replaceLast (permFree (chainFree s) σ).1.2 lab i ∘ σ' i :=
      rfl
    have htgt_mem : edgeTgt s ec ∈ lists x d (padCount x) := by
      rw [htgt, comp_perm_mem_lists_iff]
      exact hl
    have hban : (∀ i i' h, (ec.2.2.2.1 i).1 ≠ s.2.1.1 i' h) ↔
        ∀ i i' (h : Fin (padCount x + 1)),
          (mkFree z' _ hl).1.2 i (Fin.last _) ≠ (permFree (chainFree s) σ).1.2 i' h := by
      have hlast : ∀ i, (mkFree z' _ hl).1.2 i (Fin.last _) = (ec.2.2.2.1 i).1 := fun i => by
        simp [mkFree, replaceLast, ec, toEdge]
      simp only [hlast]
      exact ⟨fun h i i' k => h i i' _, fun h i i' k => by
        simpa [permFree, chainFree] using h i i' ((σ i').symm k)⟩
    have hperm : permFree (mkFree z' _ hl) σ' = mkFree z' (edgeTgt s ec) htgt_mem := rfl
    -- the row operation is `∏ V_i⁻¹` times the free kernel when its restrictions hold
    have hrow : (freeRootModel d Y d₀ u v r).rowOp 1 A₀ x d Y d₀ (permFree (chainFree s) σ)
        (mkFree z' _ hl) =
          if (∀ i i' h, (ec.2.2.2.1 i).1 ≠ s.2.1.1 i' h) ∧ d₀ ≤ (edgePad s ec : ℝ) ∧
            (edgePad s ec : ℝ) < 2 * d₀ ∧ (edgePad s ec : ℤ) ∣ edgeDet s ec then
            (((d.bandMass x)⁻¹ : ℝ) : ℂ) * freeKernel A₀ s ec
          else 0 := by
      have hpad : ∀ i (h : Fin (padCount x)), (mkFree z' _ hl).1.2 i h.castSucc =
          (permFree (chainFree s) σ).1.2 i h.castSucc := fun i h => by
        simp [mkFree, replaceLast, (Fin.castSucc_lt_last h).ne]
      have hlast : lastProd (mkFree z' _ hl).1.2 = ∏ i, (ec.2.2.2.1 i).1 := by
        simp [lastProd, mkFree, replaceLast, ec, toEdge]
      have hD : padProd (permFree (chainFree s) σ).1.2 = edgePad s ec := rfl
      have hb : lastProd (permFree (chainFree s) σ).1.2 = ∏ i, edgeSrc s ec i (Fin.last _) := rfl
      have hdet : (freeRootModel d Y d₀ u v r).det (permFree (chainFree s) σ).1.1
          (mkFree z' _ hl).1.1 = edgeDet s ec := rfl
      simp only [PosModel.rowOp, hpad, implies_true, true_and, ← hban, hD, hb, hlast, hdet,
        one_rpow, mul_one, freeKernel]
      by_cases hc : (∀ i i' h, (ec.2.2.2.1 i).1 ≠ s.2.1.1 i' h) ∧ d₀ ≤ (edgePad s ec : ℝ) ∧
          (edgePad s ec : ℝ) < 2 * d₀ ∧ (edgePad s ec : ℤ) ∣ edgeDet s ec
      · rw [ite_eq_left hc, ite_eq_left hc]
        push_cast
        ring
      · rw [ite_eq_right hc, ite_eq_right hc]
    have hgs : g (chainFree s) = if GoodFirst Y d₀ (tau r (complement s.1.1) / tau r s.1.1)
        s.2.1.1 ∧ GoodSecond x d d₀ (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1 then 1
        else 0 := rfl
    have hgt : g (mkFree z' (edgeTgt s ec) htgt_mem) = if GoodFirst Y d₀
        (tau r (complement z'.1) / tau r z'.1) (edgeTgt s ec) ∧ GoodSecond x d d₀
        (tau r (complement z'.1) / tau r z'.1) (edgeTgt s ec) then 1 else 0 := rfl
    rw [hperm, hrow, hgs, hgt, freeCoef]
    by_cases hv : FreeValid x d Y d₀ u v r B s ec
    · have hout : freeOut s ec = mkFree z' (edgeTgt s ec) htgt_mem := by
        rw [freeOut, dite_eq_left hv]
        rfl
      obtain ⟨-, hb, hd₁, hd₂, hdvd, hga, hgt⟩ := hv
      have hc : (∀ i i' h, (ec.2.2.2.1 i).1 ≠ s.2.1.1 i' h) ∧ d₀ ≤ (edgePad s ec : ℝ) ∧
          (edgePad s ec : ℝ) < 2 * d₀ ∧ (edgePad s ec : ℤ) ∣ edgeDet s ec := ⟨hb, hd₁, hd₂, hdvd⟩
      have hv : FreeValid x d Y d₀ u v r B s ec := ⟨htgt_mem, hb, hd₁, hd₂, hdvd, hga, hgt⟩
      have e₁ : (if GoodFirst Y d₀ (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1 ∧
          GoodSecond x d d₀ (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1 then (1 : ℂ)
          else 0) = 1 := ite_eq_left hga
      have e₂ : (if GoodFirst Y d₀ (tau r (complement z'.1) / tau r z'.1) (edgeTgt s ec) ∧
          GoodSecond x d d₀ (tau r (complement z'.1) / tau r z'.1) (edgeTgt s ec) then (1 : ℂ)
          else 0) = 1 := ite_eq_left hgt
      rw [e₁, e₂, ite_eq_left hc, ite_eq_left hv, hout]
      push_cast
      ring
    · rw [ite_eq_right hv, zero_mul]
      -- one of the restrictions fails
      by_cases hga : GoodFirst Y d₀ (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1 ∧
          GoodSecond x d d₀ (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1
      swap
      · simp only [hga, ite_false, zero_mul]
      by_cases hgt : GoodFirst Y d₀ (tau r (complement z'.1) / tau r z'.1) (edgeTgt s ec) ∧
          GoodSecond x d d₀ (tau r (complement z'.1) / tau r z'.1) (edgeTgt s ec)
      swap
      · simp only [hgt, ite_false, zero_mul, mul_zero]
      have hc : ¬((∀ i i' h, (ec.2.2.2.1 i).1 ≠ s.2.1.1 i' h) ∧ d₀ ≤ (edgePad s ec : ℝ) ∧
          (edgePad s ec : ℝ) < 2 * d₀ ∧ (edgePad s ec : ℤ) ∣ edgeDet s ec) := fun h =>
        hv ⟨htgt_mem, h.1, h.2.1, h.2.2.1, h.2.2.2, hga, hgt⟩
      simp only [hc, ite_false, zero_mul, mul_zero]
  · rw [dite_eq_right hl, mul_zero, mul_zero]
    refine (sum_eq_zero fun σ' _ => ?_).symm
    have hv : ¬FreeValid x d Y d₀ u v r B s (toEdge₀ (σ, z', lab, σ')) := fun hv => hl (by
      have := hv.1
      rwa [show edgeTgt s (toEdge₀ (σ, z', lab, σ')) =
        fun i => replaceLast (permFree (chainFree s) σ).1.2 lab i ∘ σ' i from rfl,
        comp_perm_mem_lists_iff] at this)
    rw [freeCoef, ite_eq_right hv, zero_mul]

/-! ### The chain coefficient over the free coefficient -/

/-- With disjoint bands, the mass `V(p)` of a prime of `𝒫_i` is `V_i`. -/
theorem primeMass_eq (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {i : Fin K} {p : ℕ} (hp : p ∈ band x (d.a i)) :
    primeMass x d p = harmonicMass (band x (d.a i)) := by
  rw [primeMass, sum_eq_single i, ite_eq_left hp]
  · intro j _ hji
    exact ite_eq_right fun hpj => disjoint_left.1 (hdisj j i hji) hpj hp
  · exact fun h => absurd (mem_univ i) h

variable (x d) in
/-- The memory weight of the new label of group `i`, with its `V_i⁻¹` moved to the free
coefficient: `S(x)` for a promotion and `V_i ν(p) = ((p + 1) b'_p)⁻¹` for a fresh prime. -/
def memLabelWeight (N : ℕ) (S : Particle x d → ℕ) (c : EdgeChoice x d Y d₀ u v r) (i : Fin K) : ℝ :=
  if (c.2.2.2.1 i).2 then
    ∑ xp : Particle x d, if xp.1 = edgePromoted c i then (S xp : ℝ) else 0
  else (((c.2.2.2.1 i).1 + 1 : ℝ) * baseline q N (c.2.2.2.1 i).1)⁻¹

open scoped Classical in
/-- The memory part of the edge coefficient: `ρ^{hits(S, z)} ρ^{hits(S', z')} ∏_i` (label
weight), zero unless the memory restrictions hold. -/
def memEdgeCoef (N : ℕ) (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℝ :=
  if MemValid x d Y d₀ u v r B s c then
    pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
      pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
      ∏ i, memLabelWeight q x d N s.2.2.1 c i
  else 0

/-- The chain edge coefficient is the free coefficient times the memory part. -/
theorem chainEdgeCoef_eq_mul (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (N : ℕ) (s : ChainState x d Y d₀ u v r B)
    (c : FreeChoice x d Y d₀ u v r) (hc : c ∈ freeChoices x d Y d₀ u v r)
    (St : Finset (Fin K)) (fl : Fin K → Bool) :
    chainEdgeCoef q A₀ x d Y d₀ u v r B N s (toEdge c St fl) =
      freeCoef A₀ s (toEdge₀ c) * (memEdgeCoef q N s (toEdge c St fl) : ℂ) := by
  classical
  have hlab : ∀ i, c.2.2.1 i ∈ band x (d.a i) := by
    simp only [freeChoices, mem_product, Fintype.mem_piFinset] at hc
    exact hc.2.2.1
  -- step: each label weight is the memory weight over `V_i`
  have hw : ∀ i, (if (c.2.2.1 i, fl i).2 then
      (∑ xp : Particle x d, if xp.1 = edgePromoted (toEdge c St fl) i then (s.2.2.1 xp : ℝ)
        else 0) / primeMass x d (c.2.2.1 i)
      else primeWeight q x d N (c.2.2.1 i)) =
      memLabelWeight q x d N s.2.2.1 (toEdge c St fl) i * (harmonicMass (band x (d.a i)))⁻¹ := by
    intro i
    by_cases hfl : fl i = true
    · simp only [memLabelWeight, toEdge, hfl, ite_true, primeMass_eq hdisj (hlab i), div_eq_mul_inv]
    · simp only [memLabelWeight, toEdge, hfl, ite_false, Bool.false_eq_true, primeWeight,
        primeMass_eq hdisj (hlab i), one_div, mul_inv]
      ring
  have hV' : (d.bandMass x)⁻¹ = ∏ i, (harmonicMass (band x (d.a i)))⁻¹ := by
    rw [Data.bandMass, prod_inv_distrib]
  rw [chainEdgeCoef, freeCoef, memEdgeCoef]
  by_cases hf : FreeValid x d Y d₀ u v r B s (toEdge₀ c)
  · by_cases hm : MemValid x d Y d₀ u v r B s (toEdge c St fl)
    · rw [ite_eq_left ((edgeValid_iff s (toEdge c St fl)).2 ⟨hf, hm⟩), ite_eq_left hf,
        ite_eq_left hm]
      have hprod : (∏ i, if ((toEdge c St fl).2.2.2.1 i).2 then
          (∑ xp : Particle x d, if xp.1 = edgePromoted (toEdge c St fl) i then (s.2.2.1 xp : ℝ)
            else 0) / primeMass x d ((toEdge c St fl).2.2.2.1 i).1
          else primeWeight q x d N ((toEdge c St fl).2.2.2.1 i).1) =
          (∏ i, memLabelWeight q x d N s.2.2.1 (toEdge c St fl) i) * (d.bandMass x)⁻¹ := by
        rw [hV', ← prod_mul_distrib]
        exact prod_congr rfl fun i _ => hw i
      have hk : freeKernel A₀ s (toEdge₀ c) = freeKernel A₀ s (toEdge c St fl) := rfl
      dsimp only
      rw [hprod, hk]
      simp only [freeKernel]
      push_cast
      ring
    · rw [ite_eq_right fun h => hm ((edgeValid_iff s (toEdge c St fl)).1 h).2, ite_eq_right hm]
      simp
  · rw [ite_eq_right fun h => hf ((edgeValid_iff s (toEdge c St fl)).1 h).1, ite_eq_right hf,
      zero_mul]

/-- The free output only sees the position and the lists. -/
theorem freeOut_congr {s s' : ChainState x d Y d₀ u v r B} (h₁ : s'.1 = s.1) (h₂ : s'.2.1 = s.2.1)
    (c : EdgeChoice x d Y d₀ u v r) : freeOut s' c = freeOut s c := by
  obtain ⟨z, a, m⟩ := s
  obtain ⟨z', a', m'⟩ := s'
  simp only at h₁ h₂
  subst h₁ h₂
  rfl

/-- On an admissible choice, the free part of the chain output is the free output. -/
theorem chainFree_chainEdgeOut (s : ChainState x d Y d₀ u v r B) (c : FreeChoice x d Y d₀ u v r)
    (St : Finset (Fin K)) (fl : Fin K → Bool)
    (h : EdgeValid x d Y d₀ u v r B s (toEdge c St fl)) :
    chainFree (chainEdgeOut x d Y d₀ u v r B s (toEdge c St fl)) = freeOut s (toEdge₀ c) := by
  have hf : FreeValid x d Y d₀ u v r B s (toEdge₀ c) := ((edgeValid_iff s _).1 h).1
  simp only [chainEdgeOut, freeOut, dite_eq_left h, dite_eq_left hf]
  rfl

/-! ### Lines along an admissible edge -/

/-- A prime dividing `det(z, z')` for primitive `z, z'` gives them the same line. -/
theorem lineOf_eq_of_dvd_det {p : ℕ} (hp : p.Prime) {z z' : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1)
    (hz' : Int.gcd z'.1 z'.2 = 1) (hdvd : (p : ℤ) ∣ z.1 * z'.2 - z.2 * z'.1) :
    lineOf p z = lineOf p z' := by
  have : Fact p.Prime := ⟨hp⟩
  -- a primitive vector is nonzero modulo `p`
  have hne {w : ℤ × ℤ} (h : Int.gcd w.1 w.2 = 1) : ¬((w.1 : ZMod p) = 0 ∧ (w.2 : ZMod p) = 0) := by
    rintro ⟨h₁, h₂⟩
    obtain ⟨a, b, hab⟩ := Int.isCoprime_iff_gcd_eq_one.2 h
    have h' := congrArg (Int.cast : ℤ → ZMod p) hab
    push_cast at h'
    rw [h₁, h₂] at h'
    simp at h'
  have hval (w : ZMod p) : w.val ≠ p := (ZMod.val_lt w).ne
  have hd : (z.1 : ZMod p) * z'.2 - z.2 * z'.1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdvd
    push_cast at this
    exact this
  simp only [lineOf]
  by_cases h₁ : (z.1 : ZMod p) = 0 <;> by_cases h₁' : (z'.1 : ZMod p) = 0
  · simp [h₁, h₁']
  · -- `z₂ z'₁ = 0` with `z₂ ≠ 0` forces `z'₁ = 0`
    have h₂ : (z.2 : ZMod p) ≠ 0 := fun h => hne hz ⟨h₁, h⟩
    rw [h₁, zero_mul, zero_sub, neg_eq_zero] at hd
    exact absurd ((mul_eq_zero.1 hd).resolve_left h₂) h₁'
  · have h₂' : (z'.2 : ZMod p) ≠ 0 := fun h => hne hz' ⟨h₁', h⟩
    rw [h₁', mul_zero, sub_zero] at hd
    exact absurd ((mul_eq_zero.1 hd).resolve_right h₂') h₁
  · simp only [h₁, h₁', ite_false]
    congr 1
    field_simp
    linear_combination -hd

/-- The target lists consist of the pads of the reordered source and the new labels. -/
theorem mem_edgeTgt_iff (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r)
    (p : ℕ) : (∃ i h, edgeTgt s c i h = p) ↔
      (∃ i, ∃ h : Fin (padCount x), edgeSrc s c i h.castSucc = p) ∨ ∃ i, (c.2.2.2.1 i).1 = p := by
  constructor
  · rintro ⟨i, h, rfl⟩
    simp only [edgeTgt]
    induction hk : c.2.2.2.2 i h using Fin.lastCases with
    | last => exact Or.inr ⟨i, by simp⟩
    | cast k => exact Or.inl ⟨i, k, by simp [(Fin.castSucc_lt_last k).ne]⟩
  · rintro (⟨i, k, rfl⟩ | ⟨i, rfl⟩)
    · refine ⟨i, (c.2.2.2.2 i).symm k.castSucc, ?_⟩
      simp [edgeTgt, (Fin.castSucc_lt_last k).ne]
    · refine ⟨i, (c.2.2.2.2 i).symm (Fin.last _), ?_⟩
      simp [edgeTgt]

section Admissible

variable {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
  (hv : FreeValid x d Y d₀ u v r B s c)
include hv

/-- A prime of the source lists that is also in the target lists keeps its line: it is a
pad, so it divides `D ∣ det(z, z')`. -/
theorem lineOf_eq_of_stay {p : ℕ} (hp : p.Prime) (h₁ : ∃ i h, s.2.1.1 i h = p)
    (h₂ : ∃ i h, edgeTgt s c i h = p) : lineOf p s.1.1 = lineOf p c.2.2.1.1 := by
  rcases (mem_edgeTgt_iff s c p).1 h₂ with ⟨i, k, hk⟩ | ⟨i, hi⟩
  · -- `p` divides the pad product, hence the determinant
    have hD : (p : ℤ) ∣ (edgePad s c : ℤ) := by
      refine Int.natCast_dvd_natCast.2 ?_
      rw [edgePad, ← hk]
      exact (dvd_prod_of_mem (fun k => edgeSrc s c i k.castSucc) (mem_univ k)).trans
        (dvd_prod_of_mem (fun i => ∏ k : Fin (padCount x), edgeSrc s c i k.castSucc)
          (mem_univ i))
    have hz := (mem_filter.1 s.1.2).2.1
    have hz' := (mem_filter.1 c.2.2.1.2).2.1
    exact lineOf_eq_of_dvd_det hp hz hz' (hD.trans hv.2.2.2.2.1)
  · obtain ⟨i', h', hp'⟩ := h₁
    exact absurd (hi.trans hp'.symm) (hv.2.1 i i' h')

/-- The primes leaving activity are the unshared slots of the reordered source. -/
theorem leave_iff (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) (p : ℕ) :
    ((∃ i h, s.2.1.1 i h = p) ∧ ¬∃ i h, edgeTgt s c i h = p) ↔
      ∃ i, edgeSrc s c i (Fin.last _) = p := by
  have hs := s.2.1.2
  constructor
  · rintro ⟨⟨i, h, rfl⟩, hn⟩
    refine ⟨i, ?_⟩
    induction hk : (c.1 i).symm h using Fin.lastCases with
    | last =>
      simp only [edgeSrc, ← hk, Equiv.apply_symm_apply]
    | cast k =>
      refine absurd ((mem_edgeTgt_iff s c _).2 (Or.inl ⟨i, k, ?_⟩)) hn
      simp only [edgeSrc, ← hk, Equiv.apply_symm_apply]
  · rintro ⟨i, rfl⟩
    refine ⟨⟨i, _, rfl⟩, fun h => ?_⟩
    rcases (mem_edgeTgt_iff s c _).1 h with ⟨i', k, hk⟩ | ⟨i', hi'⟩
    · -- a pad equal to the unshared slot: same group, then the same slot
      have h₁ : edgeSrc s c i' k.castSucc ∈ band x (d.a i') := mem_band_of_mem_lists hs i' _
      rw [hk] at h₁
      have hii : i' = i := by
        by_contra hne
        exact disjoint_left.1 (hdisj i' i hne) h₁ (mem_band_of_mem_lists hs i _)
      subst hii
      have := (c.1 i').injective (injective_of_mem_lists hs i' hk)
      exact (Fin.castSucc_lt_last k).ne this
    · exact hv.2.1 i' i _ hi'

/-- The primes entering activity are the new labels. -/
theorem enter_iff (p : ℕ) :
    ((¬∃ i h, s.2.1.1 i h = p) ∧ ∃ i h, edgeTgt s c i h = p) ↔ ∃ i, (c.2.2.2.1 i).1 = p := by
  constructor
  · rintro ⟨hn, h⟩
    rcases (mem_edgeTgt_iff s c p).1 h with ⟨i, k, hk⟩ | hi
    · exact absurd ⟨i, _, hk⟩ hn
    · exact hi
  · rintro ⟨i, rfl⟩
    exact ⟨fun ⟨i', h', hp⟩ => hv.2.1 i i' h' hp.symm, (mem_edgeTgt_iff s c _).2 (Or.inr ⟨i, rfl⟩)⟩

end Admissible

end Free

end Erdos408.OneSided
