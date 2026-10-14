import Erdos408.OneSided.Moment.PrimeFactor
import Erdos408.OneSided.Moment.PathExpansion.Average
import Erdos408.OneSided.Moment.PathExpansion.Hermitian
import Erdos408.OneSided.Moment.PathExpansion.Paths

/-!
# The path expansion of the line average

Step S1 of the memory argument (`blueprint/one_sided_type_ii.md` §11). At a real root, the
lines enter the root moment only in two ways: through the validity of states (list primes
must hit) and through the damping `q^{(ω - KM)/2}` at each end of each edge. Write
`𝒜_ℓ(s, s') = A⁰(s, s') d_ℓ(z) d_ℓ(z')`, where `A⁰` is the line-free operator: the edge
operator of `freeRootModel`, where every prime divides, at `q = 1`. The kernel `A⁰` is
Hermitian: reversing an edge negates `t`, swaps the last-slot products, and conjugates the
arc integral. Expanding `(𝒜𝒜ᴴ)^R` into paths `s₀, …, s_N`, `N = 2R`, the line-dependent
factor of a path is `∏_j [valid_ℓ(s_j)] q_j^{ω_ℓ(z_j) - KM}`. Here `q_0 = q_N = √q` and
`q_j = q` otherwise. This factor is `∏_p ∏_j λ_{p,j}(ℓ_p)`, with `λ_{p,j}(ℓ) = [ℓ = [z_j]_p]`
when `p` is active at `j` and `1 - η'_j [ℓ = [z_j]_p]` otherwise; its factor at `p` is
`lineFactor`. This is the expansion at fixed lines, `rootMoment_eq_sum_lineFactor`. Since the
lines are independent and uniform, the average factors over the band primes into
`primeFactor`s (`lineAverage_rootMoment_eq`).

The generic pieces are in `PathExpansion/`: the path expansion of matrix powers and the
restriction along an injection (`Paths.lean`), the Hermitian row operation and the damping
factorization (`Hermitian.lean`), and averages of products over the lines (`Average.lean`).
The edge factorization is `rootModel_edgeOp_eq`, and the line weights along a path give the
line factors in `prod_lineWeight_eq`.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real
open scoped Matrix

variable {K : ℕ}

/-- The line-free model at a real root: the positions of `rootModel`, with every prime
dividing. -/
def freeRootModel (d : Data K) (Y d₀ u v r : ℝ) : PosModel where
  Pos := ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)
  det z z' := z.1.1 * z'.1.2 - z.1.2 * z'.1.1
  FirstDvd _ _ := True
  ratio z := tau r (complement z.1) / tau r z.1

/-- The damping defect `η'_j = 1 - q_j`, with `q_j = √q` at the ends `j = 0, N` and `q` in
between. -/
def dampDefect (q : ℝ) (N j : ℕ) : ℝ := if j = 0 ∨ j = N then 1 - Real.sqrt q else 1 - q

/-- The line-free weight `∏_{j < N} A⁰(s_j, s_{j+1})` of a path. -/
def pathWeight (A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) {N : ℕ}
    (path : Fin (N + 1) → (freeRootModel d Y d₀ u v r).State x d) : ℂ :=
  ∏ j : Fin N, (freeRootModel d Y d₀ u v r).edgeOp 1 A₀ x d Y d₀ (path j.castSucc) (path j.succ)

/-- The visits where the prime `p` is in the active lists. -/
def activeSet {M : PosModel} {x : ℝ} {d : Data K} {N : ℕ} (p : ℕ)
    (path : Fin (N + 1) → M.State x d) : Finset ℕ :=
  (univ.filter fun j : Fin (N + 1) => ∃ i h, (path j).1.2 i h = p).map Fin.valEmbedding

/-- The lines `[z_j]_p` along a path, extended by `0` past the end. -/
def pathLines {d : Data K} {Y d₀ u v r x : ℝ} {N : ℕ} (p : ℕ)
    (path : Fin (N + 1) → (freeRootModel d Y d₀ u v r).State x d) (j : ℕ) : ℕ :=
  if h : j < N + 1 then lineOf p (path ⟨j, h⟩).1.1.1 else 0

/-- The factor `λ_p(ℓ)` of the prime `p` along a path at the line `ℓ`:
`∏_{j active} [ℓ = [z_j]_p] ∏_{j inactive} (1 - η'_j [ℓ = [z_j]_p])`, over the visits
`j = 0, …, N`. Its average over `ℓ ∈ {0, …, p}` is `primeFactor`. -/
def lineFactor {d : Data K} {Y d₀ u v r x : ℝ} {N : ℕ} (q : ℝ) (p : ℕ)
    (path : Fin (N + 1) → (freeRootModel d Y d₀ u v r).State x d) (l : ℕ) : ℝ :=
  (∏ j ∈ activeSet p path, if l = pathLines p path j then 1 else 0) *
    ∏ j ∈ (range (N + 1)).filter (· ∉ activeSet p path),
      (1 - dampDefect q N j * if l = pathLines p path j then 1 else 0)

/-- `primeFactor` is the average of `lineFactor` over the lines. -/
theorem primeFactor_eq_sum_lineFactor {d : Data K} {Y d₀ u v r x : ℝ} {N : ℕ} (q : ℝ) (p : ℕ)
    (path : Fin (N + 1) → (freeRootModel d Y d₀ u v r).State x d) :
    primeFactor p N (pathLines p path) (dampDefect q N) (activeSet p path) =
      ((p : ℝ) + 1)⁻¹ * ∑ l ∈ range (p + 1), lineFactor q p path l :=
  rfl

/-! ### The root states among the line-free states -/

section Root

variable {d : Data K} {Y d₀ u v r x : ℝ}

/-- A line-free state is a state of `rootModel` at the lines `ℓ` when its list primes all hit:
`[z]_p = ℓ_p`. -/
def RootValid (ℓ : ℕ → ℕ) (s : (freeRootModel d Y d₀ u v r).State x d) : Prop :=
  ∀ i h, lineOf (s.1.2 i h) s.1.1.1 = ℓ (s.1.2 i h)

/-- The inclusion of the states of `rootModel` into the line-free states. -/
def toFree (ℓ : ℕ → ℕ) (s : (rootModel d Y d₀ u v r ℓ).State x d) :
    (freeRootModel d Y d₀ u v r).State x d :=
  ⟨s.1, by
    classical
    exact mem_filter.2 ⟨(mem_filter.1 s.2).1, fun _ _ => trivial⟩⟩

/-- The inclusion of the root states is injective. -/
theorem toFree_injective (ℓ : ℕ → ℕ) :
    Function.Injective (toFree (d := d) (Y := Y) (d₀ := d₀) (u := u) (v := v) (r := r)
      (x := x) ℓ) :=
  fun _ _ h => Subtype.ext (Subtype.mk.inj h)

/-- The image of the root states is the valid line-free states. -/
theorem mem_range_toFree_iff (ℓ : ℕ → ℕ) (s : (freeRootModel d Y d₀ u v r).State x d) :
    s ∈ Set.range (toFree ℓ) ↔ RootValid ℓ s := by
  classical
  constructor
  · rintro ⟨s, rfl⟩
    exact (mem_filter.1 s.2).2
  · intro hs
    exact ⟨⟨s.1, mem_filter.2 ⟨(mem_filter.1 s.2).1, hs⟩⟩, rfl⟩

open scoped Classical in
/-- The validity indicator `[valid_ℓ]` of a line-free state. -/
def validInd (ℓ : ℕ → ℕ) (s : (freeRootModel d Y d₀ u v r).State x d) : ℂ :=
  if RootValid ℓ s then 1 else 0

open scoped Classical in
/-- The line weight `[valid_ℓ] q^{(ω_ℓ(z) - KM)/2}` of a line-free state. -/
def lineWeight (q : ℝ) (ℓ : ℕ → ℕ) (s : (freeRootModel d Y d₀ u v r).State x d) : ℂ :=
  if RootValid ℓ s then
    ((q ^ ((((rootModel d Y d₀ u v r ℓ).bandCount x d s.1.1 : ℝ) - K * (padCount x + 1)) / 2) :
      ℝ) : ℂ)
  else 0

/-- The inclusion keeps the position and the lists. -/
theorem toFree_val (ℓ : ℕ → ℕ) (s : (rootModel d Y d₀ u v r ℓ).State x d) :
    (toFree ℓ s).1 = s.1 :=
  rfl

/-- The determinant of the line-free model. -/
theorem freeRootModel_det (z z' : (freeRootModel d Y d₀ u v r).Pos) :
    (freeRootModel d Y d₀ u v r).det z z' = z.1.1 * z'.1.2 - z.1.2 * z'.1.1 :=
  rfl

/-- The root states are valid. -/
theorem rootValid_toFree (ℓ : ℕ → ℕ) (s : (rootModel d Y d₀ u v r ℓ).State x d) :
    RootValid ℓ (toFree ℓ s) :=
  (mem_range_toFree_iff ℓ _).1 ⟨s, rfl⟩

/-- `𝒢` of the root model is the restriction of the line-free `𝒢`. -/
theorem goodOp_toFree (ℓ : ℕ → ℕ) (s s' : (rootModel d Y d₀ u v r ℓ).State x d) :
    (rootModel d Y d₀ u v r ℓ).goodOp x d Y d₀ s s' =
      (freeRootModel d Y d₀ u v r).goodOp x d Y d₀ (toFree ℓ s) (toFree ℓ s') := by
  simp only [PosModel.goodOp, Matrix.diagonal_apply, (toFree_injective ℓ).eq_iff]
  rfl

/-- `𝒮` of the root model is the restriction of the line-free `𝒮`. -/
theorem symOp_toFree (ℓ : ℕ → ℕ) (s s' : (rootModel d Y d₀ u v r ℓ).State x d) :
    (rootModel d Y d₀ u v r ℓ).symOp x d s s' =
      (freeRootModel d Y d₀ u v r).symOp x d (toFree ℓ s) (toFree ℓ s') :=
  rfl

/-- `𝒯` of the root model is the restriction of the line-free `𝒯` at `q = 1`, weighted by the
line weights at both ends. -/
theorem rowOp_toFree {q : ℝ} (hq : 0 < q) (A₀ : ℝ) (ℓ : ℕ → ℕ)
    (s s' : (rootModel d Y d₀ u v r ℓ).State x d) :
    (rootModel d Y d₀ u v r ℓ).rowOp q A₀ x d Y d₀ s s' =
      (Matrix.diagonal (lineWeight q ℓ) * (freeRootModel d Y d₀ u v r).rowOp 1 A₀ x d Y d₀ *
        Matrix.diagonal (lineWeight q ℓ) : Matrix _ _ ℂ) (toFree ℓ s) (toFree ℓ s') := by
  classical
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, PosModel.rowOp_eq_damp _ hq]
  simp only [lineWeight, rootValid_toFree, ite_true, toFree_val]
  congr 2
  simp only [PosModel.rowOp, one_rpow]
  rfl

/-- Permuting the lists within their groups preserves validity. -/
theorem rootValid_iff_of_perm (ℓ : ℕ → ℕ) {s s' : (freeRootModel d Y d₀ u v r).State x d}
    (hpos : s.1.1 = s'.1.1) (σ : Fin K → Equiv.Perm (Fin (padCount x + 1)))
    (hσ : ∀ i, s'.1.2 i = s.1.2 i ∘ σ i) : RootValid ℓ s' ↔ RootValid ℓ s := by
  simp only [RootValid, ← hpos, hσ, Function.comp_apply]
  exact ⟨fun h i k => by simpa using h i ((σ i).symm k), fun h i k => h i (σ i k)⟩

/-- The line weights commute with `𝒮`. -/
theorem symOp_mul_lineWeight (q : ℝ) (ℓ : ℕ → ℕ) :
    (freeRootModel d Y d₀ u v r).symOp x d * Matrix.diagonal (lineWeight q ℓ) =
      Matrix.diagonal (lineWeight q ℓ) * (freeRootModel d Y d₀ u v r).symOp x d := by
  classical
  ext s s'
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : s.1.1 = s'.1.1 ∧
      ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)), ∀ i, s'.1.2 i = s.1.2 i ∘ σ i
  · obtain ⟨hpos, σ, hσ⟩ := h
    have hw : lineWeight q ℓ s' = lineWeight q ℓ s := by
      simp only [lineWeight, rootValid_iff_of_perm ℓ hpos σ hσ, ← hpos]
    rw [hw, mul_comm]
  · simp only [PosModel.symOp, h, ite_false, zero_mul, mul_zero]

/-- The line weights commute with `𝒢`. -/
theorem goodOp_mul_lineWeight (q : ℝ) (ℓ : ℕ → ℕ) :
    (freeRootModel d Y d₀ u v r).goodOp x d Y d₀ * Matrix.diagonal (lineWeight q ℓ) =
      Matrix.diagonal (lineWeight q ℓ) * (freeRootModel d Y d₀ u v r).goodOp x d Y d₀ := by
  simp only [PosModel.goodOp, Matrix.diagonal_mul_diagonal, mul_comm]

/-- The validity indicator is one on the support of the line weights. -/
theorem validInd_mul_lineWeight (q : ℝ) (ℓ : ℕ → ℕ) :
    Matrix.diagonal (validInd (d := d) (Y := Y) (d₀ := d₀) (u := u) (v := v) (r := r)
      (x := x) ℓ) * Matrix.diagonal (lineWeight q ℓ) = Matrix.diagonal (lineWeight q ℓ) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext s
  simp only [validInd, lineWeight]
  split_ifs <;> simp

/-- The validity indicator is one on the support of the line weights, on the right. -/
theorem lineWeight_mul_validInd (q : ℝ) (ℓ : ℕ → ℕ) :
    Matrix.diagonal (lineWeight q ℓ) * Matrix.diagonal (validInd (d := d) (Y := Y) (d₀ := d₀)
      (u := u) (v := v) (r := r) (x := x) ℓ) = Matrix.diagonal (lineWeight q ℓ) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext s
  simp only [validInd, lineWeight]
  split_ifs <;> simp

/-- `𝒜_ℓ(s, s') = d_ℓ(z) A⁰(s, s') d_ℓ(z')` on the root states, with `A⁰` the line-free `𝒜`
at `q = 1`. -/
theorem rootModel_edgeOp_eq {q : ℝ} (hq : 0 < q) (A₀ : ℝ) (ℓ : ℕ → ℕ)
    (s s' : (rootModel d Y d₀ u v r ℓ).State x d) :
    (rootModel d Y d₀ u v r ℓ).edgeOp q A₀ x d Y d₀ s s' =
      (Matrix.diagonal (lineWeight q ℓ) * (freeRootModel d Y d₀ u v r).edgeOp 1 A₀ x d Y d₀ *
        Matrix.diagonal (lineWeight q ℓ) : Matrix _ _ ℂ) (toFree ℓ s) (toFree ℓ s') := by
  have hv : ∀ s : (rootModel d Y d₀ u v r ℓ).State x d, validInd ℓ (toFree ℓ s) = 1 := fun s => by
    rw [validInd, ite_eq_left (rootValid_toFree ℓ s)]
  have hv₀ : ∀ k ∉ Set.range (toFree (d := d) (Y := Y) (d₀ := d₀) (u := u) (v := v) (r := r)
      (x := x) ℓ), validInd ℓ k = 0 := fun k hk => by
    rw [validInd, ite_eq_right (mt (mem_range_toFree_iff ℓ k).2 hk)]
  -- step: restrict the five factors, with the validity indicator between them
  have hι := toFree_injective (d := d) (Y := Y) (d₀ := d₀) (u := u) (v := v) (r := r)
    (x := x) ℓ
  have h₁ := mul_apply_eq_restrict hι hv hv₀ (goodOp_toFree ℓ) (symOp_toFree ℓ)
  have h₂ := mul_apply_eq_restrict hι hv hv₀ h₁ (rowOp_toFree hq A₀ ℓ)
  have h₃ := mul_apply_eq_restrict hι hv hv₀ h₂ (symOp_toFree ℓ)
  have h₄ := mul_apply_eq_restrict hι hv hv₀ h₃ (goodOp_toFree ℓ)
  rw [PosModel.edgeOp, h₄, edge_restrict_eq (goodOp_mul_lineWeight q ℓ)
    (symOp_mul_lineWeight q ℓ) (validInd_mul_lineWeight q ℓ) (lineWeight_mul_validInd q ℓ)]
  rfl

/-! ### The line weights of valid states -/

/-- The inactive hits of a state: the band primes outside the lists with `[z]_p = ℓ_p`. -/
def inactiveHits (ℓ : ℕ → ℕ) (s : (freeRootModel d Y d₀ u v r).State x d) : ℕ :=
  (((bandPrimes x d).filter fun p => ¬∃ i h, s.1.2 i h = p).filter
    fun p => ℓ p = lineOf p s.1.1.1).card

/-- With disjoint bands, the list primes of a state are `KM` distinct band primes. -/
theorem card_filter_listed (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (s : (freeRootModel d Y d₀ u v r).State x d) :
    ((bandPrimes x d).filter fun p => ∃ i h, s.1.2 i h = p).card = K * (padCount x + 1) := by
  classical
  have hs := (freeRootModel d Y d₀ u v r).mem_lists s
  -- step: the listed band primes are the union of the groups
  have hunion : ((bandPrimes x d).filter fun p => ∃ i h, s.1.2 i h = p) =
      univ.biUnion fun i => univ.image (s.1.2 i) := by
    ext p
    simp only [bandPrimes, mem_filter, mem_biUnion, mem_univ, true_and, mem_image]
    exact ⟨fun h => h.2, fun ⟨i, h, hp⟩ => ⟨⟨i, hp ▸ mem_band_of_mem_lists hs i h⟩, i, h, hp⟩⟩
  rw [hunion, card_biUnion fun i _ j _ hij => (hdisj i j hij).mono
    (image_subset_iff.2 fun h _ => mem_band_of_mem_lists hs i h)
    (image_subset_iff.2 fun h _ => mem_band_of_mem_lists hs j h)]
  simp only [card_image_of_injective _ (injective_of_mem_lists hs _), card_univ,
    Fintype.card_fin, sum_const, smul_eq_mul]

/-- For a valid state, `ω_ℓ(z) = KM + #(inactive hits)`. -/
theorem bandCount_eq (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (ℓ : ℕ → ℕ) {s : (freeRootModel d Y d₀ u v r).State x d} (hs : RootValid ℓ s) :
    (rootModel d Y d₀ u v r ℓ).bandCount x d s.1.1 = inactiveHits ℓ s + K * (padCount x + 1) := by
  classical
  -- step: `ω_ℓ` counts the hitting band primes
  have hω : (rootModel d Y d₀ u v r ℓ).bandCount x d s.1.1 =
      ((bandPrimes x d).filter fun p => ℓ p = lineOf p s.1.1.1).card := by
    simp only [PosModel.bandCount]
    rw [bandPrimes, filter_biUnion, card_biUnion fun i _ j _ hij =>
      (hdisj i j hij).mono (filter_subset _ _) (filter_subset _ _)]
    refine sum_congr rfl fun i _ => congrArg card (filter_congr fun p _ => ?_)
    exact eq_comm
  -- step: split by listing; the listed primes all hit
  have hlisted : (((bandPrimes x d).filter fun p => ℓ p = lineOf p s.1.1.1).filter
      fun p => ∃ i h, s.1.2 i h = p) = (bandPrimes x d).filter fun p => ∃ i h, s.1.2 i h = p := by
    rw [filter_comm]
    refine filter_true_of_mem fun p hp => ?_
    obtain ⟨i, h, rfl⟩ := (mem_filter.1 hp).2
    exact (hs i h).symm
  rw [hω, ← card_filter_add_card_filter_not (fun p => ∃ i h, s.1.2 i h = p), hlisted,
    card_filter_listed hdisj s, inactiveHits, filter_comm, add_comm]

/-- The line weight of a valid state is `√q^{#(inactive hits)}`. -/
theorem lineWeight_of_valid {q : ℝ} (hq : 0 < q)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) (ℓ : ℕ → ℕ)
    {s : (freeRootModel d Y d₀ u v r).State x d} (hs : RootValid ℓ s) :
    lineWeight q ℓ s = ((Real.sqrt q ^ inactiveHits ℓ s : ℝ) : ℂ) := by
  rw [lineWeight, ite_eq_left hs, bandCount_eq hdisj ℓ hs]
  push_cast
  rw [show ((inactiveHits ℓ s : ℝ) + K * (padCount x + 1) - K * (padCount x + 1)) / 2 =
    (1 / 2 : ℝ) * inactiveHits ℓ s by ring, rpow_mul hq.le, ← sqrt_eq_rpow, rpow_natCast]
  norm_cast

open scoped Classical in
/-- The factor of a visit at a state, over the band primes: `[ℓ_p = [z]_p]` for the listed
primes and `1 - (1 - Q) [ℓ_p = [z]_p]` for the others. It is `[valid_ℓ] Q^{#(inactive hits)}`. -/
theorem prod_visit_eq (ℓ : ℕ → ℕ) (s : (freeRootModel d Y d₀ u v r).State x d)
    {A : ℕ → Prop} [DecidablePred A] (hA : ∀ p, A p ↔ ∃ i h, s.1.2 i h = p) {L : ℕ → ℕ}
    (hL : ∀ p, L p = lineOf p s.1.1.1) {η Q : ℝ} (hη : η = 1 - Q) :
    ∏ p ∈ bandPrimes x d, (if A p then (if ℓ p = L p then (1 : ℝ) else 0)
      else 1 - η * if ℓ p = L p then 1 else 0) =
      if RootValid ℓ s then Q ^ inactiveHits ℓ s else 0 := by
  classical
  -- step: the inactive primes contribute `Q` per hit
  have hvisit : ∀ p, (if A p then (if ℓ p = L p then (1 : ℝ) else 0)
      else 1 - η * if ℓ p = L p then 1 else 0) =
      if ∃ i h, s.1.2 i h = p then (if ℓ p = lineOf p s.1.1.1 then 1 else 0)
      else if ℓ p = lineOf p s.1.1.1 then Q else 1 := fun p => by
    rw [hL, hη]
    by_cases hp : A p
    · rw [ite_eq_left hp, ite_eq_left ((hA p).1 hp)]
    · rw [ite_eq_right hp, ite_eq_right (mt (hA p).2 hp)]
      split_ifs <;> ring
  unfold inactiveHits
  simp only [hvisit]
  rw [prod_ite, prod_boole, prod_ite, prod_const, prod_const_one, mul_one, boole_mul]
  -- step: the listed primes all hit exactly when the state is valid
  refine if_congr ⟨fun h i k => ?_, fun h p hp => ?_⟩ rfl rfl
  · refine (h _ (mem_filter.2 ⟨?_, i, k, rfl⟩)).symm
    exact mem_biUnion.2 ⟨i, mem_univ _,
      mem_band_of_mem_lists ((freeRootModel d Y d₀ u v r).mem_lists s) i k⟩
  · obtain ⟨i, k, rfl⟩ := (mem_filter.1 hp).2
    exact (h i k).symm

/-! ### The line factor of a path -/

/-- `p` is active at the visit `j` when it is in the lists of the `j`-th state. -/
theorem mem_activeSet {M : PosModel} {N : ℕ} (p : ℕ) (path : Fin (N + 1) → M.State x d)
    (j : Fin (N + 1)) : (j : ℕ) ∈ activeSet p path ↔ ∃ i h, (path j).1.2 i h = p := by
  simp [activeSet, Fin.val_inj]

/-- The active visits are visits. -/
theorem activeSet_subset {M : PosModel} {N : ℕ} (p : ℕ) (path : Fin (N + 1) → M.State x d) :
    activeSet p path ⊆ range (N + 1) := by
  intro j hj
  obtain ⟨j, -, rfl⟩ := mem_map.1 hj
  exact mem_range.2 j.2

/-- The line `[z_j]_p` at a visit `j ≤ N`. -/
theorem pathLines_val {N : ℕ} (p : ℕ) (path : Fin (N + 1) → (freeRootModel d Y d₀ u v r).State x d)
    (j : Fin (N + 1)) : pathLines p path j = lineOf p (path j).1.1.1 := by
  simp [pathLines, j.isLt]

/-- `lineFactor` as a product over all visits. -/
theorem lineFactor_eq_prod {N : ℕ} (q : ℝ) (p : ℕ)
    (path : Fin (N + 1) → (freeRootModel d Y d₀ u v r).State x d) (l : ℕ) :
    lineFactor q p path l = ∏ j ∈ range (N + 1), if j ∈ activeSet p path then
      (if l = pathLines p path j then 1 else 0)
      else 1 - dampDefect q N j * if l = pathLines p path j then 1 else 0 := by
  rw [prod_ite, filter_mem_eq_inter, inter_eq_right.2 (activeSet_subset p path), lineFactor]

/-- The line weights along a path give the line factors: interior visits carry both half
weights `√q^h`, the ends one. -/
theorem prod_lineWeight_eq {q : ℝ} (hq : 0 < q)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) {N : ℕ} (hN : 0 < N)
    (ℓ : ℕ → ℕ) (path : Fin (N + 1) → (freeRootModel d Y d₀ u v r).State x d) :
    ∏ j : Fin N, lineWeight q ℓ (path j.castSucc) * lineWeight q ℓ (path j.succ) =
      ((∏ p ∈ bandPrimes x d, lineFactor q p path (ℓ p) : ℝ) : ℂ) := by
  -- step: collect the two half weights at each visit
  have hends : ∏ j : Fin N, lineWeight q ℓ (path j.castSucc) * lineWeight q ℓ (path j.succ) =
      ∏ j : Fin (N + 1), (if j ≠ Fin.last N then lineWeight q ℓ (path j) else 1) *
        (if j ≠ 0 then lineWeight q ℓ (path j) else 1) := by
    rw [prod_mul_distrib, prod_mul_distrib]
    congr 1
    · rw [Fin.prod_univ_castSucc]
      simp [(Fin.castSucc_lt_last _).ne]
    · rw [Fin.prod_univ_succ]
      simp [Fin.succ_ne_zero]
  rw [hends]
  simp only [lineFactor_eq_prod]
  rw [prod_comm, prod_range, Complex.ofReal_prod]
  refine prod_congr rfl fun j _ => ?_
  -- step: the factor of the visit `j`
  have hη : dampDefect q N j = 1 - if (j : ℕ) = 0 ∨ (j : ℕ) = N then Real.sqrt q else q := by
    unfold dampDefect
    split_ifs <;> ring
  rw [prod_visit_eq ℓ (path j) (fun p => mem_activeSet p path j) (fun p => pathLines_val p path j)
    hη]
  have hlast : Fin.last N ≠ 0 := Fin.ext_iff.not.2 (by simp; omega)
  by_cases hs : RootValid ℓ (path j)
  · rw [lineWeight_of_valid hq hdisj ℓ hs, ite_eq_left hs]
    by_cases h0 : j = 0
    · simp [h0, hlast.symm]
    by_cases hl : j = Fin.last N
    · simp [hl, hlast]
    -- step: an interior visit carries `√q^h √q^h = q^h`
    have hint : ¬((j : ℕ) = 0 ∨ (j : ℕ) = N) := by
      rintro (h | h)
      · exact h0 (Fin.ext h)
      · exact hl (Fin.ext h)
    rw [ite_eq_left hl, ite_eq_left h0, ite_eq_right hint, ← Complex.ofReal_mul, ← mul_pow,
      Real.mul_self_sqrt hq.le]
  · rw [lineWeight, ite_eq_right hs, ite_eq_right hs]
    by_cases hj : j = 0
    · simp [hj, hlast.symm]
    · simp [hj]

/-- The line weights are real. -/
theorem star_lineWeight (q : ℝ) (ℓ : ℕ → ℕ) :
    star (lineWeight (d := d) (Y := Y) (d₀ := d₀) (u := u) (v := v) (r := r) (x := x) q ℓ) =
      lineWeight q ℓ := by
  funext s
  rw [Pi.star_apply, lineWeight]
  split_ifs
  · exact Complex.conj_ofReal _
  · exact star_zero _

/-- With disjoint bands, `d_ℓ A⁰ d_ℓ` is Hermitian. -/
theorem conjTranspose_lineEdge (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (q A₀ : ℝ) (ℓ : ℕ → ℕ) :
    (Matrix.diagonal (lineWeight q ℓ) * (freeRootModel d Y d₀ u v r).edgeOp 1 A₀ x d Y d₀ *
      Matrix.diagonal (lineWeight q ℓ))ᴴ =
      Matrix.diagonal (lineWeight q ℓ) * (freeRootModel d Y d₀ u v r).edgeOp 1 A₀ x d Y d₀ *
        Matrix.diagonal (lineWeight q ℓ) := by
  have hdet : ∀ P Q, (freeRootModel d Y d₀ u v r).det Q P =
      -(freeRootModel d Y d₀ u v r).det P Q := fun P Q => by
    rw [freeRootModel_det, freeRootModel_det]
    ring
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose,
    star_lineWeight, PosModel.conjTranspose_edgeOp _ hdet hdisj, mul_assoc]

end Root

/-- **S1 at fixed lines**: with disjoint bands, the root moment at the lines `ℓ` is
`σ ∑_paths A⁰-weight ∏_p λ_p(ℓ_p)`, over the paths of line-free states from `e₁` to `e₁` with
`N = 2R` edges. -/
theorem rootMoment_eq_sum_lineFactor {q A₀ x : ℝ} (hq : 0 < q) {d : Data K} {Y d₀ u v r : ℝ}
    (hR : 0 < momentPower x) (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (ℓ : ℕ → ℕ) :
    rootMoment q A₀ x d Y d₀ u v r ℓ =
      (stateMass x d : ℂ) *
        ∑ path : Fin (2 * momentPower x + 1) → (freeRootModel d Y d₀ u v r).State x d,
          (if (path 0).1.1.1 = (1, 0) ∧ (path (Fin.last _)).1.1.1 = (1, 0) then (1 : ℂ) else 0) *
            pathWeight A₀ x d Y d₀ u v r path *
            ∏ p ∈ bandPrimes x d, (lineFactor q p path (ℓ p) : ℂ) := by
  set B : Matrix _ _ ℂ := Matrix.diagonal (lineWeight q ℓ) *
    (freeRootModel d Y d₀ u v r).edgeOp 1 A₀ x d Y d₀ * Matrix.diagonal (lineWeight q ℓ) with hB
  have hι := toFree_injective (d := d) (Y := Y) (d₀ := d₀) (u := u) (v := v) (r := r)
    (x := x) ℓ
  have hA := rootModel_edgeOp_eq (d := d) (Y := Y) (d₀ := d₀) (u := u) (v := v) (r := r)
    (x := x) hq A₀ ℓ
  -- step: `𝒜_ℓ` is Hermitian, so `(𝒜_ℓ 𝒜_ℓᴴ)^R = 𝒜_ℓ^N`
  have hAH : ((rootModel d Y d₀ u v r ℓ).edgeOp q A₀ x d Y d₀)ᴴ =
      (rootModel d Y d₀ u v r ℓ).edgeOp q A₀ x d Y d₀ := by
    ext s s'
    rw [Matrix.conjTranspose_apply, hA, hA, ← Matrix.conjTranspose_apply B,
      conjTranspose_lineEdge hdisj]
  -- step: `d_ℓ A⁰ d_ℓ` vanishes off the valid states
  have hw₀ : ∀ k ∉ Set.range (toFree (d := d) (Y := Y) (d₀ := d₀) (u := u) (v := v) (r := r)
      (x := x) ℓ), lineWeight q ℓ k = 0 := fun k hk => by
    rw [lineWeight, ite_eq_right (mt (mem_range_toFree_iff ℓ k).2 hk)]
  have hrow : ∀ k ∉ Set.range (toFree ℓ), ∀ j, B k j = 0 := fun k hk j => by
    rw [hB, Matrix.mul_diagonal, Matrix.diagonal_mul, hw₀ k hk, zero_mul, zero_mul]
  have hcol : ∀ k ∉ Set.range (toFree ℓ), ∀ i, B i k = 0 := fun k hk i => by
    rw [hB, Matrix.mul_diagonal, hw₀ k hk, mul_zero]
  -- step: the weight of a path splits into `A⁰` and the line factors
  have hpath : ∀ path : Fin (2 * momentPower x + 1) → (freeRootModel d Y d₀ u v r).State x d,
      ∏ j : Fin (2 * momentPower x), B (path j.castSucc) (path j.succ) =
        pathWeight A₀ x d Y d₀ u v r path *
          ∏ p ∈ bandPrimes x d, (lineFactor q p path (ℓ p) : ℂ) := fun path => by
    rw [← Complex.ofReal_prod, ← prod_lineWeight_eq hq hdisj (by omega) ℓ path, pathWeight,
      ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [hB, Matrix.mul_diagonal, Matrix.diagonal_mul]
    ring
  by_cases h₀ : ((1 : ℤ), (0 : ℤ)) ∈ rootPositions (d₀ * Y * d.Hm) d.Hn u v r
  · simp only [rootMoment, h₀, ↓reduceDIte]
    simp only [PosModel.moment]
    rw [hAH, ← sq, ← pow_mul]
    congr 1
    -- step: expand into paths of line-free states
    set g : (freeRootModel d Y d₀ u v r).State x d → (freeRootModel d Y d₀ u v r).State x d → ℂ :=
      fun b b' => if b.1.1.1 = (1, 0) ∧ b'.1.1.1 = (1, 0) then 1 else 0
    have hpaths : ∑ path : Fin (2 * momentPower x + 1) → (freeRootModel d Y d₀ u v r).State x d,
        (if (path 0).1.1.1 = (1, 0) ∧ (path (Fin.last _)).1.1.1 = (1, 0) then (1 : ℂ) else 0) *
          pathWeight A₀ x d Y d₀ u v r path *
          ∏ p ∈ bandPrimes x d, (lineFactor q p path (ℓ p) : ℂ) =
        ∑ path : Fin (2 * momentPower x + 1) → (freeRootModel d Y d₀ u v r).State x d,
          g (path 0) (path (Fin.last _)) *
            ∏ j : Fin (2 * momentPower x), B (path j.castSucc) (path j.succ) :=
      sum_congr rfl fun path _ => by rw [mul_assoc, hpath]
    rw [hpaths, ← sum_mul_pow_apply B _ g,
      ← sum_mul_pow_apply_eq_restrict hι hA hrow hcol (by omega) g]
    -- step: the endpoint condition at `e₁`, read on the line-free states
    refine sum_congr rfl fun s _ => sum_congr rfl fun s' _ => ?_
    change _ = (if s.1.1.1 = (1, 0) ∧ s'.1.1.1 = (1, 0) then (1 : ℂ) else 0) * _
    by_cases h : s.1.1.1 = (1, 0) ∧ s'.1.1.1 = (1, 0)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Subtype.ext h.1, Subtype.ext h.2⟩),
        ite_eq_left h, one_mul]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h ⟨congrArg Subtype.val h'.1,
        congrArg Subtype.val h'.2⟩), ite_eq_right h, zero_mul]
  · -- step: without `e₁`, no path starts at `e₁`
    simp only [rootMoment, h₀, ↓reduceDIte]
    rw [sum_eq_zero fun path _ => ?_, mul_zero]
    rw [ite_eq_right fun h : (path 0).1.1.1 = (1, 0) ∧ _ => h₀ (h.1 ▸ (path 0).1.1.2), zero_mul,
      zero_mul]

/-- **S1, the path expansion**: with disjoint bands, the line average of the root moment is
`σ ∑_paths A⁰-weight ∏_p primeFactor_p`, over the paths of line-free states from `e₁` to
`e₁` with `N = 2R` edges. -/
theorem lineAverage_rootMoment_eq {q A₀ x : ℝ} (hq : 0 < q) {d : Data K} {Y d₀ u v r : ℝ}
    (hR : 0 < momentPower x) (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) :
    lineAverage x d (rootMoment q A₀ x d Y d₀ u v r) =
      (stateMass x d : ℂ) *
        ∑ path : Fin (2 * momentPower x + 1) → (freeRootModel d Y d₀ u v r).State x d,
          (if (path 0).1.1.1 = (1, 0) ∧ (path (Fin.last _)).1.1.1 = (1, 0) then (1 : ℂ) else 0) *
            pathWeight A₀ x d Y d₀ u v r path *
            ∏ p ∈ bandPrimes x d,
              (primeFactor p (2 * momentPower x) (pathLines p path)
                (dampDefect q (2 * momentPower x)) (activeSet p path) : ℂ) := by
  -- step: each `primeFactor` is the line average of `lineFactor`
  have hprime : ∀ path : Fin (2 * momentPower x + 1) → (freeRootModel d Y d₀ u v r).State x d,
      ∏ p ∈ bandPrimes x d, (primeFactor p (2 * momentPower x) (pathLines p path)
        (dampDefect q (2 * momentPower x)) (activeSet p path) : ℂ) =
      lineAverage x d fun ℓ => ∏ p ∈ bandPrimes x d, (lineFactor q p path (ℓ p) : ℂ) :=
    fun path => by
      rw [lineAverage_prod x d fun p l => (lineFactor q p path l : ℂ)]
      refine prod_congr rfl fun p _ => ?_
      rw [primeFactor_eq_sum_lineFactor]
      push_cast
      rfl
  -- step: average the path expansion at fixed lines
  rw [funext (rootMoment_eq_sum_lineFactor (A₀ := A₀) (d := d) (Y := Y) (d₀ := d₀) (u := u)
    (v := v) (r := r) hq hR hdisj)]
  simp only [hprime, lineAverage, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

end Erdos408.OneSided
