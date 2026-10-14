module

public import Erdos408.Grid

/-!
# Removal of the spare slot

`RectangleInput` allows an arbitrary coefficient only on the slots before the
last one. To weight one or two original primes arbitrarily, append a spare
prime `r` in the last slot and remove it by an exact positive defect, as in
*The normal order of the number of iterations of Euler's function* (Plasma AI,
2026), §3.

Let `δ = η = c / T²⁰`, where `c` comes from `RectangleInput`, and cut the
spare coordinate into cells `S_{j'} = (x^{δ + j' m}, x^{δ + (j' + 1) m}]`. For
an original tuple `Q` in the cell box `β`, call `j'` admissible if the upper
log coordinates of `β` plus `δ + (j' + 1) m` are at most `1 - η`, and put

  `w_{j'}(Q) = (δ + j' m) L / log(2x / Q)`,
  `Z_Q(n) = ∑_{j' admissible} ∑_{r ∈ S_{j'}, r ∣ n, r ∉ Q} w_{j'}(Q)`.

Since `(δ + j' m) L < log r` and the `r` are distinct prime factors of `n / Q`
with `n < 2x`, `0 ≤ Z_Q(n) ≤ 1` exactly. The weight `w_{j'}(Q)` depends only
on `Q`, so

* `∑_p ∑_{Q ∣ p - 1} B(Q) Z_Q(p - 1)` is a sum over boxes `β × S_{j'}` of
  rectangle statistics with coefficient `B(Q) w_{j'}(Q)`;
* `∑_p ∑_{Q ∣ p - 1} (1 - Z_Q(p - 1))` is controlled by the unweighted
  statistic of the region and the case `B = 1` of the previous item, and it
  bounds `|∑_p ∑_{Q ∣ p - 1} B(Q) (1 - Z_Q(p - 1))|`.

The harmonic model of `Z_Q` is
`A(Q) = ∑_{j'} w_{j'}(Q) ∑_{r ∈ S_{j'}, r ∉ Q} 1 / r`. Mertens' first theorem on
each spare cell, in the form `v ∑_{S_{j'}} 1 / r = m + O(1 / L + m ∑_{S_{j'}} 1 / r)`
with `v = δ + j' m`, and his second theorem on their union give
`|1 - A(Q)| ≪ (δ + m log(1 / δ) + 1 / (m L) + 1 / (m x^a)) / a ≤ T⁻¹⁰` for `Q`
in the region, since `1 - log Q / L ≥ a`. There are at most `4 T⁴⁰` boxes, each
with at most `2 T²⁰` spare cells and rectangle error `O(T⁻³⁰⁰)`, and the region
has harmonic mass `∑ 1 / Q ≤ 49 T²`, so the total error is `O(T⁻⁷)`.

The argument is carried out once, for an arbitrary family of boxes
(`SpareSlot.abs_sum_sigma_sub_le`), and then applied to the cells of `region₁`
and to the cell pairs of `region₂`.
-/

@[expose] public section

namespace Erdos408

open Finset Filter

namespace SpareSlot

/-! ### Grid cells and Mertens' theorems -/

/-- The primes `q` with `x^{b + j m} < q ≤ x^{b + (j + 1) m}`. -/
noncomputable def gridCell (x b m : ℝ) (j : ℕ) : Finset ℕ :=
  primesIoc (x ^ (b + j * m)) (x ^ (b + (j + 1) * m))

/-- A prime of `(x^u, x^v]` has `u L < log q ≤ v L`. -/
lemma log_bounds_of_mem {x u v : ℝ} (hx : 1 < x) {q : ℕ} (hq : q ∈ primesIoc (x ^ u) (x ^ v)) :
    u * Real.log x < Real.log q ∧ Real.log q ≤ v * Real.log x := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hp, hlt, hle⟩ := mem_primesIoc.1 hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.pos
  constructor
  · rw [← Real.log_rpow hx0]
    exact Real.log_lt_log (Real.rpow_pos_of_pos hx0 u) hlt
  · rw [← Real.log_rpow hx0]
    exact Real.log_le_log hq0 hle

/-- Distinct grid cells are disjoint. -/
lemma gridCell_disjoint {x b m : ℝ} (hx : 1 < x) (hm : 0 ≤ m) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (gridCell x b m i) (gridCell x b m j) := by
  have key : ∀ i j : ℕ, i < j → Disjoint (gridCell x b m i) (gridCell x b m j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro q hi hj
    obtain ⟨-, -, hi⟩ := mem_primesIoc.1 hi
    obtain ⟨-, hj, -⟩ := mem_primesIoc.1 hj
    have hij' : ((i : ℝ) + 1) ≤ j := by exact_mod_cast hij
    have := Real.rpow_le_rpow_of_exponent_le hx.le
      (show b + ((i : ℝ) + 1) * m ≤ b + j * m by nlinarith)
    linarith
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

/-- The first `J` grid cells lie in `(x^b, x^{b + J m}]`. -/
lemma biUnion_gridCell_subset {x b m : ℝ} (hx : 1 < x) (hm : 0 ≤ m) (J : ℕ) :
    (range J).biUnion (gridCell x b m) ⊆ primesIoc (x ^ b) (x ^ (b + J * m)) := by
  intro q hq
  obtain ⟨j, hj, hq⟩ := mem_biUnion.1 hq
  obtain ⟨hp, hlo, hhi⟩ := mem_primesIoc.1 hq
  have hj' : ((j : ℝ) + 1) ≤ J := by exact_mod_cast mem_range.1 hj
  refine mem_primesIoc.2 ⟨hp, lt_of_le_of_lt ?_ hlo, hhi.trans ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_le hx.le (by nlinarith [(j.cast_nonneg : (0:ℝ) ≤ j)])
  · exact Real.rpow_le_rpow_of_exponent_le hx.le (by nlinarith)

/-- A nonnegative sum over the first `J` grid cells is at most the sum over
`(x^b, x^{b + J m}]`. -/
lemma sum_gridCell_le {x b m : ℝ} (hx : 1 < x) (hm : 0 ≤ m) (J : ℕ) {f : ℕ → ℝ}
    (hf : ∀ q, 0 ≤ f q) :
    ∑ j ∈ range J, ∑ q ∈ gridCell x b m j, f q ≤
      ∑ q ∈ primesIoc (x ^ b) (x ^ (b + J * m)), f q := by
  rw [← sum_biUnion fun i _ j _ hij => gridCell_disjoint hx hm hij]
  exact sum_le_sum_of_subset_of_nonneg (biUnion_gridCell_subset hx hm J) fun q _ _ => hf q

/-- Elements of `primesIoc` are prime. -/
lemma prime_of_mem_primesIoc {y z : ℝ} {q : ℕ} (hq : q ∈ primesIoc y z) : q.Prime :=
  (mem_filter.1 hq).2

/-- Mertens' first theorem on `(x^u, x^v]`. -/
lemma mertens_first_rpow : ∃ E : ℝ, 0 ≤ E ∧ ∀ x u v : ℝ, 1 < x → 0 ≤ u → u ≤ v →
    |∑ p ∈ primesIoc (x ^ u) (x ^ v), Real.log p / p - (v - u) * Real.log x| ≤ E := by
  obtain ⟨E, hE, h⟩ := mertens_first
  refine ⟨E, hE, fun x u v hx hu huv => ?_⟩
  have hx0 : 0 < x := by linarith
  have := h (x ^ u) (x ^ v) (Real.one_le_rpow hx.le hu)
    (Real.rpow_le_rpow_of_exponent_le hx.le huv)
  rwa [← Real.rpow_sub hx0, Real.log_rpow hx0] at this

/-- Mertens' second theorem on `(x^u, x^v]`. -/
lemma mertens_second_rpow : ∃ E : ℝ, 0 ≤ E ∧ ∀ x u v : ℝ, 1 < x → 0 < u → u ≤ v →
    2 ≤ x ^ u →
    |∑ p ∈ primesIoc (x ^ u) (x ^ v), (1 : ℝ) / p - Real.log (v / u)| ≤
      E / (u * Real.log x) := by
  obtain ⟨E, hE, h⟩ := mertens_second
  refine ⟨E, hE, fun x u v hx hu huv h2 => ?_⟩
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have := h (x ^ u) (x ^ v) h2 (Real.rpow_le_rpow_of_exponent_le hx.le huv)
  rwa [Real.log_rpow hx0, Real.log_rpow hx0, mul_div_mul_right _ _ hL.ne'] at this

/-- On one cell `(x^v, x^{v + m}]`, `v ∑ 1 / r = m + O(1 / L + m ∑ 1 / r)`. -/
lemma abs_mul_sum_inv_sub_le {E : ℝ}
    (hE : ∀ x u v : ℝ, 1 < x → 0 ≤ u → u ≤ v →
      |∑ p ∈ primesIoc (x ^ u) (x ^ v), Real.log p / p - (v - u) * Real.log x| ≤ E)
    {x v m : ℝ} (hx : 1 < x) (hv : 0 ≤ v) (hm : 0 ≤ m) :
    |v * ∑ r ∈ primesIoc (x ^ v) (x ^ (v + m)), (1 : ℝ) / r - m| ≤
      E / Real.log x + m * ∑ r ∈ primesIoc (x ^ v) (x ^ (v + m)), (1 : ℝ) / r := by
  set S := primesIoc (x ^ v) (x ^ (v + m))
  set H := ∑ r ∈ S, (1 : ℝ) / r
  have hL : 0 < Real.log x := Real.log_pos hx
  have hG := hE x v (v + m) hx hv (by linarith)
  rw [add_sub_cancel_left] at hG
  have hpos : ∀ r ∈ S, (0 : ℝ) < r := fun r hr => by
    exact_mod_cast (prime_of_mem_primesIoc hr).pos
  -- `v L / r < log r / r ≤ (v + m) L / r` termwise
  have hlo : v * Real.log x * H ≤ ∑ r ∈ S, Real.log r / r := by
    rw [mul_sum]
    refine sum_le_sum fun r hr => ?_
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (log_bounds_of_mem hx hr).1.le (hpos r hr).le
  have hhi : ∑ r ∈ S, Real.log r / r ≤ (v + m) * Real.log x * H := by
    rw [mul_sum]
    refine sum_le_sum fun r hr => ?_
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (log_bounds_of_mem hx hr).2 (hpos r hr).le
  have hH : 0 ≤ H := sum_nonneg fun r hr => (one_div_pos.2 (hpos r hr)).le
  set G := ∑ r ∈ S, Real.log r / r
  rw [abs_le] at hG
  have h1 : (v * H - m) * Real.log x ≤ E / Real.log x * Real.log x := by
    rw [div_mul_cancel₀ _ hL.ne']
    nlinarith [hG.2]
  have h2 : (m - v * H - m * H) * Real.log x ≤ E / Real.log x * Real.log x := by
    rw [div_mul_cancel₀ _ hL.ne']
    nlinarith [hG.1]
  have h1' := le_of_mul_le_mul_right h1 hL
  have h2' := le_of_mul_le_mul_right h2 hL
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hm hH]

/-! ### The spare coordinate -/

/-- The spare offset `δ = η = c / T²⁰`. -/
noncomputable def spareOffset (c x : ℝ) : ℝ :=
  c / Real.log (Real.log x) ^ 20

/-- The spare cell `S_j = (x^{δ + j m}, x^{δ + (j + 1) m}]`. -/
noncomputable def spareCell (c x : ℝ) (j : ℕ) : Finset ℕ :=
  gridCell x (spareOffset c x) (mesh x) j

/-- The number `⌊(1 - 2δ - s) / m⌋` of spare cells admissible above the upper log
coordinate `s`. -/
noncomputable def spareCount (c x s : ℝ) : ℕ :=
  ⌊(1 - 2 * spareOffset c x - s) / mesh x⌋₊

/-- The spare weight `w_j(V) = (δ + j m) L / log(2x / V)`. -/
noncomputable def spareWeight (c x : ℝ) (V j : ℕ) : ℝ :=
  (spareOffset c x + j * mesh x) * Real.log x / Real.log (2 * x / V)

/-- The spare kernel `Z_X(n) = ∑_j ∑_{r ∈ S_j, r ∉ X, r ∣ n} w_j(∏ X)`. -/
noncomputable def spareKernel (c x s : ℝ) (X : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ range (spareCount c x s), ∑ r ∈ spareCell c x j with r ∉ X ∧ r ∣ n,
    spareWeight c x (∏ q ∈ X, q) j

/-- The harmonic model `A(X) = ∑_j w_j(∏ X) ∑_{r ∈ S_j, r ∉ X} 1 / r` of the kernel. -/
noncomputable def spareModel (c x s : ℝ) (X : Finset ℕ) : ℝ :=
  ∑ j ∈ range (spareCount c x s), spareWeight c x (∏ q ∈ X, q) j *
    ∑ r ∈ spareCell c x j with r ∉ X, (1 : ℝ) / r

/-- An original tuple with prime set `X` in a box with upper log coordinate `s`:
at most two primes above `x^a`, with `log ∏ X / L ∈ (s - 2m, s]` and `s ≤ 1 - a`. -/
def Admissible (x s : ℝ) (X : Finset ℕ) : Prop :=
  0 ≤ s ∧ s ≤ 1 - margin x ∧ X.card ≤ 2 ∧ (∀ q ∈ X, q.Prime ∧ x ^ margin x < q) ∧
    s - 2 * mesh x < Real.log (∏ q ∈ X, q : ℕ) / Real.log x ∧
      Real.log (∏ q ∈ X, q : ℕ) / Real.log x ≤ s

/-- `log(2x / V) = (1 - log V / L + log 2 / L) L`. -/
lemma log_two_mul_div {x : ℝ} (hx : 1 < x) {V : ℕ} (hV : 0 < V) :
    Real.log (2 * x / V) =
      (1 - Real.log V / Real.log x + Real.log 2 / Real.log x) * Real.log x := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hV' : (0 : ℝ) < V := by exact_mod_cast hV
  rw [Real.log_div (by positivity) hV'.ne', Real.log_mul two_ne_zero (by positivity)]
  field_simp
  ring

/-- The spare weight is `(δ + j m) / (1 - log V / L + log 2 / L)`. -/
lemma spareWeight_eq {c x : ℝ} (hx : 1 < x) {V : ℕ} (hV : 0 < V) (j : ℕ) :
    spareWeight c x V j = (spareOffset c x + j * mesh x) /
      (1 - Real.log V / Real.log x + Real.log 2 / Real.log x) := by
  rw [spareWeight, log_two_mul_div hx hV, mul_div_mul_right _ _ (Real.log_pos hx).ne']

/-- The spare cells are the grid cells of `(x^δ, x^{δ + J m}]`. -/
lemma spareCell_eq (c x : ℝ) (j : ℕ) : spareCell c x j =
    primesIoc (x ^ (spareOffset c x + j * mesh x))
      (x ^ (spareOffset c x + j * mesh x + mesh x)) := by
  rw [spareCell, gridCell, add_one_mul, add_assoc]

/-- The defect `|1 - A(X)|` of the harmonic model, before inserting the sizes of
`a`, `m` and `δ`. -/
lemma abs_one_sub_spareModel_le : ∃ E₁ E₂ : ℝ, 0 ≤ E₁ ∧ 0 ≤ E₂ ∧ ∀ c x s : ℝ,
    ∀ X : Finset ℕ, 1 < x → 0 < mesh x → 0 < spareOffset c x →
      2 ≤ x ^ spareOffset c x → 2 * spareOffset c x ≤ margin x → Admissible x s X →
      |1 - spareModel c x s X| ≤ (2 * spareOffset c x + 3 * mesh x +
        Real.log 2 / Real.log x + E₁ / (mesh x * Real.log x) +
        mesh x * (Real.log (1 / spareOffset c x) + E₂ / (spareOffset c x * Real.log x)) +
        2 / (mesh x * x ^ margin x)) / margin x := by
  obtain ⟨E₁, hE₁, h₁⟩ := mertens_first_rpow
  obtain ⟨E₂, hE₂, h₂⟩ := mertens_second_rpow
  refine ⟨E₁, E₂, hE₁, hE₂, fun c x s X hx hm hδ h2 hδa hadm => ?_⟩
  obtain ⟨hs0, hs1, hcard, hX, htlo, hthi⟩ := hadm
  set L := Real.log x
  set a := margin x
  set m := mesh x
  set δ := spareOffset c x
  set J := spareCount c x s
  set V := ∏ q ∈ X, q
  set t := Real.log V / L
  set D := 1 - t + Real.log 2 / L
  have hL : 0 < L := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have ha : 0 < a := by linarith
  have hV : 0 < V := prod_pos fun q hq => (hX q hq).1.pos
  have hDa : a ≤ D := by
    have := div_nonneg (Real.log_nonneg one_le_two) hL.le
    linarith
  have hD : 0 < D := ha.trans_le hDa
  -- floor facts for `J`
  have hy : 0 ≤ (1 - 2 * δ - s) / m := div_nonneg (by linarith) hm.le
  have hJle : (J : ℝ) * m ≤ 1 - 2 * δ - s := (le_div_iff₀ hm).1 (Nat.floor_le hy)
  have hJgt : 1 - 2 * δ - s < (J + 1) * m := (div_lt_iff₀ hm).1 (Nat.lt_floor_add_one _)
  have hJm : (J : ℝ) ≤ 1 / m := by rw [le_div_iff₀ hm]; linarith
  -- the model as `(G - G') / D`
  set H : ℕ → ℝ := fun j => ∑ r ∈ spareCell c x j, (1 : ℝ) / r
  set H' : ℕ → ℝ := fun j => ∑ r ∈ spareCell c x j with r ∈ X, (1 : ℝ) / r
  set G := ∑ j ∈ range J, (δ + j * m) * H j
  set G' := ∑ j ∈ range J, (δ + j * m) * H' j
  have hA : spareModel c x s X = (G - G') / D := by
    rw [spareModel, ← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun j _ => ?_
    rw [spareWeight_eq hx hV]
    change (δ + j * m) / D * _ = _
    simp only [H, H']
    rw [← sum_filter_add_sum_filter_not (spareCell c x j) (· ∈ X)]
    ring
  -- `|D - J m| ≤ 2δ + 3m + log 2 / L`
  have hDJ : |D - J * m| ≤ 2 * δ + 3 * m + Real.log 2 / L := by
    have := div_nonneg (Real.log_nonneg one_le_two) hL.le
    rw [abs_le]
    constructor <;> nlinarith
  -- `|J m - G| ≤ E₁ / (m L) + m (log (1 / δ) + E₂ / (δ L))`
  have hH0 : ∀ j, 0 ≤ H j := fun j => sum_nonneg fun r _ => by positivity
  have hsumH : ∑ j ∈ range J, H j ≤ Real.log (1 / δ) + E₂ / (δ * L) := by
    have hJδ : δ ≤ δ + J * m := by have := J.cast_nonneg (α := ℝ); nlinarith
    have hM := (abs_le.1 (h₂ x δ (δ + J * m) hx hδ hJδ h2)).2
    have hlog : Real.log ((δ + J * m) / δ) ≤ Real.log (1 / δ) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith) hδ.le)
    have := sum_gridCell_le hx hm.le J (b := δ) (f := fun r => (1 : ℝ) / r)
      fun r => by positivity
    change ∑ j ∈ range J, ∑ r ∈ gridCell x δ m j, (1 : ℝ) / r ≤ _
    linarith
  have hvj : ∀ j ∈ range J, 0 ≤ δ + j * m ∧ δ + j * m ≤ 1 := fun j hj => by
    have : (j : ℝ) ≤ J := by exact_mod_cast (mem_range.1 hj).le
    constructor <;> nlinarith [j.cast_nonneg (α := ℝ)]
  have hGJ : |J * m - G| ≤ E₁ / (m * L) + m * (Real.log (1 / δ) + E₂ / (δ * L)) := by
    have hcell : ∀ j ∈ range J, |(δ + j * m) * H j - m| ≤ E₁ / L + m * H j := by
      intro j hj
      simp only [H, spareCell_eq]
      exact abs_mul_sum_inv_sub_le h₁ hx (hvj j hj).1 hm.le
    have hJ' : J * (E₁ / L) ≤ E₁ / (m * L) := by
      calc (J : ℝ) * (E₁ / L) ≤ 1 / m * (E₁ / L) := by gcongr
        _ = E₁ / (m * L) := by field_simp
    calc |J * m - G| = |∑ j ∈ range J, ((δ + j * m) * H j - m)| := by
          rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, abs_sub_comm]
      _ ≤ ∑ j ∈ range J, (E₁ / L + m * H j) :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum hcell)
      _ = J * (E₁ / L) + m * ∑ j ∈ range J, H j := by
          rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_sum]
      _ ≤ _ := by gcongr
  -- `0 ≤ G' ≤ 2 / (m x^a)`, the excluded primes of `X`
  have hH' : ∀ j, 0 ≤ H' j ∧ H' j ≤ 2 / x ^ a := fun j => by
    refine ⟨sum_nonneg fun r _ => by positivity, ?_⟩
    calc H' j ≤ ∑ r ∈ X, (1 : ℝ) / r :=
          sum_le_sum_of_subset_of_nonneg (fun r hr => (mem_filter.1 hr).2)
            fun r _ _ => by positivity
      _ ≤ X.card • (1 / x ^ a) := sum_le_card_nsmul _ _ _ fun r hr =>
          one_div_le_one_div_of_le (by positivity) (hX r hr).2.le
      _ ≤ 2 / x ^ a := by
          rw [nsmul_eq_mul, mul_one_div]
          gcongr
          exact_mod_cast hcard
  have hG' : 0 ≤ G' ∧ G' ≤ 2 / (m * x ^ a) := by
    refine ⟨sum_nonneg fun j hj => mul_nonneg (hvj j hj).1 (hH' j).1, ?_⟩
    calc G' ≤ ∑ j ∈ range J, 1 * (2 / x ^ a) :=
          sum_le_sum fun j hj => mul_le_mul (hvj j hj).2 (hH' j).2 (hH' j).1 zero_le_one
      _ = J * (2 / x ^ a) := by rw [sum_const, card_range, nsmul_eq_mul, one_mul]
      _ ≤ 1 / m * (2 / x ^ a) := by gcongr
      _ = 2 / (m * x ^ a) := by field_simp
  rw [hA, show 1 - (G - G') / D = (D - G + G') / D by field_simp; ring,
    abs_div, abs_of_pos hD]
  have hnum : |D - G + G'| ≤ |D - J * m| + |J * m - G| + G' := by
    calc |D - G + G'| ≤ |D - J * m + (J * m - G)| + |G'| := by
          rw [show D - G + G' = D - J * m + (J * m - G) + G' by ring]
          exact abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg hG'.1]; gcongr; exact abs_add_le _ _
  calc |D - G + G'| / D ≤ |D - G + G'| / a :=
        div_le_div_of_nonneg_left (abs_nonneg _) ha hDa
    _ ≤ _ := by gcongr; linarith

/-- For admissible `X` and `j < J`, the spare weight lies in `[0, 1]`. -/
lemma spareWeight_mem_Icc {c x s : ℝ} {X : Finset ℕ} (hx : 1 < x) (hm : 0 < mesh x)
    (hδ : 0 < spareOffset c x) (hδa : 2 * spareOffset c x ≤ margin x)
    (hadm : Admissible x s X) {j : ℕ} (hj : j < spareCount c x s) :
    0 ≤ spareWeight c x (∏ q ∈ X, q) j ∧ spareWeight c x (∏ q ∈ X, q) j ≤ 1 := by
  obtain ⟨hs0, hs1, -, hX, -, hthi⟩ := hadm
  have hL : 0 < Real.log x := Real.log_pos hx
  have hV : 0 < ∏ q ∈ X, q := prod_pos fun q hq => (hX q hq).1.pos
  have h2 := div_nonneg (Real.log_nonneg one_le_two) hL.le
  have hy : 0 ≤ (1 - 2 * spareOffset c x - s) / mesh x := div_nonneg (by linarith) hm.le
  have hJle := (le_div_iff₀ hm).1 (Nat.floor_le hy)
  have hj' : (j : ℝ) + 1 ≤ ⌊(1 - 2 * spareOffset c x - s) / mesh x⌋₊ := by
    exact_mod_cast hj
  rw [spareWeight_eq hx hV]
  have hD : spareOffset c x + j * mesh x ≤
      1 - Real.log (∏ q ∈ X, q : ℕ) / Real.log x + Real.log 2 / Real.log x := by
    nlinarith
  exact ⟨div_nonneg (by positivity) (by linarith), div_le_one_of_le₀ hD (by linarith)⟩

/-- For primes `r ∉ X`, `(∏ X) r ∣ n` iff `∏ X ∣ n` and `r ∣ n`. -/
lemma prod_mul_dvd_iff {X : Finset ℕ} (hX : ∀ q ∈ X, q.Prime) {r : ℕ} (hr : r.Prime)
    (hrX : r ∉ X) {n : ℕ} : (∏ q ∈ X, q) * r ∣ n ↔ (∏ q ∈ X, q) ∣ n ∧ r ∣ n := by
  refine ⟨fun h => ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩,
    fun ⟨h₁, h₂⟩ => Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ h₁ h₂⟩
  exact Nat.Coprime.prod_left fun q hq =>
    (Nat.coprime_primes (hX q hq) hr).2 fun h => hrX (h ▸ hq)

/-- `0 ≤ Z_X(n) ≤ 1` exactly when `∏ X ∣ n < 2x`: the spare primes are distinct prime
factors of `n / ∏ X` with `(δ + j m) L < log r`. -/
lemma spareKernel_mem_Icc {c x s : ℝ} (hx : 1 < x) (hδ : 0 ≤ spareOffset c x)
    (hm : 0 ≤ mesh x) {X : Finset ℕ} (hX : ∀ q ∈ X, q.Prime) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℝ) < 2 * x) (hXn : (∏ q ∈ X, q) ∣ n) :
    0 ≤ spareKernel c x s X n ∧ spareKernel c x s X n ≤ 1 := by
  set V := ∏ q ∈ X, q
  set J := spareCount c x s
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hV : 0 < V := prod_pos fun q hq => (hX q hq).pos
  have hV' : (0 : ℝ) < V := by exact_mod_cast hV
  have hVn : (V : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd hn0 hXn
  have hℓ : 0 < Real.log (2 * x / V) :=
    Real.log_pos ((one_lt_div hV').2 (hVn.trans_lt hn))
  set F : ℕ → Finset ℕ := fun j => (spareCell c x j).filter fun r => r ∉ X ∧ r ∣ n
  refine ⟨sum_nonneg fun j _ => sum_nonneg fun r _ =>
    div_nonneg (mul_nonneg (by positivity) hL.le) hℓ.le, ?_⟩
  -- termwise `w_j ≤ log r / log(2x / V)`
  have hterm : ∀ j, ∀ r ∈ F j, spareWeight c x V j ≤ Real.log r / Real.log (2 * x / V) := by
    intro j r hr
    have hr' := (mem_filter.1 hr).1
    rw [spareCell_eq] at hr'
    exact div_le_div_of_nonneg_right (log_bounds_of_mem hx hr').1.le hℓ.le
  set R := (range J).biUnion F
  have hdisj : (↑(range J) : Set ℕ).PairwiseDisjoint F := fun i _ j _ hij =>
    (gridCell_disjoint hx hm hij).mono (filter_subset _ _) (filter_subset _ _)
  have hRX : Disjoint R X := disjoint_left.2 fun r hr hrX => by
    obtain ⟨j, _, hr⟩ := mem_biUnion.1 hr
    exact (mem_filter.1 hr).2.1 hrX
  have hR : ∀ r ∈ R, r.Prime ∧ r ∣ n := fun r hr => by
    obtain ⟨j, _, hr⟩ := mem_biUnion.1 hr
    exact ⟨prime_of_mem_primesIoc (mem_filter.1 hr).1, (mem_filter.1 hr).2.2⟩
  have hdvd : (∏ r ∈ R ∪ X, r) ∣ n := by
    refine prod_primes_dvd n (fun r hr => ?_) fun r hr => ?_
    · rcases mem_union.1 hr with hr | hr
      exacts [(hR r hr).1.prime, (hX r hr).prime]
    · rcases mem_union.1 hr with hr | hr
      exacts [(hR r hr).2, (dvd_prod_of_mem _ hr).trans hXn]
  rw [prod_union hRX] at hdvd
  have hRpos : 0 < ∏ r ∈ R, r := prod_pos fun r hr => (hR r hr).1.pos
  have hlog : Real.log (∏ r ∈ R, r : ℕ) ≤ Real.log (2 * x / V) := by
    refine Real.log_le_log (by exact_mod_cast hRpos) ?_
    rw [le_div_iff₀ hV']
    have : ((∏ r ∈ R, r : ℕ) : ℝ) * V ≤ n := by exact_mod_cast Nat.le_of_dvd hn0 hdvd
    linarith
  calc spareKernel c x s X n
      ≤ ∑ j ∈ range J, ∑ r ∈ F j, Real.log r / Real.log (2 * x / V) :=
        sum_le_sum fun j _ => sum_le_sum (hterm j)
    _ = ∑ r ∈ R, Real.log r / Real.log (2 * x / V) := (sum_biUnion hdisj).symm
    _ = Real.log (∏ r ∈ R, r : ℕ) / Real.log (2 * x / V) := by
        rw [← sum_div]
        simp only [Nat.cast_prod]
        rw [Real.log_prod fun r hr => by
          exact_mod_cast (hR r hr).1.ne_zero]
    _ ≤ 1 := div_le_one_of_le₀ hlog hℓ.le

/-! ### Removing the kernel -/

/-- The combination step of the spare-slot removal: the statistics of `B Z` and `Z`,
the unweighted statistic and the defect `∑ |1 - A| / V` control the statistic of `B`,
since `0 ≤ 1 - Z ≤ 1` and `|B| ≤ 1`. -/
lemma abs_sum_sub_le_of_kernel {β : Type*} (P : Finset ℕ) (D : Finset β)
    (dv : ℕ → β → Prop) [∀ p Q, Decidable (dv p Q)] (B A V : β → ℝ) (Z : ℕ → β → ℝ)
    {ε₁ ε₀ ε₂ : ℝ} (hB : ∀ Q, |B Q| ≤ 1) (hV : ∀ Q ∈ D, 0 < V Q)
    (hZ : ∀ p ∈ P, ∀ Q ∈ D, dv p Q → 0 ≤ Z p Q ∧ Z p Q ≤ 1)
    (h₁ : |∑ p ∈ P, ∑ Q ∈ D with dv p Q, B Q * Z p Q -
      P.card * ∑ Q ∈ D, B Q * A Q / V Q| ≤ P.card * ε₁)
    (h₁' : |∑ p ∈ P, ∑ Q ∈ D with dv p Q, Z p Q - P.card * ∑ Q ∈ D, A Q / V Q| ≤
      P.card * ε₁)
    (h₀ : |∑ p ∈ P, ∑ Q ∈ D with dv p Q, (1 : ℝ) - P.card * ∑ Q ∈ D, 1 / V Q| ≤
      P.card * ε₀)
    (h₂ : ∑ Q ∈ D, |1 - A Q| / V Q ≤ ε₂) :
    |∑ p ∈ P, ∑ Q ∈ D with dv p Q, B Q - P.card * ∑ Q ∈ D, B Q / V Q| ≤
      P.card * (2 * ε₁ + ε₀ + 2 * ε₂) := by
  have hN : (0 : ℝ) ≤ P.card := P.card.cast_nonneg
  -- `B = B Z + B (1 - Z)`
  have hsplit : ∑ p ∈ P, ∑ Q ∈ D with dv p Q, B Q =
      ∑ p ∈ P, ∑ Q ∈ D with dv p Q, B Q * Z p Q +
        ∑ p ∈ P, ∑ Q ∈ D with dv p Q, B Q * (1 - Z p Q) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun p _ => by rw [← sum_add_distrib]; exact sum_congr rfl fun Q _ => by ring
  -- `|∑ B (1 - Z)| ≤ ∑ (1 - Z) = ∑ 1 - ∑ Z`
  have hrest : |∑ p ∈ P, ∑ Q ∈ D with dv p Q, B Q * (1 - Z p Q)| ≤
      ∑ p ∈ P, ∑ Q ∈ D with dv p Q, (1 : ℝ) - ∑ p ∈ P, ∑ Q ∈ D with dv p Q, Z p Q := by
    simp only [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp => ?_)
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun Q hQ => ?_)
    obtain ⟨hQ, hdv⟩ := mem_filter.1 hQ
    obtain ⟨hZ0, hZ1⟩ := hZ p hp Q hQ hdv
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - Z p Q)]
    nlinarith [hB Q]
  -- the model defect
  have hmodel : |∑ Q ∈ D, B Q * A Q / V Q - ∑ Q ∈ D, B Q / V Q| ≤ ε₂ := by
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun Q hQ => ?_).trans h₂)
    rw [show B Q * A Q / V Q - B Q / V Q = B Q * (A Q - 1) / V Q by ring, abs_div,
      abs_of_pos (hV Q hQ), abs_mul, abs_sub_comm]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_left (abs_nonneg _) (hB Q)) (hV Q hQ).le
  have hdef : ∑ Q ∈ D, 1 / V Q - ∑ Q ∈ D, A Q / V Q ≤ ε₂ := by
    rw [← sum_sub_distrib]
    refine (sum_le_sum fun Q hQ => ?_).trans h₂
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (le_abs_self _) (hV Q hQ).le
  rw [abs_le] at h₁ h₁' h₀ hrest hmodel ⊢
  have := mul_le_mul_of_nonneg_left hdef hN
  rw [hsplit]
  constructor <;> nlinarith

/-- A filtered sum over `s.sigma t` as an iterated filtered sum. -/
lemma sum_sigma_filter {ι α : Type*} (s : Finset ι) (t : ι → Finset α)
    (p : (_ : ι) × α → Prop) [DecidablePred p] (f : (_ : ι) × α → ℝ) :
    ∑ z ∈ s.sigma t with p z, f z = ∑ i ∈ s, ∑ b ∈ t i with p ⟨i, b⟩, f ⟨i, b⟩ := by
  simp only [sum_filter, sum_sigma]

/-- The kernel identity on one box: `∑_{Q ∣ n} B(Q) Z_Q(n)` is the sum over the spare
cells of the box-times-cell tuples dividing `n`, weighted by `B(Q) w_j(Q)`. -/
lemma sum_mul_spareKernel {α : Type*} {c x s : ℝ} (box : Finset α) (X : α → Finset ℕ)
    (hX : ∀ Q ∈ box, ∀ q ∈ X Q, q.Prime) (b : α → ℝ) (n : ℕ) :
    ∑ Q ∈ box with (∏ q ∈ X Q, q) ∣ n, b Q * spareKernel c x s (X Q) n =
      ∑ j ∈ range (spareCount c x s), ∑ Q ∈ box,
        ∑ r ∈ spareCell c x j with r ∉ X Q ∧ (∏ q ∈ X Q, q) * r ∣ n,
          b Q * spareWeight c x (∏ q ∈ X Q, q) j := by
  rw [sum_comm, sum_filter]
  refine sum_congr rfl fun Q hQ => ?_
  split_ifs with h
  · rw [spareKernel, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr (filter_congr fun r hr => ?_) fun _ _ => rfl
    have hr := prime_of_mem_primesIoc hr
    constructor
    · exact fun ⟨hrX, hrn⟩ => ⟨hrX, (prod_mul_dvd_iff (hX Q hQ) hr hrX).2 ⟨h, hrn⟩⟩
    · exact fun ⟨hrX, hrn⟩ => ⟨hrX, ((prod_mul_dvd_iff (hX Q hQ) hr hrX).1 hrn).2⟩
  · refine (sum_eq_zero fun j _ => sum_eq_zero fun r hr => ?_).symm
    exact absurd ((dvd_mul_right _ _).trans (mem_filter.1 hr).2.2) h

/-- The model identity on one box: `∑_Q B(Q) A(Q) / Q` is the harmonic sum over the
spare cells of `B(Q) w_j(Q) / (Q r)`. -/
lemma sum_mul_spareModel {α : Type*} {c x s : ℝ} (box : Finset α) (X : α → Finset ℕ)
    (b : α → ℝ) :
    ∑ Q ∈ box, b Q * spareModel c x s (X Q) / (∏ q ∈ X Q, q : ℕ) =
      ∑ j ∈ range (spareCount c x s), ∑ Q ∈ box, ∑ r ∈ spareCell c x j with r ∉ X Q,
        b Q * spareWeight c x (∏ q ∈ X Q, q) j / ((∏ q ∈ X Q, q : ℕ) * r) := by
  rw [sum_comm]
  refine sum_congr rfl fun Q _ => ?_
  rw [spareModel, mul_sum, sum_div]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum, mul_sum, sum_div]
  refine sum_congr rfl fun r _ => ?_
  ring

/-- The spare-slot removal over a family of boxes: if the rectangle statistic holds on
every box times every admissible spare cell with coefficients on the box, and holds
unweighted on every box, then the weighted statistic holds on the union of the boxes. -/
lemma abs_sum_sigma_sub_le {ι α : Type*} [DecidableEq α] {c x ε₁ ε₂ M Jmax : ℝ}
    (P : Finset ℕ) (boxes : Finset ι) (box : ι → Finset α) (X : α → Finset ℕ) (s : ι → ℝ)
    (hx : 1 < x) (hm : 0 < mesh x) (hδ : 0 < spareOffset c x)
    (hδa : 2 * spareOffset c x ≤ margin x)
    (hP : ∀ p ∈ P, 0 < p - 1 ∧ ((p - 1 : ℕ) : ℝ) < 2 * x)
    (hadm : ∀ β ∈ boxes, ∀ Q ∈ box β, Admissible x (s β) (X Q))
    (hA : ∀ β ∈ boxes, ∀ Q ∈ box β, |1 - spareModel c x (s β) (X Q)| ≤ ε₂)
    (hJ : ∀ β ∈ boxes, (spareCount c x (s β) : ℝ) ≤ Jmax)
    (hmass : ∑ β ∈ boxes, ∑ Q ∈ box β, (1 : ℝ) / (∏ q ∈ X Q, q : ℕ) ≤ M)
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (h₁ : ∀ β ∈ boxes, ∀ j < spareCount c x (s β), ∀ b : α → ℝ, (∀ Q, |b Q| ≤ 1) →
      |∑ p ∈ P, ∑ Q ∈ box β,
          ∑ r ∈ spareCell c x j with r ∉ X Q ∧ (∏ q ∈ X Q, q) * r ∣ p - 1, b Q -
        P.card * ∑ Q ∈ box β, ∑ r ∈ spareCell c x j with r ∉ X Q,
          b Q / ((∏ q ∈ X Q, q : ℕ) * r)| ≤ P.card * ε₁)
    (h₀ : ∀ β ∈ boxes, |∑ p ∈ P, ∑ Q ∈ box β with (∏ q ∈ X Q, q) ∣ p - 1, (1 : ℝ) -
        P.card * ∑ Q ∈ box β, (1 : ℝ) / (∏ q ∈ X Q, q : ℕ)| ≤ P.card * ε₁)
    (B : α → ℝ) (hB : ∀ Q, |B Q| ≤ 1) :
    |∑ p ∈ P, ∑ z ∈ boxes.sigma box with (∏ q ∈ X z.2, q) ∣ p - 1, B z.2 -
        P.card * ∑ z ∈ boxes.sigma box, B z.2 / (∏ q ∈ X z.2, q : ℕ)| ≤
      P.card * (2 * (boxes.card * Jmax * ε₁) + boxes.card * ε₁ + 2 * (M * ε₂)) := by
  have hN : (0 : ℝ) ≤ P.card := P.card.cast_nonneg
  have hX : ∀ β ∈ boxes, ∀ Q ∈ box β, ∀ q ∈ X Q, q.Prime := fun β hβ Q hQ q hq =>
    ((hadm β hβ Q hQ).2.2.2.1 q hq).1
  have hV : ∀ z ∈ boxes.sigma box, (0 : ℝ) < (∏ q ∈ X z.2, q : ℕ) := fun z hz => by
    obtain ⟨hβ, hQ⟩ := mem_sigma.1 hz
    exact_mod_cast prod_pos fun q hq => (hX _ hβ _ hQ q hq).pos
  -- the kernel statistic for every coefficient on the boxes
  have hw : ∀ B' : (_ : ι) × α → ℝ, (∀ z, |B' z| ≤ 1) →
      |∑ p ∈ P, ∑ z ∈ boxes.sigma box with (∏ q ∈ X z.2, q) ∣ p - 1,
          B' z * spareKernel c x (s z.1) (X z.2) (p - 1) -
        P.card * ∑ z ∈ boxes.sigma box,
          B' z * spareModel c x (s z.1) (X z.2) / (∏ q ∈ X z.2, q : ℕ)| ≤
        P.card * (boxes.card * Jmax * ε₁) := by
    intro B' hB'
    -- the box coefficients `b_{β j}(Q) = B'(β, Q) w_j(Q)`
    obtain ⟨b, hbdef⟩ : ∃ b : ι → ℕ → α → ℝ, b = fun β j Q =>
        if Q ∈ box β then B' ⟨β, Q⟩ * spareWeight c x (∏ q ∈ X Q, q) j else 0 := ⟨_, rfl⟩
    have hb : ∀ β ∈ boxes, ∀ j < spareCount c x (s β), ∀ Q, |b β j Q| ≤ 1 := by
      intro β hβ j hj Q
      simp only [hbdef]
      split_ifs with hQ
      · obtain ⟨h0, h1⟩ := spareWeight_mem_Icc hx hm hδ hδa (hadm β hβ Q hQ) hj
        rw [abs_mul, abs_of_nonneg h0]
        exact (mul_le_mul (hB' _) h1 h0 zero_le_one).trans_eq (one_mul 1)
      · simp
    have hlhs : ∑ p ∈ P, ∑ z ∈ boxes.sigma box with (∏ q ∈ X z.2, q) ∣ p - 1,
          B' z * spareKernel c x (s z.1) (X z.2) (p - 1) =
        ∑ β ∈ boxes, ∑ j ∈ range (spareCount c x (s β)), ∑ p ∈ P, ∑ Q ∈ box β,
          ∑ r ∈ spareCell c x j with r ∉ X Q ∧ (∏ q ∈ X Q, q) * r ∣ p - 1, b β j Q := by
      calc _ = ∑ p ∈ P, ∑ β ∈ boxes, ∑ j ∈ range (spareCount c x (s β)), ∑ Q ∈ box β,
            ∑ r ∈ spareCell c x j with r ∉ X Q ∧ (∏ q ∈ X Q, q) * r ∣ p - 1, b β j Q := by
            refine sum_congr rfl fun p _ => ?_
            rw [sum_sigma_filter]
            refine sum_congr rfl fun β hβ => ?_
            dsimp only
            refine (sum_mul_spareKernel (c := c) (x := x) (s := s β) (box β) X (hX β hβ)
              (fun Q => B' ⟨β, Q⟩) (p - 1)).trans ?_
            refine sum_congr rfl fun j _ => sum_congr rfl fun Q hQ =>
              sum_congr rfl fun r _ => ?_
            simp only [hbdef, hQ, ↓reduceIte]
        _ = _ := by
            rw [sum_comm]
            exact sum_congr rfl fun β _ => sum_comm
    have hrhs : (P.card : ℝ) * ∑ z ∈ boxes.sigma box,
          B' z * spareModel c x (s z.1) (X z.2) / (∏ q ∈ X z.2, q : ℕ) =
        ∑ β ∈ boxes, ∑ j ∈ range (spareCount c x (s β)), P.card * ∑ Q ∈ box β,
          ∑ r ∈ spareCell c x j with r ∉ X Q, b β j Q / ((∏ q ∈ X Q, q : ℕ) * r) := by
      rw [sum_sigma, mul_sum]
      refine sum_congr rfl fun β _ => ?_
      rw [← mul_sum]
      congr 1
      dsimp only
      refine (sum_mul_spareModel (c := c) (x := x) (s := s β) (box β) X
        (fun Q => B' ⟨β, Q⟩)).trans ?_
      refine sum_congr rfl fun j _ => sum_congr rfl fun Q hQ => sum_congr rfl fun r _ => ?_
      simp only [hbdef, hQ, ↓reduceIte]
    rw [hlhs, hrhs]
    simp only [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ β ∈ boxes, ∑ j ∈ range (spareCount c x (s β)), (P.card * ε₁ : ℝ) :=
          sum_le_sum fun β hβ => (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj =>
            h₁ β hβ j (mem_range.1 hj) (b β j) (hb β hβ j (mem_range.1 hj)))
      _ ≤ ∑ β ∈ boxes, Jmax * (P.card * ε₁) := sum_le_sum fun β hβ => by
          rw [sum_const, card_range, nsmul_eq_mul]
          gcongr
          exact hJ β hβ
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
  have h₁' := hw (fun _ => 1) fun _ => by simp
  simp only [one_mul] at h₁'
  -- the unweighted statistic, box by box
  have h₀' : |∑ p ∈ P, ∑ z ∈ boxes.sigma box with (∏ q ∈ X z.2, q) ∣ p - 1, (1 : ℝ) -
      P.card * ∑ z ∈ boxes.sigma box, (1 : ℝ) / (∏ q ∈ X z.2, q : ℕ)| ≤
        P.card * (boxes.card * ε₁) := by
    rw [sum_sigma, mul_sum]
    simp only [sum_sigma_filter]
    rw [sum_comm (s := P), ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ β ∈ boxes, (P.card * ε₁ : ℝ) := sum_le_sum fun β hβ => h₀ β hβ
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
  -- the defect
  have h₂ : ∑ z ∈ boxes.sigma box,
      |1 - spareModel c x (s z.1) (X z.2)| / (∏ q ∈ X z.2, q : ℕ) ≤ M * ε₂ := by
    calc _ ≤ ∑ z ∈ boxes.sigma box, ε₂ * (1 / (∏ q ∈ X z.2, q : ℕ)) :=
          sum_le_sum fun z hz => by
            obtain ⟨hβ, hQ⟩ := mem_sigma.1 hz
            rw [mul_one_div]
            exact div_le_div_of_nonneg_right (hA _ hβ _ hQ) (hV z hz).le
      _ = ε₂ * ∑ β ∈ boxes, ∑ Q ∈ box β, (1 : ℝ) / (∏ q ∈ X Q, q : ℕ) := by
          rw [← mul_sum, sum_sigma]
      _ ≤ M * ε₂ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hmass hε₂
  exact abs_sum_sub_le_of_kernel P (boxes.sigma box) (fun p z => (∏ q ∈ X z.2, q) ∣ p - 1)
    (fun z => B z.2) (fun z => spareModel c x (s z.1) (X z.2))
    (fun z => ((∏ q ∈ X z.2, q : ℕ) : ℝ)) (fun p z => spareKernel c x (s z.1) (X z.2) (p - 1))
    (fun z => hB z.2) hV (fun p hp z hz hdv => spareKernel_mem_Icc hx hδ.le hm.le
      (hX _ (mem_sigma.1 hz).1 _ (mem_sigma.1 hz).2) (hP p hp).1 (hP p hp).2 hdv)
    (hw _ fun z => hB z.2) h₁' h₀' h₂

/-! ### The rectangle statistic in product form -/

/-- The slot of `slotTuples` is `primesIoc`. -/
lemma filter_Iic_eq_primesIoc {y : ℝ} (hy : 0 ≤ y) (z : ℝ) :
    (Iic ⌊z⌋₊).filter (fun q : ℕ => q.Prime ∧ y < q) = primesIoc y z := by
  ext q
  simp only [primesIoc, mem_filter, mem_Iic, mem_Ioc, Nat.floor_lt hy]
  tauto

/-- Membership in `slotTuples`. -/
lemma mem_slotTuples {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (u v : Fin k → ℝ) (Q : Fin k → ℕ) :
    Q ∈ slotTuples x u v ↔
      (∀ i, Q i ∈ primesIoc (x ^ u i) (x ^ v i)) ∧ Function.Injective Q := by
  simp only [slotTuples, mem_filter, Fintype.mem_piFinset,
    filter_Iic_eq_primesIoc (Real.rpow_nonneg hx _)]

/-- `slotTuples` with one slot. -/
lemma sum_slotTuples_one {x : ℝ} (hx : 0 ≤ x) (u v : Fin 1 → ℝ) (F : (Fin 1 → ℕ) → ℝ) :
    ∑ Q ∈ slotTuples x u v, F Q = ∑ q ∈ primesIoc (x ^ u 0) (x ^ v 0), F ![q] := by
  refine sum_nbij' (fun Q => Q 0) (fun q => ![q]) (fun Q hQ => ?_) (fun q hq => ?_)
    (fun Q _ => ?_) (fun q _ => rfl) (fun Q _ => ?_)
  · exact ((mem_slotTuples hx u v Q).1 hQ).1 0
  · refine (mem_slotTuples hx u v _).2 ⟨fun i => ?_, Function.injective_of_subsingleton _⟩
    rwa [Fin.fin_one_eq_zero i]
  · funext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  · congr 1
    funext i
    rw [Fin.fin_one_eq_zero i]
    rfl

/-- `slotTuples` with two slots. -/
lemma sum_slotTuples_two {x : ℝ} (hx : 0 ≤ x) (u v : Fin 2 → ℝ) (F : (Fin 2 → ℕ) → ℝ) :
    ∑ Q ∈ slotTuples x u v, F Q = ∑ q ∈ primesIoc (x ^ u 0) (x ^ v 0),
      ∑ r ∈ primesIoc (x ^ u 1) (x ^ v 1) with r ≠ q, F ![q, r] := by
  have : ∑ q ∈ primesIoc (x ^ u 0) (x ^ v 0),
      ∑ r ∈ primesIoc (x ^ u 1) (x ^ v 1) with r ≠ q, F ![q, r] =
        ∑ y ∈ primesIoc (x ^ u 0) (x ^ v 0) ×ˢ primesIoc (x ^ u 1) (x ^ v 1) with y.2 ≠ y.1,
          F ![y.1, y.2] := by
    simp only [sum_filter, sum_product]
  rw [this]
  refine sum_nbij' (fun Q => (Q 0, Q 1)) (fun y => ![y.1, y.2]) (fun Q hQ => ?_)
    (fun y hy => ?_) (fun Q _ => ?_) (fun y _ => rfl) (fun Q _ => ?_)
  · obtain ⟨h, hinj⟩ := (mem_slotTuples hx u v Q).1 hQ
    exact mem_filter.2 ⟨mem_product.2 ⟨h 0, h 1⟩, fun h => absurd (hinj h) (by decide)⟩
  · obtain ⟨hy, hne⟩ := mem_filter.1 hy
    obtain ⟨h0, h1⟩ := mem_product.1 hy
    refine (mem_slotTuples hx u v _).2 ⟨fun i => ?_, fun i j h => ?_⟩
    · fin_cases i
      exacts [h0, h1]
    · fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · funext i
    fin_cases i <;> rfl
  · congr 1
    funext i
    fin_cases i <;> rfl

/-- `slotTuples` with three slots, the first two forming a pair. -/
lemma sum_slotTuples_three {x : ℝ} (hx : 0 ≤ x) (u v : Fin 3 → ℝ) (F : (Fin 3 → ℕ) → ℝ) :
    ∑ Q ∈ slotTuples x u v, F Q =
      ∑ y ∈ primesIoc (x ^ u 0) (x ^ v 0) ×ˢ primesIoc (x ^ u 1) (x ^ v 1) with y.1 ≠ y.2,
        ∑ r ∈ primesIoc (x ^ u 2) (x ^ v 2) with r ∉ ({y.1, y.2} : Finset ℕ),
          F ![y.1, y.2, r] := by
  have : ∑ y ∈ primesIoc (x ^ u 0) (x ^ v 0) ×ˢ primesIoc (x ^ u 1) (x ^ v 1) with y.1 ≠ y.2,
      ∑ r ∈ primesIoc (x ^ u 2) (x ^ v 2) with r ∉ ({y.1, y.2} : Finset ℕ),
        F ![y.1, y.2, r] =
      ∑ w ∈ (primesIoc (x ^ u 0) (x ^ v 0) ×ˢ primesIoc (x ^ u 1) (x ^ v 1)) ×ˢ
          primesIoc (x ^ u 2) (x ^ v 2) with
          w.1.1 ≠ w.1.2 ∧ w.2 ∉ ({w.1.1, w.1.2} : Finset ℕ),
        F ![w.1.1, w.1.2, w.2] := by
    simp only [sum_filter, sum_product, ite_and]
    refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => ?_
    split_ifs
    · rfl
    · exact sum_const_zero.symm
  rw [this]
  refine sum_nbij' (fun Q => ((Q 0, Q 1), Q 2)) (fun w => ![w.1.1, w.1.2, w.2])
    (fun Q hQ => ?_) (fun w hw => ?_) (fun Q _ => ?_) (fun w _ => rfl) (fun Q _ => ?_)
  · obtain ⟨h, hinj⟩ := (mem_slotTuples hx u v Q).1 hQ
    refine mem_filter.2 ⟨mem_product.2 ⟨mem_product.2 ⟨h 0, h 1⟩, h 2⟩,
      fun h => absurd (hinj h) (by decide), ?_⟩
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨fun h => absurd (hinj h) (by decide), fun h => absurd (hinj h) (by decide)⟩
  · obtain ⟨hw, hne, hX⟩ := mem_filter.1 hw
    obtain ⟨hw, h2⟩ := mem_product.1 hw
    obtain ⟨h0, h1⟩ := mem_product.1 hw
    simp only [mem_insert, mem_singleton, not_or] at hX
    have := hX.1
    have := hX.2
    have := Ne.symm hne
    have := Ne.symm hX.1
    have := Ne.symm hX.2
    refine (mem_slotTuples hx u v _).2 ⟨fun i => ?_, fun i j h => ?_⟩
    · fin_cases i
      exacts [h0, h1, h2]
    · fin_cases i <;> fin_cases j <;> simp_all
  · funext i
    fin_cases i <;> rfl
  · congr 1
    funext i
    fin_cases i <;> rfl

/-- The rectangle statistic at a fixed `x`, as asserted eventually by `RectangleInput`. -/
def RectangleAt (c C x : ℝ) : Prop :=
  ∀ k ≤ 2, ∀ u v : Fin (k + 1) → ℝ,
    (∀ i, c / Real.log (Real.log x) ^ 20 ≤ u i) →
    ∑ i, v i ≤ 1 - c / Real.log (Real.log x) ^ 20 →
    ∀ B : (Fin k → ℕ) → ℝ, (∀ Q, |B Q| ≤ 1) →
      |(∑ p ∈ dyadicPrimes x, ∑ Q ∈ slotTuples x u v with ∏ i, Q i ∣ p - 1,
            B (Fin.init Q)) / (dyadicPrimes x).card -
          ∑ Q ∈ slotTuples x u v, B (Fin.init Q) / ∏ i, (Q i : ℝ)| ≤
        C / Real.log (Real.log x) ^ 300

/-- Clearing the denominator `N > 0` of an average. -/
lemma abs_sub_mul_le_of_div {S M ε N : ℝ} (hN : 0 < N) (h : |S / N - M| ≤ ε) :
    |S - N * M| ≤ N * ε := by
  rw [show S - N * M = N * (S / N - M) by field_simp, abs_mul, abs_of_pos hN]
  exact mul_le_mul_of_nonneg_left h hN.le

/-- The rectangle statistic with one unweighted slot. -/
lemma stat_zero {c C x : ℝ} (hR : RectangleAt c C x) (hx : 0 ≤ x)
    (hP : 0 < (dyadicPrimes x).card) {u v : ℝ} (hu : c / Real.log (Real.log x) ^ 20 ≤ u)
    (hv : v ≤ 1 - c / Real.log (Real.log x) ^ 20) :
    |∑ p ∈ dyadicPrimes x, ∑ q ∈ primesIoc (x ^ u) (x ^ v) with q ∣ p - 1, (1 : ℝ) -
        (dyadicPrimes x).card * ∑ q ∈ primesIoc (x ^ u) (x ^ v), (1 : ℝ) / q| ≤
      (dyadicPrimes x).card * (C / Real.log (Real.log x) ^ 300) := by
  have h := hR 0 (by norm_num) ![u] ![v] (fun i => by fin_cases i; exact hu)
    (by simpa using hv) (fun _ => 1) fun _ => by simp
  have e₁ : ∀ n, ∑ Q ∈ slotTuples x ![u] ![v] with ∏ i, Q i ∣ n, (1 : ℝ) =
      ∑ q ∈ primesIoc (x ^ u) (x ^ v) with q ∣ n, (1 : ℝ) := fun n => by
    rw [sum_filter, sum_slotTuples_one hx, sum_filter]
    simp
  have e₂ : ∑ Q ∈ slotTuples x ![u] ![v], (1 : ℝ) / ∏ i, (Q i : ℝ) =
      ∑ q ∈ primesIoc (x ^ u) (x ^ v), (1 : ℝ) / q := by
    rw [sum_slotTuples_one hx]
    simp
  simp only [e₁, e₂] at h
  exact abs_sub_mul_le_of_div (by exact_mod_cast hP) h

/-- The rectangle statistic with two slots and a coefficient on the first. -/
lemma stat_one {c C x : ℝ} (hR : RectangleAt c C x) (hx : 0 ≤ x)
    (hP : 0 < (dyadicPrimes x).card) {u₀ v₀ u₁ v₁ : ℝ}
    (hu₀ : c / Real.log (Real.log x) ^ 20 ≤ u₀) (hu₁ : c / Real.log (Real.log x) ^ 20 ≤ u₁)
    (hv : v₀ + v₁ ≤ 1 - c / Real.log (Real.log x) ^ 20) (b : ℕ → ℝ) (hb : ∀ q, |b q| ≤ 1) :
    |∑ p ∈ dyadicPrimes x, ∑ q ∈ primesIoc (x ^ u₀) (x ^ v₀),
          ∑ r ∈ primesIoc (x ^ u₁) (x ^ v₁) with r ≠ q ∧ q * r ∣ p - 1, b q -
        (dyadicPrimes x).card * ∑ q ∈ primesIoc (x ^ u₀) (x ^ v₀),
          ∑ r ∈ primesIoc (x ^ u₁) (x ^ v₁) with r ≠ q, b q / (q * r)| ≤
      (dyadicPrimes x).card * (C / Real.log (Real.log x) ^ 300) := by
  have h := hR 1 (by norm_num) ![u₀, u₁] ![v₀, v₁] (fun i => by fin_cases i <;> assumption)
    (by simpa using hv) (fun Q => b (Q 0)) fun _ => hb _
  have e₁ : ∀ n, ∑ Q ∈ slotTuples x ![u₀, u₁] ![v₀, v₁] with ∏ i, Q i ∣ n, b (Fin.init Q 0) =
      ∑ q ∈ primesIoc (x ^ u₀) (x ^ v₀),
        ∑ r ∈ primesIoc (x ^ u₁) (x ^ v₁) with r ≠ q ∧ q * r ∣ n, b q := fun n => by
    rw [sum_filter, sum_slotTuples_two hx]
    refine sum_congr rfl fun q _ => ?_
    rw [← filter_filter]
    conv_rhs => rw [sum_filter]
    refine sum_congr rfl fun r _ => ?_
    simp [Fin.init]
  have e₂ : ∑ Q ∈ slotTuples x ![u₀, u₁] ![v₀, v₁], b (Fin.init Q 0) / ∏ i, (Q i : ℝ) =
      ∑ q ∈ primesIoc (x ^ u₀) (x ^ v₀),
        ∑ r ∈ primesIoc (x ^ u₁) (x ^ v₁) with r ≠ q, b q / (q * r) := by
    rw [sum_slotTuples_two hx]
    simp [Fin.init]
  simp only [e₁, e₂] at h
  exact abs_sub_mul_le_of_div (by exact_mod_cast hP) h

/-- The rectangle statistic with three slots and a joint coefficient on the first two. -/
lemma stat_two {c C x : ℝ} (hR : RectangleAt c C x) (hx : 0 ≤ x)
    (hP : 0 < (dyadicPrimes x).card) {u₀ v₀ u₁ v₁ u₂ v₂ : ℝ}
    (hu₀ : c / Real.log (Real.log x) ^ 20 ≤ u₀) (hu₁ : c / Real.log (Real.log x) ^ 20 ≤ u₁)
    (hu₂ : c / Real.log (Real.log x) ^ 20 ≤ u₂)
    (hv : v₀ + v₁ + v₂ ≤ 1 - c / Real.log (Real.log x) ^ 20) (b : ℕ × ℕ → ℝ)
    (hb : ∀ y, |b y| ≤ 1) :
    |∑ p ∈ dyadicPrimes x,
          ∑ y ∈ primesIoc (x ^ u₀) (x ^ v₀) ×ˢ primesIoc (x ^ u₁) (x ^ v₁) with y.1 ≠ y.2,
            ∑ r ∈ primesIoc (x ^ u₂) (x ^ v₂) with
              r ∉ ({y.1, y.2} : Finset ℕ) ∧ y.1 * y.2 * r ∣ p - 1, b y -
        (dyadicPrimes x).card *
          ∑ y ∈ primesIoc (x ^ u₀) (x ^ v₀) ×ˢ primesIoc (x ^ u₁) (x ^ v₁) with y.1 ≠ y.2,
            ∑ r ∈ primesIoc (x ^ u₂) (x ^ v₂) with r ∉ ({y.1, y.2} : Finset ℕ),
              b y / (y.1 * y.2 * r)| ≤
      (dyadicPrimes x).card * (C / Real.log (Real.log x) ^ 300) := by
  have h := hR 2 le_rfl ![u₀, u₁, u₂] ![v₀, v₁, v₂]
    (fun i => by fin_cases i <;> assumption) (by simpa [Fin.sum_univ_three] using hv)
    (fun Q => b (Q 0, Q 1)) fun _ => hb _
  have e₁ : ∀ n, ∑ Q ∈ slotTuples x ![u₀, u₁, u₂] ![v₀, v₁, v₂] with ∏ i, Q i ∣ n,
      b (Fin.init Q 0, Fin.init Q 1) =
        ∑ y ∈ primesIoc (x ^ u₀) (x ^ v₀) ×ˢ primesIoc (x ^ u₁) (x ^ v₁) with y.1 ≠ y.2,
          ∑ r ∈ primesIoc (x ^ u₂) (x ^ v₂) with
            r ∉ ({y.1, y.2} : Finset ℕ) ∧ y.1 * y.2 * r ∣ n, b y := fun n => by
    rw [sum_filter, sum_slotTuples_three hx]
    refine sum_congr rfl fun y _ => ?_
    rw [← filter_filter]
    conv_rhs => rw [sum_filter]
    refine sum_congr rfl fun r _ => ?_
    simp [Fin.init, Fin.prod_univ_three]
  have e₂ : ∑ Q ∈ slotTuples x ![u₀, u₁, u₂] ![v₀, v₁, v₂],
      b (Fin.init Q 0, Fin.init Q 1) / ∏ i, (Q i : ℝ) =
        ∑ y ∈ primesIoc (x ^ u₀) (x ^ v₀) ×ˢ primesIoc (x ^ u₁) (x ^ v₁) with y.1 ≠ y.2,
          ∑ r ∈ primesIoc (x ^ u₂) (x ^ v₂) with r ∉ ({y.1, y.2} : Finset ℕ),
            b y / (y.1 * y.2 * r) := by
    rw [sum_slotTuples_three hx]
    refine sum_congr rfl fun y _ => sum_congr rfl fun r _ => ?_
    simp [Fin.init, Fin.prod_univ_three]
  simp only [e₁, e₂] at h
  exact abs_sub_mul_le_of_div (by exact_mod_cast hP) h

/-! ### Asymptotics of the scales -/

/-- Eventually `K ≤ T` and `K T³⁶ ≤ L`. -/
lemma eventually_le_loglog (K : ℝ) : ∀ᶠ x : ℝ in atTop, 1 < x ∧
    K ≤ Real.log (Real.log x) ∧ K * Real.log (Real.log x) ^ 36 ≤ Real.log x := by
  have hT : Tendsto (fun x => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hev := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 36).comp hT).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / (|K| + 1) by positivity))
  filter_upwards [eventually_gt_atTop 1, hT.eventually_ge_atTop K, hev,
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with x hx hK h hL
  refine ⟨hx, hK, ?_⟩
  simp only [Function.comp, Real.exp_neg, Real.exp_log hL] at h
  rw [← div_eq_mul_inv, div_lt_div_iff₀ hL (by positivity)] at h
  have h36 : 0 ≤ Real.log (Real.log x) ^ 36 := by positivity
  nlinarith [le_abs_self K]

/-- The constant `K` of `eventually_le_loglog` used for the scales. -/
noncomputable def scaleConst (c E₁ E₂ : ℝ) : ℝ :=
  12 * c + 6 * |Real.log c| + 200 + 12 * E₁ + E₂ / c + 1 / c + E₂

/-- The hypotheses `K ≤ T`, `K T³⁶ ≤ L` and `m ≍ T⁻²⁰` in terms of real variables. -/
structure ScaleHyp (c E₁ E₂ T L m : ℝ) : Prop where
  pos : 0 < c
  E₁_nonneg : 0 ≤ E₁
  E₂_nonneg : 0 ≤ E₂
  le_T : scaleConst c E₁ E₂ ≤ T
  le_L : scaleConst c E₁ E₂ * T ^ 36 ≤ L
  mesh_le : m ≤ 1 / T ^ 20
  le_mesh : 1 / (2 * T ^ 20) ≤ m

namespace ScaleHyp

variable {c E₁ E₂ T L m : ℝ} (h : ScaleHyp c E₁ E₂ T L m)
include h

/-- The constants absorbed by `T` and `K`. -/
lemma consts : 12 * c ≤ T ∧ 6 * |Real.log c| ≤ T ∧ 200 ≤ T ∧ 12 * E₁ ≤ scaleConst c E₁ E₂ ∧
    E₂ / c ≤ scaleConst c E₁ E₂ ∧ 1 / c ≤ scaleConst c E₁ E₂ ∧ E₂ ≤ T ∧
    24 ≤ scaleConst c E₁ E₂ := by
  have := h.le_T
  have := h.pos
  have := h.E₁_nonneg
  have := h.E₂_nonneg
  have := abs_nonneg (Real.log c)
  have := div_nonneg h.E₂_nonneg h.pos.le
  have := one_div_pos.2 h.pos
  unfold scaleConst at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- `1 ≤ T`. -/
lemma one_le : 1 ≤ T := by linarith [h.consts.2.2.1]

/-- `0 < T`. -/
lemma pos_T : 0 < T := by linarith [h.one_le]

/-- `T ≤ Tⁿ`. -/
lemma le_pow {n : ℕ} (hn : n ≠ 0) : T ≤ T ^ n := le_self_pow₀ h.one_le hn

/-- `Tⁿ ≤ T³⁶` for `n ≤ 36`. -/
lemma pow_le_36 {n : ℕ} (hn : n ≤ 36) : T ^ n ≤ T ^ 36 := pow_le_pow_right₀ h.one_le hn

/-- `K' T³⁶ ≤ L` for each `K' ≤ K`. -/
lemma mul_le_L {K' : ℝ} (hK' : K' ≤ scaleConst c E₁ E₂) :
    K' * T ^ 36 ≤ L :=
  le_trans (mul_le_mul_of_nonneg_right hK' (by have := h.pos_T; positivity)) h.le_L

/-- `0 < L`. -/
lemma pos_L : 0 < L := by
  have := h.mul_le_L (K' := 24) h.consts.2.2.2.2.2.2.2
  have := h.pos_T
  have : 0 < T ^ 36 := by positivity
  nlinarith

/-- `0 < m`. -/
lemma pos_mesh : 0 < m := lt_of_lt_of_le (by have := h.pos_T; positivity) h.le_mesh

/-- `1 / m ≤ 2 T²⁰`. -/
lemma inv_mesh_le : 1 / m ≤ 2 * T ^ 20 := by
  have := h.pos_T
  have h₂ := h.le_mesh
  rw [div_le_iff₀ h.pos_mesh]
  rw [div_le_iff₀ (by positivity)] at h₂
  linarith

/-- `1 ≤ L δ`, so `x^δ ≥ 2`. -/
lemma le_L_mul_offset : 1 ≤ L * (c / T ^ 20) := by
  have := h.pos_T
  have hc := h.pos
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  have := h.mul_le_L (K' := 1 / c) h.consts.2.2.2.2.2.1
  have h20 := h.pow_le_36 (n := 20) (by norm_num)
  rw [one_div_mul_eq_div, div_le_iff₀ hc] at this
  nlinarith

/-- `T ≤ L a`, so `x^a ≥ L`. -/
lemma T_le_L_mul_margin : T ≤ L * (1 / T ^ 6) := by
  have := h.pos_T
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  have := h.mul_le_L (K' := 24) h.consts.2.2.2.2.2.2.2
  calc T * T ^ 6 = T ^ 7 := by ring
    _ ≤ T ^ 36 := h.pow_le_36 (by norm_num)
    _ ≤ 24 * T ^ 36 := by nlinarith [pow_pos h.pos_T 36]
    _ ≤ L := this

/-- `2δ ≤ a`. -/
lemma two_mul_offset_le : 2 * (c / T ^ 20) ≤ 1 / T ^ 6 := by
  have := h.pos_T
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have := h.le_pow (n := 14) (by norm_num)
  calc 2 * c * T ^ 6 ≤ T ^ 14 * T ^ 6 := by
        gcongr; linarith [h.consts.1, h.pos]
    _ = 1 * T ^ 20 := by ring

/-- `a ≤ 1 / 4`. -/
lemma margin_le : 1 / T ^ 6 ≤ 1 / 4 := by
  have := h.pos_T
  have := h.le_pow (n := 6) (by norm_num)
  have := h.consts.2.2.1
  gcongr
  linarith

/-- The defect bound of `abs_one_sub_spareModel_le` is at most `T⁻¹⁰` when `L ≤ x^a`. -/
lemma defect_le {X : ℝ} (hX : L ≤ X) :
    (2 * (c / T ^ 20) + 3 * m + Real.log 2 / L + E₁ / (m * L) +
      m * (Real.log (1 / (c / T ^ 20)) + E₂ / (c / T ^ 20 * L)) + 2 / (m * X)) /
        (1 / T ^ 6) ≤ 1 / T ^ 10 := by
  obtain ⟨hK₁, hK₂, hT, hK₄, hK₅, -, -, hK₈⟩ := h.consts
  have hc := h.pos
  have hT0 := h.pos_T
  have hL0 := h.pos_L
  have hm0 := h.pos_mesh
  have hX0 : 0 < X := hL0.trans_le hX
  have hT4 := h.le_pow (n := 4) (by norm_num)
  set u := 1 / (6 * T ^ 16)
  have h16 : 0 < 6 * T ^ 16 := by positivity
  -- the six terms, each at most `1 / (6 T¹⁶)`
  have t₁ : 2 * (c / T ^ 20) ≤ u := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) h16]
    calc 2 * c * (6 * T ^ 16) = 12 * c * T ^ 16 := by ring
      _ ≤ T ^ 4 * T ^ 16 := by gcongr; linarith
      _ = 1 * T ^ 20 := by ring
  have t₂ : 3 * m ≤ u := by
    calc 3 * m ≤ 3 * (1 / T ^ 20) := by gcongr; exact h.mesh_le
      _ ≤ u := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) h16]
        calc 3 * (6 * T ^ 16) = 18 * T ^ 16 := by ring
          _ ≤ T ^ 4 * T ^ 16 := by gcongr; linarith
          _ = 1 * T ^ 20 := by ring
  have t₃ : Real.log 2 / L ≤ u := by
    have := h.mul_le_L (K' := 24) hK₈
    calc Real.log 2 / L ≤ 1 / L :=
          div_le_div_of_nonneg_right (Real.log_two_lt_d9.le.trans (by norm_num)) hL0.le
      _ ≤ u := by
        rw [div_le_div_iff₀ hL0 h16]
        nlinarith [h.pow_le_36 (n := 16) (by norm_num)]
  have t₄ : E₁ / (m * L) ≤ u := by
    have := h.mul_le_L hK₄
    calc E₁ / (m * L) = 1 / m * E₁ / L := by field_simp
      _ ≤ 2 * T ^ 20 * E₁ / L := by
        gcongr
        · exact h.E₁_nonneg
        · exact h.inv_mesh_le
      _ ≤ u := by
        rw [div_le_div_iff₀ hL0 h16]
        nlinarith
  have t₅ : m * (Real.log (1 / (c / T ^ 20)) + E₂ / (c / T ^ 20 * L)) ≤ u := by
    have hlog : Real.log (1 / (c / T ^ 20)) ≤ 20 * T + |Real.log c| := by
      rw [one_div_div, Real.log_div (by positivity) hc.ne', Real.log_pow]
      have := Real.log_le_sub_one_of_pos hT0
      push_cast
      linarith [neg_abs_le (Real.log c)]
    have hE : E₂ / (c / T ^ 20 * L) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := h.mul_le_L hK₅
      rw [div_mul_eq_mul_div, div_le_iff₀ hc] at this
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [h.pow_le_36 (n := 20) (by norm_num), h.E₂_nonneg]
    have hT2 := h.le_pow (n := 2) (by norm_num)
    have h42 : T ^ 2 ≤ T ^ 4 := pow_le_pow_right₀ h.one_le (by norm_num)
    have hsq : T * T = T ^ 2 := by ring
    calc m * (Real.log (1 / (c / T ^ 20)) + E₂ / (c / T ^ 20 * L))
        ≤ m * (20 * T + |Real.log c| + 1) := by gcongr
      _ ≤ 1 / T ^ 20 * (20 * T + |Real.log c| + 1) :=
        mul_le_mul_of_nonneg_right h.mesh_le (by positivity)
      _ ≤ u := by
        rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) h16]
        have : 6 * (20 * T + |Real.log c| + 1) ≤ T ^ 4 := by nlinarith
        calc (20 * T + |Real.log c| + 1) * (6 * T ^ 16) =
              6 * (20 * T + |Real.log c| + 1) * T ^ 16 := by ring
          _ ≤ T ^ 4 * T ^ 16 := by gcongr
          _ = 1 * T ^ 20 := by ring
  have t₆ : 2 / (m * X) ≤ u := by
    have := h.mul_le_L (K' := 24) hK₈
    calc 2 / (m * X) = 1 / m * 2 / X := by field_simp
      _ ≤ 2 * T ^ 20 * 2 / L := by
        gcongr
        exact h.inv_mesh_le
      _ ≤ u := by
        rw [div_le_div_iff₀ hL0 h16]
        nlinarith
  calc _ ≤ (6 * u) / (1 / T ^ 6) := by gcongr; linarith
    _ = 1 / T ^ 10 := by simp only [u]; field_simp

end ScaleHyp

/-- For all large `x`, the scale hypotheses hold at `T = log log x`, `L = log x` and
`m = mesh x`. -/
lemma eventually_scaleHyp {c : ℝ} (hc : 0 < c) {E₁ E₂ : ℝ} (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) :
    ∀ᶠ x : ℝ in atTop,
      1 < x ∧ ScaleHyp c E₁ E₂ (Real.log (Real.log x)) (Real.log x) (mesh x) := by
  filter_upwards [eventually_le_loglog (scaleConst c E₁ E₂), mesh_le_margin_pow] with x
    ⟨hx, hT, hL⟩ ⟨hm₁, hm₂⟩
  exact ⟨hx, hc, hE₁, hE₂, hT, hL, hm₁, hm₂⟩

/-- `2 ≤ x^y` once `L y ≥ 1`. -/
lemma two_le_rpow {x y : ℝ} (hx : 1 < x) (hy : 1 ≤ Real.log x * y) : 2 ≤ x ^ y := by
  rw [Real.rpow_def_of_pos (by linarith)]
  linarith [Real.add_one_le_exp 1, Real.exp_le_exp.2 hy]

/-- `L ≤ x^a` once `T ≤ L a`. -/
lemma log_le_rpow {x y : ℝ} (hx : 1 < x) (hy : Real.log (Real.log x) ≤ Real.log x * y) :
    Real.log x ≤ x ^ y := by
  rw [Real.rpow_def_of_pos (by linarith)]
  calc Real.log x = Real.exp (Real.log (Real.log x)) :=
        (Real.exp_log (Real.log_pos hx)).symm
    _ ≤ _ := Real.exp_le_exp.2 hy

/-- A dyadic prime `p` has `0 < p - 1 < 2x`. -/
lemma pred_of_mem_dyadicPrimes {x : ℝ} {p : ℕ} (hp : p ∈ dyadicPrimes x) :
    0 < p - 1 ∧ ((p - 1 : ℕ) : ℝ) < 2 * x := by
  obtain ⟨hp, hpr⟩ := mem_filter.1 hp
  have h2 := hpr.two_le
  refine ⟨by omega, ?_⟩
  have hle : (p : ℝ) ≤ 2 * x := by
    have := (mem_Ioc.1 hp).2
    by_contra h
    have h0 : 0 ≤ 2 * x := by
      by_contra h'
      rw [Nat.floor_of_nonpos (not_le.1 h').le] at this
      omega
    have := (Nat.le_floor_iff h0).1 this
    linarith
  have : ((p - 1 : ℕ) : ℝ) < p := by exact_mod_cast (by omega : p - 1 < p)
  linarith

/-- `J ≤ 1 / m` spare cells. -/
lemma spareCount_le {c x s : ℝ} (hm : 0 < mesh x) (hδ : 0 ≤ spareOffset c x) (hs : 0 ≤ s) :
    (spareCount c x s : ℝ) ≤ 1 / mesh x := by
  rcases le_or_gt 0 ((1 - 2 * spareOffset c x - s) / mesh x) with h | h
  · refine (Nat.floor_le h).trans ?_
    gcongr
    linarith
  · rw [spareCount, Nat.floor_of_nonpos h.le, Nat.cast_zero]
    positivity

/-- An admissible spare cell `j < J` satisfies `s + δ + (j + 1) m ≤ 1 - δ`. -/
lemma add_le_of_lt_spareCount {c x s : ℝ} (hm : 0 < mesh x) {j : ℕ}
    (hj : j < spareCount c x s) :
    s + (spareOffset c x + (j + 1) * mesh x) ≤ 1 - spareOffset c x := by
  have h : ((j + 1 : ℕ) : ℝ) ≤ (1 - 2 * spareOffset c x - s) / mesh x :=
    (Nat.le_floor_iff' (Nat.succ_ne_zero j)).1 hj
  rw [le_div_iff₀ hm] at h
  push_cast at h
  linarith

/-- The harmonic mass of the first `J` cells is at most `log(1 / a) + 1 ≤ 7T`. -/
lemma sum_cell_inv_le {E : ℝ}
    (hE : ∀ x u v : ℝ, 1 < x → 0 < u → u ≤ v → 2 ≤ x ^ u →
      |∑ p ∈ primesIoc (x ^ u) (x ^ v), (1 : ℝ) / p - Real.log (v / u)| ≤
        E / (u * Real.log x))
    {x : ℝ} (hx : 1 < x) (hT : 1 ≤ Real.log (Real.log x)) (hm : 0 < mesh x)
    (h2 : 2 ≤ x ^ margin x) (hEa : E / (margin x * Real.log x) ≤ 1) {J : ℕ}
    (hJ : margin x + J * mesh x ≤ 1) :
    ∑ j ∈ range J, ∑ q ∈ cell x j, (1 : ℝ) / q ≤ 7 * Real.log (Real.log x) := by
  have ha : 0 < margin x := by unfold margin; positivity
  have hJa : margin x ≤ margin x + J * mesh x := by
    have := J.cast_nonneg (α := ℝ); nlinarith
  have hM := (abs_le.1 (hE x (margin x) (margin x + J * mesh x) hx ha hJa h2)).2
  have hlog : Real.log ((margin x + J * mesh x) / margin x) ≤
      6 * Real.log (Real.log x) := by
    calc Real.log ((margin x + J * mesh x) / margin x) ≤ Real.log (1 / margin x) :=
          Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hJ ha.le)
      _ = 6 * Real.log (Real.log (Real.log x)) := by
          rw [margin, one_div_one_div, Real.log_pow]
          push_cast
          ring
      _ ≤ 6 * Real.log (Real.log x) := by
          have := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log (Real.log x))
          linarith
  have := sum_gridCell_le hx hm.le J (b := margin x) (f := fun q => (1 : ℝ) / q)
    fun q => by positivity
  change ∑ j ∈ range J, ∑ q ∈ gridCell x (margin x) (mesh x) j, (1 : ℝ) / q ≤ _
  linarith

/-- The total error: with at most `4 T⁴⁰` boxes, `J ≤ 2 T²⁰` spare cells, mass at most
`49 T²` and defect `T⁻¹⁰`, everything is `O(T⁻⁷)`. -/
lemma total_error_le {T C nb M : ℝ} (hT : 1 ≤ T) (hnb : nb ≤ 4 * T ^ 40)
    (hM : M ≤ 49 * T ^ 2) :
    2 * (nb * (2 * T ^ 20) * (|C| / T ^ 300)) + nb * (|C| / T ^ 300) +
        2 * (M * (1 / T ^ 10)) ≤ (20 * |C| + 98) / T ^ 7 := by
  have hT0 : 0 < T := by linarith
  have hC := abs_nonneg C
  have h₁ : nb * (2 * T ^ 20) * (|C| / T ^ 300) ≤ 8 * |C| / T ^ 7 := by
    calc nb * (2 * T ^ 20) * (|C| / T ^ 300) ≤ 4 * T ^ 40 * (2 * T ^ 20) * (|C| / T ^ 300) := by
          gcongr
      _ = 8 * |C| / T ^ 240 := by field_simp; ring
      _ ≤ 8 * |C| / T ^ 7 := by gcongr; norm_num
  have h₂ : nb * (|C| / T ^ 300) ≤ 4 * |C| / T ^ 7 := by
    calc nb * (|C| / T ^ 300) ≤ 4 * T ^ 40 * (|C| / T ^ 300) := by gcongr
      _ = 4 * |C| / T ^ 260 := by field_simp
      _ ≤ 4 * |C| / T ^ 7 := by gcongr; norm_num
  have h₃ : M * (1 / T ^ 10) ≤ 49 / T ^ 7 := by
    calc M * (1 / T ^ 10) ≤ 49 * T ^ 2 * (1 / T ^ 10) := by gcongr
      _ = 49 / T ^ 8 := by field_simp
      _ ≤ 49 / T ^ 7 := by gcongr; norm_num
  calc _ ≤ 2 * (8 * |C| / T ^ 7) + 4 * |C| / T ^ 7 + 2 * (49 / T ^ 7) := by gcongr
    _ = (20 * |C| + 98) / T ^ 7 := by ring

/-- A sum over a disjoint union as a sum over `Finset.sigma`. -/
lemma sum_biUnion_eq_sum_sigma {ι α : Type*} [DecidableEq α] (s : Finset ι) (t : ι → Finset α)
    (h : (s : Set ι).PairwiseDisjoint t) (P : α → Prop) [DecidablePred P] (f : α → ℝ) :
    ∑ a ∈ s.biUnion t with P a, f a = ∑ z ∈ s.sigma t with P z.2, f z.2 := by
  rw [sum_filter, sum_filter, sum_biUnion h, sum_sigma]

/-! ### One original prime -/

/-- A prime of `J_j` with `j < ⌊(1 - 2a) / m⌋` is admissible with `s = a + (j + 1) m`. -/
lemma admissible_cell {x : ℝ} (hx : 1 < x) (hm : 0 < mesh x) (ha : 0 ≤ margin x) {j : ℕ}
    (hj : j < cellCount₁ x) {q : ℕ} (hq : q ∈ cell x j) :
    Admissible x (margin x + (j + 1) * mesh x) {q} := by
  have hx0 : 0 < x := by linarith
  have hj' : ((j + 1 : ℕ) : ℝ) ≤ (1 - 2 * margin x) / mesh x :=
    (Nat.le_floor_iff' (Nat.succ_ne_zero j)).1 hj
  rw [le_div_iff₀ hm] at hj'
  push_cast at hj'
  have hL := Real.log_pos hx
  obtain ⟨hlo, hhi⟩ := log_bounds_of_mem hx hq
  obtain ⟨hp, hxq, -⟩ := (mem_cell hx0.le).1 hq
  have hjm : (0 : ℝ) ≤ j * mesh x := by positivity
  refine ⟨by positivity, by linarith, by simp, fun q' hq' => ?_, ?_, ?_⟩
  · rw [mem_singleton.1 hq']
    exact ⟨hp, lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)) hxq⟩
  · rw [prod_singleton, lt_div_iff₀ hL]
    nlinarith
  · rw [prod_singleton, div_le_iff₀ hL]
    linarith

/-! ### Two original primes -/

/-- The box `J_{j₁} × J_{j₂}` of `region₂`, without the diagonal. -/
noncomputable def pairBox (x : ℝ) (j : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (cell x j.1 ×ˢ cell x j.2).filter fun Q => Q.1 ≠ Q.2

/-- The upper log coordinate `2a + (j₁ + j₂ + 2) m` of the box `J_{j₁} × J_{j₂}`. -/
noncomputable def pairTop (x : ℝ) (j : ℕ × ℕ) : ℝ :=
  2 * margin x + ((j.1 : ℝ) + j.2 + 2) * mesh x

/-- An admissible cell pair has `2a + (j₁ + j₂ + 2) m ≤ 1 - a`. -/
lemma pairTop_le {x : ℝ} (hm : 0 < mesh x) {j : ℕ × ℕ} (hj : j ∈ cellPairs₂ x) :
    pairTop x j ≤ 1 - margin x := by
  have h := (mem_filter.1 hj).2
  have h' : ((j.1 + j.2 + 2 : ℕ) : ℝ) ≤ (1 - 3 * margin x) / mesh x :=
    (Nat.le_floor_iff' (by omega)).1 h
  rw [le_div_iff₀ hm] at h'
  push_cast at h'
  rw [pairTop]
  linarith

/-- A pair of `pairBox x j` with `j ∈ cellPairs₂ x` is admissible with
`s = 2a + (j₁ + j₂ + 2) m`. -/
lemma admissible_pairBox {x : ℝ} (hx : 1 < x) (hm : 0 < mesh x) (ha : 0 ≤ margin x)
    {j : ℕ × ℕ} (hj : j ∈ cellPairs₂ x) {Q : ℕ × ℕ} (hQ : Q ∈ pairBox x j) :
    Admissible x (pairTop x j) {Q.1, Q.2} := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hQ, hne⟩ := mem_filter.1 hQ
  obtain ⟨h₁, h₂⟩ := mem_product.1 hQ
  have hL := Real.log_pos hx
  obtain ⟨hlo₁, hhi₁⟩ := log_bounds_of_mem hx h₁
  obtain ⟨hlo₂, hhi₂⟩ := log_bounds_of_mem hx h₂
  obtain ⟨hp₁, hxq₁, -⟩ := (mem_cell hx0.le).1 h₁
  obtain ⟨hp₂, hxq₂, -⟩ := (mem_cell hx0.le).1 h₂
  have hj₁ : (0 : ℝ) ≤ j.1 * mesh x := by positivity
  have hj₂ : (0 : ℝ) ≤ j.2 * mesh x := by positivity
  have hlog : Real.log (∏ q ∈ {Q.1, Q.2}, q : ℕ) = Real.log Q.1 + Real.log Q.2 := by
    rw [prod_pair hne, Nat.cast_mul, Real.log_mul (by exact_mod_cast hp₁.ne_zero)
      (by exact_mod_cast hp₂.ne_zero)]
  have htop := pairTop_le hm hj
  rw [pairTop] at htop ⊢
  refine ⟨by positivity, htop, card_insert_le _ _, fun q hq => ?_, ?_, ?_⟩
  · rcases mem_insert.1 hq with rfl | hq
    · exact ⟨hp₁, lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)) hxq₁⟩
    · rw [mem_singleton.1 hq]
      exact ⟨hp₂, lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)) hxq₂⟩
  · rw [hlog, lt_div_iff₀ hL]
    nlinarith
  · rw [hlog, div_le_iff₀ hL]
    nlinarith

/-- A filtered sum over the off-diagonal pairs as an iterated sum. -/
lemma sum_pairs_filter (A B : Finset ℕ) (P : ℕ → ℕ → Prop) [∀ q r, Decidable (P q r)]
    (f : ℕ → ℕ → ℝ) :
    ∑ Q ∈ (A ×ˢ B).filter (fun Q => Q.1 ≠ Q.2) with P Q.1 Q.2, f Q.1 Q.2 =
      ∑ q ∈ A, ∑ r ∈ B with r ≠ q ∧ P q r, f q r := by
  rw [filter_filter, sum_filter, sum_product]
  refine sum_congr rfl fun q _ => ?_
  rw [sum_filter]
  exact sum_congr rfl fun r _ =>
    if_congr ⟨fun h => ⟨Ne.symm h.1, h.2⟩, fun h => ⟨Ne.symm h.1, h.2⟩⟩ rfl rfl

/-- A sum over the off-diagonal pairs as an iterated sum. -/
lemma sum_pairs (A B : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ Q ∈ (A ×ˢ B).filter (fun Q => Q.1 ≠ Q.2), f Q.1 Q.2 =
      ∑ q ∈ A, ∑ r ∈ B with r ≠ q, f q r := by
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun q _ => ?_
  rw [sum_filter]
  exact sum_congr rfl fun r _ => if_congr ⟨Ne.symm, Ne.symm⟩ rfl rfl

end SpareSlot

open SpareSlot in
/-- One weighted prime: under `RectangleInput`, for every coefficient of
modulus at most one on `region₁`, the dyadic prime average of
`∑_{q ∣ p - 1} B(q)` agrees with `∑ B(q) / q` up to `O(T⁻⁷)`. -/
theorem spare_slot_one (hR : RectangleInput) : ∃ K : ℝ, ∀ᶠ x : ℝ in Filter.atTop,
    ∀ B : ℕ → ℝ, (∀ q, |B q| ≤ 1) →
      |∑ p ∈ dyadicPrimes x, ∑ q ∈ region₁ x with q ∣ p - 1, B q -
          (dyadicPrimes x).card * ∑ q ∈ region₁ x, B q / q| ≤
        K * (dyadicPrimes x).card / Real.log (Real.log x) ^ 7 := by
  obtain ⟨c, hc, C, hev⟩ := hR
  obtain ⟨E₁, E₂, hE₁, hE₂, hdef⟩ := abs_one_sub_spareModel_le
  obtain ⟨E, hE, hmert⟩ := mertens_second_rpow
  refine ⟨20 * |C| + 98, ?_⟩
  filter_upwards [hev, eventually_scaleHyp hc hE₁ hE₂, eventually_le_loglog E] with x hRx
    hxS hxE B hB
  obtain ⟨hx, hS⟩ := hxS
  have hET := hxE.2.1
  set T := Real.log (Real.log x)
  set J₁ := cellCount₁ x
  set s : ℕ → ℝ := fun j => margin x + (j + 1) * mesh x
  have hx0 : 0 < x := by linarith
  have hP : 0 < (dyadicPrimes x).card := dyadicPrimes_card_pos hx.le
  have hm := hS.pos_mesh
  have hT0 := hS.pos_T
  have hδ : 0 < spareOffset c x := div_pos hc (pow_pos hT0 20)
  have hδa : 2 * spareOffset c x ≤ margin x := hS.two_mul_offset_le
  have ha : 0 < margin x := by linarith
  have hcδ : c / T ^ 20 ≤ margin x := by change spareOffset c x ≤ _; linarith
  have hLa : T ≤ Real.log x * margin x := hS.T_le_L_mul_margin
  have ha4 : margin x ≤ 1 / 4 := hS.margin_le
  have hxa : Real.log x ≤ x ^ margin x := log_le_rpow hx hLa
  have h2a : 2 ≤ x ^ margin x := two_le_rpow hx (by linarith [hS.one_le])
  have h2δ : 2 ≤ x ^ spareOffset c x := two_le_rpow hx hS.le_L_mul_offset
  have hEa : E / (margin x * Real.log x) ≤ 1 := by
    rw [div_le_one (mul_pos ha hS.pos_L), mul_comm]
    exact hET.trans hLa
  have hJ₁ : (J₁ : ℝ) * mesh x ≤ 1 - 2 * margin x :=
    (le_div_iff₀ hm).1 (Nat.floor_le (div_nonneg (by linarith) hm.le))
  -- the hypotheses of `abs_sum_sigma_sub_le` for the cells of `region₁`
  have hadm : ∀ j ∈ range J₁, ∀ q ∈ cell x j, Admissible x (s j) {q} := fun j hj q hq =>
    admissible_cell hx hm ha.le (mem_range.1 hj) hq
  have hA : ∀ j ∈ range J₁, ∀ q ∈ cell x j, |1 - spareModel c x (s j) {q}| ≤ 1 / T ^ 10 :=
    fun j hj q hq => (hdef c x _ _ hx hm hδ h2δ hδa (hadm j hj q hq)).trans (hS.defect_le hxa)
  have hJ : ∀ j ∈ range J₁, (spareCount c x (s j) : ℝ) ≤ 2 * T ^ 20 := fun j _ =>
    (spareCount_le hm hδ.le (by positivity)).trans hS.inv_mesh_le
  have hmass : ∑ j ∈ range J₁, ∑ q ∈ cell x j, (1 : ℝ) / (∏ q' ∈ {q}, q' : ℕ) ≤ 7 * T := by
    simp only [prod_singleton]
    exact sum_cell_inv_le hmert hx hS.one_le hm h2a hEa (by linarith)
  have h₁ : ∀ j ∈ range J₁, ∀ j' < spareCount c x (s j), ∀ b : ℕ → ℝ, (∀ q, |b q| ≤ 1) →
      |∑ p ∈ dyadicPrimes x, ∑ q ∈ cell x j, ∑ r ∈ spareCell c x j' with
          r ∉ ({q} : Finset ℕ) ∧ (∏ q' ∈ {q}, q') * r ∣ p - 1, b q -
        (dyadicPrimes x).card * ∑ q ∈ cell x j, ∑ r ∈ spareCell c x j' with
          r ∉ ({q} : Finset ℕ), b q / ((∏ q' ∈ {q}, q' : ℕ) * r)| ≤
        (dyadicPrimes x).card * (|C| / T ^ 300) := by
    intro j _ j' hj' b hb
    simp only [prod_singleton, mem_singleton]
    have hjm : (0 : ℝ) ≤ j * mesh x := by positivity
    have hj'm : (0 : ℝ) ≤ j' * mesh x := by positivity
    refine (stat_one hRx hx0.le hP (u₀ := margin x + j * mesh x)
      (v₀ := margin x + (j + 1) * mesh x) (u₁ := spareOffset c x + j' * mesh x)
      (v₁ := spareOffset c x + (j' + 1) * mesh x) (by linarith)
      (le_add_of_nonneg_right hj'm) (add_le_of_lt_spareCount hm hj') b hb).trans ?_
    gcongr
    exact le_abs_self C
  have h₀ : ∀ j ∈ range J₁, |∑ p ∈ dyadicPrimes x, ∑ q ∈ cell x j with
        (∏ q' ∈ {q}, q') ∣ p - 1, (1 : ℝ) -
      (dyadicPrimes x).card * ∑ q ∈ cell x j, (1 : ℝ) / (∏ q' ∈ {q}, q' : ℕ)| ≤
        (dyadicPrimes x).card * (|C| / T ^ 300) := by
    intro j hj
    simp only [prod_singleton]
    have hj' : ((j : ℝ) + 1) * mesh x ≤ J₁ * mesh x := by
      gcongr
      exact_mod_cast mem_range.1 hj
    have hjm : (0 : ℝ) ≤ j * mesh x := by positivity
    refine (stat_zero hRx hx0.le hP (u := margin x + j * mesh x)
      (v := margin x + (j + 1) * mesh x) (by linarith) (by linarith)).trans ?_
    gcongr
    exact le_abs_self C
  have hcore := abs_sum_sigma_sub_le (c := c) (x := x) (ε₁ := |C| / T ^ 300)
    (ε₂ := 1 / T ^ 10) (M := 7 * T) (Jmax := 2 * T ^ 20) (dyadicPrimes x) (range J₁) (cell x)
    (fun q => {q}) s hx hm hδ hδa (fun p hp => pred_of_mem_dyadicPrimes hp) hadm hA hJ hmass
    (by positivity) (by positivity) h₁ h₀ B hB
  simp only [prod_singleton] at hcore
  -- back from `Finset.sigma` to `region₁`
  have hdisj : (↑(range J₁) : Set ℕ).PairwiseDisjoint (cell x) := fun i _ j _ hij =>
    disjoint_cell hx.le hij
  have e₁ : ∀ p, ∑ q ∈ region₁ x with q ∣ p - 1, B q =
      ∑ z ∈ (range J₁).sigma (cell x) with z.2 ∣ p - 1, B z.2 := fun p =>
    sum_biUnion_eq_sum_sigma _ _ hdisj (· ∣ p - 1) B
  have e₂ : ∑ q ∈ region₁ x, B q / q = ∑ z ∈ (range J₁).sigma (cell x), B z.2 / z.2 := by
    rw [region₁, sum_biUnion hdisj, sum_sigma]
  rw [Finset.sum_congr rfl fun p _ => e₁ p, e₂]
  refine hcore.trans ?_
  have hJ₁' : (J₁ : ℝ) ≤ 4 * T ^ 40 := by
    have h1 : (J₁ : ℝ) ≤ 1 / mesh x := by
      rw [le_div_iff₀ hm]; linarith
    have h2 := hS.inv_mesh_le
    nlinarith [hS.le_pow (n := 20) (by norm_num), pow_le_pow_right₀ hS.one_le
      (show 20 ≤ 40 by norm_num)]
  rw [card_range]
  calc _ ≤ (dyadicPrimes x).card * ((20 * |C| + 98) / T ^ 7) := by
        gcongr
        exact total_error_le hS.one_le hJ₁' (by nlinarith [hS.one_le])
    _ = _ := by ring

open SpareSlot in
/-- Two jointly weighted primes: under `RectangleInput`, for every coefficient
of modulus at most one on `region₂`, the dyadic prime average of
`∑_{q r ∣ p - 1} B(q, r)` agrees with `∑ B(q, r) / (q r)` up to `O(T⁻⁷)`. -/
theorem spare_slot_two (hR : RectangleInput) : ∃ K : ℝ, ∀ᶠ x : ℝ in Filter.atTop,
    ∀ B : ℕ → ℕ → ℝ, (∀ q r, |B q r| ≤ 1) →
      |∑ p ∈ dyadicPrimes x, ∑ Q ∈ region₂ x with Q.1 * Q.2 ∣ p - 1, B Q.1 Q.2 -
          (dyadicPrimes x).card * ∑ Q ∈ region₂ x, B Q.1 Q.2 / (Q.1 * Q.2)| ≤
        K * (dyadicPrimes x).card / Real.log (Real.log x) ^ 7 := by
  obtain ⟨c, hc, C, hev⟩ := hR
  obtain ⟨E₁, E₂, hE₁, hE₂, hdef⟩ := abs_one_sub_spareModel_le
  obtain ⟨E, hE, hmert⟩ := mertens_second_rpow
  refine ⟨20 * |C| + 98, ?_⟩
  filter_upwards [hev, eventually_scaleHyp hc hE₁ hE₂, eventually_le_loglog E] with x hRx
    hxS hxE B hB
  obtain ⟨hx, hS⟩ := hxS
  have hET := hxE.2.1
  set T := Real.log (Real.log x)
  set J₂ := cellCount₂ x
  have hx0 : 0 < x := by linarith
  have hP : 0 < (dyadicPrimes x).card := dyadicPrimes_card_pos hx.le
  have hm := hS.pos_mesh
  have hT0 := hS.pos_T
  have hδ : 0 < spareOffset c x := div_pos hc (pow_pos hT0 20)
  have hδa : 2 * spareOffset c x ≤ margin x := hS.two_mul_offset_le
  have ha : 0 < margin x := by linarith
  have hcδ : c / T ^ 20 ≤ margin x := by change spareOffset c x ≤ _; linarith
  have hLa : T ≤ Real.log x * margin x := hS.T_le_L_mul_margin
  have ha4 : margin x ≤ 1 / 4 := hS.margin_le
  have hxa : Real.log x ≤ x ^ margin x := log_le_rpow hx hLa
  have h2a : 2 ≤ x ^ margin x := two_le_rpow hx (by linarith [hS.one_le])
  have h2δ : 2 ≤ x ^ spareOffset c x := two_le_rpow hx hS.le_L_mul_offset
  have hEa : E / (margin x * Real.log x) ≤ 1 := by
    rw [div_le_one (mul_pos ha hS.pos_L), mul_comm]
    exact hET.trans hLa
  have hJ₂ : (J₂ : ℝ) * mesh x ≤ 1 - 3 * margin x :=
    (le_div_iff₀ hm).1 (Nat.floor_le (div_nonneg (by linarith) hm.le))
  have hprod : ∀ j ∈ cellPairs₂ x, ∀ Q ∈ pairBox x j,
      ∏ q ∈ ({Q.1, Q.2} : Finset ℕ), q = Q.1 * Q.2 := fun _ _ Q hQ =>
    prod_pair (mem_filter.1 hQ).2
  -- the hypotheses of `abs_sum_sigma_sub_le` for the cell pairs of `region₂`
  have hadm : ∀ j ∈ cellPairs₂ x, ∀ Q ∈ pairBox x j, Admissible x (pairTop x j) {Q.1, Q.2} :=
    fun _ hj _ hQ => admissible_pairBox hx hm ha.le hj hQ
  have hA : ∀ j ∈ cellPairs₂ x, ∀ Q ∈ pairBox x j,
      |1 - spareModel c x (pairTop x j) {Q.1, Q.2}| ≤ 1 / T ^ 10 := fun j hj Q hQ =>
    (hdef c x _ _ hx hm hδ h2δ hδa (hadm j hj Q hQ)).trans (hS.defect_le hxa)
  have hJ : ∀ j ∈ cellPairs₂ x, (spareCount c x (pairTop x j) : ℝ) ≤ 2 * T ^ 20 := fun j _ =>
    (spareCount_le hm hδ.le (by unfold pairTop; positivity)).trans hS.inv_mesh_le
  have hmass : ∑ j ∈ cellPairs₂ x, ∑ Q ∈ pairBox x j,
      (1 : ℝ) / (∏ q ∈ ({Q.1, Q.2} : Finset ℕ), q : ℕ) ≤ 49 * T ^ 2 := by
    have h7 := sum_cell_inv_le hmert hx hS.one_le hm h2a hEa (J := J₂) (by linarith)
    have h0 : 0 ≤ ∑ j ∈ range J₂, ∑ q ∈ cell x j, (1 : ℝ) / q :=
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity
    calc _ = ∑ j ∈ cellPairs₂ x, ∑ Q ∈ pairBox x j, (1 : ℝ) / (Q.1 * Q.2) :=
          sum_congr rfl fun j hj => sum_congr rfl fun Q hQ => by
            rw [hprod j hj Q hQ, Nat.cast_mul]
      _ ≤ ∑ j ∈ cellPairs₂ x, ∑ Q ∈ cell x j.1 ×ˢ cell x j.2, (1 : ℝ) / (Q.1 * Q.2) :=
          sum_le_sum fun j _ => sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun _ _ _ => by positivity
      _ ≤ ∑ j ∈ range J₂ ×ˢ range J₂, ∑ Q ∈ cell x j.1 ×ˢ cell x j.2, (1 : ℝ) / (Q.1 * Q.2) :=
          sum_le_sum_of_subset_of_nonneg (fun j hj => (mem_filter.1 hj).1)
            fun _ _ _ => sum_nonneg fun _ _ => by positivity
      _ = (∑ j ∈ range J₂, ∑ q ∈ cell x j, (1 : ℝ) / q) ^ 2 := by
          rw [sq, sum_mul_sum, sum_product]
          refine sum_congr rfl fun j₁ _ => sum_congr rfl fun j₂ _ => ?_
          rw [sum_mul_sum, sum_product]
          exact sum_congr rfl fun q _ => sum_congr rfl fun r _ => (one_div_mul_one_div _ _).symm
      _ ≤ 49 * T ^ 2 := by nlinarith
  have h₁ : ∀ j ∈ cellPairs₂ x, ∀ j' < spareCount c x (pairTop x j), ∀ b : ℕ × ℕ → ℝ,
      (∀ Q, |b Q| ≤ 1) →
      |∑ p ∈ dyadicPrimes x, ∑ Q ∈ pairBox x j, ∑ r ∈ spareCell c x j' with
          r ∉ ({Q.1, Q.2} : Finset ℕ) ∧ (∏ q ∈ ({Q.1, Q.2} : Finset ℕ), q) * r ∣ p - 1, b Q -
        (dyadicPrimes x).card * ∑ Q ∈ pairBox x j, ∑ r ∈ spareCell c x j' with
          r ∉ ({Q.1, Q.2} : Finset ℕ),
            b Q / ((∏ q ∈ ({Q.1, Q.2} : Finset ℕ), q : ℕ) * r)| ≤
        (dyadicPrimes x).card * (|C| / T ^ 300) := by
    intro j hj j' hj' b hb
    have e₁ : ∀ p, ∑ Q ∈ pairBox x j, ∑ r ∈ spareCell c x j' with
        r ∉ ({Q.1, Q.2} : Finset ℕ) ∧ (∏ q ∈ ({Q.1, Q.2} : Finset ℕ), q) * r ∣ p - 1, b Q =
          ∑ Q ∈ pairBox x j, ∑ r ∈ spareCell c x j' with
            r ∉ ({Q.1, Q.2} : Finset ℕ) ∧ Q.1 * Q.2 * r ∣ p - 1, b Q := fun p =>
      sum_congr rfl fun Q hQ => by rw [hprod j hj Q hQ]
    have e₂ : ∑ Q ∈ pairBox x j, ∑ r ∈ spareCell c x j' with r ∉ ({Q.1, Q.2} : Finset ℕ),
        b Q / ((∏ q ∈ ({Q.1, Q.2} : Finset ℕ), q : ℕ) * r) =
          ∑ Q ∈ pairBox x j, ∑ r ∈ spareCell c x j' with r ∉ ({Q.1, Q.2} : Finset ℕ),
            b Q / (Q.1 * Q.2 * r) :=
      sum_congr rfl fun Q hQ => by rw [hprod j hj Q hQ, Nat.cast_mul]
    rw [sum_congr rfl fun p _ => e₁ p, e₂]
    have hj₁ : (0 : ℝ) ≤ j.1 * mesh x := by positivity
    have hj₂ : (0 : ℝ) ≤ j.2 * mesh x := by positivity
    have hj'm : (0 : ℝ) ≤ j' * mesh x := by positivity
    have hsum : margin x + (j.1 + 1) * mesh x + (margin x + (j.2 + 1) * mesh x) +
        (spareOffset c x + (j' + 1) * mesh x) ≤ 1 - c / T ^ 20 := by
      have := add_le_of_lt_spareCount hm hj'
      rw [pairTop] at this
      change _ ≤ 1 - spareOffset c x
      linarith
    refine (stat_two hRx hx0.le hP (u₀ := margin x + j.1 * mesh x)
      (v₀ := margin x + (j.1 + 1) * mesh x) (u₁ := margin x + j.2 * mesh x)
      (v₁ := margin x + (j.2 + 1) * mesh x) (u₂ := spareOffset c x + j' * mesh x)
      (v₂ := spareOffset c x + (j' + 1) * mesh x) (by linarith) (by linarith)
      (le_add_of_nonneg_right hj'm) hsum b hb).trans ?_
    gcongr
    exact le_abs_self C
  have h₀ : ∀ j ∈ cellPairs₂ x, |∑ p ∈ dyadicPrimes x, ∑ Q ∈ pairBox x j with
        (∏ q ∈ ({Q.1, Q.2} : Finset ℕ), q) ∣ p - 1, (1 : ℝ) -
      (dyadicPrimes x).card * ∑ Q ∈ pairBox x j,
        (1 : ℝ) / (∏ q ∈ ({Q.1, Q.2} : Finset ℕ), q : ℕ)| ≤
        (dyadicPrimes x).card * (|C| / T ^ 300) := by
    intro j hj
    have e₁ : ∀ p, ∑ Q ∈ pairBox x j with (∏ q ∈ ({Q.1, Q.2} : Finset ℕ), q) ∣ p - 1,
        (1 : ℝ) = ∑ q ∈ cell x j.1, ∑ r ∈ cell x j.2 with r ≠ q ∧ q * r ∣ p - 1, (1 : ℝ) :=
      fun p => Eq.trans (sum_congr (filter_congr fun Q hQ => by rw [hprod j hj Q hQ])
        fun _ _ => rfl) (sum_pairs_filter _ _ (fun q r => q * r ∣ p - 1) fun _ _ => 1)
    have e₂ : ∑ Q ∈ pairBox x j, (1 : ℝ) / (∏ q ∈ ({Q.1, Q.2} : Finset ℕ), q : ℕ) =
        ∑ q ∈ cell x j.1, ∑ r ∈ cell x j.2 with r ≠ q, (1 : ℝ) / (q * r) :=
      Eq.trans (sum_congr rfl fun Q hQ => by rw [hprod j hj Q hQ, Nat.cast_mul])
        (sum_pairs _ _ fun q r => (1 : ℝ) / (q * r))
    rw [sum_congr rfl fun p _ => e₁ p, e₂]
    have htop := pairTop_le hm hj
    rw [pairTop] at htop
    have hj₁ : (0 : ℝ) ≤ j.1 * mesh x := by positivity
    have hj₂ : (0 : ℝ) ≤ j.2 * mesh x := by positivity
    refine (stat_one hRx hx0.le hP (u₀ := margin x + j.1 * mesh x)
      (v₀ := margin x + (j.1 + 1) * mesh x) (u₁ := margin x + j.2 * mesh x)
      (v₁ := margin x + (j.2 + 1) * mesh x) (by linarith) (by linarith) (by linarith)
      (fun _ => 1) fun _ => by simp).trans ?_
    gcongr
    exact le_abs_self C
  have hcore := abs_sum_sigma_sub_le (c := c) (x := x) (ε₁ := |C| / T ^ 300)
    (ε₂ := 1 / T ^ 10) (M := 49 * T ^ 2) (Jmax := 2 * T ^ 20) (dyadicPrimes x)
    (cellPairs₂ x) (pairBox x) (fun Q => {Q.1, Q.2}) (pairTop x) hx hm hδ hδa
    (fun p hp => pred_of_mem_dyadicPrimes hp) hadm hA hJ hmass (by positivity)
    (by positivity) h₁ h₀ (fun Q => B Q.1 Q.2) fun Q => hB Q.1 Q.2
  -- back from `Finset.sigma` to `region₂`
  have hdisj : (↑(cellPairs₂ x) : Set (ℕ × ℕ)).PairwiseDisjoint (pairBox x) :=
    fun i _ j _ hij => disjoint_left.2 fun Q hi hj => by
      obtain ⟨hi₁, hi₂⟩ := mem_product.1 (mem_filter.1 hi).1
      obtain ⟨hj₁, hj₂⟩ := mem_product.1 (mem_filter.1 hj).1
      exact hij (Prod.ext (eq_of_mem_cell hx.le hi₁ hj₁) (eq_of_mem_cell hx.le hi₂ hj₂))
  have hsig : ∀ z ∈ (cellPairs₂ x).sigma (pairBox x),
      ∏ q ∈ ({z.2.1, z.2.2} : Finset ℕ), q = z.2.1 * z.2.2 := fun z hz =>
    hprod _ (mem_sigma.1 hz).1 _ (mem_sigma.1 hz).2
  have e₁ : ∀ p, ∑ Q ∈ region₂ x with Q.1 * Q.2 ∣ p - 1, B Q.1 Q.2 =
      ∑ z ∈ (cellPairs₂ x).sigma (pairBox x) with
        (∏ q ∈ ({z.2.1, z.2.2} : Finset ℕ), q) ∣ p - 1, B z.2.1 z.2.2 := fun p =>
    (sum_biUnion_eq_sum_sigma _ _ hdisj (fun Q => Q.1 * Q.2 ∣ p - 1)
      fun Q => B Q.1 Q.2).trans
      (sum_congr (filter_congr fun z hz => by rw [hsig z hz]) fun _ _ => rfl)
  have e₂ : ∑ Q ∈ region₂ x, B Q.1 Q.2 / (Q.1 * Q.2) =
      ∑ z ∈ (cellPairs₂ x).sigma (pairBox x),
        B z.2.1 z.2.2 / (∏ q ∈ ({z.2.1, z.2.2} : Finset ℕ), q : ℕ) := by
    change ∑ Q ∈ (cellPairs₂ x).biUnion (pairBox x), B Q.1 Q.2 / (Q.1 * Q.2) = _
    rw [sum_biUnion hdisj, sum_sigma]
    exact sum_congr rfl fun j hj => sum_congr rfl fun Q hQ => by
      rw [hprod j hj Q hQ, Nat.cast_mul]
  rw [Finset.sum_congr rfl fun p _ => e₁ p, e₂]
  refine hcore.trans ?_
  have hcard : ((cellPairs₂ x).card : ℝ) ≤ 4 * T ^ 40 := by
    have h1 : (J₂ : ℝ) ≤ 1 / mesh x := by
      rw [le_div_iff₀ hm]; linarith
    have h2 : (J₂ : ℝ) ≤ 2 * T ^ 20 := h1.trans hS.inv_mesh_le
    have h3 : ((cellPairs₂ x).card : ℝ) ≤ J₂ * J₂ := by
      have : (cellPairs₂ x).card ≤ (range J₂ ×ˢ range J₂).card := card_filter_le _ _
      rw [card_product, card_range] at this
      exact_mod_cast this
    calc ((cellPairs₂ x).card : ℝ) ≤ J₂ * J₂ := h3
      _ ≤ (2 * T ^ 20) * (2 * T ^ 20) := by gcongr
      _ = 4 * T ^ 40 := by ring
  calc _ ≤ (dyadicPrimes x).card * ((20 * |C| + 98) / T ^ 7) := by
        gcongr
        exact total_error_le hS.one_le hcard le_rfl
    _ = _ := by ring

end Erdos408
