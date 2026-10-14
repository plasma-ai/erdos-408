import Erdos408.Mertens

/-!
# The logarithmic grid and the staircase regions

Write `L = log x`, `T = log L`, `a = T⁻⁶` (`margin x`) and `m = 1 / ⌈T²⁰⌉`
(`mesh x`). The cell `J_j` is the set of primes `q` with
`a + j m < log q / L ≤ a + (j + 1) m`.

* `region₁ x` is the union of the first `⌊(1 - 2a) / m⌋` cells. It is the set
  of primes in `(x^a, x^U]` for some `1 - a - m < U ≤ 1 - a`.
* `region₂ x` is the staircase of ordered pairs of distinct primes in cells
  `J_{j₁} × J_{j₂}` with `j₁ + j₂ + 2 ≤ ⌊(1 - 3a) / m⌋`. Every such pair has
  `q r ≤ x^{1-a}`, and every pair of distinct primes above `x^a` with
  `q r ≤ x^{1 - a - 3m}` lies in it.

Both regions are finite unions of cells, so a rectangle statistic applies to
each piece exactly and no boundary strip arises. The model lower bounds below
follow from Mertens' first theorem on each cell.
-/

namespace Erdos408

/-- The lower and product margin `a = T⁻⁶`, where `T = log log x`. -/
noncomputable def margin (x : ℝ) : ℝ :=
  1 / Real.log (Real.log x) ^ 6

/-- The number of mesh cells per unit, `⌈T²⁰⌉`. -/
noncomputable def meshCount (x : ℝ) : ℕ :=
  ⌈Real.log (Real.log x) ^ 20⌉₊

/-- The mesh `m = 1 / ⌈T²⁰⌉`. -/
noncomputable def mesh (x : ℝ) : ℝ :=
  1 / meshCount x

/-- The cell `J_j`: primes `q` with `x^{a + j m} < q ≤ x^{a + (j + 1) m}`. -/
noncomputable def cell (x : ℝ) (j : ℕ) : Finset ℕ :=
  primesIoc (x ^ (margin x + j * mesh x)) (x ^ (margin x + (j + 1) * mesh x))

/-- The number of cells in `region₁`, `⌊(1 - 2a) / m⌋`. -/
noncomputable def cellCount₁ (x : ℝ) : ℕ :=
  ⌊(1 - 2 * margin x) / mesh x⌋₊

/-- The bound on `j₁ + j₂ + 2` in `region₂`, `⌊(1 - 3a) / m⌋`. -/
noncomputable def cellCount₂ (x : ℝ) : ℕ :=
  ⌊(1 - 3 * margin x) / mesh x⌋₊

/-- The primes in the first `⌊(1 - 2a) / m⌋` cells. -/
noncomputable def region₁ (x : ℝ) : Finset ℕ :=
  (Finset.range (cellCount₁ x)).biUnion (cell x)

/-- The admissible pairs of cell indices of `region₂`. -/
noncomputable def cellPairs₂ (x : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.range (cellCount₂ x) ×ˢ Finset.range (cellCount₂ x)).filter
    fun j => j.1 + j.2 + 2 ≤ cellCount₂ x

/-- The ordered pairs of distinct primes in the admissible cell pairs. -/
noncomputable def region₂ (x : ℝ) : Finset (ℕ × ℕ) :=
  (cellPairs₂ x).biUnion fun j => (cell x j.1 ×ˢ cell x j.2).filter fun q => q.1 ≠ q.2

open Filter Real Finset

/-- `q ∈ J_j` iff `q` is a prime with `x^{a + j m} < q ≤ x^{a + (j + 1) m}`. -/
theorem mem_cell {x : ℝ} (_hx : 0 ≤ x) {j q : ℕ} :
    q ∈ cell x j ↔ q.Prime ∧ x ^ (margin x + j * mesh x) < q ∧
      (q : ℝ) ≤ x ^ (margin x + (j + 1) * mesh x) :=
  mem_primesIoc

/-- For `x > 1`, `q ∈ J_j` iff `q` is a prime with `a + j m < log q / L ≤ a + (j + 1) m`. -/
theorem mem_cell_iff_log {x : ℝ} (hx : 1 < x) {j q : ℕ} :
    q ∈ cell x j ↔ q.Prime ∧ margin x + j * mesh x < Real.log q / Real.log x ∧
      Real.log q / Real.log x ≤ margin x + (j + 1) * mesh x := by
  have hL : 0 < Real.log x := Real.log_pos hx
  rw [mem_cell (by linarith)]
  refine and_congr_right fun hq => ?_
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  rw [rpow_lt_iff_lt_log (by linarith) hq0, le_rpow_iff_log_le hq0 (by linarith),
    lt_div_iff₀ hL, div_le_iff₀ hL]

/-- For `x ≥ 1`, a prime lies in at most one cell. -/
theorem eq_of_mem_cell {x : ℝ} (hx : 1 ≤ x) {i j q : ℕ} (hi : q ∈ cell x i)
    (hj : q ∈ cell x j) : i = j := by
  rw [mem_cell (by linarith)] at hi hj
  have hm : 0 ≤ mesh x := by unfold mesh; positivity
  -- the top of the lower cell is at most the bottom of the upper cell
  have key : ∀ {k l : ℕ}, k < l →
      x ^ (margin x + (k + 1) * mesh x) ≤ x ^ (margin x + l * mesh x) := fun {k l} h =>
    rpow_le_rpow_of_exponent_le hx
      (by linarith [mul_le_mul_of_nonneg_right (show (k : ℝ) + 1 ≤ l by exact_mod_cast h) hm])
  rcases lt_trichotomy i j with h | h | h
  · linarith [key h]
  · exact h
  · linarith [key h]

/-- For `x ≥ 1`, distinct cells are disjoint. -/
theorem disjoint_cell {x : ℝ} (hx : 1 ≤ x) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (cell x i) (cell x j) :=
  disjoint_left.2 fun _ hi hj => hij (eq_of_mem_cell hx hi hj)

/-- For `x > 1` and `m > 0`, every prime above `x^a` lies in some cell. -/
theorem exists_mem_cell {x : ℝ} (hx : 1 < x) (hm : 0 < mesh x) {q : ℕ} (hq : q.Prime)
    (hxq : x ^ margin x < q) : ∃ j : ℕ, q ∈ cell x j := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have ht : margin x < Real.log q / Real.log x := by
    rwa [rpow_lt_iff_lt_log (by linarith) hq0, ← lt_div_iff₀ hL] at hxq
  -- `j = ⌈(t_q - a) / m⌉ - 1`
  set u := (Real.log q / Real.log x - margin x) / mesh x
  have hu : 0 < u := div_pos (by linarith) hm
  have hum : u * mesh x = Real.log q / Real.log x - margin x := div_mul_cancel₀ _ hm.ne'
  have hc : 1 ≤ ⌈u⌉₊ := Nat.ceil_pos.2 hu
  have hcast : ((⌈u⌉₊ - 1 : ℕ) : ℝ) = ⌈u⌉₊ - 1 := by rw [Nat.cast_sub hc, Nat.cast_one]
  refine ⟨⌈u⌉₊ - 1, (mem_cell_iff_log hx).2 ⟨hq, ?_, ?_⟩⟩
  · have h := mul_lt_mul_of_pos_right (show (⌈u⌉₊ : ℝ) - 1 < u by
      linarith [Nat.ceil_lt_add_one hu.le]) hm
    rw [hcast]
    linarith
  · have h := mul_le_mul_of_nonneg_right (Nat.le_ceil u) hm.le
    rw [hcast, sub_add_cancel]
    linarith

/-- Mertens' first theorem on a cell: `∑_{q ∈ J_j} (log q / L) / q = m + O(1 / L)`. -/
theorem exists_abs_sum_cell_sub_mesh_le : ∃ E : ℝ, 0 ≤ E ∧ ∀ x : ℝ, 1 < x → ∀ j : ℕ,
    |∑ q ∈ cell x j, Real.log q / Real.log x / q - mesh x| ≤ E / Real.log x := by
  obtain ⟨E, hE, hmert⟩ := mertens_first
  refine ⟨E, hE, fun x hx j => ?_⟩
  have hL : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have ha : 0 ≤ margin x := by unfold margin; positivity
  have hm : 0 ≤ mesh x := by unfold mesh; positivity
  have h := hmert (x ^ (margin x + j * mesh x)) (x ^ (margin x + (j + 1) * mesh x))
    (one_le_rpow hx.le (add_nonneg ha (mul_nonneg (Nat.cast_nonneg _) hm)))
    (rpow_le_rpow_of_exponent_le hx.le (by nlinarith))
  rw [← rpow_sub hx0, log_rpow hx0,
    show margin x + (j + 1) * mesh x - (margin x + j * mesh x) = mesh x by ring] at h
  have hsum : ∑ q ∈ cell x j, Real.log q / Real.log x / q - mesh x =
      (∑ p ∈ cell x j, Real.log p / p - mesh x * Real.log x) / Real.log x := by
    rw [sub_div, sum_div, mul_div_cancel_right₀ _ hL.ne']
    exact congrArg (· - _) (sum_congr rfl fun q _ => div_right_comm _ _ _)
  rw [hsum, abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right h hL.le

/-- Consecutive intervals `(f j, f (j + 1)]` of a monotone `f` telescope. -/
private lemma biUnion_range_Ioc {f : ℕ → ℕ} (hf : Monotone f) (n : ℕ) :
    (range n).biUnion (fun j => Ioc (f j) (f (j + 1))) = Ioc (f 0) (f n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [range_add_one, biUnion_insert, ih, union_comm,
      Ioc_union_Ioc_eq_Ioc (hf (Nat.zero_le n)) (hf n.le_succ)]

/-- For `x ≥ 1`, `region₁ x` is the set of primes in `(x^a, x^{a + J₁ m}]`. -/
theorem region₁_eq_primesIoc {x : ℝ} (hx : 1 ≤ x) :
    region₁ x = primesIoc (x ^ margin x) (x ^ (margin x + cellCount₁ x * mesh x)) := by
  have hm : 0 ≤ mesh x := by unfold mesh; positivity
  let f : ℕ → ℕ := fun j => ⌊x ^ (margin x + j * mesh x)⌋₊
  have hf : Monotone f := monotone_nat_of_le_succ fun j =>
    Nat.floor_le_floor (rpow_le_rpow_of_exponent_le hx (by push_cast; nlinarith))
  have hcell : cell x = fun j => (Ioc (f j) (f (j + 1))).filter Nat.Prime := by
    ext j : 1
    simp only [cell, primesIoc, f, Nat.cast_succ]
  rw [region₁, hcell, ← filter_biUnion, biUnion_range_Ioc hf]
  simp [primesIoc, f]

/-- `∑_{j < n} j = n (n - 1) / 2` in `ℝ`. -/
private lemma sum_range_cast (n : ℕ) : ∑ j ∈ range n, (j : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- `∑_{j < n} ((a + j m) m - c) = a (n m) + ((n m)² - (n m) m) / 2 - n c`. -/
private lemma sum_range_affine (a m c : ℝ) (n : ℕ) :
    ∑ j ∈ range n, ((a + j * m) * m - c) =
      a * (n * m) + ((n * m) ^ 2 - n * m * m) / 2 - n * c := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- The number of admissible cell pairs is `J₂ (J₂ - 1) / 2`. -/
private lemma card_cellPairs₂ (x : ℝ) :
    ((cellPairs₂ x).card : ℝ) = cellCount₂ x * (cellCount₂ x - 1) / 2 := by
  have h : (cellPairs₂ x).card = ∑ j ∈ range (cellCount₂ x), (cellCount₂ x - 1 - j) := by
    rw [cellPairs₂, card_filter, sum_product]
    refine sum_congr rfl fun j hj => ?_
    rw [← card_filter, ← card_range (cellCount₂ x - 1 - j)]
    congr 1
    ext k
    simp only [mem_filter, mem_range] at hj ⊢
    omega
  have hr := sum_range_reflect (fun j => j) (cellCount₂ x)
  rw [h, hr, Nat.cast_sum, sum_range_cast]

/-- `T = log log x` tends to infinity. -/
private lemma tendsto_loglog : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
  tendsto_log_atTop.comp tendsto_log_atTop

/-- The margin `a = T⁻⁶` tends to `0`. -/
theorem tendsto_margin : Filter.Tendsto margin Filter.atTop (nhds 0) := by
  have h := ((tendsto_pow_atTop (by norm_num : 6 ≠ 0)).comp tendsto_loglog).inv_tendsto_atTop
  have hm : margin = (fun x : ℝ => Real.log (Real.log x) ^ 6)⁻¹ := by
    funext x
    simp [margin]
  rw [hm]
  exact h

/-- Eventually `1 / (2 T²⁰) ≤ m ≤ 1 / T²⁰`. -/
theorem mesh_le_margin_pow : ∀ᶠ x : ℝ in Filter.atTop,
    mesh x ≤ 1 / Real.log (Real.log x) ^ 20 ∧ 1 / (2 * Real.log (Real.log x) ^ 20) ≤ mesh x := by
  filter_upwards [tendsto_loglog.eventually_ge_atTop 1] with x hT
  have hT20 : 1 ≤ Real.log (Real.log x) ^ 20 := one_le_pow₀ hT
  have hN : Real.log (Real.log x) ^ 20 ≤ meshCount x := Nat.le_ceil _
  have hN' : (meshCount x : ℝ) < Real.log (Real.log x) ^ 20 + 1 := Nat.ceil_lt_add_one (by linarith)
  exact ⟨one_div_le_one_div_of_le (by linarith) hN,
    one_div_le_one_div_of_le (by linarith) (by linarith)⟩

/-- `log x` eventually dominates every fixed multiple of every power of `T = log log x`. -/
private lemma eventually_mul_loglog_pow_le_log (C : ℝ) (n : ℕ) :
    ∀ᶠ x : ℝ in atTop, C * Real.log (Real.log x) ^ n ≤ Real.log x := by
  filter_upwards [tendsto_loglog.eventually ((tendsto_exp_div_pow_atTop n).eventually_ge_atTop C),
    tendsto_loglog.eventually_gt_atTop 0, tendsto_log_atTop.eventually_gt_atTop 0]
    with x hC hT hL
  rwa [le_div_iff₀ (pow_pos hT n), exp_log hL] at hC

/-- The eventual size conditions on the grid: `a, m ≤ 1 / 10`, `E ≤ m² L` and `2 ≤ m² x^a`. -/
private lemma eventually_grid (E : ℝ) : ∀ᶠ x : ℝ in atTop, 1 < x ∧ 0 < mesh x ∧
    margin x ≤ 1 / 10 ∧ mesh x ≤ 1 / 10 ∧ E ≤ mesh x ^ 2 * Real.log x ∧
      2 ≤ mesh x ^ 2 * x ^ margin x := by
  filter_upwards [eventually_gt_atTop 1, mesh_le_margin_pow, tendsto_loglog.eventually_ge_atTop 10,
    eventually_mul_loglog_pow_le_log (8 * (|E| + 1)) 46] with x hx ⟨hm₁, hm₂⟩ hT hC
  set T := Real.log (Real.log x)
  have hL : 0 < Real.log x := Real.log_pos hx
  have hT0 : 0 < T := by linarith
  have hT20 : T ≤ T ^ 20 := le_self_pow₀ (by linarith) (by norm_num)
  have hT6 : T ≤ T ^ 6 := le_self_pow₀ (by linarith) (by norm_num)
  have hT46 : T ^ 40 ≤ T ^ 46 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hm0 : 0 < mesh x := lt_of_lt_of_le (by positivity) hm₂
  have hE : 0 ≤ |E| := abs_nonneg E
  -- `m² ≥ 1 / (4 T⁴⁰)`
  have hmsq : 1 / (4 * T ^ 40) ≤ mesh x ^ 2 := by
    calc 1 / (4 * T ^ 40) = (1 / (2 * T ^ 20)) ^ 2 := by ring
      _ ≤ mesh x ^ 2 := pow_le_pow_left₀ (by positivity) hm₂ 2
  -- `x^a ≥ a L = L / T⁶`
  have hxa : Real.log x / T ^ 6 ≤ x ^ margin x := by
    rw [rpow_def_of_pos (by linarith)]
    have h := add_one_le_exp (Real.log x * margin x)
    have h' : Real.log x * margin x = Real.log x / T ^ 6 := by rw [margin, mul_one_div]
    linarith
  refine ⟨hx, hm0, ?_, ?_, ?_, ?_⟩
  · rw [margin, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  · calc mesh x ≤ 1 / T ^ 20 := hm₁
      _ ≤ 1 / 10 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  · have h := mul_le_mul_of_nonneg_left hT46 (by linarith : 0 ≤ 8 * (|E| + 1))
    calc E ≤ 2 * (|E| + 1) := by linarith [le_abs_self E]
      _ ≤ Real.log x / (4 * T ^ 40) := by rw [le_div_iff₀ (by positivity)]; linarith
      _ = 1 / (4 * T ^ 40) * Real.log x := by ring
      _ ≤ mesh x ^ 2 * Real.log x := mul_le_mul_of_nonneg_right hmsq hL.le
  · have h := mul_nonneg hE (pow_pos hT0 46).le
    calc (2 : ℝ) ≤ Real.log x / (4 * T ^ 46) := by rw [le_div_iff₀ (by positivity)]; linarith
      _ = 1 / (4 * T ^ 40) * (Real.log x / T ^ 6) := by field_simp
      _ ≤ mesh x ^ 2 * x ^ margin x :=
        mul_le_mul hmsq hxa (by positivity) (by positivity)

/-- `region₁ x` is the set of primes in `(x^a, x^U]` for some
`1 - a - m < U ≤ 1 - a`. -/
theorem exists_region₁_eq : ∀ᶠ x : ℝ in Filter.atTop, ∃ U : ℝ,
    1 - margin x - mesh x < U ∧ U ≤ 1 - margin x ∧
      region₁ x = primesIoc (x ^ margin x) (x ^ U) := by
  filter_upwards [eventually_grid 0] with x ⟨hx, hm, ha, _, _, _⟩
  have hJ : (cellCount₁ x : ℝ) ≤ (1 - 2 * margin x) / mesh x :=
    Nat.floor_le (div_nonneg (by linarith) hm.le)
  have hJ' : (1 - 2 * margin x) / mesh x < cellCount₁ x + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hm] at hJ
  rw [div_lt_iff₀ hm, add_mul, one_mul] at hJ'
  exact ⟨margin x + cellCount₁ x * mesh x, by linarith, by linarith, region₁_eq_primesIoc hx.le⟩

/-- Every pair in `region₂` consists of distinct primes above `x^a` with
`q r ≤ x^{1-a}`, and both lie in `region₁`. -/
theorem mem_region₂ : ∀ᶠ x : ℝ in Filter.atTop, ∀ Q ∈ region₂ x,
    Q.1 ∈ region₁ x ∧ Q.2 ∈ region₁ x ∧ Q.1 ≠ Q.2 ∧
      x ^ margin x < Q.1 ∧ x ^ margin x < Q.2 ∧
        ((Q.1 * Q.2 : ℕ) : ℝ) ≤ x ^ (1 - margin x) := by
  filter_upwards [eventually_grid 0] with x ⟨hx, hm, ha, _, _, _⟩
  rintro ⟨q, r⟩ hQ
  simp only [region₂, cellPairs₂, mem_biUnion, mem_filter, mem_product, mem_range] at hQ
  obtain ⟨⟨j₁, j₂⟩, ⟨-, hj⟩, ⟨hq, hr⟩, hqr⟩ := hQ
  have ha0 : 0 ≤ margin x := by unfold margin; positivity
  have hJ : cellCount₂ x ≤ cellCount₁ x :=
    Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hm.le)
  have hJm : (cellCount₂ x : ℝ) * mesh x ≤ 1 - 3 * margin x :=
    (le_div_iff₀ hm).1 (Nat.floor_le (div_nonneg (by linarith) hm.le))
  have hj' : (j₁ : ℝ) + j₂ + 2 ≤ cellCount₂ x := by exact_mod_cast hj
  have hq' := (mem_cell (by linarith)).1 hq
  have hr' := (mem_cell (by linarith)).1 hr
  -- the bottom of every cell is at least `x^a`
  have hbot : ∀ j : ℕ, x ^ margin x ≤ x ^ (margin x + j * mesh x) := fun j =>
    rpow_le_rpow_of_exponent_le hx.le (le_add_of_nonneg_right (by positivity))
  refine ⟨mem_biUnion.2 ⟨j₁, mem_range.2 (by omega), hq⟩,
    mem_biUnion.2 ⟨j₂, mem_range.2 (by omega), hr⟩, hqr, (hbot j₁).trans_lt hq'.2.1,
    (hbot j₂).trans_lt hr'.2.1, ?_⟩
  push_cast
  calc (q : ℝ) * r ≤ x ^ (margin x + (j₁ + 1) * mesh x) * x ^ (margin x + (j₂ + 1) * mesh x) :=
        mul_le_mul hq'.2.2 hr'.2.2 (Nat.cast_nonneg _) (by positivity)
    _ = x ^ (2 * margin x + (j₁ + j₂ + 2) * mesh x) := by
        rw [← rpow_add (by linarith)]
        ring_nf
    _ ≤ x ^ (1 - margin x) := rpow_le_rpow_of_exponent_le hx.le
        (by nlinarith [mul_le_mul_of_nonneg_right hj' hm.le])

/-- Every pair of distinct primes above `x^a` with `q r ≤ x^{1 - a - 3m}`
lies in `region₂`. -/
theorem mem_region₂_of_mul_le : ∀ᶠ x : ℝ in Filter.atTop, ∀ q r : ℕ, q.Prime → r.Prime →
    q ≠ r → x ^ margin x < q → x ^ margin x < r →
      ((q * r : ℕ) : ℝ) ≤ x ^ (1 - margin x - 3 * mesh x) → (q, r) ∈ region₂ x := by
  filter_upwards [eventually_grid 0] with x ⟨hx, hm, ha, _, _, _⟩
  intro q r hq hr hqr hxq hxr hmul
  have hL : 0 < Real.log x := Real.log_pos hx
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  obtain ⟨j₁, hj₁⟩ := exists_mem_cell hx hm hq hxq
  obtain ⟨j₂, hj₂⟩ := exists_mem_cell hx hm hr hxr
  have h₁ := ((mem_cell_iff_log hx).1 hj₁).2.1
  have h₂ := ((mem_cell_iff_log hx).1 hj₂).2.1
  -- `t_q + t_r ≤ 1 - a - 3m`
  have hsum : Real.log q / Real.log x + Real.log r / Real.log x ≤
      1 - margin x - 3 * mesh x := by
    push_cast at hmul
    rw [le_rpow_iff_log_le (by positivity) (by linarith), Real.log_mul hq0.ne' hr0.ne'] at hmul
    rw [← add_div, div_le_iff₀ hL]
    exact hmul
  have hj : j₁ + j₂ + 2 ≤ cellCount₂ x := by
    rw [cellCount₂, Nat.le_floor_iff (div_nonneg (by linarith) hm.le), le_div_iff₀ hm]
    push_cast
    nlinarith
  simp only [region₂, cellPairs₂, mem_biUnion, mem_filter, mem_product, mem_range]
  exact ⟨(j₁, j₂), ⟨⟨by omega, by omega⟩, hj⟩, ⟨hj₁, hj₂⟩, hqr⟩

/-- The model second moment of `region₁`:
`∑ (log q / L)² / q ≥ ((1 - a)² - a²) / 2 - O(m)`. -/
theorem region₁_square_model : ∃ K : ℝ, ∀ᶠ x : ℝ in Filter.atTop,
    ((1 - margin x) ^ 2 - margin x ^ 2) / 2 - K * mesh x ≤
      ∑ q ∈ region₁ x, (Real.log q / Real.log x) ^ 2 / q := by
  obtain ⟨E, hE, hcell⟩ := exists_abs_sum_cell_sub_mesh_le
  refine ⟨3, ?_⟩
  filter_upwards [eventually_grid E] with x ⟨hx, hm, ha, hm', hEm, _⟩
  have hL : 0 < Real.log x := Real.log_pos hx
  have ha0 : 0 ≤ margin x := by unfold margin; positivity
  have hJ : (cellCount₁ x : ℝ) * mesh x ≤ 1 - 2 * margin x :=
    (le_div_iff₀ hm).1 (Nat.floor_le (div_nonneg (by linarith) hm.le))
  have hJ' : 1 - 2 * margin x < cellCount₁ x * mesh x + mesh x := by
    have h := Nat.lt_floor_add_one ((1 - 2 * margin x) / mesh x)
    rwa [div_lt_iff₀ hm, add_mul, one_mul] at h
  -- the Mertens losses: `E / L ≤ m` and `J₁ E / L ≤ m`
  have hEL : E / Real.log x ≤ mesh x ^ 2 := by rwa [div_le_iff₀ hL]
  have hEL0 : 0 ≤ E / Real.log x := div_nonneg hE hL.le
  have hJE : cellCount₁ x * (E / Real.log x) ≤ mesh x := by
    have h := mul_le_mul_of_nonneg_left hEL (Nat.cast_nonneg (cellCount₁ x))
    nlinarith
  -- on `J_j`, `t_q > a + j m`, so `∑ t_q² / q ≥ (a + j m) ∑ t_q / q ≥ (a + j m) m - E / L`
  have hcellj : ∀ j ∈ range (cellCount₁ x), (margin x + j * mesh x) * mesh x - E / Real.log x ≤
      ∑ q ∈ cell x j, (Real.log q / Real.log x) ^ 2 / q := by
    intro j hj
    have hjJ : (j : ℝ) + 1 ≤ cellCount₁ x := by exact_mod_cast mem_range.1 hj
    have hamj0 : 0 ≤ margin x + j * mesh x := by positivity
    have hamj1 : margin x + j * mesh x ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hjJ hm.le]
    have hS := (abs_le.1 (hcell x hx j)).1
    calc (margin x + j * mesh x) * mesh x - E / Real.log x
        ≤ (margin x + j * mesh x) * ∑ q ∈ cell x j, Real.log q / Real.log x / q := by
          nlinarith [mul_le_mul_of_nonneg_left (show mesh x - E / Real.log x ≤
            ∑ q ∈ cell x j, Real.log q / Real.log x / q by linarith) hamj0]
      _ = ∑ q ∈ cell x j, (margin x + j * mesh x) * (Real.log q / Real.log x / q) := mul_sum _ _ _
      _ ≤ ∑ q ∈ cell x j, (Real.log q / Real.log x) ^ 2 / q := sum_le_sum fun q hq => by
          have ht := ((mem_cell_iff_log hx).1 hq).2.1
          rw [show (Real.log q / Real.log x) ^ 2 / q =
            Real.log q / Real.log x * (Real.log q / Real.log x / q) by ring]
          exact mul_le_mul_of_nonneg_right ht.le (by
            have := ((mem_cell_iff_log hx).1 hq).1.one_lt
            positivity)
  rw [region₁, sum_biUnion fun i _ j _ hij => disjoint_cell hx.le hij]
  refine le_trans ?_ (sum_le_sum hcellj)
  rw [sum_range_affine]
  -- with `V = J₁ m ∈ (1 - 2a - m, 1 - 2a]`, use `(V + a)² ≥ (1 - a - m)²`
  have hV := pow_le_pow_left₀ (by linarith) (show 1 - margin x - mesh x ≤
    cellCount₁ x * mesh x + margin x by linarith) 2
  nlinarith [mul_le_mul_of_nonneg_right (show (cellCount₁ x : ℝ) * mesh x ≤ 1 by linarith) hm.le,
    sq_nonneg (mesh x), mul_nonneg ha0 hm.le]

/-- The model mass of `region₂`:
`∑ (log q / L) (log r / L) / (q r) ≥ (1 - 3a)² / 2 - O(m)`. -/
theorem region₂_model : ∃ K : ℝ, ∀ᶠ x : ℝ in Filter.atTop,
    (1 - 3 * margin x) ^ 2 / 2 - K * mesh x ≤
      ∑ Q ∈ region₂ x, Real.log Q.1 / Real.log x * (Real.log Q.2 / Real.log x) /
        (Q.1 * Q.2) := by
  obtain ⟨E, hE, hcell⟩ := exists_abs_sum_cell_sub_mesh_le
  refine ⟨4, ?_⟩
  filter_upwards [eventually_grid (2 * E)] with x ⟨hx, hm, ha, hm', hEm, hxa⟩
  have hL : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have ha0 : 0 ≤ margin x := by unfold margin; positivity
  have hJ : (cellCount₂ x : ℝ) * mesh x ≤ 1 - 3 * margin x :=
    (le_div_iff₀ hm).1 (Nat.floor_le (div_nonneg (by linarith) hm.le))
  have hJ' : 1 - 3 * margin x < cellCount₂ x * mesh x + mesh x := by
    have h := Nat.lt_floor_add_one ((1 - 3 * margin x) / mesh x)
    rwa [div_lt_iff₀ hm, add_mul, one_mul] at h
  -- the losses: `E / L ≤ m² / 2` and `1 / x^a ≤ m² / 2`
  have hEL : E / Real.log x ≤ mesh x ^ 2 / 2 := by rw [div_le_iff₀ hL]; linarith
  have hEL0 : 0 ≤ E / Real.log x := div_nonneg hE hL.le
  have hELm : E / Real.log x ≤ mesh x := by nlinarith
  have hxa0 : 0 < x ^ margin x := rpow_pos_of_pos hx0 _
  have hxa' : 1 / x ^ margin x ≤ mesh x ^ 2 / 2 := by rw [div_le_iff₀ hxa0]; linarith
  have hS : ∀ j : ℕ, mesh x - E / Real.log x ≤ ∑ q ∈ cell x j, Real.log q / Real.log x / q ∧
      ∑ q ∈ cell x j, Real.log q / Real.log x / q ≤ mesh x + E / Real.log x := fun j => by
    have h := abs_le.1 (hcell x hx j)
    constructor <;> linarith
  -- on `J_j` with `j < J₂`, `0 ≤ t_q / q ≤ 1 / x^a`
  have hu : ∀ j : ℕ, j + 1 ≤ cellCount₂ x → ∀ q ∈ cell x j,
      0 ≤ Real.log q / Real.log x / q ∧ Real.log q / Real.log x / q ≤ 1 / x ^ margin x := by
    intro j hj q hq
    have h := (mem_cell_iff_log hx).1 hq
    have h' := (mem_cell hx0.le).1 hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast h.1.pos
    have hjJ : (j : ℝ) + 1 ≤ cellCount₂ x := by exact_mod_cast hj
    have ht1 : Real.log q / Real.log x ≤ 1 :=
      h.2.2.trans (by nlinarith [mul_le_mul_of_nonneg_right hjJ hm.le])
    have ht0 : 0 ≤ Real.log q / Real.log x := div_nonneg (Real.log_natCast_nonneg _) hL.le
    have hxq : x ^ margin x ≤ q := (rpow_le_rpow_of_exponent_le hx.le
      (le_add_of_nonneg_right (by positivity))).trans h'.2.1.le
    refine ⟨div_nonneg ht0 hq0.le, ?_⟩
    calc Real.log q / Real.log x / q ≤ 1 / q := div_le_div_of_nonneg_right ht1 hq0.le
      _ ≤ 1 / x ^ margin x := one_div_le_one_div_of_le hxa0 hxq
  have hF0 : ∀ Q : ℕ × ℕ, 0 ≤ Real.log Q.1 / Real.log x * (Real.log Q.2 / Real.log x) /
      (Q.1 * Q.2) := fun Q => div_nonneg (mul_nonneg (div_nonneg (Real.log_natCast_nonneg _)
        hL.le) (div_nonneg (Real.log_natCast_nonneg _) hL.le)) (by positivity)
  -- each admissible pair of cells carries mass at least `m² - 2 m³`
  have hpair : ∀ j ∈ cellPairs₂ x, mesh x ^ 2 - 2 * mesh x ^ 3 ≤
      ∑ Q ∈ (cell x j.1 ×ˢ cell x j.2).filter (fun q => q.1 ≠ q.2),
        Real.log Q.1 / Real.log x * (Real.log Q.2 / Real.log x) / (Q.1 * Q.2) := by
    rintro ⟨j₁, j₂⟩ hj
    simp only [cellPairs₂, mem_filter, mem_product, mem_range] at hj
    have hsplit := sum_filter_add_sum_filter_not (cell x j₁ ×ˢ cell x j₂)
      (fun Q : ℕ × ℕ => Q.1 ≠ Q.2)
      fun Q => Real.log Q.1 / Real.log x * (Real.log Q.2 / Real.log x) / (Q.1 * Q.2)
    -- the full rectangle factors
    have hprod : ∑ Q ∈ cell x j₁ ×ˢ cell x j₂,
        Real.log Q.1 / Real.log x * (Real.log Q.2 / Real.log x) / (Q.1 * Q.2) =
          (∑ q ∈ cell x j₁, Real.log q / Real.log x / q) *
            ∑ r ∈ cell x j₂, Real.log r / Real.log x / r := by
      rw [sum_product, sum_mul_sum]
      exact sum_congr rfl fun q _ => sum_congr rfl fun r _ => (div_mul_div_comm _ _ _ _).symm
    -- the diagonal is at most `(m + E / L) / x^a`
    have hsub : (cell x j₁ ×ˢ cell x j₂).filter (fun Q : ℕ × ℕ => ¬Q.1 ≠ Q.2) ⊆
        (cell x j₁).image fun q => (q, q) := by
      intro Q hQ
      rw [mem_filter, mem_product, not_not] at hQ
      exact mem_image.2 ⟨Q.1, hQ.1.1, Prod.ext rfl hQ.2⟩
    have hdiag : ∑ Q ∈ (cell x j₁ ×ˢ cell x j₂).filter (fun Q : ℕ × ℕ => ¬Q.1 ≠ Q.2),
        Real.log Q.1 / Real.log x * (Real.log Q.2 / Real.log x) / (Q.1 * Q.2) ≤
          (mesh x + E / Real.log x) * (1 / x ^ margin x) := by
      calc _ ≤ ∑ Q ∈ (cell x j₁).image (fun q => (q, q)),
            Real.log Q.1 / Real.log x * (Real.log Q.2 / Real.log x) / (Q.1 * Q.2) :=
            sum_le_sum_of_subset_of_nonneg hsub fun Q _ _ => hF0 Q
        _ = ∑ q ∈ cell x j₁, Real.log q / Real.log x / q * (Real.log q / Real.log x / q) := by
            rw [sum_image fun a _ b _ h => congrArg Prod.fst h]
            exact sum_congr rfl fun q _ => (div_mul_div_comm _ _ _ _).symm
        _ ≤ ∑ q ∈ cell x j₁, Real.log q / Real.log x / q * (1 / x ^ margin x) :=
            sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (hu j₁ (by omega) q hq).2
              (hu j₁ (by omega) q hq).1
        _ = (∑ q ∈ cell x j₁, Real.log q / Real.log x / q) * (1 / x ^ margin x) :=
            (sum_mul _ _ _).symm
        _ ≤ (mesh x + E / Real.log x) * (1 / x ^ margin x) :=
            mul_le_mul_of_nonneg_right (hS j₁).2 (by positivity)
    have hrect := mul_le_mul (hS j₁).1 (hS j₂).1 (by linarith) (by linarith [(hS j₁).1])
    have hA : 2 * mesh x * (E / Real.log x) ≤ mesh x ^ 3 := by nlinarith
    have hB : (mesh x + E / Real.log x) * (1 / x ^ margin x) ≤ mesh x ^ 3 :=
      calc _ ≤ (2 * mesh x) * (mesh x ^ 2 / 2) :=
            mul_le_mul (by nlinarith) hxa' (by positivity) (by positivity)
        _ = mesh x ^ 3 := by ring
    nlinarith
  rw [region₂, sum_biUnion fun i _ j _ hij => disjoint_left.2 fun Q hi hj => hij (by
    rw [mem_filter, mem_product] at hi hj
    exact Prod.ext (eq_of_mem_cell hx.le hi.1.1 hj.1.1) (eq_of_mem_cell hx.le hi.1.2 hj.1.2))]
  refine le_trans ?_ (sum_le_sum hpair)
  rw [sum_const, nsmul_eq_mul, card_cellPairs₂, show (cellCount₂ x : ℝ) * (cellCount₂ x - 1) / 2 *
    (mesh x ^ 2 - 2 * mesh x ^ 3) = ((cellCount₂ x * mesh x) ^ 2 -
      cellCount₂ x * mesh x * mesh x) / 2 * (1 - 2 * mesh x) by ring]
  -- with `V = J₂ m ∈ (1 - 3a - m, 1 - 3a]`, use `V² ≥ (1 - 3a - m)²`
  have hV := pow_le_pow_left₀ (by linarith) (show 1 - 3 * margin x - mesh x ≤
    cellCount₂ x * mesh x by linarith) 2
  have hV1 : (cellCount₂ x * mesh x : ℝ) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right (show (cellCount₂ x : ℝ) * mesh x ≤ 1 by linarith) hm.le,
    mul_le_mul_of_nonneg_left hV1 hm.le, mul_nonneg (mul_nonneg (Nat.cast_nonneg (cellCount₂ x))
      hm.le) (mul_nonneg hm.le hm.le), sq_nonneg (mesh x), mul_nonneg ha0 hm.le]

end Erdos408
