import Erdos408.OneSided.Model
import Erdos408.OneSided.Moment.Edge.Lattice
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Field.ZMod

/-!
# Lattice blocks in the root box

PD §4, "The lattice box and the clean signed norm", at a real root. The positions `z` of the
root box have `τ(z) ∈ [1/16, 16]`.

* Cells: `rootCell H r z = ⌊(z₂/τ(z))/H⌋` with `H = d₀ Y`. Since
  `z'₂/τ(z') - z₂/τ(z) = det(z, z')/(τ(z) τ(z'))`, an edge only joins nearby cells.
* Line tuples: `lineKey D z = ([z]_p)_{p ∣ D}`. For primitive `z, z'` and squarefree `D`,
  `lineKey D z = lineKey D z'` if and only if `D ∣ det(z, z')` (`lineKey_eq_iff`).
* `kerLe_shiftKernel_of_box`: the kernel
  `[z good] [D ∣ det(z, z')] [cell z' = cell z + δ] e(ϑ det(z, z')/D)` is block diagonal in the
  line tuple and the cell. In a block with a good source `z₀`, the lattice coordinates of M5
  (`exists_lattice_box`) embed the block into a box `|m₁| ≤ A'`, `|m₂| ≤ B'`, and turn
  `det(z, z')/D` into the determinant of the coordinates. Hence the kernel has the norm of the
  determinant matrix `e(ϑ (m₁ m₂' - m₂ m₁'))` on such boxes.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real

/-- `det(z, z') = z₁ z'₂ - z₂ z'₁`. -/
def zdet (z z' : ℤ × ℤ) : ℤ := z.1 * z'.2 - z.2 * z'.1

/-- The ratio `τ(w_z)/τ(z)` tested at a position. -/
def posRatio (r : ℝ) (z : ℤ × ℤ) : ℝ := tau r (complement z) / tau r z

/-- The pad part of test (i): `‖l D ρ‖ > Y^{-0.7}` for `1 ≤ l ≤ Y^{0.2}`. -/
def GoodPad (Y : ℝ) (D : ℕ) (ρ : ℝ) : Prop :=
  ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (1 / 5 : ℝ) → Y ^ (-(7 / 10 : ℝ)) < circleDist (l * D * ρ)

/-- The cell index `⌊(z₂/τ(z))/H⌋`. -/
def rootCell (H r : ℝ) (z : ℤ × ℤ) : ℤ := ⌊(z.2 / tau r z) / H⌋

/-- The line tuple `([z]_p)_{p ∣ D}`. -/
def lineKey (D : ℕ) (z : ℤ × ℤ) : ℕ → ℕ := fun p => if p ∈ D.primeFactors then lineOf p z else 0

/-- The box `|m₁| ≤ A`, `|m₂| ≤ B`. -/
def intBox (A B : ℕ) : Finset (ℤ × ℤ) := Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B

/-! ### Geometry of the root box -/

/-- Positions of the root box with `U ≤ u ≤ 16U` have `τ(z) ∈ [1/16, 16]`. -/
theorem tau_mem_of_mem_rootPositions {U V u v r : ℝ} (hU : 0 < U) (hUu : U ≤ u)
    (hu : u ≤ 16 * U) {z : ℤ × ℤ} (hz : z ∈ rootPositions U V u v r) :
    1 / 16 ≤ tau r z ∧ tau r z ≤ 16 := by
  unfold rootPositions at hz
  rw [mem_filter] at hz
  obtain ⟨-, -, h1, h2, -⟩ := hz
  have hu0 : 0 < u := hU.trans_le hUu
  constructor
  · by_contra h
    push Not at h
    have : u * tau r z < u * (1 / 16) := mul_lt_mul_of_pos_left h hu0
    linarith
  · by_contra h
    push Not at h
    have : u * 16 < u * tau r z := mul_lt_mul_of_pos_left h hu0
    nlinarith

/-- Positions of the root box are primitive. -/
theorem gcd_eq_one_of_mem_rootPositions {U V u v r : ℝ} {z : ℤ × ℤ}
    (hz : z ∈ rootPositions U V u v r) : Int.gcd z.1 z.2 = 1 := by
  unfold rootPositions at hz
  exact (mem_filter.1 hz).2.1

/-- `det(z, w_z) = 1` for a primitive `z`. -/
theorem zdet_complement {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) : zdet z (complement z) = 1 := by
  have h := Int.gcd_eq_gcd_ab z.1 z.2
  rw [hz] at h
  simp only [zdet, complement]
  push_cast at h
  linarith

/-- `z'₂/τ(z') - z₂/τ(z) = det(z, z')/(τ(z) τ(z'))`. -/
theorem div_tau_sub_div_tau (r : ℝ) {z z' : ℤ × ℤ} (hz : tau r z ≠ 0) (hz' : tau r z' ≠ 0) :
    (z'.2 : ℝ) / tau r z' - z.2 / tau r z = zdet z z' / (tau r z * tau r z') := by
  rw [div_sub_div _ _ hz' hz, mul_comm (tau r z') (tau r z)]
  congr 1
  unfold zdet tau
  push_cast
  ring

/-- With `det(z₀, w) = 1`, every `v` is `det(v, w) z₀ + det(z₀, v) w`. -/
theorem eq_zdet_smul_add {z₀ w : ℤ × ℤ} (h : zdet z₀ w = 1) (v : ℤ × ℤ) :
    v = (zdet v w * z₀.1 + zdet z₀ v * w.1, zdet v w * z₀.2 + zdet z₀ v * w.2) := by
  unfold zdet at *
  ext
  · linear_combination (-v.1) * h
  · linear_combination (-v.2) * h

/-- `det` of two combinations of `z₀` and `w`. -/
theorem zdet_combo {z₀ w : ℤ × ℤ} (h : zdet z₀ w = 1) (a b a' b' : ℤ) :
    zdet (a * z₀.1 + b * w.1, a * z₀.2 + b * w.2) (a' * z₀.1 + b' * w.1, a' * z₀.2 + b' * w.2) =
      a * b' - b * a' := by
  unfold zdet at *
  linear_combination (a * b' - b * a') * h

/-! ### Line tuples -/

/-- For a prime `p` and primitive `z, z'`, `[z]_p = [z']_p` iff `p ∣ det(z, z')`. -/
theorem lineOf_eq_iff {p : ℕ} (hp : p.Prime) {z z' : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1)
    (hz' : Int.gcd z'.1 z'.2 = 1) : lineOf p z = lineOf p z' ↔ (p : ℤ) ∣ zdet z z' := by
  have hfact : Fact p.Prime := ⟨hp⟩
  -- a primitive vector is nonzero modulo `p`
  have hprim : ∀ w : ℤ × ℤ, Int.gcd w.1 w.2 = 1 → (w.1 : ZMod p) = 0 → (w.2 : ZMod p) ≠ 0 := by
    intro w hw h1 h2
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 h2
    have := Int.dvd_gcd h1 h2
    rw [hw] at this
    have hp1 := hp.one_lt
    have : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos (by exact_mod_cast this)
    omega
  have hlt : ∀ w : ℤ × ℤ, (w.1 : ZMod p) ≠ 0 → lineOf p w < p := fun w hw => by
    simp only [lineOf, hw, ↓reduceIte]
    exact ZMod.val_lt _
  have heq : ∀ w : ℤ × ℤ, (w.1 : ZMod p) = 0 → lineOf p w = p := fun w hw => by
    simp only [lineOf, hw, ↓reduceIte]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [zdet, Int.cast_sub, Int.cast_mul]
  by_cases h1 : (z.1 : ZMod p) = 0 <;> by_cases h1' : (z'.1 : ZMod p) = 0
  · rw [heq z h1, heq z' h1', h1, h1']
    simp
  · rw [heq z h1, h1]
    have := hlt z' h1'
    constructor
    · intro h
      omega
    · intro h
      have h2 := hprim z hz h1
      simp only [zero_mul, zero_sub, neg_eq_zero] at h
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h h2
      · exact absurd h h1'
  · rw [heq z' h1', h1']
    have := hlt z h1
    constructor
    · intro h
      omega
    · intro h
      have h2 := hprim z' hz' h1'
      simp only [mul_zero, sub_zero] at h
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h h1
      · exact absurd h h2
  · simp only [lineOf, h1, h1', ↓reduceIte]
    constructor
    · intro h
      have h' := ZMod.val_injective p h
      field_simp [h1, h1'] at h'
      linear_combination -h'
    · intro h
      congr 1
      field_simp [h1, h1']
      linear_combination -h

/-- For squarefree `D` and primitive `z, z'`, the line tuples agree iff `D ∣ det(z, z')`. -/
theorem lineKey_eq_iff {D : ℕ} (hD : Squarefree D) {z z' : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1)
    (hz' : Int.gcd z'.1 z'.2 = 1) : lineKey D z = lineKey D z' ↔ (D : ℤ) ∣ zdet z z' := by
  constructor
  · intro h
    -- every prime factor of `D` divides the determinant, and `D` is their product
    have hp : ∀ p ∈ D.primeFactors, p ∣ (zdet z z').natAbs := by
      intro p hpD
      have hl := congrFun h p
      simp only [lineKey, hpD, ↓reduceIte] at hl
      exact Int.ofNat_dvd_left.1 ((lineOf_eq_iff (Nat.prime_of_mem_primeFactors hpD) hz hz').1 hl)
    have := Finset.prod_primes_dvd (zdet z z').natAbs
      (fun p hpD => (Nat.prime_of_mem_primeFactors hpD).prime) hp
    rw [Nat.prod_primeFactors_of_squarefree hD] at this
    exact Int.ofNat_dvd_left.2 this
  · intro h
    funext p
    unfold lineKey
    split_ifs with hpD
    · exact (lineOf_eq_iff (Nat.prime_of_mem_primeFactors hpD) hz hz').2
        ((Int.natCast_dvd_natCast.2 (Nat.dvd_of_mem_primeFactors hpD)).trans h)
    · rfl

/-! ### The block bound -/

/-- The lattice constant `c₀ = 256 · 2561` of a block. -/
def latConst : ℝ := 655616

/-- The Plücker identity `det(z, z') = det(z, w) det(z₀, z') - det(z₀, z) det(z', w)` when
`det(z₀, w) = 1`. -/
theorem zdet_eq_of_zdet_eq_one {z₀ w : ℤ × ℤ} (h : zdet z₀ w = 1) (z z' : ℤ × ℤ) :
    zdet z z' = zdet z w * zdet z₀ z' - zdet z₀ z * zdet z' w := by
  unfold zdet at *
  linear_combination (-(z.1 * z'.2 - z.2 * z'.1)) * h

/-- A position is determined by `det(v, w)` and `det(z₀, v)` when `det(z₀, w) = 1`. -/
theorem eq_of_zdet_eq {z₀ w : ℤ × ℤ} (h : zdet z₀ w = 1) {v v' : ℤ × ℤ}
    (h₁ : zdet v w = zdet v' w) (h₂ : zdet z₀ v = zdet z₀ v') : v = v' := by
  calc v = (zdet v w * z₀.1 + zdet z₀ v * w.1, zdet v w * z₀.2 + zdet z₀ v * w.2) :=
        eq_zdet_smul_add h v
    _ = (zdet v' w * z₀.1 + zdet z₀ v' * w.1, zdet v' w * z₀.2 + zdet z₀ v' * w.2) := by
        rw [h₁, h₂]
    _ = v' := (eq_zdet_smul_add h v').symm

open scoped Classical in
/-- The positions of a lattice block around `z₀`: the line tuple of `z₀`, in the cell of `z₀` or
in the cell shifted by `δ`. -/
def blockSet (U V u v r H : ℝ) (D : ℕ) (δ : ℤ) (z₀ : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  (rootPositions U V u v r).filter fun y => lineKey D y = lineKey D z₀ ∧
    (rootCell H r y = rootCell H r z₀ ∨ rootCell H r y = rootCell H r z₀ + δ)

open scoped Classical in
/-- Membership in a lattice block. -/
theorem mem_blockSet {U V u v r H : ℝ} {D : ℕ} {δ : ℤ} {z₀ y : ℤ × ℤ} :
    y ∈ blockSet U V u v r H D δ z₀ ↔ y ∈ rootPositions U V u v r ∧ lineKey D y = lineKey D z₀ ∧
      (rootCell H r y = rootCell H r z₀ ∨ rootCell H r y = rootCell H r z₀ + δ) := by
  unfold blockSet
  exact mem_filter

/-- `|⌊a⌋ - ⌊b⌋| ≤ n` gives `|a - b| < n + 1`. -/
private theorem abs_sub_lt_of_floor {a b : ℝ} {n : ℤ} (h : |⌊a⌋ - ⌊b⌋| ≤ n) :
    |a - b| < n + 1 := by
  have h1 := Int.floor_le a
  have h2 := Int.lt_floor_add_one a
  have h3 := Int.floor_le b
  have h4 := Int.lt_floor_add_one b
  have h' : |((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ)| ≤ n := by exact_mod_cast h
  rw [abs_le] at h'
  push_cast at h'
  rw [abs_lt]
  constructor <;> linarith [h'.1, h'.2]

/-- **The coordinates of a lattice block** (PD `mem:lattice-shape`). Let `z₀` be a good source
of the root box. The positions with the line tuple of `z₀` in its cell or in the cell shifted by
`δ` embed into a box `|m₁| ≤ A'`, `|m₂| ≤ B'` with `A' B' ≤ 6 c₀² Y` and `A', B' ≤ Y^{0.9}`, and
`det(z, z') = D (m₁ m₂' - m₂ m₁')` on them. -/
theorem exists_block_embedding {Y d₀ U V u v r : ℝ} {D : ℕ} {δ : ℤ} (hδ : |δ| ≤ 2560)
    (hY : 1 ≤ Y) (hYc : 8 * latConst ≤ Y ^ (1 / 10 : ℝ)) (hd₀ : 0 < d₀) (hD : d₀ ≤ D)
    (hDsq : Squarefree D) (hU : 0 < U) (hUu : U ≤ u) (hu : u ≤ 16 * U) {z₀ : ℤ × ℤ}
    (hz₀ : z₀ ∈ rootPositions U V u v r) (hgood : GoodPad Y D (posRatio r z₀)) :
    ∃ (A' B' : ℕ) (emb : ℤ × ℤ → ℤ × ℤ), (A' : ℝ) * B' ≤ 6 * latConst ^ 2 * Y ∧
      (A' : ℝ) ≤ Y ^ (9 / 10 : ℝ) ∧ (B' : ℝ) ≤ Y ^ (9 / 10 : ℝ) ∧
      Set.InjOn emb (blockSet U V u v r (d₀ * Y) D δ z₀) ∧
      (∀ y ∈ blockSet U V u v r (d₀ * Y) D δ z₀, emb y ∈ intBox A' B') ∧
      ∀ z ∈ blockSet U V u v r (d₀ * Y) D δ z₀, ∀ z' ∈ blockSet U V u v r (d₀ * Y) D δ z₀,
        zdet z z' = D * ((emb z).1 * (emb z').2 - (emb z).2 * (emb z').1) := by
  set H := d₀ * Y with hH
  have hH0 : 0 < H := by positivity
  have hD0 : (0 : ℝ) < D := hd₀.trans_le hD
  have hD0' : (D : ℤ) ≠ 0 := by exact_mod_cast hD0.ne'
  set w₀ := complement z₀ with hw₀
  have hdet1 : zdet z₀ w₀ = 1 := zdet_complement (gcd_eq_one_of_mem_rootPositions hz₀)
  obtain ⟨hτ₀1, hτ₀2⟩ := tau_mem_of_mem_rootPositions hU hUu hu hz₀
  set τ₀ := tau r z₀ with hτ₀
  have hτ₀pos : 0 < τ₀ := by linarith
  set α := (D : ℝ) * posRatio r z₀ with hα
  -- test (i) at `α`
  have hgood' : ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (1 / 5 : ℝ) →
      Y ^ (-(7 / 10 : ℝ)) < circleDist (l * α) := fun l hl hlY => by
    rw [hα, ← mul_assoc]
    exact hgood l hl hlY
  obtain ⟨h₁, l₁, h₂, l₂, hdetL, A', B', hAB, hA, hB, hreg⟩ :=
    exists_lattice_box (c := latConst) hY (by norm_num [latConst]) hYc hgood'
  set hc : ℤ × ℤ → ℤ := fun v => zdet v w₀ with hhc
  set lc : ℤ × ℤ → ℤ := fun v => zdet z₀ v / D with hlc
  refine ⟨A', B', fun v => (hc v * l₂ - lc v * h₂, h₁ * lc v - l₁ * hc v), hAB, hA, hB, ?_⟩
  set T := blockSet U V u v r (d₀ * Y) D δ z₀ with hT
  -- facts on the block
  have hTdvd : ∀ v ∈ T, zdet z₀ v = D * lc v := by
    intro v hv
    rw [hT, mem_blockSet] at hv
    have hdv := (lineKey_eq_iff hDsq (gcd_eq_one_of_mem_rootPositions hz₀)
      (gcd_eq_one_of_mem_rootPositions hv.1)).1 hv.2.1.symm
    exact (Int.mul_ediv_cancel' hdv).symm
  have hTτ : ∀ v ∈ T, (hc v : ℝ) + lc v * α = tau r v / τ₀ := by
    intro v hv
    have hv' := eq_zdet_smul_add hdet1 v
    rw [hTdvd v hv] at hv'
    have h1 : (v.1 : ℝ) = hc v * z₀.1 + (D * lc v) * w₀.1 := by
      have := congrArg Prod.fst hv'
      exact_mod_cast this
    have h2 : (v.2 : ℝ) = hc v * z₀.2 + (D * lc v) * w₀.2 := by
      have := congrArg Prod.snd hv'
      exact_mod_cast this
    have htv : tau r v = hc v * τ₀ + D * lc v * tau r w₀ := by
      simp only [tau, hτ₀]
      rw [h1, h2]
      ring
    rw [htv, hα, posRatio, ← hτ₀, ← hw₀]
    field_simp
  have hTh : ∀ v ∈ T, |(hc v : ℝ) + lc v * α| ≤ latConst := by
    intro v hv
    rw [hTτ v hv]
    obtain ⟨hτ1, hτ2⟩ := tau_mem_of_mem_rootPositions hU hUu hu (mem_blockSet.1 hv).1
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < tau r v), abs_of_pos hτ₀pos,
      div_le_iff₀ hτ₀pos]
    unfold latConst
    nlinarith
  have hTl : ∀ v ∈ T, |(lc v : ℝ)| ≤ latConst * Y := by
    intro v hv
    have hv' := mem_blockSet.1 hv
    obtain ⟨hτ1, hτ2⟩ := tau_mem_of_mem_rootPositions hU hUu hu hv'.1
    have hτv : 0 < tau r v := by linarith
    -- the cells differ by at most `|δ|`
    have hcell : |rootCell H r v - rootCell H r z₀| ≤ (2560 : ℤ) := by
      rcases hv'.2.2 with h | h
      · rw [h, sub_self, abs_zero]
        norm_num
      · rw [h, add_sub_cancel_left]
        exact hδ
    have hab := abs_sub_lt_of_floor hcell
    rw [← sub_div, abs_div, abs_of_pos hH0, div_lt_iff₀ hH0] at hab
    rw [div_tau_sub_div_tau r hτ₀pos.ne' hτv.ne', abs_div,
      abs_of_pos (mul_pos hτ₀pos hτv), div_lt_iff₀ (mul_pos hτ₀pos hτv)] at hab
    have hz : (zdet z₀ v : ℝ) = D * lc v := by exact_mod_cast hTdvd v hv
    rw [hz, abs_mul, abs_of_pos hD0] at hab
    have hττ : τ₀ * tau r v ≤ 256 := by nlinarith
    have : (D : ℝ) * |(lc v : ℝ)| ≤ D * (latConst * Y) := by
      have h1 : (D : ℝ) * |(lc v : ℝ)| < ((2560 : ℤ) + 1) * H * 256 := by
        have : ((2560 : ℤ) + 1 : ℝ) * H * (τ₀ * tau r v) ≤ ((2560 : ℤ) + 1) * H * 256 :=
          mul_le_mul_of_nonneg_left hττ (by positivity)
        linarith
      have h2 : ((2560 : ℤ) + 1 : ℝ) * H * 256 ≤ D * (latConst * Y) := by
        rw [hH]
        unfold latConst
        push_cast
        nlinarith
      linarith
    exact le_of_mul_le_mul_left this hD0
  refine ⟨fun v hv v' hv' he => ?_, fun v hv => ?_, fun z hz z' hz' => ?_⟩
  · -- the coordinates determine the position
    simp only [Prod.mk.injEq] at he
    have e1 : hc v = hc v' := by
      have : hc v = (hc v * l₂ - lc v * h₂) * h₁ + (h₁ * lc v - l₁ * hc v) * h₂ := by
        linear_combination (-(hc v)) * hdetL
      have h' : hc v' = (hc v' * l₂ - lc v' * h₂) * h₁ + (h₁ * lc v' - l₁ * hc v') * h₂ := by
        linear_combination (-(hc v')) * hdetL
      rw [this, h', he.1, he.2]
    have e2 : lc v = lc v' := by
      have : lc v = (hc v * l₂ - lc v * h₂) * l₁ + (h₁ * lc v - l₁ * hc v) * l₂ := by
        linear_combination (-(lc v)) * hdetL
      have h' : lc v' = (hc v' * l₂ - lc v' * h₂) * l₁ + (h₁ * lc v' - l₁ * hc v') * l₂ := by
        linear_combination (-(lc v')) * hdetL
      rw [this, h', he.1, he.2]
    refine eq_of_zdet_eq hdet1 e1 ?_
    rw [hTdvd v hv, hTdvd v' hv', e2]
  · -- the coordinates lie in the box
    obtain ⟨h1, h2⟩ := hreg (hc v) (lc v) (hTl v hv) (hTh v hv)
    exact mem_product.2 ⟨mem_Icc.2 (abs_le.1 h1), mem_Icc.2 (abs_le.1 h2)⟩
  · -- `det(z, z')/D` is the determinant of the coordinates
    rw [zdet_eq_of_zdet_eq_one hdet1 z z', hTdvd z hz, hTdvd z' hz']
    simp only [hhc]
    linear_combination (-(D : ℤ) * (zdet z w₀ * lc z' - lc z * zdet z' w₀)) * hdetL

open scoped Classical in
/-- **The lattice blocks** (PD `mem:lattice-shape` and the tensor step): for `|δ| ≤ 2560`, the
kernel `[z good] [D ∣ det(z, z')] [cell z' = cell z + δ] e(ϑ det(z, z')/D)` on the root box has
norm at most `n`, whenever the determinant matrix `e(ϑ (m₁ m₂' - m₂ m₁'))` has norm at most `n`
on every box with sides `A' B' ≤ 6 c₀² Y` and `A', B' ≤ Y^{0.9}`. -/
theorem kerLe_shiftKernel_of_box {Y d₀ U V u v r ϑ n : ℝ} {D : ℕ} {δ : ℤ} (hδ : |δ| ≤ 2560)
    (hY : 1 ≤ Y) (hYc : 8 * latConst ≤ Y ^ (1 / 10 : ℝ)) (hd₀ : 0 < d₀) (hD : d₀ ≤ D)
    (hDsq : Squarefree D) (hU : 0 < U) (hUu : U ≤ u) (hu : u ≤ 16 * U) (hn : 0 ≤ n)
    (hbox : ∀ A' B' : ℕ, (A' : ℝ) * B' ≤ 6 * latConst ^ 2 * Y → (A' : ℝ) ≤ Y ^ (9 / 10 : ℝ) →
      (B' : ℝ) ≤ Y ^ (9 / 10 : ℝ) →
      KerLe (intBox A' B') (intBox A' B') (fun m m' => ephase (ϑ * (m.1 * m'.2 - m.2 * m'.1))) n) :
    KerLe (rootPositions U V u v r) (rootPositions U V u v r)
      (fun z z' => if GoodPad Y D (posRatio r z) ∧ (D : ℤ) ∣ zdet z z' ∧
          rootCell (d₀ * Y) r z' = rootCell (d₀ * Y) r z + δ then
        ephase (ϑ * (zdet z z' / D : ℤ)) else 0) n := by
  set H := d₀ * Y with hH
  have hD0 : (0 : ℝ) < D := hd₀.trans_le hD
  have hD0' : (D : ℤ) ≠ 0 := by exact_mod_cast hD0.ne'
  refine KerLe.block (fun z => (lineKey D z, rootCell H r z))
    (fun z' => (lineKey D z', rootCell H r z' - δ)) ?_ ?_
  · -- the kernel joins equal line tuples, and cells shifted by `δ`
    intro z hz z' hz' hne
    have hc : GoodPad Y D (posRatio r z) ∧ (D : ℤ) ∣ zdet z z' ∧
        rootCell H r z' = rootCell H r z + δ := by
      by_contra h
      exact hne (ite_eq_right_iff.2 fun h' => (h h').elim)
    simp only [Prod.mk.injEq]
    exact ⟨(lineKey_eq_iff hDsq (gcd_eq_one_of_mem_rootPositions hz)
      (gcd_eq_one_of_mem_rootPositions hz')).2 hc.2.1, by rw [hc.2.2]; ring⟩
  · rintro ⟨kk, c⟩
    by_cases hex : ∃ z₀ ∈ (rootPositions U V u v r).filter
        (fun z => (lineKey D z, rootCell H r z) = (kk, c)), GoodPad Y D (posRatio r z₀)
    · obtain ⟨z₀, hz₀, hg₀⟩ := hex
      rw [mem_filter, Prod.mk.injEq] at hz₀
      obtain ⟨A', B', emb, hAB, hA, hB, hinj, hmap, hdet⟩ :=
        exists_block_embedding hδ hY hYc hd₀ hD hDsq hU hUu hu hz₀.1 hg₀
      -- the source and target sets lie in the block of `z₀`
      have hsrc : (rootPositions U V u v r).filter
          (fun z => (lineKey D z, rootCell H r z) = (kk, c)) ⊆
          blockSet U V u v r (d₀ * Y) D δ z₀ := by
        intro z hz
        rw [mem_filter, Prod.mk.injEq] at hz
        exact mem_blockSet.2 ⟨hz.1, hz.2.1.trans hz₀.2.1.symm, Or.inl (hz.2.2.trans hz₀.2.2.symm)⟩
      have htgt : (rootPositions U V u v r).filter
          (fun z' => (lineKey D z', rootCell H r z' - δ) = (kk, c)) ⊆
          blockSet U V u v r (d₀ * Y) D δ z₀ := by
        intro z' hz'
        rw [mem_filter, Prod.mk.injEq] at hz'
        refine mem_blockSet.2 ⟨hz'.1, hz'.2.1.trans hz₀.2.1.symm, Or.inr ?_⟩
        have := hz'.2.2
        rw [hz₀.2.2]
        linarith
      have hE := (hbox A' B' hAB hA hB).comp_embed (hinj.mono hsrc) (hinj.mono htgt)
        (fun z hz => hmap z (hsrc hz)) (fun z hz => hmap z (htgt hz))
      have hE' := hE.mul_diag (φ := fun z => if GoodPad Y D (posRatio r z) then (1 : ℂ) else 0)
        (φ' := fun _ => (1 : ℂ)) (fun z _ => by split_ifs <;> simp) (fun _ _ => by simp)
      refine hE'.congr fun z hz z' hz' => ?_
      have hzb := hsrc hz
      have hzb' := htgt hz'
      rw [mem_filter, Prod.mk.injEq] at hz hz'
      have hdvd : (D : ℤ) ∣ zdet z z' :=
        (lineKey_eq_iff hDsq (gcd_eq_one_of_mem_rootPositions hz.1)
          (gcd_eq_one_of_mem_rootPositions hz'.1)).1 (hz.2.1.trans hz'.2.1.symm)
      have hcell : rootCell H r z' = rootCell H r z + δ := by
        have := hz'.2.2
        rw [hz.2.2]
        linarith
      have hq : zdet z z' / D = (emb z).1 * (emb z').2 - (emb z).2 * (emb z').1 := by
        rw [hdet z hzb z' hzb']
        exact Int.mul_ediv_cancel_left _ hD0'
      simp only [hdvd, hcell, and_true, mul_one]
      split_ifs with hg
      · rw [one_mul, hq]
        push_cast
        ring_nf
      · rw [zero_mul]
    · -- no good source: the block kernel vanishes
      push Not at hex
      refine ((kerLe_zero _ _).mono le_rfl hn).congr fun z hz z' _ => ?_
      exact (ite_eq_right_iff.2 fun h => (hex z hz h.1).elim).symm

end Erdos408.OneSided
