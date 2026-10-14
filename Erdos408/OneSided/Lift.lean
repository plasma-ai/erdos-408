import Erdos408.OneSided.Setup
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# The lift

The physical states and operators of PD §3.2 (`blueprint/one_sided_type_ii.md` §4), at a
fixed label dyad `Y` and pad dyad `d₀`.

* A state is a primitive position `P ∈ Ω = [U, 16U] × [V, 2V]`, with `U = d₀ Y H_m` and
  `V = H_n`, together with ordered lists of `M = J + 1` distinct primes of each band, all
  dividing `P₁`. The state measure `∏_i V_i^{-M}` is constant, so adjoints are conjugate
  transposes.
* `rowOp` is the row operation `𝒯`: it copies the pads (slots `0, …, J - 1`), replaces
  the last slot of each group by a new label distinct from every source label (the
  cross-edge ban), and has the multiplier `𝒦` of PD `eq:det-kernel`. `symOp` averages over the
  orders of the lists, `goodOp` projects onto good states, and
  `edgeOp = 𝒢 𝒮 𝒯 𝒮 𝒢` is the operator `𝒜`.
* `endVec` is the endpoint vector `f = ᾱ_m β_{P₂}` with `m = P₁ / (list product)`; the
  vector `g` of PD `det:endpoints` equals `f`. `rowPairing` and `pairing` are `⟨f, 𝒯 f⟩` and
  `⟨f, 𝒜 f⟩`, and `detMoment` is `∑_P ⟨u_P, (𝒜𝒜^*)^R u_P⟩`.

The damping exponent `q` of the lift is a free parameter: it equals one at the endpoints,
so it affects only the moment.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real
open scoped Matrix

variable {K : ℕ}

/-- `J = ⌊L^{0.01}⌋`, the number of pads in each group. -/
def padCount (x : ℝ) : ℕ := ⌊Real.log x ^ (1 / 100 : ℝ)⌋₊

/-- `R = ⌈L^{1/2} / 2⌉`; the moment has `N = 2R` edges. -/
def momentPower (x : ℝ) : ℕ := ⌈Real.log x ^ (1 / 2 : ℝ) / 2⌉₊

/-- Ordered lists of `J + 1` labels in each of the `K` groups. -/
abbrev Lists (K J : ℕ) := Fin K → Fin (J + 1) → ℕ

/-- The primitive positions in `Ω = [U, 16U] × [V, 2V]`, with `U = d₀ Y H_m`, `V = H_n`. -/
def positions (d : Data K) (Y d₀ : ℝ) : Finset (ℕ × ℕ) :=
  ((Icc ⌈d₀ * Y * d.Hm⌉₊ ⌊16 * (d₀ * Y * d.Hm)⌋₊) ×ˢ (Icc ⌈d.Hn⌉₊ ⌊2 * d.Hn⌋₊)).filter
    fun P => Nat.Coprime P.1 P.2

open scoped Classical in
/-- The ordered lists of `J + 1` distinct primes of each band. -/
def lists (x : ℝ) (d : Data K) (J : ℕ) : Finset (Lists K J) :=
  (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin (J + 1) => band x (d.a i)).filter
    fun p => ∀ i, Function.Injective (p i)

/-- The physical states: a position and lists whose labels all divide `P₁`. -/
def states (x : ℝ) (d : Data K) (Y d₀ : ℝ) : Finset ((ℕ × ℕ) × Lists K (padCount x)) :=
  (positions d Y d₀ ×ˢ lists x d (padCount x)).filter fun s => ∀ i h, s.2 i h ∣ s.1.1

/-- The physical state space. -/
abbrev State (x : ℝ) (d : Data K) (Y d₀ : ℝ) := ↥(states x d Y d₀)

/-! ### Products of labels -/

/-- The product of all labels. -/
def listProd {J : ℕ} (p : Lists K J) : ℕ := ∏ i, ∏ h, p i h

/-- The pad product `D`: the labels in slots `0, …, J - 1`. -/
def padProd {J : ℕ} (p : Lists K J) : ℕ := ∏ i, ∏ h : Fin J, p i h.castSucc

/-- The product of the last slots. -/
def lastProd {J : ℕ} (p : Lists K J) : ℕ := ∏ i, p i (Fin.last J)

/-- The product of the labels after omitting slot `o i` in each group `i`. -/
def omitProd {J : ℕ} (p : Lists K J) (o : Fin K → Fin (J + 1)) : ℕ :=
  ∏ i, ∏ h ∈ univ.erase (o i), p i h

/-! ### Good states -/

/-- `r_P = c / P₁ mod 1` for the completion `P₁ d - P₂ c = 1`, so `c ≡ -P₂⁻¹ (mod P₁)`. -/
def rootRatio (P : ℕ × ℕ) : ℝ := ((-(P.2 : ZMod P.1)⁻¹ : ZMod P.1).val : ℝ) / P.1

/-- The distance `‖t‖` from `t` to the nearest integer. -/
def circleDist (t : ℝ) : ℝ := |t - round t|

/-- Test (i) of PD §3.2 at the ratio `r`: for every omission product `D ∈ [d₀, 2d₀)` and
`1 ≤ l ≤ Y^{0.2}`, `‖l D r‖ > Y^{-0.7}`. -/
def GoodFirst (Y d₀ : ℝ) {J : ℕ} (r : ℝ) (p : Lists K J) : Prop :=
  ∀ o : Fin K → Fin (J + 1), d₀ ≤ (omitProd p o : ℝ) → (omitProd p o : ℝ) < 2 * d₀ →
    ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (1 / 5 : ℝ) →
      Y ^ (-(7 / 10 : ℝ)) < circleDist (l * omitProd p o * r)

/-- The fresh draws outside `I`: a prime of `𝒫_i` for `i ∉ I`, and `1` for `i ∈ I`. -/
def freshDraws (x : ℝ) (d : Data K) (I : Finset (Fin K)) : Finset (Fin K → ℕ) :=
  Fintype.piFinset fun i => if i ∈ I then {1} else band x (d.a i)

/-- The probability `∏_{i ∉ I} μ_i(T_i)` of a fresh draw, `μ_i(p) = 1 / (p V_i)`. -/
def freshWeight (x : ℝ) (d : Data K) (I : Finset (Fin K)) (T : Fin K → ℕ) : ℝ :=
  ∏ i ∈ univ.filter (· ∉ I), 1 / ((T i : ℝ) * harmonicMass (band x (d.a i)))

/-- The selections `Z`: a prime of `𝒫_j` for `j ∈ I \ {i}`, and `1` otherwise. -/
def selections (x : ℝ) (d : Data K) (I : Finset (Fin K)) (i : Fin K) : Finset (Fin K → ℕ) :=
  Fintype.piFinset fun j => if j ∈ I.erase i then band x (d.a j) else {1}

/-- For the fresh draw `T`, the points `D Z T r` belonging to distinct integers `D Z` are
pairwise at circle distance at least `100 e^{-L^{a_i}}`. Here `D` ranges over the omission
products in `[d₀, 2d₀)`. -/
def Separated (x : ℝ) (d : Data K) (d₀ : ℝ) (I : Finset (Fin K)) (i : Fin K) {J : ℕ}
    (r : ℝ) (p : Lists K J) (T : Fin K → ℕ) : Prop :=
  ∀ o o' : Fin K → Fin (J + 1), ∀ Z ∈ selections x d I i, ∀ Z' ∈ selections x d I i,
    d₀ ≤ (omitProd p o : ℝ) → (omitProd p o : ℝ) < 2 * d₀ →
    d₀ ≤ (omitProd p o' : ℝ) → (omitProd p o' : ℝ) < 2 * d₀ →
    omitProd p o * ∏ j, Z j ≠ omitProd p o' * ∏ j, Z' j →
    100 * Real.exp (-Real.log x ^ d.a i) ≤
      circleDist (((omitProd p o * ∏ j, Z j : ℕ) - (omitProd p o' * ∏ j, Z' j : ℕ) : ℝ) *
        (∏ j, T j : ℕ) * r)

open scoped Classical in
/-- Test (ii) of PD §3.2 at the ratio `r`: for every nonempty set `I` of groups, with
`i_* = max I`, the fresh draws outside `I` failing `Separated` have probability at most
`exp(-L^{a_{i_*}} / 4)`. -/
def GoodSecond (x : ℝ) (d : Data K) (d₀ : ℝ) {J : ℕ} (r : ℝ) (p : Lists K J) : Prop :=
  ∀ I : Finset (Fin K), ∀ hI : I.Nonempty,
    ∑ T ∈ (freshDraws x d I).filter (fun T => ¬ Separated x d d₀ I (I.max' hI) r p T),
        freshWeight x d I T ≤
      Real.exp (-Real.log x ^ d.a (I.max' hI) / 4)

/-- A state is good when both tests pass at its ratio `r_P`. -/
def IsGood (x : ℝ) (d : Data K) (Y d₀ : ℝ) {J : ℕ} (P : ℕ × ℕ) (p : Lists K J) : Prop :=
  GoodFirst Y d₀ (rootRatio P) p ∧ GoodSecond x d d₀ (rootRatio P) p

/-! ### Operators -/

/-- `det(P, Q) = P₁ Q₂ - P₂ Q₁`. -/
def det (P Q : ℕ × ℕ) : ℤ := P.1 * Q.2 - P.2 * Q.1

open scoped Classical in
/-- The row operation `𝒯` of PD §3.2. From the source `(P, p)` to the target `(Q, p')`: the
pads are copied, each new last label differs from every source label, the pad product
`D` lies in `[d₀, 2d₀)` and divides `det(P, Q)`, and the multiplier is
`∏ V_i^{-1}` (the new labels) times
`(d₀/D) η(b/Y) η(a/Y) ψ(t/Y) {[t = b - a] - ∫_𝔐 e(θ(t - b + a)) dθ}` times the damping
`q^{(ω(P₁) - KM)/2 + (ω(Q₁) - KM)/2}`, with `t = det(P, Q) / D`, `b` and `a` the
products of the source's and target's last slots. -/
def rowOp (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) :
    Matrix (State x d Y d₀) (State x d Y d₀) ℂ := fun s s' =>
  if (∀ i (h : Fin (padCount x)), s'.1.2 i h.castSucc = s.1.2 i h.castSucc) ∧
      (∀ i i' h', s'.1.2 i (Fin.last _) ≠ s.1.2 i' h') ∧
      d₀ ≤ (padProd s.1.2 : ℝ) ∧ (padProd s.1.2 : ℝ) < 2 * d₀ ∧
      (padProd s.1.2 : ℤ) ∣ det s.1.1 s'.1.1 then
    (((d.bandMass x)⁻¹ * (d₀ / padProd s.1.2) * dyadicBump (lastProd s.1.2 / Y) *
        dyadicBump (lastProd s'.1.2 / Y) * plateau ((det s.1.1 s'.1.1 / padProd s.1.2 : ℤ) / Y) *
        q ^ (((bandCount x d s.1.1.1 : ℝ) - K * (padCount x + 1)) / 2 +
          ((bandCount x d s'.1.1.1 : ℝ) - K * (padCount x + 1)) / 2) : ℝ) : ℂ) *
      ((if det s.1.1 s'.1.1 / padProd s.1.2 = (lastProd s.1.2 : ℤ) - lastProd s'.1.2 then 1
          else 0) -
        arcIntegral A₀ x Y
          (det s.1.1 s'.1.1 / padProd s.1.2 - lastProd s.1.2 + lastProd s'.1.2))
  else 0

open scoped Classical in
/-- The slot symmetrization `𝒮`: the average over the orders of the lists. -/
def symOp (x : ℝ) (d : Data K) (Y d₀ : ℝ) : Matrix (State x d Y d₀) (State x d Y d₀) ℂ :=
  fun s s' =>
    if s.1.1 = s'.1.1 ∧
        ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)), ∀ i, s'.1.2 i = s.1.2 i ∘ σ i then
      (((padCount x + 1).factorial ^ K : ℕ) : ℂ)⁻¹
    else 0

open scoped Classical in
/-- The projection `𝒢` onto good states. -/
def goodOp (x : ℝ) (d : Data K) (Y d₀ : ℝ) : Matrix (State x d Y d₀) (State x d Y d₀) ℂ :=
  Matrix.diagonal fun s => if IsGood x d Y d₀ s.1.1 s.1.2 then 1 else 0

/-- The restricted, symmetrized operator `𝒜 = 𝒢 𝒮 𝒯 𝒮 𝒢`. -/
def edgeOp (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) :
    Matrix (State x d Y d₀) (State x d Y d₀) ℂ :=
  goodOp x d Y d₀ * symOp x d Y d₀ * rowOp q A₀ x d Y d₀ * symOp x d Y d₀ * goodOp x d Y d₀

/-! ### Pairings and the moment -/

/-- The state measure `∏_i V_i^{-M}`. -/
def stateMass (x : ℝ) (d : Data K) : ℝ := (d.bandMass x)⁻¹ ^ (padCount x + 1)

/-- The inner product `⟨u, v⟩ = ∏_i V_i^{-M} ∑_s ū(s) v(s)`. -/
def stateInner {x : ℝ} {d : Data K} {Y d₀ : ℝ} (u v : State x d Y d₀ → ℂ) : ℂ :=
  (stateMass x d : ℂ) * ∑ s, star (u s) * v s

/-- The endpoint vector `f(P, p) = ᾱ_m β_{P₂}`, `m = P₁ / (list product)`. It vanishes
unless `m` is rough, so the band part of `P₁` is exactly the list product. -/
def endVec (x : ℝ) (d : Data K) (Y d₀ : ℝ) (s : State x d Y d₀) : ℂ :=
  star (d.α (s.1.1.1 / listProd s.1.2)) * d.β s.1.1.2

/-- `⟨f, 𝒯 f⟩`. -/
def rowPairing (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) : ℂ :=
  stateInner (endVec x d Y d₀) (rowOp q A₀ x d Y d₀ *ᵥ endVec x d Y d₀)

/-- `⟨f, 𝒜 f⟩`. -/
def pairing (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) : ℂ :=
  stateInner (endVec x d Y d₀) (edgeOp q A₀ x d Y d₀ *ᵥ endVec x d Y d₀)

open scoped Classical in
/-- The determinant moment `∑_P ⟨u_P, (𝒜𝒜^*)^R u_P⟩`, where `u_P` is one on every state at
the position `P`. -/
def detMoment (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) : ℂ :=
  (stateMass x d : ℂ) * ∑ s, ∑ s',
    if s.1.1 = s'.1.1 then
      ((edgeOp q A₀ x d Y d₀ * (edgeOp q A₀ x d Y d₀)ᴴ) ^ momentPower x) s s'
    else 0

end Erdos408.OneSided
