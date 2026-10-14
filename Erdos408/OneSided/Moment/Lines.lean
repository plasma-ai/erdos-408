import Erdos408.OneSided.Model

/-!
# Independent lines

The average over independent uniform lines at the band primes, and the root moment at a
real root (`blueprint/one_sided_type_ii.md` §11). A line assignment gives each band prime `p`
a line `ℓ p ∈ {0, …, p}`, encoding the projective line `ℙ¹(𝔽_p)`.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

/-- The band primes: the union of the bands. -/
def bandPrimes (x : ℝ) (d : Data K) : Finset ℕ := univ.biUnion fun i => band x (d.a i)

open scoped Classical in
/-- The line assignments: a line `ℓ p ∈ {0, …, p}` for each band prime, and `0` elsewhere. -/
def lineAssignments (x : ℝ) (d : Data K) : Finset (ℕ → ℕ) :=
  ((bandPrimes x d).pi fun p => range (p + 1)).image fun f p =>
    if h : p ∈ bandPrimes x d then f p h else 0

/-- The average over independent uniform lines at the band primes. -/
def lineAverage (x : ℝ) (d : Data K) (F : (ℕ → ℕ) → ℂ) : ℂ :=
  ((lineAssignments x d).card : ℂ)⁻¹ * ∑ ℓ ∈ lineAssignments x d, F ℓ

/-- The root moment `⟨u_{e₁}, (𝒜𝒜^*)^R u_{e₁}⟩` of the model at the real root
`ϱ = (u, v, r)` with lines `ℓ`. It is `0` if `e₁` is not a position there. -/
def rootMoment (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (ℓ : ℕ → ℕ) : ℂ :=
  if h : ((1 : ℤ), (0 : ℤ)) ∈ rootPositions (d₀ * Y * d.Hm) d.Hn u v r then
    (rootModel d Y d₀ u v r ℓ).moment q A₀ x d Y d₀ ⟨(1, 0), h⟩
  else 0

end Erdos408.OneSided
