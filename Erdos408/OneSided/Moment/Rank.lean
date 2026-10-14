module

public import Erdos408.OneSided.Moment.Phased
public import Erdos408.OneSided.Moment.Rank.Budget
public import Erdos408.OneSided.Moment.Rank.Phase
public import Erdos408.OneSided.Bands

/-!
# The rank expansion of the memory bound

The ingredients of M10 (`blueprint/one_sided_type_ii.md` §13, PD §4.8, "Restoring global
birth distinctness") that `eventually_norm_distinctSum_le` assembles.

* `distinctSum_eq_sum_blockSum`: by the partition identity, the distinct-birth history sum
  is `∑_𝒞 c(𝒞) blockSum(𝒞)`, where `blockSum(𝒞)` is the history sum constrained by the
  block system `𝒞`.
* `norm_sum_blockCoef_mul_le`: the coefficient mass at rank `r` is at most `Q^{2r}`, so a
  bound on `blockSum` depending on the rank alone sums to `∑_r Q^{2r} f(r)`.
* `norm_blockSum_le_realized` (high rank): `blockSum(𝒞)` is at most the absolute constrained
  sum of `exists_realized_history_le`.
* `norm_blockSum_le` (low rank): the local phases of `exists_blockPhase` write
  `blockSum(𝒞)` as an average of matrix elements `⟨𝐛^ψ_init, 𝒢^ψ₀ ℰ^ψ ⋯ 𝒢^ψ_N 𝐛⟩`, each at most
  `‖𝒢^ψ₀ ℰ^ψ ⋯ 𝒢^ψ_N‖ ‖𝐛‖²` by Cauchy–Schwarz (`norm_sum_mul_le_of_normLe`).
* `normLe_phasedProduct`: the phased product has norm at most
  `C₀^{N+1} L^{-GN + (C_e + G)|U|}`, where `U` holds the addresses with a nontrivial phase.
  An edge without such an address is the plain edge, of norm `L^{-G}`; the others have the
  crude norm `L^{C_e}`.
* `wnormSq_chainInit_le`: `‖𝐛‖² ≤ 2^{KM}`, since `∑_{p ∈ 𝒫_i} ν(p) ≤ 2` once `b'_p ≥ 1/2`.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

/-! ### Operator norms -/

section Norms

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The weighted square norm is nonnegative. -/
theorem wnormSq_nonneg {μ : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i) (f : ι → ℂ) : 0 ≤ wnormSq μ f :=
  sum_nonneg fun i _ => mul_nonneg (hμ i) (sq_nonneg _)

/-- A norm bound depends only on the modulus of the constant. -/
theorem NormLe.abs {μ : ι → ℝ} {ν : κ → ℝ} {T : (κ → ℂ) → ι → ℂ} {c : ℝ}
    (hT : NormLe μ ν T c) : NormLe μ ν T |c| := fun f => by
  rw [sq_abs]
  exact hT f

/-- A product `T_{b₁} ⋯ T_{b_m} S` of operators bounded on `ℓ²(μ)` is bounded by the product
of their bounds. -/
theorem normLe_foldr {β : Type*} {μ : ι → ℝ} (T : β → (ι → ℂ) → ι → ℂ) (c : β → ℝ)
    {S : (ι → ℂ) → ι → ℂ} {c₀ : ℝ} (hS : NormLe μ μ S c₀) :
    ∀ l : List β, (∀ b ∈ l, NormLe μ μ (T b) (c b)) →
      NormLe μ μ (fun f => l.foldr T (S f)) ((l.map c).prod * c₀)
  | [], _ => by simpa using hS
  | b :: l, hl => by
    rw [List.map_cons, List.prod_cons, mul_assoc]
    exact (hl b List.mem_cons_self).comp
      (normLe_foldr T c hS l fun b' hb' => hl b' (List.mem_cons_of_mem b hb'))

/-- Cauchy–Schwarz for a matrix element: if `T` has norm at most `c` on `ℓ²(μ)` and
`|g| ≤ |f|`, then `|∑_i μ(i) g(i) (T f)(i)| ≤ c ‖f‖²_μ`. -/
theorem norm_sum_mul_le_of_normLe {μ : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i)
    {T : (ι → ℂ) → ι → ℂ} {c : ℝ} (hc : 0 ≤ c) (hT : NormLe μ μ T c) {f g : ι → ℂ}
    (hg : ∀ i, ‖g i‖ ≤ ‖f i‖) :
    ‖∑ i, (μ i : ℂ) * g i * T f i‖ ≤ c * wnormSq μ f := by
  have hW := wnormSq_nonneg hμ f
  have hX : 0 ≤ ∑ i, μ i * ‖f i‖ * ‖T f i‖ :=
    sum_nonneg fun i _ => mul_nonneg (mul_nonneg (hμ i) (norm_nonneg _)) (norm_nonneg _)
  -- `(∑ μ |f| |T f|)² ≤ ‖f‖²_μ ‖T f‖²_μ ≤ (c ‖f‖²_μ)²`
  have hsq : (∑ i, μ i * ‖f i‖ * ‖T f i‖) ^ 2 ≤ (c * wnormSq μ f) ^ 2 :=
    calc (∑ i, μ i * ‖f i‖ * ‖T f i‖) ^ 2 ≤ wnormSq μ f * wnormSq μ (T f) :=
          sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => mul_nonneg (hμ i) (sq_nonneg _))
            (fun i _ => mul_nonneg (hμ i) (sq_nonneg _)) fun i _ => le_of_eq (by ring)
      _ ≤ wnormSq μ f * (c ^ 2 * wnormSq μ f) := mul_le_mul_of_nonneg_left (hT f) hW
      _ = (c * wnormSq μ f) ^ 2 := by ring
  calc ‖∑ i, (μ i : ℂ) * g i * T f i‖ ≤ ∑ i, μ i * ‖f i‖ * ‖T f i‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ i)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hg i) (hμ i))
          (norm_nonneg _)
    _ ≤ c * wnormSq μ f := (sq_le_sq₀ hX (mul_nonneg hc hW)).1 hsq

end Norms

/-! ### The rank coefficients -/

/-- **Summing over ranks**: if `|z(𝒞)| ≤ f(r(𝒞))` on a set `S` of block systems whose ranks
lie in `R`, then `|∑_{𝒞 ∈ S} c(𝒞) z(𝒞)| ≤ ∑_{r ∈ R} Q^{2r} f(r)`, by the rank coefficients. -/
theorem norm_sum_blockCoef_mul_le {α : Type*} [Fintype α] [DecidableEq α]
    {S : Finset (Finset (Finset α))} (hS : S ⊆ blockSystems α) {R : Finset ℕ}
    (hR : ∀ 𝒞 ∈ S, blockRank 𝒞 ∈ R) (z : Finset (Finset α) → ℂ) {f : ℕ → ℝ}
    (hf : ∀ r ∈ R, 0 ≤ f r) (hz : ∀ 𝒞 ∈ S, ‖z 𝒞‖ ≤ f (blockRank 𝒞)) :
    ‖∑ 𝒞 ∈ S, (blockCoef 𝒞 : ℂ) * z 𝒞‖ ≤ ∑ r ∈ R, (Fintype.card α : ℝ) ^ (2 * r) * f r := by
  -- the coefficient mass of `S` at rank `r` is at most `Q^{2r}`
  have hcoef : ∀ r, ∑ 𝒞 ∈ S with blockRank 𝒞 = r, |(blockCoef 𝒞 : ℝ)| ≤
      (Fintype.card α : ℝ) ^ (2 * r) := fun r =>
    calc ∑ 𝒞 ∈ S with blockRank 𝒞 = r, |(blockCoef 𝒞 : ℝ)| ≤
          ∑ 𝒞 ∈ blockSystems α with blockRank 𝒞 = r, |(blockCoef 𝒞 : ℝ)| :=
          sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hS) fun _ _ _ => abs_nonneg _
      _ ≤ (Fintype.card α : ℝ) ^ (2 * r) := by exact_mod_cast sum_abs_blockCoef_le (α := α) r
  calc ‖∑ 𝒞 ∈ S, (blockCoef 𝒞 : ℂ) * z 𝒞‖ ≤ ∑ 𝒞 ∈ S, |(blockCoef 𝒞 : ℝ)| * f (blockRank 𝒞) :=
        (norm_sum_le _ _).trans (sum_le_sum fun 𝒞 h𝒞 => by
          rw [norm_mul, Complex.norm_intCast]
          exact mul_le_mul_of_nonneg_left (hz 𝒞 h𝒞) (abs_nonneg _))
    _ = ∑ r ∈ R, (∑ 𝒞 ∈ S with blockRank 𝒞 = r, |(blockCoef 𝒞 : ℝ)|) * f r := by
        rw [← sum_fiberwise_of_maps_to hR]
        refine sum_congr rfl fun r _ => ?_
        rw [sum_mul]
        exact sum_congr rfl fun 𝒞 h𝒞 => by rw [(mem_filter.1 h𝒞).2]
    _ ≤ ∑ r ∈ R, (Fintype.card α : ℝ) ^ (2 * r) * f r :=
        sum_le_sum fun r hr => mul_le_mul_of_nonneg_right (hcoef r) (hf r hr)

/-! ### The block sums -/

section Chain

variable (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

/-- With trivial phases, the phased edge is the edge. -/
theorem phasedEdge_one (N : ℕ) :
    phasedEdge q A₀ x d Y d₀ u v r B N (fun _ _ => 1) = chainEdge q A₀ x d Y d₀ u v r B N := by
  unfold phasedEdge chainEdge
  congr 1
  funext s c
  simp [phasedEdgeCoef]

open scoped Classical in
/-- The history sum constrained by the block system `𝒞`:
`∑_s μ(s) 𝐛(s) ∑_h w(s, h) ∏_{C ∈ 𝒞} [C realized] 𝐛(end(s, h))`. -/
def blockSum (N : ℕ) (𝒞 : Finset (Finset (BirthAddr (K := K) x B N))) : ℂ :=
  ∑ s, (chainMeasure q x d Y d₀ u v r B N s : ℂ) * chainInit x d Y d₀ u v r B s *
    ∑ h ∈ histories x d Y d₀ u v r B N, chainWeight q A₀ s h *
      (∏ C ∈ 𝒞, if BlockRealized (births s h) C then 1 else 0) *
        chainInit x d Y d₀ u v r B (chainEnd s h)

open scoped Classical in
/-- **The rank expansion**: by the partition identity, the distinct-birth history sum is
`∑_𝒞 c(𝒞) blockSum(𝒞)`. -/
theorem distinctSum_eq_sum_blockSum (N : ℕ) :
    distinctSum q A₀ x d Y d₀ u v r B N =
      ∑ 𝒞 ∈ blockSystems (BirthAddr (K := K) x B N),
        (blockCoef 𝒞 : ℂ) * blockSum q A₀ x d Y d₀ u v r B N 𝒞 := by
  -- the partition identity, in `ℂ`
  have hpart : ∀ s : ChainState x d Y d₀ u v r B, ∀ h : History x d Y d₀ u v r N,
      (if BirthsDistinct (births s h) then (1 : ℂ) else 0) =
        ∑ 𝒞 ∈ blockSystems (BirthAddr (K := K) x B N), (blockCoef 𝒞 : ℂ) *
          ∏ C ∈ 𝒞, if BlockRealized (births s h) C then 1 else 0 := by
    intro s h
    have := congrArg (Int.cast : ℤ → ℂ) (birthsDistinct_indicator_eq (births s h))
    push_cast at this
    exact this
  calc distinctSum q A₀ x d Y d₀ u v r B N
      = ∑ s, ∑ h ∈ histories x d Y d₀ u v r B N, ∑ 𝒞 ∈ blockSystems (BirthAddr (K := K) x B N),
          (chainMeasure q x d Y d₀ u v r B N s : ℂ) * chainInit x d Y d₀ u v r B s *
            ((blockCoef 𝒞 : ℂ) * (chainWeight q A₀ s h *
              (∏ C ∈ 𝒞, if BlockRealized (births s h) C then 1 else 0) *
                chainInit x d Y d₀ u v r B (chainEnd s h))) := by
        unfold distinctSum
        refine sum_congr rfl fun s _ => ?_
        rw [sum_filter, mul_sum]
        refine sum_congr rfl fun h _ => ?_
        rw [← mul_sum, ← boole_mul, hpart s h, sum_mul]
        congr 1
        exact sum_congr rfl fun 𝒞 _ => by ring
    _ = ∑ 𝒞 ∈ blockSystems (BirthAddr (K := K) x B N),
          (blockCoef 𝒞 : ℂ) * blockSum q A₀ x d Y d₀ u v r B N 𝒞 := by
        rw [funext fun s => sum_comm (s := histories x d Y d₀ u v r B N)
          (t := blockSystems (BirthAddr (K := K) x B N)), sum_comm]
        refine sum_congr rfl fun 𝒞 _ => ?_
        rw [blockSum, mul_sum]
        refine sum_congr rfl fun s _ => ?_
        rw [mul_sum, mul_sum]
        exact sum_congr rfl fun h _ => by ring

end Chain

section Bounds

variable {q A₀ x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B : ℕ}

/-! ### Band facts on the chain -/

/-- The active labels of group `i` are primes of `𝒫_i`. -/
theorem chainState_mem_band (s : ChainState x d Y d₀ u v r B) (i : Fin K)
    (k : Fin (padCount x + 1)) : s.2.1.1 i k ∈ band x (d.a i) := by
  have h := s.2.1.2
  unfold lists at h
  exact Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 (mem_filter.1 h).1 i) k

/-- The prime of a particle is a band prime. -/
theorem particle_mem_bandPrimes (xp : Particle x d) : xp.1.1 ∈ bandPrimes x d := by
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.1 xp.2
  obtain ⟨ℓ, -, hℓ⟩ := mem_image.1 hxp
  rw [← hℓ]
  exact hp

/-- Every performed birth of a history is a band prime. -/
theorem births_mem_bandPrimes {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    {h : History x d Y d₀ u v r N} (hh : h ∈ histories x d Y d₀ u v r B N) :
    ∀ a p, births s h a = some p → p ∈ bandPrimes x d := by
  rintro (⟨i, k⟩ | ⟨j, i⟩ | ⟨j, k⟩) p hp
  · -- an initial slot
    obtain rfl : s.2.1.1 i k = p := Option.some_injective _ hp
    exact mem_biUnion.2 ⟨i, mem_univ _, chainState_mem_band s i k⟩
  · -- a fresh label
    simp only [births] at hp
    split_ifs at hp
    obtain rfl := Option.some_injective _ hp
    have he := Fintype.mem_piFinset.1 (mem_product.1 hh).2 j
    simp only [edgeChoices, mem_product, Fintype.mem_piFinset] at he
    exact mem_biUnion.2 ⟨i, mem_univ _, (he.2.2.2.1 i).1⟩
  · -- a ghost birth
    simp only [births] at hp
    have hmem := List.mem_of_getElem? hp
    rw [batchPrimes, Multiset.mem_sort, Multiset.mem_sum] at hmem
    obtain ⟨xp, -, hxp⟩ := hmem
    rw [Multiset.eq_of_mem_replicate hxp]
    exact particle_mem_bandPrimes xp

/-- The chain measure is nonnegative when the birth weights of band primes are. -/
theorem chainMeasure_nonneg {N : ℕ} (hν : ∀ p ∈ bandPrimes x d, 0 ≤ primeWeight q x d N p)
    (s : ChainState x d Y d₀ u v r B) : 0 ≤ chainMeasure q x d Y d₀ u v r B N s :=
  mul_nonneg
    (prod_nonneg fun i _ => prod_nonneg fun k _ =>
      hν _ (mem_biUnion.2 ⟨i, mem_univ _, chainState_mem_band s i k⟩))
    (memWeight_nonneg (fun xp => hν _ (particle_mem_bandPrimes xp)) _)

variable (q x d) in
/-- For a prime `p ∈ 𝒫_i` with `V_i ≥ 1/2` and `p + 1 ≥ 2(N + 1)`: `b'_p ≥ 1/2`, so
`0 ≤ ν(p) ≤ 2 / (V_i p)`. -/
theorem primeWeight_le_two_div (hq : 0 ≤ q) {N p : ℕ} {i : Fin K}
    (hp : p ∈ band x (d.a i))
    (hV : 1 / 2 ≤ harmonicMass (band x (d.a i))) (hpN : 2 * (N + 1) ≤ p + 1) :
    0 ≤ primeWeight q x d N p ∧
      primeWeight q x d N p ≤ 2 / (harmonicMass (band x (d.a i)) * p) := by
  set V := harmonicMass (band x (d.a i)) with hVdef
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  -- `b'_p ≥ 1/2`: each defect is at most `1`
  have hb : 1 / 2 ≤ baseline q N p := by
    have hsum : ∑ j ∈ range (N + 1), dampDefect q N j ≤ N + 1 :=
      calc ∑ j ∈ range (N + 1), dampDefect q N j ≤ ∑ _j ∈ range (N + 1), (1 : ℝ) :=
            sum_le_sum fun j _ => by
              unfold dampDefect
              split_ifs <;> linarith [Real.sqrt_nonneg q]
        _ = N + 1 := by simp
    have hpN' : 2 * ((N : ℝ) + 1) ≤ p + 1 := by exact_mod_cast hpN
    have h : ((p : ℝ) + 1)⁻¹ * ∑ j ∈ range (N + 1), dampDefect q N j ≤ 1 / 2 := by
      rw [inv_mul_le_iff₀ (by positivity)]
      linarith
    unfold baseline
    linarith
  -- `V(p) ≥ V_i`
  have hmass : V ≤ primeMass x d p := by
    have hle := single_le_sum (s := univ)
      (f := fun i' => if p ∈ band x (d.a i') then harmonicMass (band x (d.a i')) else 0)
      (fun i' _ => by
        split_ifs
        · exact sum_nonneg fun p _ => by positivity
        · exact le_rfl) (mem_univ i)
    simpa [hp, primeMass] using hle
  have hV0 : 0 < V := by linarith
  -- the denominator is at least `V_i p / 2`
  have hpos : 0 < V * p / 2 := by positivity
  have hden : V * p / 2 ≤ primeMass x d p * ((p : ℝ) + 1) * baseline q N p :=
    calc V * p / 2 = V * p * (1 / 2) := by ring
      _ ≤ primeMass x d p * ((p : ℝ) + 1) * baseline q N p :=
          mul_le_mul (mul_le_mul hmass (by linarith) (by positivity) (by linarith)) hb
            (by norm_num) (mul_nonneg (by linarith) (by positivity))
  unfold primeWeight
  refine ⟨(one_div_pos.2 (hpos.trans_le hden)).le, ?_⟩
  calc 1 / (primeMass x d p * ((p : ℝ) + 1) * baseline q N p) ≤ 1 / (V * p / 2) :=
        one_div_le_one_div_of_le hpos hden
    _ = 2 / (V * p) := by field_simp

variable (q x d) in
/-- Under the hypotheses of `primeWeight_le_two_div`, the birth weights of a band sum to at
most `2`. -/
theorem sum_band_primeWeight_le (hq : 0 ≤ q) {N : ℕ} {i : Fin K}
    (hV : 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hpN : ∀ p ∈ band x (d.a i), 2 * (N + 1) ≤ p + 1) :
    ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 2 := by
  have hV0 : 0 < harmonicMass (band x (d.a i)) := by linarith
  calc ∑ p ∈ band x (d.a i), primeWeight q x d N p
      ≤ ∑ p ∈ band x (d.a i), 2 / (harmonicMass (band x (d.a i)) * p) :=
        sum_le_sum fun p hp => (primeWeight_le_two_div q x d hq hp hV (hpN p hp)).2
    _ = 2 / harmonicMass (band x (d.a i)) * harmonicMass (band x (d.a i)) := by
        rw [harmonicMass, mul_sum]
        exact sum_congr rfl fun p _ => by rw [div_mul_div_comm, mul_one]
    _ = 2 := div_mul_cancel₀ _ hV0.ne'

/-- **The boundary norm**: `‖𝐛‖² ≤ 2^{KM}`. On the support of `𝐛` the memory is empty, and
the active lists carry at most `∏_{i,k} ∑_{p ∈ 𝒫_i} ν(p) ≤ 2^{KM}`. -/
theorem wnormSq_chainInit_le {N : ℕ} (hν₀ : ∀ p ∈ bandPrimes x d, 0 ≤ primeWeight q x d N p)
    (hν : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 2) :
    wnormSq (chainMeasure q x d Y d₀ u v r B N) (chainInit x d Y d₀ u v r B) ≤
      2 ^ (K * (padCount x + 1)) := by
  -- on the support of `𝐛` the memory weight is one
  have hpt : ∀ s : ChainState x d Y d₀ u v r B,
      chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ ^ 2 =
        (if s.1.1 = (1, 0) then 1 else 0) *
          ((∏ i, ∏ k, primeWeight q x d N (s.2.1.1 i k)) *
            if memSize s.2.2.1 = 0 then 1 else 0) := by
    intro s
    unfold chainInit chainMeasure
    by_cases h₁ : s.1.1 = (1, 0) <;> by_cases h₂ : memSize s.2.2.1 = 0 <;> simp [h₁, h₂]
    have h0 : ∀ xp, s.2.2.1 xp = 0 := fun xp => by
      have := le_memSize s.2.2.1 xp
      omega
    simp [memWeight, h0]
  -- at most one position is `e₁`, and at most one memory is empty
  have hz : ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
      (if z.1 = (1, 0) then (1 : ℝ) else 0) ≤ 1 := by
    have hc : #(univ.filter fun z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) =>
        z.1 = (1, 0)) ≤ 1 :=
      card_le_one.2 fun a ha b hb =>
        Subtype.ext ((mem_filter.1 ha).2.trans (mem_filter.1 hb).2.symm)
    rw [sum_boole]
    exact_mod_cast hc
  have hS : ∑ S : MemState (Particle x d) B, (if memSize S.1 = 0 then (1 : ℝ) else 0) ≤ 1 := by
    have hc : #(univ.filter fun S : MemState (Particle x d) B => memSize S.1 = 0) ≤ 1 := by
      refine card_le_one.2 fun a ha b hb => Subtype.ext (funext fun xp => ?_)
      have ha' := le_memSize a.1 xp
      have hb' := le_memSize b.1 xp
      rw [(mem_filter.1 ha).2] at ha'
      rw [(mem_filter.1 hb).2] at hb'
      omega
    rw [sum_boole]
    exact_mod_cast hc
  -- the lists carry at most `2^{KM}`
  have hlists : ∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k) ≤
      2 ^ (K * (padCount x + 1)) :=
    calc ∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k)
        = ∑ a ∈ lists x d (padCount x), ∏ i, ∏ k, primeWeight q x d N (a i k) :=
          sum_coe_sort _ (fun a : Lists K (padCount x) => ∏ i, ∏ k, primeWeight q x d N (a i k))
      _ ≤ ∑ a ∈ Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin (padCount x + 1) =>
            band x (d.a i), ∏ i, ∏ k, primeWeight q x d N (a i k) := by
          refine sum_le_sum_of_subset_of_nonneg (by unfold lists; exact filter_subset _ _)
            fun a ha _ => prod_nonneg fun i _ => prod_nonneg fun k _ => hν₀ _ ?_
          exact mem_biUnion.2 ⟨i, mem_univ _,
            Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 ha i) k⟩
      _ = ∏ i, ∑ a ∈ Fintype.piFinset fun _ : Fin (padCount x + 1) => band x (d.a i),
            ∏ k, primeWeight q x d N (a k) :=
          (prod_univ_sum (fun i => Fintype.piFinset fun _ : Fin (padCount x + 1) =>
            band x (d.a i)) fun i a => ∏ k, primeWeight q x d N (a k)).symm
      _ = ∏ i, ∏ _k : Fin (padCount x + 1), ∑ p ∈ band x (d.a i), primeWeight q x d N p :=
          prod_congr rfl fun i _ => sum_prod_piFinset _ _
      _ ≤ ∏ _i : Fin K, ∏ _k : Fin (padCount x + 1), (2 : ℝ) :=
          prod_le_prod₀ (fun i _ => prod_nonneg fun k _ =>
              sum_nonneg fun p hp => hν₀ p (mem_biUnion.2 ⟨i, mem_univ _, hp⟩))
            fun i _ => prod_le_prod₀ (fun k _ =>
              sum_nonneg fun p hp => hν₀ p (mem_biUnion.2 ⟨i, mem_univ _, hp⟩))
              fun k _ => hν i
      _ = 2 ^ (K * (padCount x + 1)) := by
          rw [prod_const, prod_const, card_univ, card_univ, Fintype.card_fin, Fintype.card_fin,
            ← pow_mul, mul_comm]
  have hL : 0 ≤ ∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k) :=
    sum_nonneg fun a _ => prod_nonneg fun i _ => prod_nonneg fun k _ =>
      hν₀ _ (mem_biUnion.2 ⟨i, mem_univ _,
        Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 (mem_filter.1 a.2).1 i) k⟩)
  calc wnormSq (chainMeasure q x d Y d₀ u v r B N) (chainInit x d Y d₀ u v r B)
      = ∑ s : ChainState x d Y d₀ u v r B, (if s.1.1 = (1, 0) then 1 else 0) *
          ((∏ i, ∏ k, primeWeight q x d N (s.2.1.1 i k)) *
            if memSize s.2.2.1 = 0 then 1 else 0) := sum_congr rfl fun s _ => hpt s
    _ = (∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
          (if z.1 = (1, 0) then (1 : ℝ) else 0)) *
        ((∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k)) *
          ∑ S : MemState (Particle x d) B, (if memSize S.1 = 0 then (1 : ℝ) else 0)) := by
        rw [sum_mul_sum, sum_mul_sum]
        simp only [Fintype.sum_prod_type, mul_sum]
    _ ≤ 1 * ((∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k)) * 1) := by
        gcongr
    _ ≤ 2 ^ (K * (padCount x + 1)) := by rw [one_mul, mul_one]; exact hlists

/-! ### The phased products -/

/-- **The phased product**: if `ψ` has modulus at most one and is trivial off `U`, then
`𝒢^ψ₀ ℰ^ψ ⋯ ℰ^ψ 𝒢^ψ_N` has norm at most `C₀^{N+1} L^{-GN + (C_e + G)|U|}`. An edge with no
address in `U` is the plain edge, of norm `L^{-G}`; an edge with `m ≥ 1` addresses in `U` has
the crude norm `L^{C_e} ≤ L^{-G + (C_e + G) m}`. -/
theorem normLe_phasedProduct {N : ℕ} {L G Ce C₀ : ℝ} (hL : 1 ≤ L) (hCe : 0 ≤ Ce + G)
    (hC₀ : 0 ≤ C₀) (hμ : ∀ s, 0 ≤ chainMeasure q x d Y d₀ u v r B N s)
    (hG : ∀ (j : ℕ) (ψ : Fin B → Option ℕ → ℂ), (∀ k o, ‖ψ k o‖ ≤ 1) →
      NormLe (chainMeasure q x d Y d₀ u v r B N) (chainMeasure q x d Y d₀ u v r B N)
        (phasedGhost q x d Y d₀ u v r B N j ψ) C₀)
    (hE : ∀ ψ : Fin K → Option ℕ → ℂ, (∀ i o, ‖ψ i o‖ ≤ 1) →
      NormLe (chainMeasure q x d Y d₀ u v r B N) (chainMeasure q x d Y d₀ u v r B N)
        (phasedEdge q A₀ x d Y d₀ u v r B N ψ) (L ^ Ce))
    (hE₀ : NormLe (chainMeasure q x d Y d₀ u v r B N) (chainMeasure q x d Y d₀ u v r B N)
      (chainEdge q A₀ x d Y d₀ u v r B N) (L ^ (-G)))
    {U : Finset (BirthAddr (K := K) x B N)} {ψ : BirthAddr (K := K) x B N → Option ℕ → ℂ}
    (hψ : ∀ a o, ‖ψ a o‖ ≤ 1) (hψU : ∀ a ∉ U, ψ a = fun _ => 1) :
    NormLe (chainMeasure q x d Y d₀ u v r B N) (chainMeasure q x d Y d₀ u v r B N)
      (phasedProduct q A₀ x d Y d₀ u v r B N ψ)
      (C₀ ^ (N + 1) * L ^ (-G * N + (Ce + G) * #U)) := by
  have hL0 : 0 < L := by linarith
  -- the number `m_j` of addresses of edge `j` in `U`
  set m : Fin N → ℕ := fun j =>
    #(univ.filter fun i : Fin K => (.inr (.inl (j, i)) : BirthAddr (K := K) x B N) ∈ U) with hm
  -- each `𝒢^ψ_j ℰ^ψ` has norm at most `C₀ L^{-G + (C_e + G) m_j}`
  have hstep : ∀ j ∈ List.finRange N, NormLe (chainMeasure q x d Y d₀ u v r B N)
      (chainMeasure q x d Y d₀ u v r B N)
      (fun g => phasedGhost q x d Y d₀ u v r B N j (fun k => ψ (.inr (.inr (j.castSucc, k))))
        (phasedEdge q A₀ x d Y d₀ u v r B N (fun i => ψ (.inr (.inl (j, i)))) g))
      (C₀ * L ^ (-G + (Ce + G) * m j)) := by
    intro j _
    refine NormLe.comp (hG j _ fun k o => hψ _ o) ?_
    by_cases hj : m j = 0
    · -- no address in `U`: the plain edge
      have hone : (fun i => ψ (.inr (.inl (j, i)))) = fun _ _ => 1 := by
        funext i
        refine hψU _ fun hi => ?_
        rw [hm, card_eq_zero, filter_eq_empty_iff] at hj
        exact hj (mem_univ i) hi
      rw [hone, phasedEdge_one, hj, Nat.cast_zero, mul_zero, add_zero]
      exact hE₀
    · -- an address in `U`: the crude bound, with `C_e ≤ -G + (C_e + G) m_j`
      have h1 : (1 : ℝ) ≤ m j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
      refine NormLe.mono hμ (Real.rpow_nonneg hL0.le _) ?_ (hE _ fun i o => hψ _ o)
      refine Real.rpow_le_rpow_of_exponent_le hL ?_
      have : (Ce + G) * 1 ≤ (Ce + G) * m j := mul_le_mul_of_nonneg_left h1 hCe
      linarith
  -- compose along the chain
  have hfold := normLe_foldr _ (fun j : Fin N => C₀ * L ^ (-G + (Ce + G) * m j))
    (hG N (fun k => ψ (.inr (.inr (Fin.last N, k)))) fun k o => hψ _ o) (List.finRange N) hstep
  -- `∑_j m_j ≤ |U|`
  have hmU : ∑ j, m j ≤ #U := by
    have hsum : ∑ j, m j = #((univ : Finset (Fin N × Fin K)).filter fun ji =>
        (.inr (.inl ji) : BirthAddr (K := K) x B N) ∈ U) := by
      simp only [hm, card_filter, Fintype.sum_prod_type]
    rw [hsum]
    refine card_le_card_of_injOn (fun ji => .inr (.inl ji)) (fun ji hji => (mem_filter.1 hji).2)
      fun a _ b _ hab => ?_
    exact Sum.inl_injective (Sum.inr_injective hab)
  have hmU' : ∑ j, (m j : ℝ) ≤ #U := by exact_mod_cast hmU
  -- the constant is `C₀^{N+1} L^{-GN + (C_e + G) ∑_j m_j}`
  have hconst : ((List.finRange N).map fun j : Fin N => C₀ * L ^ (-G + (Ce + G) * m j)).prod *
      C₀ = C₀ ^ (N + 1) * L ^ (-G * N + (Ce + G) * ∑ j, (m j : ℝ)) := by
    rw [← Fin.prod_univ_def, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
      ← Real.rpow_sum_of_pos hL0, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      ← mul_sum, nsmul_eq_mul, pow_succ]
    ring_nf
  rw [hconst] at hfold
  refine NormLe.mono hμ (by positivity) ?_ hfold
  gcongr

/-! ### The block sums at low and high rank -/

open scoped Classical in
/-- **Low rank**: if every phased product with phases of modulus at most one, trivial off the
addresses of `𝒞`, has norm at most `c`, then `|blockSum(𝒞)| ≤ c ‖𝐛‖²`. The local phases
write `blockSum(𝒞)` as an average of matrix elements `⟨𝐛^ψ_init, 𝒢^ψ₀ ℰ^ψ ⋯ 𝒢^ψ_N 𝐛⟩`, where
the phases of the initial addresses multiply `𝐛`. -/
theorem norm_blockSum_le {N : ℕ} (hμ : ∀ s, 0 ≤ chainMeasure q x d Y d₀ u v r B N s)
    {𝒞 : Finset (Finset (BirthAddr (K := K) x B N))}
    (h𝒞 : 𝒞 ∈ blockSystems (BirthAddr (K := K) x B N)) {P : ℕ} (hP : 0 < P)
    (hβ : ∀ s : ChainState x d Y d₀ u v r B, ∀ h ∈ histories x d Y d₀ u v r B N, ∀ a p,
      births s h a = some p → p < P)
    {c : ℝ} (hc : 0 ≤ c)
    (hT : ∀ ψ : BirthAddr (K := K) x B N → Option ℕ → ℂ, (∀ a o, ‖ψ a o‖ ≤ 1) →
      (∀ a ∉ 𝒞.biUnion id, ψ a = fun _ => 1) →
      NormLe (chainMeasure q x d Y d₀ u v r B N) (chainMeasure q x d Y d₀ u v r B N)
        (phasedProduct q A₀ x d Y d₀ u v r B N ψ) c) :
    ‖blockSum q A₀ x d Y d₀ u v r B N 𝒞‖ ≤
      c * wnormSq (chainMeasure q x d Y d₀ u v r B N) (chainInit x d Y d₀ u v r B) := by
  obtain ⟨ψ, hψ, hψU, hid⟩ := exists_blockPhase h𝒞 hP
  set F := Fintype.piFinset fun _ : BirthAddr (K := K) x B N => range P with hF
  set Q := Fintype.card (BirthAddr (K := K) x B N) with hQ
  -- the phases of the initial addresses
  set ι : (BirthAddr (K := K) x B N → ℕ) → ChainState x d Y d₀ u v r B → ℂ := fun κ s =>
    ∏ a : Fin K × Fin (padCount x + 1), ψ κ (.inl a) (some (s.2.1.1 a.1 a.2)) with hι
  -- the history sum from each state is an average of phased products
  have hs : ∀ s, ∑ h ∈ histories x d Y d₀ u v r B N, chainWeight q A₀ s h *
      (∏ C ∈ 𝒞, if BlockRealized (births s h) C then 1 else 0) *
        chainInit x d Y d₀ u v r B (chainEnd s h) =
      ((P : ℂ) ^ Q)⁻¹ * ∑ κ ∈ F,
        ι κ s * phasedProduct q A₀ x d Y d₀ u v r B N (ψ κ) (chainInit x d Y d₀ u v r B) s := by
    intro s
    calc ∑ h ∈ histories x d Y d₀ u v r B N, chainWeight q A₀ s h *
          (∏ C ∈ 𝒞, if BlockRealized (births s h) C then 1 else 0) *
            chainInit x d Y d₀ u v r B (chainEnd s h)
        = ∑ h ∈ histories x d Y d₀ u v r B N, chainWeight q A₀ s h *
          (((P : ℂ) ^ Q)⁻¹ * ∑ κ ∈ F, ∏ a, ψ κ a (births s h a)) *
            chainInit x d Y d₀ u v r B (chainEnd s h) :=
          sum_congr rfl fun h hh => by rw [hid _ (hβ s h hh)]
      _ = ((P : ℂ) ^ Q)⁻¹ * ∑ κ ∈ F, ∑ h ∈ histories x d Y d₀ u v r B N,
          chainWeight q A₀ s h * (∏ a, ψ κ a (births s h a)) *
            chainInit x d Y d₀ u v r B (chainEnd s h) := by
          simp only [mul_sum, sum_mul]
          rw [sum_comm]
          exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
      _ = ((P : ℂ) ^ Q)⁻¹ * ∑ κ ∈ F, ι κ s *
          phasedProduct q A₀ x d Y d₀ u v r B N (ψ κ) (chainInit x d Y d₀ u v r B) s := by
          congr 1
          refine sum_congr rfl fun κ _ => ?_
          rw [phasedProduct_eq_sum_history, mul_sum]
          refine sum_congr rfl fun h _ => ?_
          have hinit : ∀ a : Fin K × Fin (padCount x + 1),
              births s h (.inl a) = some (s.2.1.1 a.1 a.2) := fun a => rfl
          rw [Fintype.prod_sum_type]
          simp only [hinit, hι]
          ring
  have hsum : blockSum q A₀ x d Y d₀ u v r B N 𝒞 = ((P : ℂ) ^ Q)⁻¹ * ∑ κ ∈ F, ∑ s,
      (chainMeasure q x d Y d₀ u v r B N s : ℂ) * (chainInit x d Y d₀ u v r B s * ι κ s) *
        phasedProduct q A₀ x d Y d₀ u v r B N (ψ κ) (chainInit x d Y d₀ u v r B) s := by
    rw [blockSum]
    simp only [hs, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  -- each phased matrix element is at most `c ‖𝐛‖²`
  have hκ : ∀ κ ∈ F, ‖∑ s, (chainMeasure q x d Y d₀ u v r B N s : ℂ) *
      (chainInit x d Y d₀ u v r B s * ι κ s) *
        phasedProduct q A₀ x d Y d₀ u v r B N (ψ κ) (chainInit x d Y d₀ u v r B) s‖ ≤
      c * wnormSq (chainMeasure q x d Y d₀ u v r B N) (chainInit x d Y d₀ u v r B) :=
    fun κ _ => norm_sum_mul_le_of_normLe hμ hc (hT (ψ κ) (hψ κ) (hψU κ)) fun s => by
      have hι1 : ‖ι κ s‖ ≤ 1 := by
        rw [hι, norm_prod]
        exact prod_le_one₀ (fun _ _ => norm_nonneg _) fun a _ => hψ κ _ _
      rw [norm_mul]
      calc ‖chainInit x d Y d₀ u v r B s‖ * ‖ι κ s‖ ≤ ‖chainInit x d Y d₀ u v r B s‖ * 1 :=
            mul_le_mul_of_nonneg_left hι1 (norm_nonneg _)
        _ = ‖chainInit x d Y d₀ u v r B s‖ := mul_one _
  -- `|F| = P^Q`
  have hcard : (#F : ℝ) = (P : ℝ) ^ Q := by
    rw [hF, Fintype.card_piFinset, prod_const, card_range, card_univ]
    push_cast
    rfl
  have hPQ : (0 : ℝ) < (P : ℝ) ^ Q := by positivity
  rw [hsum, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc ((P : ℝ) ^ Q)⁻¹ * ‖∑ κ ∈ F, ∑ s, (chainMeasure q x d Y d₀ u v r B N s : ℂ) *
        (chainInit x d Y d₀ u v r B s * ι κ s) *
          phasedProduct q A₀ x d Y d₀ u v r B N (ψ κ) (chainInit x d Y d₀ u v r B) s‖
      ≤ ((P : ℝ) ^ Q)⁻¹ * ∑ _κ ∈ F,
          c * wnormSq (chainMeasure q x d Y d₀ u v r B N) (chainInit x d Y d₀ u v r B) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum hκ)) (by positivity)
    _ = c * wnormSq (chainMeasure q x d Y d₀ u v r B N) (chainInit x d Y d₀ u v r B) := by
        rw [sum_const, nsmul_eq_mul, hcard, ← mul_assoc, inv_mul_cancel₀ hPQ.ne', one_mul]

open scoped Classical in
/-- **High rank**: `blockSum(𝒞)` is at most the absolute constrained history sum. -/
theorem norm_blockSum_le_realized {N : ℕ} (hμ : ∀ s, 0 ≤ chainMeasure q x d Y d₀ u v r B N s)
    (𝒞 : Finset (Finset (BirthAddr (K := K) x B N))) :
    ‖blockSum q A₀ x d Y d₀ u v r B N 𝒞‖ ≤
      ∑ s, chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ *
        ∑ h ∈ histories x d Y d₀ u v r B N,
          ‖chainWeight q A₀ s h‖ * ‖chainInit x d Y d₀ u v r B (chainEnd s h)‖ *
            ∏ C ∈ 𝒞, (if BlockRealized (births s h) C then 1 else 0) := by
  refine (norm_sum_le _ _).trans (sum_le_sum fun s _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ s)]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_))
    (mul_nonneg (hμ s) (norm_nonneg _))
  refine sum_congr rfl fun h _ => ?_
  have hind : ‖(∏ C ∈ 𝒞, if BlockRealized (births s h) C then 1 else 0 : ℂ)‖ =
      ∏ C ∈ 𝒞, (if BlockRealized (births s h) C then 1 else 0 : ℝ) := by
    rw [norm_prod]
    exact prod_congr rfl fun C _ => by split_ifs <;> simp
  rw [norm_mul, norm_mul, hind]
  ring

end Bounds

/-- `N = 2R` is between `L^{1/2}` and `L^{1/2} + 2`. -/
theorem two_mul_momentPower_mem {x : ℝ} (hL : 0 < Real.log x) :
    Real.log x ^ (1 / 2 : ℝ) ≤ ((2 * momentPower x : ℕ) : ℝ) ∧
      ((2 * momentPower x : ℕ) : ℝ) ≤ Real.log x ^ (1 / 2 : ℝ) + 2 := by
  have hpos : 0 < Real.log x ^ (1 / 2 : ℝ) / 2 := by positivity
  have h₁ : Real.log x ^ (1 / 2 : ℝ) / 2 ≤ momentPower x := Nat.le_ceil _
  have h₂ : (momentPower x : ℝ) < Real.log x ^ (1 / 2 : ℝ) / 2 + 1 :=
    Nat.ceil_lt_add_one hpos.le
  push_cast
  constructor <;> linarith

end Erdos408.OneSided
