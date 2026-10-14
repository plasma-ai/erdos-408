module

public import Erdos408.OneSided.Moment.Chain.EdgeStage

/-!
# The memory identity along the path

The running distinct-birth history sum (`distinctFold`, `Moment/Chain/Births.lean`) from a
consistent state at the visit `t` equals the line-free path sum from that state with the
lifespan product of all band primes (`distinctFold_eq_path`):

`ρ^{hits(S, z)} distinctFold(t, s, Bn) = ∑_π A⁰-weight(π from t) [z_N = e₁] ∏_p β_p(t, status_p)`,

the sum over the paths `π` that agree with a fixed path `π₀` before `t` and pass through the
state's position and lists at `t`. The proof is a backward induction on the number of
remaining edges:

* the last visit is the ghost step alone, since after the last ghost a pending prime has
  value `0` (`postProd_last`) and `𝐛` requires empty memory;
* an earlier visit is the ghost step (`ghost_stage`) followed by the edge step
  (`edge_stage`) for each free choice, and the free choices recombine into `A⁰` by the free
  expansion (`sum_edgeOp_mul_eq`).
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

section Induction

variable (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

variable {x d Y d₀ u v r B}

/-! ### Paths through a state -/

open scoped Classical in
/-- The paths that agree with `π₀` before the visit `t` and pass through `a` at `t`. -/
def pathsFrom {N : ℕ} (π₀ : Fin (N + 1) → FreeState x d Y d₀ u v r) (t : ℕ)
    (a : FreeState x d Y d₀ u v r) : Finset (Fin (N + 1) → FreeState x d Y d₀ u v r) :=
  univ.filter fun π => (∀ j : Fin (N + 1), (j : ℕ) < t → π j = π₀ j) ∧
    ∀ j : Fin (N + 1), (j : ℕ) = t → π j = a

/-- Membership in `pathsFrom`. -/
theorem mem_pathsFrom {N : ℕ} {π₀ π : Fin (N + 1) → FreeState x d Y d₀ u v r} {t : ℕ}
    {a : FreeState x d Y d₀ u v r} :
    π ∈ pathsFrom π₀ t a ↔ (∀ j : Fin (N + 1), (j : ℕ) < t → π j = π₀ j) ∧
      ∀ j : Fin (N + 1), (j : ℕ) = t → π j = a := by
  simp [pathsFrom]

/-- The `A⁰`-weight of a path from the visit `t` on. -/
def weightFrom {N : ℕ} (π : Fin (N + 1) → FreeState x d Y d₀ u v r) (t : ℕ) : ℂ :=
  ∏ j ∈ univ.filter (fun j : Fin N => t ≤ (j : ℕ)),
    (freeRootModel d Y d₀ u v r).edgeOp 1 A₀ x d Y d₀ (π j.castSucc) (π j.succ)

/-- The indicator that a path ends at `e₁`. -/
def endInd {N : ℕ} (π : Fin (N + 1) → FreeState x d Y d₀ u v r) : ℂ :=
  if (π (Fin.last N)).1.1.1 = (1, 0) then 1 else 0

/-- A path through `a` at `t ≤ N` is at `a` there. -/
theorem apply_of_mem_pathsFrom {N : ℕ} {π₀ π : Fin (N + 1) → FreeState x d Y d₀ u v r} {t : ℕ}
    {a : FreeState x d Y d₀ u v r} (hπ : π ∈ pathsFrom π₀ t a) (ht : t ≤ N) :
    π ⟨t, Nat.lt_succ_of_le ht⟩ = a :=
  (mem_pathsFrom.1 hπ).2 _ rfl

/-- The lines of a path through `a` at `t`. -/
theorem pathLines_of_mem_pathsFrom {N : ℕ} {π₀ π : Fin (N + 1) → FreeState x d Y d₀ u v r}
    {t : ℕ} {a : FreeState x d Y d₀ u v r} (hπ : π ∈ pathsFrom π₀ t a) (ht : t ≤ N) (p : ℕ) :
    pathLines p π t = lineOf p a.1.1.1 := by
  have := pathLines_val p π ⟨t, Nat.lt_succ_of_le ht⟩
  rw [apply_of_mem_pathsFrom hπ ht] at this
  exact this

/-- The activity of a path through `a` at `t`. -/
theorem mem_activeSet_of_mem_pathsFrom {N : ℕ} {π₀ π : Fin (N + 1) → FreeState x d Y d₀ u v r}
    {t : ℕ} {a : FreeState x d Y d₀ u v r} (hπ : π ∈ pathsFrom π₀ t a) (ht : t ≤ N) (p : ℕ) :
    t ∈ activeSet p π ↔ ∃ i h, a.1.2 i h = p := by
  have := mem_activeSet p π ⟨t, Nat.lt_succ_of_le ht⟩
  rw [apply_of_mem_pathsFrom hπ ht] at this
  exact this

/-- At the last visit only one path is left. -/
theorem sum_pathsFrom_last {N : ℕ} (π₀ : Fin (N + 1) → FreeState x d Y d₀ u v r)
    (a : FreeState x d Y d₀ u v r) (F : (Fin (N + 1) → FreeState x d Y d₀ u v r) → ℂ) :
    ∑ π ∈ pathsFrom π₀ N a, F π = F fun j => if (j : ℕ) = N then a else π₀ j := by
  classical
  refine sum_eq_single_of_mem _ ?_ fun π hπ hne => absurd ?_ hne
  · refine mem_pathsFrom.2 ⟨fun j hj => ?_, fun j hj => ?_⟩
    · simp [hj.ne]
    · simp [hj]
  · funext j
    by_cases hj : (j : ℕ) = N
    · simp [hj, (mem_pathsFrom.1 hπ).2 j hj]
    · simp [hj, (mem_pathsFrom.1 hπ).1 j (lt_of_le_of_ne (Nat.lt_succ_iff.1 j.2) hj)]

/-- Past the last edge the weight is `1`. -/
theorem weightFrom_last {N : ℕ} (π : Fin (N + 1) → FreeState x d Y d₀ u v r) :
    weightFrom A₀ π N = 1 := by
  rw [weightFrom, filter_false_of_mem fun j _ => not_le.2 j.2, prod_empty]

/-- Splitting a path at its visit `t < N`: the first edge, and the paths through the next
state. -/
theorem sum_pathsFrom_succ {N : ℕ} (π₀ : Fin (N + 1) → FreeState x d Y d₀ u v r) {t : ℕ}
    (ht : t < N) (a : FreeState x d Y d₀ u v r)
    (F : (Fin (N + 1) → FreeState x d Y d₀ u v r) → ℂ) :
    ∑ π ∈ pathsFrom π₀ t a, weightFrom A₀ π t * F π =
      ∑ b, (freeRootModel d Y d₀ u v r).edgeOp 1 A₀ x d Y d₀ a b *
        ∑ π ∈ pathsFrom (fun j => if (j : ℕ) = t then a else π₀ j) (t + 1) b,
          weightFrom A₀ π (t + 1) * F π := by
  classical
  set t₁ : Fin (N + 1) := ⟨t + 1, Nat.succ_lt_succ ht⟩
  -- step: group the paths by their state at `t + 1`
  rw [← sum_fiberwise (pathsFrom π₀ t a) (fun π => π t₁)]
  refine sum_congr rfl fun b _ => ?_
  have hset : (pathsFrom π₀ t a).filter (fun π => π t₁ = b) =
      pathsFrom (fun j => if (j : ℕ) = t then a else π₀ j) (t + 1) b := by
    ext π
    rw [mem_filter, mem_pathsFrom, mem_pathsFrom]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · by_cases hjt : (j : ℕ) = t
        · simp [hjt, h₂ j hjt]
        · simp [hjt, h₁ j (by omega)]
      · rw [show j = t₁ from Fin.ext hj, h₃]
    · rintro ⟨h₁, h₂⟩
      refine ⟨⟨fun j hj => ?_, fun j hj => ?_⟩, h₂ t₁ rfl⟩
      · have := h₁ j (by omega)
        simpa [hj.ne] using this
      · have := h₁ j (by omega)
        simpa [hj] using this
  rw [hset, mul_sum]
  refine sum_congr rfl fun π hπ => ?_
  -- step: the weight from `t` is the first edge times the weight from `t + 1`
  have hfilter : univ.filter (fun j : Fin N => t ≤ (j : ℕ)) =
      insert ⟨t, ht⟩ (univ.filter fun j : Fin N => t + 1 ≤ (j : ℕ)) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  have hπt : π (Fin.castSucc ⟨t, ht⟩) = a := by
    have := (mem_pathsFrom.1 hπ).1 ⟨t, by omega⟩ (by simp)
    simpa using this
  have hπt₁ : π (Fin.succ ⟨t, ht⟩) = b := (mem_pathsFrom.1 hπ).2 _ rfl
  rw [weightFrom, hfilter, prod_insert (by simp), hπt, hπt₁, ← weightFrom]
  ring

/-! ### The baseline and the last visit -/

variable {q} in
/-- The damping defects are at most `1`. -/
theorem dampDefect_le_one (hq : 0 < q) (N j : ℕ) : dampDefect q N j ≤ 1 := by
  unfold dampDefect
  split_ifs <;> linarith [Real.sqrt_nonneg q]

variable {q} in
/-- For a prime `p > N`, `(p + 1) b'_p = (p + 1) - ∑_{j ≤ N} η'_j > 0`. -/
theorem baseline_mul_pos (hq : 0 < q) {N p : ℕ} (hp : N < p) :
    0 < ((p : ℝ) + 1) * baseline q N p := by
  have hsum : ∑ j ∈ range (N + 1), dampDefect q N j ≤ (N : ℝ) + 1 := by
    calc ∑ j ∈ range (N + 1), dampDefect q N j ≤ ∑ _j ∈ range (N + 1), (1 : ℝ) :=
          sum_le_sum fun j _ => dampDefect_le_one hq N j
      _ = (N : ℝ) + 1 := by simp
  have hp' : (N : ℝ) + 1 < (p : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hp
  have h : ((p : ℝ) + 1) * baseline q N p =
      (p : ℝ) + 1 - ∑ j ∈ range (N + 1), dampDefect q N j := by
    rw [baseline, mul_sub, mul_one, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  rw [h]
  linarith

variable {q} in
/-- The birth constant inverts `(p + 1) - ∑_{j ≤ N} η'_j`. -/
theorem birthConst_mul (hq : 0 < q) {N p : ℕ} (hp : N < p) :
    birthConst q N p * ((p : ℝ) + 1 - ∑ j ∈ range (N + 1), dampDefect q N j) = 1 := by
  have h : ((p : ℝ) + 1) * baseline q N p =
      (p : ℝ) + 1 - ∑ j ∈ range (N + 1), dampDefect q N j := by
    rw [baseline, mul_sub, mul_one, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  rw [birthConst, ← h, inv_mul_cancel₀ (baseline_mul_pos hq hp).ne']

open scoped Classical in
variable {q} in
/-- After the last ghost, the lifespan product of a consistent state is the indicator of the
empty memory. -/
theorem postProd_last (hq : 0 < q) {N : ℕ} (hbig : ∀ p ∈ bandPrimes x d, N < p)
    (π : Fin (N + 1) → FreeState x d Y d₀ u v r) {J : ℕ} {act : Lists K J}
    {S : Particle x d → ℕ} {Bn : Multiset ℕ} (hS : Consistent act S Bn) :
    postProd q N π N act S Bn = if memSize S = 0 then 1 else 0 := by
  have hval : ∀ p ∈ bandPrimes x d, primePost q N π p N (statusOf act S Bn p) =
      if ∃ ℓ, statusOf act S Bn p = .pending ℓ then 0 else 1 := by
    intro p hp
    rw [primePost, postValue_last (activeSet_subset p π) (birthConst_mul hq (hbig p hp))]
    cases statusOf act S Bn p <;> simp
  rw [postProd, prod_congr rfl hval]
  by_cases hm : memSize S = 0
  · rw [ite_eq_left hm]
    refine prod_eq_one fun p _ => ite_eq_right fun ⟨ℓ, h⟩ => ?_
    obtain ⟨xp, -, hxp⟩ := exists_of_statusOf_eq_pending h
    exact hxp (Nat.eq_zero_of_le_zero (hm ▸ le_memSize S xp))
  · rw [ite_eq_right hm]
    obtain ⟨xp, hxp⟩ : ∃ xp, S xp ≠ 0 := by
      by_contra h
      push Not at h
      exact hm (sum_eq_zero fun xp _ => h xp)
    have hp : xp.1.1 ∈ bandPrimes x d :=
      (mem_particles.1 (show (xp.1.1, xp.1.2) ∈ particles x d from xp.2)).1
    exact prod_eq_zero hp (ite_eq_left ⟨_, statusOf_of_pend hS hxp⟩)

/-- A memory of size zero has no pending hits. -/
theorem pendingHits_of_memSize_eq_zero {z : ℤ × ℤ} {S : Particle x d → ℕ} (h : memSize S = 0) :
    pendingHits x d z S = 0 :=
  sum_eq_zero fun xp _ => by
    have := Nat.eq_zero_of_le_zero (h ▸ le_memSize S xp)
    simp [this]

/-- The position of `chainFree s` is the position of `s`. -/
theorem chainFree_pos (s : ChainState x d Y d₀ u v r B) : (chainFree s).1.1.1 = s.1.1 := rfl

/-- The lists of `chainFree s` are the lists of `s`. -/
theorem chainFree_lists (s : ChainState x d Y d₀ u v r B) : (chainFree s).1.2 = s.2.1.1 := rfl

open scoped Classical in
/-- **The last visit**: the running sum of the last ghost is the path sum. -/
theorem distinctFold_zero_eq (hq : 0 < q)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) (hB : (bandPrimes x d).card ≤ B) {N : ℕ}
    (hbig : ∀ p ∈ bandPrimes x d, N < p) (π₀ : Fin (N + 1) → FreeState x d Y d₀ u v r)
    (s : ChainState x d Y d₀ u v r B) {Bn : Multiset ℕ} (hS : Consistent s.2.1.1 s.2.2.1 Bn) :
    (pendingWeight q : ℂ) ^ pendingHits x d s.1.1 s.2.2.1 *
        distinctFold q A₀ Y d₀ u v r B N 0 N s Bn =
      ∑ π ∈ pathsFrom π₀ N (chainFree s),
        weightFrom A₀ π N * endInd π * (lifeProd q N π N s.2.1.1 s.2.2.1 Bn : ℂ) := by
  rw [sum_pathsFrom_last, weightFrom_last, one_mul]
  set πs : Fin (N + 1) → FreeState x d Y d₀ u v r := fun j => if (j : ℕ) = N then chainFree s
    else π₀ j
  have hmem := (mem_pathsFrom (π₀ := π₀) (π := πs) (t := N) (a := chainFree s)).2
    ⟨fun j hj => by simp [πs, hj.ne], fun j hj => by simp [πs, hj]⟩
  -- step: the ghost step at the last visit
  rw [← ghost_stage q hq hdisj hV hB le_rfl πs s hS
    (fun p => pathLines_of_mem_pathsFrom hmem le_rfl p)
    (fun p => mem_activeSet_of_mem_pathsFrom hmem le_rfl p)]
  have hend : endInd πs = if s.1.1 = (1, 0) then 1 else 0 := by
    simp [endInd, πs, chainFree_pos]
  rw [hend, distinctFold, mul_sum]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun g _ => ?_
  by_cases hv : GhostValid (HitsAt x d s.1.1) B s.2.2.1 g
  · by_cases hnd : (Bn + batchBirths g.2).Nodup
    · have hc := consistent_ghostMem hS (ghostOK_of_valid hv hnd)
      rw [postProd_last hq hbig πs hc, ← chainGhostOut_mem hv, visitWeight_eq q,
        ite_eq_left hnd, chainInit]
      by_cases hm : memSize (chainGhostOut x d Y d₀ u v r B s g).2.2.1 = 0
      · rw [ite_eq_left hm, pendingHits_of_memSize_eq_zero hm]
        have : (chainGhostOut x d Y d₀ u v r B s g).1.1 = s.1.1 := rfl
        simp only [this, hm, and_true]
        split_ifs <;> push_cast <;> ring
      · simp [hm]
    · simp [hnd]
  · have h0 : chainGhostCoef q x d Y d₀ u v r B N N s g = 0 := by
      rw [chainGhostCoef, ghostCoef, ite_eq_right hv]
    rw [visitWeight, ite_eq_right hv, h0]
    simp

/-! ### An earlier visit -/

/-- The edge choices are the free choices with stored groups and promotion flags. -/
theorem sum_edgeChoices (F : EdgeChoice x d Y d₀ u v r → ℂ) :
    ∑ c ∈ edgeChoices x d Y d₀ u v r, F c =
      ∑ c₀ ∈ freeChoices x d Y d₀ u v r, ∑ St : Finset (Fin K), ∑ fl : Fin K → Bool,
        F (toEdge c₀ St fl) := by
  simp only [← sum_product']
  refine sum_nbij' (fun c => ((c.1, c.2.2.1, fun i => (c.2.2.2.1 i).1, c.2.2.2.2), c.2.1,
    fun i => (c.2.2.2.1 i).2)) (fun e => toEdge e.1 e.2.1 e.2.2) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp_all [edgeChoices, freeChoices]
  · intro e he
    simp_all [edgeChoices, freeChoices, toEdge]
  · intro c _
    rfl
  · intro e _
    rfl
  · intro c _
    rfl

/-- The memory restrictions and distinct fresh labels make the flags compatible. -/
theorem edgeGood_of_valid {s : ChainState x d Y d₀ u v r B} {c₀ : FreeChoice x d Y d₀ u v r}
    (hc₀ : c₀ ∈ freeChoices x d Y d₀ u v r) {Bn : Multiset ℕ} {St : Finset (Fin K)}
    {fl : Fin K → Bool} (hm : MemValid x d Y d₀ u v r B s (toEdge c₀ St fl))
    (hnd : (Bn + freshBirths (toEdge c₀ St fl)).Nodup) : EdgeGood (s := s) hc₀ Bn fl := by
  classical
  intro i
  refine ⟨fun hfi => ?_, fun hfi hB' => ?_⟩
  · obtain ⟨xp, hxp, h1⟩ := hm.1 i hfi
    have : promPart hc₀ i = xp := (Subtype.ext hxp).symm
    rw [this]
    exact Nat.one_le_iff_ne_zero.1 h1
  · have h₁ := Multiset.nodup_iff_count_le_one.1 hnd (c₀.2.2.1 i)
    rw [Multiset.count_add, count_freshBirths] at h₁
    have h₂ := Multiset.count_pos.2 hB'
    have h₃ : 0 < (univ.filter fun j => fl j = false ∧ c₀.2.2.1 j = c₀.2.2.1 i).card :=
      card_pos.2 ⟨i, mem_filter.2 ⟨mem_univ _, hfi, rfl⟩⟩
    omega

/-- The free output of an admissible choice: its target and its target lists. -/
theorem freeOut_val {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hv : FreeValid x d Y d₀ u v r B s c) : (freeOut s c).1 = (c.2.2.1, edgeTgt s c) := by
  rw [freeOut, dite_eq_left hv]
  rfl

/-- Moving the innermost of four sums outside. -/
theorem sum_comm_four {α β γ δ : Type*} (sa : Finset α) (sb : Finset β) (sc : Finset γ)
    (sd : Finset δ) (F : α → β → γ → δ → ℂ) :
    ∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, ∑ e ∈ sd, F a b c e =
      ∑ e ∈ sd, ∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, F a b c e := by
  calc ∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, ∑ e ∈ sd, F a b c e =
      ∑ a ∈ sa, ∑ e ∈ sd, ∑ b ∈ sb, ∑ c ∈ sc, F a b c e := by
        refine sum_congr rfl fun a _ => ?_
        rw [sum_comm (s := sd)]
        exact sum_congr rfl fun b _ => sum_comm
    _ = _ := sum_comm

open scoped Classical in
/-- One term of the running sum at an earlier visit, against the induction hypothesis. -/
theorem distinctFold_term_eq
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) {N n t : ℕ}
    (π₁ : Fin (N + 1) → FreeState x d Y d₀ u v r)
    (ih : ∀ (s : ChainState x d Y d₀ u v r B) (Bn : Multiset ℕ),
      Consistent s.2.1.1 s.2.2.1 Bn →
        (pendingWeight q : ℂ) ^ pendingHits x d s.1.1 s.2.2.1 *
            distinctFold q A₀ Y d₀ u v r B N n (t + 1) s Bn =
          ∑ π ∈ pathsFrom π₁ (t + 1) (chainFree s),
            weightFrom A₀ π (t + 1) * endInd π * (lifeProd q N π (t + 1) s.2.1.1 s.2.2.1 Bn : ℂ))
    (s : ChainState x d Y d₀ u v r B) {Bn : Multiset ℕ} (hS : Consistent s.2.1.1 s.2.2.1 Bn)
    (g : GhostChoice x d) {c₀ : FreeChoice x d Y d₀ u v r}
    (hc₀ : c₀ ∈ freeChoices x d Y d₀ u v r) (St : Finset (Fin K)) (fl : Fin K → Bool) :
    (pendingWeight q : ℂ) ^ pendingHits x d s.1.1 s.2.2.1 *
        (chainGhostCoef q x d Y d₀ u v r B N t s g *
          chainEdgeCoef q A₀ x d Y d₀ u v r B N (chainGhostOut x d Y d₀ u v r B s g)
            (toEdge c₀ St fl) *
          (if (Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl)).Nodup then 1 else 0) *
          distinctFold q A₀ Y d₀ u v r B N n (t + 1)
            (chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s g) (toEdge c₀ St fl))
            (Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl))) =
      freeCoef A₀ s (toEdge₀ c₀) *
        ∑ π ∈ pathsFrom π₁ (t + 1) (freeOut s (toEdge₀ c₀)),
          weightFrom A₀ π (t + 1) * endInd π *
            ((visitWeight q N t s g * (if (Bn + batchBirths g.2).Nodup then 1 else 0) *
              ((if MemValid x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s g) (toEdge c₀ St fl)
                  then ∏ i, memLabelWeight q x d N (chainGhostOut x d Y d₀ u v r B s g).2.2.1
                    (toEdge c₀ St fl) i else 0) *
                (if (Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl)).Nodup then 1 else 0) *
                lifeProd q N π (t + 1) (edgeTgt s (toEdge c₀ St fl))
                  (edgeMem (chainGhostOut x d Y d₀ u v r B s g) (toEdge c₀ St fl))
                  (Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl))) : ℝ) : ℂ) := by
  set sg := chainGhostOut x d Y d₀ u v r B s g
  have hcoef := chainEdgeCoef_eq_mul q A₀ hdisj N sg c₀ hc₀ St fl
  have hfree : freeCoef A₀ sg (toEdge₀ c₀) = freeCoef A₀ s (toEdge₀ c₀) :=
    freeCoef_congr A₀ rfl rfl _
  rw [hcoef, hfree]
  -- the cases where a coefficient or a distinctness condition fails
  by_cases hv : GhostValid (HitsAt x d s.1.1) B s.2.2.1 g
  swap
  · have h0 : chainGhostCoef q x d Y d₀ u v r B N t s g = 0 := by
      rw [chainGhostCoef, ghostCoef, ite_eq_right hv]
    rw [h0, visitWeight, ite_eq_right hv]
    simp only [zero_mul, mul_zero, Complex.ofReal_zero, sum_const_zero]
  by_cases hnd : (Bn + batchBirths g.2).Nodup
  swap
  · have hnd' : ¬(Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl)).Nodup := fun h =>
      hnd (Multiset.nodup_add.1 h).1
    rw [ite_eq_right hnd', ite_eq_right hnd]
    simp only [zero_mul, mul_zero, Complex.ofReal_zero, sum_const_zero]
  by_cases hf : FreeValid x d Y d₀ u v r B s (toEdge₀ c₀)
  swap
  · rw [freeCoef, ite_eq_right hf]
    simp only [zero_mul, mul_zero]
  by_cases hm : MemValid x d Y d₀ u v r B sg (toEdge c₀ St fl)
  swap
  · rw [memEdgeCoef, ite_eq_right hm, ite_eq_right hm]
    simp only [zero_mul, mul_zero, Complex.ofReal_zero, sum_const_zero]
  by_cases hnd' : (Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl)).Nodup
  swap
  · rw [ite_eq_right hnd', ite_eq_right hnd']
    simp only [zero_mul, mul_zero, Complex.ofReal_zero, sum_const_zero]
  -- all restrictions hold: apply the induction hypothesis after the edge
  have hS' : Consistent sg.2.1.1 sg.2.2.1 (Bn + batchBirths g.2) := by
    rw [show sg.2.2.1 = ghostMem s.2.2.1 g from chainGhostOut_mem hv]
    exact consistent_ghostMem hS (ghostOK_of_valid hv hnd)
  have hg : EdgeGood (s := sg) hc₀ (Bn + batchBirths g.2) fl := edgeGood_of_valid hc₀ hm hnd'
  have hf' : FreeValid x d Y d₀ u v r B sg (toEdge₀ c₀) := (freeValid_congr rfl rfl _).2 hf
  have hev : EdgeValid x d Y d₀ u v r B sg (toEdge c₀ St fl) :=
    (edgeValid_iff sg (toEdge c₀ St fl)).2 ⟨(freeValid_toEdge sg c₀ St fl).2 hf', hm⟩
  have hc' := consistent_edgeMem hdisj hc₀ hf' hS' St hg
  set out := chainEdgeOut x d Y d₀ u v r B sg (toEdge c₀ St fl) with hout
  have hout₁ : out.1.1 = c₀.2.1.1 := by
    simp only [hout, chainEdgeOut, dite_eq_left hev]; rfl
  have hout₂ : out.2.1.1 = edgeTgt s (toEdge c₀ St fl) := by
    simp only [hout, chainEdgeOut, dite_eq_left hev]; rfl
  have hout₃ : out.2.2.1 = edgeMem sg (toEdge c₀ St fl) := by
    simp only [hout, chainEdgeOut, dite_eq_left hev]
  have hfo : chainFree out = freeOut s (toEdge₀ c₀) :=
    (chainFree_chainEdgeOut sg c₀ St fl hev).trans (freeOut_congr rfl rfl _)
  have hih := ih out (Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl)) (by
    rw [hout₂, hout₃]
    exact hc')
  rw [hfo, hout₁, hout₂, hout₃] at hih
  rw [memEdgeCoef, ite_eq_left hm, ite_eq_left hm, ite_eq_left hnd', ite_eq_left hnd',
    ite_eq_left hnd]
  -- collect the pending factors into the visit weight
  have hvw := visitWeight_eq q N t s g
  have hρ : (pendingWeight q : ℂ) ^ pendingHits x d c₀.2.1.1 (edgeMem sg (toEdge c₀ St fl)) *
      distinctFold q A₀ Y d₀ u v r B N n (t + 1) out
        (Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl)) =
      ∑ π ∈ pathsFrom π₁ (t + 1) (freeOut s (toEdge₀ c₀)),
        weightFrom A₀ π (t + 1) * endInd π *
          (lifeProd q N π (t + 1) (edgeTgt s (toEdge c₀ St fl)) (edgeMem sg (toEdge c₀ St fl))
            (Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl)) : ℂ) := hih
  calc (pendingWeight q : ℂ) ^ pendingHits x d s.1.1 s.2.2.1 *
        (chainGhostCoef q x d Y d₀ u v r B N t s g *
          (freeCoef A₀ s (toEdge₀ c₀) *
            ((pendingWeight q ^ pendingHits x d sg.1.1 sg.2.2.1 *
              pendingWeight q ^ pendingHits x d c₀.2.1.1 (edgeMem sg (toEdge c₀ St fl)) *
              ∏ i, memLabelWeight q x d N sg.2.2.1 (toEdge c₀ St fl) i : ℝ) : ℂ)) * 1 *
          distinctFold q A₀ Y d₀ u v r B N n (t + 1) out
            (Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl)))
      = freeCoef A₀ s (toEdge₀ c₀) * ((visitWeight q N t s g : ℂ) *
          ((∏ i, memLabelWeight q x d N sg.2.2.1 (toEdge c₀ St fl) i : ℝ) : ℂ)) *
          ((pendingWeight q : ℂ) ^ pendingHits x d c₀.2.1.1 (edgeMem sg (toEdge c₀ St fl)) *
            distinctFold q A₀ Y d₀ u v r B N n (t + 1) out
              (Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl))) := by
        rw [hvw, show sg.1.1 = s.1.1 from rfl]
        push_cast
        ring
    _ = _ := by
        rw [hρ, mul_assoc, mul_sum]
        refine congrArg (freeCoef A₀ s (toEdge₀ c₀) * ·) (sum_congr rfl fun π _ => ?_)
        push_cast
        ring

open scoped Classical in
/-- **An earlier visit**: the induction step of the running sum. -/
theorem distinctFold_succ_eq (hq : 0 < q)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) (hB : (bandPrimes x d).card ≤ B) {N n t : ℕ}
    (htn : t + 1 + n = N)
    (ih : ∀ (π₁ : Fin (N + 1) → FreeState x d Y d₀ u v r) (s : ChainState x d Y d₀ u v r B)
      (Bn : Multiset ℕ), Consistent s.2.1.1 s.2.2.1 Bn →
        (pendingWeight q : ℂ) ^ pendingHits x d s.1.1 s.2.2.1 *
            distinctFold q A₀ Y d₀ u v r B N n (t + 1) s Bn =
          ∑ π ∈ pathsFrom π₁ (t + 1) (chainFree s),
            weightFrom A₀ π (t + 1) * endInd π * (lifeProd q N π (t + 1) s.2.1.1 s.2.2.1 Bn : ℂ))
    (π₀ : Fin (N + 1) → FreeState x d Y d₀ u v r) (s : ChainState x d Y d₀ u v r B)
    {Bn : Multiset ℕ} (hS : Consistent s.2.1.1 s.2.2.1 Bn) :
    (pendingWeight q : ℂ) ^ pendingHits x d s.1.1 s.2.2.1 *
        distinctFold q A₀ Y d₀ u v r B N (n + 1) t s Bn =
      ∑ π ∈ pathsFrom π₀ t (chainFree s),
        weightFrom A₀ π t * endInd π * (lifeProd q N π t s.2.1.1 s.2.2.1 Bn : ℂ) := by
  have htN : t < N := by omega
  set π₁ : Fin (N + 1) → FreeState x d Y d₀ u v r :=
    fun j => if (j : ℕ) = t then chainFree s else π₀ j with hπ₁
  -- step: expand the first ghost and edge, and apply the induction hypothesis termwise
  rw [distinctFold, mul_sum]
  simp only [mul_sum, sum_edgeChoices]
  rw [sum_congr rfl fun g _ => sum_congr rfl fun c₀ hc₀ => sum_congr rfl fun St _ =>
    sum_congr rfl fun fl _ => distinctFold_term_eq q A₀ hdisj π₁ (ih π₁) s hS g hc₀ St fl]
  rw [sum_comm]
  -- step: for each free choice, the ghost and edge steps
  have hstep : ∀ c₀ ∈ freeChoices x d Y d₀ u v r,
      ∑ g ∈ multBox B ×ˢ multBox B, ∑ St : Finset (Fin K), ∑ fl : Fin K → Bool,
        freeCoef A₀ s (toEdge₀ c₀) *
          ∑ π ∈ pathsFrom π₁ (t + 1) (freeOut s (toEdge₀ c₀)),
            weightFrom A₀ π (t + 1) * endInd π *
              ((visitWeight q N t s g * (if (Bn + batchBirths g.2).Nodup then 1 else 0) *
                ((if MemValid x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s g)
                    (toEdge c₀ St fl) then ∏ i, memLabelWeight q x d N
                      (chainGhostOut x d Y d₀ u v r B s g).2.2.1 (toEdge c₀ St fl) i else 0) *
                  (if (Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl)).Nodup then 1 else 0) *
                  lifeProd q N π (t + 1) (edgeTgt s (toEdge c₀ St fl))
                    (edgeMem (chainGhostOut x d Y d₀ u v r B s g) (toEdge c₀ St fl))
                    (Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl))) : ℝ) : ℂ) =
        freeCoef A₀ s (toEdge₀ c₀) *
          ∑ π ∈ pathsFrom π₁ (t + 1) (freeOut s (toEdge₀ c₀)),
            weightFrom A₀ π (t + 1) * endInd π * (lifeProd q N π t s.2.1.1 s.2.2.1 Bn : ℂ) := by
    intro c₀ hc₀
    by_cases hf : FreeValid x d Y d₀ u v r B s (toEdge₀ c₀)
    swap
    · simp only [freeCoef, ite_eq_right hf, zero_mul, sum_const_zero]
    simp only [← mul_sum]
    congr 1
    -- move the path sum outside
    rw [sum_comm_four]
    refine sum_congr rfl fun π hπ => ?_
    -- the path passes through `s` at `t` and through the free output at `t + 1`
    have hπt : π ⟨t, by omega⟩ = chainFree s := by
      have := (mem_pathsFrom.1 hπ).1 ⟨t, by omega⟩ (by simp)
      rw [this]
      simp [π₁]
    have hπt₁ : π ⟨t + 1, by omega⟩ = freeOut s (toEdge₀ c₀) := (mem_pathsFrom.1 hπ).2 _ rfl
    have hline : ∀ p, pathLines p π t = lineOf p s.1.1 := fun p => by
      rw [pathLines_val p π ⟨t, by omega⟩, hπt]
      rfl
    have hact : ∀ p, t ∈ activeSet p π ↔ ∃ i h, s.2.1.1 i h = p := fun p => by
      rw [mem_activeSet p π ⟨t, by omega⟩, hπt]
      rfl
    have hline' : ∀ p, pathLines p π (t + 1) = lineOf p c₀.2.1.1 := fun p => by
      rw [pathLines_val p π ⟨t + 1, by omega⟩, hπt₁, freeOut_val hf]
      rfl
    have hact' : ∀ p, t + 1 ∈ activeSet p π ↔ ∃ i h, edgeTgt s (toEdge₀ c₀) i h = p := fun p => by
      rw [mem_activeSet p π ⟨t + 1, by omega⟩, hπt₁, freeOut_val hf]
    simp only [← mul_sum]
    congr 1
    rw [← ghost_stage q hq hdisj hV hB htN.le π s hS hline hact]
    push_cast
    refine sum_congr rfl fun g _ => ?_
    simp only [← mul_sum]
    -- the edge step after an admissible ghost choice with distinct births
    by_cases hv : GhostValid (HitsAt x d s.1.1) B s.2.2.1 g
    swap
    · simp [visitWeight, hv]
    by_cases hnd : (Bn + batchBirths g.2).Nodup
    swap
    · simp [hnd]
    set sg := chainGhostOut x d Y d₀ u v r B s g
    have hmem : sg.2.2.1 = ghostMem s.2.2.1 g := chainGhostOut_mem hv
    have hS' : Consistent sg.2.1.1 sg.2.2.1 (Bn + batchBirths g.2) := by
      rw [hmem]
      exact consistent_ghostMem hS (ghostOK_of_valid hv hnd)
    have hf' : FreeValid x d Y d₀ u v r B sg (toEdge₀ c₀) := (freeValid_congr rfl rfl _).2 hf
    have he := edge_stage q hdisj hc₀ hf' hS' hB htN π hline hline' hact'
    have htgt : ∀ St fl, edgeTgt sg (toEdge c₀ St fl) = edgeTgt s (toEdge c₀ St fl) :=
      fun _ _ => rfl
    simp only [htgt] at he
    rw [show sg.2.1.1 = s.2.1.1 from rfl] at he
    rw [← hmem]
    have hsum : ∑ St : Finset (Fin K), ∑ fl : Fin K → Bool,
        (((if MemValid x d Y d₀ u v r B sg (toEdge c₀ St fl) then
            ∏ i, memLabelWeight q x d N sg.2.2.1 (toEdge c₀ St fl) i else 0) *
          (if (Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl)).Nodup then 1 else 0) *
          lifeProd q N π (t + 1) (edgeTgt s (toEdge c₀ St fl)) (edgeMem sg (toEdge c₀ St fl))
            (Bn + batchBirths g.2 + freshBirths (toEdge c₀ St fl)) : ℝ) : ℂ) =
        (postProd q N π t s.2.1.1 sg.2.2.1 (Bn + batchBirths g.2) : ℂ) := by
      rw [← he]
      push_cast
      rfl
    rw [← hsum]
    push_cast
    rfl
  rw [sum_congr rfl hstep]
  -- step: recombine the free choices into `A⁰` and the paths through `s`
  rw [← sum_edgeOp_mul_eq A₀ s fun b => ∑ π ∈ pathsFrom π₁ (t + 1) b,
    weightFrom A₀ π (t + 1) * endInd π * (lifeProd q N π t s.2.1.1 s.2.2.1 Bn : ℂ)]
  have hsplit := sum_pathsFrom_succ A₀ π₀ htN (chainFree s)
    fun π => endInd π * (lifeProd q N π t s.2.1.1 s.2.2.1 Bn : ℂ)
  simp only [← mul_assoc] at hsplit
  rw [hsplit]

/-! ### The induction -/

/-- **The memory identity along the path**: from a consistent state at the visit `t`, the
running distinct-birth history sum, with the incoming pending factor, is the line-free path
sum through the state weighted by the lifespan product. -/
theorem distinctFold_eq_path (hq : 0 < q)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) (hB : (bandPrimes x d).card ≤ B) {N : ℕ}
    (hbig : ∀ p ∈ bandPrimes x d, N < p) :
    ∀ n t : ℕ, t + n = N → ∀ (π₀ : Fin (N + 1) → FreeState x d Y d₀ u v r)
      (s : ChainState x d Y d₀ u v r B) (Bn : Multiset ℕ), Consistent s.2.1.1 s.2.2.1 Bn →
        (pendingWeight q : ℂ) ^ pendingHits x d s.1.1 s.2.2.1 *
            distinctFold q A₀ Y d₀ u v r B N n t s Bn =
          ∑ π ∈ pathsFrom π₀ t (chainFree s),
            weightFrom A₀ π t * endInd π * (lifeProd q N π t s.2.1.1 s.2.2.1 Bn : ℂ) := by
  intro n
  induction n with
  | zero =>
    intro t htn π₀ s Bn hS
    obtain rfl : t = N := by omega
    exact distinctFold_zero_eq q A₀ hq hdisj hV hB hbig π₀ s hS
  | succ n ih =>
    intro t htn π₀ s Bn hS
    exact distinctFold_succ_eq q A₀ hq hdisj hV hB (by omega)
      (fun π₁ s' Bn' hS' => ih (t + 1) (by omega) π₁ s' Bn' hS') π₀ s hS

end Induction

end Erdos408.OneSided
