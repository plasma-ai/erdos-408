import Erdos821.S2.GhostTasks

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Matrix
open Filter InnerProductSpace
open scoped ComplexOrder
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

private theorem spectral_holder {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsPositive) (R : ℕ) (hR : 1 ≤ R) (x : E) :
    (inner ℂ x (T x)).re ≤
      (‖x‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) *
        (inner ℂ x ((T ^ R) x)).re ^ (R : ℝ)⁻¹ := by
  classical
  let hS := hT.isSymmetric
  let n := Module.finrank ℂ E
  let b := hS.eigenvectorBasis rfl
  let c : Fin n → ℂ := fun i => (b.repr x).ofLp i
  let lam : Fin n → ℝ := hS.eigenvalues rfl
  have hlam (i : Fin n) : 0 ≤ lam i := by
    exact hT.nonneg_eigenvalues rfl i
  have hcoord (k : ℕ) (i : Fin n) :
      (b.repr ((T ^ k) x)).ofLp i = ((lam i : ℝ) ^ k : ℂ) * c i := by
    induction k with
    | zero => simp [c]
    | succ k ih =>
      rw [pow_succ' T k, Module.End.mul_apply]
      calc
        (b.repr (T ((T ^ k) x))).ofLp i =
            (lam i : ℂ) * (b.repr ((T ^ k) x)).ofLp i := by
          simpa [b, lam] using hS.eigenvectorBasis_apply_self_apply rfl ((T ^ k) x) i
        _ = _ := by rw [ih]; simp only [pow_succ]; ring
  have hquad (k : ℕ) :
      (inner ℂ x ((T ^ k) x)).re =
        ∑ i : Fin n, lam i ^ k * ‖c i‖ ^ 2 := by
    have hterm (i : Fin n) :
        star (c i) * (((lam i : ℝ) : ℂ) ^ k * c i) =
          ((lam i ^ k * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
      calc
        _ = (((lam i : ℝ) : ℂ) ^ k) * (star (c i) * c i) := by ring
        _ = (((lam i : ℝ) : ℂ) ^ k) * ((‖c i‖ : ℂ) ^ 2) :=
          congrArg (fun z : ℂ => (((lam i : ℝ) : ℂ) ^ k) * z) (Complex.conj_mul' (c i))
        _ = ((lam i ^ k * ‖c i‖ ^ 2 : ℝ) : ℂ) := by norm_cast
    have hinner : inner ℂ x ((T ^ k) x) =
        ∑ i : Fin n, ((lam i ^ k * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
      rw [← b.repr.inner_map_map x ((T ^ k) x), PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [RCLike.inner_apply', hcoord]
      simpa [c] using hterm i
    have hre := congrArg Complex.re hinner
    simpa only [Complex.re_sum, Complex.ofReal_re] using hre
  have hnorm : ‖x‖ ^ 2 = ∑ i : Fin n, ‖c i‖ ^ 2 := by
    calc
      ‖x‖ ^ 2 = ‖b.repr x‖ ^ 2 := by rw [← b.repr.norm_map]
      _ = ∑ i, ‖(b.repr x).ofLp i‖ ^ 2 := EuclideanSpace.norm_sq_eq (b.repr x)
      _ = _ := by rfl
  have hw (i : Fin n) : 0 ≤ ‖c i‖ ^ 2 := sq_nonneg _
  have := Real.inner_le_weight_mul_Lp_of_nonneg Finset.univ (p := (R : ℝ)) (by exact_mod_cast hR)
      (fun i => ‖c i‖ ^ 2) lam hw hlam
  calc
    (inner ℂ x (T x)).re = ∑ i : Fin n, ‖c i‖ ^ 2 * lam i := by
      simpa [mul_comm] using hquad 1
    _ ≤ (∑ i : Fin n, ‖c i‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) *
        (∑ i : Fin n, ‖c i‖ ^ 2 * lam i ^ R) ^ (R : ℝ)⁻¹ := by
      simpa [mul_comm] using this
    _ = (‖x‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) *
        (inner ℂ x ((T ^ R) x)).re ^ (R : ℝ)⁻¹ := by rw [hnorm, hquad R]; simp [mul_comm]

private theorem pattern_D_le_sup_pow {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) (u : P.Aux J) :
    ν.D a u ≤ P.allPrimes.sup id ^ (J * P.count) := by
  classical
  let S := P.allPrimes.sup id
  have hval (g : P.Group) (i : Fin J) :
      (if i ∈ ν.changed g then (u g i).val else (a g (ν.slot i)).val) ≤ S := by
    split_ifs with hi
    · change (u g i).val ≤ P.allPrimes.sup id
      exact Finset.le_sup (s := P.allPrimes) (f := id) (b := (u g i).val)
        (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, (u g i).property⟩)
    · change (a g (ν.slot i)).val ≤ P.allPrimes.sup id
      exact Finset.le_sup (s := P.allPrimes) (f := id) (b := (a g (ν.slot i)).val)
        (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, (a g (ν.slot i)).property⟩)
  calc
    ν.D a u = ∏ z ∈ (Finset.univ : Finset P.Group).product (Finset.univ : Finset (Fin J)),
        (if z.2 ∈ ν.changed z.1 then (u z.1 z.2).val else (a z.1 (ν.slot z.2)).val) := by
      simpa [Pattern.D] using
        (Finset.prod_product' (Finset.univ : Finset P.Group) (Finset.univ : Finset (Fin J))
          (fun g i => if i ∈ ν.changed g then (u g i).val else (a g (ν.slot i)).val)).symm
    _ ≤ S ^ ((Finset.univ : Finset P.Group).product (Finset.univ : Finset (Fin J))).card :=
      Finset.prod_le_pow_card _ _ S (by
        intro z hz
        exact hval z.1 z.2)
    _ = S ^ (J * P.count) := by simp [Finset.card_product, mul_comm]


private theorem displacement_mem_neighbors {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (a b : A.State) (ν : Pattern P J F.ell m)
    (labels : P.Labels (J + F.ell)) (u : P.Aux J)
    (htrans : b.1 = a.1 + A.k * (ν.D labels u : ℤ)) :
    b ∈ A.neighbors a.1 := by
  have hD := pattern_D_le_sup_pow ν labels u
  have hn : Int.natAbs (A.k * (ν.D labels u : ℤ)) ≤
      A.k.natAbs * (P.allPrimes.sup id) ^ (J * P.count) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ hD
  have hcast : (Int.natAbs (A.k * (ν.D labels u : ℤ)) : ℤ) ≤ (A.stepBound : ℤ) := by
    exact_mod_cast hn
  have habs : |A.k * (ν.D labels u : ℤ)| ≤ (A.stepBound : ℤ) := by
    simpa only [Int.natCast_natAbs] using hcast
  have hdisp := abs_le.mp habs
  have hmem : b.1 ∈ Finset.Icc (a.1 - A.stepBound) (a.1 + A.stepBound) := by
    simp only [Finset.mem_Icc]
    omega
  simp [Model.neighbors, hmem]

private theorem physicalKernel_false_zero_of_not_neighbor {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (z z' : A.State)
    (hz : z' ∉ A.neighbors z.1) : A.physicalKernel false z z' = 0 := by
  classical
  have hraw (π τ : P.Permutations (J + F.ell)) :
      A.physicalRaw false (z.1, P.act π z.2) (z'.1, P.act τ z'.2) = 0 := by
    unfold Model.physicalRaw
    by_cases hphys : P.physical (J + F.ell) z.1 (P.act π z.2) ∧
        P.physical (J + F.ell) z'.1 (P.act τ z'.2)
    · simp only [if_pos hphys]
      apply Finset.sum_eq_zero
      intro v hv
      apply Finset.sum_eq_zero
      intro u hu
      by_cases hc : (A.pattern v).compatible (P.act π z.2) (P.act τ z'.2) ∧
          (A.pattern v).ban (P.act π z.2) (P.act τ z'.2) u ∧
          z'.1 = z.1 + A.k * ((A.pattern v).D (P.act π z.2) u : ℤ)
      · have hmem := displacement_mem_neighbors A z z' (A.pattern v) (P.act π z.2) u hc.2.2
        exact (hz hmem).elim
      · simp [hc]
    · simp [hphys]
  simp [Model.physicalKernel, hraw]


private theorem neighbors_symm {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (z z' : A.State) :
    z' ∈ A.neighbors z.1 ↔ z ∈ A.neighbors z'.1 := by
  simp [Model.neighbors]
  omega

private theorem adjointKernel_zero_of_not_neighbor {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (z z' : A.State)
    (hz : z' ∉ A.neighbors z.1) : A.adjointKernel z z' = 0 := by
  have hrev : z ∉ A.neighbors z'.1 := by
    intro h
    exact hz ((neighbors_symm A z' z).mp h)
  simp [Model.adjointKernel, physicalKernel_false_zero_of_not_neighbor A z' z hrev]

private theorem kernelComp_eq_sum_neighbors {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (a b : A.State) :
    kernelComp (A.physicalKernel false) A.adjointKernel a b =
      ∑ z ∈ A.neighbors a.1,
        A.physicalKernel false a z * A.adjointKernel z b := by
  unfold kernelComp
  apply tsum_eq_sum
  intro z hz
  simp [physicalKernel_false_zero_of_not_neighbor A a z hz]

def twoNeighbors {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (a : A.State) : Finset A.State :=
  (A.neighbors a.1).biUnion fun z => A.neighbors z.1

private theorem kernelComp_zero_of_not_twoNeighbors {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (a b : A.State)
    (h : b ∉ twoNeighbors A a) : kernelComp (A.physicalKernel false)
      A.adjointKernel a b = 0 := by
  rw [kernelComp_eq_sum_neighbors]
  apply Finset.sum_eq_zero
  intro z hz
  have hbz : b ∉ A.neighbors z.1 := by
    intro hbz
    exact h (Finset.mem_biUnion.mpr ⟨z, hz, hbz⟩)
  simp [adjointKernel_zero_of_not_neighbor A z b hbz]


private theorem kernelComp_eq_twoNeighbors {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (f : A.State → A.State → ℂ) (a b : A.State) :
    kernelComp (kernelComp (A.physicalKernel false) A.adjointKernel) f a b =
      ∑ z ∈ twoNeighbors A a,
        kernelComp (A.physicalKernel false) A.adjointKernel a z * f z b := by
  change (∑' z, kernelComp (A.physicalKernel false) A.adjointKernel a z * f z b) = _
  apply tsum_eq_sum
  intro z hz
  simp [kernelComp_zero_of_not_twoNeighbors A a z hz]

def twoReach {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (s : Finset A.State) : ℕ → Finset A.State
  | 0 => s
  | n + 1 => twoReach A s n ∪ (twoReach A s n).biUnion (twoNeighbors A)

private theorem twoReach_mono {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (s : Finset A.State) (n : ℕ) :
    twoReach A s n ⊆ twoReach A s (n + 1) := by
  intro z hz
  simp only [twoReach, Finset.mem_union]
  exact Or.inl hz

private theorem twoReach_subset {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (s : Finset A.State) {n r : ℕ} (h : n ≤ r) :
    twoReach A s n ⊆ twoReach A s r := by
  induction r with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    exact Finset.Subset.rfl
  | succ r ih =>
    by_cases hn : n ≤ r
    · exact (ih hn).trans (twoReach_mono A s r)
    · have : n = r + 1 := by omega
      subst n
      exact Finset.Subset.rfl

private theorem twoHop_mem_reach_succ {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (s : Finset A.State) (n : ℕ)
    {a z : A.State} (ha : a ∈ twoReach A s n) (hz : z ∈ twoNeighbors A a) :
    z ∈ twoReach A s (n + 1) := by
  simp only [twoReach, Finset.mem_union]
  exact Or.inr (Finset.mem_biUnion.mpr ⟨a, ha, hz⟩)

private def finiteKernelPower {α : Type*} (B : α → α → ℂ) (S : Finset α) :
    ℕ → α → α → ℂ
  | 0, a, b => if a = b then 1 else 0
  | n + 1, a, b => ∑ z ∈ S, B a z * finiteKernelPower B S n z b

private theorem kernelPower_eq_finite {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (s : Finset A.State) (R n k : ℕ)
    (hk : k + n ≤ R) (a b : A.State)
    (ha : a ∈ twoReach A s k) :
    kernelPower (kernelComp (A.physicalKernel false) A.adjointKernel) n a b =
      finiteKernelPower (kernelComp (A.physicalKernel false) A.adjointKernel)
        (twoReach A s R) n a b := by
  induction n generalizing k a with
  | zero => rfl
  | succ n ih =>
    have hsub : twoNeighbors A a ⊆ twoReach A s R := by
      intro z hz
      exact (twoReach_subset A s (by omega))
        (twoHop_mem_reach_succ A s k ha hz)
    rw [kernelPower, kernelComp_eq_twoNeighbors]
    calc
      (∑ z ∈ twoNeighbors A a,
          kernelComp (A.physicalKernel false) A.adjointKernel a z *
            kernelPower (kernelComp (A.physicalKernel false) A.adjointKernel) n z b) =
          ∑ z ∈ twoNeighbors A a,
            kernelComp (A.physicalKernel false) A.adjointKernel a z *
              finiteKernelPower (kernelComp (A.physicalKernel false) A.adjointKernel)
                (twoReach A s R) n z b := by
            apply Finset.sum_congr rfl
            intro z hz
            have hz' := twoHop_mem_reach_succ A s k ha hz
            have hih := ih (k + 1) (by omega) z hz'
            rw [hih]
      _ = ∑ z ∈ twoReach A s R,
          kernelComp (A.physicalKernel false) A.adjointKernel a z *
            finiteKernelPower (kernelComp (A.physicalKernel false) A.adjointKernel)
              (twoReach A s R) n z b := by
            refine Finset.sum_subset hsub ?_
            intro z hz hnot
            simp [kernelComp_zero_of_not_twoNeighbors A a z hnot]


private def finiteKernelMatrix {α : Type*} [DecidableEq α] (S : Finset α)
    (B : α → α → ℂ) : Matrix {x : α // x ∈ S} {x : α // x ∈ S} ℂ :=
  fun i j => B i.1 j.1

private theorem matrix_pow_apply_eq_finiteKernelPower {α : Type*} [DecidableEq α]
    (S : Finset α) [Fintype {x : α // x ∈ S}] [DecidableEq {x : α // x ∈ S}]
    (B : α → α → ℂ) :
    ∀ (n : ℕ) (i j : {x : α // x ∈ S}),
      (finiteKernelMatrix S B ^ n) i j = finiteKernelPower B S n i.1 j.1 := by
  classical
  intro n
  induction n with
  | zero =>
    intro i j
    by_cases hij : i = j
    · subst j
      simp [finiteKernelMatrix, finiteKernelPower]
    · have hv : i.1 ≠ j.1 := by
        intro h
        apply hij
        exact Subtype.ext h
      simp [finiteKernelMatrix, finiteKernelPower, Matrix.one_apply, hij, hv]
  | succ n ih =>
    intro i j
    rw [pow_succ' (finiteKernelMatrix S B) n, Matrix.mul_apply]
    simp_rw [ih]
    change (∑ z : {x : α // x ∈ S}, B i.1 z.1 *
      finiteKernelPower B S n z.1 j.1) =
      ∑ z ∈ S, B i.1 z * finiteKernelPower B S n z j.1
    symm
    exact Finset.sum_subtype S (by intro x; simp) _


def neighborUnion {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (S : Finset A.State) : Finset A.State :=
  S.biUnion fun z => A.neighbors z.1

private theorem neighbors_subset_neighborUnion {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (S : Finset A.State)
    {a : A.State} (ha : a ∈ S) : A.neighbors a.1 ⊆ neighborUnion A S := by
  intro z hz
  exact Finset.mem_biUnion.mpr ⟨a, ha, hz⟩

private def finitePhysicalMatrix {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (S T : Finset A.State) :
    Matrix {z // z ∈ S} {z // z ∈ T} ℂ :=
  fun x y => A.physicalKernel false x.1 y.1

private theorem kernelComp_eq_matrix_gram {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (S T : Finset A.State)
    (hST : ∀ a ∈ S, A.neighbors a.1 ⊆ T)
    (a b : A.State) (ha : a ∈ S) (hb : b ∈ S) :
    kernelComp (A.physicalKernel false) A.adjointKernel a b =
      ((finitePhysicalMatrix A S T) * Matrix.conjTranspose (finitePhysicalMatrix A S T))
        ⟨a, ha⟩ ⟨b, hb⟩ := by
  classical
  let C : Matrix {z // z ∈ S} {z // z ∈ T} ℂ := finitePhysicalMatrix A S T
  calc
    kernelComp (A.physicalKernel false) A.adjointKernel a b =
        ∑ z ∈ A.neighbors a.1,
          A.physicalKernel false a z * A.adjointKernel z b :=
      kernelComp_eq_sum_neighbors A a b
    _ = ∑ z ∈ T, A.physicalKernel false a z * star (A.physicalKernel false b z) := by
      refine Finset.sum_subset (hST a ha) ?_
      intro z hz hnot
      simp [physicalKernel_false_zero_of_not_neighbor A a z hnot]
    _ = ∑ z : {z // z ∈ T},
          A.physicalKernel false a z.1 * star (A.physicalKernel false b z.1) :=
      Finset.sum_subtype T (by intro z; simp) _
    _ = _ := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, C, finitePhysicalMatrix]



private theorem gram_toEuclideanLin {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (C : Matrix ι κ ℂ) :
    (C * Matrix.conjTranspose C).toEuclideanLin =
      C.toEuclideanLin.comp C.toEuclideanLin.adjoint := by
  calc
    (C * Matrix.conjTranspose C).toEuclideanLin =
        C.toEuclideanLin.comp (Matrix.conjTranspose C).toEuclideanLin := by
      simpa [Matrix.toEuclideanLin] using
        (Matrix.toLpLin_mul_same (p := 2) (q := 2) (r := 2) C (Matrix.conjTranspose C))
    _ = C.toEuclideanLin.comp C.toEuclideanLin.adjoint := by
      rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]


private theorem matrix_toEuclideanLin_mul {m n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] (A : Matrix m n ℂ) (B : Matrix n o ℂ) :
    (A * B).toEuclideanLin = A.toEuclideanLin.comp B.toEuclideanLin := by
  simpa [Matrix.toEuclideanLin] using
    (Matrix.toLpLin_mul_same (p := 2) (q := 2) (r := 2) A B)

private theorem matrix_pow_toEuclideanLin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) (R : ℕ) :
    (G ^ R).toEuclideanLin = (G.toEuclideanLin) ^ R := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_pow]

private theorem posSemidef_quadratic_le_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) (hG : G.PosSemidef) (x : EuclideanSpace ℂ ι) :
    (inner ℂ x (G.toEuclideanLin x)).re ≤ G.trace.re * ‖x‖ ^ 2 := by
  classical
  let T := G.toEuclideanLin
  have hT : T.IsPositive := by
    change G.toEuclideanLin.IsPositive
    exact (Matrix.isPositive_toEuclideanLin_iff (A := G)).2 hG
  let hS := hT.isSymmetric
  let n := Module.finrank ℂ (EuclideanSpace ℂ ι)
  let b := hS.eigenvectorBasis rfl
  let c : Fin n → ℂ := fun i => (b.repr x).ofLp i
  let lam : Fin n → ℝ := hS.eigenvalues rfl
  have hlam (i : Fin n) : 0 ≤ lam i := hT.nonneg_eigenvalues rfl i
  have hcoord (k : ℕ) (i : Fin n) :
      (b.repr ((T ^ k) x)).ofLp i = ((lam i : ℝ) ^ k : ℂ) * c i := by
    induction k with
    | zero => simp [c]
    | succ k ih =>
      rw [pow_succ' T k, Module.End.mul_apply]
      calc
        (b.repr (T ((T ^ k) x))).ofLp i =
            (lam i : ℂ) * (b.repr ((T ^ k) x)).ofLp i := by
          simpa [b, lam] using hS.eigenvectorBasis_apply_self_apply rfl ((T ^ k) x) i
        _ = _ := by rw [ih]; simp only [pow_succ]; ring
  have hquad (k : ℕ) :
      (inner ℂ x ((T ^ k) x)).re =
        ∑ i : Fin n, lam i ^ k * ‖c i‖ ^ 2 := by
    have hterm (i : Fin n) :
        star (c i) * (((lam i : ℝ) : ℂ) ^ k * c i) =
          ((lam i ^ k * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
      calc
        _ = (((lam i : ℝ) : ℂ) ^ k) * (star (c i) * c i) := by ring
        _ = (((lam i : ℝ) : ℂ) ^ k) * ((‖c i‖ : ℂ) ^ 2) :=
          congrArg (fun z : ℂ => (((lam i : ℝ) : ℂ) ^ k) * z) (Complex.conj_mul' (c i))
        _ = ((lam i ^ k * ‖c i‖ ^ 2 : ℝ) : ℂ) := by norm_cast
    have hinner : inner ℂ x ((T ^ k) x) =
        ∑ i : Fin n, ((lam i ^ k * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
      rw [← b.repr.inner_map_map x ((T ^ k) x), PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [RCLike.inner_apply', hcoord]
      simpa [c] using hterm i
    have hre := congrArg Complex.re hinner
    simpa only [Complex.re_sum, Complex.ofReal_re] using hre
  have hnorm : ‖x‖ ^ 2 = ∑ i : Fin n, ‖c i‖ ^ 2 := by
    calc
      ‖x‖ ^ 2 = ‖b.repr x‖ ^ 2 := by rw [← b.repr.norm_map]
      _ = ∑ i, ‖(b.repr x).ofLp i‖ ^ 2 := EuclideanSpace.norm_sq_eq (b.repr x)
      _ = _ := by rfl
  have htrace : (T.trace ℂ (EuclideanSpace ℂ ι)).re = ∑ i : Fin n, lam i := by
    exact hS.re_trace_eq_sum_eigenvalues rfl
  have htraceG : (T.trace ℂ (EuclideanSpace ℂ ι)) = G.trace := by
    change (Matrix.toEuclideanLin G).trace ℂ (EuclideanSpace ℂ ι) = G.trace
    simpa only [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      (Matrix.trace_toLin_eq G (EuclideanSpace.basisFun ι ℂ).toBasis)
  have hLamSum : (∑ i : Fin n, lam i) = G.trace.re := by
    rw [← htraceG]
    exact htrace.symm
  have hLamBound (i : Fin n) : lam i ≤ ∑ j : Fin n, lam j :=
    Finset.single_le_sum (fun j hj => hlam j) (Finset.mem_univ i)
  calc
    (inner ℂ x (T x)).re = ∑ i : Fin n, lam i * ‖c i‖ ^ 2 := by
      simpa using hquad 1
    _ ≤ ∑ i : Fin n, (∑ j : Fin n, lam j) * ‖c i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hLamBound i) (sq_nonneg _)
    _ = (∑ j : Fin n, lam j) * (∑ i : Fin n, ‖c i‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ = G.trace.re * ‖x‖ ^ 2 := by rw [hLamSum, hnorm]

private theorem finite_matrix_pairing_sq_bound {S T I : Type*}
    [Fintype S] [Fintype T] [Fintype I]
    [DecidableEq S] [DecidableEq T] [DecidableEq I]
    (C : Matrix S T ℂ) (U : Matrix S I ℂ) (R : ℕ) (hR : 1 ≤ R)
    (c : EuclideanSpace ℂ I) (g : EuclideanSpace ℂ T) :
    ‖inner ℂ (U.toEuclideanLin c) (C.toEuclideanLin g)‖ ^ 2 ≤
      ‖g‖ ^ 2 * (‖U.toEuclideanLin c‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) *
        (((Matrix.conjTranspose U * ((C * Matrix.conjTranspose C) ^ R) * U).trace.re * ‖c‖ ^ 2) ^ (R : ℝ)⁻¹) := by
  classical
  let G : Matrix S S ℂ := C * Matrix.conjTranspose C
  let B : EuclideanSpace ℂ S →ₗ[ℂ] EuclideanSpace ℂ S := G.toEuclideanLin
  let H : Matrix I I ℂ := Matrix.conjTranspose U * (G ^ R) * U
  let Um : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ S := U.toEuclideanLin
  let Cm : EuclideanSpace ℂ T →ₗ[ℂ] EuclideanSpace ℂ S := C.toEuclideanLin
  have hBdecomp : B = Cm.comp Cm.adjoint := by
    exact gram_toEuclideanLin C
  have hB : B.IsPositive := by
    rw [hBdecomp]
    exact LinearMap.isPositive_self_comp_adjoint Cm
  have hGpos : G.PosSemidef := by
    exact Matrix.posSemidef_self_mul_conjTranspose C
  have hGpow : (G ^ R).PosSemidef := hGpos.pow R
  have hHpos : H.PosSemidef := by
    exact hGpow.conjTranspose_mul_mul_same U
  have hBpow : (G ^ R).toEuclideanLin = B ^ R := by
    dsimp [B]
    exact matrix_pow_toEuclideanLin G R
  have hHmap : H.toEuclideanLin = Um.adjoint.comp ((B ^ R).comp Um) := by
    dsimp [H, Um, B]
    rw [matrix_toEuclideanLin_mul, matrix_toEuclideanLin_mul,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, matrix_pow_toEuclideanLin]
    simp only [LinearMap.comp_assoc]
  let F : EuclideanSpace ℂ S := Um c
  have hQ : inner ℂ c (H.toEuclideanLin c) = inner ℂ F ((B ^ R) F) := by
    rw [hHmap]
    simpa [F, LinearMap.comp_apply] using
      (LinearMap.adjoint_inner_right Um c ((B ^ R) (Um c)))
  have hQle : (inner ℂ F ((B ^ R) F)).re ≤ H.trace.re * ‖c‖ ^ 2 := by
    rw [← hQ]
    exact posSemidef_quadratic_le_trace H hHpos c
  have hQnonneg : 0 ≤ (inner ℂ F ((B ^ R) F)).re := by
    rw [← hQ]
    have hdot := hHpos.dotProduct_mulVec_nonneg (fun i => c i)
    have hEq : (inner ℂ c (H.toEuclideanLin c)).re =
        (star (fun i => c i) ⬝ᵥ (H *ᵥ fun i => c i)).re := by
      simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, PiLp.inner_apply,
        Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    exact hEq.symm ▸ (Complex.nonneg_iff.mp hdot).1
  have hdnonneg : 0 ≤ H.trace.re * ‖c‖ ^ 2 := by
    apply mul_nonneg
    · exact (Complex.nonneg_iff.mp hHpos.trace_nonneg).1
    · positivity
  have hpow : (inner ℂ F ((B ^ R) F)).re ^ (R : ℝ)⁻¹ ≤
      (H.trace.re * ‖c‖ ^ 2) ^ (R : ℝ)⁻¹ :=
    Real.rpow_le_rpow hQnonneg hQle (by positivity)
  have hspec := spectral_holder B hB R hR F
  have hnormAdj : ‖Cm.adjoint F‖ ^ 2 = (inner ℂ F (B F)).re := by
    calc
      ‖Cm.adjoint F‖ ^ 2 =
          (inner ℂ (Cm.adjoint F) (Cm.adjoint F)).re := by
            simpa [pow_two] using (inner_self_eq_norm_mul_norm (Cm.adjoint F)).symm
      _ = (inner ℂ F (Cm (Cm.adjoint F))).re :=
        congrArg Complex.re (LinearMap.adjoint_inner_left Cm (Cm.adjoint F) F)
      _ = (inner ℂ F (B F)).re := by
        simp [hBdecomp, LinearMap.comp_apply]
  have hCS : ‖inner ℂ F (Cm g)‖ ≤ ‖Cm.adjoint F‖ * ‖g‖ := by
    calc
      _ = ‖inner ℂ (Cm.adjoint F) g‖ := by
        rw [← LinearMap.adjoint_inner_left Cm g F]
      _ ≤ _ := norm_inner_le_norm _ _
  have hCSsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hCS
  have hspec' : ‖Cm.adjoint F‖ ^ 2 ≤
      (‖F‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) *
        (H.trace.re * ‖c‖ ^ 2) ^ (R : ℝ)⁻¹ := by
    calc
      _ = (inner ℂ F (B F)).re := hnormAdj
      _ ≤ (‖F‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) *
          (inner ℂ F ((B ^ R) F)).re ^ (R : ℝ)⁻¹ := hspec
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  calc
    ‖inner ℂ F (Cm g)‖ ^ 2 ≤ (‖Cm.adjoint F‖ * ‖g‖) ^ 2 := hCSsq
    _ = ‖g‖ ^ 2 * ‖Cm.adjoint F‖ ^ 2 := by ring
    _ ≤ _ := by
      simpa [F, Um, H, G, mul_assoc] using
        mul_le_mul_of_nonneg_left hspec' (sq_nonneg (‖g‖))


private theorem finite_matrix_pairing_bound {S T I : Type*}
    [Fintype S] [Fintype T] [Fintype I]
    [DecidableEq S] [DecidableEq T] [DecidableEq I]
    (C : Matrix S T ℂ) (U : Matrix S I ℂ) (R : ℕ) (hR : 1 ≤ R)
    (c : EuclideanSpace ℂ I) (g : EuclideanSpace ℂ T)
    (hd : 0 ≤ (Matrix.conjTranspose U * ((C * Matrix.conjTranspose C) ^ R) * U).trace.re * ‖c‖ ^ 2) :
    ‖inner ℂ (U.toEuclideanLin c) (C.toEuclideanLin g)‖ ≤
      ‖g‖ * Real.sqrt ((‖U.toEuclideanLin c‖ ^ 2) ^ (1 - (R : ℝ)⁻¹)) *
        Real.sqrt (((Matrix.conjTranspose U * ((C * Matrix.conjTranspose C) ^ R) * U).trace.re *
          ‖c‖ ^ 2) ^ (R : ℝ)⁻¹) := by
  have hs := finite_matrix_pairing_sq_bound C U R hR c g
  let d : ℝ := (Matrix.conjTranspose U * ((C * Matrix.conjTranspose C) ^ R) * U).trace.re *
      ‖c‖ ^ 2
  let A : ℝ := ‖g‖ * Real.sqrt ((‖U.toEuclideanLin c‖ ^ 2) ^ (1 - (R : ℝ)⁻¹)) *
    Real.sqrt (d ^ (R : ℝ)⁻¹)
  have hd' : 0 ≤ d := hd
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hA2 : A ^ 2 = ‖g‖ ^ 2 * (‖U.toEuclideanLin c‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) *
      (d ^ (R : ℝ)⁻¹) := by
    dsimp [A]
    rw [mul_pow, mul_pow, Real.sq_sqrt (Real.rpow_nonneg (sq_nonneg _) _),
      Real.sq_sqrt (Real.rpow_nonneg hd' _)]
  have hsq : ‖inner ℂ (U.toEuclideanLin c) (C.toEuclideanLin g)‖ ^ 2 ≤ A ^ 2 := by
    calc
      _ ≤ ‖g‖ ^ 2 * (‖U.toEuclideanLin c‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) * d ^ (R : ℝ)⁻¹ := hs
      _ = A ^ 2 := hA2.symm
  exact (sq_le_sq₀ (norm_nonneg _) hA).mp hsq


private theorem physical_act_iff {P : PrimeGroups} {M : ℕ}
    (π : P.Permutations M) (n : ℤ) (a : P.Labels M) :
    P.physical M n (P.act π a) ↔ P.physical M n a := by
  constructor
  · intro h g
    obtain ⟨hi, hd⟩ := h g
    constructor
    · intro i j hij
      have h' : (P.act π a) g ((π g).symm i) = (P.act π a) g ((π g).symm j) := by
        simpa [PrimeGroups.act] using hij
      have heq := hi h'
      simpa using congrArg (π g) heq
    · intro i
      simpa [PrimeGroups.act] using hd ((π g).symm i)
  · intro h g
    obtain ⟨hi, hd⟩ := h g
    constructor
    · intro i j hij
      have h' : a g (π g i) = a g (π g j) := by
        simpa [PrimeGroups.act] using hij
      exact (π g).injective (hi h')
    · intro i
      simpa [PrimeGroups.act] using hd (π g i)

private theorem physicalKernel_false_zero_of_invalid_left {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (z z' : A.State)
    (hz : ¬ P.physical (J + F.ell) z.1 z.2) :
    A.physicalKernel false z z' = 0 := by
  classical
  unfold Model.physicalKernel
  have hraw (π τ : P.Permutations (J + F.ell)) :
      A.physicalRaw false (z.1, P.act π z.2) (z'.1, P.act τ z'.2) = 0 := by
    unfold Model.physicalRaw
    have hp : ¬ P.physical (J + F.ell) z.1 (P.act π z.2) := by
      intro hp
      exact hz ((physical_act_iff π z.1 z.2).mp hp)
    simp [hp]
  simp [hraw]

private theorem physicalKernel_false_zero_of_invalid_right {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (z z' : A.State)
    (hz : ¬ P.physical (J + F.ell) z'.1 z'.2) :
    A.physicalKernel false z z' = 0 := by
  classical
  unfold Model.physicalKernel
  have hraw (π τ : P.Permutations (J + F.ell)) :
      A.physicalRaw false (z.1, P.act π z.2) (z'.1, P.act τ z'.2) = 0 := by
    unfold Model.physicalRaw
    have hp : ¬ P.physical (J + F.ell) z'.1 (P.act τ z'.2) := by
      intro hp
      exact hz ((physical_act_iff τ z'.1 z'.2).mp hp)
    simp [hp]
  simp [hraw]

private theorem markMass_nonneg_of_admissible {F : FixedData} {P : PrimeGroups} {x : ℝ}
    (hP : P.Admissible F x) (M : ℕ) : 0 ≤ P.markMass M := by
  rcases hP with ⟨_, _, _, _, hV, _⟩
  unfold PrimeGroups.markMass
  apply Finset.prod_nonneg
  intro g hg
  have hv : 0 < P.V g := lt_of_lt_of_le F.vMin_pos (hV g).1
  positivity

private theorem stateMass_nonneg_of_admissible {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) {x : ℝ} (hP : P.Admissible F x) (z : A.State) :
    0 ≤ A.stateMass z := by
  unfold Model.stateMass
  split_ifs
  · exact markMass_nonneg_of_admissible hP (J + F.ell)
  · exact le_rfl

private theorem stateMass_eq_markMass_of_physical {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (n : ℤ) (a : A.Labels)
    (h : P.physical (J + F.ell) n a) :
    A.stateMass (n, a) = P.markMass (J + F.ell) := by
  simp [Model.stateMass, h]

private theorem stateMass_eq_zero_of_not_physical {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (n : ℤ) (a : A.Labels)
    (h : ¬ P.physical (J + F.ell) n a) : A.stateMass (n, a) = 0 := by
  simp [Model.stateMass, h]

private theorem kernelComp_zero_of_left_zero {α : Type*} [Countable α]
    (K H : α → α → ℂ) (a b : α) (h : ∀ z, K a z = 0) :
    kernelComp K H a b = 0 := by
  unfold kernelComp
  have hzero : (fun z => K a z * H z b) = 0 := by
    funext z
    simp [h z]
  rw [hzero]
  exact tsum_zero

private theorem kernelComp_zero_of_right_zero {α : Type*} [Countable α]
    (K H : α → α → ℂ) (a b : α) (h : ∀ z, H z b = 0) :
    kernelComp K H a b = 0 := by
  unfold kernelComp
  have hzero : (fun z => K a z * H z b) = 0 := by
    funext z
    simp [h z]
  rw [hzero]
  exact tsum_zero

private theorem physicalKernelComp_zero_of_invalid_left {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (a b : A.State)
    (ha : ¬ P.physical (J + F.ell) a.1 a.2) :
    kernelComp (A.physicalKernel false) A.adjointKernel a b = 0 := by
  apply kernelComp_zero_of_left_zero
  intro z
  exact physicalKernel_false_zero_of_invalid_left A a z ha

private theorem physicalKernelComp_zero_of_invalid_right {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (a b : A.State)
    (hb : ¬ P.physical (J + F.ell) b.1 b.2) :
    kernelComp (A.physicalKernel false) A.adjointKernel a b = 0 := by
  apply kernelComp_zero_of_right_zero
  intro z
  change star (A.physicalKernel false b z) = 0
  rw [physicalKernel_false_zero_of_invalid_left A b z hb]
  simp

private theorem kernelComp_invalid_left {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (H : A.State → A.State → ℂ)
    (a b : A.State) (ha : ¬ P.physical (J + F.ell) a.1 a.2) :
    kernelComp (kernelComp (A.physicalKernel false) A.adjointKernel) H a b = 0 := by
  apply kernelComp_zero_of_left_zero
  intro z
  exact physicalKernelComp_zero_of_invalid_left A a z ha

private theorem kernelComp_invalid_right {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (K : A.State → A.State → ℂ)
    (a b : A.State) (hb : ∀ z, K z b = 0) :
    kernelComp (kernelComp (A.physicalKernel false) A.adjointKernel) K a b = 0 := by
  apply kernelComp_zero_of_right_zero
  exact hb

private theorem kernelPower_one {α : Type*} [Countable α] (K : α → α → ℂ)
    (a b : α) : kernelPower K 1 a b = K a b := by
  rw [kernelPower]
  unfold kernelComp
  change (∑' z, K a z * (if z = b then (1 : ℂ) else 0)) = K a b
  rw [tsum_eq_single b]
  · simp
  · intro z hz
    simp [hz]

private theorem kernelPower_zero_of_invalid_left {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (R : ℕ) (hR : 1 ≤ R) (a b : A.State)
    (ha : ¬ P.physical (J + F.ell) a.1 a.2) :
    kernelPower (kernelComp (A.physicalKernel false) A.adjointKernel) R a b = 0 := by
  cases R with
  | zero => omega
  | succ R =>
    cases R with
    | zero => rw [kernelPower_one]; exact physicalKernelComp_zero_of_invalid_left A a b ha
    | succ R =>
      rw [kernelPower]
      exact kernelComp_invalid_left A (kernelPower _ (R + 1)) a b ha

private theorem kernelPower_zero_of_invalid_right {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (R : ℕ) (hR : 1 ≤ R) (a b : A.State)
    (hb : ¬ P.physical (J + F.ell) b.1 b.2) :
    kernelPower (kernelComp (A.physicalKernel false) A.adjointKernel) R a b = 0 := by
  cases R with
  | zero => omega
  | succ R =>
    cases R with
    | zero =>
      rw [kernelPower_one]
      exact physicalKernelComp_zero_of_invalid_right A a b hb
    | succ R =>
      rw [kernelPower]
      apply kernelComp_invalid_right A
      intro z
      exact kernelPower_zero_of_invalid_right A (R + 1) (by omega) z b hb


private theorem kernelPower_eq_matrix_entry {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (base : Finset A.State) (R : ℕ)
    {a b : A.State} (ha : a ∈ base) (hb : b ∈ base) :
    kernelPower (kernelComp (A.physicalKernel false) A.adjointKernel) R a b =
      ((finitePhysicalMatrix A (twoReach A base R) (neighborUnion A (twoReach A base R)) *
        Matrix.conjTranspose (finitePhysicalMatrix A (twoReach A base R)
          (neighborUnion A (twoReach A base R)))) ^ R)
        ⟨a, (twoReach_subset A base (Nat.zero_le R) (by simpa [twoReach] using ha))⟩
        ⟨b, (twoReach_subset A base (Nat.zero_le R) (by simpa [twoReach] using hb))⟩ := by
  classical
  let S := twoReach A base R
  let T := neighborUnion A S
  let C := finitePhysicalMatrix A S T
  let D : A.State → A.State → ℂ := kernelComp (A.physicalKernel false) A.adjointKernel
  let G : Matrix {z // z ∈ S} {z // z ∈ S} ℂ := fun x y => D x.1 y.1
  have haS : a ∈ S := twoReach_subset A base (Nat.zero_le R) (by simpa [twoReach] using ha)
  have hbS : b ∈ S := twoReach_subset A base (Nat.zero_le R) (by simpa [twoReach] using hb)
  have hST : ∀ x ∈ S, A.neighbors x.1 ⊆ T := fun x hx => neighbors_subset_neighborUnion A S hx
  have hG : G = C * Matrix.conjTranspose C := by
    ext x y
    simpa [G, C, D] using kernelComp_eq_matrix_gram A S T hST x.1 y.1 x.2 y.2
  have hfin := kernelPower_eq_finite A base R R 0 (by omega) a b (by simpa [twoReach] using ha)
  have hmatrix := matrix_pow_apply_eq_finiteKernelPower S D R
    ⟨a, haS⟩ ⟨b, hbS⟩
  have hM : finiteKernelMatrix S D = G := by
    ext x y
    rfl
  calc
    kernelPower D R a b = finiteKernelPower D S R a b := hfin
    _ = (finiteKernelMatrix S D ^ R) ⟨a, haS⟩ ⟨b, hbS⟩ := hmatrix.symm
    _ = (G ^ R) ⟨a, haS⟩ ⟨b, hbS⟩ := by rw [hM]
    _ = ((C * Matrix.conjTranspose C) ^ R) ⟨a, haS⟩ ⟨b, hbS⟩ := by rw [hG]

private def blockStates {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (I : Finset ℤ) : Finset A.State := I.product Finset.univ

private theorem sum_blockStates {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (I : Finset ℤ) {R : Type*} [AddCommMonoid R]
    (f : A.State → R) :
    (∑ z ∈ blockStates A I, f z) = ∑ n ∈ I, ∑ a : A.Labels, f (n, a) := by
  classical
  simpa [blockStates] using
    (Finset.sum_product I (Finset.univ : Finset A.Labels) f)

private def rootMatrix {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (S : Finset A.State) (I : Finset ℤ) :
    Matrix {z // z ∈ S} {n // n ∈ I} ℂ :=
  fun z n => if z.1.1 = n.1 then (Real.sqrt (A.stateMass z.1) : ℂ) else 0

private theorem sum_subtype_states_at_time {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (I : Finset ℤ) (S : Finset A.State)
    (hbase : blockStates A I ⊆ S) (n : ℤ) (hn : n ∈ I)
    (f : A.State → ℂ) :
    (∑ z : {z // z ∈ S}, if z.1.1 = n then f z.1 else 0) =
      ∑ a : A.Labels, f (n, a) := by
  classical
  let e : A.Labels → A.State := fun a => (n, a)
  have hfilter : S.filter (fun z : A.State => z.1 = n) = Finset.univ.image e := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_filter.mp hz with ⟨hzS, hzn⟩
      rcases z with ⟨z, a⟩
      simp only at hzn
      subst z
      apply Finset.mem_image.mpr
      exact ⟨a, Finset.mem_univ _, rfl⟩
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨a, -, hza⟩
      subst z
      change (n, a) ∈ S.filter (fun z : A.State => z.1 = n)
      apply Finset.mem_filter.mpr
      constructor
      · exact hbase (by simp [blockStates, hn])
      · rfl
  have hsubtype :
      (∑ z : {z // z ∈ S}, if z.1.1 = n then f z.1 else 0) =
        ∑ z ∈ S, if z.1 = n then f z else 0 := by
    symm
    exact Finset.sum_subtype S (by intro z; simp)
      (fun z => if z.1 = n then f z else 0)
  calc
    _ = ∑ z ∈ S, if z.1 = n then f z else 0 := hsubtype
    _ = ∑ z ∈ S.filter (fun z : A.State => z.1 = n), f z := by
      rw [Finset.sum_filter]
    _ = ∑ z ∈ Finset.univ.image e, f z := by rw [hfilter]
    _ = ∑ a : A.Labels, f (n, a) := by
      rw [Finset.sum_image (by
        intro a ha b hb hab
        injection hab)]

private theorem rootMatrix_column_pairing {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (I : Finset ℤ) (S : Finset A.State)
    (hbase : blockStates A I ⊆ S) (n : ℤ) (hn : n ∈ I)
    (f : {z // z ∈ S} → ℂ) :
    (∑ z : {z // z ∈ S},
      star (rootMatrix A S I z ⟨n, hn⟩) * f z) =
      ∑ a : A.Labels,
        (Real.sqrt (A.stateMass (n, a)) : ℂ) *
          f ⟨(n, a), hbase (by simp [blockStates, hn])⟩ := by
  classical
  have hroot (a : A.Labels) : (n, a) ∈ S := hbase (by simp [blockStates, hn])
  let r (a : A.Labels) : {z // z ∈ S} := ⟨(n, a), hroot a⟩
  have hstar (z : {z // z ∈ S}) :
      star (rootMatrix A S I z ⟨n, hn⟩) =
        if z.1.1 = n then (Real.sqrt (A.stateMass z.1) : ℂ) else 0 := by
    by_cases hz : z.1.1 = n <;> simp [rootMatrix, hz]
  let q (z : A.State) : ℂ := (Real.sqrt (A.stateMass z) : ℂ) * f (r z.2)
  calc
    _ = ∑ z : {z // z ∈ S}, if z.1.1 = n then q z.1 else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases htime : z.1.1 = n
      · have hrow : z = r z.1.2 := by
          apply Subtype.ext
          rcases z with ⟨⟨k, a⟩, hz⟩
          simp only at htime
          subst k
          rfl
        rw [hstar]
        simp only [if_pos htime]
        rw [hrow]
      · rw [hstar]
        simp [htime]
    _ = ∑ a : A.Labels, q (n, a) :=
      sum_subtype_states_at_time A I S hbase n hn q
    _ = _ := by rfl

private theorem rootMatrix_quadratic_expansion {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (I : Finset ℤ) (S : Finset A.State)
    (hbase : blockStates A I ⊆ S) (M : Matrix {z // z ∈ S} {z // z ∈ S} ℂ)
    (n : ℤ) (hn : n ∈ I) :
    ((Matrix.conjTranspose (rootMatrix A S I) * M * rootMatrix A S I)
      ⟨n, hn⟩ ⟨n, hn⟩) =
      ∑ a : A.Labels, ∑ b : A.Labels,
        (Real.sqrt (A.stateMass (n, a)) : ℂ) *
          M ⟨(n, a), hbase (by simp [blockStates, hn])⟩
            ⟨(n, b), hbase (by simp [blockStates, hn])⟩ *
          (Real.sqrt (A.stateMass (n, b)) : ℂ) := by
  classical
  let U := rootMatrix A S I
  let r (a : A.Labels) : {z // z ∈ S} := ⟨(n, a), hbase (by simp [blockStates, hn])⟩
  let q (j : {z // z ∈ S}) (z : A.State) : ℂ :=
    (Real.sqrt (A.stateMass (n, z.2)) : ℂ) * M (r z.2) j
  have hstarU (i : {z // z ∈ S}) :
      star (U i ⟨n, hn⟩) =
        if i.1.1 = n then (Real.sqrt (A.stateMass i.1) : ℂ) else 0 := by
    by_cases hit : i.1.1 = n <;> simp [U, rootMatrix, hit]
  have hinner (j : {z // z ∈ S}) :
      (∑ i : {z // z ∈ S}, star (U i ⟨n, hn⟩) * M i j) =
        ∑ a : A.Labels, (Real.sqrt (A.stateMass (n, a)) : ℂ) * M (r a) j := by
    calc
      _ = ∑ i : {z // z ∈ S}, if i.1.1 = n then q j i.1 else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hit : i.1.1 = n
            · have hrow : i = r i.1.2 := by
                apply Subtype.ext
                rcases i with ⟨⟨k, a⟩, hi⟩
                simp only at hit
                subst k
                rfl
              rw [hstarU]
              simp only [if_pos hit]
              rw [hrow]
            · rw [hstarU]
              simp [hit]
      _ = ∑ a : A.Labels, q j (n, a) :=
        sum_subtype_states_at_time A I S hbase n hn (q j)
      _ = _ := by rfl
  haveI : DecidableEq {z // z ∈ S} := Classical.decEq _
  let x (j : {z // z ∈ S}) : ℂ :=
    ∑ a : A.Labels, (Real.sqrt (A.stateMass (n, a)) : ℂ) * M (r a) j
  have hUrow (j : {z // z ∈ S}) :
      U j ⟨n, hn⟩ =
        if j.1.1 = n then (Real.sqrt (A.stateMass j.1) : ℂ) else 0 := by
    rfl
  calc
    ((Matrix.conjTranspose U * M * U) ⟨n, hn⟩ ⟨n, hn⟩) =
        ∑ j : {z // z ∈ S}, x j * U j ⟨n, hn⟩ := by
          change (∑ j : {z // z ∈ S},
            (∑ i : {z // z ∈ S}, star (U i ⟨n, hn⟩) * M i j) * U j ⟨n, hn⟩) = _
          apply Finset.sum_congr rfl
          intro j hj
          rw [hinner j]
    _ = ∑ j : {z // z ∈ S},
        if j.1.1 = n then x j * (Real.sqrt (A.stateMass j.1) : ℂ) else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases htime : j.1.1 = n
          · rw [hUrow]
            simp only [if_pos htime]
          · rw [hUrow]
            simp [htime]
    _ = ∑ b : A.Labels,
        (∑ a : A.Labels, (Real.sqrt (A.stateMass (n, a)) : ℂ) *
          M (r a) (r b)) * (Real.sqrt (A.stateMass (n, b)) : ℂ) := by
          let v (z : A.State) : ℂ :=
            x ⟨(n, z.2), hbase (by simp [blockStates, hn])⟩ *
              (Real.sqrt (A.stateMass (n, z.2)) : ℂ)
          calc
            _ = ∑ j : {z // z ∈ S}, if j.1.1 = n then v j.1 else 0 := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases htime : j.1.1 = n
              · have hrow : j = r j.1.2 := by
                  apply Subtype.ext
                  rcases j with ⟨⟨k, a⟩, hj⟩
                  simp only at htime
                  subst k
                  rfl
                rw [hrow]
              · simp [htime]
            _ = ∑ b : A.Labels, v (n, b) :=
              sum_subtype_states_at_time A I S hbase n hn v
            _ = _ := by rfl
    _ = ∑ a : A.Labels, ∑ b : A.Labels,
        (Real.sqrt (A.stateMass (n, a)) : ℂ) * M (r a) (r b) *
          (Real.sqrt (A.stateMass (n, b)) : ℂ) := by
          calc
            _ = ∑ b : A.Labels, ∑ a : A.Labels,
                ((Real.sqrt (A.stateMass (n, a)) : ℂ) * M (r a) (r b)) *
                  (Real.sqrt (A.stateMass (n, b)) : ℂ) := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  rw [Finset.sum_mul]
            _ = _ := Finset.sum_comm

private theorem euclidean_matrix_pairing_expansion {S T I : Type*}
    [Fintype S] [Fintype T] [Fintype I]
    [DecidableEq S] [DecidableEq T] [DecidableEq I]
    (C : Matrix S T ℂ) (U : Matrix S I ℂ)
    (c : EuclideanSpace ℂ I) (g : EuclideanSpace ℂ T) :
    inner ℂ (U.toEuclideanLin c) (C.toEuclideanLin g) =
      ∑ s : S, star (∑ i : I, U s i * c i) * (∑ t : T, C s t * g t) := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, PiLp.inner_apply,
    Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro s hs
  ring

private theorem root_weighted_power_eq {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) {x : ℝ} (hP : P.Admissible F x)
    (R : ℕ) (hR : 1 ≤ R) (n : ℤ) (a b : A.Labels) :
    (Real.sqrt (A.stateMass (n, a)) : ℂ) *
        kernelPower (kernelComp (A.physicalKernel false) A.adjointKernel) R
          (n, a) (n, b) *
        (Real.sqrt (A.stateMass (n, b)) : ℂ) =
      (A.stateMass (n, a) : ℂ) *
        kernelPower (kernelComp (A.physicalKernel false) A.adjointKernel) R
          (n, a) (n, b) := by
  by_cases ha : P.physical (J + F.ell) n a
  · by_cases hb : P.physical (J + F.ell) n b
    · rw [stateMass_eq_markMass_of_physical A n a ha,
        stateMass_eq_markMass_of_physical A n b hb]
      have hμ := markMass_nonneg_of_admissible hP (J + F.ell)
      have hsqrt : (Real.sqrt (P.markMass (J + F.ell)) : ℂ) ^ 2 =
          (P.markMass (J + F.ell) : ℂ) := by
        exact_mod_cast Real.sq_sqrt hμ
      calc
        _ = ((Real.sqrt (P.markMass (J + F.ell)) : ℂ) ^ 2) *
              kernelPower (kernelComp (A.physicalKernel false) A.adjointKernel) R
                (n, a) (n, b) := by ring
        _ = _ := by rw [hsqrt]
    · rw [stateMass_eq_markMass_of_physical A n a ha,
        stateMass_eq_zero_of_not_physical A n b hb]
      simp [kernelPower_zero_of_invalid_right A R hR (n, a) (n, b) hb]
  · rw [stateMass_eq_zero_of_not_physical A n a ha]
    simp [kernelPower_zero_of_invalid_left A R hR (n, a) (n, b) ha]

private theorem root_weighted_kernel_eq {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) {x : ℝ} (hP : P.Admissible F x)
    (n : ℤ) (a : A.Labels) (z : A.State) :
    (Real.sqrt (A.stateMass (n, a)) : ℂ) * A.physicalKernel false (n, a) z *
        (Real.sqrt (A.stateMass z) : ℂ) =
      (A.stateMass (n, a) : ℂ) * A.physicalKernel false (n, a) z := by
  by_cases ha : P.physical (J + F.ell) n a
  · by_cases hz : P.physical (J + F.ell) z.1 z.2
    · rw [stateMass_eq_markMass_of_physical A n a ha,
        stateMass_eq_markMass_of_physical A z.1 z.2 hz]
      have hμ := markMass_nonneg_of_admissible hP (J + F.ell)
      have hsqrt : (Real.sqrt (P.markMass (J + F.ell)) : ℂ) ^ 2 =
          (P.markMass (J + F.ell) : ℂ) := by
        exact_mod_cast Real.sq_sqrt hμ
      calc
        _ = ((Real.sqrt (P.markMass (J + F.ell)) : ℂ) ^ 2) *
              A.physicalKernel false (n, a) z := by ring
        _ = _ := by rw [hsqrt]
    · rw [stateMass_eq_markMass_of_physical A n a ha]
      rw [stateMass_eq_zero_of_not_physical A z.1 z.2 hz]
      simp [physicalKernel_false_zero_of_invalid_right A (n, a) z hz]
  · rw [stateMass_eq_zero_of_not_physical A n a ha]
    simp [physicalKernel_false_zero_of_invalid_left A (n, a) z ha]

private theorem sum_supported_kernel_restrict {α : Type*} [DecidableEq α]
    (T t : Finset α) (K : α → α → ℂ) (a : α) (w : α → ℂ)
    (hK : ∀ z, z ∉ T → K a z = 0) :
    (∑ z ∈ T, K a z * (if z ∈ t then w z else 0)) =
      ∑ z ∈ t, K a z * w z := by
  classical
  have hT : T.filter (fun z => z ∈ t) ⊆ t := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  calc
    (∑ z ∈ T, K a z * (if z ∈ t then w z else 0)) =
        ∑ z ∈ T.filter (fun z => z ∈ t), K a z * w z := by
          simp only [mul_ite, mul_zero]
          rw [Finset.sum_filter]
    _ = ∑ z ∈ t, K a z * w z := by
      refine Finset.sum_subset hT ?_
      intro z hz hnot
      have hzT : z ∉ T := by
        intro hzT
        exact hnot (Finset.mem_filter.mpr ⟨hzT, hz⟩)
      simp [hK z hzT]

private theorem block_pairing_eq_matrix {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) {x : ℝ} (hP : P.Admissible F x)
    (I : Finset ℤ) (t : Finset A.State) (f : ℤ → ℂ)
    (g : A.State → ℂ) (R : ℕ) :
    let B := blockStates A I
    let S := twoReach A B R
    let T := neighborUnion A S
    let C := finitePhysicalMatrix A S T
    let U := rootMatrix A S I
    let c : EuclideanSpace ℂ {n // n ∈ I} :=
      WithLp.toLp 2 (fun n : {n // n ∈ I} => f n.1)
    let v : EuclideanSpace ℂ {z // z ∈ T} :=
      WithLp.toLp 2 (fun z : {z // z ∈ T} =>
        if z.1 ∈ t then (Real.sqrt (A.stateMass z.1) : ℂ) * g z.1 else 0)
    (∑ n : {n // n ∈ I}, ∑ a : A.Labels, ∑ z ∈ t,
        (A.stateMass (n.1, a) : ℂ) * star (f n.1) *
          A.physicalKernel false (n.1, a) z * g z) =
      inner ℂ (U.toEuclideanLin c) (C.toEuclideanLin v) := by
  classical
  let B := blockStates A I
  let S := twoReach A B R
  let T := neighborUnion A S
  let C := finitePhysicalMatrix A S T
  let U := rootMatrix A S I
  let c : EuclideanSpace ℂ {n // n ∈ I} :=
    WithLp.toLp 2 (fun n : {n // n ∈ I} => f n.1)
  let v : EuclideanSpace ℂ {z // z ∈ T} :=
    WithLp.toLp 2 (fun z : {z // z ∈ T} =>
      if z.1 ∈ t then (Real.sqrt (A.stateMass z.1) : ℂ) * g z.1 else 0)
  let action (s : {z // z ∈ S}) : ℂ := ∑ z : {z // z ∈ T}, C s z * v z
  have hbase : B ⊆ S := by exact twoReach_subset A B (Nat.zero_le R)
  change blockStates A I ⊆ S at hbase
  have hroot (n : {n // n ∈ I}) (a : A.Labels) : (n.1, a) ∈ S :=
    hbase (by simp [blockStates, n.2])
  let r (n : {n // n ∈ I}) (a : A.Labels) : {z // z ∈ S} :=
    ⟨(n.1, a), hroot n a⟩
  have hsource (n : {n // n ∈ I}) :
      (∑ s : {z // z ∈ S}, star (U s n) * action s) =
        ∑ a : A.Labels, (Real.sqrt (A.stateMass (n.1, a)) : ℂ) * action (r n a) := by
    exact rootMatrix_column_pairing A I S hbase n.1 n.2 action
  have haction (n : {n // n ∈ I}) (a : A.Labels) :
      action (r n a) =
        ∑ z ∈ t, A.physicalKernel false (n.1, a) z *
          ((Real.sqrt (A.stateMass z) : ℂ) * g z) := by
    have hK (z : A.State) (hz : z ∉ T) : A.physicalKernel false (n.1, a) z = 0 := by
      apply physicalKernel_false_zero_of_not_neighbor A (n.1, a) z
      intro hnbr
      exact hz (neighbors_subset_neighborUnion A S
        (hroot n a) hnbr)
    calc
      action (r n a) =
          ∑ z ∈ T, A.physicalKernel false (n.1, a) z *
            (if z ∈ t then (Real.sqrt (A.stateMass z) : ℂ) * g z else 0) := by
              change (∑ z : {z // z ∈ T}, C (r n a) z * v z) = _
              simpa only [C, finitePhysicalMatrix, v, WithLp.ofLp_toLp] using
                (Finset.sum_subtype T (by intro z; simp)
                  (fun z => A.physicalKernel false (n.1, a) z *
                    (if z ∈ t then (Real.sqrt (A.stateMass z) : ℂ) * g z else 0))).symm
      _ = ∑ z ∈ t, A.physicalKernel false (n.1, a) z *
            ((Real.sqrt (A.stateMass z) : ℂ) * g z) :=
              sum_supported_kernel_restrict T t (A.physicalKernel false) (n.1, a)
                (fun z => (Real.sqrt (A.stateMass z) : ℂ) * g z) hK
  have hmatrix : inner ℂ (U.toEuclideanLin c) (C.toEuclideanLin v) =
      ∑ n : {n // n ∈ I}, ∑ s : {z // z ∈ S},
        star (c n) * star (U s n) * action s := by
    calc
      _ = ∑ s : {z // z ∈ S},
          star (∑ n : {n // n ∈ I}, U s n * c n) * action s := by
            exact euclidean_matrix_pairing_expansion C U c v
      _ = ∑ n : {n // n ∈ I}, ∑ s : {z // z ∈ S},
          star (c n) * star (U s n) * action s := by
            calc
              _ = ∑ s : {z // z ∈ S}, ∑ n : {n // n ∈ I},
                  star (c n) * star (U s n) * action s := by
                    apply Finset.sum_congr rfl
                    intro s hs
                    calc
                      _ = ∑ n : {n // n ∈ I}, star (U s n * c n) * action s := by
                        have hs : star (∑ n : {n // n ∈ I}, U s n * c n) =
                            ∑ n : {n // n ∈ I}, star (U s n * c n) := by
                          simpa using (star_sum (Finset.univ : Finset {n // n ∈ I})
                            (fun n => U s n * c n))
                        rw [hs]
                        simpa using (Finset.sum_mul (Finset.univ : Finset {n // n ∈ I})
                          (fun n => star (U s n * c n)) (action s))
                      _ = _ := by
                        apply Finset.sum_congr rfl
                        intro n hn
                        rw [star_mul]
              _ = _ := Finset.sum_comm
  have hmatrix' : inner ℂ (U.toEuclideanLin c) (C.toEuclideanLin v) =
      ∑ n : {n // n ∈ I}, ∑ a : A.Labels,
        star (c n) * ((Real.sqrt (A.stateMass (n.1, a)) : ℂ) * action (r n a)) := by
    calc
      _ = ∑ n : {n // n ∈ I}, ∑ s : {z // z ∈ S},
          star (U s n) * (star (c n) * action s) := by
            rw [hmatrix]
            apply Finset.sum_congr rfl
            intro n hn
            apply Finset.sum_congr rfl
            intro s hs
            ring
      _ = ∑ n : {n // n ∈ I}, ∑ a : A.Labels,
          (Real.sqrt (A.stateMass (n.1, a)) : ℂ) *
            (star (c n) * action (r n a)) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact rootMatrix_column_pairing A I S hbase n.1 n.2
          (fun s => star (c n) * action s)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro a ha
        ring
  have htarget (n : {n // n ∈ I}) (a : A.Labels) :
      (∑ z ∈ t, (A.stateMass (n.1, a) : ℂ) * star (f n.1) *
        A.physicalKernel false (n.1, a) z * g z) =
        star (f n.1) * ((Real.sqrt (A.stateMass (n.1, a)) : ℂ) *
          ∑ z ∈ t, A.physicalKernel false (n.1, a) z *
            ((Real.sqrt (A.stateMass z) : ℂ) * g z)) := by
    calc
      _ = ∑ z ∈ t, star (f n.1) *
          ((Real.sqrt (A.stateMass (n.1, a)) : ℂ) *
            (A.physicalKernel false (n.1, a) z *
              ((Real.sqrt (A.stateMass z) : ℂ) * g z))) := by
            apply Finset.sum_congr rfl
            intro z hz
            have hweight := root_weighted_kernel_eq A hP n.1 a z
            calc
              (A.stateMass (n.1, a) : ℂ) * star (f n.1) *
                  A.physicalKernel false (n.1, a) z * g z =
                star (f n.1) *
                  ((Real.sqrt (A.stateMass (n.1, a)) : ℂ) *
                    (A.physicalKernel false (n.1, a) z *
                      ((Real.sqrt (A.stateMass z) : ℂ) * g z))) := by
                        calc
                          _ = star (f n.1) *
                              ((A.stateMass (n.1, a) : ℂ) *
                                A.physicalKernel false (n.1, a) z * g z) := by ring
                          _ = star (f n.1) *
                              ((Real.sqrt (A.stateMass (n.1, a)) : ℂ) *
                                A.physicalKernel false (n.1, a) z *
                                (Real.sqrt (A.stateMass z) : ℂ) * g z) := by
                                  rw [← hweight]
                          _ = _ := by ring
              _ = _ := by ring
      _ = star (f n.1) *
          (∑ z ∈ t, (Real.sqrt (A.stateMass (n.1, a)) : ℂ) *
            (A.physicalKernel false (n.1, a) z *
              ((Real.sqrt (A.stateMass z) : ℂ) * g z))) :=
            (Finset.mul_sum t _ _).symm
      _ = _ := by
            congr 1
            exact (Finset.mul_sum t
              (fun z => A.physicalKernel false (n.1, a) z *
                ((Real.sqrt (A.stateMass z) : ℂ) * g z))
              (Real.sqrt (A.stateMass (n.1, a)) : ℂ)).symm
  calc
    (∑ n : {n // n ∈ I}, ∑ a : A.Labels, ∑ z ∈ t,
        (A.stateMass (n.1, a) : ℂ) * star (f n.1) *
          A.physicalKernel false (n.1, a) z * g z) =
      ∑ n : {n // n ∈ I}, ∑ a : A.Labels,
        star (c n) * ((Real.sqrt (A.stateMass (n.1, a)) : ℂ) * action (r n a)) := by
          apply Finset.sum_congr rfl
          intro n hn
          apply Finset.sum_congr rfl
          intro a ha
          rw [htarget n a, haction n a]
    _ = inner ℂ (U.toEuclideanLin c) (C.toEuclideanLin v) := hmatrix'.symm

private def chunkIndex (lo : ℤ) (B : ℕ) (n : ℤ) : ℤ := (n - lo) / (B : ℤ)

private theorem sum_by_chunk {α β γ : Type*} [DecidableEq β] [AddCommMonoid γ]
    (s : Finset α) (q : α → β) (f : α → γ) :
    (∑ a ∈ s, f a) = ∑ b ∈ s.image q, ∑ a ∈ s with q a = b, f a := by
  classical
  exact (Finset.sum_fiberwise_of_maps_to
    (fun a ha => Finset.mem_image_of_mem q ha) f).symm

private theorem dyad_card_bounds {X : ℝ} (hX : 1 ≤ X) :
    0 < ((dyad X).card : ℝ) ∧ ((dyad X).card : ℝ) ≤ 2 * X := by
  have hceilOrder : Int.ceil X ≤ Int.ceil (2 * X) := Int.ceil_mono (by linarith)
  have hcard : ((dyad X).card : ℝ) = (Int.ceil (2 * X) : ℝ) - Int.ceil X := by
    unfold dyad
    exact_mod_cast (Int.card_Ico_of_le (a := Int.ceil X) (b := Int.ceil (2 * X)) hceilOrder)
  have hceilXLower : X ≤ (Int.ceil X : ℝ) := Int.le_ceil X
  have hceil2Upper : (Int.ceil (2 * X) : ℝ) < 2 * X + 1 := Int.ceil_lt_add_one _
  have hcardPos : 0 < (dyad X).card := by
    apply Finset.card_pos.mpr
    refine ⟨Int.ceil X, ?_⟩
    simp only [dyad, Finset.mem_Ico]
    constructor
    · exact le_rfl
    · apply Int.lt_ceil.mpr
      have hXceilLt : (Int.ceil X : ℝ) < 2 * X := by
        calc
          (Int.ceil X : ℝ) < X + 1 := Int.ceil_lt_add_one _
          _ ≤ 2 * X := by linarith
      exact hXceilLt
  constructor
  · exact_mod_cast hcardPos
  · rw [hcard]
    linarith

private theorem allPrimes_sup_le_two_exp {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) {x : ℝ} (hP : P.Admissible F x)
    (hy : 1 ≤ L x) :
    ((P.allPrimes.sup id : ℕ) : ℝ) ≤ 2 * Real.exp ((L x) ^ F.d) := by
  classical
  let y := L x
  have hdPos : 0 < F.d := lt_trans F.a_pos (lt_trans F.ab (lt_trans F.bc F.cd))
  have hprimeUpper (p : ℕ) (hp : p ∈ P.allPrimes) :
      (p : ℝ) ≤ Real.exp (y ^ F.d) := by
    rcases Finset.mem_biUnion.mp hp with ⟨g, hg, hpGroup⟩
    have hprime := hP.2.2.2.2.2 g p hpGroup
    by_cases hbig : P.big g
    · simp [hbig] at hprime
      exact hprime.2
    · simp [hbig] at hprime
      calc
        (p : ℝ) ≤ Real.exp (y ^ F.b) := hprime.2
        _ ≤ Real.exp (y ^ F.d) := by
          apply Real.exp_le_exp.mpr
          exact Real.rpow_le_rpow_of_exponent_le hy (le_of_lt (lt_trans F.bc F.cd))
  let Z : ℝ := Real.exp (y ^ F.d)
  have hsup : P.allPrimes.sup id ≤ Nat.ceil Z := by
    apply Finset.sup_le_iff.mpr
    intro p hp
    have hcast : (p : ℝ) ≤ (Nat.ceil Z : ℝ) :=
      (hprimeUpper p hp).trans (Nat.le_ceil Z)
    exact_mod_cast hcast
  have hsupCast : ((P.allPrimes.sup id : ℕ) : ℝ) ≤ (Nat.ceil Z : ℝ) := by
    exact_mod_cast hsup
  have hceil : (Nat.ceil Z : ℝ) ≤ Z + 1 := by
    have hcf : (Nat.ceil Z : ℝ) ≤ (Nat.floor Z : ℝ) + 1 := by
      exact_mod_cast Nat.ceil_le_floor_add_one Z
    have hfloor : (Nat.floor Z : ℝ) ≤ Z := Nat.floor_le (le_of_lt (Real.exp_pos _))
    linarith
  have hZ : 1 ≤ Z := Real.one_le_exp_iff.mpr (Real.rpow_nonneg (by linarith [hy]) _)
  calc
    ((P.allPrimes.sup id : ℕ) : ℝ) ≤ (Nat.ceil Z : ℝ) := hsupCast
    _ ≤ Z + 1 := hceil
    _ ≤ 2 * Z := by linarith
    _ = 2 * Real.exp ((L x) ^ F.d) := by simp [Z, y]

private theorem model_stepBound_exp_bound {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) {x C₂ : ℝ}
    (hP : P.Admissible F x) (hy : 1 ≤ L x)
    (hkBound : |(A.k : ℝ)| ≤ (L x) ^ C₂) :
    (A.stepBound : ℝ) ≤
      Real.exp (C₂ * Real.log (L x) + (J : ℝ) *
        (2 * F.C₀ * Real.log (L x)) * (Real.log 2 + (L x) ^ F.d)) := by
  classical
  let y := L x
  let S := P.allPrimes.sup id
  let Q := 2 * Real.exp (y ^ F.d)
  have hS : (S : ℝ) ≤ Q := allPrimes_sup_le_two_exp A hP hy
  have hsmall : (P.smallGroups.card : ℝ) ≤ F.C₀ * Real.log y := by
    simpa [T, y] using hP.2.1
  have hbig : (P.bigGroups.card : ℝ) ≤ F.C₀ * Real.log y := by
    simpa [T, y] using hP.2.2.2.1
  have hcounts : P.smallGroups.card + P.bigGroups.card = P.count := by
    have hfilter :
        (Finset.univ.filter (fun g : P.Group => P.big g = false)) =
          Finset.univ.filter (fun g : P.Group => ¬ P.big g = true) := by
      ext g
      simp
    calc
      _ = (Finset.univ.filter (fun g : P.Group => ¬ P.big g = true)).card +
            (Finset.univ.filter (fun g : P.Group => P.big g = true)).card := by
        simp only [PrimeGroups.smallGroups, PrimeGroups.bigGroups, hfilter]
      _ = (Finset.univ : Finset P.Group).card := by
        rw [Nat.add_comm]
        exact Finset.card_filter_add_card_filter_not
          (p := fun g : P.Group => P.big g = true)
      _ = P.count := by simp [PrimeGroups.Group]
  have hcount : (P.count : ℝ) ≤ 2 * F.C₀ * Real.log y := by
    have hcast : (P.count : ℝ) =
        (P.smallGroups.card : ℝ) + (P.bigGroups.card : ℝ) := by exact_mod_cast hcounts.symm
    rw [hcast]
    linarith
  have hnatAbs : (A.k.natAbs : ℝ) = |(A.k : ℝ)| := by
    calc
      (A.k.natAbs : ℝ) = ((A.k.natAbs : ℤ) : ℝ) := by norm_num
      _ = ((|A.k| : ℤ) : ℝ) := by exact_mod_cast (Int.natCast_natAbs A.k)
      _ = |(A.k : ℝ)| := by norm_cast
  have hYpos : 0 < y := by linarith [hy]
  have hQpos : 0 < Q := by positivity
  have hlogQ : Real.log Q = Real.log 2 + y ^ F.d := by
    dsimp [Q]
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  let n : ℕ := J * P.count
  have hn : (n : ℝ) ≤ (J : ℝ) * (2 * F.C₀ * Real.log y) := by
    dsimp [n]
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hcount (by positivity)
  have hpow : (S : ℝ) ^ n ≤ Q ^ n := by
    gcongr
  have hpowEq : Q ^ n = Real.exp ((n : ℝ) * (Real.log 2 + y ^ F.d)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hQpos, hlogQ]
    congr 1
    ring
  have hpowExp : Real.exp ((n : ℝ) * (Real.log 2 + y ^ F.d)) ≤
      Real.exp ((J : ℝ) * (2 * F.C₀ * Real.log y) * (Real.log 2 + y ^ F.d)) := by
    apply Real.exp_le_exp.mpr
    have hlogQ0 : 0 ≤ Real.log 2 + y ^ F.d := by
      have hyPow : 0 ≤ y ^ F.d := Real.rpow_nonneg (le_of_lt hYpos) _
      exact add_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hyPow
    exact mul_le_mul_of_nonneg_right hn hlogQ0
  have hyRpow : y ^ C₂ = Real.exp (C₂ * Real.log y) := by
    rw [Real.rpow_def_of_pos hYpos]
    congr 1
    ring
  calc
    (A.stepBound : ℝ) = (A.k.natAbs : ℝ) * (S : ℝ) ^ n := by
      simp [Model.stepBound, S, n, Nat.cast_mul, Nat.cast_pow]
    _ ≤ y ^ C₂ * Q ^ n := by
      rw [hnatAbs]
      exact mul_le_mul hkBound hpow (by positivity) (by positivity)
    _ = Real.exp (C₂ * Real.log y) *
          Real.exp ((n : ℝ) * (Real.log 2 + y ^ F.d)) := by rw [hyRpow, hpowEq]
    _ ≤ Real.exp (C₂ * Real.log y) *
          Real.exp ((J : ℝ) * (2 * F.C₀ * Real.log y) * (Real.log 2 + y ^ F.d)) :=
        mul_le_mul_of_nonneg_left hpowExp (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]

private theorem blockLength_exp_bound {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) {x C₂ : ℝ}
    (hP : P.Admissible F x) (hy : 1 ≤ L x) (hC₂ : 0 < C₂)
    (hk : A.k ≠ 0) (hkBound : |(A.k : ℝ)| ≤ (L x) ^ C₂)
    (hlarge : 64 + 100 * C₂ + 600 * (J : ℝ) * F.C₀ ≤ (L x) ^ ((3 : ℝ) / 100)) :
    let R := Nat.ceil ((L x) ^ ((52 : ℝ) / 100))
    let B := 2 * ((2 * R + 1) * A.stepBound) + 1
    (B : ℝ) ≤ Real.exp ((L x) ^ ((51 : ℝ) / 100)) := by
  classical
  let y := L x
  let R : ℕ := Nat.ceil (y ^ ((52 : ℝ) / 100))
  let B : ℕ := 2 * ((2 * R + 1) * A.stepBound) + 1
  let H : ℝ := C₂ * Real.log y + (J : ℝ) *
    (2 * F.C₀ * Real.log y) * (Real.log 2 + y ^ F.d)
  let Q : ℝ := 10 * y ^ ((52 : ℝ) / 100) * Real.exp H
  have hypos : 0 < y := by linarith [hy]
  have hyPowOne : 1 ≤ y ^ ((52 : ℝ) / 100) := by
    calc
      1 = (1 : ℝ) ^ ((52 : ℝ) / 100) := by simp
      _ ≤ y ^ ((52 : ℝ) / 100) :=
        Real.rpow_le_rpow (by norm_num) hy (by norm_num)
  have hceil : (R : ℝ) ≤ y ^ ((52 : ℝ) / 100) + 1 := by
    have hcf : Nat.ceil (y ^ ((52 : ℝ) / 100)) ≤
        Nat.floor (y ^ ((52 : ℝ) / 100)) + 1 :=
      Nat.ceil_le_floor_add_one _
    have hfloor : (Nat.floor (y ^ ((52 : ℝ) / 100)) : ℝ) ≤
        y ^ ((52 : ℝ) / 100) := Nat.floor_le (by positivity)
    have hcast : (R : ℝ) ≤
        (Nat.floor (y ^ ((52 : ℝ) / 100)) : ℝ) + 1 := by exact_mod_cast hcf
    linarith
  have hRlen : 2 * (R : ℝ) + 1 ≤ 5 * y ^ ((52 : ℝ) / 100) := by
    linarith [hceil, hyPowOne]
  have hlogSmall : Real.log y ≤ 100 * y ^ ((1 : ℝ) / 100) := by
    have hlog := Real.log_le_rpow_div (le_of_lt hypos) (by norm_num : 0 < (1 : ℝ) / 100)
    calc
      Real.log y ≤ y ^ ((1 : ℝ) / 100) / ((1 : ℝ) / 100) := hlog
      _ = 100 * y ^ ((1 : ℝ) / 100) := by norm_num [div_eq_mul_inv] <;> ring
  have hlognonneg : 0 ≤ Real.log y := Real.log_nonneg hy
  have hy01_le48 : y ^ ((1 : ℝ) / 100) ≤ y ^ ((48 : ℝ) / 100) :=
    Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
  have hyd_le47 : y ^ F.d ≤ y ^ ((47 : ℝ) / 100) :=
    Real.rpow_le_rpow_of_exponent_le hy F.d_lt.le
  have hy48one : 1 ≤ y ^ ((48 : ℝ) / 100) := by
    calc
      1 = (1 : ℝ) ^ ((48 : ℝ) / 100) := by simp
      _ ≤ y ^ ((48 : ℝ) / 100) :=
        Real.rpow_le_rpow (by norm_num) hy (by norm_num)
  have hlogy48 : Real.log y ≤ 100 * y ^ ((48 : ℝ) / 100) :=
    hlogSmall.trans (mul_le_mul_of_nonneg_left hy01_le48 (by norm_num))
  have hlogD : Real.log y * y ^ F.d ≤ 100 * y ^ ((48 : ℝ) / 100) := by
    have hprod : y ^ ((1 : ℝ) / 100) * y ^ ((47 : ℝ) / 100) =
        y ^ ((48 : ℝ) / 100) := by
      rw [← Real.rpow_add hypos]
      congr 1
      norm_num
    calc
      Real.log y * y ^ F.d ≤
          (100 * y ^ ((1 : ℝ) / 100)) * y ^ ((47 : ℝ) / 100) :=
        mul_le_mul hlogSmall hyd_le47 (by positivity) (by positivity)
      _ = 100 * y ^ ((48 : ℝ) / 100) := by
        calc
          _ = 100 * (y ^ ((1 : ℝ) / 100) * y ^ ((47 : ℝ) / 100)) := by ring
          _ = _ := by rw [hprod]
  have hlog2 : 0 ≤ Real.log 2 ∧ Real.log 2 ≤ 2 :=
    ⟨Real.log_nonneg (by norm_num), Real.log_le_self (by norm_num)⟩
  have hlogPart : Real.log y * (Real.log 2 + y ^ F.d) ≤
      300 * y ^ ((48 : ℝ) / 100) := by
    have hfirst : Real.log y * Real.log 2 ≤ 200 * y ^ ((48 : ℝ) / 100) := by
      calc
        _ ≤ Real.log y * 2 := mul_le_mul_of_nonneg_left hlog2.2 hlognonneg
        _ = 2 * Real.log y := by ring
        _ ≤ 200 * y ^ ((48 : ℝ) / 100) := by nlinarith [hlogy48]
    calc
      Real.log y * (Real.log 2 + y ^ F.d) =
          Real.log y * Real.log 2 + Real.log y * y ^ F.d := by ring
      _ ≤ 300 * y ^ ((48 : ℝ) / 100) := by linarith [hfirst, hlogD]
  have hHbound : H ≤ (100 * C₂ + 600 * (J : ℝ) * F.C₀) *
      y ^ ((48 : ℝ) / 100) := by
    dsimp [H]
    calc
      _ = C₂ * Real.log y + ((J : ℝ) * (2 * F.C₀)) *
            (Real.log y * (Real.log 2 + y ^ F.d)) := by ring
      _ ≤ C₂ * (100 * y ^ ((48 : ℝ) / 100)) +
            ((J : ℝ) * (2 * F.C₀)) *
              (300 * y ^ ((48 : ℝ) / 100)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hlogy48 (le_of_lt hC₂))
          (mul_le_mul_of_nonneg_left hlogPart
            (mul_nonneg (by positivity)
              (mul_nonneg (by norm_num) (le_of_lt F.C₀_pos))))
      _ = _ := by ring
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    have hcoef : 0 ≤ 2 * F.C₀ * Real.log y :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt F.C₀_pos)) hlognonneg
    have hlast : 0 ≤ Real.log 2 + y ^ F.d :=
      add_nonneg hlog2.1 (Real.rpow_nonneg (le_of_lt hypos) _)
    exact add_nonneg
      (mul_nonneg (le_of_lt hC₂) hlognonneg)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg J) hcoef) hlast)
  have hExpHone : 1 ≤ Real.exp H := Real.one_le_exp_iff.mpr hHnonneg
  have hQone : 1 ≤ Q := by
    dsimp [Q]
    calc
      1 ≤ 10 * 1 * 1 := by norm_num
      _ ≤ 10 * y ^ ((52 : ℝ) / 100) * Real.exp H := by gcongr
  have hstep := model_stepBound_exp_bound A hP hy hkBound
  have hBbound : (B : ℝ) ≤ Q + 1 := by
    dsimp [B, Q]
    push_cast
    have hprod : (2 * (R : ℝ) + 1) * (A.stepBound : ℝ) ≤
        (5 * y ^ ((52 : ℝ) / 100)) * Real.exp H :=
      mul_le_mul hRlen hstep (by positivity) (by positivity)
    calc
      _ ≤ 2 * ((5 * y ^ ((52 : ℝ) / 100)) * Real.exp H) + 1 :=
        by
          have h2 : 2 * ((2 * (R : ℝ) + 1) * (A.stepBound : ℝ)) ≤
              2 * ((5 * y ^ ((52 : ℝ) / 100)) * Real.exp H) :=
            mul_le_mul_of_nonneg_left hprod (by norm_num)
          linarith
      _ = 10 * y ^ ((52 : ℝ) / 100) * Real.exp H + 1 := by ring
  have hBtwice : (B : ℝ) ≤ 2 * Q := hBbound.trans (by linarith)
  have hQpos : 0 < Q := by linarith
  have hlogQ : Real.log Q = Real.log 10 +
      ((52 : ℝ) / 100) * Real.log y + H := by
    dsimp [Q]
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
      Real.log_mul (by norm_num) (by positivity), Real.log_rpow hypos, Real.log_exp]
  have hlogB : Real.log (B : ℝ) ≤
      (64 + 100 * C₂ + 600 * (J : ℝ) * F.C₀) * y ^ ((48 : ℝ) / 100) := by
    have hBpos : 0 < (B : ℝ) := by positivity
    calc
      Real.log (B : ℝ) ≤ Real.log (2 * Q) := Real.log_le_log hBpos hBtwice
      _ = Real.log 2 + Real.log Q := by rw [Real.log_mul (by norm_num) (ne_of_gt hQpos)]
      _ = Real.log 2 + Real.log 10 + ((52 : ℝ) / 100) * Real.log y + H := by
        rw [hlogQ]
        ring
      _ ≤ _ := by
        have hLogSmall : ((52 : ℝ) / 100) * Real.log y ≤
            52 * y ^ ((48 : ℝ) / 100) := by nlinarith [hlogy48]
        nlinarith [hlog2.2, Real.log_le_self (by norm_num : 0 ≤ (10 : ℝ)), hLogSmall,
          hHbound, hy48one]
  have hLogBsmall : Real.log (B : ℝ) ≤ y ^ ((51 : ℝ) / 100) := by
    calc
      Real.log (B : ℝ) ≤
          (64 + 100 * C₂ + 600 * (J : ℝ) * F.C₀) * y ^ ((48 : ℝ) / 100) := hlogB
      _ ≤ y ^ ((3 : ℝ) / 100) * y ^ ((48 : ℝ) / 100) :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg (le_of_lt hypos) _)
      _ = y ^ ((51 : ℝ) / 100) := by
        rw [← Real.rpow_add hypos]
        congr 1
        norm_num
  have hBpos : 0 < (B : ℝ) := by positivity
  have hBexp : (B : ℝ) ≤ Real.exp (y ^ ((51 : ℝ) / 100)) :=
    (Real.log_le_log_iff hBpos (Real.exp_pos _)).mp (by simpa using hLogBsmall)
  simpa [R, B, y] using hBexp

private theorem packet_scalar_cleanup (E C₃ Cf X y : ℝ) (R B : ℕ)
    (t s r : ℝ) (hy : 1 ≤ y) (hX : 1 ≤ X) (hR : 2 ≤ R)
    (hRlow : y ^ ((52 : ℝ) / 100) ≤ (R : ℝ))
    (hB : (B : ℝ) ≤ Real.exp (y ^ ((51 : ℝ) / 100)))
    (ht0 : 0 ≤ t) (ht : t ≤ X * y ^ (2 * C₃))
    (hs0 : 0 ≤ s) (hs : s ≤ X * y ^ (2 * C₃))
    (hr0 : 0 ≤ r)
    (hr : r ≤ 2 * X * y ^ (-2 * (E + 1) * (R : ℝ))) :
    Real.sqrt (2 * t * s ^ (1 - (R : ℝ)⁻¹) *
      ((B : ℝ) * Real.exp (2 * Cf * Real.sqrt y) * r) ^ (R : ℝ)⁻¹) ≤
        Real.exp (10 + |Cf| + 2 * |C₃|) * X * y ^ (-E + 2 * C₃) := by
  classical
  let α : ℝ := 1 - (R : ℝ)⁻¹
  let β : ℝ := (R : ℝ)⁻¹
  let U : ℝ := X * y ^ (2 * C₃)
  let V : ℝ := Real.exp (y ^ ((51 : ℝ) / 100)) *
    Real.exp (2 * Cf * Real.sqrt y) *
      (2 * X * y ^ (-2 * (E + 1) * (R : ℝ)))
  let W : ℝ := (B : ℝ) * Real.exp (2 * Cf * Real.sqrt y) * r
  let Upper : ℝ := 2 * U * U ^ α * V ^ β
  let K : ℝ := Real.exp (10 + |Cf| + 2 * |C₃|)
  have hypos : 0 < y := by linarith
  have hXpos : 0 < X := by linarith
  have hRpos : 0 < (R : ℝ) := by positivity
  have hβpos : 0 < β := by dsimp [β]; positivity
  have hβ0 : 0 ≤ β := hβpos.le
  have hβ1 : β ≤ 1 := by
    dsimp [β]
    exact (inv_le_one₀ hRpos).2 (by exact_mod_cast (by omega : 1 ≤ R))
  have hα0 : 0 ≤ α := by
    dsimp [α]
    linarith [hβ1]
  have hβR : β * (R : ℝ) = 1 := by
    dsimp [β]
    exact inv_mul_cancel₀ hRpos.ne'
  have hsqrtR : Real.sqrt y ≤ (R : ℝ) := by
    calc
      Real.sqrt y = y ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow y
      _ ≤ y ^ ((52 : ℝ) / 100) :=
        Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
      _ ≤ (R : ℝ) := hRlow
  have hpowR : y ^ ((51 : ℝ) / 100) ≤ (R : ℝ) := by
    calc
      y ^ ((51 : ℝ) / 100) ≤ y ^ ((52 : ℝ) / 100) :=
        Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
      _ ≤ (R : ℝ) := hRlow
  have hβsqrt : β * Real.sqrt y ≤ 1 := by
    calc
      β * Real.sqrt y ≤ β * (R : ℝ) := mul_le_mul_of_nonneg_left hsqrtR hβ0
      _ = 1 := hβR
  have hβpow : β * y ^ ((51 : ℝ) / 100) ≤ 1 := by
    calc
      β * y ^ ((51 : ℝ) / 100) ≤ β * (R : ℝ) := mul_le_mul_of_nonneg_left hpowR hβ0
      _ = 1 := hβR
  have hlogUpperR : Real.log y ≤ 2 * (R : ℝ) := by
    have hlog := Real.log_le_rpow_div (le_of_lt hypos)
      (by norm_num : 0 < (52 : ℝ) / 100)
    have hcoeff : ((52 : ℝ) / 100)⁻¹ ≤ 2 := by norm_num
    calc
      Real.log y ≤ y ^ ((52 : ℝ) / 100) / ((52 : ℝ) / 100) := hlog
      _ ≤ 2 * y ^ ((52 : ℝ) / 100) := by
        calc
          _ = ((52 : ℝ) / 100)⁻¹ * y ^ ((52 : ℝ) / 100) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff
            (Real.rpow_nonneg (le_trans zero_le_one hy) _)
      _ ≤ 2 * (R : ℝ) := by gcongr
  have hβlog : β * Real.log y ≤ 2 := by
    calc
      β * Real.log y = Real.log y / (R : ℝ) := by dsimp [β]; ring
      _ ≤ 2 := (div_le_iff₀ hRpos).2 hlogUpperR
  have hlognonneg : 0 ≤ Real.log y := Real.log_nonneg hy
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hWleV : W ≤ V := by
    dsimp [W, V]
    have hbExp : (B : ℝ) * Real.exp (2 * Cf * Real.sqrt y) ≤
        Real.exp (y ^ ((51 : ℝ) / 100)) * Real.exp (2 * Cf * Real.sqrt y) :=
      mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le
    exact mul_le_mul hbExp hr (by positivity) (by positivity)
  have hRpowSource : s ^ α ≤ U ^ α := Real.rpow_le_rpow hs0 hs (by exact hα0)
  have hRpowMoment : W ^ β ≤ V ^ β := Real.rpow_le_rpow hW0 hWleV hβ0
  have hRad :
      2 * t * s ^ α * W ^ β ≤ Upper := by
    dsimp [Upper]
    calc
      _ ≤ 2 * U * s ^ α * W ^ β := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left ht (by norm_num)
          · exact Real.rpow_nonneg hs0 _
        · exact Real.rpow_nonneg hW0 _
      _ ≤ 2 * U * U ^ α * W ^ β := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hRpowSource (by positivity)
        · exact Real.rpow_nonneg hW0 _
      _ ≤ 2 * U * U ^ α * V ^ β := by
        exact mul_le_mul_of_nonneg_left hRpowMoment
          (mul_nonneg (mul_nonneg (by norm_num) hUpos.le)
            (Real.rpow_nonneg (le_of_lt hUpos) _))
  have hlogU : Real.log U = Real.log X + (2 * C₃) * Real.log y := by
    dsimp [U]
    rw [Real.log_mul (ne_of_gt hXpos) (ne_of_gt (Real.rpow_pos_of_pos hypos _)),
      Real.log_rpow hypos]
  have hpowMoment : 0 < 2 * X * y ^ (-2 * (E + 1) * (R : ℝ)) := by positivity
  have hlogMomentBase :
      Real.log (2 * X * y ^ (-2 * (E + 1) * (R : ℝ))) =
        Real.log 2 + Real.log X + (-2 * (E + 1) * (R : ℝ)) * Real.log y := by
    rw [Real.log_mul (ne_of_gt (mul_pos (by norm_num) hXpos))
        (ne_of_gt (Real.rpow_pos_of_pos hypos _)),
      Real.log_mul (by norm_num) (ne_of_gt hXpos), Real.log_rpow hypos]
  have hlogV : Real.log V = y ^ ((51 : ℝ) / 100) +
      2 * Cf * Real.sqrt y + Real.log 2 + Real.log X +
        (-2 * (E + 1) * (R : ℝ)) * Real.log y := by
    dsimp [V]
    rw [Real.log_mul (by positivity) (ne_of_gt hpowMoment),
      Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp, hlogMomentBase]
    ring
  have hlogUpper : Real.log Upper = Real.log 2 + Real.log U +
      α * Real.log U + β * Real.log V := by
    dsimp [Upper]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_rpow hVpos]
    rw [Real.log_mul (by norm_num) (ne_of_gt hUpos)]
    rw [Real.log_rpow hUpos]
  have hlogTarget :
      Real.log ((K * X * y ^ (-E + 2 * C₃)) ^ 2) =
        2 * ((10 + |Cf| + 2 * |C₃|) + Real.log X + (-E + 2 * C₃) * Real.log y) := by
    dsimp [K]
    rw [Real.log_pow]
    rw [Real.log_mul (ne_of_gt (mul_pos (Real.exp_pos _) hXpos))
      (ne_of_gt (Real.rpow_pos_of_pos hypos _))]
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hXpos)]
    rw [Real.log_exp, Real.log_rpow hypos]
    ring
  have hβlogV : β * Real.log V =
      β * y ^ ((51 : ℝ) / 100) + 2 * Cf * β * Real.sqrt y +
        β * Real.log 2 + β * Real.log X + (-2 * (E + 1)) * Real.log y := by
    rw [hlogV]
    have hcancel : β * ((-2 * (E + 1) * (R : ℝ)) * Real.log y) =
        (-2 * (E + 1)) * Real.log y := by
      calc
        _ = (-2 * (E + 1)) * (β * (R : ℝ)) * Real.log y := by ring
        _ = _ := by rw [hβR]; ring
    calc
      _ = β * y ^ ((51 : ℝ) / 100) + 2 * Cf * β * Real.sqrt y +
            β * Real.log 2 + β * Real.log X +
            β * ((-2 * (E + 1) * (R : ℝ)) * Real.log y) := by ring
      _ = _ := by rw [hcancel]
  have hlogUpperSimplified : Real.log Upper =
      2 * Real.log X +
        (4 * C₃ - 2 * C₃ * β - 2 * (E + 1)) * Real.log y +
        (1 + β) * Real.log 2 + β * y ^ ((51 : ℝ) / 100) +
        2 * Cf * β * Real.sqrt y := by
    rw [hlogUpper, hlogU, hβlogV]
    dsimp [α]
    ring
  have hlogUpper_le_target : Real.log Upper ≤
      Real.log ((K * X * y ^ (-E + 2 * C₃)) ^ 2) := by
    rw [hlogUpperSimplified, hlogTarget]
    have hBetaY51 : (R : ℝ)⁻¹ * y ^ ((51 : ℝ) / 100) ≤ 1 := hβpow
    have hCfTerm : 2 * Cf * (R : ℝ)⁻¹ * Real.sqrt y ≤ 2 * |Cf| := by
      calc
        2 * Cf * (R : ℝ)⁻¹ * Real.sqrt y = 2 * Cf * ((R : ℝ)⁻¹ * Real.sqrt y) := by ring
        _ ≤ 2 * |Cf| * ((R : ℝ)⁻¹ * Real.sqrt y) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_abs_self Cf) (by norm_num)) (by positivity)
        _ ≤ 2 * |Cf| := by
          calc
            2 * |Cf| * ((R : ℝ)⁻¹ * Real.sqrt y) ≤ 2 * |Cf| * 1 :=
              mul_le_mul_of_nonneg_left hβsqrt (by positivity)
            _ = 2 * |Cf| := by ring
    have hC₃Term : -2 * C₃ * (R : ℝ)⁻¹ * Real.log y ≤ 4 * |C₃| := by
      calc
        -2 * C₃ * (R : ℝ)⁻¹ * Real.log y =
            2 * (-C₃) * ((R : ℝ)⁻¹ * Real.log y) := by ring
        _ ≤ 2 * |C₃| * ((R : ℝ)⁻¹ * Real.log y) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (neg_le_abs C₃) (by norm_num)) (by positivity)
        _ ≤ 4 * |C₃| := by
          calc
            2 * |C₃| * ((R : ℝ)⁻¹ * Real.log y) ≤ 2 * |C₃| * 2 :=
              mul_le_mul_of_nonneg_left hβlog (by positivity)
            _ = 4 * |C₃| := by ring
    have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog2le : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
    have hlog2part' : (1 + (R : ℝ)⁻¹) * Real.log 2 ≤ 4 := by
      have hcoef : 1 + (R : ℝ)⁻¹ ≤ 2 := by linarith [hβ1]
      calc
        _ ≤ 2 * Real.log 2 := mul_le_mul_of_nonneg_right hcoef hlog2_nonneg
        _ ≤ 4 := by nlinarith [hlog2le]
    have hLterm : -2 * Real.log y ≤ 0 := by nlinarith [hlognonneg]
    nlinarith [hBetaY51, hCfTerm, hC₃Term, hlog2part', hLterm,
      hβR, hβlog, hlognonneg]
  have hupper_le_target : Upper ≤ (K * X * y ^ (-E + 2 * C₃)) ^ 2 :=
    (Real.log_le_log_iff (by positivity) (by positivity)).mp hlogUpper_le_target
  have hrad_le_target :
      2 * t * s ^ α * W ^ β ≤ (K * X * y ^ (-E + 2 * C₃)) ^ 2 :=
    hRad.trans hupper_le_target
  have htarget_nonneg : 0 ≤ K * X * y ^ (-E + 2 * C₃) := by positivity
  rw [Real.sqrt_le_iff]
  exact ⟨htarget_nonneg, hrad_le_target⟩

private theorem chunk_fiber_card_le {B : ℕ} (hB : 0 < B) (lo : ℤ) (D : Finset ℤ)
    (j : ℤ) :
    (D.filter (fun n => chunkIndex lo B n = j)).card ≤ B := by
  classical
  let I := D.filter (fun n => chunkIndex lo B n = j)
  let rem (n : ℤ) : ℕ := ((n - lo) % (B : ℤ)).toNat
  have hBz : (0 : ℤ) < B := by exact_mod_cast hB
  have hmod_nonneg (n : ℤ) : 0 ≤ (n - lo) % (B : ℤ) :=
    Int.emod_nonneg _ (ne_of_gt hBz)
  have hmod_lt (n : ℤ) : (n - lo) % (B : ℤ) < B := by
    have h := Int.emod_lt_abs (n - lo) (ne_of_gt hBz)
    simpa [abs_of_pos hBz] using h
  have hmaps : ∀ n ∈ I, rem n ∈ Finset.range B := by
    intro n hn
    simp only [I, Finset.mem_filter] at hn
    simp only [Finset.mem_range]
    change ((n - lo) % (B : ℤ)).toNat < B
    exact (Int.toNat_lt (hmod_nonneg n)).2 (hmod_lt n)
  have hinj : Set.InjOn rem I := by
    intro n hn m hm hnm
    change n ∈ I at hn
    change m ∈ I at hm
    simp only [I, Finset.mem_filter] at hn hm
    have hremn := hmod_nonneg n
    have hremm := hmod_nonneg m
    have heq : (n - lo) % (B : ℤ) = (m - lo) % (B : ℤ) := by
      have hc := congrArg (fun k : ℕ => (k : ℤ)) hnm
      simpa [rem, Int.toNat_of_nonneg hremn, Int.toNat_of_nonneg hremm] using hc
    have hnq : chunkIndex lo B n = j := hn.2
    have hmq : chunkIndex lo B m = j := hm.2
    have hdiv : (n - lo) / (B : ℤ) = (m - lo) / (B : ℤ) := by simpa [chunkIndex] using hnq.trans hmq.symm
    have hdecompN : n - lo = (n - lo) % (B : ℤ) + (B : ℤ) * ((n - lo) / (B : ℤ)) :=
      (Int.emod_add_mul_ediv (n - lo) (B : ℤ)).symm
    have hdecompM : m - lo = (m - lo) % (B : ℤ) + (B : ℤ) * ((m - lo) / (B : ℤ)) :=
      (Int.emod_add_mul_ediv (m - lo) (B : ℤ)).symm
    have hsub : n - lo = m - lo := by rw [hdecompN, hdecompM, heq, hdiv]
    omega
  have hcard := Finset.card_le_card_of_injOn rem hmaps hinj
  simpa [I] using hcard

private theorem chunkIndex_close {B : ℕ} (hB : 0 < B) (lo n m : ℤ) (M : ℤ)
    (hBM : 2 * M < B) (hclose : |n - m| ≤ 2 * M) :
    |chunkIndex lo B n - chunkIndex lo B m| ≤ 1 := by
  have hBz : (0 : ℤ) < B := by exact_mod_cast hB
  have hmodn0 : 0 ≤ (n - lo) % (B : ℤ) := Int.emod_nonneg _ (ne_of_gt hBz)
  have hmodm0 : 0 ≤ (m - lo) % (B : ℤ) := Int.emod_nonneg _ (ne_of_gt hBz)
  have hmodnlt : (n - lo) % (B : ℤ) < B := by
    simpa [abs_of_pos hBz] using Int.emod_lt_abs (n - lo) (ne_of_gt hBz)
  have hmodmlt : (m - lo) % (B : ℤ) < B := by
    simpa [abs_of_pos hBz] using Int.emod_lt_abs (m - lo) (ne_of_gt hBz)
  have hdecompN : n - lo = (n - lo) % (B : ℤ) + (B : ℤ) * ((n - lo) / (B : ℤ)) :=
    (Int.emod_add_mul_ediv (n - lo) (B : ℤ)).symm
  have hdecompM : m - lo = (m - lo) % (B : ℤ) + (B : ℤ) * ((m - lo) / (B : ℤ)) :=
    (Int.emod_add_mul_ediv (m - lo) (B : ℤ)).symm
  by_contra hnot
  have hnotQ : ¬ |(n - lo) / (B : ℤ) - (m - lo) / (B : ℤ)| ≤ 1 := by
    simpa [chunkIndex] using hnot
  have hdiff :
      (n - lo) / (B : ℤ) + 2 ≤ (m - lo) / (B : ℤ) ∨
        (m - lo) / (B : ℤ) + 2 ≤ (n - lo) / (B : ℤ) := by
    have hbigQ : 1 < |(n - lo) / (B : ℤ) - (m - lo) / (B : ℤ)| :=
      lt_of_not_ge hnotQ
    by_cases hq : (n - lo) / (B : ℤ) ≤ (m - lo) / (B : ℤ)
    · left
      have hgap : 1 < (m - lo) / (B : ℤ) - (n - lo) / (B : ℤ) := by
        simpa [abs_of_nonpos (sub_nonpos.mpr hq)] using hbigQ
      omega
    · right
      have hq' : (m - lo) / (B : ℤ) ≤ (n - lo) / (B : ℤ) := by omega
      have hgap : 1 < (n - lo) / (B : ℤ) - (m - lo) / (B : ℤ) := by
        simpa [abs_of_nonneg (sub_nonneg.mpr hq')] using hbigQ
      omega
  rcases hdiff with hdiff | hdiff
  · have hmul := mul_le_mul_of_nonneg_left hdiff (le_of_lt hBz)
    have hmn : B + 1 ≤ m - n := by
      nlinarith [hdecompN, hdecompM, hmul, hmodn0, hmodm0, hmodnlt, hmodmlt]
    have hclose' := (abs_le.mp hclose).1
    nlinarith [hBM]
  · have hmul := mul_le_mul_of_nonneg_left hdiff (le_of_lt hBz)
    have hnm : B + 1 ≤ n - m := by
      nlinarith [hdecompN, hdecompM, hmul, hmodn0, hmodm0, hmodnlt, hmodmlt]
    have hclose' := (abs_le.mp hclose).2
    nlinarith [hBM]

private theorem neighbors_time_span {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (a z : A.State) (hz : z ∈ A.neighbors a.1) :
    |z.1 - a.1| ≤ (A.stepBound : ℤ) := by
  have hz' : z ∈ Finset.Icc (a.1 - A.stepBound) (a.1 + A.stepBound) ×ˢ Finset.univ := by
    simpa [Model.neighbors] using hz
  have htime : z.1 ∈ Finset.Icc (a.1 - A.stepBound) (a.1 + A.stepBound) :=
    (Finset.mem_product.mp hz').1
  simp only [Finset.mem_Icc] at htime
  exact abs_le.mpr ⟨by omega, by omega⟩

private theorem twoNeighbors_time_span {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (a z : A.State) (hz : z ∈ twoNeighbors A a) :
    |z.1 - a.1| ≤ 2 * (A.stepBound : ℤ) := by
  classical
  rcases Finset.mem_biUnion.mp hz with ⟨w, hwa, hwz⟩
  have h1 := neighbors_time_span A a w hwa
  have h2 := neighbors_time_span A w z hwz
  calc
    |z.1 - a.1| ≤ |z.1 - w.1| + |w.1 - a.1| := abs_sub_le _ _ _
    _ ≤ 2 * (A.stepBound : ℤ) := by omega

private theorem twoReach_time_span {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (base : Finset A.State) :
    ∀ (R : ℕ) (z : A.State), z ∈ twoReach A base R →
      ∃ a ∈ base, |z.1 - a.1| ≤ 2 * (R : ℤ) * (A.stepBound : ℤ) := by
  intro R
  induction R with
  | zero =>
      intro z hz
      simp only [twoReach] at hz
      exact ⟨z, hz, by simp⟩
  | succ R ih =>
      intro z hz
      simp only [twoReach, Finset.mem_union, Finset.mem_biUnion] at hz
      rcases hz with hz | ⟨w, hw, hwz⟩
      · obtain ⟨a, ha, hspan⟩ := ih z hz
        refine ⟨a, ha, ?_⟩
        have hstep : 0 ≤ (A.stepBound : ℤ) := Nat.cast_nonneg _
        have hR : (R : ℤ) ≤ (R + 1 : ℤ) := by omega
        have hmono : 2 * (R : ℤ) * (A.stepBound : ℤ) ≤
            2 * (R + 1 : ℤ) * (A.stepBound : ℤ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hR (by norm_num)) hstep
        exact hspan.trans hmono
      · obtain ⟨a, ha, hspan⟩ := ih w hw
        have hstep := twoNeighbors_time_span A w z hwz
        refine ⟨a, ha, ?_⟩
        calc
          |z.1 - a.1| ≤ |z.1 - w.1| + |w.1 - a.1| := abs_sub_le _ _ _
          _ ≤ 2 * (A.stepBound : ℤ) + 2 * (R : ℤ) * (A.stepBound : ℤ) :=
            add_le_add hstep hspan
          _ = 2 * ((R + 1 : ℕ) : ℤ) * (A.stepBound : ℤ) := by
            simp only [Nat.cast_add, Nat.cast_one]
            ring

private theorem neighborUnion_time_span {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (base : Finset A.State) (R : ℕ)
    (z : A.State) (hz : z ∈ neighborUnion A (twoReach A base R)) :
    ∃ a ∈ base,
      |z.1 - a.1| ≤ (2 * (R : ℤ) + 1) * (A.stepBound : ℤ) := by
  classical
  rcases Finset.mem_biUnion.mp hz with ⟨w, hw, hwz⟩
  obtain ⟨a, ha, hspan⟩ := twoReach_time_span A base R w hw
  have hstep := neighbors_time_span A w z hwz
  refine ⟨a, ha, ?_⟩
  calc
    |z.1 - a.1| ≤ |z.1 - w.1| + |w.1 - a.1| := abs_sub_le _ _ _
    _ ≤ (A.stepBound : ℤ) + 2 * (R : ℤ) * (A.stepBound : ℤ) := add_le_add hstep hspan
    _ = (2 * (R : ℤ) + 1) * (A.stepBound : ℤ) := by ring

private theorem block_target_time_span {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (I : Finset ℤ) (R : ℕ)
    (z : A.State)
    (hz : z ∈ neighborUnion A (twoReach A (blockStates A I) R)) :
    ∃ n ∈ I, |z.1 - n| ≤ (2 * (R : ℤ) + 1) * (A.stepBound : ℤ) := by
  obtain ⟨a, ha, hspan⟩ := neighborUnion_time_span A (blockStates A I) R z hz
  have ha' : a.1 ∈ I := by simpa [blockStates] using ha
  exact ⟨a.1, ha', hspan⟩

private theorem chunk_target_overlap {α : Type*} (D : Finset ℤ) (lo : ℤ)
    {B : ℕ} (hB : 0 < B) (M : ℤ) (hBM : 2 * M < B)
    (time : α → ℤ) (Tgt : ℤ → Finset α)
    (hspan : ∀ j ∈ D.image (chunkIndex lo B), ∀ z,
      z ∈ Tgt j → ∃ n ∈ D, chunkIndex lo B n = j ∧ |time z - n| ≤ M)
    (z : α) :
    ((D.image (chunkIndex lo B)).filter (fun j => z ∈ Tgt j)).card ≤ 2 := by
  classical
  let U := (D.image (chunkIndex lo B)).filter (fun j => z ∈ Tgt j)
  have hpair (j k : ℤ) (hj : j ∈ U) (hk : k ∈ U) : |j - k| ≤ 1 := by
    have hj' := Finset.mem_filter.mp hj
    have hk' := Finset.mem_filter.mp hk
    obtain ⟨n, hn, hqN, hN⟩ := hspan j hj'.1 z hj'.2
    obtain ⟨m, hm, hqM, hM⟩ := hspan k hk'.1 z hk'.2
    have hclose : |n - m| ≤ 2 * M := by
      calc
        |n - m| ≤ |n - time z| + |time z - m| := abs_sub_le _ _ _
        _ = |time z - n| + |time z - m| := by
          congr 1
          rw [show n - time z = -(time z - n) by ring, abs_neg]
        _ ≤ M + M := add_le_add hN hM
        _ = 2 * M := by ring
    have hqclose := chunkIndex_close hB lo n m M hBM hclose
    rw [hqN, hqM] at hqclose
    exact hqclose
  by_cases hne : U.Nonempty
  · let j₀ := U.min' hne
    have hj₀ : j₀ ∈ U := Finset.min'_mem U hne
    have hlo (j : ℤ) (hj : j ∈ U) : j₀ ≤ j := Finset.min'_le U j hj
    have hhi (j : ℤ) (hj : j ∈ U) : j ≤ j₀ + 1 := by
      have h := hpair j j₀ hj hj₀
      have hh := abs_le.mp h
      omega
    have hsub : U ⊆ Finset.Icc j₀ (j₀ + 1) := by
      intro j hj
      simp only [Finset.mem_Icc]
      exact ⟨hlo j hj, hhi j hj⟩
    have hcard : (Finset.Icc j₀ (j₀ + 1)).card = 2 := by
      simp only [Int.card_Icc]
      rw [show j₀ + 1 + 1 - j₀ = (2 : ℤ) by ring]
      rfl
    calc
      U.card ≤ (Finset.Icc j₀ (j₀ + 1)).card := Finset.card_le_card hsub
      _ = 2 := hcard
  · have hU : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [U, hU]

private theorem sum_chunk_target_norm_sq_le {α : Type*} (J : Finset ℤ)
    (t : Finset α) (Tgt : ℤ → Finset α) (w : α → ℝ)
    (hW : ∀ z, 0 ≤ w z)
    (hoverlap : ∀ z, (J.filter (fun j => z ∈ Tgt j)).card ≤ 2) :
    (∑ j ∈ J, ∑ z ∈ t.filter (fun z => z ∈ Tgt j), w z) ≤
      2 * ∑ z ∈ t, w z := by
  classical
  calc
    (∑ j ∈ J, ∑ z ∈ t.filter (fun z => z ∈ Tgt j), w z) =
        ∑ j ∈ J, ∑ z ∈ t, if z ∈ Tgt j then w z else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_filter]
    _ = ∑ z ∈ t, ∑ j ∈ J, if z ∈ Tgt j then w z else 0 := Finset.sum_comm
    _ = ∑ z ∈ t, ((J.filter (fun j => z ∈ Tgt j)).card : ℝ) * w z := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [← Finset.sum_filter]
          simp [Finset.sum_const, mul_comm]
    _ ≤ ∑ z ∈ t, (2 : ℝ) * w z := by
          apply Finset.sum_le_sum
          intro z hz
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hoverlap z) (hW z)
    _ = 2 * ∑ z ∈ t, w z := by rw [Finset.mul_sum]

private theorem model_chunk_target_overlap {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (D : Finset ℤ) (lo : ℤ)
    {B : ℕ} (hB : 0 < B) (R : ℕ)
    (hBM : 2 * ((2 * (R : ℤ) + 1) * (A.stepBound : ℤ)) < B) :
    ∀ z : A.State,
      ((D.image (chunkIndex lo B)).filter (fun j => z ∈
        (fun j => neighborUnion A (twoReach A
          (blockStates A (D.filter (fun n => chunkIndex lo B n = j))) R)) j)).card ≤ 2 := by
  intro z
  let Tgt : ℤ → Finset A.State := fun j => neighborUnion A (twoReach A
    (blockStates A (D.filter (fun n => chunkIndex lo B n = j))) R)
  change (((D.image (chunkIndex lo B)).filter (fun j => z ∈ Tgt j)).card ≤ 2)
  simpa [Tgt] using (chunk_target_overlap (D := D) (lo := lo) (B := B) hB
    ((2 * (R : ℤ) + 1) * (A.stepBound : ℤ)) hBM
    (fun z : A.State => z.1) Tgt
    (by
      intro j hj z' hz
      obtain ⟨n, hn, hdist⟩ := block_target_time_span A
        (D.filter (fun n => chunkIndex lo B n = j)) R z' hz
      rcases Finset.mem_filter.mp hn with ⟨hnD, hq⟩
      exact ⟨n, hnD, hq, hdist⟩) z)

private theorem rootMatrix_mul_coordinate {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (I : Finset ℤ) (S : Finset A.State)
    (f : ℤ → ℂ) (s : {z // z ∈ S}) :
    ((rootMatrix A S I).toEuclideanLin
      (WithLp.toLp 2 (fun n : {n // n ∈ I} => f n.1))).ofLp s =
      if s.1.1 ∈ I then
        (Real.sqrt (A.stateMass s.1) : ℂ) * f s.1.1 else 0 := by
  classical
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, rootMatrix, WithLp.ofLp_toLp]
  by_cases htime : s.1.1 ∈ I
  · rw [if_pos htime]
    change (∑ i ∈ I.attach,
        if s.1.1 = i.1 then (Real.sqrt (A.stateMass s.1) : ℂ) * f i.1 else 0) =
      (Real.sqrt (A.stateMass s.1) : ℂ) * f s.1.1
    let i₀ : {n // n ∈ I} := ⟨s.1.1, htime⟩
    calc
      _ = (Real.sqrt (A.stateMass s.1) : ℂ) * f i₀.1 := by
        calc
          _ = if s.1.1 = i₀.1 then
                (Real.sqrt (A.stateMass s.1) : ℂ) * f i₀.1 else 0 :=
                  Finset.sum_eq_single (s := I.attach) i₀
                    (by
                      intro i hi hne
                      have hneq : s.1.1 ≠ i.1 := by
                        intro heq
                        apply hne
                        exact Subtype.ext heq.symm
                      change (if s.1.1 = i.1 then
                        (Real.sqrt (A.stateMass s.1) : ℂ) * f i.1 else 0) = 0
                      split_ifs with heq
                      · exact (hneq heq).elim
                      · rfl)
                    (by
                      intro hnot
                      exact False.elim (hnot (Finset.mem_attach I i₀)))
          _ = (Real.sqrt (A.stateMass s.1) : ℂ) * f i₀.1 := by simp [i₀]
      _ = _ := by simp [i₀]
  · rw [if_neg htime]
    have hzero (i : {n // n ∈ I}) (hi : i ∈ I.attach) : s.1.1 ≠ i.1 := by
      intro heq
      exact htime (heq ▸ i.2)
    change (∑ i ∈ I.attach,
        if s.1.1 = i.1 then (Real.sqrt (A.stateMass s.1) : ℂ) * f i.1 else 0) = 0
    apply Finset.sum_eq_zero
    intro i hi
    simp [hzero i hi]

private theorem blockStates_filter_eq {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (I : Finset ℤ) (S : Finset A.State)
    (hbase : blockStates A I ⊆ S) :
    S.filter (fun z => z.1 ∈ I) = blockStates A I := by
  classical
  ext z
  constructor
  · intro hz
    rcases Finset.mem_filter.mp hz with ⟨_, htime⟩
    change z ∈ I.product Finset.univ
    exact Finset.mem_product.mpr ⟨htime, Finset.mem_univ _⟩
  · intro hz
    have hz' : z ∈ I.product Finset.univ := by simpa [blockStates] using hz
    have htime := (Finset.mem_product.mp hz').1
    apply Finset.mem_filter.mpr
    exact ⟨hbase (by simpa [blockStates] using hz), htime⟩

private theorem rootMatrix_mul_norm_sq {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) {x : ℝ} (hP : P.Admissible F x)
    (I : Finset ℤ) (S : Finset A.State) (hbase : blockStates A I ⊆ S)
    (f : ℤ → ℂ) :
    ‖(rootMatrix A S I).toEuclideanLin
        (WithLp.toLp 2 (fun n : {n // n ∈ I} => f n.1))‖ ^ 2 =
      ∑ n ∈ I, ∑ a : A.Labels,
        A.stateMass (n, a) * ‖f n‖ ^ 2 := by
  classical
  let c : EuclideanSpace ℂ {n // n ∈ I} :=
    WithLp.toLp 2 (fun n : {n // n ∈ I} => f n.1)
  let U := rootMatrix A S I
  have hnorm : ‖U.toEuclideanLin c‖ ^ 2 =
      ∑ z : {z // z ∈ S}, ‖(U.toEuclideanLin c).ofLp z‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq (U.toEuclideanLin c)
  have hcoord (z : {z // z ∈ S}) :
      (U.toEuclideanLin c).ofLp z =
        if z.1.1 ∈ I then
          (Real.sqrt (A.stateMass z.1) : ℂ) * f z.1.1 else 0 := by
    exact rootMatrix_mul_coordinate A I S f z
  let w (z : A.State) : ℝ :=
    if z.1 ∈ I then A.stateMass z * ‖f z.1‖ ^ 2 else 0
  have hsubsum :
      (∑ z : {z // z ∈ S}, ‖(U.toEuclideanLin c).ofLp z‖ ^ 2) =
        ∑ z ∈ S, w z := by
    calc
      _ = ∑ z : {z // z ∈ S}, w z.1 := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [hcoord]
            by_cases htime : z.1.1 ∈ I
            · simp only [if_pos htime]
              have hmass := stateMass_nonneg_of_admissible A hP z.1
              calc
                ‖(Real.sqrt (A.stateMass z.1) : ℂ) * f z.1.1‖ ^ 2 =
                    ‖(Real.sqrt (A.stateMass z.1) : ℂ)‖ ^ 2 * ‖f z.1.1‖ ^ 2 := by
                      rw [norm_mul]
                      ring
                _ = w z.1 := by
                      simp [w, htime, Complex.norm_real, Real.sq_sqrt hmass]
            · simp [w, htime]
      _ = ∑ z ∈ S, w z :=
        (Finset.sum_subtype S (by intro z; simp) w).symm
  have hsum :
      (∑ z : {z // z ∈ S}, ‖(U.toEuclideanLin c).ofLp z‖ ^ 2) =
        ∑ n ∈ I, ∑ a : A.Labels,
          A.stateMass (n, a) * ‖f n‖ ^ 2 := by
    have hfilter :
        (∑ z ∈ S, w z) =
          ∑ z ∈ S.filter (fun z => z.1 ∈ I), A.stateMass z * ‖f z.1‖ ^ 2 := by
      simp only [w]
      rw [Finset.sum_filter]
    have hproduct :
        (∑ z ∈ blockStates A I, A.stateMass z * ‖f z.1‖ ^ 2) =
          ∑ n ∈ I, ∑ a : A.Labels,
            A.stateMass (n, a) * ‖f n‖ ^ 2 :=
      sum_blockStates A I (fun z : A.State => A.stateMass z * ‖f z.1‖ ^ 2)
    calc
      _ = ∑ z ∈ S, w z := hsubsum
      _ = ∑ z ∈ S.filter (fun z => z.1 ∈ I),
          A.stateMass z * ‖f z.1‖ ^ 2 := hfilter
      _ = ∑ z ∈ blockStates A I, A.stateMass z * ‖f z.1‖ ^ 2 := by
        rw [blockStates_filter_eq A I S hbase]
      _ = _ := hproduct
  calc
    _ = ∑ z : {z // z ∈ S}, ‖(U.toEuclideanLin c).ofLp z‖ ^ 2 := hnorm
    _ = _ := hsum

private theorem targetVector_norm_sq_eq {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) {x : ℝ} (hP : P.Admissible F x)
    (T t : Finset A.State) (g : A.State → ℂ) :
    ‖WithLp.toLp 2 (fun z : {z // z ∈ T} =>
        if z.1 ∈ t then (Real.sqrt (A.stateMass z.1) : ℂ) * g z.1 else 0)‖ ^ 2 =
      ∑ z ∈ T.filter (fun z => z ∈ t), A.stateMass z * ‖g z‖ ^ 2 := by
  classical
  let v : EuclideanSpace ℂ {z // z ∈ T} := WithLp.toLp 2 (fun z : {z // z ∈ T} =>
    if z.1 ∈ t then (Real.sqrt (A.stateMass z.1) : ℂ) * g z.1 else 0)
  have hnorm : ‖v‖ ^ 2 = ∑ z : {z // z ∈ T}, ‖v.ofLp z‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq v
  have hsum :
      (∑ z : {z // z ∈ T}, ‖v.ofLp z‖ ^ 2) =
        ∑ z ∈ T, if z ∈ t then A.stateMass z * ‖g z‖ ^ 2 else 0 := by
    calc
      _ = ∑ z : {z // z ∈ T},
          if z.1 ∈ t then A.stateMass z.1 * ‖g z.1‖ ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro z hz
            simp only [v, WithLp.ofLp_toLp]
            by_cases hzt : z.1 ∈ t
            · simp only [if_pos hzt]
              have hmass := stateMass_nonneg_of_admissible A hP z.1
              calc
                ‖(Real.sqrt (A.stateMass z.1) : ℂ) * g z.1‖ ^ 2 =
                    ‖(Real.sqrt (A.stateMass z.1) : ℂ)‖ ^ 2 * ‖g z.1‖ ^ 2 := by
                      rw [norm_mul]
                      ring
                _ = A.stateMass z.1 * ‖g z.1‖ ^ 2 := by
                      simp [Complex.norm_real, Real.sq_sqrt hmass]
            · simp [hzt]
      _ = ∑ z ∈ T, if z ∈ t then A.stateMass z * ‖g z‖ ^ 2 else 0 := by
            exact (Finset.sum_subtype T (by intro z; simp)
              (fun z => if z ∈ t then A.stateMass z * ‖g z‖ ^ 2 else 0)).symm
  have hfilter :
      (∑ z ∈ T, if z ∈ t then A.stateMass z * ‖g z‖ ^ 2 else 0) =
        ∑ z ∈ T.filter (fun z => z ∈ t), A.stateMass z * ‖g z‖ ^ 2 := by
    rw [Finset.sum_filter]
  calc
    ‖v‖ ^ 2 = ∑ z : {z // z ∈ T}, ‖v.ofLp z‖ ^ 2 := hnorm
    _ = ∑ z ∈ T, if z ∈ t then A.stateMass z * ‖g z‖ ^ 2 else 0 := hsum
    _ = ∑ z ∈ T.filter (fun z => z ∈ t), A.stateMass z * ‖g z‖ ^ 2 := hfilter

private theorem sourceVector_norm_sq (I : Finset ℤ) (f : ℤ → ℂ) :
    ‖WithLp.toLp 2 (fun n : {n // n ∈ I} => f n.1)‖ ^ 2 =
      ∑ n ∈ I, ‖f n‖ ^ 2 := by
  classical
  let c : EuclideanSpace ℂ {n // n ∈ I} :=
    WithLp.toLp 2 (fun n : {n // n ∈ I} => f n.1)
  calc
    ‖c‖ ^ 2 = ∑ n : {n // n ∈ I}, ‖c.ofLp n‖ ^ 2 := EuclideanSpace.norm_sq_eq c
    _ = ∑ n ∈ I, ‖f n‖ ^ 2 := by
      change (∑ n : {n // n ∈ I}, ‖f n.1‖ ^ 2) = ∑ n ∈ I, ‖f n‖ ^ 2
      exact (Finset.sum_subtype I (p := fun n => n ∈ I)
        (by intro n; simp) (fun n => ‖f n‖ ^ 2)).symm

private theorem rootMoment_eq_matrix_quadratic {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) {x : ℝ} (hP : P.Admissible F x)
    (I : Finset ℤ) (S : Finset A.State) (hbase : blockStates A I ⊆ S)
    (M : Matrix {z // z ∈ S} {z // z ∈ S} ℂ) (R : ℕ) (hR : 1 ≤ R)
    (n : ℤ) (hn : n ∈ I)
    (hM : ∀ a b : A.Labels,
      M ⟨(n, a), hbase (by simp [blockStates, hn])⟩
          ⟨(n, b), hbase (by simp [blockStates, hn])⟩ =
        kernelPower (kernelComp (A.physicalKernel false) A.adjointKernel) R
          (n, a) (n, b)) :
    A.rootMoment R n =
      ((Matrix.conjTranspose (rootMatrix A S I) * M * rootMatrix A S I)
        ⟨n, hn⟩ ⟨n, hn⟩).re := by
  have hsum :
      ∑ a : A.Labels, ∑ b : A.Labels,
          (Real.sqrt (A.stateMass (n, a)) : ℂ) *
            M ⟨(n, a), hbase (by simp [blockStates, hn])⟩
              ⟨(n, b), hbase (by simp [blockStates, hn])⟩ *
            (Real.sqrt (A.stateMass (n, b)) : ℂ) =
        ∑ a : A.Labels, ∑ b : A.Labels,
          (A.stateMass (n, a) : ℂ) *
            kernelPower (kernelComp (A.physicalKernel false) A.adjointKernel) R
              (n, a) (n, b) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hM]
    exact root_weighted_power_eq A hP R hR n a b
  rw [rootMatrix_quadratic_expansion A I S hbase M n hn]
  unfold Model.rootMoment
  exact (congrArg Complex.re hsum).symm

private theorem block_root_trace {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) {x : ℝ} (hP : P.Admissible F x)
    (I : Finset ℤ) (R : ℕ) (hR : 1 ≤ R) :
    (Matrix.conjTranspose
        (rootMatrix A (twoReach A (blockStates A I) R) I) *
      ((finitePhysicalMatrix A (twoReach A (blockStates A I) R)
          (neighborUnion A (twoReach A (blockStates A I) R)) *
        Matrix.conjTranspose (finitePhysicalMatrix A (twoReach A (blockStates A I) R)
          (neighborUnion A (twoReach A (blockStates A I) R)))) ^ R) *
      rootMatrix A (twoReach A (blockStates A I) R) I).trace.re =
        ∑ n ∈ I, A.rootMoment R n := by
  classical
  let B := blockStates A I
  let S := twoReach A B R
  let T := neighborUnion A S
  let C := finitePhysicalMatrix A S T
  let U := rootMatrix A S I
  let M : Matrix {z // z ∈ S} {z // z ∈ S} ℂ := (C * Matrix.conjTranspose C) ^ R
  let H : Matrix {n // n ∈ I} {n // n ∈ I} ℂ := Matrix.conjTranspose U * M * U
  have hbase : B ⊆ S := by
    exact twoReach_subset A B (Nat.zero_le R)
  have hM (n : ℤ) (hn : n ∈ I) (a b : A.Labels) :
      M ⟨(n, a), hbase (by simp [B, blockStates, hn])⟩
          ⟨(n, b), hbase (by simp [B, blockStates, hn])⟩ =
        kernelPower (kernelComp (A.physicalKernel false) A.adjointKernel) R
          (n, a) (n, b) := by
    dsimp [M, C, T, S, B]
    exact (kernelPower_eq_matrix_entry A (blockStates A I) R
      (by simp [blockStates, hn]) (by simp [blockStates, hn])).symm
  have hdiag (n : ℤ) (hn : n ∈ I) : A.rootMoment R n = (H ⟨n, hn⟩ ⟨n, hn⟩).re := by
    exact rootMoment_eq_matrix_quadratic A hP I S hbase M R hR n hn
      (hM n hn)
  have htrace : H.trace.re = ∑ n : {n // n ∈ I}, A.rootMoment R n := by
    rw [Matrix.trace, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n hn
    exact (hdiag n.1 n.2).symm
  calc
    H.trace.re = ∑ n : {n // n ∈ I}, A.rootMoment R n := htrace
    _ = ∑ n ∈ I, A.rootMoment R n :=
      (Finset.sum_subtype I (by intro n; simp) (fun n => A.rootMoment R n)).symm

private theorem rootMoment_nonneg {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) {x : ℝ} (hP : P.Admissible F x)
    (n : ℤ) (R : ℕ) (hR : 1 ≤ R) : 0 ≤ A.rootMoment R n := by
  classical
  let I : Finset ℤ := {n}
  let B := blockStates A I
  let S := twoReach A B R
  let T := neighborUnion A S
  let C := finitePhysicalMatrix A S T
  let U := rootMatrix A S I
  let G : Matrix {z // z ∈ S} {z // z ∈ S} ℂ := C * Matrix.conjTranspose C
  let H : Matrix {n // n ∈ I} {n // n ∈ I} ℂ := Matrix.conjTranspose U * (G ^ R) * U
  have hG : G.PosSemidef := by
    dsimp [G]
    exact Matrix.posSemidef_self_mul_conjTranspose C
  have hH : H.PosSemidef := by
    dsimp [H]
    exact hG.pow R |>.conjTranspose_mul_mul_same U
  have htrace : 0 ≤ H.trace.re := (Complex.nonneg_iff.mp hH.trace_nonneg).1
  have hEq : H.trace.re = A.rootMoment R n := by
    have h := block_root_trace A hP I R hR
    simpa [I, B, S, T, C, U, G, H] using h
  rw [← hEq]
  exact htrace

private theorem sum_three_factors_le {ι : Type*} (s : Finset ι)
    (b u d : ι → ℝ) (R : ℕ) (hR : 2 ≤ R)
    (hb : ∀ i, 0 ≤ b i) (hu : ∀ i, 0 ≤ u i) (hd : ∀ i, 0 ≤ d i) :
    (∑ i ∈ s, b i * Real.sqrt (u i ^ (1 - (R : ℝ)⁻¹)) *
        Real.sqrt (d i ^ (R : ℝ)⁻¹)) ≤
      Real.sqrt ((∑ i ∈ s, b i ^ 2) *
        (∑ i ∈ s, u i) ^ (1 - (R : ℝ)⁻¹) *
        (∑ i ∈ s, d i) ^ (R : ℝ)⁻¹) := by
  classical
  let α : ℝ := 1 - (R : ℝ)⁻¹
  let β : ℝ := (R : ℝ)⁻¹
  have hRpos : 0 < (R : ℝ) := by positivity
  have hRgt : (1 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
  have hα : 0 < α := by
    dsimp [α]
    have hi : (R : ℝ)⁻¹ < 1 := (inv_lt_one₀ hRpos).2 hRgt
    linarith
  have hβ : 0 < β := by dsimp [β]; positivity
  have hαβ : α + β = 1 := by dsimp [α, β]; ring
  let q : ι → ℝ := fun i => Real.sqrt (u i ^ α) * Real.sqrt (d i ^ β)
  have hq (i) : 0 ≤ q i := by dsimp [q]; positivity
  have hq2 (i) : q i ^ 2 = u i ^ α * d i ^ β := by
    dsimp [q]
    rw [mul_pow, Real.sq_sqrt (Real.rpow_nonneg (hu i) _),
      Real.sq_sqrt (Real.rpow_nonneg (hd i) _)]
  have hHolderTriple : α⁻¹.HolderTriple β⁻¹ 1 := by
    refine ⟨?_, inv_pos.mpr hα, inv_pos.mpr hβ⟩
    simp [hα.ne', hβ.ne', hαβ]
  have hHolder := Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg s
      (f := fun i => u i ^ α) (g := fun i => d i ^ β)
      (p := α⁻¹) (q := β⁻¹) (r := 1) hHolderTriple
      (by intro i hi; exact Real.rpow_nonneg (hu i) _)
      (by intro i hi; exact Real.rpow_nonneg (hd i) _)
  have hsumU : (∑ i ∈ s, (u i ^ α) ^ α⁻¹) = ∑ i ∈ s, u i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.rpow_rpow_inv (hu i) hα.ne'
  have hsumD : (∑ i ∈ s, (d i ^ β) ^ β⁻¹) = ∑ i ∈ s, d i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.rpow_rpow_inv (hd i) hβ.ne'
  have hqSum :
      (∑ i ∈ s, q i ^ 2) ≤
        (∑ i ∈ s, u i) ^ α * (∑ i ∈ s, d i) ^ β := by
    calc
      _ = ∑ i ∈ s, u i ^ α * d i ^ β := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hq2 i
      _ ≤ _ := by
        have hHolderSum := hHolder
        rw [hsumU, hsumD] at hHolderSum
        have hαexp : (1 : ℝ) / α⁻¹ = α := by field_simp
        have hβexp : (1 : ℝ) / β⁻¹ = β := by field_simp
        simpa only [Real.rpow_one, hαexp, hβexp] using hHolderSum
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s b q
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, b i * q i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hb i) (hq i)
  have hbound :
      (∑ i ∈ s, b i * q i) ^ 2 ≤
        (∑ i ∈ s, b i ^ 2) *
          ((∑ i ∈ s, u i) ^ α * (∑ i ∈ s, d i) ^ β) := by
    calc
      _ ≤ (∑ i ∈ s, b i ^ 2) * ∑ i ∈ s, q i ^ 2 := hCS
      _ ≤ _ := mul_le_mul_of_nonneg_left hqSum (Finset.sum_nonneg fun i hi => sq_nonneg _)
  have hmain := Real.le_sqrt_of_sq_le hbound
  simpa [q, α, β, mul_assoc] using hmain

private theorem block_matrix_pairing_spectral {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) {x : ℝ} (hP : P.Admissible F x)
    (I : Finset ℤ) (t : Finset A.State) (f : ℤ → ℂ) (g : A.State → ℂ)
    (R : ℕ) (hR : 1 ≤ R) :
    let B := blockStates A I
    let S := twoReach A B R
    let T := neighborUnion A S
    let C := finitePhysicalMatrix A S T
    let U := rootMatrix A S I
    let c : EuclideanSpace ℂ {n // n ∈ I} :=
      WithLp.toLp 2 (fun n : {n // n ∈ I} => f n.1)
    let v : EuclideanSpace ℂ {z // z ∈ T} :=
      WithLp.toLp 2 (fun z : {z // z ∈ T} =>
        if z.1 ∈ t then (Real.sqrt (A.stateMass z.1) : ℂ) * g z.1 else 0)
    ‖∑ n : {n // n ∈ I}, ∑ a : A.Labels, ∑ z ∈ t,
        (A.stateMass (n.1, a) : ℂ) * star (f n.1) *
          A.physicalKernel false (n.1, a) z * g z‖ ≤
      ‖v‖ * Real.sqrt ((‖U.toEuclideanLin c‖ ^ 2) ^ (1 - (R : ℝ)⁻¹)) *
        Real.sqrt ((((Matrix.conjTranspose U *
          ((C * Matrix.conjTranspose C) ^ R) * U).trace.re) * ‖c‖ ^ 2) ^
          (R : ℝ)⁻¹) := by
  classical
  let B := blockStates A I
  let S := twoReach A B R
  let T := neighborUnion A S
  let C := finitePhysicalMatrix A S T
  let U := rootMatrix A S I
  let c : EuclideanSpace ℂ {n // n ∈ I} :=
    WithLp.toLp 2 (fun n : {n // n ∈ I} => f n.1)
  let v : EuclideanSpace ℂ {z // z ∈ T} :=
    WithLp.toLp 2 (fun z : {z // z ∈ T} =>
      if z.1 ∈ t then (Real.sqrt (A.stateMass z.1) : ℂ) * g z.1 else 0)
  let G : Matrix {z // z ∈ S} {z // z ∈ S} ℂ := C * Matrix.conjTranspose C
  let H : Matrix {n // n ∈ I} {n // n ∈ I} ℂ := Matrix.conjTranspose U * (G ^ R) * U
  have hG : G.PosSemidef := by
    dsimp [G]
    exact Matrix.posSemidef_self_mul_conjTranspose C
  have hGpow : (G ^ R).PosSemidef := hG.pow R
  have hH : H.PosSemidef := by
    dsimp [H]
    exact hGpow.conjTranspose_mul_mul_same U
  have hd : 0 ≤ H.trace.re * ‖c‖ ^ 2 :=
    mul_nonneg (Complex.nonneg_iff.mp hH.trace_nonneg).1 (sq_nonneg _)
  calc
    _ = ‖inner ℂ (U.toEuclideanLin c) (C.toEuclideanLin v)‖ := by
      congr 1
      exact block_pairing_eq_matrix A hP I t f g R
    _ ≤ _ := by
      simpa [B, S, T, C, U, c, v, G, H, mul_assoc] using
        finite_matrix_pairing_bound C U R hR c v hd

private theorem block_pairing_factored {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) {x : ℝ} (hP : P.Admissible F x)
    (I : Finset ℤ) (t : Finset A.State) (f : ℤ → ℂ) (g : A.State → ℂ)
    (R : ℕ) (hR : 1 ≤ R) :
    let B := blockStates A I
    let S := twoReach A B R
    let T := neighborUnion A S
    let c : EuclideanSpace ℂ {n // n ∈ I} :=
      WithLp.toLp 2 (fun n : {n // n ∈ I} => f n.1)
    let v : EuclideanSpace ℂ {z // z ∈ T} :=
      WithLp.toLp 2 (fun z : {z // z ∈ T} =>
        if z.1 ∈ t then (Real.sqrt (A.stateMass z.1) : ℂ) * g z.1 else 0)
    ‖∑ n ∈ I, ∑ a : A.Labels, ∑ z ∈ t,
        (A.stateMass (n, a) : ℂ) * star (f n) *
          A.physicalKernel false (n, a) z * g z‖ ≤
      ‖v‖ * Real.sqrt ((∑ n ∈ I, ∑ a : A.Labels,
        A.stateMass (n, a) * ‖f n‖ ^ 2) ^ (1 - (R : ℝ)⁻¹)) *
        Real.sqrt (((∑ n ∈ I, A.rootMoment R n) *
          (∑ n ∈ I, ‖f n‖ ^ 2)) ^ (R : ℝ)⁻¹) := by
  classical
  let B := blockStates A I
  let S := twoReach A B R
  let T := neighborUnion A S
  let C := finitePhysicalMatrix A S T
  let U := rootMatrix A S I
  let c : EuclideanSpace ℂ {n // n ∈ I} :=
    WithLp.toLp 2 (fun n : {n // n ∈ I} => f n.1)
  let v : EuclideanSpace ℂ {z // z ∈ T} :=
    WithLp.toLp 2 (fun z : {z // z ∈ T} =>
      if z.1 ∈ t then (Real.sqrt (A.stateMass z.1) : ℂ) * g z.1 else 0)
  have hbase : blockStates A I ⊆ S := twoReach_subset A B (Nat.zero_le R)
  have hsubtype :
      (∑ n : {n // n ∈ I}, ∑ a : A.Labels, ∑ z ∈ t,
        (A.stateMass (n.1, a) : ℂ) * star (f n.1) *
          A.physicalKernel false (n.1, a) z * g z) =
        ∑ n ∈ I, ∑ a : A.Labels, ∑ z ∈ t,
          (A.stateMass (n, a) : ℂ) * star (f n) *
            A.physicalKernel false (n, a) z * g z := by
    exact (Finset.sum_subtype I (p := fun n => n ∈ I) (by intro n; simp)
      (fun n : ℤ => ∑ a : A.Labels, ∑ z ∈ t,
        (A.stateMass (n, a) : ℂ) * star (f n) *
          A.physicalKernel false (n, a) z * g z)).symm
  have hspec := block_matrix_pairing_spectral A hP I t f g R hR
  have hsource := rootMatrix_mul_norm_sq A hP I S hbase f
  have htrace := block_root_trace A hP I R hR
  have hcoord := sourceVector_norm_sq I f
  dsimp only [U, c, S, B, T, C] at hsource htrace
  rw [← hsubtype]
  dsimp only [B, S, T, C, U, c, v] at hspec ⊢
  simpa only [hsource, htrace, hcoord] using hspec

private theorem dyad_chunk_pairing_bound {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) {x : ℝ} (hP : P.Admissible F x)
    (D : Finset ℤ) (lo : ℤ) (B R : ℕ) (hB : 0 < B)
    (hBM : 2 * ((2 * (R : ℤ) + 1) * (A.stepBound : ℤ)) < B)
    (hR : 2 ≤ R) (t : Finset A.State) (f : ℤ → ℂ) (g : A.State → ℂ)
    (Cf : ℝ) (hf : ∀ n ∈ D, ‖f n‖ ≤ Real.exp (Cf * Real.sqrt (L x))) :
    ‖∑ n ∈ D, ∑ a : A.Labels, ∑ z ∈ t,
        (A.stateMass (n, a) : ℂ) * star (f n) *
          A.physicalKernel false (n, a) z * g z‖ ≤
      Real.sqrt ((2 * (∑ z ∈ t, A.stateMass z * ‖g z‖ ^ 2)) *
        (∑ n ∈ D, ∑ a : A.Labels, A.stateMass (n, a) * ‖f n‖ ^ 2) ^
          (1 - (R : ℝ)⁻¹) *
        ((B : ℝ) * Real.exp (2 * Cf * Real.sqrt (L x)) *
          (∑ n ∈ D, A.rootMoment R n)) ^ (R : ℝ)⁻¹) := by
  classical
  let q : ℤ → ℤ := fun n => chunkIndex lo B n
  let chunks := D.image q
  let I (j : ℤ) := D.filter (fun n => q n = j)
  let Tgt (j : ℤ) := neighborUnion A (twoReach A (blockStates A (I j)) R)
  let v (j : ℤ) : EuclideanSpace ℂ {z // z ∈ Tgt j} :=
    WithLp.toLp 2 (fun z : {z // z ∈ Tgt j} =>
      if z.1 ∈ t then (Real.sqrt (A.stateMass z.1) : ℂ) * g z.1 else 0)
  let b (j : ℤ) := ‖v j‖
  let u (j : ℤ) := ∑ n ∈ I j, ∑ a : A.Labels,
    A.stateMass (n, a) * ‖f n‖ ^ 2
  let r (j : ℤ) := ∑ n ∈ I j, A.rootMoment R n
  let c (j : ℤ) := ∑ n ∈ I j, ‖f n‖ ^ 2
  let d (j : ℤ) := r j * c j
  let blockPair (j : ℤ) := ∑ n ∈ I j, ∑ a : A.Labels, ∑ z ∈ t,
    (A.stateMass (n, a) : ℂ) * star (f n) * A.physicalKernel false (n, a) z * g z
  have hparts :
      (∑ n ∈ D, ∑ a : A.Labels, ∑ z ∈ t,
          (A.stateMass (n, a) : ℂ) * star (f n) *
            A.physicalKernel false (n, a) z * g z) =
        ∑ j ∈ chunks, blockPair j := by
    simpa [chunks, blockPair, I, q] using
      (sum_by_chunk D q (fun n => ∑ a : A.Labels, ∑ z ∈ t,
        (A.stateMass (n, a) : ℂ) * star (f n) *
          A.physicalKernel false (n, a) z * g z))
  have hlocal (j : ℤ) (hj : j ∈ chunks) :
      ‖blockPair j‖ ≤ b j *
        Real.sqrt (u j ^ (1 - (R : ℝ)⁻¹)) * Real.sqrt (d j ^ (R : ℝ)⁻¹) := by
    have h := block_pairing_factored A hP (I j) t f g R (by omega)
    simpa [blockPair, b, u, d, r, c, v, Tgt, I, q] using h
  have hb : ∀ j, 0 ≤ b j := fun j => norm_nonneg _
  have hu : ∀ j, 0 ≤ u j := by
    intro j
    apply Finset.sum_nonneg
    intro n hn
    apply Finset.sum_nonneg
    intro a ha
    exact mul_nonneg (stateMass_nonneg_of_admissible A hP (n, a)) (sq_nonneg _)
  have hr : ∀ j, 0 ≤ r j := by
    intro j
    apply Finset.sum_nonneg
    intro n hn
    exact rootMoment_nonneg A hP n R (by omega)
  have hc : ∀ j, 0 ≤ c j := by
    intro j
    apply Finset.sum_nonneg
    intro n hn
    exact sq_nonneg _
  have hd : ∀ j, 0 ≤ d j := by
    intro j
    exact mul_nonneg (hr j) (hc j)
  let w (z : A.State) := A.stateMass z * ‖g z‖ ^ 2
  have hw : ∀ z, 0 ≤ w z := by
    intro z
    exact mul_nonneg (stateMass_nonneg_of_admissible A hP z) (sq_nonneg _)
  have hoverlap : ∀ z, (chunks.filter (fun j => z ∈ Tgt j)).card ≤ 2 := by
    intro z
    simpa [chunks, Tgt, I, q] using
      (model_chunk_target_overlap A D lo hB R hBM z)
  have hbsq : (∑ j ∈ chunks, b j ^ 2) ≤ 2 * (∑ z ∈ t, w z) := by
    calc
      _ = ∑ j ∈ chunks, ‖v j‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rfl
      _ ≤ ∑ j ∈ chunks, ∑ z ∈ (Tgt j).filter (fun z => z ∈ t), w z := by
        apply Finset.sum_le_sum
        intro j hj
        have hv := targetVector_norm_sq_eq A hP (Tgt j) t g
        have hv' : ‖v j‖ ^ 2 =
            ∑ z ∈ (Tgt j).filter (fun z => z ∈ t), w z := by
          simpa [v, b, w, Tgt, I, q] using hv
        simpa [b] using hv'.le
      _ = ∑ j ∈ chunks, ∑ z ∈ t.filter (fun z => z ∈ Tgt j), w z := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr
        · ext z
          simp [and_comm]
        · intro z hz
          rfl
      _ = ∑ j ∈ chunks, ∑ z ∈ t, if z ∈ Tgt j then w z else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_filter]
      _ = ∑ z ∈ t, ∑ j ∈ chunks, if z ∈ Tgt j then w z else 0 :=
        Finset.sum_comm
      _ = ∑ z ∈ t, ((chunks.filter (fun j => z ∈ Tgt j)).card : ℝ) * w z := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [← Finset.sum_filter]
        simp [Finset.sum_const, mul_comm]
      _ ≤ ∑ z ∈ t, (2 : ℝ) * w z := by
        apply Finset.sum_le_sum
        intro z hz
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hoverlap z) (hw z)
      _ = 2 * (∑ z ∈ t, w z) := by rw [Finset.mul_sum]
  have huEq :
      (∑ j ∈ chunks, u j) =
        ∑ n ∈ D, ∑ a : A.Labels, A.stateMass (n, a) * ‖f n‖ ^ 2 := by
    simpa [chunks, u, I, q] using
      (sum_by_chunk D q (fun n => ∑ a : A.Labels,
        A.stateMass (n, a) * ‖f n‖ ^ 2)).symm
  have hrEq : (∑ j ∈ chunks, r j) = ∑ n ∈ D, A.rootMoment R n := by
    simpa [chunks, r, I, q] using
      (sum_by_chunk D q (fun n => A.rootMoment R n)).symm
  have hcBound (j : ℤ) : c j ≤ (B : ℝ) * Real.exp (2 * Cf * Real.sqrt (L x)) := by
    have hterms : ∀ n ∈ I j, ‖f n‖ ^ 2 ≤ Real.exp (2 * Cf * Real.sqrt (L x)) := by
      intro n hn
      have hnD : n ∈ D := (Finset.mem_filter.mp hn).1
      have hfn := hf n hnD
      calc
        ‖f n‖ ^ 2 ≤ Real.exp (Cf * Real.sqrt (L x)) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (le_of_lt (Real.exp_pos _))).2 hfn
        _ = Real.exp (2 * Cf * Real.sqrt (L x)) := by
          rw [← Real.exp_nat_mul (Cf * Real.sqrt (L x)) 2]
          ring_nf
    calc
      c j ≤ ∑ n ∈ I j, Real.exp (2 * Cf * Real.sqrt (L x)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hterms n hn
      _ = ((I j).card : ℝ) * Real.exp (2 * Cf * Real.sqrt (L x)) := by
        simp [Finset.sum_const, mul_comm]
      _ ≤ (B : ℝ) * Real.exp (2 * Cf * Real.sqrt (L x)) := by
        gcongr
        exact chunk_fiber_card_le hB lo D j
  have hdSum :
      (∑ j ∈ chunks, d j) ≤
        (B : ℝ) * Real.exp (2 * Cf * Real.sqrt (L x)) *
          (∑ n ∈ D, A.rootMoment R n) := by
    calc
      _ = ∑ j ∈ chunks, r j * c j := by rfl
      _ ≤ ∑ j ∈ chunks, r j *
          ((B : ℝ) * Real.exp (2 * Cf * Real.sqrt (L x))) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hcBound j) (hr j)
      _ = (B : ℝ) * Real.exp (2 * Cf * Real.sqrt (L x)) *
          (∑ j ∈ chunks, r j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [hrEq]
  have hsumLocal :
      ‖∑ j ∈ chunks, blockPair j‖ ≤
        Real.sqrt ((∑ j ∈ chunks, b j ^ 2) *
          (∑ j ∈ chunks, u j) ^ (1 - (R : ℝ)⁻¹) *
          (∑ j ∈ chunks, d j) ^ (R : ℝ)⁻¹) := by
    calc
      _ ≤ ∑ j ∈ chunks, ‖blockPair j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ chunks, b j * Real.sqrt (u j ^ (1 - (R : ℝ)⁻¹)) *
            Real.sqrt (d j ^ (R : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hlocal j hj
      _ ≤ _ := sum_three_factors_le chunks b u d R hR hb hu hd
  have hfinal :
      Real.sqrt ((∑ j ∈ chunks, b j ^ 2) *
          (∑ j ∈ chunks, u j) ^ (1 - (R : ℝ)⁻¹) *
          (∑ j ∈ chunks, d j) ^ (R : ℝ)⁻¹) ≤
        Real.sqrt ((2 * (∑ z ∈ t, w z)) *
          (∑ n ∈ D, ∑ a : A.Labels, A.stateMass (n, a) * ‖f n‖ ^ 2) ^
            (1 - (R : ℝ)⁻¹) *
          ((B : ℝ) * Real.exp (2 * Cf * Real.sqrt (L x)) *
            (∑ n ∈ D, A.rootMoment R n)) ^ (R : ℝ)⁻¹) := by
    apply Real.sqrt_le_sqrt
    have hsource0 : 0 ≤ ∑ n ∈ D, ∑ a : A.Labels,
        A.stateMass (n, a) * ‖f n‖ ^ 2 := by
      rw [← huEq]
      exact Finset.sum_nonneg fun j hj => hu j
    have htarget0 : 0 ≤ ∑ z ∈ t, w z :=
      Finset.sum_nonneg fun z hz => hw z
    have hroot0 : 0 ≤ ∑ n ∈ D, A.rootMoment R n := by
      apply Finset.sum_nonneg
      intro n hn
      exact rootMoment_nonneg A hP n R (by omega)
    have hα : 0 ≤ 1 - (R : ℝ)⁻¹ := by
      have hRpos : 0 < (R : ℝ) := by positivity
      have hRone : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
      have hinv : (R : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hRpos).2 hRone
      linarith
    have hβ : 0 ≤ (R : ℝ)⁻¹ := by positivity
    have hsourcePow : 0 ≤
        (∑ n ∈ D, ∑ a : A.Labels, A.stateMass (n, a) * ‖f n‖ ^ 2) ^
          (1 - (R : ℝ)⁻¹) := Real.rpow_nonneg hsource0 _
    have hdPow : 0 ≤ (∑ j ∈ chunks, d j) ^ (R : ℝ)⁻¹ :=
      Real.rpow_nonneg (Finset.sum_nonneg fun j hj => hd j) _
    have hblockBase0 : 0 ≤
        (B : ℝ) * Real.exp (2 * Cf * Real.sqrt (L x)) *
          (∑ n ∈ D, A.rootMoment R n) := by positivity
    have hdPow_le :
        (∑ j ∈ chunks, d j) ^ (R : ℝ)⁻¹ ≤
          ((B : ℝ) * Real.exp (2 * Cf * Real.sqrt (L x)) *
            (∑ n ∈ D, A.rootMoment R n)) ^ (R : ℝ)⁻¹ :=
      Real.rpow_le_rpow (Finset.sum_nonneg fun j hj => hd j) hdSum hβ
    calc
      _ = (∑ j ∈ chunks, b j ^ 2) *
            (∑ n ∈ D, ∑ a : A.Labels,
              A.stateMass (n, a) * ‖f n‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) *
            (∑ j ∈ chunks, d j) ^ (R : ℝ)⁻¹ := by rw [huEq]
      _ ≤ (2 * (∑ z ∈ t, w z)) *
            (∑ n ∈ D, ∑ a : A.Labels,
              A.stateMass (n, a) * ‖f n‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) *
            (∑ j ∈ chunks, d j) ^ (R : ℝ)⁻¹ := by
        calc
          _ = (∑ j ∈ chunks, b j ^ 2) *
                ((∑ n ∈ D, ∑ a : A.Labels,
                  A.stateMass (n, a) * ‖f n‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) *
                  (∑ j ∈ chunks, d j) ^ (R : ℝ)⁻¹) := by ring
          _ ≤ (2 * (∑ z ∈ t, w z)) *
                ((∑ n ∈ D, ∑ a : A.Labels,
                  A.stateMass (n, a) * ‖f n‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) *
                  (∑ j ∈ chunks, d j) ^ (R : ℝ)⁻¹) :=
              mul_le_mul_of_nonneg_right hbsq (mul_nonneg hsourcePow hdPow)
          _ = _ := by ring
      _ ≤ (2 * (∑ z ∈ t, w z)) *
            (∑ n ∈ D, ∑ a : A.Labels,
              A.stateMass (n, a) * ‖f n‖ ^ 2) ^ (1 - (R : ℝ)⁻¹) *
            ((B : ℝ) * Real.exp (2 * Cf * Real.sqrt (L x)) *
              (∑ n ∈ D, A.rootMoment R n)) ^ (R : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hdPow_le (mul_nonneg (by positivity) hsourcePow)
  rw [hparts]
  exact hsumLocal.trans hfinal

theorem PairingFromMomentTask_proof : PairingFromMomentTask := by
  intro _habs htrans
  unfold TransferencePairing
  intro F E hE
  obtain ⟨Eid, hEid, htransF⟩ := htrans F (E + 1) (by linarith)
  refine ⟨Eid, hEid, ?_⟩
  intro m C₁
  obtain ⟨J₀, htransJ⟩ := htransF m C₁
  refine ⟨J₀, ?_⟩
  intro J hJ γ C₂ C₃ Cf hγ hC₂
  let K : ℝ := Real.exp (10 + |Cf| + 2 * |C₃|)
  let Cblock : ℝ := 64 + 100 * C₂ + 600 * (J : ℝ) * F.C₀
  have hKpos : 0 < K := by positivity
  refine ⟨K, hKpos, ?_⟩
  have hMomentEv := htransJ J hJ γ C₂ hγ hC₂
  have hLlarge : ∀ᶠ x : ℝ in atTop, 1 ≤ L x := by
    simpa [L] using Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hBlockCoeff : ∀ᶠ x : ℝ in atTop,
      Cblock ≤ (L x) ^ ((3 : ℝ) / 100) := by
    have hpow :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (3 : ℝ) / 100)).eventually_ge_atTop Cblock
    simpa [L] using Real.tendsto_log_atTop.eventually hpow
  filter_upwards [hMomentEv, hLlarge, hBlockCoeff, eventually_gt_atTop (1 : ℝ)]
    with x hMoment hy hCblock hx
  intro P A X t f g hP hmass hk hkBound hNorm hXlo hXhi hf hSourceNorm hTargetNorm
  let y : ℝ := L x
  let R : ℕ := Nat.ceil (y ^ ((52 : ℝ) / 100))
  let B : ℕ := 2 * ((2 * R + 1) * A.stepBound) + 1
  let D : Finset ℤ := dyad X
  have hypos : 0 < y := by linarith [hy]
  have hCblock64 : 64 ≤ Cblock := by dsimp [Cblock]; nlinarith [hC₂, F.C₀_pos]
  have hy03 : 64 ≤ y ^ ((3 : ℝ) / 100) := by
    simpa [y] using hCblock64.trans hCblock
  have hy52 : 1 < y ^ ((52 : ℝ) / 100) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hy (by norm_num :
      (3 : ℝ) / 100 ≤ (52 : ℝ) / 100)
    linarith
  have hR2 : 2 ≤ R := by
    dsimp [R]
    rw [Nat.add_one_le_ceil_iff]
    exact_mod_cast hy52
  have hRlow : y ^ ((52 : ℝ) / 100) ≤ (R : ℝ) := by
    dsimp [R]
    exact Nat.le_ceil _
  have hBpos : 0 < B := by dsimp [B]; omega
  have hBM : 2 * ((2 * (R : ℤ) + 1) * (A.stepBound : ℤ)) < (B : ℤ) := by
    dsimp [B]
    push_cast
    omega
  have hBexp : (B : ℝ) ≤ Real.exp (y ^ ((51 : ℝ) / 100)) := by
    simpa [B, R, y, Cblock] using
      blockLength_exp_bound A hP hy hC₂ hk hkBound hCblock
  have hxpow : 1 < x ^ γ := Real.one_lt_rpow hx hγ
  have hX : 1 ≤ X := le_trans hxpow.le hXlo
  have hDcard : 0 < (D.card : ℝ) ∧ (D.card : ℝ) ≤ 2 * X := by
    simpa [D, dyad] using dyad_card_bounds hX
  have hMoment : A.averagedMoment R X ≤
      y ^ (-(E + 1) * (2 * (R : ℝ))) := by
    have h := hMoment P A hP hmass hk hkBound hNorm X hXlo hXhi
    have hRceil : R = Nat.ceil (L x ^ (0.52 : ℝ)) := by
      dsimp [R, y]
      congr 1
      norm_num
    rw [hRceil]
    simpa [y] using h
  have hrootSum0 : 0 ≤ ∑ n ∈ D, A.rootMoment R n := by
    apply Finset.sum_nonneg
    intro n hn
    exact rootMoment_nonneg A hP n R (by omega)
  have hrootSum : ∑ n ∈ D, A.rootMoment R n ≤
      2 * X * y ^ (-2 * (E + 1) * (R : ℝ)) := by
    have havg : (∑ n ∈ D, A.rootMoment R n) / (D.card : ℝ) ≤
        y ^ (-(E + 1) * (2 * (R : ℝ))) := by
      simpa [Model.averagedMoment, D, dyad] using hMoment
    have hdiv := (div_le_iff₀ hDcard.1).mp havg
    have hpowEq : y ^ (-(E + 1) * (2 * (R : ℝ))) =
        y ^ (-2 * (E + 1) * (R : ℝ)) := by
      congr 1
      ring
    calc
      _ ≤ y ^ (-(E + 1) * (2 * (R : ℝ))) * (D.card : ℝ) := hdiv
      _ ≤ y ^ (-(E + 1) * (2 * (R : ℝ))) * (2 * X) :=
        mul_le_mul_of_nonneg_left hDcard.2 (Real.rpow_nonneg (le_of_lt hypos) _)
      _ = 2 * X * y ^ (-(E + 1) * (2 * (R : ℝ))) := by ring
      _ = 2 * X * y ^ (-2 * (E + 1) * (R : ℝ)) := by rw [hpowEq]
  let sourceSq : ℝ := ∑ n ∈ D, ∑ a : A.Labels,
    A.stateMass (n, a) * ‖f n‖ ^ 2
  let targetSq : ℝ := ∑ z ∈ t, A.stateMass z * ‖g z‖ ^ 2
  have hSourceRaw0 : 0 ≤ ∑ z ∈ D.product Finset.univ,
      A.stateMass z * ‖f z.1‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (stateMass_nonneg_of_admissible A hP z) (sq_nonneg _)
  have hSourceNormSq :
      A.normOn (D.product Finset.univ) (fun z => f z.1) ^ 2 = sourceSq := by
    unfold Model.normOn
    rw [Real.sq_sqrt hSourceRaw0]
    simpa [sourceSq, blockStates] using
      (sum_blockStates A D (fun z => A.stateMass z * ‖f z.1‖ ^ 2))
  have hTargetRaw0 : 0 ≤ targetSq := by
    dsimp [targetSq]
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (stateMass_nonneg_of_admissible A hP z) (sq_nonneg _)
  have hTargetNormSq : A.normOn t g ^ 2 = targetSq := by
    unfold Model.normOn
    rw [Real.sq_sqrt hTargetRaw0]
  have hSourceHyp :
      A.normOn (D.product Finset.univ) (fun z => f z.1) ≤
        Real.sqrt X * y ^ C₃ := by
    simpa [D, dyad, y, L] using hSourceNorm
  have hTargetHyp : A.normOn t g ≤ Real.sqrt X * y ^ C₃ := by
    simpa [y, L] using hTargetNorm
  have hSourceSqBound : sourceSq ≤ X * y ^ (2 * C₃) := by
    have hpowSq : (y ^ C₃) ^ 2 = y ^ (2 * C₃) := by
      calc
        (y ^ C₃) ^ 2 = (y ^ C₃) ^ (2 : ℝ) := (Real.rpow_natCast _ _).symm
        _ = y ^ (C₃ * 2) := (Real.rpow_mul (le_of_lt hypos) C₃ 2).symm
        _ = y ^ (2 * C₃) := by congr 1 <;> ring
    calc
      sourceSq = A.normOn (D.product Finset.univ) (fun z => f z.1) ^ 2 := hSourceNormSq.symm
      _ ≤ (Real.sqrt X * y ^ C₃) ^ 2 :=
        (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).2 hSourceHyp
      _ = X * y ^ (2 * C₃) := by
        rw [mul_pow, Real.sq_sqrt (by positivity), hpowSq]
  have hTargetSqBound : targetSq ≤ X * y ^ (2 * C₃) := by
    have hpowSq : (y ^ C₃) ^ 2 = y ^ (2 * C₃) := by
      calc
        (y ^ C₃) ^ 2 = (y ^ C₃) ^ (2 : ℝ) := (Real.rpow_natCast _ _).symm
        _ = y ^ (C₃ * 2) := (Real.rpow_mul (le_of_lt hypos) C₃ 2).symm
        _ = y ^ (2 * C₃) := by congr 1 <;> ring
    calc
      targetSq = A.normOn t g ^ 2 := hTargetNormSq.symm
      _ ≤ (Real.sqrt X * y ^ C₃) ^ 2 :=
        (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).2 hTargetHyp
      _ = X * y ^ (2 * C₃) := by
        rw [mul_pow, Real.sq_sqrt (by positivity), hpowSq]
  have hPair := dyad_chunk_pairing_bound A hP D (Int.ceil X) B R hBpos hBM hR2
    t f g Cf (by simpa [D, dyad] using hf)
  have hPair' : ‖A.pairing X t f g‖ ≤
      Real.sqrt (2 * targetSq * sourceSq ^ (1 - (R : ℝ)⁻¹) *
        ((B : ℝ) * Real.exp (2 * Cf * Real.sqrt y) *
          (∑ n ∈ D, A.rootMoment R n)) ^ (R : ℝ)⁻¹) := by
    simpa [Model.pairing, targetSq, sourceSq, D, dyad, y, L] using hPair
  have hClean := packet_scalar_cleanup E C₃ Cf X y R B targetSq sourceSq
    (∑ n ∈ D, A.rootMoment R n) hy hX hR2 hRlow hBexp
    hTargetRaw0 hTargetSqBound (by
      dsimp [sourceSq]
      exact Finset.sum_nonneg fun n hn =>
        Finset.sum_nonneg fun a ha =>
          mul_nonneg (stateMass_nonneg_of_admissible A hP (n, a)) (sq_nonneg _))
    hSourceSqBound hrootSum0 hrootSum
  calc
    ‖A.pairing X t f g‖ ≤ _ := hPair'
    _ ≤ K * X * y ^ (-E + 2 * C₃) := by simpa [K] using hClean

example : PairingFromMomentTask := PairingFromMomentTask_proof



end Erdos821.S2Core
