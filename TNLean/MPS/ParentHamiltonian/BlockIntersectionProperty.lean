/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.IntersectionProperty
import TNLean.MPS.ParentHamiltonian.BoundaryMatrixIdentities
import TNLean.MPS.MPDO.BiCFDerivation.Selectors

/-!
# Block-diagonal intersection identities

Algebraic identities for the block-diagonal parent-Hamiltonian intersection
argument: the left-boundary trace decomposition, the blockwise boundary-matrix
compatibilities \(A_bC_a=D_bA_a\), and the one-step block-intersection
equality for the join of the block ground spaces.

## References

* [Perez-Garcia--Verstraete--Wolf--Cirac 2007], Theorem 12, proof around
  \(A_b C_a=D_b A_a\) and \(E=\sum_a C_a A_a^\dagger\).
* [Cirac--Perez-Garcia--Schuch--Verstraete 2021], Section IV.C, lines
  2120--2129.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- A vector in the linear sum of finitely many subspaces can be written as a
sum of vectors from those subspaces. -/
theorem exists_sum_mem_of_mem_iSup_fin
    {ι V : Type*} [Fintype ι]
    [AddCommMonoid V] [Module ℂ V]
    (p : ι → Submodule ℂ V) {v : V}
    (hv : v ∈ ⨆ i, p i) :
    ∃ x : ι → V, (∀ i, x i ∈ p i) ∧ v = ∑ i, x i := by
  classical
  refine Submodule.iSup_induction (p := p) (x := v) hv ?_ ?_ ?_
  · intro i y hy
    refine ⟨fun k => if k = i then y else 0, ?_, ?_⟩
    · intro k
      by_cases h : k = i
      · subst k
        simpa using hy
      · simp [h]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        simp [hk]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
  · refine ⟨fun _ => 0, ?_, by simp⟩
    intro i
    exact Submodule.zero_mem _
  · intro y z hy hz
    rcases hy with ⟨fy, hfy, rfl⟩
    rcases hz with ⟨fz, hfz, rfl⟩
    refine ⟨fun i => fy i + fz i, ?_, by simp [Finset.sum_add_distrib]⟩
    intro i
    exact Submodule.add_mem _ (hfy i) (hfz i)

/-- The left-boundary summand in the PGVWC block-diagonal intersection proof:
\[
  \sigma\longmapsto
  \operatorname{tr}(A_{\sigma_{n+2}} C_{\sigma_1}
    A_{\sigma_2}\cdots A_{\sigma_{n+1}}).
\]
-/
noncomputable def pgvwc07LeftBoundaryComponent
    (A : MPSTensor d D) (C : Fin d → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    NSiteSpace d (n + 2) :=
  fun σ => Matrix.trace
    (A (σ (Fin.last (n + 1))) * C (σ 0) *
      evalWord A (List.ofFn (Fin.tail (Fin.init σ))))

/-- Fixing the first physical index in the PGVWC left-boundary summand gives the
usual ground-space parametrization with boundary matrix \(C_a\). -/
theorem restrictFirst_pgvwc07LeftBoundaryComponent
    (A : MPSTensor d D) (C : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (n : ℕ) (a : Fin d) :
    restrictFirst (pgvwc07LeftBoundaryComponent A C n) a =
      groundSpaceMap A (n + 1) (C a) := by
  ext σ
  have hσ :
      σ = Fin.snoc (Fin.init σ) (σ (Fin.last n)) := by
    exact (Fin.snoc_init_self σ).symm
  have hinit :
      (Fin.init (Fin.cons a σ : Fin (n + 2) → Fin d) : Fin (n + 1) → Fin d) =
        (Fin.cons a (Fin.init σ : Fin n → Fin d) : Fin (n + 1) → Fin d) := by
    ext k
    cases k using Fin.cases with
    | zero => simp [Fin.init, Fin.cons]
    | succ k => simp [Fin.init, Fin.cons]
  have htail :
      (Fin.tail
        (Fin.init (Fin.cons a σ : Fin (n + 2) → Fin d) : Fin (n + 1) → Fin d) :
          Fin n → Fin d) =
        (Fin.init σ : Fin n → Fin d) := by
    rw [hinit]
    exact @Fin.tail_cons n (fun _ => Fin d) a (Fin.init σ : Fin n → Fin d)
  have hlast :
      (Fin.cons a σ : Fin (n + 2) → Fin d) (Fin.last (n + 1)) = σ (Fin.last n) := by
    change (Fin.cons a σ : Fin (n + 2) → Fin d) (Fin.succ (Fin.last n)) =
      σ (Fin.last n)
    rw [Fin.cons_succ]
  have hfirst : (Fin.cons a σ : Fin (n + 2) → Fin d) 0 = a := by
    rw [Fin.cons_zero]
  simp only [restrictFirst_apply, pgvwc07LeftBoundaryComponent, groundSpaceMap_apply,
    htail, hlast, hfirst]
  rw [hσ, evalWord_ofFn_snoc]
  simp only [Fin.snoc_last, Fin.init_snoc]
  calc
    Matrix.trace (A (σ (Fin.last n)) * C a * evalWord A (List.ofFn (Fin.init σ)))
        = Matrix.trace ((A (σ (Fin.last n)) * C a) *
            evalWord A (List.ofFn (Fin.init σ))) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (evalWord A (List.ofFn (Fin.init σ)) *
        (A (σ (Fin.last n)) * C a)) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (evalWord A (List.ofFn (Fin.init σ)) *
        A (σ (Fin.last n)) * C a) := by rw [Matrix.mul_assoc]

/-- Boundary form of a ground-space vector after fixing the final physical index. -/
theorem groundSpaceMap_snoc_trace_boundary
    (A : MPSTensor d D) {n : ℕ} (X : Matrix (Fin D) (Fin D) ℂ)
    (w : Fin n → Fin d) (b : Fin d) :
    groundSpaceMap A (n + 1) X (Fin.snoc w b) =
      Matrix.trace ((A b * X) * evalWord A (List.ofFn w)) := by
  simp only [groundSpaceMap_apply, evalWord_ofFn_snoc]
  calc
    Matrix.trace (evalWord A (List.ofFn w) * A b * X)
        = Matrix.trace (evalWord A (List.ofFn w) * (A b * X)) := by
            rw [Matrix.mul_assoc]
    _ = Matrix.trace ((A b * X) * evalWord A (List.ofFn w)) := by
            rw [Matrix.trace_mul_comm]

/-- Boundary form of a ground-space vector after fixing the initial physical index. -/
theorem groundSpaceMap_cons_trace_boundary
    (A : MPSTensor d D) {n : ℕ} (X : Matrix (Fin D) (Fin D) ℂ)
    (a : Fin d) (w : Fin n → Fin d) :
    groundSpaceMap A (n + 1) X (Fin.cons a w) =
      Matrix.trace ((X * A a) * evalWord A (List.ofFn w)) := by
  simp only [groundSpaceMap_apply, evalWord_ofFn_cons]
  calc
    Matrix.trace (A a * evalWord A (List.ofFn w) * X)
        = Matrix.trace ((A a * evalWord A (List.ofFn w)) * X) := by
            rw [Matrix.mul_assoc]
    _ = Matrix.trace (X * (A a * evalWord A (List.ofFn w))) := by
            rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((X * A a) * evalWord A (List.ofFn w)) := by
            rw [Matrix.mul_assoc]

/-- Boundary form of a ground-space vector after fixing the initial and final
physical indices. -/
theorem groundSpaceMap_cons_snoc_trace_boundary
    (A : MPSTensor d D) {n : ℕ} (X : Matrix (Fin D) (Fin D) ℂ)
    (a b : Fin d) (w : Fin n → Fin d) :
    groundSpaceMap A (n + 2) X (Fin.cons a (Fin.snoc w b)) =
      Matrix.trace ((A b * X * A a) * evalWord A (List.ofFn w)) := by
  simp only [groundSpaceMap_apply, evalWord_ofFn_cons, evalWord_ofFn_snoc]
  calc
    Matrix.trace ((A a * (evalWord A (List.ofFn w) * A b)) * X)
        = Matrix.trace (((A a * evalWord A (List.ofFn w)) * A b) * X) := by
            rw [← Matrix.mul_assoc (A a) (evalWord A (List.ofFn w)) (A b)]
    _ = Matrix.trace ((A a * evalWord A (List.ofFn w)) * (A b * X)) := by
            rw [Matrix.mul_assoc]
    _ = Matrix.trace ((A b * X) * (A a * evalWord A (List.ofFn w))) := by
            rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((A b * X * A a) * evalWord A (List.ofFn w)) := by
            simp [Matrix.mul_assoc]

/-- The left-boundary summand is a ground-space vector once the PGVWC boundary
identity \(A_bC_a=A_bEA_a\) holds. -/
theorem pgvwc07LeftBoundaryComponent_eq_groundSpaceMap
    (A : MPSTensor d D) (C : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (E : Matrix (Fin D) (Fin D) ℂ) (n : ℕ)
    (hACE : ∀ a b : Fin d, A b * C a = A b * E * A a) :
    pgvwc07LeftBoundaryComponent A C n = groundSpaceMap A (n + 2) E := by
  ext σ
  let M := evalWord A (List.ofFn (Fin.tail (Fin.init σ)))
  let a := σ 0
  let b := σ (Fin.last (n + 1))
  have hEvalInit :
      evalWord A (List.ofFn (Fin.init σ)) = A a * M := by
    have hinit : Fin.cons a (Fin.tail (Fin.init σ)) = Fin.init σ := by
      dsimp [a]
      exact Fin.cons_self_tail (Fin.init σ)
    rw [← hinit]
    exact evalWord_ofFn_cons A a (Fin.tail (Fin.init σ))
  have hEval :
      evalWord A (List.ofFn σ) = (A a * M) * A b := by
    have hσ : Fin.snoc (Fin.init σ) b = σ := by
      simp [b]
    rw [← hσ]
    calc
      evalWord A (List.ofFn (Fin.snoc (Fin.init σ) b))
          = evalWord A (List.ofFn (Fin.init σ)) * A b :=
              evalWord_ofFn_snoc A (Fin.init σ) b
      _ = (A a * M) * A b := by rw [hEvalInit]
  change Matrix.trace (A b * C a * M) =
    Matrix.trace (evalWord A (List.ofFn σ) * E)
  rw [hEval]
  calc
    Matrix.trace (A b * C a * M)
        = Matrix.trace ((A b * E * A a) * M) := by
            rw [hACE a b]
    _ = Matrix.trace ((A b * E) * (A a * M)) := by
            rw [Matrix.mul_assoc]
    _ = Matrix.trace ((A a * M) * (A b * E)) := by
            rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (((A a * M) * A b) * E) := by
            rw [← Matrix.mul_assoc]

/-- The left-boundary summand belongs to \(G_{n+2}(A)\) once the PGVWC
boundary identity \(A_bC_a=A_bEA_a\) holds. -/
theorem pgvwc07LeftBoundaryComponent_mem_groundSpace
    (A : MPSTensor d D) (C : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (E : Matrix (Fin D) (Fin D) ℂ) (n : ℕ)
    (hACE : ∀ a b : Fin d, A b * C a = A b * E * A a) :
    pgvwc07LeftBoundaryComponent A C n ∈ groundSpace A (n + 2) := by
  rw [pgvwc07LeftBoundaryComponent_eq_groundSpaceMap A C E n hACE]
  rw [groundSpace, LinearMap.mem_range]
  exact ⟨E, rfl⟩

/-- A finite sum of PGVWC left-boundary summands lies in the supremum of the
corresponding block ground spaces. -/
theorem pgvwc07_sum_leftBoundaryComponents_mem_iSup_groundSpace
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    (C : (j : Fin r) → Fin d → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (E : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (n : ℕ)
    (hACE : ∀ j : Fin r, ∀ a b : Fin d,
      A j b * C j a = A j b * E j * A j a) :
    (∑ j : Fin r, pgvwc07LeftBoundaryComponent (A j) (C j) n) ∈
      ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  classical
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.mem_iSup_of_mem j
    (pgvwc07LeftBoundaryComponent_mem_groundSpace (A j) (C j) (E j) n (hACE j))

/-- A common product span makes the local block spaces an internal direct sum.

Suppose
\[
  \operatorname{span}\{(A^1_w,\ldots,A^r_w): |w|=n\}
  =
  \prod_j M_{D_j}(\mathbb C).
\]
If \(\phi_j\in G_n(A^j)\) and \(\sum_j\phi_j=0\), write
\[
  \phi_j(\sigma)=\operatorname{tr}(A^j_\sigma X_j).
\]
Then, for every word \(w\) of length \(n\),
\[
  \sum_j\operatorname{tr}(X_jA^j_w)=0.
\]
The product span and nondegeneracy of the product trace pairing force
\(X_j=0\) for every \(j\), hence \(\phi_j=0\). -/
theorem groundSpace_iSupIndep_of_wordTupleSpanTop
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n) :
    iSupIndep fun j : Fin r => groundSpace (A j) n := by
  classical
  rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero]
  intro s φ hφ hsum j hj
  have hMatrix : ∀ i : Fin r, i ∈ s →
      ∃ X : Matrix (Fin (dim i)) (Fin (dim i)) ℂ,
        groundSpaceMap (A i) n X = φ i := by
    intro i hi
    simpa [groundSpace] using hφ i hi
  let X : (i : Fin r) → Matrix (Fin (dim i)) (Fin (dim i)) ℂ :=
    fun i => if hi : i ∈ s then Classical.choose (hMatrix i hi) else 0
  have hX : ∀ i : Fin r, ∀ hi : i ∈ s, groundSpaceMap (A i) n (X i) = φ i := by
    intro i hi
    dsimp [X]
    rw [dif_pos hi]
    exact Classical.choose_spec (hMatrix i hi)
  have hsum_all : (∑ i : Fin r, groundSpaceMap (A i) n (X i)) = 0 := by
    calc
      (∑ i : Fin r, groundSpaceMap (A i) n (X i))
          = s.sum (fun i => groundSpaceMap (A i) n (X i)) := by
              symm
              apply Finset.sum_subset (Finset.subset_univ s)
              intro i _ hi
              simp [X, hi]
      _ = s.sum φ := by
              exact Finset.sum_congr rfl fun i hi => hX i hi
      _ = 0 := by simpa using hsum
  have hTraceEval : ∀ w : Fin n → Fin d,
      (∑ i : Fin r, Matrix.trace (evalWord (A i) (List.ofFn w) * X i)) = 0 := by
    intro w
    simpa [groundSpaceMap_apply] using congrFun hsum_all w
  have hTrace : ∀ w : Fin n → Fin d,
      (∑ i : Fin r, Matrix.trace (X i * evalWord (A i) (List.ofFn w))) = 0 := by
    intro w
    calc
      (∑ i : Fin r, Matrix.trace (X i * evalWord (A i) (List.ofFn w)))
          = ∑ i : Fin r, Matrix.trace (evalWord (A i) (List.ofFn w) * X i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              exact Matrix.trace_mul_comm (X i) (evalWord (A i) (List.ofFn w))
      _ = 0 := hTraceEval w
  have hXzero : X j = 0 :=
    block_matrices_eq_zero_of_wordTupleSpanTop_trace A hSpan X hTrace j
  calc
    φ j = groundSpaceMap (A j) n (X j) := (hX j hj).symm
    _ = 0 := by simp [hXzero]

/-- Equality of block matrices from equality of their trace pairings against a
common word family.

If the blockwise word tuples of length \(n\) span the product matrix algebra,
and if, for every length-\(n\) word \(w\),
\[
  \sum_j\operatorname{tr}(X_jA^j_w)
  =
  \sum_j\operatorname{tr}(Y_jA^j_w)
\]
then \(X_j=Y_j\) for every block \(j\). -/
theorem block_matrices_eq_of_wordTupleSpanTop_trace
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (X Y : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hTrace : ∀ w : Fin n → Fin d,
      (∑ j : Fin r, Matrix.trace (X j * evalWord (A j) (List.ofFn w))) =
      (∑ j : Fin r, Matrix.trace (Y j * evalWord (A j) (List.ofFn w)))) :
    ∀ j : Fin r, X j = Y j := by
  intro j
  have hzero := block_matrices_eq_zero_of_wordTupleSpanTop_trace A hSpan
    (fun k => X k - Y k) (by
      intro w
      simpa [Matrix.sub_mul, Matrix.trace_sub, Finset.sum_sub_distrib, sub_eq_zero]
        using sub_eq_zero.mpr (hTrace w)) j
  exact sub_eq_zero.mp hzero

/-- Blockwise boundary identities from membership of a PGVWC left-boundary
trace decomposition in the block ground-space sum.

This is the coefficient-comparison direction in the proof of
[Perez-Garcia--Verstraete--Wolf--Cirac 2007], Theorem 12.  If a vector
with coefficients
\[
  \sum_j\operatorname{tr}(A^j_b C^j_a A^j_w)
\]
already lies in \(\bigvee_j G_{n+2}(A^j)\), and the length-\(n\) simultaneous
word tuples span the product matrix algebra, then each block has a boundary
matrix \(E_j\) such that
\[
  A^j_bC^j_a=A^j_bE_jA^j_a.
\] -/
theorem pgvwc07_boundary_identities_of_leftBoundaryComponent_mem_iSup
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (C : (j : Fin r) → Fin d → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (ψ : NSiteSpace d (n + 2))
    (hψ : ψ = ∑ j : Fin r, pgvwc07LeftBoundaryComponent (A j) (C j) n)
    (hmem : ψ ∈ ⨆ j : Fin r, groundSpace (A j) (n + 2)) :
    ∃ E : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ∀ j : Fin r, ∀ a b : Fin d, A j b * C j a = A j b * E j * A j a := by
  classical
  obtain ⟨φ, hφmem, hφsum⟩ :=
    exists_sum_mem_of_mem_iSup_fin
      (fun j : Fin r => groundSpace (A j) (n + 2)) hmem
  have hMatrix : ∀ j : Fin r,
      ∃ E : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        φ j = groundSpaceMap (A j) (n + 2) E := by
    intro j
    have hφj := hφmem j
    rw [groundSpace, LinearMap.mem_range] at hφj
    rcases hφj with ⟨E, hE⟩
    exact ⟨E, hE.symm⟩
  choose E hE using hMatrix
  refine ⟨E, ?_⟩
  intro j a b
  have hCoeff : ∀ w : Fin n → Fin d,
      (∑ k : Fin r,
        Matrix.trace ((A k b * C k a) * evalWord (A k) (List.ofFn w))) =
      (∑ k : Fin r,
        Matrix.trace ((A k b * E k * A k a) * evalWord (A k) (List.ofFn w))) := by
    intro w
    have hLeftEval :
        ψ (Fin.cons a (Fin.snoc w b)) =
          ∑ k : Fin r,
            Matrix.trace ((A k b * C k a) * evalWord (A k) (List.ofFn w)) := by
      calc
        ψ (Fin.cons a (Fin.snoc w b))
            = (∑ k : Fin r, pgvwc07LeftBoundaryComponent (A k) (C k) n)
                (Fin.cons a (Fin.snoc w b)) := by
              rw [hψ]
        _ = ∑ k : Fin r,
              pgvwc07LeftBoundaryComponent (A k) (C k) n
                (Fin.cons a (Fin.snoc w b)) := by
              simp
        _ = ∑ k : Fin r,
              restrictFirst (pgvwc07LeftBoundaryComponent (A k) (C k) n) a
                (Fin.snoc w b) := by
              rfl
        _ = ∑ k : Fin r,
              groundSpaceMap (A k) (n + 1) (C k a) (Fin.snoc w b) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              rw [restrictFirst_pgvwc07LeftBoundaryComponent]
        _ = ∑ k : Fin r,
              Matrix.trace ((A k b * C k a) * evalWord (A k) (List.ofFn w)) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              exact groundSpaceMap_snoc_trace_boundary (A k) (C k a) w b
    have hRightEval :
        ψ (Fin.cons a (Fin.snoc w b)) =
          ∑ k : Fin r,
            Matrix.trace ((A k b * E k * A k a) * evalWord (A k) (List.ofFn w)) := by
      calc
        ψ (Fin.cons a (Fin.snoc w b))
            = (∑ k : Fin r, φ k) (Fin.cons a (Fin.snoc w b)) := by
              rw [hφsum]
        _ = ∑ k : Fin r, φ k (Fin.cons a (Fin.snoc w b)) := by
              simp
        _ = ∑ k : Fin r,
              groundSpaceMap (A k) (n + 2) (E k) (Fin.cons a (Fin.snoc w b)) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              rw [hE k]
        _ = ∑ k : Fin r,
              Matrix.trace ((A k b * E k * A k a) *
                evalWord (A k) (List.ofFn w)) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              exact groundSpaceMap_cons_snoc_trace_boundary (A k) (E k) a b w
    exact hLeftEval.symm.trans hRightEval
  exact block_matrices_eq_of_wordTupleSpanTop_trace A hSpan
    (fun k => A k b * C k a) (fun k => A k b * E k * A k a) hCoeff j

/-- Boundary-matrix compatibility from equality of the two coefficient
decompositions in the PGVWC block-diagonal intersection proof.

For fixed physical indices \(a,b\), the coefficient comparison in
[Perez-Garcia--Verstraete--Wolf--Cirac 2007], Theorem 12, gives
\[
  \sum_j \operatorname{tr}\!\left(
    A^j_b C^j_a A^j_{i_2}\cdots A^j_{i_m}\right)
  =
  \sum_j \operatorname{tr}\!\left(
    D^j_b A^j_a A^j_{i_2}\cdots A^j_{i_m}\right)
\]
for every middle word.  Under the common word-span condition, this implies
\[
  A^j_b C^j_a=D^j_b A^j_a
\]
for every block \(j\).
-/
theorem pgvwc07_blockwise_compatibility_of_trace_decomposition
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {m : ℕ} (hSpan : WordTupleSpanTop A m)
    (C Dmat : (j : Fin r) → Fin d → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hCoeff : ∀ a b : Fin d, ∀ w : Fin m → Fin d,
      (∑ j : Fin r, Matrix.trace ((A j b * C j a) * evalWord (A j) (List.ofFn w))) =
      (∑ j : Fin r, Matrix.trace ((Dmat j b * A j a) * evalWord (A j) (List.ofFn w)))) :
    ∀ j : Fin r, ∀ a b : Fin d, A j b * C j a = Dmat j b * A j a := by
  intro j a b
  exact block_matrices_eq_of_wordTupleSpanTop_trace A hSpan
    (fun k => A k b * C k a) (fun k => Dmat k b * A k a) (hCoeff a b) j

/-- Word-valued boundary-matrix compatibility from equality of the two
coefficient decompositions in the Perez-Garcia--Verstraete--Wolf--Cirac
block-diagonal intersection proof.

This is the same extraction as
`pgvwc07_blockwise_compatibility_of_trace_decomposition`, with the boundary
letters replaced by words.  If, for every wrapped word \(\beta\), complementary
word \(\rho\), and middle word \(w\), the two trace decompositions agree,
then the blockwise matrices satisfy
\[
  A^j_\beta C^j_\rho=D^j_\beta A^j_\rho .
\]
This is the word form needed for the boundary-crossing comparison in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1451. -/
theorem pgvwc07_blockwise_word_compatibility_of_trace_decomposition
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {m K M : ℕ} (hSpan : WordTupleSpanTop A m)
    (C : (j : Fin r) → (Fin M → Fin d) →
      Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (Dmat : (j : Fin r) → (Fin K → Fin d) →
      Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hCoeff : ∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
      ∀ w : Fin m → Fin d,
        (∑ j : Fin r,
          Matrix.trace
            ((evalWord (A j) (List.ofFn β) * C j ρ) *
              evalWord (A j) (List.ofFn w))) =
        (∑ j : Fin r,
          Matrix.trace
            ((Dmat j β * evalWord (A j) (List.ofFn ρ)) *
              evalWord (A j) (List.ofFn w)))) :
    ∀ j : Fin r, ∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
      evalWord (A j) (List.ofFn β) * C j ρ =
        Dmat j β * evalWord (A j) (List.ofFn ρ) := by
  intro j ρ β
  exact block_matrices_eq_of_wordTupleSpanTop_trace A hSpan
    (fun k => evalWord (A k) (List.ofFn β) * C k ρ)
    (fun k => Dmat k β * evalWord (A k) (List.ofFn ρ))
    (hCoeff ρ β) j

/-- Fixed complementary-word compatibility from equality of the two coefficient
decompositions in the Perez-Garcia--Verstraete--Wolf--Cirac block-diagonal
intersection proof.

Fix a complementary word \(\rho\). If, for every wrapped word \(\beta\) and
middle word \(w\), the trace decompositions agree with
\[
  D^j_\beta=X_jA^j_\beta ,
\]
then the blockwise matrices satisfy
\[
  A^j_\beta C^j_\rho=(X_jA^j_\beta)A^j_\rho .
\]
This is the fixed-\(\rho\) form of the comparison in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1451. -/
theorem pgvwc07_fixed_complementary_word_compatibility_of_trace_decomposition
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {m K M : ℕ} (hSpan : WordTupleSpanTop A m)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (C : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (ρ : Fin M → Fin d)
    (hCoeff : ∀ β : Fin K → Fin d, ∀ w : Fin m → Fin d,
      (∑ j : Fin r,
        Matrix.trace
          ((evalWord (A j) (List.ofFn β) * C j) *
            evalWord (A j) (List.ofFn w))) =
      (∑ j : Fin r,
        Matrix.trace
          (((X j * evalWord (A j) (List.ofFn β)) *
              evalWord (A j) (List.ofFn ρ)) *
            evalWord (A j) (List.ofFn w)))) :
    ∀ j : Fin r, ∀ β : Fin K → Fin d,
      evalWord (A j) (List.ofFn β) * C j =
        (X j * evalWord (A j) (List.ofFn β)) *
          evalWord (A j) (List.ofFn ρ) := by
  intro j β
  exact block_matrices_eq_of_wordTupleSpanTop_trace A hSpan
    (fun k => evalWord (A k) (List.ofFn β) * C k)
    (fun k =>
      (X k * evalWord (A k) (List.ofFn β)) * evalWord (A k) (List.ofFn ρ))
    (hCoeff β) j

/-- Word-valued compatibility for a block-diagonal boundary matrix.

Assume the right trace decomposition has
\[
  D^j_\beta=(X_jA^j_\beta).
\]
Then the word-valued trace comparison gives
\[
  A^j_\beta C^j_\rho=(X_jA^j_\beta)A^j_\rho .
\]
This is the exact compatibility hypothesis used by the complementary-word
boundary theorem, following the boundary-crossing comparison in
arXiv:quant-ph/0608197, Theorem 12, proof lines 1446--1451. -/
theorem pgvwc07_complementary_word_compatibility_of_trace_decomposition
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {m K M : ℕ} (hSpan : WordTupleSpanTop A m)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (C : (j : Fin r) → (Fin M → Fin d) →
      Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hCoeff : ∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
      ∀ w : Fin m → Fin d,
        (∑ j : Fin r,
          Matrix.trace
            ((evalWord (A j) (List.ofFn β) * C j ρ) *
              evalWord (A j) (List.ofFn w))) =
        (∑ j : Fin r,
          Matrix.trace
            (((X j * evalWord (A j) (List.ofFn β)) *
                evalWord (A j) (List.ofFn ρ)) *
              evalWord (A j) (List.ofFn w)))) :
    ∀ j : Fin r, ∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
      evalWord (A j) (List.ofFn β) * C j ρ =
        (X j * evalWord (A j) (List.ofFn β)) *
          evalWord (A j) (List.ofFn ρ) := by
  exact
    pgvwc07_blockwise_word_compatibility_of_trace_decomposition
      (A := A) (m := m) (K := K) (M := M) hSpan C
      (fun j β => X j * evalWord (A j) (List.ofFn β)) hCoeff

/-- Complementary-word boundary identities from the PGVWC trace decompositions.

Assume the right trace decomposition has
\[
  D^j_\beta=X_jA^j_\beta .
\]
If the two trace decompositions agree for every wrapped word \(\beta\),
complementary word \(\rho\), and middle word \(w\), then the normalization
\(\sum_\rho A^j_\rho A^{j\dagger}_\rho=I\) and the compatibility identity give,
for every block \(j\) and complementary word \(\rho\), a matrix \(E_{j,\rho}\)
such that
\[
  (X_jA^j_\beta)A^j_\rho=A^j_\beta E_{j,\rho}.
\]
This is the word-valued form of arXiv:quant-ph/0608197, Theorem 12,
proof lines 1446--1451.

**Local fix (adjoint correction):** The source line writes
\(E^j=\sum_k C^j_kA^j_k\), while the normalization step uses
\(\sum_k A^j_kA^{j\dagger}_k=I\). The formal statement uses the adjointed
matrix \(E^j=\sum_k C^j_kA^{j\dagger}_k\), as recorded in
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. -/
theorem pgvwc07_complementary_word_boundary_identities_of_trace_decomposition
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {m K M : ℕ} (hSpan : WordTupleSpanTop A m)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (C : (j : Fin r) → (Fin M → Fin d) →
      Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    (hCoeff : ∀ ρ : Fin M → Fin d, ∀ β : Fin K → Fin d,
      ∀ w : Fin m → Fin d,
        (∑ j : Fin r,
          Matrix.trace
            ((evalWord (A j) (List.ofFn β) * C j ρ) *
              evalWord (A j) (List.ofFn w))) =
        (∑ j : Fin r,
          Matrix.trace
            (((X j * evalWord (A j) (List.ofFn β)) *
                evalWord (A j) (List.ofFn ρ)) *
              evalWord (A j) (List.ofFn w)))) :
    ∀ j : Fin r, ∀ ρ : Fin M → Fin d,
      ∃ E : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        ∀ β : Fin K → Fin d,
          (X j * evalWord (A j) (List.ofFn β)) *
              evalWord (A j) (List.ofFn ρ) =
            evalWord (A j) (List.ofFn β) * E := by
  intro j ρ
  exact pgvwc07_complementary_word_boundary_identities_of_compatibility
    (A := A j) (K := K) (M := M) (X := X j) (C := C j)
    (sum_evalWord_mul_conjTranspose_evalWord (A j) (hUnital j) M)
    ((pgvwc07_complementary_word_compatibility_of_trace_decomposition
      (A := A) (m := m) (K := K) (M := M) hSpan X C hCoeff) j)
    ρ

/-- The composed PGVWC open-segment step from the trace decompositions to
membership in the supremum of block ground spaces.

For a vector with left-boundary trace decomposition
\[
  \psi=\sum_j\alpha_j,\qquad
  \alpha_j(i_1,\ldots,i_{n+2})
    =\operatorname{tr}(A^j_{i_{n+2}}C^j_{i_1}A^j_{i_2}\cdots A^j_{i_{n+1}}),
\]
the trace-decomposition equality, the common word-span hypothesis, and the
normalization
\[
  \sum_a A^j_a A^{j\dagger}_a=I
\]
imply
\[
  \psi\in \bigvee_j G_{n+2}(A^j).
\]
This is the local membership step in
[Perez-Garcia--Verstraete--Wolf--Cirac 2007] (arXiv:quant-ph/0608197),
Theorem 12, proof lines 1446--1452. -/
theorem pgvwc07_mem_iSup_groundSpace_of_trace_decomposition
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (C Dmat : (j : Fin r) → Fin d → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    (hCoeff : ∀ a b : Fin d, ∀ w : Fin n → Fin d,
      (∑ j : Fin r, Matrix.trace ((A j b * C j a) * evalWord (A j) (List.ofFn w))) =
      (∑ j : Fin r, Matrix.trace ((Dmat j b * A j a) * evalWord (A j) (List.ofFn w))))
    (ψ : NSiteSpace d (n + 2))
    (hψ : ψ = ∑ j : Fin r, pgvwc07LeftBoundaryComponent (A j) (C j) n) :
    ψ ∈ ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  rw [hψ]
  let E : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
    fun j => ∑ a : Fin d, C j a * (A j a)ᴴ
  have hCompat :
      ∀ j : Fin r, ∀ a b : Fin d, A j b * C j a = Dmat j b * A j a :=
    pgvwc07_blockwise_compatibility_of_trace_decomposition A hSpan C Dmat hCoeff
  have hACE : ∀ j : Fin r, ∀ a b : Fin d,
      A j b * C j a = A j b * E j * A j a := by
    intro j
    exact (pgvwc07_boundary_matrix_identities_of_compatibility
      (A j) (C j) (Dmat j) (hUnital j) (hCompat j)).2
  exact pgvwc07_sum_leftBoundaryComponents_mem_iSup_groundSpace A C E n hACE

/-- One-step block intersection from block-ground-space restrictions.

Let \(\psi\) be an \((n+2)\)-site vector.  Suppose that fixing the first
physical index or the last physical index always gives a vector in
\[
  \bigvee_j G_{n+1}(A^j).
\]
Under the PGVWC common word-span hypothesis and the normalization
\[
  \sum_a A^j_a A^{j\dagger}_a=I,
\]
the vector itself lies in
\[
  \bigvee_j G_{n+2}(A^j).
\]
This is the restriction form of the open-segment step in
[Perez-Garcia--Verstraete--Wolf--Cirac 2007] (arXiv:quant-ph/0608197),
Theorem 12, proof lines 1442--1452. -/
theorem pgvwc07_mem_iSup_groundSpace_of_iSup_restrictions
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    (ψ : NSiteSpace d (n + 2))
    (hLeft : ∀ b : Fin d,
      restrictLast ψ b ∈ ⨆ j : Fin r, groundSpace (A j) (n + 1))
    (hRight : ∀ a : Fin d,
      restrictFirst ψ a ∈ ⨆ j : Fin r, groundSpace (A j) (n + 1)) :
    ψ ∈ ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  classical
  have hRightDecomp : ∀ a : Fin d,
      ∃ φ : (j : Fin r) → NSiteSpace d (n + 1),
        (∀ j : Fin r, φ j ∈ groundSpace (A j) (n + 1)) ∧
          restrictFirst ψ a = ∑ j : Fin r, φ j := by
    intro a
    exact exists_sum_mem_of_mem_iSup_fin
      (fun j : Fin r => groundSpace (A j) (n + 1)) (hRight a)
  choose φ hφmem hφsum using hRightDecomp
  have hRightMatrix : ∀ j : Fin r, ∀ a : Fin d,
      ∃ C : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        φ a j = groundSpaceMap (A j) (n + 1) C := by
    intro j a
    have hmem := hφmem a j
    rw [groundSpace, LinearMap.mem_range] at hmem
    rcases hmem with ⟨C, hC⟩
    exact ⟨C, hC.symm⟩
  choose C hC using hRightMatrix
  have hLeftDecomp : ∀ b : Fin d,
      ∃ χ : (j : Fin r) → NSiteSpace d (n + 1),
        (∀ j : Fin r, χ j ∈ groundSpace (A j) (n + 1)) ∧
          restrictLast ψ b = ∑ j : Fin r, χ j := by
    intro b
    exact exists_sum_mem_of_mem_iSup_fin
      (fun j : Fin r => groundSpace (A j) (n + 1)) (hLeft b)
  choose χ hχmem hχsum using hLeftDecomp
  have hLeftMatrix : ∀ j : Fin r, ∀ b : Fin d,
      ∃ Dmat : Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
        χ b j = groundSpaceMap (A j) (n + 1) Dmat := by
    intro j b
    have hmem := hχmem b j
    rw [groundSpace, LinearMap.mem_range] at hmem
    rcases hmem with ⟨Dmat, hDmat⟩
    exact ⟨Dmat, hDmat.symm⟩
  choose Dmat hDmat using hLeftMatrix
  have hψ :
      ψ = ∑ j : Fin r, pgvwc07LeftBoundaryComponent (A j) (C j) n := by
    apply eq_of_forall_restrictFirst_eq
    intro a
    calc
      restrictFirst ψ a = ∑ j : Fin r, φ a j := hφsum a
      _ = ∑ j : Fin r, groundSpaceMap (A j) (n + 1) (C j a) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            exact hC j a
      _ = ∑ j : Fin r, restrictFirst
            (pgvwc07LeftBoundaryComponent (A j) (C j) n) a := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [restrictFirst_pgvwc07LeftBoundaryComponent]
      _ = restrictFirst
            (∑ j : Fin r, pgvwc07LeftBoundaryComponent (A j) (C j) n) a := by
            ext σ
            simp [restrictFirst_apply]
  have hCoeff : ∀ a b : Fin d, ∀ w : Fin n → Fin d,
      (∑ j : Fin r,
        Matrix.trace ((A j b * C j a) * evalWord (A j) (List.ofFn w))) =
      (∑ j : Fin r,
        Matrix.trace ((Dmat j b * A j a) * evalWord (A j) (List.ofFn w))) := by
    intro a b w
    have hRightEval :
        ψ (Fin.cons a (Fin.snoc w b)) =
          ∑ j : Fin r,
            Matrix.trace ((A j b * C j a) * evalWord (A j) (List.ofFn w)) := by
      calc
        ψ (Fin.cons a (Fin.snoc w b))
            = restrictFirst ψ a (Fin.snoc w b) := by rfl
        _ = (∑ j : Fin r, φ a j) (Fin.snoc w b) := by
              exact congrFun (hφsum a) (Fin.snoc w b)
        _ = ∑ j : Fin r, φ a j (Fin.snoc w b) := by simp
        _ = ∑ j : Fin r,
            Matrix.trace ((A j b * C j a) * evalWord (A j) (List.ofFn w)) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [hC j a]
              exact groundSpaceMap_snoc_trace_boundary (A j) (C j a) w b
    have hLeftEval :
        ψ (Fin.snoc (Fin.cons a w) b) =
          ∑ j : Fin r,
            Matrix.trace ((Dmat j b * A j a) * evalWord (A j) (List.ofFn w)) := by
      calc
        ψ (Fin.snoc (Fin.cons a w) b)
            = restrictLast ψ b (Fin.cons a w) := by rfl
        _ = (∑ j : Fin r, χ b j) (Fin.cons a w) := by
              exact congrFun (hχsum b) (Fin.cons a w)
        _ = ∑ j : Fin r, χ b j (Fin.cons a w) := by simp
        _ = ∑ j : Fin r,
            Matrix.trace ((Dmat j b * A j a) * evalWord (A j) (List.ofFn w)) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [hDmat j b]
              exact groundSpaceMap_cons_trace_boundary (A j) (Dmat j b) a w
    calc
      (∑ j : Fin r,
        Matrix.trace ((A j b * C j a) * evalWord (A j) (List.ofFn w)))
          = ψ (Fin.cons a (Fin.snoc w b)) := hRightEval.symm
      _ = ψ (Fin.snoc (Fin.cons a w) b) := by
            rw [Fin.cons_snoc_eq_snoc_cons]
      _ = ∑ j : Fin r,
        Matrix.trace ((Dmat j b * A j a) * evalWord (A j) (List.ofFn w)) := hLeftEval
  exact pgvwc07_mem_iSup_groundSpace_of_trace_decomposition
    A hSpan C Dmat hUnital hCoeff ψ hψ

/-- One-step block intersection as a restriction characterization.

Under the PGVWC common word-span hypothesis and the normalization
\[
  \sum_a A^j_a A^{j\dagger}_a=I,
\]
membership of an \((n+2)\)-site vector in \(\bigvee_jG_{n+2}(A^j)\) is
equivalent to the two fixed-boundary conditions
\[
  \psi(-,b)\in\bigvee_jG_{n+1}(A^j),
  \qquad
  \psi(a,-)\in\bigvee_jG_{n+1}(A^j).
\]
This is the one-step block-intersection identity of
[Perez-Garcia--Verstraete--Wolf--Cirac 2007] (arXiv:quant-ph/0608197),
Theorem 12, proof lines 1442--1452. -/
theorem pgvwc07_mem_iSup_groundSpace_iff_iSup_restrictions
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1)
    (ψ : NSiteSpace d (n + 2)) :
    ψ ∈ ⨆ j : Fin r, groundSpace (A j) (n + 2) ↔
      (∀ b : Fin d,
        restrictLast ψ b ∈ ⨆ j : Fin r, groundSpace (A j) (n + 1)) ∧
      (∀ a : Fin d,
        restrictFirst ψ a ∈ ⨆ j : Fin r, groundSpace (A j) (n + 1)) := by
  classical
  constructor
  · intro hψ
    constructor
    · intro b
      refine Submodule.iSup_induction
        (p := fun j : Fin r => groundSpace (A j) (n + 2))
        (motive := fun φ => restrictLast φ b ∈
          ⨆ j : Fin r, groundSpace (A j) (n + 1))
        (x := ψ) hψ ?_ ?_ ?_
      · intro j φ hφ
        exact Submodule.mem_iSup_of_mem j
          (groundSpace_inLeftGround (A j) (n + 1) hφ b)
      · change (0 : NSiteSpace d (n + 1)) ∈
          ⨆ j : Fin r, groundSpace (A j) (n + 1)
        exact Submodule.zero_mem _
      · intro φ ξ hφ hξ
        simpa [restrictLast, restrictLastₗ] using
          (Submodule.add_mem (⨆ j : Fin r, groundSpace (A j) (n + 1)) hφ hξ)
    · intro a
      refine Submodule.iSup_induction
        (p := fun j : Fin r => groundSpace (A j) (n + 2))
        (motive := fun φ => restrictFirst φ a ∈
          ⨆ j : Fin r, groundSpace (A j) (n + 1))
        (x := ψ) hψ ?_ ?_ ?_
      · intro j φ hφ
        exact Submodule.mem_iSup_of_mem j
          (groundSpace_inRightGround (A j) (n + 1) hφ a)
      · change (0 : NSiteSpace d (n + 1)) ∈
          ⨆ j : Fin r, groundSpace (A j) (n + 1)
        exact Submodule.zero_mem _
      · intro φ ξ hφ hξ
        simpa [restrictFirst, restrictFirstₗ] using
          (Submodule.add_mem (⨆ j : Fin r, groundSpace (A j) (n + 1)) hφ hξ)
  · intro hRestrict
    exact pgvwc07_mem_iSup_groundSpace_of_iSup_restrictions
      A hSpan hUnital ψ hRestrict.1 hRestrict.2

/-- Subspace form of the one-step block intersection identity.

Let \(S_n=\bigvee_jG_{n+1}(A^j)\).  Under the PGVWC common word-span
hypothesis and the normalization
\[
  \sum_a A^j_a A^{j\dagger}_a=I,
\]
the \((n+2)\)-site block ground space is the intersection of the inverse
images of \(S_n\) under all fixed last-letter and fixed first-letter
restrictions.  This is the restriction-subspace form of
[Perez-Garcia--Verstraete--Wolf--Cirac 2007] (arXiv:quant-ph/0608197),
Theorem 12, proof lines 1442--1452. -/
theorem pgvwc07_iSup_groundSpace_eq_restriction_intersection
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1) :
    ((⨅ b : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
      (⨅ a : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
      ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  classical
  ext ψ
  simp only [Submodule.mem_inf, Submodule.mem_iInf]
  simpa [restrictLast, restrictFirst] using
    (pgvwc07_mem_iSup_groundSpace_iff_iSup_restrictions A hSpan hUnital ψ).symm

/-- Product spans give the PGVWC one-step intersection identity as an internal
direct sum.

Let
\[
  S_{n+1}=\bigvee_jG_{n+1}(A^j).
\]
If the simultaneous block-word tuples span the full product algebra at lengths
\(n\), \(n+1\), and \(n+2\), and the blocks satisfy
\[
  \sum_a A^j_aA^{j\dagger}_a=I,
\]
then \(S_{n+1}\) and \(\bigvee_jG_{n+2}(A^j)\) are internal direct sums, and
\[
  \left(\bigcap_b\operatorname{Res}_{-,b}^{-1}S_{n+1}\right)
  \cap
  \left(\bigcap_a\operatorname{Res}_{a,-}^{-1}S_{n+1}\right)
  =
  \bigvee_jG_{n+2}(A^j).
\]
This is the one-step block-intersection formula of
[Perez-Garcia--Verstraete--Wolf--Cirac 2007] (arXiv:quant-ph/0608197) together
with the directness needed to read the joins as direct sums of local block
spaces. -/
theorem pgvwc07_directSum_restriction_intersection_of_wordTupleSpanTop
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (hSpan_succ : WordTupleSpanTop A (n + 1))
    (hSpan_succ_succ : WordTupleSpanTop A (n + 2))
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1) :
    iSupIndep (fun j : Fin r => groundSpace (A j) (n + 1)) ∧
      iSupIndep (fun j : Fin r => groundSpace (A j) (n + 2)) ∧
        ((⨅ b : Fin d,
            (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
          (⨅ a : Fin d,
            (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
          ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  exact ⟨groundSpace_iSupIndep_of_wordTupleSpanTop A hSpan_succ,
    groundSpace_iSupIndep_of_wordTupleSpanTop A hSpan_succ_succ,
    pgvwc07_iSup_groundSpace_eq_restriction_intersection A hSpan hUnital⟩

/-- Period-window form of the PGVWC one-step block intersection.

If a positive period and a complete residue window give full homogeneous
blockwise product spans, then the one-step block-intersection subspace equality
holds at every sufficiently large internal word length. -/
theorem pgvwc07_iSup_restriction_intersection_eventually_of_period_window
    {r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    {start period : ℕ} (hperiod_pos : 0 < period)
    (hperiod : WordTupleSpanTop A period)
    (hwindow : ∀ s : ℕ, s < period → WordTupleSpanTop A (start + s))
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1) :
    ∃ L : ℕ, ∀ n : ℕ, n ≥ L →
      ((⨅ b : Fin d,
          (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
        (⨅ a : Fin d,
          (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
        ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  rcases wordTupleSpanTop_eventually_of_wordTupleSpanTop_period_window
      A hperiod_pos hperiod hwindow with
    ⟨L, hL⟩
  refine ⟨L, ?_⟩
  intro n hn
  exact pgvwc07_iSup_groundSpace_eq_restriction_intersection A (hL n hn) hUnital

end MPSTensor
