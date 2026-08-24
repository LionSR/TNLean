/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.DFinsupp
import TNLean.MPS.ParentHamiltonian.IntersectionProperty
import TNLean.MPS.ParentHamiltonian.BoundaryMatrixIdentities
import TNLean.MPS.SharedInfra.WordTupleGauge

/-!
# Boundary decompositions for block intersections

The left-boundary trace decomposition, direct-sum independence, and boundary
identities used in the block-diagonal parent-Hamiltonian intersection argument.

## References

* arXiv:quant-ph/0608197, Theorem 12.
* [Cirac--Perez-Garcia--Schuch--Verstraete 2021], Section IV.C.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The left-boundary summand in the source block-diagonal intersection proof:
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
      Kraus.evalWord A (List.ofFn (Fin.tail (Fin.init σ))))

/-- Fixing the first physical index in the source left-boundary summand gives the
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
    Matrix.trace (A (σ (Fin.last n)) * C a * Kraus.evalWord A (List.ofFn (Fin.init σ)))
        = Matrix.trace ((A (σ (Fin.last n)) * C a) *
            Kraus.evalWord A (List.ofFn (Fin.init σ))) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (Kraus.evalWord A (List.ofFn (Fin.init σ)) *
        (A (σ (Fin.last n)) * C a)) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (Kraus.evalWord A (List.ofFn (Fin.init σ)) *
        A (σ (Fin.last n)) * C a) := by rw [Matrix.mul_assoc]

/-- Boundary form of a ground-space vector after fixing the final physical index. -/
theorem groundSpaceMap_snoc_trace_boundary
    (A : MPSTensor d D) {n : ℕ} (X : Matrix (Fin D) (Fin D) ℂ)
    (w : Fin n → Fin d) (b : Fin d) :
    groundSpaceMap A (n + 1) X (Fin.snoc w b) =
      Matrix.trace ((A b * X) * Kraus.evalWord A (List.ofFn w)) := by
  simp only [groundSpaceMap_apply, evalWord_ofFn_snoc]
  calc
    Matrix.trace (Kraus.evalWord A (List.ofFn w) * A b * X)
        = Matrix.trace (Kraus.evalWord A (List.ofFn w) * (A b * X)) := by
            rw [Matrix.mul_assoc]
    _ = Matrix.trace ((A b * X) * Kraus.evalWord A (List.ofFn w)) := by
            rw [Matrix.trace_mul_comm]

/-- Boundary form of a ground-space vector after fixing the initial physical index. -/
theorem groundSpaceMap_cons_trace_boundary
    (A : MPSTensor d D) {n : ℕ} (X : Matrix (Fin D) (Fin D) ℂ)
    (a : Fin d) (w : Fin n → Fin d) :
    groundSpaceMap A (n + 1) X (Fin.cons a w) =
      Matrix.trace ((X * A a) * Kraus.evalWord A (List.ofFn w)) := by
  simp only [groundSpaceMap_apply, evalWord_ofFn_cons]
  calc
    Matrix.trace (A a * Kraus.evalWord A (List.ofFn w) * X)
        = Matrix.trace ((A a * Kraus.evalWord A (List.ofFn w)) * X) := by
            rw [Matrix.mul_assoc]
    _ = Matrix.trace (X * (A a * Kraus.evalWord A (List.ofFn w))) := by
            rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((X * A a) * Kraus.evalWord A (List.ofFn w)) := by
            rw [Matrix.mul_assoc]

/-- Boundary form of a ground-space vector after fixing the initial and final
physical indices. -/
theorem groundSpaceMap_cons_snoc_trace_boundary
    (A : MPSTensor d D) {n : ℕ} (X : Matrix (Fin D) (Fin D) ℂ)
    (a b : Fin d) (w : Fin n → Fin d) :
    groundSpaceMap A (n + 2) X (Fin.cons a (Fin.snoc w b)) =
      Matrix.trace ((A b * X * A a) * Kraus.evalWord A (List.ofFn w)) := by
  simp only [groundSpaceMap_apply, evalWord_ofFn_cons, evalWord_ofFn_snoc]
  calc
    Matrix.trace ((A a * (Kraus.evalWord A (List.ofFn w) * A b)) * X)
        = Matrix.trace (((A a * Kraus.evalWord A (List.ofFn w)) * A b) * X) := by
            rw [← Matrix.mul_assoc (A a) (Kraus.evalWord A (List.ofFn w)) (A b)]
    _ = Matrix.trace ((A a * Kraus.evalWord A (List.ofFn w)) * (A b * X)) := by
            rw [Matrix.mul_assoc]
    _ = Matrix.trace ((A b * X) * (A a * Kraus.evalWord A (List.ofFn w))) := by
            rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((A b * X * A a) * Kraus.evalWord A (List.ofFn w)) := by
            simp [Matrix.mul_assoc]

/-- The left-boundary summand is a ground-space vector once the boundary
identity \(A_bC_a=A_bEA_a\) holds. -/
theorem pgvwc07LeftBoundaryComponent_eq_groundSpaceMap
    (A : MPSTensor d D) (C : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (E : Matrix (Fin D) (Fin D) ℂ) (n : ℕ)
    (hACE : ∀ a b : Fin d, A b * C a = A b * E * A a) :
    pgvwc07LeftBoundaryComponent A C n = groundSpaceMap A (n + 2) E := by
  ext σ
  let M := Kraus.evalWord A (List.ofFn (Fin.tail (Fin.init σ)))
  let a := σ 0
  let b := σ (Fin.last (n + 1))
  have hEvalInit :
      Kraus.evalWord A (List.ofFn (Fin.init σ)) = A a * M := by
    have hinit : Fin.cons a (Fin.tail (Fin.init σ)) = Fin.init σ := by
      dsimp [a]
      exact Fin.cons_self_tail (Fin.init σ)
    rw [← hinit]
    exact evalWord_ofFn_cons A a (Fin.tail (Fin.init σ))
  have hEval :
      Kraus.evalWord A (List.ofFn σ) = (A a * M) * A b := by
    have hσ : Fin.snoc (Fin.init σ) b = σ := by
      simp [b]
    rw [← hσ]
    calc
      Kraus.evalWord A (List.ofFn (Fin.snoc (Fin.init σ) b))
          = Kraus.evalWord A (List.ofFn (Fin.init σ)) * A b :=
              evalWord_ofFn_snoc A (Fin.init σ) b
      _ = (A a * M) * A b := by rw [hEvalInit]
  change Matrix.trace (A b * C a * M) =
    Matrix.trace (Kraus.evalWord A (List.ofFn σ) * E)
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

/-- The left-boundary summand belongs to \(G_{n+2}(A)\) once the
boundary identity \(A_bC_a=A_bEA_a\) holds. -/
theorem pgvwc07LeftBoundaryComponent_mem_groundSpace
    (A : MPSTensor d D) (C : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (E : Matrix (Fin D) (Fin D) ℂ) (n : ℕ)
    (hACE : ∀ a b : Fin d, A b * C a = A b * E * A a) :
    pgvwc07LeftBoundaryComponent A C n ∈ groundSpace A (n + 2) := by
  rw [pgvwc07LeftBoundaryComponent_eq_groundSpaceMap A C E n hACE]
  rw [groundSpace, LinearMap.mem_range]
  exact ⟨E, rfl⟩

/-- A finite sum of source left-boundary summands lies in the supremum of the
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
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
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
    rw [dite_eq_left hi]
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
      (∑ i : Fin r, Matrix.trace (Kraus.evalWord (A i) (List.ofFn w) * X i)) = 0 := by
    intro w
    simpa [groundSpaceMap_apply] using congrFun hsum_all w
  have hTrace : ∀ w : Fin n → Fin d,
      (∑ i : Fin r, Matrix.trace (X i * Kraus.evalWord (A i) (List.ofFn w))) = 0 := by
    intro w
    calc
      (∑ i : Fin r, Matrix.trace (X i * Kraus.evalWord (A i) (List.ofFn w)))
          = ∑ i : Fin r, Matrix.trace (Kraus.evalWord (A i) (List.ofFn w) * X i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              exact Matrix.trace_mul_comm (X i) (Kraus.evalWord (A i) (List.ofFn w))
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
      (∑ j : Fin r, Matrix.trace (X j * Kraus.evalWord (A j) (List.ofFn w))) =
      (∑ j : Fin r, Matrix.trace (Y j * Kraus.evalWord (A j) (List.ofFn w)))) :
    ∀ j : Fin r, X j = Y j := by
  intro j
  have hzero := block_matrices_eq_zero_of_wordTupleSpanTop_trace A hSpan
    (fun k => X k - Y k) (by
      intro w
      simpa [Matrix.sub_mul, Matrix.trace_sub, Finset.sum_sub_distrib, sub_eq_zero]
        using sub_eq_zero.mpr (hTrace w)) j
  exact sub_eq_zero.mp hzero

/-- Blockwise boundary identities from membership of a source left-boundary
trace decomposition in the block ground-space sum.

This is the coefficient-comparison direction in the proof of
Theorem 12 of arXiv:quant-ph/0608197. If a vector
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
    (Submodule.mem_iSup_iff_exists_finsupp
      (fun j : Fin r => groundSpace (A j) (n + 2)) ψ).mp hmem
  have hφsum_univ : ψ = ∑ j : Fin r, φ j := by
    simpa [Finsupp.sum_fintype] using hφsum.symm
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
        Matrix.trace ((A k b * C k a) * Kraus.evalWord (A k) (List.ofFn w))) =
      (∑ k : Fin r,
        Matrix.trace ((A k b * E k * A k a) * Kraus.evalWord (A k) (List.ofFn w))) := by
    intro w
    have hLeftEval :
        ψ (Fin.cons a (Fin.snoc w b)) =
          ∑ k : Fin r,
            Matrix.trace ((A k b * C k a) * Kraus.evalWord (A k) (List.ofFn w)) := by
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
              Matrix.trace ((A k b * C k a) * Kraus.evalWord (A k) (List.ofFn w)) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              exact groundSpaceMap_snoc_trace_boundary (A k) (C k a) w b
    have hRightEval :
        ψ (Fin.cons a (Fin.snoc w b)) =
          ∑ k : Fin r,
            Matrix.trace ((A k b * E k * A k a) * Kraus.evalWord (A k) (List.ofFn w)) := by
      calc
        ψ (Fin.cons a (Fin.snoc w b))
            = (∑ k : Fin r, φ k) (Fin.cons a (Fin.snoc w b)) := by
              rw [hφsum_univ]
        _ = ∑ k : Fin r, φ k (Fin.cons a (Fin.snoc w b)) := by
              simp
        _ = ∑ k : Fin r,
              groundSpaceMap (A k) (n + 2) (E k) (Fin.cons a (Fin.snoc w b)) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              rw [hE k]
        _ = ∑ k : Fin r,
              Matrix.trace ((A k b * E k * A k a) *
                Kraus.evalWord (A k) (List.ofFn w)) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              exact groundSpaceMap_cons_snoc_trace_boundary (A k) (E k) a b w
    exact hLeftEval.symm.trans hRightEval
  exact block_matrices_eq_of_wordTupleSpanTop_trace A hSpan
    (fun k => A k b * C k a) (fun k => A k b * E k * A k a) hCoeff j


end MPSTensor
