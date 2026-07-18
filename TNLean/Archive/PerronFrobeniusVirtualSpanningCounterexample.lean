/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import TNLean.Algebra.PerronFrobenius.RankOne
import TNLean.MPS.MPDO.ZCL

/-!
# A virtual-spanning obstruction to the rank-one step in Lemma C.5

This file strengthens the rectangular-pairing counterexample for
arXiv:1606.00608, Appendix C.2, lines 1406--1499.  It gives four pairs of
vectors
\[
  l_k\in\mathbb R^2,\qquad r_k\in(\mathbb R^2)^*,
\]
with the following properties.

* The four sector matrices `l_k r_k` span the full algebra `M₂(ℝ)`.
* The closed pairing operator `L Q` is idempotent.
* The opposite product `T = Q L` is entrywise nonnegative, primitive, and
  trace-normalized.
* Every positive power of `T` has the same trace, and `T ^ 2 = T ^ 3`.
* Nevertheless `T` is not idempotent, the remainder
  `Q (1 - L Q) L` is nonzero, and `T` has no rank-one factorization.
* The matrices `l_k r_k` are the diagonal slices of an injective source-ZCL
  MPO tensor.

Thus the virtual-matrix spanning conclusion obtained from injectivity in the
formal inverse-map construction does not, by itself, eliminate the nilpotent
generalized zero-eigenspace of the sector trace matrix.  The example does not
claim to arise from the complete strong-area-law inverse-map construction;
that additional provenance remains the precise boundary of issue #3593.

This file is deliberately excluded from the root `TNLean.lean` import list.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.2, Lemmas C.4--C.5, lines 1406--1499.

## Main results

* `counterexample_with_virtual_spanning`: the matrix-level obstruction with
  full virtual spanning.
* `injective_sourceZCL_tensor_with_nilpotent_sector_pairing`: the same sector
  data realized as the diagonal slices of an injective source-ZCL MPO tensor.
-/

namespace TNLean.Archive.PerronFrobeniusVirtualSpanningCounterexample

open Matrix

/-- The four closed left-sector vectors, arranged as the columns of a matrix. -/
noncomputable def pairingL : Matrix (Fin 2) (Fin 4) ℝ :=
  !![1 / 6, 1 / 6, 1 / 3, 1 / 3;
     0,     1 / 6, 1 / 6, -1 / 3]

/-- The four closed right-sector functionals, arranged as the rows of a matrix. -/
noncomputable def pairingQ : Matrix (Fin 4) (Fin 2) ℝ :=
  !![1,  1;
     1,  1;
     1, -1;
     1,  0]

/-- The idempotent product on the two-dimensional closed-tensor space. -/
noncomputable def pairingProjection : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 0]

/-- The four-dimensional sector trace matrix `Q L`. -/
noncomputable def traceMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / 6, 1 / 3, 1 / 2, 0;
     1 / 6, 1 / 3, 1 / 2, 0;
     1 / 6, 0,     1 / 6, 2 / 3;
     1 / 6, 1 / 6, 1 / 3, 1 / 3]

/-- The rank-one Perron projection `traceMatrix ^ 2`. -/
noncomputable def perronProjection : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / 6, 1 / 6, 1 / 3, 1 / 3;
     1 / 6, 1 / 6, 1 / 3, 1 / 3;
     1 / 6, 1 / 6, 1 / 3, 1 / 3;
     1 / 6, 1 / 6, 1 / 3, 1 / 3]

/-- The sector virtual matrix `l_k r_k`. -/
noncomputable def virtualMatrix (k : Fin 4) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.vecMulVec (fun i => pairingL i k) (fun j => pairingQ k j)

/-- Coefficients expressing an arbitrary two-by-two matrix in the four sector
virtual matrices. -/
noncomputable def reconstructionCoefficients
    {𝕜 : Type*} [Ring 𝕜] (X : Matrix (Fin 2) (Fin 2) 𝕜) : Fin 4 → 𝕜 :=
  ![X 0 0 + 5 * X 0 1 + X 1 0 - 7 * X 1 1,
    X 0 0 - X 0 1 + X 1 0 + 5 * X 1 1,
    X 0 0 - X 0 1 + X 1 0 - X 1 1,
    X 0 0 - X 0 1 - 2 * X 1 0 + 2 * X 1 1]

lemma pairingL_mul_pairingQ : pairingL * pairingQ = pairingProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairingL, pairingQ, pairingProjection, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring

lemma pairingQ_mul_pairingL : pairingQ * pairingL = traceMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairingL, pairingQ, traceMatrix, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

/-- The product in the closed-tensor space is idempotent, as required by the
normalized source zero-correlation-length identity at lines 1490--1493. -/
theorem pairingL_mul_pairingQ_isIdempotent :
    IsIdempotentElem (pairingL * pairingQ) := by
  rw [pairingL_mul_pairingQ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairingProjection, Matrix.mul_apply, Fin.sum_univ_two]

lemma traceMatrix_sq : traceMatrix * traceMatrix = perronProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceMatrix, perronProjection, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring

lemma traceMatrix_nonneg (i j : Fin 4) : 0 ≤ traceMatrix i j := by
  fin_cases i <;> fin_cases j <;>
    first
    | (simp [traceMatrix]; norm_num)
    | simp [traceMatrix]

lemma traceMatrix_pow_two_pos (i j : Fin 4) : 0 < (traceMatrix ^ 2) i j := by
  rw [sq, traceMatrix_sq]
  fin_cases i <;> fin_cases j <;> simp [perronProjection]

/-- The sector trace matrix is primitive. -/
theorem traceMatrix_isPrimitive : Matrix.IsPrimitive traceMatrix :=
  ⟨traceMatrix_nonneg, 2, by norm_num, traceMatrix_pow_two_pos⟩

lemma trace_traceMatrix : Matrix.trace traceMatrix = 1 := by
  simp [Matrix.trace, traceMatrix, Fin.sum_univ_four]
  ring

/-- Every positive power of the sector trace matrix has the same trace. -/
theorem traceMatrix_tracePowersConstant :
    ∀ N : ℕ, 0 < N →
      Matrix.trace (traceMatrix ^ N) = Matrix.trace traceMatrix := by
  rw [← pairingQ_mul_pairingL]
  exact Matrix.trace_pow_eq_trace_of_rectangular_idempotent
    pairingL pairingQ pairingL_mul_pairingQ_isIdempotent

/-- The sector trace matrix satisfies the scale-invariant consequence of the
rectangular idempotence, although it is not itself idempotent. -/
theorem traceMatrix_sq_eq_cube : traceMatrix ^ 2 = traceMatrix ^ 3 := by
  rw [← pairingQ_mul_pairingL]
  exact Matrix.pow_two_eq_pow_three_of_rectangular_idempotent
    pairingL pairingQ pairingL_mul_pairingQ_isIdempotent

/-- The sector trace matrix is not idempotent. -/
theorem traceMatrix_not_idempotent : traceMatrix * traceMatrix ≠ traceMatrix := by
  intro h
  have hentry := congrFun (congrFun h 0) 1
  rw [traceMatrix_sq] at hentry
  norm_num [perronProjection, traceMatrix] at hentry

/-- The nilpotent remainder is exactly the failure of the desired identity
`Q (1 - L Q) L = 0`. -/
theorem pairing_nilpotent_remainder_ne_zero :
    pairingQ * (1 - pairingL * pairingQ) * pairingL ≠ 0 := by
  intro h
  apply traceMatrix_not_idempotent
  rw [← pairingQ_mul_pairingL]
  have hdiff :
      pairingQ * pairingL -
          (pairingQ * pairingL) * (pairingQ * pairingL) = 0 := by
    calc
      pairingQ * pairingL -
          (pairingQ * pairingL) * (pairingQ * pairingL) =
        pairingQ * (1 - pairingL * pairingQ) * pairingL := by
          simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
            Matrix.mul_assoc]
      _ = 0 := h
  exact (sub_eq_zero.mp hdiff).symm

/-- The four sector virtual matrices reconstruct every two-by-two matrix. -/
theorem virtualMatrix_reconstruction (X : Matrix (Fin 2) (Fin 2) ℝ) :
    ∑ k, reconstructionCoefficients X k • virtualMatrix k = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reconstructionCoefficients, virtualMatrix, pairingL, pairingQ,
      Fin.sum_univ_four] <;> ring

/-- The sector virtual matrices span the full two-by-two matrix algebra. -/
theorem virtualMatrix_span_eq_top :
    Submodule.span ℝ (Set.range virtualMatrix) =
      (⊤ : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [Submodule.eq_top_iff']
  intro X
  rw [← virtualMatrix_reconstruction X]
  apply Submodule.sum_mem
  intro k _
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self k)

/-! ### An injective source-ZCL MPO tensor carrying the same sector data -/

/-- The complexification of a sector virtual matrix. -/
noncomputable def complexVirtualMatrix (k : Fin 4) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.map (virtualMatrix k) Complex.ofReal

/-- A physical-diagonal MPO tensor whose four diagonal matrices are the sector
virtual matrices above. -/
noncomputable def mpoTensor : MPOTensor 4 2 :=
  fun i j => if i = j then complexVirtualMatrix i else 0

theorem complexVirtualMatrix_reconstruction (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ k, reconstructionCoefficients X k • complexVirtualMatrix k = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reconstructionCoefficients, complexVirtualMatrix, virtualMatrix,
      pairingL, pairingQ, Fin.sum_univ_four] <;> ring

lemma complexVirtualMatrix_mem_tensor_span (k : Fin 4) :
    complexVirtualMatrix k ∈
      Submodule.span ℂ (Set.range (MPOTensor.toMPSTensor mpoTensor)) := by
  apply Submodule.subset_span
  refine ⟨finProdFinEquiv (k, k), ?_⟩
  change mpoTensor (finProdFinEquiv (k, k)).divNat
      (finProdFinEquiv (k, k)).modNat = complexVirtualMatrix k
  rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
  simp [mpoTensor]

/-- The diagonal MPO tensor is injective: its four physical matrices span the
full two-by-two virtual matrix algebra. -/
theorem mpoTensor_isInjective : MPSTensor.IsInjective mpoTensor.toMPSTensor := by
  unfold MPSTensor.IsInjective
  rw [Submodule.eq_top_iff']
  intro X
  rw [← complexVirtualMatrix_reconstruction X]
  apply Submodule.sum_mem
  intro k _
  exact Submodule.smul_mem _ _ (complexVirtualMatrix_mem_tensor_span k)

lemma physTraceTransfer_mpoTensor :
    MPOTensor.physTraceTransfer mpoTensor =
      Matrix.map pairingProjection Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MPOTensor.physTraceTransfer, mpoTensor, complexVirtualMatrix,
      virtualMatrix, pairingL, pairingQ, pairingProjection,
      Fin.sum_univ_four] <;> ring

/-- The injective diagonal tensor has source zero correlation length because
its physical-trace transfer is the idempotent `L Q`. -/
theorem mpoTensor_isSourceZCL : MPOTensor.IsSourceZCL mpoTensor := by
  apply MPOTensor.isSourceZCL_of_physTraceTransfer_sq mpoTensor
  · rw [physTraceTransfer_mpoTensor]
    intro h
    have hentry := congrFun (congrFun h 0) 0
    norm_num [pairingProjection] at hentry
  · rw [physTraceTransfer_mpoTensor]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairingProjection, Matrix.mul_apply, Fin.sum_univ_two]

/-- The four sector virtual matrices occur as the diagonal physical slices of
the tensor. -/
theorem mpoTensor_diagonal_slice (k : Fin 4) :
    mpoTensor k k = complexVirtualMatrix k := by
  simp [mpoTensor]

/-- The primitive trace matrix has no rank-one factorization. -/
theorem traceMatrix_not_rankOne :
    ¬ ∃ a b : Fin 4 → ℝ, traceMatrix = Matrix.vecMulVec a b := by
  rintro ⟨a, b, hT⟩
  have h00 : a 0 * b 0 = (1 : ℝ) / 6 := by
    have h := congrFun (congrFun hT 0) 0
    simpa [traceMatrix, Matrix.vecMulVec_apply] using h.symm
  have h03 : a 0 = 0 ∨ b 3 = 0 := by
    have h := congrFun (congrFun hT 0) 3
    simpa [traceMatrix, Matrix.vecMulVec_apply] using h
  have h23 : a 2 * b 3 = (2 : ℝ) / 3 := by
    have h := congrFun (congrFun hT 2) 3
    simpa [traceMatrix, Matrix.vecMulVec_apply] using h.symm
  have ha0 : a 0 ≠ 0 := by
    intro ha
    rw [ha, zero_mul] at h00
    norm_num at h00
  have hb3 : b 3 = 0 := h03.resolve_left ha0
  rw [hb3, mul_zero] at h23
  norm_num at h23

/-- Virtual spanning does not repair the rank-one inference.  The same data
satisfy the rectangular pairing identity, primitivity, trace normalization,
and full virtual-matrix spanning, while the trace matrix is neither idempotent
nor an outer product. -/
theorem counterexample_with_virtual_spanning :
    traceMatrix = pairingQ * pairingL ∧
      IsIdempotentElem (pairingL * pairingQ) ∧
      Matrix.IsPrimitive traceMatrix ∧
      Matrix.trace traceMatrix = 1 ∧
      Submodule.span ℝ (Set.range virtualMatrix) =
        (⊤ : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ)) ∧
      traceMatrix * traceMatrix ≠ traceMatrix ∧
      ¬ ∃ a b : Fin 4 → ℝ, traceMatrix = Matrix.vecMulVec a b :=
  ⟨pairingQ_mul_pairingL.symm, pairingL_mul_pairingQ_isIdempotent,
    traceMatrix_isPrimitive, trace_traceMatrix, virtualMatrix_span_eq_top,
    traceMatrix_not_idempotent, traceMatrix_not_rankOne⟩

/-- An injective source-ZCL tensor realizes the spanning sector matrices of
the counterexample as its diagonal physical slices.  Its physical-trace
transfer is the idempotent product `L Q`, while the opposite product `Q L`
retains a nonzero nilpotent remainder.

This statement contains every tensor-independent algebraic conclusion used in
the present formal proof of Lemma C.5.  It does not identify `pairingL` and
`pairingQ` with the particular tensors chosen by the SAL inverse-map
construction. -/
theorem injective_sourceZCL_tensor_with_nilpotent_sector_pairing :
    MPSTensor.IsInjective mpoTensor.toMPSTensor ∧
      MPOTensor.IsSourceZCL mpoTensor ∧
      MPOTensor.physTraceTransfer mpoTensor =
        Matrix.map pairingProjection Complex.ofReal ∧
      (∀ k : Fin 4, mpoTensor k k = complexVirtualMatrix k) ∧
      Submodule.span ℝ (Set.range virtualMatrix) =
        (⊤ : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ)) ∧
      IsIdempotentElem (pairingL * pairingQ) ∧
      traceMatrix = pairingQ * pairingL ∧
      Matrix.IsPrimitive traceMatrix ∧
      Matrix.trace traceMatrix = 1 ∧
      (∀ N : ℕ, 0 < N →
        Matrix.trace (traceMatrix ^ N) = Matrix.trace traceMatrix) ∧
      traceMatrix ^ 2 = traceMatrix ^ 3 ∧
      pairingQ * (1 - pairingL * pairingQ) * pairingL ≠ 0 ∧
      ¬ ∃ a b : Fin 4 → ℝ, traceMatrix = Matrix.vecMulVec a b :=
  ⟨mpoTensor_isInjective, mpoTensor_isSourceZCL, physTraceTransfer_mpoTensor,
    mpoTensor_diagonal_slice, virtualMatrix_span_eq_top,
    pairingL_mul_pairingQ_isIdempotent, pairingQ_mul_pairingL.symm,
    traceMatrix_isPrimitive, trace_traceMatrix,
    traceMatrix_tracePowersConstant, traceMatrix_sq_eq_cube,
    pairing_nilpotent_remainder_ne_zero, traceMatrix_not_rankOne⟩

end TNLean.Archive.PerronFrobeniusVirtualSpanningCounterexample
