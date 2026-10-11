/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BlockBoundarySelector
import TNLean.MPS.MPDO.NormalAdjointBoundary
import TNLean.MPS.SharedInfra.BoundaryDecomposition

/-!
# Adjoint closure of actual normal block-sum MPO families

Arbitrary boundaries of a literal finite block sum split into their diagonal
blocks. For normal positive-dimensional blocks with an involutive periodic
physical adjoint dual, the normal-target reduction theorem supplies a bond
similarity for each block. Conjugate and transport each diagonal boundary,
then insert it into its dual block. This constructs one boundary transport
working at every chain length, including zero.

The periodic physical adjoint identities remain explicit hypotheses. This
result neither constructs a weak Hopf algebra nor supplies those identities
from algebraic arbitrary-boundary multiplication.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `algcond` and Appendix A:
  a sufficient criterion for adjoint closure of the represented operators,
  under the additional physical star-representation hypothesis.
-/

open scoped Matrix BigOperators

noncomputable section

namespace MPOTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- An arbitrary boundary of the actual unweighted block sum contributes
only its diagonal blocks, at every length. -/
theorem mpoWithBoundary_blockSum
    (A : (a : Fin r) → MPOTensor d (dim a))
    (X : Matrix (Fin (∑ a, dim a)) (Fin (∑ a, dim a)) ℂ) (N : ℕ) :
    mpoWithBoundary (blockSum A) X N =
      ∑ a, mpoWithBoundary (A a) (Matrix.finSigmaDiagonalBlock X a) N := by
  ext σ τ
  simp only [Matrix.sum_apply, mpoWithBoundary]
  rw [Matrix.trace_mul_comm, ← evalWord_toMPSTensor_pairConfig,
    blockSum_toMPSTensor, MPSTensor.trace_evalWord_toTensorFromBlocks_mul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [one_pow, one_smul, evalWord_toMPSTensor_pairConfig]
  exact Matrix.trace_mul_comm _ _

/-- Insert one arbitrary boundary into a chosen summand of the flattened
virtual direct sum. -/
def embedBlockBoundary (dim : Fin r → ℕ) (a : Fin r)
    (X : Matrix (Fin (dim a)) (Fin (dim a)) ℂ) :
    Matrix (Fin (∑ b, dim b)) (Fin (∑ b, dim b)) ℂ :=
  Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
    (Matrix.sigmaBlockInclusion (fun b ↦ Fin (dim b)) a * X *
      (Matrix.sigmaBlockInclusion (fun b ↦ Fin (dim b)) a)ᴴ)

/-- A boundary inserted into one summand closes precisely that block.
Unlike a scalar selector, the inserted boundary may be any matrix. -/
theorem mpoWithBoundary_blockSum_embedBlockBoundary
    (A : (a : Fin r) → MPOTensor d (dim a)) (a : Fin r)
    (X : Matrix (Fin (dim a)) (Fin (dim a)) ℂ) (N : ℕ) :
    mpoWithBoundary (blockSum A) (embedBlockBoundary dim a X) N =
      mpoWithBoundary (A a) X N := by
  ext σ τ
  change Matrix.trace (embedBlockBoundary dim a X *
      evalWord (blockSum A) (List.ofFn σ) (List.ofFn τ)) =
    Matrix.trace (X * evalWord (A a) (List.ofFn σ) (List.ofFn τ))
  rw [evalWord_blockSum]
  let e : ((b : Fin r) × Fin (dim b)) ≃ Fin (∑ b, dim b) := finSigmaFinEquiv
  let E := Matrix.sigmaBlockInclusion (fun b ↦ Fin (dim b)) a
  let B := fun b ↦ evalWord (A b) (List.ofFn σ) (List.ofFn τ)
  change Matrix.trace (Matrix.reindexLinearEquiv ℂ ℂ e e (E * X * Eᴴ) *
      Matrix.reindexLinearEquiv ℂ ℂ e e (Matrix.blockDiagonal' B)) =
    Matrix.trace (X * B a)
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ e e e]
  simp only [Matrix.coe_reindexLinearEquiv, Matrix.trace_reindex]
  calc
    Matrix.trace ((E * X * Eᴴ) * Matrix.blockDiagonal' B) =
        Matrix.trace (E * (X * Eᴴ * Matrix.blockDiagonal' B)) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((X * Eᴴ * Matrix.blockDiagonal' B) * E) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (X * (Eᴴ * Matrix.blockDiagonal' B * E)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (X * B a) := by
      rw [Matrix.sigmaBlockInclusion_compression]

/-- Conjugate each input diagonal block, transport it by the corresponding
bond similarity, and insert the result into its dual summand. This is one
map on the ambient boundary space, with no length parameter. -/
def blockSumAdjointBoundary (dual : Fin r → Fin r)
    (V : ∀ a, Matrix (Fin (dim (dual a))) (Fin (dim a)) ℂ)
    (W : ∀ a, Matrix (Fin (dim a)) (Fin (dim (dual a))) ℂ)
    (X : Matrix (Fin (∑ a, dim a)) (Fin (∑ a, dim a)) ℂ) :
    Matrix (Fin (∑ a, dim a)) (Fin (∑ a, dim a)) ℂ :=
  ∑ a, embedBlockBoundary dim (dual a)
    (V a * (Matrix.finSigmaDiagonalBlock X a).map (starRingEnd ℂ) * W a)

/-- Arbitrary-boundary adjoint closure asks for one output boundary valid
simultaneously at all positive lengths. -/
def IsBoundaryAdjointClosed {D : ℕ} (T : MPOTensor d D) : Prop :=
  ∀ X : Matrix (Fin D) (Fin D) ℂ,
    ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ N : ℕ, 0 < N → (mpoWithBoundary T X N)ᴴ = mpoWithBoundary T Y N

/-- Normality and periodic physical adjoint duality construct exact block
gauges and a single boundary transport for the literal block sum.

Only positive-length periodic equalities are assumed. Equality of dual bond
dimensions makes the resulting arbitrary-boundary formula hold also at zero.
No injectivity of the unblocked letters, pairwise block inequivalence,
canonical normalization, fusion data, or boundary adjoint-closure assumption
is required. -/
theorem IsPeriodicAdjointFamily.exists_blockSumAdjointBoundary
    {A : (a : Fin r) → MPOTensor d (dim a)} {dual : Fin r → Fin r}
    (h : IsPeriodicAdjointFamily A dual) (hdual : Function.Involutive dual)
    (hNormal : ∀ a, Kraus.IsNormal (A a).toMPSTensor)
    (hDim : ∀ a, 0 < dim a) :
    ∃ (V : ∀ a, Matrix (Fin (dim (dual a))) (Fin (dim a)) ℂ)
      (W : ∀ a, Matrix (Fin (dim a)) (Fin (dim (dual a))) ℂ),
      (∀ a, V a * W a = 1) ∧ (∀ a, W a * V a = 1) ∧
      (∀ a i j, physicalAdjointTensor (A a) i j =
        W a * A (dual a) i j * V a) ∧
      ∀ (X : Matrix (Fin (∑ a, dim a)) (Fin (∑ a, dim a)) ℂ) (N : ℕ),
        (mpoWithBoundary (blockSum A) X N)ᴴ =
          mpoWithBoundary (blockSum A) (blockSumAdjointBoundary dual V W X) N := by
  classical
  choose V W hVW hWV hletter hboundary using h.exists_boundaryGauge hdual hNormal hDim
  refine ⟨V, W, hVW, hWV, hletter, fun X N ↦ ?_⟩
  rw [mpoWithBoundary_blockSum, Matrix.conjTranspose_sum]
  simp_rw [hboundary]
  have hsum (Y : Fin r →
      Matrix (Fin (∑ a, dim a)) (Fin (∑ a, dim a)) ℂ) :
      mpoWithBoundary (blockSum A) (∑ a, Y a) N =
        ∑ a, mpoWithBoundary (blockSum A) (Y a) N := by
    ext σ τ
    simp only [mpoWithBoundary, Matrix.sum_mul, Matrix.trace_sum, Matrix.sum_apply]
  rw [blockSumAdjointBoundary, hsum]
  simp_rw [mpoWithBoundary_blockSum_embedBlockBoundary]

/-- The actual block sum is adjoint closed with one boundary choice for all
positive lengths, derived from normal blocks and explicit periodic duality. -/
theorem IsPeriodicAdjointFamily.isBoundaryAdjointClosed_blockSum
    {A : (a : Fin r) → MPOTensor d (dim a)} {dual : Fin r → Fin r}
    (h : IsPeriodicAdjointFamily A dual) (hdual : Function.Involutive dual)
    (hNormal : ∀ a, Kraus.IsNormal (A a).toMPSTensor)
    (hDim : ∀ a, 0 < dim a) : IsBoundaryAdjointClosed (blockSum A) := by
  obtain ⟨V, W, _, _, _, hboundary⟩ := h.exists_blockSumAdjointBoundary hdual hNormal hDim
  intro X
  exact ⟨blockSumAdjointBoundary dual V W X, fun N _ ↦ hboundary X N⟩

end MPOTensor
