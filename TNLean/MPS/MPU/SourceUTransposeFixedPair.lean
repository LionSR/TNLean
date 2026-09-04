/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceUCompleteNetwork

/-!
# The source gate u for a weight that need not be symmetric

The complete source-$u$ network of arXiv:1703.09188, equation `uUnitary`
(lines 545--557), closes the Gram matrix of the paper gate
$u=Y_2\mathbin{-}Y_1$ to a trace of two double-layer letters separated by the
rank-one insertion $|\rho^{\mathsf T})(\Phi|$, where $\rho$ is the weight
carried by the two normalizations `X1X2b`.  That closure is exact for every
weight.  This file pairs it with the matching stabilized fixed pair
$E^K=|\rho^{\mathsf T})(\Phi|$ and reads off $u^\dagger u=\Id$ from input-first
unitarity of the MPU chain, for an arbitrary positive definite weight.

The weight and the fixed point are paired as the column-stacking coordinates
of `Matrix.vec` require, so no symmetry of $\rho$ enters.  In the source's
canonical-form-II coordinates $\rho$ is diagonal and the two matrices
coincide, which is the case treated in `TNLean.MPS.MPU.SourceUCompleteNetwork`.

**Scope restriction (supplied stabilized fixed pair):** the theorems below
assume the exact rank-one identity $E^K=|\rho^{\mathsf T})(\Phi|$ as a
hypothesis, whereas CPSV17 Lemma `lemuisometry` inherits the fixed pair from
the preceding canonical-form-II convention.  Documented in
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.

## Main results

* `MPOTensor.SourceFactors.sourceU_gram_eq_closed_doubleLayer_trace_of_transpose_fixed_pair`:
  the source-$u$ Gram matrix is the closed direct double-layer trace with one
  $K$-site interior.
* `MPOTensor.SourceFactors.sourceU_isIsometry_of_isMPU_of_transpose_fixed_pair`:
  the gate $u$ of an MPU tensor is an isometry.
* `MPOTensor.IsMPU.sourceU_isIsometry_of_transpose_fixed_pair`: the same for
  the compact-SVD source factors.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017, arXiv:1703.09188], equations
  `Erightleft`, `X1X2b`, `uu`, and `uUnitary`, and Lemma `lemuisometry`
  (lines 269--280 and 487--557).
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

namespace SourceFactors

/-- For a supplied source weight whose transpose is the stabilized fixed
point, the source-$u$ Gram matrix is the closed direct double-layer trace with
one $K$-site interior between the two retained endpoint letters.  The pair `p`
is starred and `q` is unstarred.

No symmetry of the weight is used: the exact closure already inserts
$|\rho^{\mathsf T})(\Phi|$, and that is the vector the stabilized pair
supplies.

Source: CPSV17 equation `uUnitary` and Lemma `lemuisometry` (lines 545--557),
with the fixed pair of lines 269--280. -/
theorem sourceU_gram_eq_closed_doubleLayer_trace_of_transpose_fixed_pair
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) (K : ℕ)
    (hK : normalizedDiagonal (doubleLayerTensor U) ^ K =
      Matrix.vecMulVec (fun x ↦ ρᵀ.vec (finProdFinEquiv.symm x))
        (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)))
    (p q : Fin d × Fin d) :
    (∑ lr, sourceU U S lr q * star (sourceU U S lr p)) =
      Matrix.trace
        (doubleLayerTensor U p.1 q.1 * doubleLayerTensor U p.2 q.2 *
          normalizedDiagonal (doubleLayerTensor U) ^ K) := by
  rw [sourceU_gram_eq_transpose_fixed_pair_trace, ← hK]
  exact Matrix.trace_mul_cycle _ _ _

/-- For supplied source factors whose weight has the stabilized fixed point as
its transpose, the paper gate $u=Y_2\mathbin{-}Y_1$ of an MPU tensor is an
isometry.

Source: CPSV17 Lemma `lemuisometry` (lines 545--557), with the fixed pair of
lines 269--280. -/
theorem sourceU_isIsometry_of_isMPU_of_transpose_fixed_pair [NeZero d]
    (hU : IsMPU U) {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (K : ℕ)
    (hK : normalizedDiagonal (doubleLayerTensor U) ^ K =
      Matrix.vecMulVec (fun x ↦ ρᵀ.vec (finProdFinEquiv.symm x))
        (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x))) :
    (sourceU U S).IsIsometry := by
  change (sourceU U S)ᴴ * sourceU U S = 1
  ext p q
  have h := sourceU_gram_eq_closed_doubleLayer_trace_of_transpose_fixed_pair
    U S K hK p q
  rw [← normalized_mpo_input_tail_eq_closed_doubleLayer_trace,
    hU.normalized_mpo_tail_isometry] at h
  rw [Matrix.mul_apply, Matrix.one_apply, ← h]
  exact Finset.sum_congr rfl fun lr _ ↦ by
    rw [Matrix.conjTranspose_apply, mul_comm]

end SourceFactors

variable {U} in
/-- For a positive definite weight whose transpose is the stabilized fixed
point, the compact-SVD paper gate $u$ of an MPU tensor is an isometry.

Source: CPSV17 Lemma `lemuisometry` (lines 545--557), with the fixed pair of
lines 269--280. -/
theorem IsMPU.sourceU_isIsometry_of_transpose_fixed_pair [NeZero d]
    (hU : IsMPU U) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) (K : ℕ)
    (hK : normalizedDiagonal (doubleLayerTensor U) ^ K =
      Matrix.vecMulVec (fun x ↦ ρᵀ.vec (finProdFinEquiv.symm x))
        (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x))) :
    (sourceU U ρ hρ).IsIsometry :=
  SourceFactors.sourceU_isIsometry_of_isMPU_of_transpose_fixed_pair U hU
    (sourceFactors U ρ hρ) K hK

end MPOTensor
