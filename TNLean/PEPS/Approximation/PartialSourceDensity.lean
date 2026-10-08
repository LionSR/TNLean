/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartialSourceEvaluation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Density coefficients of the chronological partial expansion

The exact chronological operator identity gives an exact ket–bra expansion in
any orthonormal bases of the grouped memories. Its scalar weights are the
original ket coefficients times the conjugates of the bra coefficients. The
identity holds for arbitrary input matrices.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 342–381.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section
open scoped ComplexConjugate Matrix
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- The weighted partial expansion is the original operator under the canonical
owner identifications. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 351–417. -/
theorem expandedEval_eq_mapOwner (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) :
    expandedEval A w = isoL (Layout.mapOwnerIso (affectedOwner A) b) ∘L w.eval ∘L
      isoL (Layout.mapOwnerIso (affectedOwner A) a).symm := by
  ext x
  simpa only [comp_apply, isoL_apply, LinearIsometryEquiv.apply_symm_apply] using
    DFunLike.congr_fun (expandedEval_mapOwner A w)
      ((Layout.mapOwnerIso (affectedOwner A) a).symm x)

/-- Taking orthonormal coordinates preserves every original complex coefficient
in the partial expansion. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 351–381. -/
theorem toMatrix_eval_eq_sum_partialWord {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (bIn : OrthonormalBasis n ℂ (Mem (Layout.mapOwner (affectedOwner A) a)))
    (bOut : OrthonormalBasis m ℂ (Mem (Layout.mapOwner (affectedOwner A) b))) :
    LinearMap.toMatrix bIn.toBasis bOut.toBasis
        (isoL (Layout.mapOwnerIso (affectedOwner A) b) ∘L w.eval ∘L
          isoL (Layout.mapOwnerIso (affectedOwner A) a).symm).toLinearMap =
      ∑ ξ, coefficient A w ξ • LinearMap.toMatrix bIn.toBasis bOut.toBasis
        (partialWord A w ξ).eval.toLinearMap := by
  rw [← expandedEval_eq_mapOwner A w]
  simp only [expandedEval, toLinearMap_sum, toLinearMap_smul, map_sum, map_smul]

/-- The density calculation has independent partial choices on its ket and bra
sides, weighted by the original coefficient and the conjugate bra coefficient.
Untouched gates remain aggregate operators in every summand. No positivity or
normalization assumption on the input matrix is required.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–381. -/
theorem density_eval_eq_sum_partialWord {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq n]
    (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (bIn : OrthonormalBasis n ℂ (Mem (Layout.mapOwner (affectedOwner A) a)))
    (bOut : OrthonormalBasis m ℂ (Mem (Layout.mapOwner (affectedOwner A) b)))
    (ρ : Matrix n n ℂ) :
    let M := LinearMap.toMatrix bIn.toBasis bOut.toBasis
      (isoL (Layout.mapOwnerIso (affectedOwner A) b) ∘L w.eval ∘L
        isoL (Layout.mapOwnerIso (affectedOwner A) a).symm).toLinearMap
    let K := fun ξ ↦ LinearMap.toMatrix bIn.toBasis bOut.toBasis
      (partialWord A w ξ).eval.toLinearMap
    M * ρ * Mᴴ = ∑ ξ, ∑ ζ,
      (coefficient A w ξ * conj (coefficient A w ζ)) • (K ξ * ρ * (K ζ)ᴴ) := by
  dsimp only
  rw [toMatrix_eval_eq_sum_partialWord A w bIn bOut]
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul,
    Complex.star_def]
  rw [Finset.sum_comm]
  simp only [mul_comm]

end TNLean.PEPS.PairEffect.SourceCircuit
