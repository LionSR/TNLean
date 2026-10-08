/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyWord
import Mathlib.Analysis.CStarAlgebra.Matrix
import QICLean.Channel.PartialTrace

/-!
# Physical output components of allowed words

The physical basis projection in the polynomial-PEPS manuscript, Theorem 5.2,
`04-compression.tex`, lines 435–463, is applied after an explicit fixed
identification of the output memory with physical output and discarded memory.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-contraction; Theorem 5.2, lines 409–450.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
Provenance-ID: 8769-source-resource-physicaloutputcontraction-repr
TNLean.PEPS.PairEffect.Word.repr_effectMap
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-physical-physicaloutputcontraction-01
Downstream declaration:
TNLean.PEPS.PairEffect.Layout.physicalDiscardIso

Provenance-ID: 8769-physical-physicaloutputcontraction-02
Downstream declaration:
TNLean.PEPS.PairEffect.Layout.physicalDiscardIso_tmul

Provenance-ID: 8769-physical-physicaloutputcontraction-03
Downstream declaration:
TNLean.PEPS.PairEffect.Word.norm_physicalComponentCoordinates_le_one

Provenance-ID: 8769-physical-physicaloutputcontraction-04
Downstream declaration:
TNLean.PEPS.PairEffect.Word.norm_physicalComponent_le_one

Provenance-ID: 8769-physical-physicaloutputcontraction-05
Downstream declaration:
TNLean.PEPS.PairEffect.Word.norm_physicalGramMap_le_one

Provenance-ID: 8769-physical-physicaloutputcontraction-06
Downstream declaration:
TNLean.PEPS.PairEffect.Word.norm_physicalGramMatrix_le_one

Provenance-ID: 8769-physical-physicaloutputcontraction-07
Downstream declaration:
TNLean.PEPS.PairEffect.Word.partialTrace_physicalOutputMatrix_mul_conjTranspose

Provenance-ID: 8769-physical-physicaloutputcontraction-08
Downstream declaration:
TNLean.PEPS.PairEffect.Word.physicalComponent

Provenance-ID: 8769-physical-physicaloutputcontraction-09
Downstream declaration:
TNLean.PEPS.PairEffect.Word.physicalComponentCoordinates

Provenance-ID: 8769-physical-physicaloutputcontraction-10
Downstream declaration:
TNLean.PEPS.PairEffect.Word.physicalGramMap

Provenance-ID: 8769-physical-physicaloutputcontraction-11
Downstream declaration:
TNLean.PEPS.PairEffect.Word.physicalGramMap_inner

Provenance-ID: 8769-physical-physicaloutputcontraction-12
Downstream declaration:
TNLean.PEPS.PairEffect.Word.physicalGramMatrix

Provenance-ID: 8769-physical-physicaloutputcontraction-13
Downstream declaration:
TNLean.PEPS.PairEffect.Word.physicalGramMatrix_apply

Provenance-ID: 8769-physical-physicaloutputcontraction-14
Downstream declaration:
TNLean.PEPS.PairEffect.Word.physicalOutputMatrix

-/


noncomputable section
open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.Word

variable {P X : Type} [Fintype X] {a b : Layout P}
    {D : Type} [NormedAddCommGroup D] [InnerProductSpace ℂ D]

/-- The physical basis component of an actual word, retaining its discarded output.
Polynomial-PEPS manuscript, Theorem 5.2, lines 435–455. -/
def physicalComponent
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x : X) (v : Word a b) :
    Mem a →L[ℂ] D :=
  effectMap (EuclideanSpace.basisFun X ℂ x) D ∘L
    J.toLinearIsometry.toContinuousLinearMap ∘L v.eval

/-- Physical projection preserves the contraction bound on every input vector.
Polynomial-PEPS manuscript, Theorem 5.2, lines 435–455. -/
theorem norm_physicalComponent_le_one
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x : X) (v : Word a b)
    (hv : v.IsAllowed) : ‖physicalComponent J x v‖ ≤ 1 := by
  exact norm_comp_le_one
    (norm_effectMap_le ((EuclideanSpace.basisFun X ℂ).norm_eq_one x) D)
    (norm_comp_le_one (LinearIsometry.norm_toContinuousLinearMap_le _)
      (v.norm_eval_le_one hv))

/-- Finite orthonormal coordinates on the full free-input memory.
Polynomial-PEPS manuscript, Theorem 5.2, lines 435–455. -/
def physicalComponentCoordinates {n : Type} [Fintype n]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x : X) (v : Word a b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) : EuclideanSpace ℂ n →L[ℂ] D :=
  physicalComponent J x v ∘L bIn.repr.symm.toLinearIsometry.toContinuousLinearMap

/-- The coordinate form still contracts arbitrary joint free inputs.
Polynomial-PEPS manuscript, Theorem 5.2, lines 435–455. -/
theorem norm_physicalComponentCoordinates_le_one {n : Type} [Fintype n]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x : X) (v : Word a b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (hv : v.IsAllowed) :
    ‖physicalComponentCoordinates J x v bIn‖ ≤ 1 := by
  exact norm_comp_le_one (norm_physicalComponent_le_one J x v hv)
    (LinearIsometry.norm_toContinuousLinearMap_le _)

/-- The mixed affected operator, with the bra component on the adjoint side.
Polynomial-PEPS manuscript, equation `eq:compression-block-contraction`.
Both words have the same output memory and discarded-output identification. -/
def physicalGramMap {a' : Layout P} {n n' : Type} [Fintype n] [Fintype n']
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bIn' : OrthonormalBasis n' ℂ (Mem a')) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n' :=
  (((InnerProductSpace.toDual ℂ (EuclideanSpace ℂ n')).symm :
    StrongDual ℂ (EuclideanSpace ℂ n') →L⋆[ℂ] EuclideanSpace ℂ n').comp
    (toSesqForm (physicalComponentCoordinates J y w bIn'))).comp
      (physicalComponentCoordinates J x v bIn)

/-- The mixed affected operator has norm at most one, independently of discard dimension.
Polynomial-PEPS manuscript, equation `eq:compression-block-contraction`. -/
theorem norm_physicalGramMap_le_one {a' : Layout P} {n n' : Type}
    [Fintype n] [Fintype n']
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bIn' : OrthonormalBasis n' ℂ (Mem a'))
    (hv : v.IsAllowed) (hw : w.IsAllowed) :
    ‖physicalGramMap J x y v w bIn bIn'‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro z
  change ‖(InnerProductSpace.toDual ℂ (EuclideanSpace ℂ n')).symm
    (toSesqForm (physicalComponentCoordinates J y w bIn')
      (physicalComponentCoordinates J x v bIn z))‖ ≤ 1 * ‖z‖
  rw [LinearIsometryEquiv.norm_map, one_mul]
  calc
    _ ≤ ‖physicalComponentCoordinates J y w bIn'‖ *
        ‖physicalComponentCoordinates J x v bIn z‖ := toSesqForm_apply_norm_le
    _ ≤ ‖physicalComponentCoordinates J x v bIn z‖ :=
      mul_le_of_le_one_left (norm_nonneg _)
        (norm_physicalComponentCoordinates_le_one J y w bIn' hw)
    _ ≤ ‖z‖ := by
      simpa only [one_mul] using
        (physicalComponentCoordinates J x v bIn).le_of_opNorm_le
          (norm_physicalComponentCoordinates_le_one J x v bIn hv) z

/-- The mixed operator pairs the bra output with the ket output, in that order.
Polynomial-PEPS manuscript, equation `eq:compression-block-contraction`. -/
theorem physicalGramMap_inner {a' : Layout P} {n n' : Type}
    [Fintype n] [Fintype n']
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bIn' : OrthonormalBasis n' ℂ (Mem a'))
    (z : EuclideanSpace ℂ n) (t : EuclideanSpace ℂ n') :
    ⟪t, physicalGramMap J x y v w bIn bIn' z⟫_ℂ =
      ⟪physicalComponentCoordinates J y w bIn' t,
        physicalComponentCoordinates J x v bIn z⟫_ℂ := by
  rw [← inner_conj_symm]
  simp only [physicalGramMap, comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, InnerProductSpace.toDual_symm_apply,
    toSesqForm_apply_coe, coe_innerSL_apply]
  exact inner_conj_symm _ _

/-- The rectangular coordinate matrix of the mixed affected contraction.
Polynomial-PEPS manuscript, equation `eq:compression-block-contraction`. -/
def physicalGramMatrix {a' : Layout P} {n n' : Type} [Fintype n] [Fintype n']
    [DecidableEq n]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bIn' : OrthonormalBasis n' ℂ (Mem a')) :
    Matrix n' n ℂ := by
  classical
  exact Matrix.toEuclideanLin.symm (physicalGramMap J x y v w bIn bIn').toLinearMap

/-- Matrix entries are the exact bra–ket inner products of retained discard vectors.
Polynomial-PEPS manuscript, Theorem 5.2, lines 453–468. -/
theorem physicalGramMatrix_apply {a' : Layout P} {n n' : Type}
    [Fintype n] [Fintype n'] [DecidableEq n]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bIn' : OrthonormalBasis n' ℂ (Mem a'))
    (j : n') (i : n) :
    physicalGramMatrix J x y v w bIn bIn' j i =
      ⟪physicalComponent J y w (bIn' j), physicalComponent J x v (bIn i)⟫_ℂ := by
  classical
  change LinearMap.toMatrix (EuclideanSpace.basisFun n ℂ).toBasis
    (EuclideanSpace.basisFun n' ℂ).toBasis
    (physicalGramMap J x y v w bIn bIn').toLinearMap j i = _
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
  change ⟪EuclideanSpace.basisFun n' ℂ j,
    physicalGramMap J x y v w bIn bIn' (EuclideanSpace.basisFun n ℂ i)⟫_ℂ = _
  rw [physicalGramMap_inner]
  simp [physicalComponentCoordinates]

open scoped Matrix.Norms.L2Operator in
/-- The coordinate matrix has the same dimension-free contraction bound.
Polynomial-PEPS manuscript, equation `eq:compression-block-contraction`. -/
theorem norm_physicalGramMatrix_le_one {a' : Layout P} {n n' : Type}
    [Fintype n] [Fintype n'] [DecidableEq n]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bIn' : OrthonormalBasis n' ℂ (Mem a'))
    (hv : v.IsAllowed) (hw : w.IsAllowed) :
    ‖physicalGramMatrix J x y v w bIn bIn'‖ ≤ 1 := by
  classical
  rw [Matrix.l2_opNorm_def, physicalGramMatrix, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  have h : LinearMap.toContinuousLinearMap
      (physicalGramMap J x y v w bIn bIn').toLinearMap =
      physicalGramMap J x y v w bIn bIn' := by ext z; rfl
  rw [h]
  exact norm_physicalGramMap_le_one J x y v w bIn bIn' hv hw

end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.PairEffect.Layout

/-- The fixed physical and discarded output layouts give a canonical output identification.
Polynomial-PEPS manuscript, Theorem 5.2, lines 435–455. -/
def physicalDiscardIso {P X : Type} [Fintype X]
    (physical discard : Layout P) (bPhysical : OrthonormalBasis X ℂ (Mem physical)) :
    Mem (physical ++ discard) ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] Mem discard :=
  (appendIso physical discard).trans (bPhysical.repr.rTensor (Mem discard))

/-- The output identification maps each physical basis vector to its coordinate vector.
Polynomial-PEPS manuscript, Theorem 5.2, lines 435–455. -/
theorem physicalDiscardIso_tmul {P X : Type} [Fintype X]
    (physical discard : Layout P) (bPhysical : OrthonormalBasis X ℂ (Mem physical))
    (x : X) (z : Mem discard) :
    physicalDiscardIso physical discard bPhysical
      ((appendIso physical discard).symm (bPhysical x ⊗ₜ[ℂ] z)) =
      EuclideanSpace.basisFun X ℂ x ⊗ₜ[ℂ] z := by
  classical
  simp [physicalDiscardIso]

end TNLean.PEPS.PairEffect.Layout

namespace TNLean.PEPS.PairEffect.Word

/-- Partial inner product extracts the corresponding tensor coordinate. -/
theorem repr_effectMap {X d D : Type} [Fintype X] [Fintype d]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    (bD : OrthonormalBasis d ℂ D) (x : X) (z : EuclideanSpace ℂ X ⊗[ℂ] D) (k : d) :
    bD.repr (effectMap (EuclideanSpace.basisFun X ℂ x) D z) k =
      ((EuclideanSpace.basisFun X ℂ).tensorProduct bD).repr z (x, k) := by
  induction z using TensorProduct.inductionOn with
  | tmul z t => simp [effectMap_tmul, OrthonormalBasis.tensorProduct_repr_tmul_apply, mul_comm]
  | add z t hz ht => simp [hz, ht]

/-- The actual word matrix in joint physical-output and discarded-output coordinates.
Polynomial-PEPS manuscript, Theorem 5.2, lines 435–468. -/
def physicalOutputMatrix {P X d n : Type} [Fintype X] [Fintype d] [Fintype n]
    [DecidableEq n] {a b : Layout P} {D : Type}
    [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (v : Word a b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bD : OrthonormalBasis d ℂ D) :
    Matrix (X × d) n ℂ :=
  LinearMap.toMatrix bIn.toBasis ((EuclideanSpace.basisFun X ℂ).tensorProduct bD).toBasis
    (J.toLinearEquiv.toLinearMap.comp v.eval.toLinearMap)

/-- Output coordinates are the coordinates of the actual projected discard vector. -/
private theorem physicalOutputMatrix_apply {P X d n : Type}
    [Fintype X] [Fintype d] [Fintype n] [DecidableEq n]
    {a b : Layout P} {D : Type} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (v : Word a b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bD : OrthonormalBasis d ℂ D)
    (x : X) (k : d) (i : n) :
    physicalOutputMatrix J v bIn bD (x, k) i =
      bD.repr (physicalComponent J x v (bIn i)) k := by
  rw [physicalOutputMatrix, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis]
  exact (repr_effectMap bD x (J (v.eval (bIn i))) k).symm

/-- In finite discard coordinates, the intrinsic Gram entry is the ordinary matrix product. -/
private theorem physicalGramMatrix_eq_sum {P X d n n' : Type}
    [Fintype X] [Fintype d] [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    {a a' b : Layout P} {D : Type} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bIn' : OrthonormalBasis n' ℂ (Mem a'))
    (bD : OrthonormalBasis d ℂ D) (j : n') (i : n) :
    physicalGramMatrix J x y v w bIn bIn' j i =
      ∑ k, star (physicalOutputMatrix J w bIn' bD (y, k) j) *
        physicalOutputMatrix J v bIn bD (x, k) i := by
  rw [physicalGramMatrix_apply]
  simp only [physicalOutputMatrix_apply, OrthonormalBasis.repr_apply_apply,
    RCLike.star_def, inner_conj_symm]
  exact (bD.sum_inner_mul_inner _ _).symm

/-- Tracing the common discarded output pairs an arbitrary rectangular input
operator with the opposite-index Gram entry. No positivity or Hermiticity is assumed.
Polynomial-PEPS manuscript, Theorem 5.2, lines 453–474. -/
theorem partialTrace_physicalOutputMatrix_mul_conjTranspose {P X d n n' : Type}
    [Fintype X] [Fintype d] [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    {a a' b : Layout P} {D : Type} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bIn' : OrthonormalBasis n' ℂ (Mem a'))
    (bD : OrthonormalBasis d ℂ D) (ρ : Matrix n n' ℂ) :
    Matrix.partialTraceRight (physicalOutputMatrix J v bIn bD * ρ *
      (physicalOutputMatrix J w bIn' bD).conjTranspose) x y =
      ∑ i, ∑ j, ρ i j * physicalGramMatrix J x y v w bIn bIn' j i := by
  let K : Matrix d n ℂ := fun k i ↦ physicalOutputMatrix J v bIn bD (x, k) i
  let L : Matrix d n' ℂ := fun k j ↦ physicalOutputMatrix J w bIn' bD (y, k) j
  change Matrix.trace (K * ρ * L.conjTranspose) = _
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  simp_rw [physicalGramMatrix_eq_sum J x y v w bIn bIn' bD]
  rfl

end TNLean.PEPS.PairEffect.Word
