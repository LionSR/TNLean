/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryObservableCompression
import TNLean.MPS.ParentHamiltonian.LocalObservableQuasiLocalState
import TNLean.QCA.StateSpace
import TNLean.QCA.QuasiLocalInterval
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# Uniqueness of the state supported in primitive MPS ground spaces

A positive functional supported in an orthogonal projection has the same
value on an observable and on its compression to that projection. For a
primitive MPS tensor, scalar compression on expanding intervals therefore
identifies every local expectation of a supported quasi-local state with
the MPS insertion expectation. Continuity then identifies the states on
the completed observable algebra. No translation invariance is assumed
of the competing state.

This is a uniqueness consequence of the primitive boundary convergence
used in Nachtergaele, arXiv:cond-mat/9410110, Section 3, lines 1380--1505,
and Section 6, lines 2649--2675. The argument concerns all normalized
positive continuous state functionals, rather than only invariant states.
The support-compression lemma is a general algebraic intermediate result.
-/

open Filter
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology

namespace PositiveLinearMap
variable {E : Type*} [Ring E] [PartialOrder E] [Module ℂ E] [StarRing E]
  [StarOrderedRing E] [SelfAdjointDecompose E] [StarModule ℂ E] [IsScalarTower ℂ E E]

/-- A positive functional supported in a projection evaluates every observable
by its compression to that projection. This is the algebraic Cauchy--Schwarz
support argument used for local state uniqueness. -/
theorem apply_projection_compression_eq (f : E →ₚ[ℂ] ℂ) (p X : E)
    (hpstar : star p = p) (hp : p * p = p) (hfp : f p = f 1) :
    f (p * X * p) = f X := by
  have hqstar : star (1 - p) = 1 - p := by simp only [star_sub, star_one, hpstar]
  have hq : (1 - p) * (1 - p) = 1 - p := by noncomm_ring [hp]
  have hfq : f (1 - p) = 0 := by rw [map_sub, hfp, sub_self]
  have hL (Y : E) : f ((1 - p) * Y) = 0 :=
    norm_eq_zero.mp (le_antisymm
      (by simpa only [hqstar, hq, hfq, norm_zero, Real.sqrt_zero, zero_mul] using
        PositiveLinearMap.norm_map_star_mul_le f (1 - p) Y) (norm_nonneg _))
  have hR (Y : E) : f (Y * (1 - p)) = 0 :=
    norm_eq_zero.mp (le_antisymm
      (by simpa only [star_star, hqstar, hq, hfq, norm_zero, Real.sqrt_zero, mul_zero] using
        PositiveLinearMap.norm_map_star_mul_le f (star Y) (1 - p)) (norm_nonneg _))
  have hPL (Y : E) : f (p * Y) = f Y := by
    exact (sub_eq_zero.mp (by simpa only [sub_mul, one_mul, map_sub] using hL Y)).symm
  exact (sub_eq_zero.mp
    (by simpa only [mul_sub, mul_one, map_sub] using hR (p * X))).symm.trans (hPL X)

end PositiveLinearMap

open SpinChain
namespace MPSTensor
variable {d D : ℕ}

/-- The orthogonal projection onto the finite-chain MPS space in numbered
matrix coordinates. Source: Nachtergaele, arXiv:cond-mat/9410110,
Section 3, local support spaces after equation (3.6). -/
noncomputable def groundSpaceProjectionMatrix (A : MPSTensor d D) (N : ℕ) :
    Matrix (Cfg d N) (Cfg d N) ℂ :=
  (Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)).symm (groundSpaceES A N).starProjection

/-- The matrix of the ground-space projection is self-adjoint and idempotent. -/
theorem isStarProjection_groundSpaceProjectionMatrix (A : MPSTensor d D) (N : ℕ) :
    IsStarProjection (groundSpaceProjectionMatrix A N) :=
  IsStarProjection.map
    (A := EuclideanSpace ℂ (Cfg d N) →L[ℂ] EuclideanSpace ℂ (Cfg d N))
    (B := Matrix (Cfg d N) (Cfg d N) ℂ)
    (isStarProjection_starProjection (U := groundSpaceES A N))
    (Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)).symm.toStarAlgHom

variable [NeZero d]

/-- Placing a ground-space projection on a consecutive interval preserves
self-adjointness and idempotence. -/
theorem isStarProjection_quasiLocalIntervalObservable_groundSpaceProjectionMatrix
    (A : MPSTensor d D) (a : ℤ) (N : ℕ) :
    IsStarProjection (quasiLocalIntervalObservable d a N (groundSpaceProjectionMatrix A N)) :=
  (isStarProjection_groundSpaceProjectionMatrix A N).map (quasiLocalIntervalObservable d a N)

/-- Restriction of a functional nonnegative on squares to a numbered finite
interval, regarded as a positive complex-linear functional. -/
noncomputable def intervalStateFunctional
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ)
    (hpos : ∀ X, 0 ≤ φ (star X * X)) (a : ℤ) (N : ℕ) :
    Matrix (Cfg d N) (Cfg d N) ℂ →ₚ[ℂ] ℂ where
  toLinearMap := φ.toLinearMap.comp
    (quasiLocalIntervalObservable d a N).toAlgHom.toLinearMap
  monotone' := by
    apply (monotone_iff_map_nonneg
      (φ.toLinearMap.comp (quasiLocalIntervalObservable d a N).toAlgHom.toLinearMap)).mpr
    intro X hX
    obtain ⟨Y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX
    change 0 ≤ φ (quasiLocalIntervalObservable d a N (star Y * Y))
    simpa only [map_mul, map_star] using hpos (quasiLocalIntervalObservable d a N Y)

/-- The finite-interval positive restriction evaluates by the interval inclusion. -/
@[simp] theorem intervalStateFunctional_apply
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ)
    (hpos : ∀ X, 0 ≤ φ (star X * X)) (a : ℤ) (N : ℕ)
    (X : Matrix (Cfg d N) (Cfg d N) ℂ) :
    intervalStateFunctional φ hpos a N X = φ (quasiLocalIntervalObservable d a N X) := rfl

/-- A state supported in an interval projection differs from a scalar by at
most the norm of the corresponding compressed scalar defect. This estimate
requires no translation invariance. -/
theorem norm_quasiLocalState_interval_sub_scalar_le_projection_compression
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (a : ℤ) {N : ℕ} (p X : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hp : IsStarProjection p) (hφp : φ (quasiLocalIntervalObservable d a N p) = 1)
    (c : ℂ) :
    ‖φ (quasiLocalIntervalObservable d a N X) - c‖ ≤
      ‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) (p * X * p - c • p)‖ := by
  let f := intervalStateFunctional φ hφ.2.2 a N
  have hf : f p = f 1 := by
    change φ (quasiLocalIntervalObservable d a N p) =
      φ (quasiLocalIntervalObservable d a N 1)
    rw [map_one, hφp, hφ.2.1]
  have heq : φ (quasiLocalIntervalObservable d a N (p * X * p - c • p)) =
      φ (quasiLocalIntervalObservable d a N X) - c := by
    change f (p * X * p - c • p) = f X - c
    rw [map_sub, map_smul,
      PositiveLinearMap.apply_projection_compression_eq f p X hp.isSelfAdjoint.star_eq
        hp.isIdempotentElem hf, (show f p = 1 from hφp), smul_eq_mul, mul_one]
  rw [← heq]
  refine (φ.le_opNorm _).trans_eq ?_
  rw [hφ.1, one_mul, norm_quasiLocalIntervalObservable]
  exact NonUnitalStarAlgHom.norm_map
    CStarMatrix.ofMatrixStarAlgEquiv (EquivLike.injective _)
      (p * X * p - c • p)

private theorem quasiLocalIntervalObservable_bulkObservable (a : ℤ) (k b c : ℕ)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    quasiLocalIntervalObservable d (a - b) ((b + k) + c) (bulkObservable X b c) =
      quasiLocalIntervalObservable d a k X := by
  have hb : intervalCoordinates d (a - b) ((b + k) + c)
      (localInclusion (intervalRegion_subset_expanded a k b c)
        ((intervalCoordinates d a k).symm X)) = bulkObservable X b c := by
    simpa only [StarAlgEquiv.apply_symm_apply] using
      intervalCoordinates_localInclusion_eq_bulkObservable d a k b c
        ((intervalCoordinates d a k).symm X)
  rw [← hb, quasiLocalIntervalObservable_apply, StarAlgEquiv.symm_apply_apply,
    quasiLocalObservable_localInclusion, ← quasiLocalIntervalObservable_apply]

/-- Every normalized positive state supported in all finite-interval primitive
MPS spaces has the prescribed insertion expectations on every local interval.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3 and the boundary
convergence argument in Section 6, lines 2649--2675. -/
theorem IsPrimitiveMPS.quasiLocalState_interval_eq_insertion_of_groundSpace_support
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef)
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (hSupport : ∀ (a : ℤ) (N : ℕ),
      φ (quasiLocalIntervalObservable d a N (groundSpaceProjectionMatrix A N)) = 1)
    (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    φ (quasiLocalIntervalObservable d a k X) = observableInsertionExpectation A ρ X := by
  have hlim := hP.bulkObservable_groundSpace_compression_tendsto_scalar hρ X
    (ℓ := id) (r := id) tendsto_id tendsto_id
  have hbound (n : ℕ) :
      ‖φ (quasiLocalIntervalObservable d a k X) - observableInsertionExpectation A ρ X‖ ≤
        ‖(groundSpaceES A ((n + k) + n)).starProjection.comp
          ((Matrix.toEuclideanCLM (n := Cfg d ((n + k) + n)) (𝕜 := ℂ)
            (bulkObservable X n n)).comp (groundSpaceES A ((n + k) + n)).starProjection) -
          observableInsertionExpectation A ρ X •
            (groundSpaceES A ((n + k) + n)).starProjection‖ := by
    have h := norm_quasiLocalState_interval_sub_scalar_le_projection_compression
      φ hφ (a - n) (groundSpaceProjectionMatrix A ((n + k) + n))
      (bulkObservable X n n) (isStarProjection_groundSpaceProjectionMatrix A _)
      (hSupport (a - n) _) (observableInsertionExpectation A ρ X)
    simpa only [quasiLocalIntervalObservable_bulkObservable, groundSpaceProjectionMatrix,
      map_sub, map_mul, map_smul, StarAlgEquiv.apply_symm_apply,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using h
  have hzero := squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall hbound) hlim
  exact sub_eq_zero.mp (norm_eq_zero.mp
    (tendsto_nhds_unique tendsto_const_nhds hzero))

/-- A primitive MPS state is the unique normalized positive quasi-local state
supported in its finite-interval MPS spaces. The competing state need not be
translation invariant. Source: Nachtergaele, arXiv:cond-mat/9410110,
Section 3, lines 1469--1490, and Section 6, lines 2649--2675. -/
theorem IsPrimitiveMPS.eq_quasiLocalExpectation_of_groundSpace_support
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef)
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (hSupport : ∀ (a : ℤ) (N : ℕ),
      φ (quasiLocalIntervalObservable d a N (groundSpaceProjectionMatrix A N)) = 1) :
    φ = quasiLocalExpectation A hP.norm hP.fixedPoint_psd
      hP.fixedPoint_is_fixed hP.trace_ne_zero := by
  apply (localMPSState A hP.norm hP.fixedPoint_psd
    hP.fixedPoint_is_fixed hP.trace_ne_zero).quasiLocalFunctional_unique φ
  intro Λ X
  change φ (quasiLocalObservable d Λ X) = localObservableExpectation A ρ Λ X
  unfold localObservableExpectation
  dsimp only [LinearMap.comp_apply, observableInsertionExpectationₗ]
  change φ (quasiLocalObservable d Λ X) = observableInsertionExpectation A ρ _
  rw [← hP.quasiLocalState_interval_eq_insertion_of_groundSpace_support hρ φ hφ hSupport
    (-((Λ.sup Int.natAbs : ℕ) : ℤ))]
  simp only [quasiLocalIntervalObservable_apply, LinearEquiv.coe_coe,
    AlgEquiv.coe_toLinearEquiv, StarAlgEquiv.coe_toAlgEquiv, AlgHom.toLinearMap_apply,
    StarAlgHom.coe_toAlgHom,
    StarAlgEquiv.symm_apply_apply, quasiLocalObservable_localInclusion]

end MPSTensor
