/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PrimitiveQuasiLocalUniqueness
/-!
# Finite-interval projection estimates for quasi-local states

The positive restriction of a normalized quasi-local state evaluates an
orthogonal projection in the real interval $[0,1]$. If that expectation
is one, every observable has the same expectation as its compression to
the projection. The operator norm bounds the resulting evaluation error.
These are general state estimates; no tensor, invariance, or asymptotic
hypothesis is involved.
-/

open Filter SpinChain
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
namespace MPSTensor
variable {d : ℕ} [NeZero d]

/-- The interval expectation is bounded by the matrix operator norm. -/
theorem norm_quasiLocalState_interval_le
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (a : ℤ) {N : ℕ} (X : Matrix (Cfg d N) (Cfg d N) ℂ) :
    ‖φ (quasiLocalIntervalObservable d a N X)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) X‖ := by
  refine (φ.le_opNorm _).trans_eq ?_
  rw [hφ.1, one_mul, norm_quasiLocalIntervalObservable]
  exact NonUnitalStarAlgHom.norm_map CStarMatrix.ofMatrixStarAlgEquiv
    (EquivLike.injective _) X
/-- The expectation of a finite-interval orthogonal projection lies in $[0,1]$. -/
theorem intervalStateFunctional_projection_mem_unitInterval
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (a : ℤ) {N : ℕ} (p : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hp : IsStarProjection p) :
    0 ≤ (φ (quasiLocalIntervalObservable d a N p)).re ∧
      (φ (quasiLocalIntervalObservable d a N p)).re ≤ 1 := by
  let f := intervalStateFunctional φ hφ.2.2 a N
  have hf : f 1 = 1 := by simp [f, hφ.2.1]
  have hnonneg : 0 ≤ f p := f.map_nonneg hp.nonneg
  have hle : f p ≤ 1 := by
    have hq := f.map_nonneg hp.one_sub.nonneg
    rwa [map_sub, hf, sub_nonneg] at hq
  exact ⟨(Complex.nonneg_iff.mp hnonneg).1, (Complex.le_def.mp hle).1⟩

/-- The expectation of a finite-interval orthogonal projection is real. -/
theorem intervalStateFunctional_projection_eq_ofReal_re
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (a : ℤ) {N : ℕ} (p : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hp : IsStarProjection p) :
    φ (quasiLocalIntervalObservable d a N p) =
      ((φ (quasiLocalIntervalObservable d a N p)).re : ℂ) := by
  have hnonneg := (intervalStateFunctional φ hφ.2.2 a N).map_nonneg hp.nonneg
  exact Complex.ext rfl (Complex.nonneg_iff.mp hnonneg).2.symm

/-- Support in a projection bounds an expectation error by the compressed operator defect. -/
theorem norm_quasiLocalState_interval_sub_le_projection_compression
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (a : ℤ) {N : ℕ} (p X Y : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hp : IsStarProjection p) (hφp : φ (quasiLocalIntervalObservable d a N p) = 1) :
    ‖φ (quasiLocalIntervalObservable d a N X) -
      φ (quasiLocalIntervalObservable d a N Y)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) (p * X * p - Y)‖ := by
  let f := intervalStateFunctional φ hφ.2.2 a N
  have hf : f p = f 1 := by simpa [f, hφ.2.1] using hφp
  have heq : φ (quasiLocalIntervalObservable d a N (p * X * p - Y)) =
      φ (quasiLocalIntervalObservable d a N X) -
        φ (quasiLocalIntervalObservable d a N Y) := by
    change f (p * X * p - Y) = f X - f Y
    rw [map_sub, PositiveLinearMap.apply_projection_compression_eq f p X
      hp.isSelfAdjoint.star_eq hp.isIdempotentElem hf]
  rw [← heq]
  exact norm_quasiLocalState_interval_le φ hφ a (p * X * p - Y)

/-- Support in a finite-interval projection permits compression of every observable. -/
theorem quasiLocalState_interval_projection_compression_eq
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (a : ℤ) {N : ℕ} (p X : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hp : IsStarProjection p) (hφp : φ (quasiLocalIntervalObservable d a N p) = 1) :
    φ (quasiLocalIntervalObservable d a N (p * X * p)) =
      φ (quasiLocalIntervalObservable d a N X) := by
  exact PositiveLinearMap.apply_projection_compression_eq
    (intervalStateFunctional φ hφ.2.2 a N) p X hp.isSelfAdjoint.star_eq
      hp.isIdempotentElem (by simpa [hφ.2.1] using hφp)
end MPSTensor
