/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixCoordinateInclusion
import TNLean.MPS.Symmetry.SPTFixedPoint
import TNLean.MPS.Core.PhysicalIndexMixing
import TNLean.MPS.Core.PhysicalRotation

/-!
# Coordinate embeddings of the fixed-point physical space

An inclusion of bond basis indices induces an inclusion of the pairs which
label the physical matrix units. The resulting physical map is isometric
and preserves injectivity. These are the endpoint inclusions in
arXiv:1010.3732, Section II.F.2, equation `eq:1d-sym:jointsym`.
-/

open scoped Matrix

namespace MPSTensor

/-- The physical basis inclusion induced by an inclusion of bond indices.
Source: arXiv:1010.3732, Section II.F.2, `eq:1d-sym:jointsym`. -/
def sptPhysicalEmbedding {D K : ℕ} (e : Fin D ↪ Fin K) : Fin (D * D) ↪ Fin (K * K) :=
  finProdFinEquiv.symm.toEmbedding.trans
    ((e.prodMap e).trans finProdFinEquiv.toEmbedding)

/-- Each entry of a physically embedded fixed point is its normalized
matrix-unit coefficient at the included pair of bond indices.
Source: arXiv:1010.3732, Section II.F.2, `eq:1d-sym:jointsym`. -/
theorem rotatePhysical_coordinateInclusion_sptFixedPointTensor_apply
    {D K : ℕ} (e : Fin D ↪ Fin K) (p : Fin (K * K)) (a b : Fin D) :
    rotatePhysical (Matrix.coordinateInclusion (sptPhysicalEmbedding e))
      (sptFixedPointTensor D) p a b =
      if p = finProdFinEquiv (e a, e b) then sptScale D else 0 := by
  rw [rotatePhysical_apply, sum_smul_sptFixedPointTensor_apply]
  simp [Matrix.coordinateInclusion, sptPhysicalEmbedding]

/-- A coordinate embedding of a fixed-point tensor remains injective.
Source: arXiv:1010.3732, Section II.F.2, `eq:1d-sym:jointsym`,
isometric endpoint embeddings. -/
theorem isInjective_rotatePhysical_coordinateInclusion_sptFixedPointTensor
    {D K : ℕ} [NeZero D] (e : Fin D ↪ Fin K) :
    Kraus.IsInjective (rotatePhysical (Matrix.coordinateInclusion (sptPhysicalEmbedding e))
      (sptFixedPointTensor D)) :=
  isInjective_kraus_isometry _ _
    (Matrix.coordinateInclusion_isometry (sptPhysicalEmbedding e))
    sptFixedPointTensor_isInjective

end MPSTensor
