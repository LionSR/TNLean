/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.DependentBlockDiagonal
import TNLean.Algebra.ScalarCommutant
import TNLean.MPS.SharedInfra.SectorDecomposition

/-!
# Virtual compression to a flattened sector block

This file identifies each weighted flattened block of a sector decomposition
as an isometric virtual compression of its block-diagonal tensor.

## Main results

- `MPSTensor.SectorDecomposition.flatBlockInclusion`: the canonical inclusion
  of one flattened block.
- `MPSTensor.SectorDecomposition.flatWeight_smul_flatBasis_eq_compression`:
  compression of the ambient tensor recovers the weighted block.

The construction is the blockwise virtual corner from arXiv:1606.00608,
Section 2.3, equation `II_Aiplusk1`, lines 195--219. Appendix C.2, Case I,
lines 1374--1450 and 1571--1619 is a downstream application context.
-/

open scoped Matrix

noncomputable section

namespace MPSTensor.SectorDecomposition

variable {d : ℕ}

/-- The canonical isometric inclusion of a flattened sector block into the
full virtual space.

Source: arXiv:1606.00608, Section 2.3, equation `II_Aiplusk1`, lines 195--219. -/
def flatBlockInclusion
    (P : SectorDecomposition d) (s : Fin P.totalCopies) :
    Matrix (Fin P.totalDim) (Fin (P.flatDim s)) ℂ :=
  Matrix.reindex finSigmaFinEquiv (Equiv.refl _)
    (Matrix.sigmaBlockInclusion
      (fun t : Fin P.totalCopies ↦ Fin (P.flatDim t)) s)

/-- The canonical inclusion of a flattened sector block is an isometry.

Source: arXiv:1606.00608, Section 2.3, equation `II_Aiplusk1`, lines 195--219. -/
@[simp]
theorem flatBlockInclusion_isometry
    (P : SectorDecomposition d) (s : Fin P.totalCopies) :
    (P.flatBlockInclusion s)ᴴ * P.flatBlockInclusion s = 1 := by
  let dim := fun t : Fin P.totalCopies ↦ Fin (P.flatDim t)
  let e : ((t : Fin P.totalCopies) × dim t) ≃ Fin P.totalDim :=
    finSigmaFinEquiv
  let E := Matrix.sigmaBlockInclusion dim s
  change (Matrix.reindex e (Equiv.refl _) E)ᴴ *
      Matrix.reindex e (Equiv.refl _) E = 1
  rw [Matrix.conjTranspose_reindex]
  change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e Eᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _) E = 1
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) e (Equiv.refl _),
    Matrix.sigmaBlockInclusion_isometry,
    Matrix.reindexLinearEquiv_one]

/-- The range projection of a flattened block inclusion is the reindexed
projection onto that block.

Source: arXiv:1606.00608, Section 2.3, equation `II_Aiplusk1`, lines 195--219. -/
theorem flatBlockInclusion_mul_conjTranspose
    (P : SectorDecomposition d) (s : Fin P.totalCopies) :
    P.flatBlockInclusion s * (P.flatBlockInclusion s)ᴴ =
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockProjection
          (n := fun t : Fin P.totalCopies ↦ Fin (P.flatDim t))
          (R := ℂ) s) := by
  let dim := fun t : Fin P.totalCopies ↦ Fin (P.flatDim t)
  let e : ((t : Fin P.totalCopies) × dim t) ≃ Fin P.totalDim :=
    finSigmaFinEquiv
  let E := Matrix.sigmaBlockInclusion dim s
  change Matrix.reindex e (Equiv.refl _) E *
      (Matrix.reindex e (Equiv.refl _) E)ᴴ =
        Matrix.reindex e e (Matrix.blockProjection (n := dim) (R := ℂ) s)
  rw [Matrix.conjTranspose_reindex]
  change Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _) E *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e Eᴴ =
        Matrix.reindexLinearEquiv ℂ ℂ e e
          (Matrix.blockProjection (n := dim) (R := ℂ) s)
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ e (Equiv.refl _) e]
  rw [Matrix.sigmaBlockInclusion_mul_conjTranspose_eq_blockProjection
    (n := dim) s]

/-- The flattened block inclusion intertwines the ambient tensor with the
weighted selected block on the right.

Source: arXiv:1606.00608, Section 2.3, equation `II_Aiplusk1`, lines 195--219. -/
theorem toTensor_mul_flatBlockInclusion
    (P : SectorDecomposition d) (s : Fin P.totalCopies) (i : Fin d) :
    P.toTensor i * P.flatBlockInclusion s =
      P.flatBlockInclusion s * (P.flatWeight s • P.flatBasis s i) := by
  let dim := fun t : Fin P.totalCopies ↦ Fin (P.flatDim t)
  let e : ((t : Fin P.totalCopies) × dim t) ≃ Fin P.totalDim :=
    finSigmaFinEquiv
  let E := Matrix.sigmaBlockInclusion dim s
  let B := fun t : Fin P.totalCopies ↦ P.flatWeight t • P.flatBasis t i
  change Matrix.reindex e e (Matrix.blockDiagonal' B) *
      Matrix.reindex e (Equiv.refl _) E =
        Matrix.reindex e (Equiv.refl _) E * B s
  change Matrix.reindexLinearEquiv ℂ ℂ e e (Matrix.blockDiagonal' B) *
      Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _) E =
        Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _) E *
          Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _) (B s)
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ e e (Equiv.refl _),
    Matrix.reindexLinearEquiv_mul ℂ ℂ e (Equiv.refl _) (Equiv.refl _),
    Matrix.blockDiagonal'_mul_sigmaBlockInclusion]

/-- The adjoint flattened block inclusion intertwines the ambient tensor with
the weighted selected block on the left.

Source: arXiv:1606.00608, Section 2.3, equation `II_Aiplusk1`, lines 195--219. -/
theorem flatBlockInclusion_conjTranspose_mul_toTensor
    (P : SectorDecomposition d) (s : Fin P.totalCopies) (i : Fin d) :
    (P.flatBlockInclusion s)ᴴ * P.toTensor i =
      (P.flatWeight s • P.flatBasis s i) *
        (P.flatBlockInclusion s)ᴴ := by
  let dim := fun t : Fin P.totalCopies ↦ Fin (P.flatDim t)
  let e : ((t : Fin P.totalCopies) × dim t) ≃ Fin P.totalDim :=
    finSigmaFinEquiv
  let E := Matrix.sigmaBlockInclusion dim s
  let B := fun t : Fin P.totalCopies ↦ P.flatWeight t • P.flatBasis t i
  change (Matrix.reindex e (Equiv.refl _) E)ᴴ *
      Matrix.reindex e e (Matrix.blockDiagonal' B) =
        B s * (Matrix.reindex e (Equiv.refl _) E)ᴴ
  rw [Matrix.conjTranspose_reindex]
  change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e Eᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ e e (Matrix.blockDiagonal' B) =
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _) (B s) *
          Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e Eᴴ
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) e e,
    Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) (Equiv.refl _) e,
    Matrix.sigmaBlockInclusion_conjTranspose_mul_blockDiagonal']

/-- Compressing the ambient tensor to a flattened sector recovers its exact
weighted block.

Source: arXiv:1606.00608, Section 2.3, equation `II_Aiplusk1`, lines 195--219.
Application context: Appendix C.2, Case I, lines 1571--1619. -/
theorem flatWeight_smul_flatBasis_eq_compression
    (P : SectorDecomposition d) (s : Fin P.totalCopies) (i : Fin d) :
    P.flatWeight s • P.flatBasis s i =
      (P.flatBlockInclusion s)ᴴ * P.toTensor i *
        P.flatBlockInclusion s := by
  symm
  rw [Matrix.mul_assoc, P.toTensor_mul_flatBlockInclusion s i,
    ← Matrix.mul_assoc, P.flatBlockInclusion_isometry s, Matrix.one_mul]

end MPSTensor.SectorDecomposition
