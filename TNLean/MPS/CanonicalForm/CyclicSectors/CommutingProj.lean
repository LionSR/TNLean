/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.CyclicSectors.Basic
import TNLean.MPS.CanonicalForm.CyclicSectors.Compression

/-!
# Cyclic-sector decompositions from commuting projections

This file assembles the per-sector compression theorem into a direct-sum
decomposition when a left-canonical tensor commutes with a family of
orthogonal projections.

## Main declarations

* `exists_blockDecomp_of_commuting_projections_with_letter`
* `exists_blockDecomp_of_commuting_projections`

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Appendix A]
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex

namespace MPSTensor

variable {d D : ℕ}

section CommutingProjectionDecomposition

variable {m : ℕ}

/-- If a left-canonical tensor commutes with a family of orthogonal projections summing to `1`,
then it decomposes into compressed sectors whose direct-sum tensor is `SameMPV₂`-equivalent to the
original tensor. The compression isomorphism also sends each compressed sector
letter to the corresponding ambient corner P_k A_i P_k.

For each sector k, the compression isomorphism φ_k identifies the compressed
matrix algebra with the corner of P_k. Its intertwining identity identifies
the compressed adjoint transfer map with the sector adjoint transfer map on
that corner, so irreducibility and primitivity are preserved across the
compression. -/
theorem exists_blockDecomp_of_commuting_projections_with_letter_and_isometry
    (A : MPSTensor d D)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hComm : ∀ k : Fin m, ∀ i : Fin d, P k * A i = A i * P k) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor d (dim k))
      (φ : (k : Fin m) →
        Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
      (V : (k : Fin m) → Matrix (Fin D) (Fin (dim k)) ℂ),
      (∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
      (∀ k (N : ℕ) (σ : Fin N → Fin d),
        mpv (blocks k) σ = (P k * evalWord A (List.ofFn σ)).trace) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (transferMap (d := d) (D := dim k)
            (fun i => (blocks k i)ᴴ) X)).1 =
          transferMap (d := d) (D := D)
            (fun i => (P k * A i)ᴴ) ((φ k X).1)) ∧
      (∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k Xᴴ).1 = ((φ k X).1)ᴴ) ∧
      (∀ k (i : Fin d), (φ k (blocks k i)).1 = P k * A i * P k) ∧
      (∀ k, (V k)ᴴ * V k = 1) ∧
      (∀ k, V k * (V k)ᴴ = P k) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k X).1 = V k * X * (V k)ᴴ) := by
  -- For each k, sector tensor P_k * A_i is P_k-supported
  have hSectorSupp : ∀ k i, P k * (P k * A i) * P k = P k * A i := by
    intro k i
    rw [← Matrix.mul_assoc (P k) (P k) _, (hPproj k).2,
      hComm k i, Matrix.mul_assoc, (hPproj k).2]
  -- TP condition for each sector
  have hSectorTP : ∀ k, ∑ i : Fin d, (P k * A i)ᴴ * (P k * A i) = P k := by
    intro k
    have hterm : ∀ i, (P k * A i)ᴴ * (P k * A i) = (A i)ᴴ * A i * P k := by
      intro i
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (P k)ᴴ (P k) (A i), (hPproj k).1.eq, (hPproj k).2]
      rw [hComm k i, ← Matrix.mul_assoc]
    simp_rw [hterm, ← Finset.sum_mul, hLeft, Matrix.one_mul]
  -- Apply compression to each sector
  choose dim blocks φ V hDim hTPblocks hMPVblocks hIntertwine hMul hStar hLetterRaw
    hV_iso hV_range hEmbed using fun k =>
    exists_compressedTensor_of_supported_projection_with_letter_and_isometry
      (fun i => P k * A i) (P k) (hPproj k) (hSectorSupp k) (hSectorTP k)
  -- Per-sector trace relation: mpv(blocks k) σ = tr(P_k · evalWord A σ)
  have hSectorTrace : ∀ k (N : ℕ) (σ : Fin N → Fin d),
      mpv (blocks k) σ = (P k * evalWord A (List.ofFn σ)).trace := by
    intro k N σ
    rw [hMPVblocks k N σ]
    congr 1
    exact left_mul_evalWord_leftSectorTensor_of_commutes (P k) A (hPproj k).2 (hComm k) _
  have hLetter : ∀ k (i : Fin d), (φ k (blocks k i)).1 = P k * A i * P k := by
    intro k i
    calc
      (φ k (blocks k i)).1 = P k * A i := hLetterRaw k i
      _ = P k * A i * P k := by
          calc
            P k * A i = A i * P k := hComm k i
            _ = A i * (P k * P k) := by rw [(hPproj k).2]
            _ = (A i * P k) * P k := by rw [Matrix.mul_assoc]
            _ = (P k * A i) * P k := by rw [← hComm k i]
  refine ⟨dim, blocks, φ, V, hTPblocks, ?_, hSectorTrace, hIntertwine, hMul, hStar,
    hLetter, hV_iso, hV_range, hEmbed⟩
  -- SameMPV₂ follows from summing per-sector traces over the projection partition
  intro N σ
  rw [mpv_toTensorFromBlocks_eq_sum]; simp only [one_pow, one_smul]
  simp only [mpv, coeff]
  conv_lhs => rw [show evalWord A (List.ofFn σ) = 1 * evalWord A (List.ofFn σ) from by
    rw [Matrix.one_mul]]
  rw [show (1 : MatrixAlg D) = ∑ k : Fin m, P k from hPsum.symm]
  rw [Finset.sum_mul, Matrix.trace_sum]
  congr 1; ext k
  exact (hSectorTrace k N σ).symm

/-- If a left-canonical tensor commutes with a family of orthogonal projections summing to `1`,
then it decomposes into compressed sectors whose direct-sum tensor is `SameMPV₂`-equivalent to the
original tensor. The compression isomorphism also sends each compressed sector
letter to the corresponding ambient corner P_k A_i P_k.

This is the projection of
`exists_blockDecomp_of_commuting_projections_with_letter_and_isometry` that forgets
the support isometries. -/
theorem exists_blockDecomp_of_commuting_projections_with_letter
    (A : MPSTensor d D)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hComm : ∀ k : Fin m, ∀ i : Fin d, P k * A i = A i * P k) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor d (dim k))
      (φ : (k : Fin m) →
        Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)),
      (∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
      (∀ k (N : ℕ) (σ : Fin N → Fin d),
        mpv (blocks k) σ = (P k * evalWord A (List.ofFn σ)).trace) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (transferMap (d := d) (D := dim k)
            (fun i => (blocks k i)ᴴ) X)).1 =
          transferMap (d := d) (D := D)
            (fun i => (P k * A i)ᴴ) ((φ k X).1)) ∧
      (∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k Xᴴ).1 = ((φ k X).1)ᴴ) ∧
      (∀ k (i : Fin d), (φ k (blocks k i)).1 = P k * A i * P k) := by
  obtain ⟨dim, blocks, φ, _V, hTPblocks, hMPV, hSectorTrace, hIntertwine, hMul,
    hStar, hLetter, _hV_iso, _hV_range, _hEmbed⟩ :=
    exists_blockDecomp_of_commuting_projections_with_letter_and_isometry
      A P hPproj hPsum hLeft hComm
  exact ⟨dim, blocks, φ, hTPblocks, hMPV, hSectorTrace, hIntertwine, hMul, hStar,
    hLetter⟩

/-- If a left-canonical tensor commutes with a family of orthogonal projections summing to `1`,
then it decomposes into compressed sectors whose direct-sum tensor is `SameMPV₂`-equivalent to the
original tensor.

This is the projection of
`exists_blockDecomp_of_commuting_projections_with_letter` that forgets the
letter-expansion identity. -/
theorem exists_blockDecomp_of_commuting_projections
    (A : MPSTensor d D)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hComm : ∀ k : Fin m, ∀ i : Fin d, P k * A i = A i * P k) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor d (dim k))
      (φ : (k : Fin m) →
        Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)),
      (∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
      (∀ k (N : ℕ) (σ : Fin N → Fin d),
        mpv (blocks k) σ = (P k * evalWord A (List.ofFn σ)).trace) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (transferMap (d := d) (D := dim k)
            (fun i => (blocks k i)ᴴ) X)).1 =
          transferMap (d := d) (D := D)
            (fun i => (P k * A i)ᴴ) ((φ k X).1)) ∧
      (∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k Xᴴ).1 = ((φ k X).1)ᴴ) := by
  obtain ⟨dim, blocks, φ, hLC, hMPV, hTrace, hIntertwine, hMul, hStar, _hLetter⟩ :=
    exists_blockDecomp_of_commuting_projections_with_letter A P hPproj hPsum hLeft hComm
  exact ⟨dim, blocks, φ, hLC, hMPV, hTrace, hIntertwine, hMul, hStar⟩

end CommutingProjectionDecomposition

end MPSTensor
