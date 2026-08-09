/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Peripheral.CyclicDecomposition
import TNLean.Channel.KrausCornerCompression

/-!
# Compression to cyclic sectors

This file contains the compression theorem for tensors supported on an
orthogonal projection, together with the resulting intertwining,
multiplicative, and star-preserving identities.

## Main declarations

* `exists_compressedTensor_of_supported_projection_with_letter`
* `exists_compressedTensor_of_supported_projection`

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Appendix A]
* [Wolf, *Quantum Channels & Operations*, Chapter 6]
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex

namespace MPSTensor

variable {d D : ℕ}

section Compression

variable {P : MatrixAlg D}

/-- Compress a tensor supported on an orthogonal projection to the corresponding sector bond
space.  The compressed tensor has the same sector MPVs and inherits the left-canonical equation.
Moreover, the compression equivalence sends each compressed letter back to the
ambient supported letter.

The theorem also records the compression isomorphism from the compressed matrix
algebra onto the corner subspace.  This isomorphism intertwines the compressed
adjoint transfer map with the ambient adjoint transfer map restricted to the
corner.  The strengthened form returns a rectangular support isometry
V : ℂ^n → ℂ^D with Vᴴ V = 1, V Vᴴ = P, and φ(X) = V X Vᴴ. -/
theorem exists_compressedTensor_of_supported_projection_with_letter_and_isometry
    (A : MPSTensor d D) (P : MatrixAlg D)
    (hP : IsOrthogonalProjection P)
    (hSupp : ∀ i : Fin d, P * A i * P = A i)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = P) :
    ∃ (n : ℕ) (C : MPSTensor d n)
      (φ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P)
      (V : Matrix (Fin D) (Fin n) ℂ),
      ((n : ℂ) = Matrix.trace P) ∧
      (∑ i : Fin d, (C i)ᴴ * C i = 1) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv C σ = Matrix.trace (P * evalWord A (List.ofFn σ))) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ,
        (φ (transferMap (d := d) (D := n) (fun i => (C i)ᴴ) X)).1 =
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) ((φ X).1)) ∧
      (∀ X Y : Matrix (Fin n) (Fin n) ℂ,
        (φ (X * Y)).1 = (φ X).1 * (φ Y).1) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, (φ Xᴴ).1 = ((φ X).1)ᴴ) ∧
      (∀ i : Fin d, (φ (C i)).1 = A i) ∧
      Vᴴ * V = 1 ∧
      V * Vᴴ = P ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, (φ X).1 = V * X * Vᴴ) := by
  obtain ⟨n, C, φ, V, hdim, hCtp, hIntertw, hMul, hStar, hLetter, hCompression,
    hVtV, hVVt, hφV⟩ :=
    Kraus.exists_corner_compression_of_supported_projection A P hP hSupp hTP
  have hPV : P * V = V := by
    rw [← hVVt, Matrix.mul_assoc, hVtV, Matrix.mul_one]
  have hIntertwineLetter : ∀ i : Fin d, A i * V = V * C i := by
    intro i
    calc
      A i * V = (P * A i * P) * V := by rw [hSupp i]
      _ = P * A i * (P * V) := by rw [Matrix.mul_assoc (P * A i) P V]
      _ = P * A i * V := by rw [hPV]
      _ = (V * Vᴴ) * A i * V := by rw [hVVt]
      _ = V * (Vᴴ * A i * V) := by simp only [Matrix.mul_assoc]
      _ = V * C i := by rw [hCompression i]
  have hEvalCompression (w : List (Fin d)) :
      evalWord C w = Vᴴ * evalWord A w * V := by
    calc
      evalWord C w = 1 * evalWord C w := (Matrix.one_mul _).symm
      _ = (Vᴴ * V) * evalWord C w := by rw [hVtV]
      _ = Vᴴ * (V * evalWord C w) := Matrix.mul_assoc _ _ _
      _ = Vᴴ * (evalWord A w * V) := by
        rw [evalWord_intertwine A C V hIntertwineLetter w]
      _ = Vᴴ * evalWord A w * V := (Matrix.mul_assoc _ _ _).symm
  refine ⟨n, C, φ, V, hdim, hCtp, ?_, ?_, hMul, hStar, hLetter, hVtV, hVVt, hφV⟩
  · intro N σ
    let w := List.ofFn σ
    change Matrix.trace (evalWord C w) = Matrix.trace (P * evalWord A w)
    rw [hEvalCompression]
    calc
      Matrix.trace (Vᴴ * evalWord A w * V) =
          Matrix.trace ((evalWord A w * V) * Vᴴ) := by
            rw [Matrix.mul_assoc]
            exact Matrix.trace_mul_comm _ _
      _ = Matrix.trace (evalWord A w * P) := by rw [Matrix.mul_assoc, hVVt]
      _ = Matrix.trace (P * evalWord A w) := Matrix.trace_mul_comm _ _
  · intro X
    simpa [Kraus.adjointMap, transferMap_apply] using hIntertw X

/-- Compress a tensor supported on an orthogonal projection to the corresponding sector bond
space.  The compressed tensor has the same sector MPVs and inherits the left-canonical equation.
Moreover, the compression equivalence sends each compressed letter back to the
ambient supported letter.

This is the projection of
`exists_compressedTensor_of_supported_projection_with_letter_and_isometry` that
forgets the support isometry. -/
theorem exists_compressedTensor_of_supported_projection_with_letter
    (A : MPSTensor d D) (P : MatrixAlg D)
    (hP : IsOrthogonalProjection P)
    (hSupp : ∀ i : Fin d, P * A i * P = A i)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = P) :
    ∃ (n : ℕ) (C : MPSTensor d n)
      (φ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P),
      ((n : ℂ) = Matrix.trace P) ∧
      (∑ i : Fin d, (C i)ᴴ * C i = 1) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv C σ = Matrix.trace (P * evalWord A (List.ofFn σ))) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ,
        (φ (transferMap (d := d) (D := n) (fun i => (C i)ᴴ) X)).1 =
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) ((φ X).1)) ∧
      (∀ X Y : Matrix (Fin n) (Fin n) ℂ,
        (φ (X * Y)).1 = (φ X).1 * (φ Y).1) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, (φ Xᴴ).1 = ((φ X).1)ᴴ) ∧
      (∀ i : Fin d, (φ (C i)).1 = A i) := by
  obtain ⟨n, C, φ, _V, hdim, hCtp, hCmpv, hIntertwine, hMul, hStar, hLetter,
    _hV_iso, _hV_range, _hEmbed_eq_V⟩ :=
    exists_compressedTensor_of_supported_projection_with_letter_and_isometry A P hP hSupp hTP
  exact ⟨n, C, φ, hdim, hCtp, hCmpv, hIntertwine, hMul, hStar, hLetter⟩

/-- Compress a tensor supported on an orthogonal projection to the corresponding sector bond
space.  The compressed tensor has the same sector MPVs and inherits the left-canonical equation.

This is the projection of
`exists_compressedTensor_of_supported_projection_with_letter` that forgets the
letter-expansion identity. -/
theorem exists_compressedTensor_of_supported_projection
    (A : MPSTensor d D) (P : MatrixAlg D)
    (hP : IsOrthogonalProjection P)
    (hSupp : ∀ i : Fin d, P * A i * P = A i)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = P) :
    ∃ (n : ℕ) (C : MPSTensor d n)
      (φ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P),
      ((n : ℂ) = Matrix.trace P) ∧
      (∑ i : Fin d, (C i)ᴴ * C i = 1) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv C σ = Matrix.trace (P * evalWord A (List.ofFn σ))) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ,
        (φ (transferMap (d := d) (D := n) (fun i => (C i)ᴴ) X)).1 =
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) ((φ X).1)) ∧
      (∀ X Y : Matrix (Fin n) (Fin n) ℂ,
        (φ (X * Y)).1 = (φ X).1 * (φ Y).1) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, (φ Xᴴ).1 = ((φ X).1)ᴴ) := by
  obtain ⟨n, C, φ, hdim, hCtp, hCmpv, hIntertwine, hMul, hStar, _hLetter⟩ :=
    exists_compressedTensor_of_supported_projection_with_letter A P hP hSupp hTP
  exact ⟨n, C, φ, hdim, hCtp, hCmpv, hIntertwine, hMul, hStar⟩

end Compression

end MPSTensor
