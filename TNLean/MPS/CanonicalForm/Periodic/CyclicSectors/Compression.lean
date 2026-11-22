/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausMap.KrausCornerCompression
import QICLean.Channel.Peripheral.CyclicDecomposition
import QICLean.Kraus.Transfer
import TNLean.MPS.Tensor.Defs

/-!
# Compression to cyclic sectors

This file contains the compression theorem for tensors supported on an
orthogonal projection, together with the resulting intertwining,
multiplicative, and star-preserving identities.

## Main declarations

* `exists_compressedTensor_of_supported_projection_with_letter_and_isometry`

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Appendix A]
* [Wolf, *Quantum Channels & Operations*, Chapter 6]

## Positive-length MPV preservation for cyclic-sector compression

This file extracts the positive-length MPV consequence of the supported
compression theorem.

### Main declarations

* `exists_compressedTensor_of_supported_projection_pos_mpv`

### References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Appendix A]
-/

section

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
        mpv C σ = Matrix.trace (P * Kraus.evalWord A (List.ofFn σ))) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ,
        (φ (Kraus.transferMap (ι := Fin d) (n := Fin n) (fun i => (C i)ᴴ) X)).1 =
          Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) ((φ X).1)) ∧
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
      Kraus.evalWord C w = Vᴴ * Kraus.evalWord A w * V := by
    calc
      Kraus.evalWord C w = 1 * Kraus.evalWord C w := (Matrix.one_mul _).symm
      _ = (Vᴴ * V) * Kraus.evalWord C w := by rw [hVtV]
      _ = Vᴴ * (V * Kraus.evalWord C w) := Matrix.mul_assoc _ _ _
      _ = Vᴴ * (Kraus.evalWord A w * V) := by
        rw [Kraus.evalWord_intertwine A C V hIntertwineLetter w]
      _ = Vᴴ * Kraus.evalWord A w * V := (Matrix.mul_assoc _ _ _).symm
  refine ⟨n, C, φ, V, hdim, hCtp, ?_, ?_, hMul, hStar, hLetter, hVtV, hVVt, hφV⟩
  · intro N σ
    let w := List.ofFn σ
    change Matrix.trace (Kraus.evalWord C w) = Matrix.trace (P * Kraus.evalWord A w)
    rw [hEvalCompression]
    calc
      Matrix.trace (Vᴴ * Kraus.evalWord A w * V) =
          Matrix.trace ((Kraus.evalWord A w * V) * Vᴴ) := by
            rw [Matrix.mul_assoc]
            exact Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Kraus.evalWord A w * P) := by rw [Matrix.mul_assoc, hVVt]
      _ = Matrix.trace (P * Kraus.evalWord A w) := Matrix.trace_mul_comm _ _
  · intro X
    simpa [Kraus.adjointMap, Kraus.transferMap_apply] using hIntertw X

end Compression

end MPSTensor

end

section

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex

namespace MPSTensor

variable {d D : ℕ}

section CompressionPositiveMPV

/-- A supported-projection compression preserves MPVs at all positive lengths.

This is the usable replacement for a rectangular `SameMPV₂` statement:
compression changes the `N = 0` coefficient from `trace 1 = D` to `trace P`,
so exact all-length equality is false in general, but every positive-length MPV
is preserved. -/
theorem exists_compressedTensor_of_supported_projection_pos_mpv
    (A : MPSTensor d D) (P : MatrixAlg D)
    (hP : IsOrthogonalProjection P)
    (hSupp : ∀ i : Fin d, P * A i * P = A i)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = P) :
    ∃ (n : ℕ) (C : MPSTensor d n),
      ((n : ℂ) = Matrix.trace P) ∧
      (∑ i : Fin d, (C i)ᴴ * C i = 1) ∧
      (∀ {N : ℕ}, 0 < N → ∀ σ : Fin N → Fin d, mpv A σ = mpv C σ) := by
  obtain ⟨dim, C, _φ, _V, hdim, hCtp, hCmpv, _hIntertwine, _hMul, _hStar, _hLetter,
    _hV_iso, _hV_range, _hEmbed⟩ :=
    exists_compressedTensor_of_supported_projection_with_letter_and_isometry A P hP hSupp hTP
  refine ⟨dim, C, hdim, hCtp, ?_⟩
  have hleft : ∀ i : Fin d, P * A i = A i := by
    intro i
    calc
      P * A i = P * (P * A i * P) := by rw [hSupp i]
      _ = (P * P) * A i * P := by simp only [Matrix.mul_assoc]
      _ = P * A i * P := by rw [hP.2]
      _ = A i := by simpa [Matrix.mul_assoc] using hSupp i
  have hword :
      ∀ {w : List (Fin d)}, w ≠ [] → P * Kraus.evalWord A w = Kraus.evalWord A w := by
    intro w hw
    cases w with
    | nil =>
        cases hw rfl
    | cons i w =>
        calc
          P * Kraus.evalWord A (i :: w) = P * (A i * Kraus.evalWord A w) := by rfl
          _ = (P * A i) * Kraus.evalWord A w := by rw [Matrix.mul_assoc]
          _ = A i * Kraus.evalWord A w := by rw [hleft i]
          _ = Kraus.evalWord A (i :: w) := by rfl
  intro N hN σ
  have hPw : P * Kraus.evalWord A (List.ofFn σ) = Kraus.evalWord A (List.ofFn σ) := by
    apply hword
    exact List.ne_nil_of_length_pos (by simpa only [List.length_ofFn] using hN)
  calc
    mpv A σ = Matrix.trace (Kraus.evalWord A (List.ofFn σ)) := by rfl
    _ = Matrix.trace (P * Kraus.evalWord A (List.ofFn σ)) :=
          congrArg Matrix.trace hPw.symm
    _ = mpv C σ := (hCmpv N σ).symm

end CompressionPositiveMPV

end MPSTensor

end
