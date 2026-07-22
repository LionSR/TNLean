/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Peripheral.CyclicDecomposition

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
  classical
  obtain ⟨Umat, S, T, n, -, eST, eS, hUU, hU'U, hPdiag_std, hP_decomp,
    hPdiag_back, htrace, -⟩ := ProjectionSpectralSplit.ofOrthogonalProjection P hP
  let Pdiag : MatrixAlg D := Umatᴴ * P * Umat
  let P0 : Matrix (S ⊕ T) (S ⊕ T) ℂ :=
    Matrix.fromBlocks (1 : Matrix S S ℂ) 0 0 (0 : Matrix T T ℂ)
  let expand : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] MatrixAlg D :=
    cornerCompressionExpand Umat eST eS
  let φ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P :=
    cornerCompressionLinearEquiv (P := P) (Pdiag := Pdiag) Umat eST eS P0 rfl
      hP_decomp rfl hPdiag_std hPdiag_back hU'U hUU
  let V : Matrix (Fin D) (Fin n) ℂ := cornerCompressionIsometry Umat eST eS
  have hV_iso : Vᴴ * V = 1 := by
    exact cornerCompressionIsometry_conjTranspose_mul Umat eST eS hU'U
  have hExpand_one : expand 1 = P := by
    exact cornerCompressionExpand_one (P := P) (Pdiag := Pdiag) Umat eST eS P0 rfl
      hP_decomp hPdiag_back
  have hV_range : V * Vᴴ = P := by
    rw [show V * Vᴴ = expand 1 by
      simpa [V, expand] using
        (cornerCompressionExpand_eq_isometry Umat eST eS
          (1 : Matrix (Fin n) (Fin n) ℂ)).symm]
    exact hExpand_one
  have hφ_apply (X : Matrix (Fin n) (Fin n) ℂ) : (φ X).1 = expand X := rfl
  have hExpand_eq_V (X : Matrix (Fin n) (Fin n) ℂ) : expand X = V * X * Vᴴ := by
    simpa [expand, V] using cornerCompressionExpand_eq_isometry Umat eST eS X
  let C : MPSTensor d n := fun i => Vᴴ * A i * V
  have hLetter : ∀ i : Fin d, expand (C i) = A i := by
    intro i
    rw [hExpand_eq_V]
    change V * (Vᴴ * A i * V) * Vᴴ = A i
    calc
      V * (Vᴴ * A i * V) * Vᴴ = (V * Vᴴ) * A i * (V * Vᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = P * A i * P := by rw [hV_range]
      _ = A i := hSupp i
  have hIntertwineLetter : ∀ i : Fin d, A i * V = V * C i := by
    intro i
    have htemp : (V * Vᴴ) * A i * (V * Vᴴ) * V = V * (Vᴴ * A i * V) := by
      calc
        (V * Vᴴ) * A i * (V * Vᴴ) * V = ((V * Vᴴ) * A i) * ((V * Vᴴ) * V) := by
          rw [Matrix.mul_assoc]
        _ = ((V * Vᴴ) * A i) * (V * (Vᴴ * V)) := by rw [Matrix.mul_assoc]
        _ = ((V * Vᴴ) * A i) * (V * 1) := by rw [hV_iso]
        _ = ((V * Vᴴ) * A i) * V := by simp
        _ = (V * (Vᴴ * A i)) * V := by rw [Matrix.mul_assoc]
        _ = V * ((Vᴴ * A i) * V) := by rw [Matrix.mul_assoc]
        _ = V * (Vᴴ * A i * V) := rfl
    calc
      A i * V = (P * A i * P) * V := by rw [hSupp i]
      _ = (V * Vᴴ) * A i * (V * Vᴴ) * V := by rw [hV_range]
      _ = V * (Vᴴ * A i * V) := by rw [htemp]
      _ = V * C i := rfl
  have hEvalCompression (w : List (Fin d)) :
      evalWord C w = Vᴴ * evalWord A w * V := by
    calc
      evalWord C w = 1 * evalWord C w := (Matrix.one_mul _).symm
      _ = (Vᴴ * V) * evalWord C w := by rw [hV_iso]
      _ = Vᴴ * (V * evalWord C w) := Matrix.mul_assoc _ _ _
      _ = Vᴴ * (evalWord A w * V) := by
        rw [evalWord_intertwine A C V hIntertwineLetter w]
      _ = Vᴴ * evalWord A w * V := (Matrix.mul_assoc _ _ _).symm
  refine ⟨n, C, φ, V, htrace, ?_, ?_, ?_, ?_, ?_, ?_, hV_iso, hV_range, ?_⟩
  · apply φ.injective
    apply Subtype.ext
    rw [hφ_apply, hφ_apply]
    change expand (∑ i : Fin d, (C i)ᴴ * C i) = expand 1
    rw [map_sum]
    have hsum : (∑ i : Fin d, expand ((C i)ᴴ * C i)) = (∑ i : Fin d, (A i)ᴴ * A i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [cornerCompressionExpand_mul Umat eST eS hU'U,
        ← cornerCompressionExpand_conjTranspose Umat eST eS, hLetter]
    calc
      (∑ i : Fin d, expand ((C i)ᴴ * C i)) = (∑ i : Fin d, (A i)ᴴ * A i) := hsum
      _ = P := hTP
      _ = expand 1 := by rw [hExpand_one]
  · intro N σ
    let w := List.ofFn σ
    change Matrix.trace (evalWord C w) = Matrix.trace (P * evalWord A w)
    rw [hEvalCompression]
    calc
      Matrix.trace (Vᴴ * evalWord A w * V) =
          Matrix.trace ((evalWord A w * V) * Vᴴ) := by
            rw [Matrix.mul_assoc]
            exact Matrix.trace_mul_comm _ _
      _ = Matrix.trace (evalWord A w * P) := by rw [Matrix.mul_assoc, hV_range]
      _ = Matrix.trace (P * evalWord A w) := Matrix.trace_mul_comm _ _
  · intro Z
    rw [hφ_apply]
    change expand (transferMap (d := d) (D := n) (fun j => (C j)ᴴ) Z) =
      transferMap (d := d) (D := D) (fun j => (A j)ᴴ) (expand Z)
    simp only [transferMap_apply, Matrix.conjTranspose_conjTranspose]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [cornerCompressionExpand_mul Umat eST eS hU'U,
      cornerCompressionExpand_mul Umat eST eS hU'U,
      ← cornerCompressionExpand_conjTranspose Umat eST eS, hLetter]
  · intro X Y
    simp only [hφ_apply]
    exact cornerCompressionExpand_mul Umat eST eS hU'U X Y
  · intro X
    simp only [hφ_apply]
    exact (cornerCompressionExpand_conjTranspose Umat eST eS X).symm
  · intro i
    rw [hφ_apply]
    exact hLetter i
  · intro X
    rw [hφ_apply, hExpand_eq_V]

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
