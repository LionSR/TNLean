/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CornerCompression
import TNLean.Channel.KrausMap

/-!
# Compression of a finite Kraus family to a projection corner

A finite matrix family supported on an orthogonal projection can be represented on the
support coordinates of that projection. The resulting family is trace-preserving when the
ambient normalization equals the projection. The support isometry identifies its Kraus map
and adjoint map with the corresponding ambient corner actions.

## Main declaration

* `Kraus.exists_cornerCompression_of_supported_projection`: compression of a supported
  finite Kraus family to the support matrix algebra.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

/-- Compress a finite matrix family supported on an orthogonal projection to the support
matrix algebra. The result includes the corner equivalence, its support isometry, the
trace-preserving normalization, the adjoint-map intertwining, and the algebraic identities
needed to move between the compressed and ambient corners. -/
theorem exists_cornerCompression_of_supported_projection
    (A : Fin d → MatrixAlg D) (P : MatrixAlg D)
    (hP : IsOrthogonalProjection P)
    (hSupp : ∀ i : Fin d, P * A i * P = A i)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = P) :
    ∃ (n : ℕ) (C : Fin d → MatrixAlg n)
      (φ : MatrixAlg n ≃ₗ[ℂ] cornerSubmodule P)
      (V : Matrix (Fin D) (Fin n) ℂ),
      ((n : ℂ) = Matrix.trace P) ∧
      IsTP C ∧
      (∀ X : MatrixAlg n,
        (φ (adjointMap C X)).1 = adjointMap A (φ X).1) ∧
      (∀ X Y : MatrixAlg n, (φ (X * Y)).1 = (φ X).1 * (φ Y).1) ∧
      (∀ X : MatrixAlg n, (φ Xᴴ).1 = ((φ X).1)ᴴ) ∧
      (∀ i : Fin d, (φ (C i)).1 = A i) ∧
      (∀ i : Fin d, C i = Vᴴ * A i * V) ∧
      Vᴴ * V = 1 ∧
      V * Vᴴ = P ∧
      (∀ X : MatrixAlg n, (φ X).1 = V * X * Vᴴ) := by
  classical
  obtain ⟨Umat, S, T, n, -, eST, eS, hUU, hU'U, hPdiag_std, hP_decomp,
    hPdiag_back, htrace, -⟩ := ProjectionSpectralSplit.ofOrthogonalProjection P hP
  let Pdiag : MatrixAlg D := Umatᴴ * P * Umat
  let P0 : Matrix (S ⊕ T) (S ⊕ T) ℂ :=
    Matrix.fromBlocks (1 : Matrix S S ℂ) 0 0 (0 : Matrix T T ℂ)
  let expand : MatrixAlg n →ₗ[ℂ] MatrixAlg D :=
    cornerCompressionExpand Umat eST eS
  let φ : MatrixAlg n ≃ₗ[ℂ] cornerSubmodule P :=
    cornerCompressionLinearEquiv (P := P) (Pdiag := Pdiag) Umat eST eS P0 rfl
      hP_decomp rfl hPdiag_std hPdiag_back hU'U hUU
  let V : Matrix (Fin D) (Fin n) ℂ := cornerCompressionIsometry Umat eST eS
  have hV_iso : Vᴴ * V = 1 :=
    cornerCompressionIsometry_conjTranspose_mul Umat eST eS hU'U
  have hExpand_one : expand 1 = P :=
    cornerCompressionExpand_one (P := P) (Pdiag := Pdiag) Umat eST eS P0 rfl
      hP_decomp hPdiag_back
  have hV_range : V * Vᴴ = P := by
    rw [show V * Vᴴ = expand 1 by
      simpa [V, expand] using
        (cornerCompressionExpand_eq_isometry Umat eST eS (1 : MatrixAlg n)).symm]
    exact hExpand_one
  have hφ_apply (X : MatrixAlg n) : (φ X).1 = expand X := rfl
  have hExpand_eq_V (X : MatrixAlg n) : expand X = V * X * Vᴴ := by
    simpa [expand, V] using cornerCompressionExpand_eq_isometry Umat eST eS X
  let C : Fin d → MatrixAlg n := fun i => Vᴴ * A i * V
  have hCompression : ∀ i : Fin d, C i = Vᴴ * A i * V := fun _ => rfl
  have hLetter : ∀ i : Fin d, expand (C i) = A i := by
    intro i
    rw [hExpand_eq_V]
    change V * (Vᴴ * A i * V) * Vᴴ = A i
    calc
      V * (Vᴴ * A i * V) * Vᴴ = (V * Vᴴ) * A i * (V * Vᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = P * A i * P := by rw [hV_range]
      _ = A i := hSupp i
  refine ⟨n, C, φ, V, htrace, ?_, ?_, ?_, ?_, ?_, hCompression,
    hV_iso, hV_range, ?_⟩
  · change ∑ i : Fin d, (C i)ᴴ * C i = 1
    apply φ.injective
    apply Subtype.ext
    rw [hφ_apply, hφ_apply, map_sum]
    have hsum : (∑ i : Fin d, expand ((C i)ᴴ * C i)) =
        ∑ i : Fin d, (A i)ᴴ * A i := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [cornerCompressionExpand_mul Umat eST eS hU'U,
        ← cornerCompressionExpand_conjTranspose Umat eST eS, hLetter]
    calc
      (∑ i : Fin d, expand ((C i)ᴴ * C i)) = ∑ i : Fin d, (A i)ᴴ * A i := hsum
      _ = P := hTP
      _ = expand 1 := by rw [hExpand_one]
  · intro Z
    change expand (adjointMap C Z) = adjointMap A (expand Z)
    simp only [adjointMap_apply]
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

end Kraus
