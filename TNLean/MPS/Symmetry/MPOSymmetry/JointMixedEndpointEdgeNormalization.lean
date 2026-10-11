/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointEdgeFactors

/-!
# Joint polar compression and boundary-only edge normalization

Let the actual joint boundary columns be \(L=U_LP_L\) and \(R=U_RP_R\).
Compression by the isometric factors gives exactly \(P_L\) or \(P_R\)
on the corresponding one-sided core. Applying the inverse positive factor
therefore carries each compressed actual support onto that core support.
The adjacent physical site is acted on by the identity throughout.

The positive factors act on all block labels jointly. No diagonalization
by physical block label is asserted or needed. These local identities
are valid for empty labels and zero-dimensional fibers. They contain no
edge sum; at chain length two the sole edge must still be counted once.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777. That passage
defines the degenerate-case path and asserts, without proof, that its
Hamiltonian stays well behaved along the whole path (line 1777). The
boundary columns, their polar factors and the compression below are not in
the source; they are this library's proof of that assertion.
-/

open scoped Matrix BigOperators Kronecker ComplexOrder

namespace MPSTensor.MPOSymmetry

noncomputable section

variable {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}

private theorem polar_adjoint_mul_self {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (M : Matrix ι κ ℂ) (hM : Function.Injective M.mulVec) :
    (Matrix.polarIso M)ᴴ * M = Matrix.polarPos M := by
  calc
    (Matrix.polarIso M)ᴴ * M =
        (Matrix.polarIso M)ᴴ * (Matrix.polarIso M * Matrix.polarPos M) := by
      rw [Matrix.polarIso_mul_polarPos]
    _ = Matrix.polarPos M := by
      rw [← Matrix.mul_assoc, Matrix.isIsometry_polarIso_of_injective M hM,
        Matrix.one_mul]

private theorem inverse_polarPos_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (M : Matrix ι κ ℂ) (hM : Function.Injective M.mulVec) :
    (Matrix.polarPos M)⁻¹ * Matrix.polarPos M = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.posDef_polarPos_of_injective M hM).isUnit)

/-- Isometric compression of the actual first edge by the joint first
polar frame, with identity on the adjacent full physical alphabet.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedFirstEdgeCompressedMap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    ((x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) →ₗ[ℂ]
      (JointMixedFirstBoundaryIndex D₀ D₁ × Fin d₀ → ℂ) :=
  ((Matrix.polarIso (jointMixedFirstBoundaryColumns A₀ A₁))ᴴ ⊗ₖ
    (1 : Matrix (Fin d₀) (Fin d₀) ℂ)).mulVecLin.comp
      (jointMixedFirstEdgeBoundaryMap A₀ A₁)

/-- The reflected isometric compression of the actual last edge.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedLastEdgeCompressedMap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    ((x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) →ₗ[ℂ]
      (Fin d₀ × JointMixedLastBoundaryIndex D₀ D₁ → ℂ) :=
  ((1 : Matrix (Fin d₀) (Fin d₀) ℂ) ⊗ₖ
    (Matrix.polarIso (jointMixedLastBoundaryColumns A₀ A₁))ᴴ).mulVecLin.comp
      (jointMixedLastEdgeBoundaryMap A₀ A₁)

/-- The compressed first-edge coefficients have precisely one joint
positive weight, on the first boundary coordinate only.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstEdgeCompressedMap_eq_polarPos_core
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    jointMixedFirstEdgeCompressedMap A₀ A₁ X =
      (Matrix.polarPos (jointMixedFirstBoundaryColumns A₀ A₁) ⊗ₖ
          (1 : Matrix (Fin d₀) (Fin d₀) ℂ)) *ᵥ
        jointEndpointFirstEdgeCoreMap A₀ (fun x => D₀ x + D₁ x)
          (fun x => (X x).submatrix (Fin.castAdd (D₁ x)) id) := by
  change (_ ⊗ₖ _) *ᵥ jointMixedFirstEdgeBoundaryMap A₀ A₁ X = _
  rw [jointMixedFirstEdgeBoundaryMap_eq_columns_core, Matrix.mulVec_mulVec,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    polar_adjoint_mul_self _ (jointMixedFirstBoundaryColumns_injective A₀ A₁ h₀ h₁)]

/-- The compressed last-edge coefficients have one joint positive
weight on the last boundary coordinate, leaving the bulk site unchanged.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastEdgeCompressedMap_eq_polarPos_core
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    jointMixedLastEdgeCompressedMap A₀ A₁ X =
      ((1 : Matrix (Fin d₀) (Fin d₀) ℂ) ⊗ₖ
          Matrix.polarPos (jointMixedLastBoundaryColumns A₀ A₁)) *ᵥ
        jointEndpointLastEdgeCoreMap A₀ (fun x => D₀ x + D₁ x)
          (fun x => (X x).submatrix id (Fin.castAdd (D₁ x))) := by
  change (_ ⊗ₖ _) *ᵥ jointMixedLastEdgeBoundaryMap A₀ A₁ X = _
  rw [jointMixedLastEdgeBoundaryMap_eq_columns_core, Matrix.mulVec_mulVec,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    polar_adjoint_mul_self _ (jointMixedLastBoundaryColumns_injective A₀ A₁ h₀ h₁)]

/-- Inverting only the joint first-boundary weight recovers the actual
one-sided core coefficient for every virtual boundary.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstEdge_normalize_compressed
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    ((Matrix.polarPos (jointMixedFirstBoundaryColumns A₀ A₁))⁻¹ ⊗ₖ
        (1 : Matrix (Fin d₀) (Fin d₀) ℂ)) *ᵥ jointMixedFirstEdgeCompressedMap A₀ A₁ X =
      jointEndpointFirstEdgeCoreMap A₀ (fun x => D₀ x + D₁ x)
        (fun x => (X x).submatrix (Fin.castAdd (D₁ x)) id) := by
  rw [jointMixedFirstEdgeCompressedMap_eq_polarPos_core A₀ A₁ h₀ h₁,
    Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    inverse_polarPos_mul _ (jointMixedFirstBoundaryColumns_injective A₀ A₁ h₀ h₁),
    Matrix.one_kronecker_one, Matrix.one_mulVec]

/-- The inverse last-boundary weight recovers the reflected core
coefficient, with no normalization of an interior letter.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastEdge_normalize_compressed
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    ((1 : Matrix (Fin d₀) (Fin d₀) ℂ) ⊗ₖ
        (Matrix.polarPos (jointMixedLastBoundaryColumns A₀ A₁))⁻¹) *ᵥ
          jointMixedLastEdgeCompressedMap A₀ A₁ X =
      jointEndpointLastEdgeCoreMap A₀ (fun x => D₀ x + D₁ x)
        (fun x => (X x).submatrix id (Fin.castAdd (D₁ x))) := by
  rw [jointMixedLastEdgeCompressedMap_eq_polarPos_core A₀ A₁ h₀ h₁,
    Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    inverse_polarPos_mul _ (jointMixedLastBoundaryColumns_injective A₀ A₁ h₀ h₁),
    Matrix.one_kronecker_one, Matrix.one_mulVec]

/-- Boundary-only normalization carries the compressed actual first-edge
support exactly onto the full first core support. Surjectivity is proved
by padding rectangular virtual boundaries, with no dimension assumption.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem map_jointMixedFirstEdgeCompressed_range_eq_core
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    (jointMixedFirstEdgeCompressedMap A₀ A₁).range.map
        (((Matrix.polarPos (jointMixedFirstBoundaryColumns A₀ A₁))⁻¹ ⊗ₖ
          (1 : Matrix (Fin d₀) (Fin d₀) ℂ)).mulVecLin) =
      (jointEndpointFirstEdgeCoreMap A₀ (fun x => D₀ x + D₁ x)).range := by
  apply SetLike.coe_injective
  simp only [Submodule.map_coe, LinearMap.coe_range, ← Set.range_comp]
  change Set.range (fun X => (_ ⊗ₖ _) *ᵥ jointMixedFirstEdgeCompressedMap A₀ A₁ X) = _
  simp_rw [jointMixedFirstEdge_normalize_compressed A₀ A₁ h₀ h₁]
  exact (jointMixedFirstBoundaryExtraction_surjective (D₀ := D₀) (D₁ := D₁)).range_comp
    (jointEndpointFirstEdgeCoreMap A₀ (fun x => D₀ x + D₁ x))

/-- The corresponding exact last-edge support image. Labels are joint
before the change and remain unrestricted in the core coordinates.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem map_jointMixedLastEdgeCompressed_range_eq_core
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    (jointMixedLastEdgeCompressedMap A₀ A₁).range.map
        (((1 : Matrix (Fin d₀) (Fin d₀) ℂ) ⊗ₖ
          (Matrix.polarPos (jointMixedLastBoundaryColumns A₀ A₁))⁻¹).mulVecLin) =
      (jointEndpointLastEdgeCoreMap A₀ (fun x => D₀ x + D₁ x)).range := by
  apply SetLike.coe_injective
  simp only [Submodule.map_coe, LinearMap.coe_range, ← Set.range_comp]
  change Set.range (fun X => (_ ⊗ₖ _) *ᵥ jointMixedLastEdgeCompressedMap A₀ A₁ X) = _
  simp_rw [jointMixedLastEdge_normalize_compressed A₀ A₁ h₀ h₁]
  exact (jointMixedLastBoundaryExtraction_surjective (D₀ := D₀) (D₁ := D₁)).range_comp
    (jointEndpointLastEdgeCoreMap A₀ (fun x => D₀ x + D₁ x))

end

end MPSTensor.MPOSymmetry
