/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointFamily
import TNLean.MPS.Symmetry.MPOSymmetry.JointInsertedOpenKernel

/-!
# Joint supports of the actual mixed block family

The simultaneous span of the mixed family is derived from the endpoint
families. The prescribed bond matrices are continuous and remain nonzero,
including at both singular endpoints. The joint inserted boundary maps
therefore give constant-dimensional local supports and the exact open-chain
kernels, with continuous orthogonal projectors at every fixed chain length.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
These finite-volume statements assert neither a uniform gap nor MPO symmetry.
-/

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

variable {d₀ d₁ r N : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- Appending the omitted insertion recovers the ordinary word of the
right-weighted tensor. Source: arXiv:2203.12563, Section 5, lines 1690–1692
and 1695–1704. -/
theorem insertedEvalWord_mul_right {d D : ℕ} (A : MPSTensor d D)
    (W : Matrix (Fin D) (Fin D) ℂ) {w : List (Fin d)} (hw : w ≠ []) :
    insertedEvalWord A W w * W = Kraus.evalWord (fun i => A i * W) w := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons i w =>
      change A i * Kraus.evalWord (fun j => W * A j) w * W =
        (A i * W) * Kraus.evalWord (fun j => A j * W) w
      rw [Matrix.mul_assoc, Kraus.evalWord_intertwine
        (fun j => W * A j) (fun j => A j * W) W
        (fun j => Matrix.mul_assoc W (A j) W) w]
      simp only [Matrix.mul_assoc]

/-- Multiplication of the joint virtual boundary by the last insertion
relates the canonical and extended coefficient maps.
Source: arXiv:2203.12563, Section 5, lines 1690–1692 and 1695–1704. -/
theorem blockGroundSpaceMap_rightMul_eq_inserted {d : ℕ} {dim : Fin r → ℕ}
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W X : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ) (hN : 0 < N) :
    blockGroundSpaceMap (fun x i => A x i * W x) N X =
      blockInsertedGroundSpaceMap A W N (fun x => W x * X x) := by
  ext σ
  simp only [blockGroundSpaceMap_apply, blockInsertedGroundSpaceMap_apply,
    Finset.sum_apply, groundSpaceMap_apply, insertedGroundSpaceMap_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [← insertedEvalWord_mul_right (A x) (W x)
    (mt List.ofFn_eq_nil_iff.mp (Nat.ne_of_gt hN)), Matrix.mul_assoc]

/-- Invertible block insertions leave the canonical and extended joint
coefficient supports equal. No physical block orthogonality is used.
Source: arXiv:2203.12563, Section 5, lines 1690–1692 and 1695–1704. -/
theorem range_blockInsertedGroundSpaceMap_eq_of_isUnit {d : ℕ} {dim : Fin r → ℕ}
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, IsUnit (W x)) (hN : 0 < N) :
    (blockInsertedGroundSpaceMap A W N).range =
      (blockGroundSpaceMap (fun x i => A x i * W x) N).range := by
  classical
  choose u hu using hW
  apply le_antisymm
  · rintro ψ ⟨X, rfl⟩
    refine ⟨fun x => ↑((u x)⁻¹) * X x, ?_⟩
    rw [blockGroundSpaceMap_rightMul_eq_inserted _ _ _ hN]
    congr 1
    funext x
    simp [← hu x, Matrix.mul_assoc]
  · rintro ψ ⟨X, rfl⟩
    exact ⟨fun x => W x * X x,
      (blockGroundSpaceMap_rightMul_eq_inserted A W X hN).symm⟩

/-- In the interior, the actual joint extended coefficient support is the
sum of the canonical block supports of the actual path.
Source: arXiv:2203.12563, Section 5, lines 1690–1692 and 1695–1777. -/
theorem jointMixedEndpoint_extendedGroundSpace_eq_iSup
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (hN : 0 < N) :
    (blockInsertedGroundSpaceMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) N).range =
        ⨆ x, groundSpace (jointMixedEndpointInterpolation A₀ A₁ γ x) N := by
  rw [range_blockInsertedGroundSpaceMap_eq_of_isUnit _ _
    (fun x => isUnit_bondInterpolationMatrix_of_mem_Ioo hγ) hN]
  exact range_blockGroundSpaceMap _ N

/-- The prescribed joint insertions are continuous and nonzero at every real
parameter when both endpoint bond dimensions are positive.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem continuous_nonzero_jointMixedEndpointInsertion
    (hD₀ : ∀ x, 0 < D₀ x) (hD₁ : ∀ x, 0 < D₁ x) :
    (Continuous fun γ : ℝ => fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) ∧
      (∀ γ : ℝ, ∀ x, bondInterpolationMatrix (D₀ x) (D₁ x) γ ≠ 0) :=
  ⟨continuous_pi fun x => continuous_bondInterpolationMatrix (D₀ x) (D₁ x),
    fun γ x => bondInterpolationMatrix_ne_zero (hD₀ x) (hD₁ x) γ⟩

/-- The actual joint extended boundary map is injective through both singular
endpoints. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_blockInsertedBoundaryMap_injective
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₀ : ∀ x, 0 < D₀ x) (hD₁ : ∀ x, 0 < D₁ x) (γ : ℝ) (hN : 0 < N) :
    Function.Injective (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) N) :=
  blockInsertedBoundaryMap_injective _ (wordTupleSpanTop_jointMixedEndpointBase A₀ A₁ h₀ h₁)
    _ (fun x => bondInterpolationMatrix_ne_zero (hD₀ x) (hD₁ x) γ) hN

/-- The joint extended support has the sum of squared enlarged block
sizes, including at the two singular endpoints.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem finrank_jointMixedEndpoint_extendedBoundarySupport
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₀ : ∀ x, 0 < D₀ x) (hD₁ : ∀ x, 0 < D₁ x) (γ : ℝ) (hN : 0 < N) :
    Module.finrank ℂ (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) N).range =
        ∑ x, (D₀ x + D₁ x) * (D₀ x + D₁ x) :=
  finrank_range_blockInsertedBoundaryMap _ (wordTupleSpanTop_jointMixedEndpointBase A₀ A₁ h₀ h₁)
    _ (fun x => bondInterpolationMatrix_ne_zero (hD₀ x) (hD₁ x) γ) hN

/-- The actual joint boundary maps vary continuously through both endpoints.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem continuous_jointMixedEndpoint_blockInsertedBoundaryMap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (N : ℕ) :
    Continuous fun γ : ℝ => blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) N :=
  continuous_blockInsertedBoundaryMap_family (fun _ => jointMixedEndpointBase A₀ A₁)
    (fun _ => continuous_const) _
    (fun x => continuous_bondInterpolationMatrix (D₀ x) (D₁ x)) N

/-- Orthogonal projection onto the actual joint support is continuous at
every positive fixed chain length. Source: arXiv:2203.12563,
Section 5, lines 1695–1777. -/
theorem continuous_jointMixedEndpoint_extendedBoundarySupport_starProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₀ : ∀ x, 0 < D₀ x) (hD₁ : ∀ x, 0 < D₁ x) (hN : 0 < N) :
    Continuous fun γ : ℝ => (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) N).range.starProjection := by
  have h := ContinuousLinearMap.continuous_injectiveRangeProjector
    (fun γ : ℝ => blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) N)
    (continuous_jointMixedEndpoint_blockInsertedBoundaryMap A₀ A₁ N)
    (fun γ => jointMixedEndpoint_blockInsertedBoundaryMap_injective A₀ A₁ h₀ h₁ hD₀ hD₁ γ hN)
  simpa only [ContinuousLinearMap.injectiveRangeProjector_eq_starProjection] using h

/-- The actual two-site joint support determines the exact open-chain kernel
at every length at least two. Source: arXiv:2203.12563,
Section 5, lines 1695–1777. -/
theorem ker_openInteractionHamiltonianES_jointMixedEndpoint_eq
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₀ : ∀ x, 0 < D₀ x) (hD₁ : ∀ x, 0 < D₁ x) (γ : ℝ) (hN : 2 ≤ N) :
    LinearMap.ker (openInteractionHamiltonianES
      (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) 2).range.starProjection).toLinearMap N) =
      (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) N).range :=
  ker_openInteractionHamiltonianES_blockInserted_eq _
    (wordTupleSpanTop_jointMixedEndpointBase A₀ A₁ h₀ h₁) _
    (fun x => bondInterpolationMatrix_ne_zero (hD₀ x) (hD₁ x) γ) hN

/-- The open-kernel projector for the actual family is continuous at each
fixed chain length, with no gap assumption.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem continuous_ker_openInteractionHamiltonianES_jointMixedEndpoint_starProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₀ : ∀ x, 0 < D₀ x) (hD₁ : ∀ x, 0 < D₁ x) (hN : 2 ≤ N) :
    Continuous fun γ : ℝ => (LinearMap.ker (openInteractionHamiltonianES
      (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) 2).range.starProjection).toLinearMap
          N)).starProjection :=
  continuous_ker_openInteractionHamiltonianES_blockInserted_starProjection
    (fun _ => jointMixedEndpointBase A₀ A₁) (fun _ => continuous_const)
    (fun γ x => bondInterpolationMatrix (D₀ x) (D₁ x) γ)
    (fun x => continuous_bondInterpolationMatrix (D₀ x) (D₁ x))
    (fun _ => wordTupleSpanTop_jointMixedEndpointBase A₀ A₁ h₀ h₁)
    (fun γ x => bondInterpolationMatrix_ne_zero (hD₀ x) (hD₁ x) γ) hN

end MPSTensor.MPOSymmetry
