/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IsometricFrameEmbedding
import TNLean.MPS.Symmetry.EmbeddedInjectiveGappedPath

/-!
# Physical embeddings selected by the polar frame

The isometric polar factor of an injective tensor occupies a copy of its
virtual pair space. Given another isometric frame, the physical embedding
replaces the occupied frame and retains its orthogonal complement in a
second summand. Its polar endpoint has exactly the prescribed target frame.

**Scope restriction (one-site injective tensors):** the parent paths constructed
here are the single-block, one-site injective case of arXiv:1010.3732,
Sections II.C and II.F.2, equation eq:1d-sym:jointsym. The several-block
case is documented in `docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.
-/

open scoped Matrix Kronecker

namespace MPSTensor

variable {d m D : ℕ}

/-- The physical isometry selected by the tensor's polar frame and a
prescribed target frame. Source context: arXiv:1010.3732, Sections II.C
and II.F.2, equation eq:1d-sym:jointsym. -/
noncomputable def polarFrameEmbedding (A : MPSTensor d D)
    (W : Matrix (Fin m) (Fin (D * D)) ℂ) : Matrix (Fin (m + d)) (Fin d) ℂ :=
  Matrix.finIsometricFrameEmbedding (polarIsoMatrix A) W

/-- Replacing the polar frame preserves the entire physical inner product.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem polarFrameEmbedding_isometry {A : MPSTensor d D}
    (hA : Kraus.IsInjective A) (W : Matrix (Fin m) (Fin (D * D)) ℂ)
    (hW : Wᴴ * W = 1) : (polarFrameEmbedding A W)ᴴ * polarFrameEmbedding A W = 1 := by
  exact Matrix.finIsometricFrameEmbedding_isometry _ W
    (isIsometry_polarIsoMatrix_of_isInjective hA) hW

/-- The embedded polar endpoint has the prescribed target frame and zero
spectator component. Source context: arXiv:1010.3732, Sections II.C and
II.F.2, equation eq:1d-sym:jointsym. -/
theorem polarFrameEmbedding_polar_endpoint {A : MPSTensor d D}
    (hA : Kraus.IsInjective A) (W : Matrix (Fin m) (Fin (D * D)) ℂ) :
    rotatePhysical (polarFrameEmbedding A W) (polarIsometricTensor A) =
      ofPhysicalMatrix ((Matrix.fromRows W 0).submatrix
        finSumFinEquiv.symm finProdFinEquiv) := by
  apply physicalMatrix_injective
  have h := Matrix.finIsometricFrameEmbedding_mul_frame (polarIsoMatrix A) W
    (isIsometry_polarIsoMatrix_of_isInjective hA)
  ext i p
  simpa [physicalMatrix_rotatePhysical, polarIsometricTensor,
    polarFrameEmbedding, polarIsoMatrix, virtualPairEquiv, Matrix.mul_apply,
    Matrix.submatrix_apply] using congrFun (congrFun h i) (finProdFinEquiv p)

/-- The polar frame intertwines the original physical action with the
virtual pair action in configuration indices. Source: arXiv:1010.3732,
Section II.C, isometric form and symmetries. -/
theorem polarIsoMatrix_covariance_of_isInjective {A : MPSTensor d D}
    (hA : Kraus.IsInjective A) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (K : Matrix.unitaryGroup (Fin D × Fin D) ℂ)
    (hCov : (U : Matrix (Fin d) (Fin d) ℂ) * physicalMatrix A =
      physicalMatrix A * (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)) :
    (U : Matrix (Fin d) (Fin d) ℂ) * polarIsoMatrix A =
      polarIsoMatrix A * Matrix.reindex finProdFinEquiv finProdFinEquiv
        (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) := by
  have h := polarIso_covariance_of_isInjective hA U K
    (SetLike.coe_mem U) (SetLike.coe_mem K) hCov
  exact calc
    _ = ((U : Matrix (Fin d) (Fin d) ℂ) * Matrix.polarIso (physicalMatrix A)).submatrix
        id (virtualPairEquiv D) :=
      Matrix.submatrix_mul_equiv (U : Matrix (Fin d) (Fin d) ℂ) (Matrix.polarIso (physicalMatrix A))
        id (Equiv.refl (Fin d)) (virtualPairEquiv D)
    _ = (Matrix.polarIso (physicalMatrix A) *
        (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)).submatrix
        id (virtualPairEquiv D) := congrArg (fun M => M.submatrix id (virtualPairEquiv D)) h
    _ = _ := (Matrix.submatrix_mul_equiv (Matrix.polarIso (physicalMatrix A))
      (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
      id (virtualPairEquiv D) (virtualPairEquiv D)).symm

/-- A target frame with the same virtual pair action gives covariance
of the full polar-selected physical embedding. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem polarFrameEmbedding_intertwiner {A : MPSTensor d D}
    (hA : Kraus.IsInjective A) (W : Matrix (Fin m) (Fin (D * D)) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (V : Matrix.unitaryGroup (Fin m) ℂ)
    (K : Matrix.unitaryGroup (Fin D × Fin D) ℂ)
    (hCov : (U : Matrix (Fin d) (Fin d) ℂ) * physicalMatrix A =
      physicalMatrix A * (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ))
    (hW : (V : Matrix (Fin m) (Fin m) ℂ) * W =
      W * Matrix.reindex finProdFinEquiv finProdFinEquiv
        (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)) :
    (Matrix.unitaryDirectSum V U : Matrix (Fin (m + d)) (Fin (m + d)) ℂ) *
        polarFrameEmbedding A W =
      polarFrameEmbedding A W * (U : Matrix (Fin d) (Fin d) ℂ) := by
  let S : Matrix.unitaryGroup (Fin (D * D)) ℂ :=
    ⟨Matrix.reindex finProdFinEquiv finProdFinEquiv K,
      Matrix.reindex_mem_unitaryGroup finProdFinEquiv _ (SetLike.coe_mem K)⟩
  exact Matrix.finIsometricFrameEmbedding_intertwiner (polarIsoMatrix A) W U V S
    (polarIsoMatrix_covariance_of_isInjective hA U K hCov) hW

/-- Replacing the polar frame constructs a symmetric, uniformly gapped
path from the prescribed isometric endpoint to the embedded original parent.
Source context: arXiv:1010.3732, Sections II.C and II.F.2,
equation eq:1d-sym:jointsym. -/
noncomputable def polarFrameGappedInteractionPath
    {G : Type} [Group G] [NeZero D]
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (V : G →* Matrix.unitaryGroup (Fin m) ℂ)
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (W : Matrix (Fin m) (Fin (D * D)) ℂ) (hW : Wᴴ * W = 1)
    (X : G → Matrix.unitaryGroup (Fin D) ℂ)
    (hCov : ∀ g, rotatePhysical (U g) A =
      fun i => (X g : Matrix (Fin D) (Fin D) ℂ) * A i *
        (X g : Matrix (Fin D) (Fin D) ℂ)ᴴ)
    (hInt : ∀ g, (V g : Matrix (Fin m) (Fin m) ℂ) * W =
      W * Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((X g : Matrix (Fin D) (Fin D) ℂ)ᵀ ⊗ₖ
          (X g : Matrix (Fin D) (Fin D) ℂ)ᴴ)) :
    SymmetricGappedInteractionPath (Matrix.unitaryDirectSumHom.comp (V.prod U))
      (LinearMap.toMatrix' (parentInteraction
        (ofPhysicalMatrix ((Matrix.fromRows W 0).submatrix
          finSumFinEquiv.symm finProdFinEquiv)) 2))
      (LinearMap.toMatrix' (parentInteraction (rotatePhysical (polarFrameEmbedding A W) A) 2)) := by
  have hE : ∀ g,
      (Matrix.unitaryDirectSum (V g) (U g) : Matrix (Fin (m + d)) (Fin (m + d)) ℂ) *
          polarFrameEmbedding A W =
        polarFrameEmbedding A W * (U g : Matrix (Fin d) (Fin d) ℂ) := by
    intro g
    let K : Matrix.unitaryGroup (Fin D × Fin D) ℂ :=
      ⟨(X g : Matrix (Fin D) (Fin D) ℂ)ᵀ ⊗ₖ (X g : Matrix (Fin D) (Fin D) ℂ)ᴴ,
        Matrix.kronecker_mem_unitary
          (Matrix.transpose_mem_unitaryGroup_iff.mpr (SetLike.coe_mem (X g)))
          (Unitary.star_mem (SetLike.coe_mem (X g)))⟩
    apply polarFrameEmbedding_intertwiner hA W (U g) (V g) K _ (hInt g)
    rw [← physicalMatrix_rotatePhysical, hCov g, physicalMatrix_mul_left_right]
  simpa only [polarFrameEmbedding_polar_endpoint hA] using
    embeddedPolarGappedInteractionPath U (Matrix.unitaryDirectSumHom.comp (V.prod U))
      (polarFrameEmbedding A W) (polarFrameEmbedding_isometry hA W hW) hE A hA X hCov

end MPSTensor
