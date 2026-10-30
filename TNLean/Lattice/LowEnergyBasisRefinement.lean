/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisSimpleSpectrum
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Combining bases after a spectral split

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708, successively
diagonalizes compressions on unresolved subspaces. Bases chosen on complementary
orthogonal subspaces combine into a basis of the original space. The identities below
retain the chosen basis vectors exactly, as needed for recursive matrix-element bounds.
-/

open scoped InnerProductSpace

namespace TNLean.Lattice

variable {𝕜 E α β : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [Fintype α] [Fintype β]

noncomputable local instance (K : Submodule 𝕜 E) : InnerProductSpace 𝕜 K := K.innerProductSpace

/-- Compression to a subspace, acting on that subspace itself. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
noncomputable def subspaceCompression (K : Submodule 𝕜 E) (A : E →L[𝕜] E) : K →L[𝕜] K :=
  K.orthogonalProjectionOnto.comp (A.comp K.subtypeL)

/-- Extension by zero from a subspace to the ambient space. This identifies the compressed
operators occurring in Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
noncomputable def subspaceExtension (K : Submodule 𝕜 E) (A : K →L[𝕜] K) : E →L[𝕜] E :=
  K.subtypeL.comp (A.comp K.orthogonalProjectionOnto)

@[simp]
theorem coe_subspaceCompression_apply (K : Submodule 𝕜 E) (A : E →L[𝕜] E) (x : K) :
    (subspaceCompression K A x : E) = K.starProjection (A x) := rfl

@[simp]
theorem subspaceExtension_coe_apply (K : Submodule 𝕜 E) (A : K →L[𝕜] K) (x : K) :
    subspaceExtension K A x = (A x : E) := by
  simp [subspaceExtension]

@[simp]
theorem inner_subspaceCompression_right (K : Submodule 𝕜 E) (A : E →L[𝕜] E) (x y : K) :
    ⟪x, subspaceCompression K A y⟫_𝕜 = ⟪(x : E), A y⟫_𝕜 :=
  K.inner_orthogonalProjectionOnto_eq_of_mem_left x (A y)

@[simp]
theorem inner_subspaceCompression_left (K : Submodule 𝕜 E) (A : E →L[𝕜] E) (x y : K) :
    ⟪subspaceCompression K A x, y⟫_𝕜 = ⟪A x, (y : E)⟫_𝕜 :=
  K.inner_orthogonalProjectionOnto_eq_of_mem_right y (A x)

/-- Compression does not increase the operator norm. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem norm_subspaceCompression_le (K : Submodule 𝕜 E) (A : E →L[𝕜] E) :
    ‖subspaceCompression K A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  exact (K.norm_orthogonalProjectionOnto_apply_le (A x)).trans (A.le_opNorm x.val)

/-- Extending by zero preserves the operator norm. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem norm_subspaceExtension (K : Submodule 𝕜 E) (A : K →L[𝕜] K) :
    ‖subspaceExtension K A‖ = ‖A‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    calc ‖subspaceExtension K A x‖ ≤ ‖A‖ * ‖K.orthogonalProjectionOnto x‖ := A.le_opNorm _
      _ ≤ ‖A‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left (K.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg _)
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have h := (subspaceExtension K A).le_opNorm x.val
    simpa only [subspaceExtension_coe_apply, Submodule.norm_coe] using h

@[simp]
theorem subspaceExtension_compression (K : Submodule 𝕜 E) (A : E →L[𝕜] E) :
    subspaceExtension K (subspaceCompression K A) = K.starProjection * A * K.starProjection := rfl

@[simp]
theorem subspaceExtension_mul (K : Submodule 𝕜 E) (A B : K →L[𝕜] K) :
    subspaceExtension K (A * B) = subspaceExtension K A * subspaceExtension K B := by
  ext x
  simp [subspaceExtension]

@[simp]
theorem subspaceExtension_sub (K : Submodule 𝕜 E) (A B : K →L[𝕜] K) :
    subspaceExtension K (A - B) = subspaceExtension K A - subspaceExtension K B := by
  ext x
  rfl

/-- Compression preserves symmetry of the inner-product pairing. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem isSymmetric_subspaceCompression (K : Submodule 𝕜 E) (A : E →L[𝕜] E)
    (hA : A.toLinearMap.IsSymmetric) : (subspaceCompression K A).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪subspaceCompression K A x, y⟫_𝕜 = ⟪x, subspaceCompression K A y⟫_𝕜
  rw [inner_subspaceCompression_left, inner_subspaceCompression_right]
  exact hA x.val y.val

/-- A compressed self-adjoint operator is self-adjoint on the subspace. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem isSelfAdjoint_subspaceCompression (K : Submodule 𝕜 E)
    [CompleteSpace E] [CompleteSpace K] (A : E →L[𝕜] E)
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (subspaceCompression K A) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (isSymmetric_subspaceCompression K A hA.isSymmetric)

/-- Norm equality identifying a commutator on a subspace with its extension to the
ambient space. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem norm_subspaceCompression_commutator (K : Submodule 𝕜 E) (A B : E →L[𝕜] E) :
    ‖subspaceCompression K A * subspaceCompression K B -
        subspaceCompression K B * subspaceCompression K A‖ =
      ‖(K.starProjection * A * K.starProjection) * (K.starProjection * B * K.starProjection) -
        (K.starProjection * B * K.starProjection) * (K.starProjection * A * K.starProjection)‖ := by
  rw [← norm_subspaceExtension K (subspaceCompression K A * subspaceCompression K B -
    subspaceCompression K B * subspaceCompression K A)]
  rw [subspaceExtension_sub, subspaceExtension_mul, subspaceExtension_mul,
    subspaceExtension_compression, subspaceExtension_compression]

/-- Orthonormal bases on a subspace and its orthogonal complement combine without changing
their vectors. This is the basis refinement step of Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem exists_orthonormalBasis_orthogonal_sum (K : Submodule 𝕜 E)
    (u : OrthonormalBasis α 𝕜 K) (v : OrthonormalBasis β 𝕜 Kᗮ) :
    ∃ b : OrthonormalBasis (α ⊕ β) 𝕜 E,
      (∀ a, b (Sum.inl a) = (u a : E)) ∧ (∀ c, b (Sum.inr c) = (v c : E)) := by
  classical
  let e := K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal
  let b := (u.toBasis.prod v.toBasis).map e
  have hl (a : α) : b (Sum.inl a) = (u a : E) := by
    simp [b, e, Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
  have hr (c : β) : b (Sum.inr c) = (v c : E) := by
    simp [b, e, Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
  have horth : Orthonormal 𝕜 b := by
    rw [orthonormal_iff_ite]
    intro a c
    rcases a with a | a <;> rcases c with c | c
    · simpa only [hl, Sum.inl.injEq, Submodule.coe_inner] using
        (orthonormal_iff_ite.mp u.orthonormal a c)
    · simp only [hl, hr, Sum.inl_ne_inr, ↓reduceIte]
      exact (K.mem_orthogonal _).mp (v c).property _ (u a).property
    · simp only [hl, hr, Sum.inr_ne_inl, ↓reduceIte]
      exact (K.mem_orthogonal' _).mp (v a).property _ (u c).property
    · simpa only [hr, Sum.inr.injEq, Submodule.coe_inner] using
        (orthonormal_iff_ite.mp v.orthonormal a c)
  refine ⟨b.toOrthonormalBasis horth, ?_, ?_⟩
  · simpa only [Module.Basis.coe_toOrthonormalBasis] using hl
  · simpa only [Module.Basis.coe_toOrthonormalBasis] using hr

/-- The same combined basis with finite-dimensional indices. The displayed equivalence
identifies each basis vector with its original vector on one of the two summands.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem exists_orthonormalBasis_orthogonal_sum_fin (K : Submodule 𝕜 E)
    (u : OrthonormalBasis α 𝕜 K) (v : OrthonormalBasis β 𝕜 Kᗮ) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
      (e : Fin (Module.finrank 𝕜 E) ≃ α ⊕ β),
      ∀ a, b a = Sum.elim (fun c => (u c : E)) (fun c => (v c : E)) (e a) := by
  classical
  obtain ⟨b, hl, hr⟩ := exists_orthonormalBasis_orthogonal_sum K u v
  let e : α ⊕ β ≃ Fin (Module.finrank 𝕜 E) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b.toBasis).symm
  refine ⟨b.reindex e, e.symm, fun a => ?_⟩
  rw [OrthonormalBasis.reindex_apply]
  cases h : e.symm a with
  | inl c => exact hl c
  | inr c => exact hr c

/-- A matrix element between complementary orthogonal subspaces is bounded by the norm
of the corresponding cross compression. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1695–1708. -/
theorem norm_inner_subspace_cross_le (K : Submodule 𝕜 E) (A : E →L[𝕜] E)
    (x : K) (y : Kᗮ) :
    ‖⟪(x : E), A y⟫_𝕜‖ ≤ ‖K.starProjection * A * Kᗮ.starProjection‖ * ‖x‖ * ‖y‖ := by
  have heq : ⟪(x : E), (K.starProjection * A * Kᗮ.starProjection) y⟫_𝕜 =
      ⟪(x : E), A y⟫_𝕜 := by
    change ⟪(x : E), K.starProjection (A (Kᗮ.starProjection y))⟫_𝕜 = _
    rw [Kᗮ.starProjection_mem_subspace_eq_self y, ← K.inner_starProjection_left_eq_right,
      K.starProjection_mem_subspace_eq_self x]
  rw [← heq]
  calc _ ≤ ‖x‖ * ‖(K.starProjection * A * Kᗮ.starProjection) y‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖K.starProjection * A * Kᗮ.starProjection‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left
        ((K.starProjection * A * Kᗮ.starProjection).le_opNorm y.val) (norm_nonneg _)
    _ = _ := by ring

/-- Matrix-element bounds on the two subspaces and their cross compression combine in
the orthonormal basis formed from the two chosen bases. This retains all three errors in
the recursion of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem norm_inner_le_of_orthogonal_sum (K : Submodule 𝕜 E)
    (u : OrthonormalBasis α 𝕜 K) (v : OrthonormalBasis β 𝕜 Kᗮ)
    (b : OrthonormalBasis (α ⊕ β) 𝕜 E)
    (hl : ∀ a, b (Sum.inl a) = (u a : E)) (hr : ∀ c, b (Sum.inr c) = (v c : E))
    (A : E →L[𝕜] E) (hA : A.toLinearMap.IsSymmetric) {L R X : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hX : 0 ≤ X)
    (hu : ∀ a c, a ≠ c → ‖⟪u a, subspaceCompression K A (u c)⟫_𝕜‖ ≤ L)
    (hv : ∀ a c, a ≠ c → ‖⟪v a, subspaceCompression Kᗮ A (v c)⟫_𝕜‖ ≤ R)
    (hcross : ‖K.starProjection * A * Kᗮ.starProjection‖ ≤ X)
    {a c : α ⊕ β} (hac : a ≠ c) : ‖⟪b a, A (b c)⟫_𝕜‖ ≤ L + R + X := by
  rcases a with a | a <;> rcases c with c | c
  · rw [hl, hl]
    have h := hu a c (fun h => hac (congrArg Sum.inl h))
    rw [inner_subspaceCompression_right] at h
    linarith
  · rw [hl, hr]
    have h := norm_inner_subspace_cross_le K A (u a) (v c)
    simp only [u.orthonormal.1 a, v.orthonormal.1 c, mul_one] at h
    linarith
  · rw [hr, hl, norm_inner_symm]
    have heq : ⟪A (u c), (v a : E)⟫_𝕜 = ⟪(u c : E), A (v a)⟫_𝕜 := hA (u c).val (v a).val
    rw [heq]
    have h := norm_inner_subspace_cross_le K A (u c) (v a)
    simp only [u.orthonormal.1 c, v.orthonormal.1 a, mul_one] at h
    linarith
  · rw [hr, hr]
    have h := hv a c (fun h => hac (congrArg Sum.inr h))
    rw [inner_subspaceCompression_right] at h
    linarith

end TNLean.Lattice
