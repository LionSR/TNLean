/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.PhysicalIndexMixing
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.ParentHamiltonian.PhysicalDeformation

/-!
# Rectangular physical embeddings of MPS ground spaces

A one-site isometry from a smaller physical space into a larger one acts on
every site of a chain. The finite-window MPS ground space of the embedded
tensor is exactly the isometric image of the original ground space. This is
the local geometric step in placing isometric MPS representatives in the
common physical space of Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Sections II.B.2 and II.D.2.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- The rectangular tensor power of a one-site physical-coordinate map.
Source context: arXiv:1010.3732, Sections II.B.2 and II.D.2. -/
noncomputable def physicalEmbeddingTensorPow {d e : ℕ} (L : ℕ)
    (V : Matrix (Fin e) (Fin d) ℂ) :
    Matrix (Cfg e L) (Cfg d L) ℂ :=
  Matrix.of fun τ σ ↦ ∏ k : Fin L, V (τ k) (σ k)

@[simp] theorem physicalEmbeddingTensorPow_apply {d e : ℕ} (L : ℕ)
    (V : Matrix (Fin e) (Fin d) ℂ) (τ : Cfg e L) (σ : Cfg d L) :
    physicalEmbeddingTensorPow L V τ σ =
      ∏ k : Fin L, V (τ k) (σ k) := rfl

/-- An isometry on the one-site physical space remains an isometry on every
finite tensor power. Source context: arXiv:1010.3732, Section II.B.2. -/
theorem physicalEmbeddingTensorPow_conjTranspose_mul_self
    {d e : ℕ} (L : ℕ) (V : Matrix (Fin e) (Fin d) ℂ)
    (hV : Vᴴ * V = 1) :
    (physicalEmbeddingTensorPow L V)ᴴ * physicalEmbeddingTensorPow L V = 1 := by
  classical
  ext σ σ'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    physicalEmbeddingTensorPow_apply, star_prod]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum
    (fun k : Fin L => fun j : Fin e => star (V j (σ k)) * V j (σ' k))]
  simp_rw [← Matrix.conjTranspose_apply, ← Matrix.mul_apply]
  rw [hV]
  simp only [Matrix.one_apply]
  by_cases h : σ = σ'
  · subst σ'
    simp
  · have ⟨k, hk⟩ := Function.ne_iff.mp h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)

private theorem evalWord_physicalEmbedding {d e D : ℕ}
    (A : MPSTensor d D) (V : Matrix (Fin e) (Fin d) ℂ)
    (L : ℕ) (τ : Cfg e L) :
    Kraus.evalWord (fun τ' : Fin e ↦ ∑ σ' : Fin d, V τ' σ' • A σ')
        (List.ofFn τ) =
      ∑ σ : Cfg d L,
        (∏ k : Fin L, V (τ k) (σ k)) • Kraus.evalWord A (List.ofFn σ) := by
  classical
  rw [evalWord_ofFn_eq_prod, List.prod_ofFn_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [List.prod_ofFn_smul, evalWord_ofFn_eq_prod]

/-- The boundary map of a physically mixed tensor is the tensor power of
the physical map applied to the original boundary map. Source context:
arXiv:1010.3732, Section II.D.2. -/
theorem groundSpaceMap_physicalEmbedding {d e D : ℕ}
    (A : MPSTensor d D) (V : Matrix (Fin e) (Fin d) ℂ)
    (L : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    groundSpaceMap (fun τ : Fin e ↦ ∑ σ : Fin d, V τ σ • A σ) L X =
      Matrix.toLin' (physicalEmbeddingTensorPow L V) (groundSpaceMap A L X) := by
  classical
  ext τ
  simp only [groundSpaceMap_apply, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, physicalEmbeddingTensorPow_apply]
  rw [evalWord_physicalEmbedding]
  simp only [Finset.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp [smul_eq_mul]

/-- The finite-window MPS ground space of an embedded tensor is precisely
the image of the original ground space under the physical tensor power.
No isometry hypothesis is needed for this equality of images.
Source context: arXiv:1010.3732, Section II.D.2. -/
theorem groundSpace_physicalEmbedding {d e D : ℕ}
    (A : MPSTensor d D) (V : Matrix (Fin e) (Fin d) ℂ) (L : ℕ) :
    groundSpace (fun τ : Fin e ↦ ∑ σ : Fin d, V τ σ • A σ) L =
      (groundSpace A L).map (Matrix.toLin' (physicalEmbeddingTensorPow L V)) := by
  have h : groundSpaceMap (fun τ : Fin e ↦ ∑ σ : Fin d, V τ σ • A σ) L =
      (Matrix.toLin' (physicalEmbeddingTensorPow L V)).comp (groundSpaceMap A L) :=
    LinearMap.ext (groundSpaceMap_physicalEmbedding A V L)
  rw [groundSpace, groundSpace, h, LinearMap.range_comp]

/-- The Euclidean realization of the embedded ground space is the image
under the rectangular physical tensor power. Source: arXiv:1010.3732,
Section II.D.2. -/
theorem groundSpaceES_physicalEmbedding {d e D : ℕ}
    (A : MPSTensor d D) (V : Matrix (Fin e) (Fin d) ℂ) (L : ℕ) :
    groundSpaceES (fun τ : Fin e ↦ ∑ σ : Fin d, V τ σ • A σ) L =
      (groundSpaceES A L).map (Matrix.toEuclideanLin (physicalEmbeddingTensorPow L V)) := by
  rw [groundSpaceES, groundSpaceES, groundSpace_physicalEmbedding,
    ← Submodule.map_comp, ← Submodule.map_comp]
  rfl

/-- The canonical parent interaction of an isometrically embedded tensor
acts on the embedded physical subspace as the original parent interaction.
Source: arXiv:1010.3732, Sections II.B.2 and II.D.2. -/
theorem parentInteractionES_physicalEmbedding_apply {d e D : ℕ}
    (A : MPSTensor d D) (V : Matrix (Fin e) (Fin d) ℂ)
    (hV : Vᴴ * V = 1) (L : ℕ) (v : EuclideanSpace ℂ (Cfg d L)) :
    parentInteractionES (fun τ : Fin e ↦ ∑ σ : Fin d, V τ σ • A σ) L
        (Matrix.toEuclideanLin (physicalEmbeddingTensorPow L V) v) =
      Matrix.toEuclideanLin (physicalEmbeddingTensorPow L V)
        (parentInteractionES A L v) := by
  let T := Matrix.toEuclideanLin (physicalEmbeddingTensorPow L V)
  have hadj : T.adjoint.comp T = 1 := by
    dsimp only [T]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [← Matrix.toLpLin_mul]
    rw [physicalEmbeddingTensorPow_conjTranspose_mul_self L V hV]
    exact Matrix.toLpLin_one 2
  have hinner (x y : EuclideanSpace ℂ (Cfg d L)) :
      inner ℂ (T x) (T y) = inner ℂ x y := by
    have hy : T.adjoint (T y) = y := LinearMap.congr_fun hadj y
    rw [← LinearMap.adjoint_inner_right, hy]
  let I := T.isometryOfInner hinner
  let K := groundSpaceES A L
  have hproj := I.map_starProjection K v
  change T (K.starProjection v) =
    (K.map T).starProjection (T v) at hproj
  change (groundSpaceES (fun τ : Fin e ↦ ∑ σ : Fin d, V τ σ • A σ) L)ᗮ.starProjection
      (T v) = T (Kᗮ.starProjection v)
  rw [groundSpaceES_physicalEmbedding]
  rw [Submodule.starProjection_orthogonal, Submodule.starProjection_orthogonal]
  simp only [sub_apply, ContinuousLinearMap.id_apply, map_sub]
  rw [hproj]

/-- Vectors orthogonal to the embedded physical space have unit energy
under the canonical parent interaction. Source: arXiv:1010.3732,
Section II.B.2, embedding the local support in a larger physical space. -/
theorem parentInteractionES_physicalEmbedding_of_orthogonal_range {d e D : ℕ}
    (A : MPSTensor d D) (V : Matrix (Fin e) (Fin d) ℂ)
    (L : ℕ) (v : EuclideanSpace ℂ (Cfg e L))
    (hv : v ∈ (LinearMap.range
      (Matrix.toEuclideanLin (physicalEmbeddingTensorPow L V)))ᗮ) :
    parentInteractionES (fun τ : Fin e ↦ ∑ σ : Fin d, V τ σ • A σ) L v = v := by
  apply Submodule.starProjection_eq_self_iff.mpr
  have hle : groundSpaceES (fun τ : Fin e ↦ ∑ σ : Fin d, V τ σ • A σ) L ≤
      LinearMap.range (Matrix.toEuclideanLin (physicalEmbeddingTensorPow L V)) := by
    rw [groundSpaceES_physicalEmbedding]
    rintro _ ⟨w, _, rfl⟩
    exact ⟨w, rfl⟩
  exact Submodule.orthogonal_le hle hv

/-- An intertwining physical embedding preserves exact virtual covariance.
Source: arXiv:1010.3732, Section II.C.2, the common physical symmetry space. -/
theorem gaugeEquiv_physicalEmbedding_of_intertwining {d e D : ℕ}
    (A : MPSTensor d D) (V : Matrix (Fin e) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (W : Matrix (Fin e) (Fin e) ℂ)
    (hInter : W * V = V * U) (hCov : GaugeEquiv A (rotatePhysical U A)) :
    GaugeEquiv (fun τ : Fin e ↦ ∑ σ : Fin d, V τ σ • A σ)
      (rotatePhysical W (fun τ : Fin e ↦ ∑ σ : Fin d, V τ σ • A σ)) := by
  have hmix : rotatePhysical W (fun τ : Fin e ↦ ∑ σ : Fin d, V τ σ • A σ) =
      fun τ : Fin e ↦ ∑ σ : Fin d, V τ σ • rotatePhysical U A σ := by
    have hcomp {a b c : ℕ} (X : Matrix (Fin a) (Fin b) ℂ)
        (Y : Matrix (Fin b) (Fin c) ℂ) (B : MPSTensor c D) :
        (fun i ↦ ∑ j, X i j • ∑ k, Y j k • B k) =
          fun i ↦ ∑ k, (X * Y) i k • B k := by
      funext i
      simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      exact Finset.sum_comm
    change (fun i ↦ ∑ j, W i j • ∑ k, V j k • A k) =
      fun i ↦ ∑ j, V i j • ∑ k, U j k • A k
    rw [hcomp, hcomp, hInter]
  rw [hmix]
  exact hCov.sum_smul V

end MPSTensor
