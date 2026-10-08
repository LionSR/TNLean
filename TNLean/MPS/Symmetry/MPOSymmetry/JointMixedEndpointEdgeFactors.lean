/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointBoundaryColumns
import TNLean.MPS.Symmetry.MPOSymmetry.JointInsertedBoundary
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Actual joint edge coefficients with the original bulk tensor

Cropping the adjacent bulk site to the shared first-endpoint alphabet
expresses each actual edge map as its joint boundary column matrix times
a one-sided core map. The exterior coordinate is an arbitrary spectator;
the core retains the original endpoint letters. The extraction of the
rectangular virtual boundary is surjective, including for empty labels
and zero-dimensional fibers.

These are identities for the actual inserted coefficient map. No
orthogonality of physical block labels, Hamiltonian identity, or spectral
gap is assumed. Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor.MPOSymmetry

noncomputable section

variable {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- A one-sided first-edge core with arbitrary exterior multiplicities.
The adjacent physical letter is the unchanged first endpoint.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointEndpointFirstEdgeCoreMap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x)) (E : Fin r → ℕ) :
    ((x : Fin r) → Matrix (Fin (D₀ x)) (Fin (E x)) ℂ) →ₗ[ℂ]
      (((x : Fin r) × (Fin (E x) × Fin (D₀ x))) × Fin d₀ → ℂ) where
  toFun Y := fun (p, i) => (A₀ p.1 i * Y p.1) p.2.2 p.2.1
  map_add' Y Z := by ext ⟨⟨x, a, b⟩, i⟩; simp [Matrix.mul_add]
  map_smul' z Y := by ext ⟨⟨x, a, b⟩, i⟩; simp [Matrix.mul_smul]

/-- The reflected one-sided core with arbitrary exterior multiplicities.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointEndpointLastEdgeCoreMap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x)) (E : Fin r → ℕ) :
    ((x : Fin r) → Matrix (Fin (E x)) (Fin (D₀ x)) ℂ) →ₗ[ℂ]
      (Fin d₀ × ((x : Fin r) × (Fin (D₀ x) × Fin (E x))) → ℂ) where
  toFun Y := fun (i, p) => (Y p.1 * A₀ p.1 i) p.2.2 p.2.1
  map_add' Y Z := by ext ⟨i, ⟨x, c, e⟩⟩; simp [Matrix.add_mul]
  map_smul' z Y := by ext ⟨i, ⟨x, c, e⟩⟩; simp [Matrix.smul_mul]

/-- The actual first-edge coefficient map, cropped only at its adjacent
bulk site to the entire shared first alphabet.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedFirstEdgeBoundaryMap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    ((x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) →ₗ[ℂ]
      (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁) × Fin d₀ → ℂ) where
  toFun X := fun (i, j) => blockInsertedGroundSpaceMap (jointMixedEndpointBase A₀ A₁)
    (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2 X
      ![i, jointMixedFirstPhysicalIndex d₁ D₀ D₁ j]
  map_add' X Y := by
    ext ⟨i, j⟩
    exact congrFun (map_add (blockInsertedGroundSpaceMap _ _ 2) X Y) _
  map_smul' z X := by
    ext ⟨i, j⟩
    exact congrFun (map_smul (blockInsertedGroundSpaceMap _ _ 2) z X) _

/-- The actual last-edge coefficient map, with its adjacent bulk site
cropped to the entire shared first alphabet.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedLastEdgeBoundaryMap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    ((x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) →ₗ[ℂ]
      (Fin d₀ × Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁) → ℂ) where
  toFun X := fun (i, j) => blockInsertedGroundSpaceMap (jointMixedEndpointBase A₀ A₁)
    (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2 X
      ![jointMixedFirstPhysicalIndex d₁ D₀ D₁ i, j]
  map_add' X Y := by
    ext ⟨i, j⟩
    exact congrFun (map_add (blockInsertedGroundSpaceMap _ _ 2) X Y) _
  map_smul' z X := by
    ext ⟨i, j⟩
    exact congrFun (map_smul (blockInsertedGroundSpaceMap _ _ 2) z X) _

private theorem firstVirtual_ne_secondVirtual {m n : ℕ} (a : Fin m) (b : Fin n) :
    Fin.castAdd n a ≠ Fin.natAdd m b := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

/-- A shared first-endpoint letter has only its first virtual rows.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem jointMixedEndpointBase_firstPhysical_mul_inclusion
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (x : Fin r) (i : Fin d₀) :
    jointMixedEndpointBase A₀ A₁ x (jointMixedFirstPhysicalIndex d₁ D₀ D₁ i) *
        Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x)) =
      Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x)) * A₀ x i := by
  classical
  rw [Matrix.mul_coordinateInclusion]
  ext a b
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
  cases a <;>
    simp [jointMixedEndpointBase, jointMixedFirstPhysicalIndex,
      jointMixedEndpointLetter, Matrix.reindex_apply, Matrix.coordinateInclusion,
      Matrix.mul_apply, Fin.castAddEmb_apply, eq_comm, firstVirtual_ne_secondVirtual]

/-- The reflected first-sector boundary identity.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem jointMixedEndpointBase_inclusion_adjoint_mul_firstPhysical
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (x : Fin r) (i : Fin d₀) :
    (Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x)))ᴴ *
        jointMixedEndpointBase A₀ A₁ x (jointMixedFirstPhysicalIndex d₁ D₀ D₁ i) =
      A₀ x i * (Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x)))ᴴ := by
  classical
  rw [Matrix.conjTranspose_coordinateInclusion_mul]
  ext a b
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
  cases b <;>
    simp [jointMixedEndpointBase, jointMixedFirstPhysicalIndex,
      jointMixedEndpointLetter, Matrix.reindex_apply, Matrix.coordinateInclusion,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.castAddEmb_apply,
      eq_comm, firstVirtual_ne_secondVirtual]

private theorem firstEdge_trace
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ)
    (i : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) (j : Fin d₀) :
    jointMixedFirstEdgeBoundaryMap A₀ A₁ X (i, j) =
      ∑ x, Matrix.trace ((jointMixedEndpointBase A₀ A₁ x i *
        Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x))) *
          (A₀ x j * ((X x).submatrix (Fin.castAdd (D₁ x)) id))) := by
  change blockInsertedGroundSpaceMap _ _ 2 X _ = _
  simp only [blockInsertedGroundSpaceMap_apply, Finset.sum_apply,
    insertedGroundSpaceMap_apply]
  apply Finset.sum_congr rfl
  intro x _
  have hword : List.ofFn ![i, jointMixedFirstPhysicalIndex d₁ D₀ D₁ j] =
      i :: ([] ++ [jointMixedFirstPhysicalIndex d₁ D₀ D₁ j]) := by simp
  rw [hword, jointMixedEndpoint_insertedEvalWord_boundaryFactors]
  simp only [Kraus.evalWord, Matrix.mul_one]
  rw [jointMixedEndpointBase_inclusion_adjoint_mul_firstPhysical]
  simp only [Matrix.mul_assoc, Matrix.conjTranspose_coordinateInclusion_mul,
    Fin.coe_castAddEmb]

private theorem lastEdge_trace
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ)
    (i : Fin d₀) (j : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) :
    jointMixedLastEdgeBoundaryMap A₀ A₁ X (i, j) =
      ∑ x, Matrix.trace (((Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x)))ᴴ *
          jointMixedEndpointBase A₀ A₁ x j) *
        ((X x).submatrix id (Fin.castAdd (D₁ x)) * A₀ x i)) := by
  change blockInsertedGroundSpaceMap _ _ 2 X _ = _
  simp only [blockInsertedGroundSpaceMap_apply, Finset.sum_apply,
    insertedGroundSpaceMap_apply]
  apply Finset.sum_congr rfl
  intro x _
  have hword : List.ofFn ![jointMixedFirstPhysicalIndex d₁ D₀ D₁ i, j] =
      jointMixedFirstPhysicalIndex d₁ D₀ D₁ i :: ([] ++ [j]) := by simp
  rw [hword, jointMixedEndpoint_insertedEvalWord_boundaryFactors]
  simp only [Kraus.evalWord, Matrix.mul_one,
    jointMixedEndpointBase_firstPhysical_mul_inclusion]
  rw [Matrix.trace_mul_comm _ (X x)]
  rw [Matrix.trace_mul_comm ((Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x)))ᴴ *
    jointMixedEndpointBase A₀ A₁ x j)]
  simp only [← Matrix.mul_assoc, Matrix.mul_coordinateInclusion, Fin.coe_castAddEmb]

/-- The actual first-edge coefficients are the joint first column matrix
applied to the original one-sided core, with identity on the adjacent
physical site. The virtual boundary is cropped only in its first rows.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstEdgeBoundaryMap_eq_columns_core
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    jointMixedFirstEdgeBoundaryMap A₀ A₁ X =
      (jointMixedFirstBoundaryColumns A₀ A₁ ⊗ₖ (1 : Matrix (Fin d₀) (Fin d₀) ℂ)) *ᵥ
        jointEndpointFirstEdgeCoreMap A₀ (fun x => D₀ x + D₁ x)
          (fun x => (X x).submatrix (Fin.castAdd (D₁ x)) id) := by
  classical
  ext ⟨i, j⟩
  rw [firstEdge_trace]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_sigma, Matrix.one_apply, jointEndpointFirstEdgeCoreMap,
    Matrix.trace, Matrix.mul_apply, jointMixedFirstBoundaryColumns,
    Matrix.mul_coordinateInclusion]

/-- The reflected coefficient factorization; again the adjacent physical
site retains its entire original alphabet and identity change.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastEdgeBoundaryMap_eq_columns_core
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    jointMixedLastEdgeBoundaryMap A₀ A₁ X =
      ((1 : Matrix (Fin d₀) (Fin d₀) ℂ) ⊗ₖ jointMixedLastBoundaryColumns A₀ A₁) *ᵥ
        jointEndpointLastEdgeCoreMap A₀ (fun x => D₀ x + D₁ x)
          (fun x => (X x).submatrix id (Fin.castAdd (D₁ x))) := by
  classical
  ext ⟨i, j⟩
  rw [lastEdge_trace]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_sigma, Matrix.one_apply, jointEndpointLastEdgeCoreMap,
    Matrix.trace, Matrix.mul_apply, jointMixedLastBoundaryColumns,
    Matrix.conjTranspose_coordinateInclusion_mul]

/-- Cropping the first virtual rows is onto all rectangular joint
boundaries, even when labels or fibers are empty.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstBoundaryExtraction_surjective :
    Function.Surjective (fun X : (x : Fin r) →
      Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ =>
        fun x => (X x).submatrix (Fin.castAdd (D₁ x)) id) := by
  intro Y
  refine ⟨fun x => Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x)) * Y x, ?_⟩
  funext x
  change (Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x)) * Y x).submatrix
    (Fin.castAddEmb (D₁ x)) id = Y x
  rw [← Matrix.conjTranspose_coordinateInclusion_mul, ← Matrix.mul_assoc,
    Matrix.coordinateInclusion_isometry, Matrix.one_mul]

/-- Cropping the first virtual columns is likewise surjective.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastBoundaryExtraction_surjective :
    Function.Surjective (fun X : (x : Fin r) →
      Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ =>
        fun x => (X x).submatrix id (Fin.castAdd (D₁ x))) := by
  intro Y
  refine ⟨fun x => Y x * (Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x)))ᴴ, ?_⟩
  funext x
  change (Y x * (Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x)))ᴴ).submatrix
    id (Fin.castAddEmb (D₁ x)) = Y x
  rw [← Matrix.mul_coordinateInclusion, Matrix.mul_assoc,
    Matrix.coordinateInclusion_isometry, Matrix.mul_one]

end

end MPSTensor.MPOSymmetry
