/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointSectors
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointEmbedding

/-!
# The joint canonical endpoint as the all-zero phase corner

Compressing every enlarged virtual boundary to its first corner recovers
the full joint canonical support. The physical endpoint alphabet remains
shared by all blocks, so the resulting support is their linear sum with
all overlaps retained.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

variable {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- The actual extended interaction is the complementary projection of the
joint two-site support. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
noncomputable def jointMixedEndpointParentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (γ : ℝ) :
    EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) →L[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :=
  1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
    (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) 2).range.starProjection

/-- Padding every original boundary into the first virtual corner gives
exactly its joint canonical two-site vector.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem blockInsertedBoundaryMap_jointMixed_first_boundary
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (X : (x : Fin r) → Matrix (Fin (D₀ x)) (Fin (D₀ x)) ℂ) :
    let V := fun x => Matrix.coordinateInclusion
      (Fin.castAddEmb (D₁ x) : Fin (D₀ x) ↪ Fin (D₀ x + D₁ x))
    blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2
      (blockBoundaryEquiv.symm fun x => V x * X x * (V x)ᴴ) =
        blockGroundSpaceMapES (jointMixedEndpointLeftTensor A₀ d₁ D₁) 2
          (blockBoundaryEquiv.symm X) := by
  dsimp only
  let V := fun x => Matrix.coordinateInclusion
    (Fin.castAddEmb (D₁ x) : Fin (D₀ x) ↪ Fin (D₀ x + D₁ x))
  ext σ
  rw [blockInsertedBoundaryMap_two_apply, blockGroundSpaceMapES_apply]
  apply Finset.sum_congr rfl
  intro x _
  change Matrix.trace (jointMixedEndpointBase A₀ A₁ x (σ 0) *
    bondInterpolationMatrix (D₀ x) (D₁ x) 0 * jointMixedEndpointBase A₀ A₁ x (σ 1) *
      (V x * X x * (V x)ᴴ)) = groundSpaceMap
        (jointMixedEndpointLeftTensor A₀ d₁ D₁ x) 2 (X x) σ
  rw [← coordinateInclusion_first_projection_eq_bondWeight]
  change Matrix.trace (jointMixedEndpointBase A₀ A₁ x (σ 0) * (V x * (V x)ᴴ) *
    jointMixedEndpointBase A₀ A₁ x (σ 1) * (V x * X x * (V x)ᴴ)) = _
  rw [show jointMixedEndpointBase A₀ A₁ x (σ 0) * (V x * (V x)ᴴ) *
      jointMixedEndpointBase A₀ A₁ x (σ 1) * (V x * X x * (V x)ᴴ) =
      (jointMixedEndpointBase A₀ A₁ x (σ 0) * V x * (V x)ᴴ *
        jointMixedEndpointBase A₀ A₁ x (σ 1) * V x * X x) * (V x)ᴴ by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  rw [show (V x)ᴴ * (jointMixedEndpointBase A₀ A₁ x (σ 0) * V x * (V x)ᴴ *
      jointMixedEndpointBase A₀ A₁ x (σ 1) * V x * X x) =
      ((V x)ᴴ * jointMixedEndpointBase A₀ A₁ x (σ 0) * V x) *
        ((V x)ᴴ * jointMixedEndpointBase A₀ A₁ x (σ 1) * V x) * X x by
    simp only [Matrix.mul_assoc]]
  rw [jointMixedEndpointBase_first_compression, jointMixedEndpointBase_first_compression]
  simp [groundSpaceMap_apply, List.ofFn_succ, Kraus.evalWord, Matrix.mul_assoc]

/-- The outer zero-phase compression of the actual joint extended support
is the full canonical support of the embedded first family. No physical
orthogonality of block labels is assumed.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_extendedSupport_outerCorner_eq_groundSpaceES
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.map
        ((jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2)).comp
          (jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2))) =
      groundSpaceES (toTensorFromBlocks (μ := fun _ => 1)
        (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2 := by
  let V := fun x => Matrix.coordinateInclusion
    (Fin.castAddEmb (D₁ x) : Fin (D₀ x) ↪ Fin (D₀ x + D₁ x))
  let P := fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0
  have hP (x) : P x = V x * (V x)ᴴ :=
    coordinateInclusion_first_projection_eq_bondWeight.symm
  have hV (x) : (V x)ᴴ * V x = 1 := Matrix.coordinateInclusion_isometry _
  rw [groundSpaceES_toTensorFromBlocks_eq_iSup _ _ (fun _ => one_ne_zero),
    ← range_blockGroundSpaceMapES]
  apply le_antisymm
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    obtain ⟨X, rfl⟩ := blockBoundaryEquiv.symm.surjective v
    change jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2)
      (jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2)
        (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) P 2
          (blockBoundaryEquiv.symm X))) ∈ _
    rw [jointMixedColumnSector_blockInsertedBoundaryMap,
      jointMixedRowSector_blockInsertedBoundaryMap]
    have hcorner : (fun x => P x * X x * P x) =
        (fun x => V x * ((V x)ᴴ * X x * V x) * (V x)ᴴ) := by
      funext x
      rw [hP]
      simp only [Matrix.mul_assoc]
    change blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) P 2
      (blockBoundaryEquiv.symm fun x => P x * X x * P x) ∈ _
    rw [hcorner, blockInsertedBoundaryMap_jointMixed_first_boundary]
    exact ⟨_, rfl⟩
  · rintro _ ⟨v, rfl⟩
    obtain ⟨X, rfl⟩ := blockBoundaryEquiv.symm.surjective v
    refine ⟨blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) P 2
      (blockBoundaryEquiv.symm fun x => V x * X x * (V x)ᴴ), ⟨_, rfl⟩, ?_⟩
    change jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2)
      (jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2)
        (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) P 2
          (blockBoundaryEquiv.symm fun x => V x * X x * (V x)ᴴ))) = _
    rw [jointMixedColumnSector_blockInsertedBoundaryMap,
      jointMixedRowSector_blockInsertedBoundaryMap]
    have hcorner : (fun x => P x * (V x * X x * (V x)ᴴ) * P x) =
        (fun x => V x * X x * (V x)ᴴ) := by
      funext x
      have hPV : P x * V x = V x := by rw [hP, Matrix.mul_assoc, hV, Matrix.mul_one]
      have hVP : (V x)ᴴ * P x = (V x)ᴴ := by rw [hP, ← Matrix.mul_assoc, hV, Matrix.one_mul]
      calc
        P x * (V x * X x * (V x)ᴴ) * P x =
            (P x * V x) * X x * ((V x)ᴴ * P x) := by simp only [Matrix.mul_assoc]
        _ = V x * X x * (V x)ᴴ := by rw [hPV, hVP]
    change blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁) P 2
      (blockBoundaryEquiv.symm fun x => P x * (V x * X x * (V x)ᴴ) * P x) = _
    rw [hcorner]
    exact blockInsertedBoundaryMap_jointMixed_first_boundary A₀ A₁ X

end MPSTensor.MPOSymmetry
