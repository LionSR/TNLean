/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointCornerSupport
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointSwap
import QICLean.Algebra.TraceReindex

/-!
# Exchanging the endpoints of the actual joint mixed family

The physical permutation exchanges the shared endpoint alphabets and the
two block-labeled rectangular alphabets. The virtual permutation exchanges
the two bond summands separately in each block. Together they identify the
actual family at parameter \(\gamma\) with the reversed family at
\(1-\gamma\), including its joint two-site support and parent interaction.

The rectangular coordinates keep their order. In particular, this is a
change of the two sector labels, not a transpose of each matrix letter.
No block orthogonality, span, or positive-dimension assumption is needed.
Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix

namespace MPSTensor.MPOSymmetry

variable {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- Exchange both shared physical alphabets and the two rectangular
alphabets, preserving the block label and the order of rectangular indices.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
def jointMixedPhysicalSwap (d₀ d₁ : ℕ) (D₀ D₁ : Fin r → ℕ) :
    JointMixedPhysical d₀ d₁ D₀ D₁ ≃ JointMixedPhysical d₁ d₀ D₁ D₀ where
  toFun
    | .inl i => .inr (.inr (.inr i))
    | .inr (.inl p) => .inr (.inr (.inl p))
    | .inr (.inr (.inl p)) => .inr (.inl p)
    | .inr (.inr (.inr i)) => .inl i
  invFun
    | .inl i => .inr (.inr (.inr i))
    | .inr (.inl p) => .inr (.inr (.inl p))
    | .inr (.inr (.inl p)) => .inr (.inl p)
    | .inr (.inr (.inr i)) => .inl i
  left_inv := by rintro (i | p | p | i) <;> rfl
  right_inv := by rintro (i | p | p | i) <;> rfl

/-- The endpoint exchange in the actual finite physical coordinates.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
noncomputable def jointMixedEndpointPhysicalSwap
    (d₀ d₁ : ℕ) (D₀ D₁ : Fin r → ℕ) :
    Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁) ≃
      Fin (jointMixedPhysicalDim d₁ d₀ D₁ D₀) :=
  (Fintype.equivFin (JointMixedPhysical d₀ d₁ D₀ D₁)).symm.trans
    ((jointMixedPhysicalSwap d₀ d₁ D₀ D₁).trans
      (Fintype.equivFin (JointMixedPhysical d₁ d₀ D₁ D₀)))

/-- The joint mixed letters are preserved by simultaneous physical sector
exchange and virtual summand exchange in each block.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem jointMixedEndpointBase_swap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (x : Fin r) (p : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) :
    jointMixedEndpointBase A₁ A₀ x (jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁ p) =
      Matrix.reindexAlgEquiv ℂ ℂ (mixedEndpointBondSwap (D₀ x) (D₁ x))
        (jointMixedEndpointBase A₀ A₁ x p) := by
  classical
  ext i j
  obtain ⟨i, rfl⟩ := (mixedEndpointBondSwap (D₀ x) (D₁ x)).surjective i
  obtain ⟨j, rfl⟩ := (mixedEndpointBondSwap (D₀ x) (D₁ x)).surjective j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases hp : (Fintype.equivFin (JointMixedPhysical d₀ d₁ D₀ D₁)).symm p with
    a | ⟨y, a, b⟩ | ⟨y, a, b⟩ | a
  · cases i <;> cases j <;>
      simp [jointMixedEndpointBase, jointMixedEndpointLetter, jointMixedEndpointPhysicalSwap,
        jointMixedPhysicalSwap, mixedEndpointBondSwap, hp, Matrix.fromBlocks]
  · by_cases h : x = y
    · subst y
      cases i <;> cases j <;>
        simp [jointMixedEndpointBase, jointMixedEndpointLetter, jointMixedEndpointPhysicalSwap,
          jointMixedPhysicalSwap, mixedEndpointBondSwap, hp, Matrix.single_apply]
    · simp [jointMixedEndpointBase, jointMixedEndpointLetter, jointMixedEndpointPhysicalSwap,
        jointMixedPhysicalSwap, mixedEndpointBondSwap, hp, Pi.single_eq_of_ne h]
  · by_cases h : x = y
    · subst y
      cases i <;> cases j <;>
        simp [jointMixedEndpointBase, jointMixedEndpointLetter, jointMixedEndpointPhysicalSwap,
          jointMixedPhysicalSwap, mixedEndpointBondSwap, hp, Matrix.single_apply]
    · simp [jointMixedEndpointBase, jointMixedEndpointLetter, jointMixedEndpointPhysicalSwap,
        jointMixedPhysicalSwap, mixedEndpointBondSwap, hp, Pi.single_eq_of_ne h]
  · cases i <;> cases j <;>
      simp [jointMixedEndpointBase, jointMixedEndpointLetter, jointMixedEndpointPhysicalSwap,
        jointMixedPhysicalSwap, mixedEndpointBondSwap, hp, Matrix.fromBlocks]

/-- Exchanging the virtual summands reflects the interpolation parameter.
This holds for every real parameter, including either endpoint.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem bondInterpolationMatrix_reflect_swap (D₀ D₁ : ℕ) (γ : ℝ) :
    bondInterpolationMatrix D₁ D₀ (1 - γ) =
      Matrix.reindexAlgEquiv ℂ ℂ (mixedEndpointBondSwap D₀ D₁)
        (bondInterpolationMatrix D₀ D₁ γ) := by
  ext i j
  obtain ⟨i, rfl⟩ := (mixedEndpointBondSwap D₀ D₁).surjective i
  obtain ⟨j, rfl⟩ := (mixedEndpointBondSwap D₀ D₁).surjective j
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, bondInterpolationMatrix, Matrix.diagonal_apply,
    Equiv.apply_eq_iff_eq]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [mixedEndpointBondSwap, bondInterpolationWeight]

/-- The actual weighted joint tensors at reflected parameters differ only
by the physical permutation and the blockwise virtual permutation.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
theorem jointMixedEndpointInterpolation_reflect_swap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (γ : ℝ)
    (x : Fin r) (p : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) :
    jointMixedEndpointInterpolation A₁ A₀ (1 - γ) x
        (jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁ p) =
      Matrix.reindexAlgEquiv ℂ ℂ (mixedEndpointBondSwap (D₀ x) (D₁ x))
        (jointMixedEndpointInterpolation A₀ A₁ γ x p) := by
  simp only [jointMixedEndpointInterpolation, jointMixedEndpointBase_swap,
    bondInterpolationMatrix_reflect_swap, map_mul]

/-- The joint two-site boundary map intertwines the reflected family and
the original family. Every virtual boundary is permuted within its block.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem blockInsertedBoundaryMap_jointMixed_reflect_swap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (γ : ℝ)
    (X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    physicalReindexLinearIsometryEquiv (jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁) 2
      (blockInsertedBoundaryMap (jointMixedEndpointBase A₁ A₀)
        (fun x => bondInterpolationMatrix (D₁ x) (D₀ x) (1 - γ)) 2
        (blockBoundaryEquiv.symm fun x =>
          Matrix.reindexAlgEquiv ℂ ℂ (mixedEndpointBondSwap (D₀ x) (D₁ x)) (X x))) =
      blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) 2
        (blockBoundaryEquiv.symm X) := by
  apply PiLp.ext
  intro σ
  simp only [physicalReindexLinearIsometryEquiv_apply_apply,
    blockInsertedBoundaryMap_two_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [jointMixedEndpointBase_swap, jointMixedEndpointBase_swap,
    bondInterpolationMatrix_reflect_swap, ← map_mul, ← map_mul, ← map_mul]
  exact Matrix.trace_reindex (mixedEndpointBondSwap (D₀ x) (D₁ x)) _

/-- The actual joint support at a parameter is the physical isometric
image of the reversed joint support at its reflected parameter.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_extendedSupport_eq_map_reflect_swap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (γ : ℝ) :
    (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) 2).range =
        (blockInsertedBoundaryMap (jointMixedEndpointBase A₁ A₀)
          (fun x => bondInterpolationMatrix (D₁ x) (D₀ x) (1 - γ)) 2).range.map
          (physicalReindexLinearIsometryEquiv
            (jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁) 2).toLinearMap := by
  let Φ (x : Fin r) := Matrix.reindexAlgEquiv ℂ ℂ
    (mixedEndpointBondSwap (D₀ x) (D₁ x))
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    let X := blockBoundaryEquiv v
    refine ⟨blockInsertedBoundaryMap (jointMixedEndpointBase A₁ A₀)
      (fun x => bondInterpolationMatrix (D₁ x) (D₀ x) (1 - γ)) 2
      (blockBoundaryEquiv.symm fun x => Φ x (X x)), ⟨_, rfl⟩, ?_⟩
    simpa only [X, Φ, LinearEquiv.symm_apply_apply] using
      blockInsertedBoundaryMap_jointMixed_reflect_swap A₀ A₁ γ X
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    let Y := blockBoundaryEquiv v
    refine ⟨blockBoundaryEquiv.symm (fun x => (Φ x).symm (Y x)), ?_⟩
    have h := blockInsertedBoundaryMap_jointMixed_reflect_swap A₀ A₁ γ
      (fun x => (Φ x).symm (Y x))
    simpa only [Φ, AlgEquiv.apply_symm_apply, Y, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv] using h.symm

/-- The actual local parent interactions at reflected parameters are
unitarily conjugate by the physical sector exchange.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpointParentInteraction_eq_conj_reflect_swap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (γ : ℝ) :
    (jointMixedEndpointParentInteraction A₀ A₁ γ).toLinearMap =
      (physicalReindexLinearIsometryEquiv
        (jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁) 2).toLinearEquiv.conj
          (jointMixedEndpointParentInteraction A₁ A₀ (1 - γ)).toLinearMap := by
  let U := physicalReindexLinearIsometryEquiv (jointMixedEndpointPhysicalSwap d₀ d₁ D₀ D₁) 2
  let S := (blockInsertedBoundaryMap (jointMixedEndpointBase A₁ A₀)
    (fun x => bondInterpolationMatrix (D₁ x) (D₀ x) (1 - γ)) 2).range
  have hproj := congrArg
    (fun T : Submodule ℂ (EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)) =>
      T.starProjection)
    (jointMixedEndpoint_extendedSupport_eq_map_reflect_swap A₀ A₁ γ)
  apply LinearMap.ext
  intro v
  have hmap := Submodule.starProjection_map_apply U S v
  change v - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
    (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) 2).range.starProjection v =
      U (U.symm v - S.starProjection (U.symm v))
  rw [hproj]
  change v - (S.map U.toLinearEquiv.toLinearMap).starProjection v =
    U (U.symm v - S.starProjection (U.symm v))
  rw [hmap, map_sub, U.apply_symm_apply]

end MPSTensor.MPOSymmetry
