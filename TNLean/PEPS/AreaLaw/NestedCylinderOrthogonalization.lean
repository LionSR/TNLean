/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Cylinder
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Orthogonalization of nested cylinders

Given nested finite regions and arbitrary inside subspaces, subtracting the
orthogonal projection onto the earlier span produces projected-image subspaces.
The resulting cylinders are pairwise orthogonal, have the same prefix spans,
and have no larger inside dimensions.

Source: the polynomial PEPS approximation manuscript, `03-patches.tex`, lines
563–603 at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

/-!
Source: September 24, 2026, 03-patches.tex.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex
sec:patches, prop:patch, eq:patch-cylinder-projection; independently formalized;
no upstream Lean proof text reused.
Manuscript commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript passage: lines 563–603.

Provenance-ID: orthogonalization8767-tnlean.peps.nestedcylinderearlierinside
Downstream declaration: TNLean.PEPS.nestedCylinderEarlierInside

Provenance-ID: orthogonalization8767-tnlean.peps.nestedcylinderinnovation
Downstream declaration: TNLean.PEPS.nestedCylinderInnovation

Provenance-ID: orthogonalization8767-tnlean.peps.dependentregioncylinder_nestedcylinderearlierinside
Downstream declaration: TNLean.PEPS.dependentRegionCylinder_nestedCylinderEarlierInside

Provenance-ID: orthogonalization8767-tnlean.peps.dependentregioncylinder_nestedcylinderinnovation
Downstream declaration: TNLean.PEPS.dependentRegionCylinder_nestedCylinderInnovation

Provenance-ID: orthogonalization8767-tnlean.peps.finrank_nestedcylinderinnovation_le
Downstream declaration: TNLean.PEPS.finrank_nestedCylinderInnovation_le

Provenance-ID: orthogonalization8767-tnlean.peps.nestedcylinderinnovation_sup
Downstream declaration: TNLean.PEPS.nestedCylinderInnovation_sup

Provenance-ID: orthogonalization8767-tnlean.peps.nestedcylinderinnovation_orthogonalearlier
Downstream declaration: TNLean.PEPS.nestedCylinderInnovation_orthogonalEarlier

Provenance-ID: orthogonalization8767-tnlean.peps.nestedcylinderinnovation_prefix_span
Downstream declaration: TNLean.PEPS.nestedCylinderInnovation_prefix_span

Provenance-ID: orthogonalization8767-tnlean.peps.nestedcylinderinnovation_span
Downstream declaration: TNLean.PEPS.nestedCylinderInnovation_span

Provenance-ID: orthogonalization8767-tnlean.peps.nestedcylinderinnovation_pairwise_orthogonal
Downstream declaration: TNLean.PEPS.nestedCylinderInnovation_pairwise_orthogonal

Provenance-ID: orthogonalization8767-tnlean.peps.nestedcylinderinnovation_projector_sum
Downstream declaration: TNLean.PEPS.nestedCylinderInnovation_projector_sum

Provenance-ID: orthogonalization8767-tnlean.peps.sum_finrank_nestedcylinderinnovation_le
Downstream declaration: TNLean.PEPS.sum_finrank_nestedCylinderInnovation_le

Provenance-ID: orthogonalization8767-tnlean.peps.sum_int_finrank_nestedcylinderinnovation_le
Downstream declaration: TNLean.PEPS.sum_int_finrank_nestedCylinderInnovation_le

Provenance-ID: orthogonalization8767-tnlean.peps.nestedcylinder_projector_supported
Downstream declaration: TNLean.PEPS.nestedCylinder_projector_supported

Provenance-ID: orthogonalization8767-tnlean.peps.nestedcylinderinnovation_eq_bot_of_le
Downstream declaration: TNLean.PEPS.nestedCylinderInnovation_eq_bot_of_le

-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

private theorem sup_map_one_sub_projector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W S : Submodule ℂ (ι → ℂ)) :
    W ⊔ S.map (1 - coordinateRangeProjector W).mulVecLin = W ⊔ S := by
  classical
  have hmem (x : ι → ℂ) : coordinateRangeProjector W *ᵥ x ∈ W := by
    have h : coordinateRangeProjector W *ᵥ x ∈
        (coordinateRangeProjector W).mulVecLin.range := ⟨x, rfl⟩
    rwa [range_coordinateRangeProjector] at h
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rintro x ⟨y, hy, rfl⟩
    change (1 - coordinateRangeProjector W) *ᵥ y ∈ W ⊔ S
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact (W ⊔ S).sub_mem ((show S ≤ W ⊔ S from le_sup_right) hy)
      ((show W ≤ W ⊔ S from le_sup_left) (hmem y))
  · refine sup_le le_sup_left ?_
    intro x hx
    refine Submodule.mem_sup.mpr ⟨coordinateRangeProjector W *ᵥ x, hmem x,
      (1 - coordinateRangeProjector W) *ᵥ x, ⟨x, hx, rfl⟩, ?_⟩
    simp [Matrix.sub_mulVec]

private theorem projector_mul_projected_image_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W S : Submodule ℂ (ι → ℂ)) :
    coordinateRangeProjector W *
      coordinateRangeProjector (S.map (1 - coordinateRangeProjector W).mulVecLin) = 0 := by
  classical
  let T := S.map (1 - coordinateRangeProjector W).mulVecLin
  ext a b
  have hcol : (coordinateRangeProjector T).col b ∈ T := by
    have h : (coordinateRangeProjector T).col b ∈
        (coordinateRangeProjector T).mulVecLin.range :=
      ⟨Pi.single b 1, Matrix.mulVec_single_one _ b⟩
    rwa [range_coordinateRangeProjector] at h
  obtain ⟨y, _, hy⟩ := hcol
  change (coordinateRangeProjector W *ᵥ (coordinateRangeProjector T).col b) a = 0
  rw [← hy]
  change (coordinateRangeProjector W *ᵥ ((1 - coordinateRangeProjector W) *ᵥ y)) a = 0
  rw [Matrix.mulVec_mulVec, (coordinateRangeProjector_isStarProjection W).mul_one_sub_self]
  simp

private theorem coordinate_ortho_of_mul_eq_zero {ι : Type*} [Fintype ι]
    (S T : Submodule ℂ (ι → ℂ))
    (h : coordinateRangeProjector S * coordinateRangeProjector T = 0) :
    (coordinateSubspaceES S).IsOrtho (coordinateSubspaceES T) := by
  classical
  apply Submodule.starProjection_comp_starProjection_eq_zero_iff.mp
  apply ContinuousLinearMap.ext
  intro x
  change (coordinateSubspaceES S).starProjection ((coordinateSubspaceES T).starProjection x) = 0
  have he := congrArg (fun A => Matrix.toEuclideanLin A x) h
  rw [Matrix.toLpLin_mul 2 2 2] at he
  simp only [LinearMap.comp_apply, coordinateRangeProjector,
    LinearEquiv.apply_symm_apply, map_zero, LinearMap.zero_apply] at he
  exact he

private theorem projector_sup_eq_add {ι : Type*} [Fintype ι]
    (S T : Submodule ℂ (ι → ℂ))
    (hST : coordinateRangeProjector S * coordinateRangeProjector T = 0) :
    coordinateRangeProjector (S ⊔ T) = coordinateRangeProjector S + coordinateRangeProjector T := by
  classical
  have hS := coordinateRangeProjector_isStarProjection S
  have hT := coordinateRangeProjector_isStarProjection T
  have hTS : coordinateRangeProjector T * coordinateRangeProjector S = 0 := by
    simpa only [star_mul, hS.isSelfAdjoint.star_eq, hT.isSelfAdjoint.star_eq, star_zero]
      using congrArg star hST
  have hleft : (coordinateRangeProjector S + coordinateRangeProjector T) *
      coordinateRangeProjector S = coordinateRangeProjector S := by
    rw [add_mul, hS.isIdempotentElem.eq, hTS, add_zero]
  have hright : (coordinateRangeProjector S + coordinateRangeProjector T) *
      coordinateRangeProjector T = coordinateRangeProjector T := by
    rw [add_mul, hST, hT.isIdempotentElem.eq, zero_add]
  symm
  apply eq_coordinateRangeProjector_of_range (hS.add hT hST)
  apply le_antisymm
  · simpa only [Matrix.mulVecLin_add, range_coordinateRangeProjector] using
      LinearMap.range_add_le (coordinateRangeProjector S).mulVecLin
        (coordinateRangeProjector T).mulVecLin
  · apply sup_le
    · nth_rw 1 [← range_coordinateRangeProjector S, ← hleft]
      rw [Matrix.mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
    · nth_rw 1 [← range_coordinateRangeProjector T, ← hright]
      rw [Matrix.mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _


private theorem projector_finset_sup {ι κ : Type*} [Fintype κ]
    (S : ι → Submodule ℂ (κ → ℂ))
    (h : Pairwise fun i j => coordinateRangeProjector (S i) * coordinateRangeProjector (S j) = 0)
    (s : Finset ι) :
    coordinateRangeProjector (s.sup S) = ∑ i ∈ s, coordinateRangeProjector (S i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sup_empty, Finset.sum_empty]
    exact (eq_coordinateRangeProjector_of_range (IsStarProjection.zero _) ⊥ (by simp)).symm
  | @insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha, projector_sup_eq_add, ih]
    rw [ih, Finset.mul_sum]
    exact Finset.sum_eq_zero fun i hi => h (ne_of_mem_of_not_mem hi ha).symm

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)] {n : ℕ}

/-- The earlier cylinders expressed inside the current region, using the identity
extensions of their original range projectors. -/
noncomputable def nestedCylinderEarlierInside (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (j : Fin n) : Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ) :=
  ⨆ i : {i : Fin n // i < j},
    (dependentSubregionOperatorLift (R i.1) (R j) (hR i.2.le)
      (coordinateRangeProjector (S i.1))).mulVecLin.range

/-- The projected-image innovation \((I-P_{W_j})S_j\), which need not equal
\(S_j\cap W_j^\perp\). -/
noncomputable def nestedCylinderInnovation (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (j : Fin n) : Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ) :=
  (S j).map (LinearMap.id -
    (coordinateRangeProjector (nestedCylinderEarlierInside R hR S j)).mulVecLin)

/-- The inside earlier subspace has exactly the span of the earlier global cylinders. -/
theorem dependentRegionCylinder_nestedCylinderEarlierInside
    (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (j : Fin n) :
    dependentRegionCylinder (R j) (nestedCylinderEarlierInside R hR S j) =
      ⨆ i : {i : Fin n // i < j}, dependentRegionCylinder (R i.1) (S i.1) := by
  unfold nestedCylinderEarlierInside
  rw [dependentRegionCylinder_iSup]
  simp only [dependentRegionCylinder_subregion]

/-- The global innovation is the projected image of the original cylinder after
removing its orthogonal projection onto the earlier span. -/
theorem dependentRegionCylinder_nestedCylinderInnovation
    (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (j : Fin n) :
    dependentRegionCylinder (R j) (nestedCylinderInnovation R hR S j) =
      (dependentRegionCylinder (R j) (S j)).map
        (LinearMap.id - (coordinateRangeProjector
          (⨆ i : {i : Fin n // i < j}, dependentRegionCylinder (R i.1) (S i.1))).mulVecLin) := by
  classical
  have hm : LinearMap.id -
      (coordinateRangeProjector (nestedCylinderEarlierInside R hR S j)).mulVecLin =
        (1 - coordinateRangeProjector (nestedCylinderEarlierInside R hR S j)).mulVecLin := by
    ext x α
    simp
  rw [nestedCylinderInnovation, hm, dependentRegionCylinder_map, dependentRegionOperatorLift_sub,
    dependentRegionOperatorLift_one (Out := Out),
    ← coordinateRangeProjector_dependentRegionCylinder,
    dependentRegionCylinder_nestedCylinderEarlierInside,
    ← Matrix.toLin'_apply', map_sub, Matrix.toLin'_one]
  rfl

/-- Orthogonalization does not increase the inside dimension. -/
theorem finrank_nestedCylinderInnovation_le (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (j : Fin n) : Module.finrank ℂ (nestedCylinderInnovation R hR S j) ≤
      Module.finrank ℂ (S j) := by
  classical
  exact Submodule.finrank_map_le _ _

/-- Adjoining the projected-image innovation gives exactly the enlarged original span. -/
theorem nestedCylinderInnovation_sup (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (j : Fin n) :
    (⨆ i : {i : Fin n // i < j}, dependentRegionCylinder (R i.1) (S i.1)) ⊔
        dependentRegionCylinder (R j) (nestedCylinderInnovation R hR S j) =
      (⨆ i : {i : Fin n // i < j}, dependentRegionCylinder (R i.1) (S i.1)) ⊔
        dependentRegionCylinder (R j) (S j) := by
  classical
  rw [dependentRegionCylinder_nestedCylinderInnovation]
  simpa only [← Matrix.toLin'_apply', map_sub, Matrix.toLin'_one] using
    sup_map_one_sub_projector
      (⨆ i : {i : Fin n // i < j}, dependentRegionCylinder (R i.1) (S i.1))
      (dependentRegionCylinder (R j) (S j))

private theorem earlier_projector_mul_innovation_eq_zero
    (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (j : Fin n) :
    coordinateRangeProjector
        (⨆ i : {i : Fin n // i < j}, dependentRegionCylinder (R i.1) (S i.1)) *
      coordinateRangeProjector (dependentRegionCylinder (R j) (nestedCylinderInnovation R hR S j)) =
        0 := by
  classical
  rw [dependentRegionCylinder_nestedCylinderInnovation]
  simpa only [← Matrix.toLin'_apply', map_sub, Matrix.toLin'_one] using
    projector_mul_projected_image_eq_zero
      (⨆ i : {i : Fin n // i < j}, dependentRegionCylinder (R i.1) (S i.1))
      (dependentRegionCylinder (R j) (S j))

/-- The new cylinder is orthogonal to the entire earlier span. -/
theorem nestedCylinderInnovation_orthogonalEarlier
    (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (j : Fin n) :
    (coordinateSubspaceES
        (⨆ i : {i : Fin n // i < j}, dependentRegionCylinder (R i.1) (S i.1))).IsOrtho
      (coordinateSubspaceES (dependentRegionCylinder (R j)
        (nestedCylinderInnovation R hR S j))) :=
  coordinate_ortho_of_mul_eq_zero _ _ (earlier_projector_mul_innovation_eq_zero R hR S j)

private theorem innovation_le_original_prefix
    (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (j : Fin n) :
    dependentRegionCylinder (R j) (nestedCylinderInnovation R hR S j) ≤
      ⨆ i : {i : Fin n // i ≤ j}, dependentRegionCylinder (R i.1) (S i.1) := by
  apply le_trans (le_sup_right : _ ≤
    (⨆ i : {i : Fin n // i < j}, dependentRegionCylinder (R i.1) (S i.1)) ⊔ _)
  rw [nestedCylinderInnovation_sup]
  exact sup_le (iSup_le fun i => le_iSup_of_le ⟨i.1, i.2.le⟩ le_rfl)
    (le_iSup_of_le ⟨j, le_rfl⟩ le_rfl)

private theorem original_le_innovation_prefix
    (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (j : Fin n) :
    dependentRegionCylinder (R j) (S j) ≤
      ⨆ i : {i : Fin n // i ≤ j},
        dependentRegionCylinder (R i.1) (nestedCylinderInnovation R hR S i.1) := by
  induction j using (show WellFounded ((· < ·) : Fin n → Fin n → Prop)
      from wellFounded_lt).induction with
  | h j ih =>
    apply le_trans (le_sup_right : _ ≤
      (⨆ i : {i : Fin n // i < j}, dependentRegionCylinder (R i.1) (S i.1)) ⊔ _)
    rw [← nestedCylinderInnovation_sup R hR S j]
    refine sup_le (iSup_le fun i => (ih i.1 i.2).trans ?_) (le_iSup_of_le ⟨j, le_rfl⟩ le_rfl)
    exact iSup_le fun k => le_iSup_of_le ⟨k.1, k.2.trans i.2.le⟩ le_rfl

/-- Every prefix of innovation cylinders spans exactly the corresponding original prefix.
The bound may be zero or larger than the family length. -/
theorem nestedCylinderInnovation_prefix_span
    (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (k : ℕ) :
    (⨆ i : {i : Fin n // i.1 < k},
      dependentRegionCylinder (R i.1) (nestedCylinderInnovation R hR S i.1)) =
      ⨆ i : {i : Fin n // i.1 < k}, dependentRegionCylinder (R i.1) (S i.1) := by
  apply le_antisymm
  · refine iSup_le fun i => (innovation_le_original_prefix R hR S i.1).trans ?_
    exact iSup_le fun j => le_iSup_of_le ⟨j.1, lt_of_le_of_lt j.2 i.2⟩ le_rfl
  · refine iSup_le fun i => (original_le_innovation_prefix R hR S i.1).trans ?_
    exact iSup_le fun j => le_iSup_of_le ⟨j.1, lt_of_le_of_lt j.2 i.2⟩ le_rfl

/-- All innovation cylinders have the same span as the original cylinders. -/
theorem nestedCylinderInnovation_span
    (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ)) :
    (⨆ i, dependentRegionCylinder (R i) (nestedCylinderInnovation R hR S i)) =
      ⨆ i, dependentRegionCylinder (R i) (S i) := by
  apply le_antisymm
  · exact iSup_le fun i => (innovation_le_original_prefix R hR S i).trans
      (iSup_le fun j => le_iSup_of_le j.1 le_rfl)
  · exact iSup_le fun i => (original_le_innovation_prefix R hR S i).trans
      (iSup_le fun j => le_iSup_of_le j.1 le_rfl)

private theorem innovation_projectors_mul_eq_zero
    (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    {i j : Fin n} (hij : i < j) :
    coordinateRangeProjector (dependentRegionCylinder (R i) (nestedCylinderInnovation R hR S i)) *
      coordinateRangeProjector (dependentRegionCylinder (R j) (nestedCylinderInnovation R hR S j)) =
        0 := by
  let E := ⨆ k : {k : Fin n // k < j}, dependentRegionCylinder (R k.1) (S k.1)
  let T := dependentRegionCylinder (R i) (nestedCylinderInnovation R hR S i)
  have hTE : T ≤ E := (innovation_le_original_prefix R hR S i).trans
    (iSup_le fun k => le_iSup_of_le ⟨k.1, lt_of_le_of_lt k.2 hij⟩ le_rfl)
  have hET : coordinateRangeProjector E * coordinateRangeProjector T =
      coordinateRangeProjector T := by
    apply matrix_mul_eq_right_of_range_le
      (coordinateRangeProjector_isStarProjection E).isIdempotentElem.eq
    simpa only [range_coordinateRangeProjector] using hTE
  have hTE' : coordinateRangeProjector T * coordinateRangeProjector E =
      coordinateRangeProjector T := by
    simpa only [star_mul, (coordinateRangeProjector_isStarProjection E).isSelfAdjoint.star_eq,
      (coordinateRangeProjector_isStarProjection T).isSelfAdjoint.star_eq] using congrArg star hET
  change coordinateRangeProjector T * _ = 0
  rw [← hTE', mul_assoc, earlier_projector_mul_innovation_eq_zero R hR S j, mul_zero]

/-- Distinct innovation cylinders are orthogonal in the physical coordinate inner product. -/
theorem nestedCylinderInnovation_pairwise_orthogonal
    (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ)) :
    Pairwise fun i j =>
      (coordinateSubspaceES (dependentRegionCylinder (R i)
        (nestedCylinderInnovation R hR S i))).IsOrtho
      (coordinateSubspaceES (dependentRegionCylinder (R j)
        (nestedCylinderInnovation R hR S j))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact coordinate_ortho_of_mul_eq_zero _ _ (innovation_projectors_mul_eq_zero R hR S h)
  · exact (coordinate_ortho_of_mul_eq_zero _ _
      (innovation_projectors_mul_eq_zero R hR S h)).symm

/-- The projection onto the original span is the sum of the lifted innovation projectors. -/
theorem nestedCylinderInnovation_projector_sum
    (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ)) :
    coordinateRangeProjector (⨆ i, dependentRegionCylinder (R i) (S i)) =
      ∑ i, dependentRegionOperatorLift (R i)
        (coordinateRangeProjector (nestedCylinderInnovation R hR S i)) := by
  classical
  rw [← nestedCylinderInnovation_span R hR S, ← Finset.sup_univ_eq_iSup]
  have hp : Pairwise fun i j =>
      coordinateRangeProjector (dependentRegionCylinder (R i) (nestedCylinderInnovation R hR S i)) *
        coordinateRangeProjector (dependentRegionCylinder (R j)
          (nestedCylinderInnovation R hR S j)) = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact innovation_projectors_mul_eq_zero R hR S h
    · have he := congrArg star (innovation_projectors_mul_eq_zero R hR S h)
      simpa only [star_mul, (coordinateRangeProjector_isStarProjection _).isSelfAdjoint.star_eq,
        star_zero] using he
  rw [projector_finset_sup _ hp]
  simp only [coordinateRangeProjector_dependentRegionCylinder]

/-- The sum of inside innovation dimensions is no larger than the original inside-rank sum. -/
theorem sum_finrank_nestedCylinderInnovation_le
    (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ)) :
    (∑ i, Module.finrank ℂ (nestedCylinderInnovation R hR S i)) ≤
      ∑ i, Module.finrank ℂ (S i) :=
  Finset.sum_le_sum fun i _ => finrank_nestedCylinderInnovation_le R hR S i

/-- The integer inside-rank sum satisfies the same bound; no outside dimension enters it. -/
theorem sum_int_finrank_nestedCylinderInnovation_le
    (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ)) :
    (∑ i, (Module.finrank ℂ (nestedCylinderInnovation R hR S i) : ℤ)) ≤
      ∑ i, (Module.finrank ℂ (S i) : ℤ) := by
  exact_mod_cast sum_finrank_nestedCylinderInnovation_le R hR S

/-- The projector onto the cylinder span is supported on every region containing all
original regions. This assertion also holds for the empty family. -/
theorem nestedCylinder_projector_supported
    (R : Fin n → Finset V)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (U : Finset V) (hU : ∀ i, R i ⊆ U) :
    ∃ T : Submodule ℂ (((w : {w : V // w ∈ U}) → Out w.1) → ℂ),
      coordinateRangeProjector (⨆ i, dependentRegionCylinder (R i) (S i)) =
        dependentRegionOperatorLift U (coordinateRangeProjector T) := by
  refine ⟨⨆ i, (dependentSubregionOperatorLift (R i) U (hU i)
    (coordinateRangeProjector (S i))).mulVecLin.range, ?_⟩
  rw [← coordinateRangeProjector_dependentRegionCylinder, dependentRegionCylinder_iSup]
  simp only [dependentRegionCylinder_subregion]

/-- A current inside space already contained in the earlier inside span contributes zero. -/
theorem nestedCylinderInnovation_eq_bot_of_le
    (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (j : Fin n) (hS : S j ≤ nestedCylinderEarlierInside R hR S j) :
    nestedCylinderInnovation R hR S j = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  rintro x ⟨y, hy, rfl⟩
  change y - coordinateRangeProjector (nestedCylinderEarlierInside R hR S j) *ᵥ y = 0
  rw [(coordinateRangeProjector_mulVec_eq_self_iff _ _).mpr (hS hy), sub_self]

end TNLean.PEPS
