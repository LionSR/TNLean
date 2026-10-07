/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.NestedCylinderOrthogonalization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tilted-line counterexamples for nested-cylinder orthogonalization

In complex dimension two, projecting the line through \((1,1)\) away from the
first coordinate axis gives the second coordinate axis. Intersecting that line
with the orthogonal complement instead gives zero. The sandwich of the original
line projector with the complementary coordinate projector has diagonal
\((0,1/2)\), and is not a projector.

The final examples realize these same lines on two repeated one-site regions
and compute the actual nested-cylinder innovation.
-/

open scoped BigOperators Matrix
open TNLean.PEPS

namespace TNLeanTest.NestedCylinderCounterexamples

noncomputable section

private def e₁ : Fin 2 → ℂ := ![1, 0]
private def e₂ : Fin 2 → ℂ := ![0, 1]
private def tilted : Fin 2 → ℂ := ![1, 1]

private def firstAxis : Submodule ℂ (Fin 2 → ℂ) := Submodule.span ℂ {e₁}
private def secondAxis : Submodule ℂ (Fin 2 → ℂ) := Submodule.span ℂ {e₂}
private def tiltedLine : Submodule ℂ (Fin 2 → ℂ) := Submodule.span ℂ {tilted}

private def firstProjector : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
private def tiltedProjector : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

private theorem firstProjector_mulVec (x : Fin 2 → ℂ) :
    firstProjector *ᵥ x = x 0 • e₁ := by
  ext i
  fin_cases i <;> simp [firstProjector, e₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem tiltedProjector_mulVec (x : Fin 2 → ℂ) :
    tiltedProjector *ᵥ x = ((x 0 + x 1) / 2) • tilted := by
  ext i
  fin_cases i <;>
    simp [tiltedProjector, tilted, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

private theorem firstProjector_isStarProjection : IsStarProjection firstProjector := by
  rw [isStarProjection_iff']
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [firstProjector, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

private theorem tiltedProjector_isStarProjection : IsStarProjection tiltedProjector := by
  rw [isStarProjection_iff']
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [tiltedProjector, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

private theorem firstProjector_range : firstProjector.mulVecLin.range = firstAxis := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨y 0, (firstProjector_mulVec y).symm⟩
  · intro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨c • e₁, ?_⟩
    simpa [e₁] using firstProjector_mulVec (c • e₁)

private theorem tiltedProjector_range : tiltedProjector.mulVecLin.range = tiltedLine := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Submodule.mem_span_singleton.mpr
      ⟨(y 0 + y 1) / 2, (tiltedProjector_mulVec y).symm⟩
  · intro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨c • tilted, ?_⟩
    simpa [tilted] using tiltedProjector_mulVec (c • tilted)

private theorem coordinateRangeProjector_firstAxis :
    coordinateRangeProjector firstAxis = firstProjector :=
  (eq_coordinateRangeProjector_of_range firstProjector_isStarProjection firstAxis
    firstProjector_range).symm

private theorem coordinateRangeProjector_tiltedLine :
    coordinateRangeProjector tiltedLine = tiltedProjector :=
  (eq_coordinateRangeProjector_of_range tiltedProjector_isStarProjection tiltedLine
    tiltedProjector_range).symm

private theorem projectedImage_eq_secondAxis :
    tiltedLine.map (1 - coordinateRangeProjector firstAxis).mulVecLin = secondAxis := by
  rw [coordinateRangeProjector_firstAxis]
  have h : (1 - firstProjector).mulVecLin tilted = e₂ := by
    rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
      firstProjector_mulVec]
    ext i
    fin_cases i <;> simp [tilted, e₁, e₂]
  simpa only [tiltedLine, secondAxis, Submodule.map_span, Set.image_singleton] using
    congrArg (fun x : Fin 2 → ℂ => Submodule.span ℂ {x}) h

-- The genuine projected image is a nonzero line.
example : tiltedLine.map (1 - coordinateRangeProjector firstAxis).mulVecLin =
    Submodule.span ℂ {e₂} := projectedImage_eq_secondAxis

example : tiltedLine.map (1 - coordinateRangeProjector firstAxis).mulVecLin ≠ ⊥ := by
  rw [projectedImage_eq_secondAxis]
  intro h
  have he : e₂ ∈ secondAxis := Submodule.mem_span_singleton_self e₂
  rw [h, Submodule.mem_bot] at he
  have := congrFun he 1
  norm_num [e₂] at this

-- Intersecting the original tilted line with the orthogonal complement loses it entirely.
private theorem tiltedLine_inf_orthogonal_eq_bot :
    coordinateSubspaceES tiltedLine ⊓ (coordinateSubspaceES firstAxis)ᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx.1
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have he : WithLp.toLp 2 e₁ ∈ coordinateSubspaceES firstAxis :=
    ⟨e₁, Submodule.mem_span_singleton_self e₁, rfl⟩
  have hinner := (Submodule.mem_orthogonal _ _).mp hx.2 _ he
  have hc : c = 0 := by
    simpa [PiLp.inner_apply, Fin.sum_univ_two, e₁, tilted] using hinner
  simp [hc]

example : coordinateSubspaceES tiltedLine ⊓ (coordinateSubspaceES firstAxis)ᗮ = ⊥ :=
  tiltedLine_inf_orthogonal_eq_bot

private def sandwich : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 - coordinateRangeProjector firstAxis) * coordinateRangeProjector tiltedLine *
    (1 - coordinateRangeProjector firstAxis)

private theorem sandwich_eq : sandwich = !![0, 0; 0, 1 / 2] := by
  rw [sandwich, coordinateRangeProjector_firstAxis, coordinateRangeProjector_tiltedLine]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstProjector, tiltedProjector, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply]

-- Exact rational coefficients distinguish the sandwich from the true range projector.
example : sandwich = !![0, 0; 0, (1 / 2 : ℂ)] := sandwich_eq

example : sandwich * sandwich ≠ sandwich := by
  intro h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h
  norm_num [sandwich_eq, Matrix.mul_apply, Fin.sum_univ_two] at h11

example : ¬ IsStarProjection sandwich := by
  intro h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1)
    h.isIdempotentElem.eq
  norm_num [sandwich_eq, Matrix.mul_apply, Fin.sum_univ_two] at h11

/-! ## The tilted-line example in repeated dependent-region coordinates -/

private abbrev Config := {w : Fin 1 // w ∈ (Finset.univ : Finset (Fin 1))} → Fin 2

private def configEquiv : Config ≃ Fin 2 where
  toFun σ := σ ⟨0, Finset.mem_univ 0⟩
  invFun i := fun _ => i
  left_inv σ := by
    funext w
    exact congrArg σ (Subsingleton.elim _ _)
  right_inv _ := rfl

private def insideFirst : Config → ℂ := e₁ ∘ configEquiv
private def insideSecond : Config → ℂ := e₂ ∘ configEquiv
private def insideTilted : Config → ℂ := tilted ∘ configEquiv

private def insideFirstAxis : Submodule ℂ (Config → ℂ) := Submodule.span ℂ {insideFirst}
private def insideSecondAxis : Submodule ℂ (Config → ℂ) := Submodule.span ℂ {insideSecond}
private def insideTiltedLine : Submodule ℂ (Config → ℂ) := Submodule.span ℂ {insideTilted}

private def insideProjector : Matrix Config Config ℂ :=
  firstProjector.submatrix configEquiv configEquiv

private theorem insideProjector_mulVec (x : Config → ℂ) :
    insideProjector *ᵥ x = x (configEquiv.symm 0) • insideFirst := by
  rw [insideProjector, Matrix.submatrix_mulVec_equiv, firstProjector_mulVec]
  rfl

private theorem insideProjector_isStarProjection : IsStarProjection insideProjector := by
  rw [isStarProjection_iff']
  constructor
  · simpa only [insideProjector, Matrix.submatrix_mul_equiv] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M.submatrix configEquiv configEquiv)
        firstProjector_isStarProjection.isIdempotentElem.eq
  · ext a b
    exact congrFun (congrFun firstProjector_isStarProjection.isSelfAdjoint.star_eq
      (configEquiv a)) (configEquiv b)

private theorem insideProjector_range :
    insideProjector.mulVecLin.range = insideFirstAxis := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Submodule.mem_span_singleton.mpr
      ⟨y (configEquiv.symm 0), (insideProjector_mulVec y).symm⟩
  · intro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨c • insideFirst, ?_⟩
    change insideProjector *ᵥ (c • insideFirst) = c • insideFirst
    rw [insideProjector_mulVec]
    simp [insideFirst, Function.comp_def, e₁]

private theorem coordinateRangeProjector_insideFirstAxis :
    coordinateRangeProjector insideFirstAxis = insideProjector :=
  (eq_coordinateRangeProjector_of_range insideProjector_isStarProjection insideFirstAxis
    insideProjector_range).symm

private abbrev regions : Fin 2 → Finset (Fin 1) := fun _ => Finset.univ

private theorem regions_monotone : Monotone regions := fun _ _ _ => Finset.Subset.refl _

private def insideFamily (j : Fin 2) : Submodule ℂ (Config → ℂ) :=
  if j = 0 then insideFirstAxis else insideTiltedLine

private theorem full_subregion_lift
    (h : (Finset.univ : Finset (Fin 1)) ⊆ Finset.univ) (K : Matrix Config Config ℂ) :
    dependentSubregionOperatorLift (Out := fun _ : Fin 1 => Fin 2)
      Finset.univ Finset.univ h K = K := by
  classical
  ext a b
  simp [dependentSubregionOperatorLift]

private theorem earlierInside_one :
    nestedCylinderEarlierInside (Out := fun _ : Fin 1 => Fin 2)
      regions regions_monotone insideFamily 1 = insideFirstAxis := by
  unfold nestedCylinderEarlierInside
  simp only [regions, full_subregion_lift, range_coordinateRangeProjector]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    have hi : i.1 = 0 := by omega
    simp [insideFamily, hi]
  · exact le_iSup_of_le ⟨0, by decide⟩ (by simp [insideFamily])

private theorem innovation_one_eq_secondAxis :
    nestedCylinderInnovation (Out := fun _ : Fin 1 => Fin 2)
      regions regions_monotone insideFamily 1 = insideSecondAxis := by
  classical
  unfold nestedCylinderInnovation
  rw [earlierInside_one, coordinateRangeProjector_insideFirstAxis]
  change insideTiltedLine.map (LinearMap.id - insideProjector.mulVecLin) = insideSecondAxis
  have h : (LinearMap.id - insideProjector.mulVecLin : (Config → ℂ) →ₗ[ℂ] Config → ℂ)
      insideTilted = insideSecond := by
    change insideTilted - insideProjector *ᵥ insideTilted = insideSecond
    rw [insideProjector_mulVec]
    ext σ
    change tilted (configEquiv σ) -
      tilted (configEquiv (configEquiv.symm 0)) * e₁ (configEquiv σ) = e₂ (configEquiv σ)
    rw [configEquiv.apply_symm_apply]
    generalize configEquiv σ = i
    fin_cases i <;> simp [tilted, e₁, e₂]
  simpa only [insideTiltedLine, insideSecondAxis, Submodule.map_span,
    Set.image_singleton] using
    congrArg (fun x : Config → ℂ => Submodule.span ℂ {x}) h

-- This evaluates the production definition on actual repeated finite regions.
example : nestedCylinderInnovation (Out := fun _ : Fin 1 => Fin 2)
    regions regions_monotone insideFamily 1 = Submodule.span ℂ {insideSecond} :=
  innovation_one_eq_secondAxis

example : nestedCylinderInnovation (Out := fun _ : Fin 1 => Fin 2)
    regions regions_monotone insideFamily 1 ≠ ⊥ := by
  rw [innovation_one_eq_secondAxis]
  intro h
  have he : insideSecond ∈ insideSecondAxis := Submodule.mem_span_singleton_self insideSecond
  rw [h, Submodule.mem_bot] at he
  have := congrFun he (configEquiv.symm 1)
  norm_num [insideSecond, Function.comp_def, e₂] at this

end

end TNLeanTest.NestedCylinderCounterexamples
