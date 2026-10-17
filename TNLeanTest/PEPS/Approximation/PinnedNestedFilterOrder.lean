/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PinnedNestedFilterCoordinates

/-! Singular complex projections through the actual adapted source output. -/

noncomputable section

open Complex Matrix
open scoped ComplexOrder

namespace TNLean.PEPS.Approximation

open Pinned Pinned.NestedFilter

private def configurationEquiv : Configuration 1 2 ≃ Fin 2 where
  toFun σ := σ (0, 0)
  invFun i := fun _ ↦ i
  left_inv σ := by
    funext v
    exact congrArg σ (Subsingleton.elim _ _)
  right_inv _ := rfl

private def fullRegionEquiv : RegionConfiguration 2 (Finset.univ : Finset (Vertex 1)) ≃ Fin 2 where
  toFun σ := σ ⟨(0, 0), Finset.mem_univ _⟩
  invFun i := fun _ ↦ i
  left_inv σ := by
    funext v
    exact congrArg σ (Subsingleton.elim _ _)
  right_inv _ := rfl

private def oneSiteState : EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ] State 1 2 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ configurationEquiv.symm

private def oneSiteFilter (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef) :
    PositiveFilter 2 (Finset.univ : Finset (Vertex 1)) :=
  ⟨reindex fullRegionEquiv.symm fullRegionEquiv.symm A, hA.submatrix fullRegionEquiv⟩

private theorem oneSite_lift (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef) :
    liftLocal Finset.univ (oneSiteFilter A hA).matrix =
      reindex configurationEquiv.symm configurationEquiv.symm A := by
  ext σ τ
  simp [liftLocal, oneSiteFilter, reindex_apply, fullRegionEquiv, configurationEquiv]

private theorem oneSite_action (A : Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : EuclideanSpace ℂ (Fin 2)) :
    toEuclideanLin (reindex configurationEquiv.symm configurationEquiv.symm A)
      (oneSiteState ψ) = oneSiteState (toEuclideanLin A ψ) := by
  ext σ
  exact congrFun (reindex_mulVec configurationEquiv.symm A (WithLp.ofLp ψ)) σ

private def firstProjection : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 0]

private def complexProjection : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℝ) • vecMulVec ![1, I] (star ![1, I])

private theorem complexProjection_apply (i j : Fin 2) :
    complexProjection i j = (1 / 2 : ℝ) •
      ((![1, I] : Fin 2 → ℂ) i * star ((![1, I] : Fin 2 → ℂ) j)) := rfl

private theorem firstProjection_positive : firstProjection.PosSemidef := by
  apply posSemidef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num

private theorem complexProjection_positive : complexProjection.PosSemidef :=
  (posSemidef_vecMulVec_self_star (![1, I] : Fin 2 → ℂ)).smul
    (by norm_num : (0 : ℝ) ≤ 1 / 2)

private def projectionFamily : FilterFamily 2 2
    (fun _ ↦ (Finset.univ : Finset (Vertex 1))) :=
  ![oneSiteFilter firstProjection firstProjection_positive,
    oneSiteFilter complexProjection complexProjection_positive]

private theorem projectionFamily_output (ψ : EuclideanSpace ℂ (Fin 2)) :
    output projectionFamily (oneSiteState ψ) =
      oneSiteState (toEuclideanLin (complexProjection * firstProjection) ψ) := by
  have hfold : output projectionFamily (oneSiteState ψ) =
      toEuclideanLin
        (liftLocal Finset.univ (oneSiteFilter complexProjection complexProjection_positive).matrix *
          liftLocal Finset.univ (oneSiteFilter firstProjection firstProjection_positive).matrix)
        (oneSiteState ψ) := by
    simpa [output, projectionFamily, asMap, List.ofFn_succ] using
      foldl_toEuclideanCLM_eq_reverse_prod
        [liftLocal Finset.univ (oneSiteFilter firstProjection firstProjection_positive).matrix,
          liftLocal Finset.univ (oneSiteFilter complexProjection complexProjection_positive).matrix]
        (oneSiteState ψ)
  rw [hfold, oneSite_lift, oneSite_lift,
    ← map_mul (reindexAlgEquiv ℂ ℂ configurationEquiv.symm)]
  exact oneSite_action _ ψ

private theorem projectionFamily_e0 :
    output projectionFamily (oneSiteState (WithLp.toLp 2 ![(1 : ℂ), 0])) =
      oneSiteState (WithLp.toLp 2 ![(1 / 2 : ℂ), I / 2]) := by
  rw [projectionFamily_output]
  apply congrArg oneSiteState
  ext i
  fin_cases i <;>
    norm_num [firstProjection, complexProjection_apply, toLpLin_apply, mulVec, dotProduct,
      Fin.sum_univ_two, mul_apply, Complex.ext_iff]

-- Both matrices are singular; the test does not assume they form a maximizing family.
example : firstProjection.det = 0 ∧ complexProjection.det = 0 := by
  constructor <;> norm_num [firstProjection, det_fin_two,
    complexProjection_apply, Complex.ext_iff]

-- The actual source output on repeated full regions is Q P e₀ = (1,i)/2.
example : output projectionFamily (oneSiteState (WithLp.toLp 2 ![(1 : ℂ), 0])) =
    oneSiteState (WithLp.toLp 2 ![(1 / 2 : ℂ), I / 2]) :=
  projectionFamily_e0

-- Reversing the action order or transposing its product gives different original-grid states.
example :
    output projectionFamily (oneSiteState (WithLp.toLp 2 ![(1 : ℂ), 0])) ≠
      oneSiteState (toEuclideanLin (firstProjection * complexProjection)
        (WithLp.toLp 2 ![(1 : ℂ), 0])) ∧
    output projectionFamily (oneSiteState (WithLp.toLp 2 ![(1 : ℂ), 0])) ≠
      oneSiteState (toEuclideanLin (complexProjection * firstProjection)ᵀ
        (WithLp.toLp 2 ![(1 : ℂ), 0])) := by
  rw [projectionFamily_e0]
  constructor <;> intro h
  all_goals
    have hIm := congrArg (fun ψ : EuclideanSpace ℂ (Fin 2) ↦ (ψ 1).im)
      (oneSiteState.injective h)
    norm_num [firstProjection, complexProjection, toLpLin_apply, mulVec, dotProduct,
      Fin.sum_univ_two, mul_apply, vecMulVec_apply, transpose_apply] at hIm

-- A nonzero input killed by a singular filter has exactly zero normalized output.
example :
    output projectionFamily (oneSiteState (WithLp.toLp 2 ![(0 : ℂ), 1])) = 0 ∧
      normalizedOutput projectionFamily
        (oneSiteState (WithLp.toLp 2 ![(0 : ℂ), 1])) = 0 := by
  have hz : output projectionFamily
      (oneSiteState (WithLp.toLp 2 ![(0 : ℂ), 1])) = 0 := by
    rw [projectionFamily_output, ← map_zero oneSiteState]
    apply congrArg oneSiteState
    ext i
    fin_cases i <;>
      norm_num [firstProjection, complexProjection_apply, toLpLin_apply, mulVec, dotProduct,
        Fin.sum_univ_two, mul_apply, Complex.ext_iff]
  exact ⟨hz, by simp only [normalizedOutput, hz, smul_zero]⟩

end TNLean.PEPS.Approximation
