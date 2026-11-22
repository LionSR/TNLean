/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryMap.SpectatorBoundaryGram
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.DimensionConstant.MatrixUnitPaths
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.DimensionConstant.MarkovMatrix

/-!
# Boundary vectors multiplied on spectator sites

Multiplying a full boundary vector by a function of the spectator configuration
preserves membership in the corresponding interval ground-space range.

## A matrix coefficient lower bound for a projection defect

Unit vectors in two subspaces, one orthogonal to a third subspace, give a
lower bound for the norm of the product of the first two projections minus
the third projection. This is the Hilbert-space estimate used to test the
constant in Nachtergaele, arXiv:cond-mat/9410110, Section 6, equation `boundAm`.

## Physical witnesses for the dimension-four projection defect

Marked paths in a weighted matrix-unit tensor give unit vectors in two
three-site interval spaces. Their matrix coefficient bounds the overlap
projection defect from below, as required to test the dimension-only constant
in Nachtergaele, arXiv:cond-mat/9410110, Section 6, equation `boundAm`.
-/

section

namespace MPSTensor

/-- A multiplier on the prefix spectator sites is absorbed into the boundary
matrix of the tail interval. -/
theorem marked_groundSpaceMap_mem_tailBoundaryRange
    {d D : ℕ} (A : MPSTensor d D) (K L : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (u : Cfg d K → ℂ) :
    WithLp.toLp 2 (fun σ : Cfg d (K + L) ↦
      u (σ ∘ Fin.castAdd L) * groundSpaceMap A (K + L) X σ) ∈
        (tailBoundaryMapES A K L).range := by
  refine ⟨(boundaryFamilyEquiv (D := D) (Cfg d K)).symm
    (fun τ ↦ u τ • (X * Kraus.evalWord A (List.ofFn τ))), ?_⟩
  apply PiLp.ext
  intro σ
  change tailBoundaryMap A K L
    (boundaryFamilyEquiv (D := D) (Cfg d K)
      ((boundaryFamilyEquiv (D := D) (Cfg d K)).symm _)) σ = _
  rw [LinearEquiv.apply_symm_apply, tailBoundaryMap_apply,
    Matrix.mul_smul, Matrix.trace_smul]
  change u (σ ∘ Fin.castAdd L) *
    tailBoundaryMap A K L (fun τ ↦ X * Kraus.evalWord A (List.ofFn τ)) σ = _
  rw [tailBoundaryMap_factorization]

/-- A multiplier on the suffix spectator sites is absorbed into the boundary
matrix of the left interval. -/
theorem marked_groundSpaceMap_mem_leftBoundaryRange
    {d D : ℕ} (A : MPSTensor d D) (K L : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (u : Cfg d L → ℂ) :
    WithLp.toLp 2 (fun σ : Cfg d (K + L) ↦
      u (σ ∘ Fin.natAdd K) * groundSpaceMap A (K + L) X σ) ∈
        (leftBoundaryMapES A K L).range := by
  refine ⟨(boundaryFamilyEquiv (D := D) (Cfg d L)).symm
    (fun τ ↦ u τ • (Kraus.evalWord A (List.ofFn τ) * X)), ?_⟩
  apply PiLp.ext
  intro σ
  change leftBoundaryMap A K L
    (boundaryFamilyEquiv (D := D) (Cfg d L)
      ((boundaryFamilyEquiv (D := D) (Cfg d L)).symm _)) σ = _
  rw [LinearEquiv.apply_symm_apply, leftBoundaryMap_apply,
    Matrix.mul_smul, Matrix.trace_smul]
  change u (σ ∘ Fin.natAdd K) *
    leftBoundaryMap A K L (fun τ ↦ Kraus.evalWord A (List.ofFn τ) * X) σ = _
  rw [leftBoundaryMap_factorization]

end MPSTensor

end

section

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Unit witnesses bound a projection defect from below by their inner product. -/
theorem norm_inner_le_norm_projection_defect
    (U V W : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    {x y : E} (hx : x ∈ V) (hy : y ∈ U) (hxW : x ∈ Wᗮ)
    (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1) :
    ‖inner ℂ y x‖ ≤ ‖U.starProjection.comp V.starProjection - W.starProjection‖ := by
  have hinner : inner ℂ y
      ((U.starProjection.comp V.starProjection - W.starProjection) x) = inner ℂ y x := by
    simp only [FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.comp_apply,
      V.starProjection_eq_self_iff.mpr hx, W.starProjection_apply_eq_zero_iff.mpr hxW,
      sub_zero, ← U.inner_starProjection_left_eq_right,
      U.starProjection_eq_self_iff.mpr hy]
  exact (show ‖inner ℂ y x‖ ≤
      ‖(U.starProjection.comp V.starProjection - W.starProjection) x‖ from
    by simpa only [hinner, hny, one_mul] using
      norm_inner_le_norm (𝕜 := ℂ) y
        ((U.starProjection.comp V.starProjection - W.starProjection) x)).trans
      (by simpa only [hnx, mul_one] using
        (U.starProjection.comp V.starProjection - W.starProjection).le_opNorm x)

/-- The same witnesses bound the defect with the two projections reversed. -/
theorem norm_inner_le_norm_projection_defect_reverse [CompleteSpace E]
    (U V W : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    {x y : E} (hx : x ∈ V) (hy : y ∈ U) (hxW : x ∈ Wᗮ)
    (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1) :
    ‖inner ℂ y x‖ ≤ ‖V.starProjection.comp U.starProjection - W.starProjection‖ := by
  have h := norm_inner_le_norm_projection_defect U V W hx hy hxW hnx hny
  simpa only [← ContinuousLinearMap.mul_def, star_sub, star_mul,
    (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection V).star_eq, (isSelfAdjoint_starProjection W).star_eq] using
    h.trans_eq (norm_star (U.starProjection * V.starProjection - W.starProjection)).symm

end Submodule

end

section

open scoped BigOperators Matrix InnerProductSpace

namespace MPSTensor.FNWDimensionConstant

variable {k : ℕ}

/-- A mark at the first internal vertex acts only on the prefix spectator. -/
theorem pathVector_first_mark_mem_tailBoundaryRange
    (t : Matrix (Fin k) (Fin k) ℝ) (u : Fin k → ℝ) (a f : Fin k) :
    pathVector t (fun b _ ↦ u b) a f ∈
      (tailBoundaryMapES (matrixUnitTensor t) 1 3).range := by
  convert marked_groundSpaceMap_mem_tailBoundaryRange (matrixUnitTensor t) 1 3
    (Matrix.single f a 1) (fun τ ↦ (u (finProdFinEquiv.symm (τ 0)).2 : ℂ)) using 1
  apply PiLp.ext
  intro σ
  rw [pathVector_first_mark_apply, pathVector_one_eq_groundSpaceMap]
  rfl

/-- A mark at the last internal vertex acts only on the suffix spectator. -/
theorem pathVector_last_mark_mem_leftBoundaryRange
    (t : Matrix (Fin k) (Fin k) ℝ) (u : Fin k → ℝ) (a f : Fin k) :
    pathVector t (fun _ e ↦ u e) a f ∈
      (leftBoundaryMapES (matrixUnitTensor t) 3 1).range := by
  convert marked_groundSpaceMap_mem_leftBoundaryRange (matrixUnitTensor t) 3 1
    (Matrix.single f a 1) (fun τ ↦ (u (finProdFinEquiv.symm (τ 0)).1 : ℂ)) using 1
  apply PiLp.ext
  intro σ
  rw [pathVector_last_mark_apply, pathVector_one_eq_groundSpaceMap]
  rfl

/-- Squared path amplitudes are classical path probabilities. -/
private theorem markovAmplitude_path_sq (a b c e f : Fin 4) :
    (markovAmplitude a b * markovAmplitude b c *
      markovAmplitude c e * markovAmplitude e f) ^ 2 =
      realMarkovMatrix a b * realMarkovMatrix b c *
        realMarkovMatrix c e * realMarkovMatrix e f := by
  simp only [mul_pow, markovAmplitude_sq]

/-- A sign mark, multiplied by two, has unit self-contraction. -/
private theorem marked_path_self_sum (z : Matrix (Fin 4) (Fin 4) ℝ)
    (hz : ∀ b e, z b e ^ 2 = 1) (a f : Fin 4) :
    (∑ b, ∑ c, ∑ e, (2 * z b e) * (2 * z b e) *
      (markovAmplitude a b * markovAmplitude b c *
        markovAmplitude c e * markovAmplitude e f) ^ 2) = 1 := by
  calc
    _ = ∑ b, ∑ c, ∑ e, 4 * (realMarkovMatrix a b * realMarkovMatrix b c *
        realMarkovMatrix c e * realMarkovMatrix e f) := by
      refine Finset.sum_congr₂ fun b _ c _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
      rw [markovAmplitude_path_sq]
      calc
        _ = 4 * (z b e) ^ 2 * (realMarkovMatrix a b * realMarkovMatrix b c *
            realMarkovMatrix c e * realMarkovMatrix e f) := by ring
        _ = _ := by rw [hz]; ring
    _ = 1 := by simp only [← Finset.mul_sum,
        realMarkovMatrix_path_sum]; norm_num

/-- The first Hadamard mark has zero contraction with every full boundary. -/
private theorem marked_path_zero_sum (a f : Fin 4) :
    (∑ b, ∑ c, ∑ e, (2 * realHadamardU b) *
      (markovAmplitude a b * markovAmplitude b c *
        markovAmplitude c e * markovAmplitude e f) ^ 2) = 0 := by
  simp_rw [markovAmplitude_path_sq, mul_assoc (2 : ℝ)]
  simp only [← Finset.mul_sum _ _ (2 : ℝ), realMarkovMatrix_path_hadamardU_sum, mul_zero]

/-- The two different Hadamard marks have scalar contraction one sixteenth. -/
private theorem marked_path_cross_sum (a f : Fin 4) :
    (∑ b, ∑ c, ∑ e, (2 * realHadamardW e) * (2 * realHadamardU b) *
      (markovAmplitude a b * markovAmplitude b c *
        markovAmplitude c e * markovAmplitude e f) ^ 2) = 1 / 16 := by
  calc
    _ = ∑ b, ∑ c, ∑ e, 4 * (realHadamardU b * realHadamardW e *
        (realMarkovMatrix a b * realMarkovMatrix b c *
          realMarkovMatrix c e * realMarkovMatrix e f)) := by
      refine Finset.sum_congr₂ fun b _ c _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
      rw [markovAmplitude_path_sq]
      ring
    _ = 1 / 16 := by
      simp only [← Finset.mul_sum _ _ (4 : ℝ), realMarkovMatrix_path_hadamardUW_sum]
      norm_num

/-- At overlap length two, the physical projection defect of the dimension-four
weighted matrix-unit tensor is at least one sixteenth. The product is the
adjoint of the order printed in Nachtergaele, arXiv:cond-mat/9410110, Section 6,
equation `boundAm`, and has the same norm. -/
theorem dimensionFour_projection_defect_lower :
    (1 / 16 : ℝ) ≤
      ‖(tailBoundaryMapES (matrixUnitTensor markovAmplitude) 1 3).range.starProjection.comp
          (leftBoundaryMapES (matrixUnitTensor markovAmplitude) 3 1).range.starProjection -
        (groundSpaceES (matrixUnitTensor markovAmplitude) 4).starProjection‖ := by
  let x := pathVector markovAmplitude (fun b _ ↦ 2 * realHadamardU b) 0 0
  let y := pathVector markovAmplitude (fun _ e ↦ 2 * realHadamardW e) 0 0
  have hx : x ∈ (tailBoundaryMapES (matrixUnitTensor markovAmplitude) 1 3).range :=
    pathVector_first_mark_mem_tailBoundaryRange markovAmplitude
      (fun b ↦ 2 * realHadamardU b) 0 0
  have hy : y ∈ (leftBoundaryMapES (matrixUnitTensor markovAmplitude) 3 1).range :=
    pathVector_last_mark_mem_leftBoundaryRange markovAmplitude
      (fun e ↦ 2 * realHadamardW e) 0 0
  have hxW : x ∈ (groundSpaceES (matrixUnitTensor markovAmplitude) 4)ᗮ :=
    pathVector_mem_groundSpaceES_orthogonal markovAmplitude
      (fun b _ ↦ 2 * realHadamardU b) 0 0 (marked_path_zero_sum 0 0)
  have hnx : ‖x‖ = 1 := norm_pathVector_eq_one markovAmplitude
    (fun b _ ↦ 2 * realHadamardU b) 0 0
    (marked_path_self_sum (fun b _ ↦ realHadamardU b)
      (fun b _ ↦ realHadamardU_sq b) 0 0)
  have hny : ‖y‖ = 1 := norm_pathVector_eq_one markovAmplitude
    (fun _ e ↦ 2 * realHadamardW e) 0 0
    (marked_path_self_sum (fun _ e ↦ realHadamardW e)
      (fun _ e ↦ realHadamardW_sq e) 0 0)
  have hinner : ‖inner ℂ y x‖ = 1 / 16 := by
    have hi := inner_pathVector markovAmplitude
      (fun _ e ↦ 2 * realHadamardW e) (fun b _ ↦ 2 * realHadamardU b) 0 0
    rw [marked_path_cross_sum] at hi
    change ‖inner ℂ (pathVector markovAmplitude (fun _ e ↦ 2 * realHadamardW e) 0 0)
      (pathVector markovAmplitude (fun b _ ↦ 2 * realHadamardU b) 0 0)‖ = _
    rw [hi]
    norm_num
  have h := Submodule.norm_inner_le_norm_projection_defect_reverse
    (leftBoundaryMapES (matrixUnitTensor markovAmplitude) 3 1).range
    (tailBoundaryMapES (matrixUnitTensor markovAmplitude) 1 3).range
    (groundSpaceES (matrixUnitTensor markovAmplitude) 4) hx hy hxW hnx hny
  rwa [hinner] at h

end MPSTensor.FNWDimensionConstant

end
