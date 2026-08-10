/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.GramConvergence
import TNLean.MPS.ParentHamiltonian.ProjectorCancellation
import TNLean.MPS.ParentHamiltonian.TailVirtualGram

/-!
# Direct-sum factors for the centered overlap residual

This file defines the two boundary multiplications in the centered overlapping
Gram as maps into a common direct sum indexed by a prefix and one final site.
Their norms are controlled by the corresponding virtual word maps without a
factor depending on the number of prefix configurations.  The construction and
factorization are exact algebraic consequences of the boundary-map formulas.

## Main definitions

* `MPSTensor.c3LeftOverlapFactorES` and `MPSTensor.c3RightOverlapFactorES` are the two common
  direct-sum factors.
* `MPSTensor.c3CenteredVirtualResidualES` is the centered virtual residual in the
  tail-after-left overlap orientation.

## Main results

* `MPSTensor.c3LeftOverlapFactorES_norm_le` and
  `MPSTensor.c3RightOverlapFactorES_norm_le` give
  bounds uniform in the spectator configuration type.
* `MPSTensor.c3_centeredVirtualResidualES_eq_overlapFactors` factors the centered
  overlapping Gram through its finite Gram error.
* `MPSTensor.c3_centeredVirtualResidualES_norm_le` is the resulting operator-norm bound.
* `MPSTensor.IsPrimitiveMPS.c3_centeredVirtualResidualES_norm_sq_le_geometric` gives the
  squared geometric estimate, uniformly in the prefix length.
-/

open scoped ComplexOrder Matrix Matrix.Norms.Frobenius

namespace MPSTensor

variable {d D : ℕ}

/-- The left direct-sum factor in the centered overlapping Gram.  On the
fiber indexed by a prefix \(u\) and final-site configuration \(j\), it sends the
input matrix \(X_u\) to \(A^j X_u\). -/
noncomputable def c3LeftOverlapFactorES (A : MPSTensor d D) (K : ℕ) :
    BoundaryFamilySpace (D := D) (Cfg d K) →L[ℂ]
      BoundaryFamilySpace (D := D) (Cfg d K × Cfg d 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun sp =>
        leftVirtualMapES A 1 (boundaryFamilyFiber (D := D) x sp.1.1) (sp.1.2, sp.2)
      map_add' := by
        intro x y
        apply PiLp.ext
        rintro ⟨⟨u, j⟩, p⟩
        change leftVirtualMapES A 1
          (boundaryFamilyFiber (D := D) (x + y) u) (j, p) = _
        rw [show boundaryFamilyFiber (D := D) (x + y) u =
            boundaryFamilyFiber (D := D) x u + boundaryFamilyFiber (D := D) y u by
          apply PiLp.ext
          intro q
          rfl, map_add]
        rfl
      map_smul' := by
        intro c x
        apply PiLp.ext
        rintro ⟨⟨u, j⟩, p⟩
        change leftVirtualMapES A 1
          (boundaryFamilyFiber (D := D) (c • x) u) (j, p) = _
        rw [show boundaryFamilyFiber (D := D) (c • x) u =
            c • boundaryFamilyFiber (D := D) x u by
          apply PiLp.ext
          intro q
          rfl, map_smul]
        rfl }

/-- The right direct-sum factor in the centered overlapping Gram.  On the
fiber indexed by a prefix \(u\) and final-site configuration \(j\), it sends the
input matrix \(Z_j\) to \(Z_j A^u\). -/
noncomputable def c3RightOverlapFactorES (A : MPSTensor d D) (K : ℕ) :
    BoundaryFamilySpace (D := D) (Cfg d 1) →L[ℂ]
      BoundaryFamilySpace (D := D) (Cfg d K × Cfg d 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 fun sp =>
        tailVirtualMapES A K (boundaryFamilyFiber (D := D) y sp.1.2) (sp.1.1, sp.2)
      map_add' := by
        intro x y
        apply PiLp.ext
        rintro ⟨⟨u, j⟩, p⟩
        change tailVirtualMapES A K
          (boundaryFamilyFiber (D := D) (x + y) j) (u, p) = _
        rw [show boundaryFamilyFiber (D := D) (x + y) j =
            boundaryFamilyFiber (D := D) x j + boundaryFamilyFiber (D := D) y j by
          apply PiLp.ext
          intro q
          rfl, map_add]
        rfl
      map_smul' := by
        intro c x
        apply PiLp.ext
        rintro ⟨⟨u, j⟩, p⟩
        change tailVirtualMapES A K
          (boundaryFamilyFiber (D := D) (c • x) j) (u, p) = _
        rw [show boundaryFamilyFiber (D := D) (c • x) j =
            c • boundaryFamilyFiber (D := D) x j by
          apply PiLp.ext
          intro q
          rfl, map_smul]
        rfl }

/-- Fiber formula for the left overlap factor. -/
@[simp]
theorem boundaryFamilyEquiv_c3LeftOverlapFactorES_apply
    (A : MPSTensor d D) (K : ℕ)
    (x : BoundaryFamilySpace (D := D) (Cfg d K))
    (u : Cfg d K) (j : Cfg d 1) :
    boundaryFamilyEquiv (D := D) (Cfg d K × Cfg d 1)
        (c3LeftOverlapFactorES A K x) (u, j) =
      evalWord A (List.ofFn j) *
        boundaryFamilyEquiv (D := D) (Cfg d K) x u := by
  apply (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).injective
  rw [← boundaryFamilyFiber_eq_frobeniusEquivEuclidean]
  calc
    boundaryFamilyFiber (D := D) (c3LeftOverlapFactorES A K x) (u, j) =
        boundaryFamilyFiber (D := D)
          (leftVirtualMapES A 1 (boundaryFamilyFiber (D := D) x u)) j := by
      apply PiLp.ext
      intro p
      rfl
    _ = Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
        (boundaryFamilyEquiv (D := D) (Cfg d 1)
          (leftVirtualMapES A 1 (boundaryFamilyFiber (D := D) x u)) j) :=
      boundaryFamilyFiber_eq_frobeniusEquivEuclidean _ _
    _ = _ := by
      rw [boundaryFamilyEquiv_leftVirtualMapES_apply,
        boundaryFamilyFiber_eq_frobeniusEquivEuclidean,
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm_apply_apply]

/-- Fiber formula for the right overlap factor. -/
@[simp]
theorem boundaryFamilyEquiv_c3RightOverlapFactorES_apply
    (A : MPSTensor d D) (K : ℕ)
    (y : BoundaryFamilySpace (D := D) (Cfg d 1))
    (u : Cfg d K) (j : Cfg d 1) :
    boundaryFamilyEquiv (D := D) (Cfg d K × Cfg d 1)
        (c3RightOverlapFactorES A K y) (u, j) =
      boundaryFamilyEquiv (D := D) (Cfg d 1) y j *
        evalWord A (List.ofFn u) := by
  apply (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).injective
  rw [← boundaryFamilyFiber_eq_frobeniusEquivEuclidean]
  calc
    boundaryFamilyFiber (D := D) (c3RightOverlapFactorES A K y) (u, j) =
        boundaryFamilyFiber (D := D)
          (tailVirtualMapES A K (boundaryFamilyFiber (D := D) y j)) u := by
      apply PiLp.ext
      intro p
      rfl
    _ = Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
        (boundaryFamilyEquiv (D := D) (Cfg d K)
          (tailVirtualMapES A K (boundaryFamilyFiber (D := D) y j)) u) :=
      boundaryFamilyFiber_eq_frobeniusEquivEuclidean _ _
    _ = _ := by
      rw [boundaryFamilyEquiv_tailVirtualMapES_apply,
        boundaryFamilyFiber_eq_frobeniusEquivEuclidean,
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm_apply_apply]

/-- The left direct-sum factor has no spectator-cardinality loss. -/
theorem c3LeftOverlapFactorES_norm_le (A : MPSTensor d D) (K : ℕ) :
    ‖c3LeftOverlapFactorES A K‖ ≤ ‖leftVirtualMapES A 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  rw [← sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_pow,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    ∑ sp : (Cfg d K × Cfg d 1) × (Fin D × Fin D),
        ‖c3LeftOverlapFactorES A K x sp‖ ^ 2 =
        ∑ u : Cfg d K, ‖leftVirtualMapES A 1
          (boundaryFamilyFiber (D := D) x u)‖ ^ 2 := by
      simp only [Fintype.sum_prod_type, EuclideanSpace.norm_sq_eq]
      rfl
    _ ≤ ∑ u : Cfg d K,
        (‖leftVirtualMapES A 1‖ * ‖boundaryFamilyFiber (D := D) x u‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro u _
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
          (ContinuousLinearMap.le_opNorm _ _)
    _ = ‖leftVirtualMapES A 1‖ ^ 2 *
        ∑ sp : Cfg d K × (Fin D × Fin D), ‖x sp‖ ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [mul_pow, EuclideanSpace.norm_sq_eq]
      simp only [boundaryFamilyFiber, Finset.mul_sum]

/-- The right direct-sum factor has no spectator-cardinality loss. -/
theorem c3RightOverlapFactorES_norm_le (A : MPSTensor d D) (K : ℕ) :
    ‖c3RightOverlapFactorES A K‖ ≤ ‖tailVirtualMapES A K‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
  rw [← sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_pow,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    ∑ sp : (Cfg d K × Cfg d 1) × (Fin D × Fin D),
        ‖c3RightOverlapFactorES A K y sp‖ ^ 2 =
        ∑ j : Cfg d 1, ‖tailVirtualMapES A K
          (boundaryFamilyFiber (D := D) y j)‖ ^ 2 := by
      simp only [Fintype.sum_prod_type, EuclideanSpace.norm_sq_eq]
      rw [Finset.sum_comm]
      rfl
    _ ≤ ∑ j : Cfg d 1,
        (‖tailVirtualMapES A K‖ * ‖boundaryFamilyFiber (D := D) y j‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
          (ContinuousLinearMap.le_opNorm _ _)
    _ = ‖tailVirtualMapES A K‖ ^ 2 *
        ∑ sp : Cfg d 1 × (Fin D × Fin D), ‖y sp‖ ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_pow, EuclideanSpace.norm_sq_eq]
      simp only [boundaryFamilyFiber, Finset.mul_sum]

/-- The centered virtual residual in the tail-after-left overlap orientation. -/
noncomputable def c3CenteredVirtualResidualES [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    BoundaryFamilySpace (D := D) (Cfg d 1) →L[ℂ]
      BoundaryFamilySpace (D := D) (Cfg d K) :=
  let Kinf := Matrix.gramReshuffle
    (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  let Kinftail := boundaryFiberwiseMap (D := D) (Cfg d K) Kinf
  let Kinfleft := boundaryFiberwiseMap (D := D) (Cfg d 1) Kinf
  let Iinf := Ring.inverse Kinf
  (tailBoundaryMapES A K (l + 1)).adjoint.comp
      (leftBoundaryMapES A (K + l) 1) -
    Kinftail.comp ((tailVirtualMapES A K).comp
      (Iinf.comp ((leftVirtualMapES A 1).adjoint.comp Kinfleft)))

/-- The centered overlap residual factors exactly through the length-\(l\) Gram
error on the common direct sum. -/
theorem c3_centeredVirtualResidualES_eq_overlapFactors [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    c3CenteredVirtualResidualES A K l ρ hρ =
      (c3LeftOverlapFactorES A K).adjoint.comp
        ((boundaryFiberwiseMap (D := D) (Cfg d K × Cfg d 1)
          (groundSpaceGram A l - Kinf)).comp
            (c3RightOverlapFactorES A K)) := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  simp only [c3CenteredVirtualResidualES]
  rw [inner_c3_centeredVirtualResidual_eq_gramError A K l ρ hρ x y]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,
    inner_boundaryFiberwiseMap]
  simp only [boundaryFamilyFiber_eq_frobeniusEquivEuclidean,
    boundaryFamilyEquiv_c3LeftOverlapFactorES_apply,
    boundaryFamilyEquiv_c3RightOverlapFactorES_apply,
    Fintype.sum_prod_type]

/-- Operator-norm bound for the exact centered overlap factorization. -/
theorem c3_centeredVirtualResidualES_norm_le [NeZero D]
    (A : MPSTensor d D) (K l : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    let Kinf := Matrix.gramReshuffle
      (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
    ‖c3CenteredVirtualResidualES A K l ρ hρ‖ ≤
      ‖leftVirtualMapES A 1‖ * ‖groundSpaceGram A l - Kinf‖ *
        ‖tailVirtualMapES A K‖ := by
  dsimp only
  rw [c3_centeredVirtualResidualES_eq_overlapFactors A K l ρ hρ]
  calc
    _ ≤ ‖(c3LeftOverlapFactorES A K).adjoint‖ *
        ‖boundaryFiberwiseMap (D := D) (Cfg d K × Cfg d 1)
          (groundSpaceGram A l -
            Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos)))‖ *
          ‖c3RightOverlapFactorES A K‖ := by
      calc
        _ ≤ ‖(c3LeftOverlapFactorES A K).adjoint‖ *
            ‖(boundaryFiberwiseMap (D := D) (Cfg d K × Cfg d 1)
              (groundSpaceGram A l - Matrix.gramReshuffle
                (fixedPointProj ρ (ne_of_gt hρ.trace_pos)))).comp
                (c3RightOverlapFactorES A K)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖(c3LeftOverlapFactorES A K).adjoint‖ *
            (‖boundaryFiberwiseMap (D := D) (Cfg d K × Cfg d 1)
              (groundSpaceGram A l - Matrix.gramReshuffle
                (fixedPointProj ρ (ne_of_gt hρ.trace_pos)))‖ *
              ‖c3RightOverlapFactorES A K‖) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
        _ = _ := by ring
    _ = ‖c3LeftOverlapFactorES A K‖ *
        ‖boundaryFiberwiseMap (D := D) (Cfg d K × Cfg d 1)
          (groundSpaceGram A l -
            Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos)))‖ *
          ‖c3RightOverlapFactorES A K‖ := by
      rw [LinearIsometryEquiv.norm_map
        (ContinuousLinearMap.adjoint (𝕜 := ℂ))]
    _ ≤ ‖leftVirtualMapES A 1‖ *
        ‖groundSpaceGram A l -
          Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos))‖ *
          ‖tailVirtualMapES A K‖ := by
      gcongr
      · exact c3LeftOverlapFactorES_norm_le A K
      · exact norm_boundaryFiberwiseMap_le _ _
      · exact c3RightOverlapFactorES_norm_le A K

/-- For a primitive MPS tensor with a positive-definite fixed point, the
squared norm of the centered overlap residual decays geometrically in the
overlap length, uniformly in the prefix length.  The prefactor retains the
explicit dimension-cubed conversion from the Gram convergence estimate. -/
theorem IsPrimitiveMPS.c3_centeredVirtualResidualES_norm_sq_le_geometric
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧ ∀ K l : ℕ, 1 ≤ l →
      ‖c3CenteredVirtualResidualES A K l ρ hρ‖ ^ 2 ≤
        (D : ℝ) ^ 3 * (C * r ^ l) ^ 2 := by
  obtain ⟨C_G, r, hC_G, hr_pos, hr_lt_one, hGram⟩ :=
    hP.groundSpaceGram_sub_fixedPointProj_norm_sq_le_geometric
  obtain ⟨C_T, hC_T, hTail⟩ := hP.tailVirtualMapES_norm_uniform
  refine ⟨C_G * C_T * (‖leftVirtualMapES A 1‖ + 1), r, by positivity,
    hr_pos, hr_lt_one, ?_⟩
  intro K l hl
  let Kinf := Matrix.gramReshuffle
    (fixedPointProj ρ (ne_of_gt hρ.trace_pos))
  have hCenter : ‖c3CenteredVirtualResidualES A K l ρ hρ‖ ≤
      ‖leftVirtualMapES A 1‖ * ‖groundSpaceGram A l - Kinf‖ *
        ‖tailVirtualMapES A K‖ := by
    simpa only [Kinf] using c3_centeredVirtualResidualES_norm_le A K l ρ hρ
  have hGram' : ‖groundSpaceGram A l - Kinf‖ ^ 2 ≤
      (D : ℝ) ^ 3 * (C_G * r ^ l) ^ 2 := by
    simpa only [Kinf] using hGram l hl
  have hLeft : ‖leftVirtualMapES A 1‖ ^ 2 ≤
      (‖leftVirtualMapES A 1‖ + 1) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _)
      (by positivity : 0 ≤ ‖leftVirtualMapES A 1‖ + 1)).mpr (by linarith)
  have hTail' : ‖tailVirtualMapES A K‖ ^ 2 ≤ C_T ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) hC_T.le).mpr (hTail K)
  calc
    ‖c3CenteredVirtualResidualES A K l ρ hρ‖ ^ 2 ≤
        (‖leftVirtualMapES A 1‖ * ‖groundSpaceGram A l - Kinf‖ *
          ‖tailVirtualMapES A K‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hCenter
    _ = ‖leftVirtualMapES A 1‖ ^ 2 *
        ‖groundSpaceGram A l - Kinf‖ ^ 2 * ‖tailVirtualMapES A K‖ ^ 2 := by ring
    _ ≤ (‖leftVirtualMapES A 1‖ + 1) ^ 2 *
        ((D : ℝ) ^ 3 * (C_G * r ^ l) ^ 2) * C_T ^ 2 := by
      gcongr
    _ = (D : ℝ) ^ 3 *
        (C_G * C_T * (‖leftVirtualMapES A 1‖ + 1) * r ^ l) ^ 2 := by ring

end MPSTensor
