/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.TwoProjectionCompressionSpectrum
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Orthogonality of two-projection angle blocks

Distinct vectors in the chosen orthonormal eigenbasis of the compression of one orthogonal
projection to the range of another determine orthogonal defect blocks. The argument never
compares eigenvalues, so it applies without change inside repeated eigenspaces.

These are the cross-block orthogonality identities in the Jordan-lemma decomposition used in
arXiv:1703.09188, Proposition IV.5 (`prop:continuity-index`), lines 759–762.

**Local fix (projector label):** Source line 762 repeats `P` for the second projector, where the
surrounding argument requires `Q`; see `docs/paper-gaps/1703_two_projection_projector_typo.tex`.
-/

open scoped InnerProductSpace

namespace LinearMap.IsSymmetricProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

private abbrev CompressionIndex {P : E →ₗ[ℂ] E} := Fin (Module.finrank ℂ P.range)

/-- Every compression eigenvector is orthogonal to every angle defect. -/
theorem rangeCompressionEigenbasis_inner_angleDefect_eq_zero {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (i j : CompressionIndex (P := P)) :
    ⟪(rangeCompressionEigenbasis hP hQ i : E),
      angleDefect Q (rangeCompressionEigenvalues hP hQ j)
        (rangeCompressionEigenbasis hP hQ j : E)⟫_ℂ = 0 := by
  let x := fun k => (rangeCompressionEigenbasis hP hQ k : E)
  let μ := rangeCompressionEigenvalues hP hQ
  have hxiP : P (x i) = x i :=
    (LinearMap.IsIdempotentElem.mem_range_iff hP.isIdempotentElem).mp
      (rangeCompressionEigenbasis hP hQ i).property
  have hxjEig : P (Q (x j)) = (μ j : ℂ) • x j :=
    congr_arg Subtype.val (rangeCompression_apply_eigenbasis hP hQ j)
  rw [angleDefect, inner_sub_right, inner_smul_right]
  calc
    ⟪x i, Q (x j)⟫_ℂ - (μ j : ℂ) * ⟪x i, x j⟫_ℂ =
        ⟪P (x i), Q (x j)⟫_ℂ - (μ j : ℂ) * ⟪x i, x j⟫_ℂ := by rw [hxiP]
    _ = ⟪x i, P (Q (x j))⟫_ℂ - (μ j : ℂ) * ⟪x i, x j⟫_ℂ := by
      rw [hP.isSymmetric]
    _ = 0 := by rw [hxjEig, inner_smul_right]; exact sub_self _

/-- Every angle defect is orthogonal to every compression eigenvector. -/
theorem angleDefect_inner_rangeCompressionEigenbasis_eq_zero {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (i j : CompressionIndex (P := P)) :
    ⟪angleDefect Q (rangeCompressionEigenvalues hP hQ i)
        (rangeCompressionEigenbasis hP hQ i : E),
      (rangeCompressionEigenbasis hP hQ j : E)⟫_ℂ = 0 := by
  rw [inner_eq_zero_symm]
  exact rangeCompressionEigenbasis_inner_angleDefect_eq_zero hP hQ j i

/-- Exact pairing of two angle defects, before imposing distinctness of their basis indices. -/
theorem angleDefect_inner_angleDefect {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (i j : CompressionIndex (P := P)) :
    ⟪angleDefect Q (rangeCompressionEigenvalues hP hQ i)
        (rangeCompressionEigenbasis hP hQ i : E),
      angleDefect Q (rangeCompressionEigenvalues hP hQ j)
        (rangeCompressionEigenbasis hP hQ j : E)⟫_ℂ =
      (rangeCompressionEigenvalues hP hQ j *
        (1 - rangeCompressionEigenvalues hP hQ j) : ℂ) *
        ⟪(rangeCompressionEigenbasis hP hQ i : E),
          (rangeCompressionEigenbasis hP hQ j : E)⟫_ℂ := by
  let x := fun k => (rangeCompressionEigenbasis hP hQ k : E)
  let μ := rangeCompressionEigenvalues hP hQ
  have hxd : ⟪x i, angleDefect Q (μ j) (x j)⟫_ℂ = 0 :=
    rangeCompressionEigenbasis_inner_angleDefect_eq_zero hP hQ i j
  have hxjP : P (x j) = x j :=
    (LinearMap.IsIdempotentElem.mem_range_iff hP.isIdempotentElem).mp
      (rangeCompressionEigenbasis hP hQ j).property
  have hxjnorm : ‖x j‖ = 1 := (rangeCompressionEigenbasis hP hQ).norm_eq_one j
  have hxjEig : P (Q (x j)) = (μ j : ℂ) • x j :=
    congr_arg Subtype.val (rangeCompression_apply_eigenbasis hP hQ j)
  have hQdj := (angleDefect_block hP hQ hxjP hxjnorm hxjEig).2.2.1
  change ⟪Q (x i) - (μ i : ℂ) • x i, angleDefect Q (μ j) (x j)⟫_ℂ = _
  rw [inner_sub_left, inner_smul_left, hxd, mul_zero, sub_zero]
  rw [hQ.isSymmetric, hQdj, inner_add_right, inner_smul_right, inner_smul_right, hxd,
    mul_zero, add_zero]
  norm_cast

/-- Angle defects belonging to distinct compression-basis coordinates are orthogonal. This
includes distinct basis vectors with the same compression eigenvalue. -/
theorem angleDefect_inner_angleDefect_eq_zero {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    {i j : CompressionIndex (P := P)} (hij : i ≠ j) :
    ⟪angleDefect Q (rangeCompressionEigenvalues hP hQ i)
        (rangeCompressionEigenbasis hP hQ i : E),
      angleDefect Q (rangeCompressionEigenvalues hP hQ j)
        (rangeCompressionEigenbasis hP hQ j : E)⟫_ℂ = 0 := by
  rw [angleDefect_inner_angleDefect hP hQ i j]
  have hinner : ⟪(rangeCompressionEigenbasis hP hQ i : E),
      (rangeCompressionEigenbasis hP hQ j : E)⟫_ℂ = 0 :=
    (rangeCompressionEigenbasis hP hQ).inner_eq_zero hij
  rw [hinner, mul_zero]

/-- The span of a compression eigenvector and its unnormalized angle defect. -/
noncomputable def angleDefectBlock {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (i : CompressionIndex (P := P)) : Submodule ℂ E :=
  Submodule.span ℂ {(rangeCompressionEigenbasis hP hQ i : E),
    angleDefect Q (rangeCompressionEigenvalues hP hQ i)
      (rangeCompressionEigenbasis hP hQ i : E)}

/-- The defect block has dimension at most two, including at the degenerate endpoints. -/
theorem finrank_angleDefectBlock_le_two {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (i : CompressionIndex (P := P)) :
    Module.finrank ℂ (angleDefectBlock hP hQ i) ≤ 2 := by
  classical
  rw [angleDefectBlock]
  let s : Finset E := {(rangeCompressionEigenbasis hP hQ i : E),
    angleDefect Q (rangeCompressionEigenvalues hP hQ i)
      (rangeCompressionEigenbasis hP hQ i : E)}
  rw [show ({(rangeCompressionEigenbasis hP hQ i : E),
      angleDefect Q (rangeCompressionEigenvalues hP hQ i)
        (rangeCompressionEigenbasis hP hQ i : E)} : Set E) = (s : Set E) by simp [s]]
  exact (finrank_span_finset_le_card s).trans (Finset.card_insert_le _ _ |>.trans (by simp))

/-- Each defect block is invariant under the first projection. -/
theorem map_angleDefectBlock_le_P {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (i : CompressionIndex (P := P)) :
    Submodule.map P (angleDefectBlock hP hQ i) ≤ angleDefectBlock hP hQ i := by
  let x := (rangeCompressionEigenbasis hP hQ i : E)
  let μ := rangeCompressionEigenvalues hP hQ i
  have hxP : P x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff hP.isIdempotentElem).mp
      (rangeCompressionEigenbasis hP hQ i).property
  have hxnorm : ‖x‖ = 1 := (rangeCompressionEigenbasis hP hQ).norm_eq_one i
  have hxEig : P (Q x) = (μ : ℂ) • x :=
    congr_arg Subtype.val (rangeCompression_apply_eigenbasis hP hQ i)
  have hdP := (angleDefect_block hP hQ hxP hxnorm hxEig).1
  rw [angleDefectBlock, LinearMap.map_span_le]
  rintro y (rfl | rfl)
  · rw [hxP]
    exact Submodule.subset_span (by left; rfl)
  · rw [hdP]
    exact Submodule.zero_mem _

/-- Each defect block is invariant under the second projection. -/
theorem map_angleDefectBlock_le_Q {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (i : CompressionIndex (P := P)) :
    Submodule.map Q (angleDefectBlock hP hQ i) ≤ angleDefectBlock hP hQ i := by
  let x := (rangeCompressionEigenbasis hP hQ i : E)
  let μ := rangeCompressionEigenvalues hP hQ i
  let d := angleDefect Q μ x
  have hxP : P x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff hP.isIdempotentElem).mp
      (rangeCompressionEigenbasis hP hQ i).property
  have hxnorm : ‖x‖ = 1 := (rangeCompressionEigenbasis hP hQ).norm_eq_one i
  have hxEig : P (Q x) = (μ : ℂ) • x :=
    congr_arg Subtype.val (rangeCompression_apply_eigenbasis hP hQ i)
  obtain ⟨_, hxQ, hQd, _, _⟩ := angleDefect_block hP hQ hxP hxnorm hxEig
  rw [angleDefectBlock, LinearMap.map_span_le]
  rintro y (rfl | rfl)
  · rw [hxQ]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by left; rfl)))
      (Submodule.subset_span (by right; rfl))
  · rw [hQd]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by left; rfl)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by right; rfl)))

/-- Distinct compression-basis coordinates determine orthogonal defect blocks. In particular,
this remains true for repeated compression eigenvalues. -/
theorem angleDefectBlock_isOrtho {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    {i j : CompressionIndex (P := P)} (hij : i ≠ j) :
    angleDefectBlock hP hQ i ⟂ angleDefectBlock hP hQ j := by
  rw [angleDefectBlock, angleDefectBlock, Submodule.isOrtho_span]
  rintro u (rfl | rfl) v (rfl | rfl)
  · exact (rangeCompressionEigenbasis hP hQ).inner_eq_zero hij
  · exact rangeCompressionEigenbasis_inner_angleDefect_eq_zero hP hQ i j
  · exact angleDefect_inner_rangeCompressionEigenbasis_eq_zero hP hQ i j
  · exact angleDefect_inner_angleDefect_eq_zero hP hQ hij

end LinearMap.IsSymmetricProjection
