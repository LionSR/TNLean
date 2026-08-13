/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.TwoProjectionAngleBlock
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Compression spectrum for the two-projection decomposition

This file begins Jordan's lemma for two orthogonal projections: it diagonalizes
the compression of the second projection to the range of the first and
classifies every compression eigenvector as a common one-dimensional block
(compression eigenvalue `0` or `1`) or a genuine two-dimensional angle block.

The construction is the first global step used in arXiv:1703.09188,
Proposition IV.5 (`prop:continuity-index`), lines 759–762.

**Local fix (projector label):** Source line 762 repeats `P` for the second
projector, where the surrounding argument requires `Q`; see
`docs/paper-gaps/1703_two_projection_projector_typo.tex`.
-/

open scoped InnerProductSpace

namespace LinearMap.IsSymmetricProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The ordered real eigenvalues of the compression of `Q` to `range P`.

This is the spectral parameter family used in the Jordan decomposition from
arXiv:1703.09188, Proposition IV.5, lines 759–762. -/
noncomputable def rangeCompressionEigenvalues {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    Fin (Module.finrank ℂ P.range) → ℝ :=
  (rangeCompression_isSymmetric hP hQ).eigenvalues rfl

/-- An orthonormal eigenbasis for the compression of `Q` to `range P`.

This is the basis from which the one- and two-dimensional blocks in the
`P`-range are obtained in arXiv:1703.09188, Proposition IV.5, lines 759–762. -/
noncomputable def rangeCompressionEigenbasis {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    OrthonormalBasis (Fin (Module.finrank ℂ P.range)) ℂ P.range :=
  (rangeCompression_isSymmetric hP hQ).eigenvectorBasis rfl

/-- The compression acts diagonally on `rangeCompressionEigenbasis`. -/
theorem rangeCompression_apply_eigenbasis {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (i : Fin (Module.finrank ℂ P.range)) :
    rangeCompression hP (Q := Q) (rangeCompressionEigenbasis hP hQ i) =
      (rangeCompressionEigenvalues hP hQ i : ℂ) •
        rangeCompressionEigenbasis hP hQ i := by
  exact (rangeCompression_isSymmetric hP hQ).apply_eigenvectorBasis rfl i

/-- The ambient first projection fixes every vector in the compression eigenbasis. -/
theorem rangeCompressionEigenbasis_apply_self {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (i : Fin (Module.finrank ℂ P.range)) :
    P (rangeCompressionEigenbasis hP hQ i : E) =
      (rangeCompressionEigenbasis hP hQ i : E) := by
  exact (LinearMap.IsIdempotentElem.mem_range_iff hP.isIdempotentElem).mp
    (rangeCompressionEigenbasis hP hQ i).property

/-- The ambient compression equation for a vector in `rangeCompressionEigenbasis`. -/
theorem rangeCompressionEigenbasis_apply_compression {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (i : Fin (Module.finrank ℂ P.range)) :
    P (Q (rangeCompressionEigenbasis hP hQ i : E)) =
      (rangeCompressionEigenvalues hP hQ i : ℂ) •
        (rangeCompressionEigenbasis hP hQ i : E) := by
  exact congr_arg Subtype.val (rangeCompression_apply_eigenbasis hP hQ i)

/-- Every eigenvalue of the compressed projection belongs to `[0,1]`.

These endpoint bounds separate the commuting one-dimensional summands from the
genuine angle blocks in arXiv:1703.09188, Proposition IV.5, lines 759–762. -/
theorem rangeCompressionEigenvalues_mem_unitInterval {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (i : Fin (Module.finrank ℂ P.range)) :
    rangeCompressionEigenvalues hP hQ i ∈ Set.Icc (0 : ℝ) 1 := by
  let x := rangeCompressionEigenbasis hP hQ i
  let μ := rangeCompressionEigenvalues hP hQ i
  have hxnorm : ‖(x : E)‖ = 1 := (rangeCompressionEigenbasis hP hQ).norm_eq_one i
  have hxP : P (x : E) = x := rangeCompressionEigenbasis_apply_self hP hQ i
  have hxEig : P (Q (x : E)) = (μ : ℂ) • (x : E) :=
    rangeCompressionEigenbasis_apply_compression hP hQ i
  obtain ⟨_, _, _, _, hnorm⟩ := angleDefect_block hP hQ hxP hxnorm hxEig
  change 0 ≤ μ ∧ μ ≤ 1
  constructor <;> nlinarith [sq_nonneg ‖angleDefect Q μ (x : E)‖]

/-- Compression eigenvectors at `0` and `1` give common one-dimensional
blocks; every other eigenvector gives the normalized two-dimensional angle
block from `exists_orthonormal_angle_block`.

This is the spectral classification used in the global Jordan decomposition
of arXiv:1703.09188, Proposition IV.5, lines 759–762. It does not yet include
the orthogonal complement of `range P` in the ambient orthogonal direct sum or
define the reduced projector used later in that proof. -/
theorem rangeCompressionEigenvalues_eq_zero_or_eq_one_or_exists_angle_block
    {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (i : Fin (Module.finrank ℂ P.range)) :
    let x : E := rangeCompressionEigenbasis hP hQ i
    let μ := rangeCompressionEigenvalues hP hQ i
    (μ = 0 ∧ Q x = 0) ∨ (μ = 1 ∧ Q x = x) ∨
      (0 < μ ∧ μ < 1 ∧ ∃ w : E,
        P w = 0 ∧ ‖w‖ = 1 ∧ ⟪x, w⟫_ℂ = 0 ∧
        Q x = (μ : ℂ) • x + (Real.sqrt (μ * (1 - μ)) : ℂ) • w ∧
        Q w = (Real.sqrt (μ * (1 - μ)) : ℂ) • x +
          ((1 - μ : ℝ) : ℂ) • w) := by
  let x : E := rangeCompressionEigenbasis hP hQ i
  let μ := rangeCompressionEigenvalues hP hQ i
  have hxnorm : ‖x‖ = 1 := (rangeCompressionEigenbasis hP hQ).norm_eq_one i
  have hxP : P x = x := rangeCompressionEigenbasis_apply_self hP hQ i
  have hxEig : P (Q x) = (μ : ℂ) • x :=
    rangeCompressionEigenbasis_apply_compression hP hQ i
  have hμ := rangeCompressionEigenvalues_mem_unitInterval hP hQ i
  rcases hμ with ⟨hμ0, hμ1⟩
  rcases eq_or_lt_of_le hμ0 with hμeq | hμpos
  · left
    refine ⟨hμeq.symm, ?_⟩
    obtain ⟨_, _, _, _, hnorm⟩ := angleDefect_block hP hQ hxP hxnorm hxEig
    have hdefect : angleDefect Q μ x = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (angleDefect Q μ x)]
    have hμzero : μ = 0 := hμeq.symm
    have hdefect0 : angleDefect Q 0 x = 0 := by simpa [hμzero] using hdefect
    calc
      Q x = (μ : ℂ) • x + angleDefect Q μ x := by simp [angleDefect]
      _ = 0 := by simp [hμzero, hdefect0]
  · rcases eq_or_lt_of_le hμ1 with hμeq | hμlt
    · right; left
      refine ⟨hμeq, ?_⟩
      obtain ⟨_, hxQ, _, _, hnorm⟩ := angleDefect_block hP hQ hxP hxnorm hxEig
      have hdefect : angleDefect Q μ x = 0 := by
        apply norm_eq_zero.mp
        nlinarith [norm_nonneg (angleDefect Q μ x)]
      have hμone : μ = 1 := hμeq
      have hdefect1 : angleDefect Q 1 x = 0 := by simpa [hμone] using hdefect
      calc
        Q x = (μ : ℂ) • x + angleDefect Q μ x := hxQ
        _ = x := by simp [hμone, hdefect1]
    · right; right
      exact ⟨hμpos, hμlt, exists_orthonormal_angle_block hP hQ hμpos hμlt hxP hxnorm hxEig⟩

end LinearMap.IsSymmetricProjection
