/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.IdempotentEndomorphism
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# A generic angle block for two orthogonal projections

This file gives the local two-dimensional block used in the two-projection
lemma invoked in arXiv:1703.09188, Proposition IV.5 (`prop:continuity-index`),
lines 756–764. It does not assume that the projections commute.

**Local fix (projector label):** Source line 762 repeats `P` for the second projector, where the
surrounding argument requires `Q`. This typographical correction is documented
in `docs/paper-gaps/1703_two_projection_projector_typo.tex`.
-/

open scoped InnerProductSpace

namespace LinearMap.IsSymmetricProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The compression of `Q` to the range of the symmetric projection `P`. -/
def rangeCompression {P Q : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection) :
    P.range →ₗ[ℂ] P.range :=
  (P.comp Q).restrict fun x hx ↦ by
    rw [LinearMap.mem_range]
    exact ⟨P (Q x), by
      exact LinearMap.IsIdempotentElem.apply_apply hP.isIdempotentElem (Q x)⟩

/-- The compression of a symmetric projection is symmetric on `range P`.

This is the compression used in the two-projection argument of
arXiv:1703.09188, Proposition IV.5 (`prop:continuity-index`),
`Papers/1703.09188/paper_v2.tex`, lines 756–764.

**Local fix (projector label):** Source line 762 repeats `P` for the second
projector, where the surrounding argument requires `Q`; see
`docs/paper-gaps/1703_two_projection_projector_typo.tex`. -/
theorem rangeCompression_isSymmetric {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection) :
    (rangeCompression hP (Q := Q)).IsSymmetric := by
  intro x y
  change ⟪(P (Q x) : E), (y : E)⟫_ℂ = ⟪(x : E), (P (Q y) : E)⟫_ℂ
  have hx : P (x : E) = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff hP.isIdempotentElem).mp x.property
  have hy : P (y : E) = y :=
    (LinearMap.IsIdempotentElem.mem_range_iff hP.isIdempotentElem).mp y.property
  rw [hP.isSymmetric, hQ.isSymmetric, hy]
  exact ((hP.isSymmetric x (Q y)).symm.trans (by rw [hx])).symm

/-- The defect vector \(Qx-μx\).

When `x` satisfies the compression-eigenvector hypotheses of
`angleDefect_block`, this vector is orthogonal to `x` and lies in the kernel of
`P`. -/
def angleDefect (Q : E →ₗ[ℂ] E) (μ : ℝ) (x : E) : E :=
  Q x - (μ : ℂ) • x

/-- Exact formulas for the possibly degenerate angle block determined by a unit
compression eigenvector.

**Local fix (projector label):** Source line 762 repeats `P` for the second projector; the
surrounding argument requires `Q`. See
`docs/paper-gaps/1703_two_projection_projector_typo.tex`.

Writing \(d=Qx-μx\), the conclusions include
\(Pd=0\), \(Qx=μx+d\),
\(Qd=μ(1-μ)x+(1-μ)d\), \(\langle x,d\rangle=0\), and
\(\lVert d\rVert^2=μ(1-μ)\). No strict endpoint bound or nonzero claim is made
here; `exists_orthonormal_angle_block` adds \(0<μ<1\) before normalizing \(d\).
-/
theorem angleDefect_block {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    {μ : ℝ} {x : E}
    (hxP : P x = x) (hxnorm : ‖x‖ = 1) (hxEig : P (Q x) = (μ : ℂ) • x) :
    P (angleDefect Q μ x) = 0 ∧
      Q x = (μ : ℂ) • x + angleDefect Q μ x ∧
      Q (angleDefect Q μ x) =
        ((μ * (1 - μ) : ℝ) : ℂ) • x + ((1 - μ : ℝ) : ℂ) • angleDefect Q μ x ∧
      ⟪x, angleDefect Q μ x⟫_ℂ = 0 ∧
      ‖angleDefect Q μ x‖ ^ 2 = μ * (1 - μ) := by
  have hQidem : Q (Q x) = Q x := LinearMap.IsIdempotentElem.apply_apply hQ.isIdempotentElem x
  have hxx : ⟪x, x⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hxnorm]
    norm_num
  have hxQx : ⟪x, Q x⟫_ℂ = μ := by
    calc
      ⟪x, Q x⟫_ℂ = ⟪P x, Q x⟫_ℂ := by rw [hxP]
      _ = ⟪x, P (Q x)⟫_ℂ := hP.isSymmetric x (Q x)
      _ = μ := by rw [hxEig, inner_smul_right, hxx, mul_one]
  have hQxQx : ⟪Q x, Q x⟫_ℂ = μ := by
    calc
      ⟪Q x, Q x⟫_ℂ = ⟪x, Q (Q x)⟫_ℂ := hQ.isSymmetric x (Q x)
      _ = μ := by rw [hQidem, hxQx]
  constructor
  · simp only [angleDefect, map_sub, map_smul, hxEig, hxP]
    norm_num
  constructor
  · simp [angleDefect]
  constructor
  · simp only [angleDefect, map_sub, map_smul, hQidem]
    rw [show Q x = (μ : ℂ) • x + angleDefect Q μ x by simp [angleDefect]]
    module
  constructor
  · rw [angleDefect, inner_sub_right, inner_smul_right, hxQx, hxx]
    norm_num
  · have hQxx : ⟪Q x, x⟫_ℂ = μ := by
      rw [← inner_conj_symm, hxQx]
      exact RCLike.conj_ofReal μ
    have hxDefect : ⟪x, angleDefect Q μ x⟫_ℂ = 0 := by
      rw [angleDefect, inner_sub_right, inner_smul_right, hxQx, hxx]
      norm_num
    have hQxDefect : ⟪Q x, angleDefect Q μ x⟫_ℂ = μ * (1 - μ) := by
      rw [angleDefect, inner_sub_right, inner_smul_right, hQxQx, hQxx]
      ring
    calc
      ‖angleDefect Q μ x‖ ^ 2 =
          RCLike.re (⟪angleDefect Q μ x, angleDefect Q μ x⟫_ℂ) :=
        @norm_sq_eq_re_inner ℂ E _ _ _ (angleDefect Q μ x)
      _ = RCLike.re (⟪Q x, angleDefect Q μ x⟫_ℂ -
          (starRingEnd ℂ) (μ : ℂ) * ⟪x, angleDefect Q μ x⟫_ℂ) := by
        rw [angleDefect, inner_sub_left, inner_smul_left]
      _ = μ * (1 - μ) := by rw [hQxDefect, hxDefect]; norm_num

/-- Normalized form of `angleDefect_block`.

**Local fix (projector label):** The second projector in arXiv:1703.09188, line 762 is `Q`, not
the repeated `P`; see `docs/paper-gaps/1703_two_projection_projector_typo.tex`.

The vectors `x,w` are orthonormal; on their two-dimensional span, `P` acts as
the projection onto `x`, while `Q`
has its standard angle-block action with off-diagonal coefficient
\(\sqrt{μ(1-μ)}\). -/
theorem exists_orthonormal_angle_block {P Q : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) {x : E}
    (hxP : P x = x) (hxnorm : ‖x‖ = 1) (hxEig : P (Q x) = (μ : ℂ) • x) :
    ∃ w : E,
      P w = 0 ∧ ‖w‖ = 1 ∧ ⟪x, w⟫_ℂ = 0 ∧
      Q x = (μ : ℂ) • x + (Real.sqrt (μ * (1 - μ)) : ℂ) • w ∧
      Q w = (Real.sqrt (μ * (1 - μ)) : ℂ) • x + ((1 - μ : ℝ) : ℂ) • w := by
  let d := angleDefect Q μ x
  let a := Real.sqrt (μ * (1 - μ))
  have hdpos : 0 < μ * (1 - μ) := mul_pos hμ0 (sub_pos.mpr hμ1)
  have hapos : 0 < a := Real.sqrt_pos.2 hdpos
  have ha0 : a ≠ 0 := ne_of_gt hapos
  have haSq : a ^ 2 = μ * (1 - μ) := Real.sq_sqrt hdpos.le
  obtain ⟨hdP, hxQ, hQd, hxd, hdNormSq⟩ :=
    angleDefect_block hP hQ hxP hxnorm hxEig
  have hdNorm : ‖d‖ = a := by
    have hda : ‖d‖ ^ 2 = a ^ 2 := by simpa [d, haSq] using hdNormSq
    nlinarith [norm_nonneg d]
  refine ⟨((a⁻¹ : ℝ) : ℂ) • d, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_smul, hdP, smul_zero]
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hapos,
      hdNorm]
    exact inv_mul_cancel₀ ha0
  · rw [inner_smul_right, hxd, mul_zero]
  · rw [hxQ]
    change (μ : ℂ) • x + d = (μ : ℂ) • x + (a : ℂ) • ((a⁻¹ : ℝ) : ℂ) • d
    rw [smul_smul]
    simp [ha0]
  · rw [map_smul, hQd]
    change ((a⁻¹ : ℝ) : ℂ) •
        (((μ * (1 - μ) : ℝ) : ℂ) • x + ((1 - μ : ℝ) : ℂ) • d) =
      (a : ℂ) • x + ((1 - μ : ℝ) : ℂ) • ((a⁻¹ : ℝ) : ℂ) • d
    rw [smul_add, smul_smul, smul_smul, smul_smul]
    congr 1
    · congr 1
      norm_cast
      calc
        a⁻¹ * (μ * (1 - μ)) = a⁻¹ * a ^ 2 := by rw [haSq]
        _ = a⁻¹ * (a * a) := by rw [pow_two]
        _ = a := by rw [inv_mul_cancel_left₀ ha0]
    · rw [mul_comm]

end LinearMap.IsSymmetricProjection
