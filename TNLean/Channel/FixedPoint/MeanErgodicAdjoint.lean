/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.MeanErgodicProjection
import TNLean.Channel.Schwarz.TwoPositive

/-!
# Trace adjoints of mean-ergodic projections

This module identifies the trace-pairing adjoint of a finite-dimensional
mean-ergodic projection.  Its range is the fixed-point space of the adjoint
endomorphism.  For a positive trace-preserving matrix endomorphism, this
adjoint projection is a positive unital retraction.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.3 and
  Equation (6.14); local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--269.
* M. Wolf, Theorem 6.14, proof; local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1488--1492.
-/

open scoped Matrix Matrix.Norms.Frobenius

variable {D : ℕ}

/-- The trace-pairing adjoint of the mean-ergodic projection of `T`.

This is the projection `P*` used in the proof of Wolf Theorem 6.14
(see Equation 6.14 and lines 1488-1492 of the local source)
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`.

The explicit definition as a named function avoids typeclass instance diamonds
in downstream modules that import additional matrix instances
(e.g., `Mathlib.Analysis.Matrix.Order`). -/
noncomputable def LinearMap.HasBoundedOrbits.traceAdjointMeanErgodicProjection
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hb : T.HasBoundedOrbits) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  Matrix.traceAdjointMap (LinearMap.meanErgodicProjection T hb)

/-- A matrix endomorphism is trace-preserving if and only if its trace-pairing
adjoint fixes the identity.

Source: Wolf, Chapter 3 trace-pairing duality and Proposition 6.3; local
sources `Notes/WolfNoteTexSource/ch03_positive_not_completely.tex`, lines
723--737, and `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines
226--256. -/
theorem isTracePreservingMap_iff_traceAdjointMap_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} :
    IsTracePreservingMap T ↔ Matrix.traceAdjointMap T 1 = 1 := by
  constructor
  · intro hTP
    refine sub_eq_zero.mp ((Matrix.trace_mul_right_eq_zero_iff
      (M := Matrix.traceAdjointMap T 1 - 1)).1 ?_)
    intro X
    simp only [Matrix.sub_mul, Matrix.trace_sub,
      Matrix.trace_traceAdjointMap_mul, one_mul]
    exact sub_eq_zero.mpr (hTP X)
  · intro hOne X
    calc
      Matrix.trace (T X) = Matrix.trace (1 * T X) := by simp
      _ = Matrix.trace (Matrix.traceAdjointMap T 1 * X) :=
        (Matrix.trace_traceAdjointMap_mul T 1 X).symm
      _ = Matrix.trace X := by rw [hOne]; simp

/-- The trace adjoint of the mean-ergodic projection fixes exactly the fixed
points of the trace adjoint of the original endomorphism.

The proof uses the complementary decomposition
\(X - P(X) \in \operatorname{range}(T - \mathrm{id})\).  A fixed point of
\(T^*\) annihilates this range under the trace pairing, so it is fixed by
\(P^*\).  This avoids any bounded-orbit or spectral hypothesis on \(T^*\).

Source: Wolf, Proposition 6.3 and Equation (6.14), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--269; this is
the adjoint projection used in the proof of Theorem 6.14, lines 1488--1492. -/
theorem LinearMap.HasBoundedOrbits.traceAdjointMap_meanErgodicProjection_apply_eq_self_iff
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hbounded : T.HasBoundedOrbits) (Y : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.traceAdjointMap (LinearMap.meanErgodicProjection T hbounded) Y = Y ↔
      Matrix.traceAdjointMap T Y = Y := by
  let P := LinearMap.meanErgodicProjection T hbounded
  constructor
  · intro hPfixed
    refine sub_eq_zero.mp ((Matrix.trace_mul_right_eq_zero_iff
      (M := Matrix.traceAdjointMap T Y - Y)).1 ?_)
    intro X
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_traceAdjointMap_mul]
    have hpairTX := Matrix.trace_traceAdjointMap_mul P Y (T X)
    change Matrix.trace (Matrix.traceAdjointMap P Y * T X) =
      Matrix.trace (Y * P (T X)) at hpairTX
    rw [hPfixed] at hpairTX
    have hpairX := Matrix.trace_traceAdjointMap_mul P Y X
    change Matrix.trace (Matrix.traceAdjointMap P Y * X) =
      Matrix.trace (Y * P X) at hpairX
    rw [hPfixed] at hpairX
    have hPT := congrArg
      (fun F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ ↦ F X)
      hbounded.meanErgodicProjection_comp
    change P (T X) = P X at hPT
    rw [hPT] at hpairTX
    exact sub_eq_zero.mpr (hpairTX.trans hpairX.symm)
  · intro hfixed
    refine sub_eq_zero.mp ((Matrix.trace_mul_right_eq_zero_iff
      (M := Matrix.traceAdjointMap P Y - Y)).1 ?_)
    intro X
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_traceAdjointMap_mul]
    have hrem : X - P X ∈ LinearMap.range (T - 1) := by
      change X - LinearMap.meanErgodicProjection T hbounded X ∈
        LinearMap.range (T - 1)
      exact Submodule.sub_projection_mem
        hbounded.isCompl_ker_sub_one_range_sub_one X
    obtain ⟨Z, hZ⟩ := hrem
    have hpair := Matrix.trace_traceAdjointMap_mul T Y Z
    rw [hfixed] at hpair
    have hzero : Matrix.trace (Y * (X - P X)) = 0 := by
      rw [← hZ]
      simp only [LinearMap.sub_apply, Module.End.one_apply, Matrix.mul_sub,
        Matrix.trace_sub]
      exact sub_eq_zero.mpr hpair.symm
    rw [Matrix.mul_sub, Matrix.trace_sub] at hzero
    exact sub_eq_zero.mpr (sub_eq_zero.mp hzero).symm

/-- The trace adjoint of a mean-ergodic projection is idempotent.

Source: Wolf, Proposition 6.3 and Equation (6.14), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--269; this is
the adjoint projection used in the proof of Theorem 6.14, lines 1488--1492. -/
theorem LinearMap.HasBoundedOrbits.traceAdjointMap_meanErgodicProjection_apply_self
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hbounded : T.HasBoundedOrbits) (Y : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.traceAdjointMap (LinearMap.meanErgodicProjection T hbounded)
        (Matrix.traceAdjointMap (LinearMap.meanErgodicProjection T hbounded) Y) =
      Matrix.traceAdjointMap (LinearMap.meanErgodicProjection T hbounded) Y := by
  let P := LinearMap.meanErgodicProjection T hbounded
  refine sub_eq_zero.mp ((Matrix.trace_mul_right_eq_zero_iff
    (M := Matrix.traceAdjointMap P (Matrix.traceAdjointMap P Y) -
      Matrix.traceAdjointMap P Y)).1 ?_)
  intro X
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_traceAdjointMap_mul,
    Matrix.trace_traceAdjointMap_mul]
  rw [Matrix.trace_traceAdjointMap_mul]
  rw [show P (P X) = P X from
    hbounded.meanErgodicProjection_apply_meanErgodicProjection X]
  exact sub_self _

/-- The range of the trace adjoint of a mean-ergodic projection is exactly the
fixed-point space of the trace adjoint of the original endomorphism.

Source: Wolf, Proposition 6.3 and Equation (6.14), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--269; this is
the adjoint projection used in the proof of Theorem 6.14, lines 1488--1492. -/
@[simp]
theorem LinearMap.HasBoundedOrbits.range_traceAdjointMap_meanErgodicProjection
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hbounded : T.HasBoundedOrbits) :
    LinearMap.range
        (Matrix.traceAdjointMap (LinearMap.meanErgodicProjection T hbounded)) =
      LinearMap.ker (Matrix.traceAdjointMap T - 1) := by
  ext Y
  constructor
  · rintro ⟨Z, rfl⟩
    rw [LinearMap.mem_ker]
    apply sub_eq_zero.mpr
    simpa only [Module.End.one_apply] using
      (hbounded.traceAdjointMap_meanErgodicProjection_apply_eq_self_iff
        (Matrix.traceAdjointMap (LinearMap.meanErgodicProjection T hbounded) Z)).1
        (hbounded.traceAdjointMap_meanErgodicProjection_apply_self Z)
  · intro hY
    rw [LinearMap.mem_ker] at hY
    have hfixed : Matrix.traceAdjointMap T Y = Y := by
      simpa only [LinearMap.sub_apply, Module.End.one_apply] using sub_eq_zero.mp hY
    refine ⟨Y, ?_⟩
    exact
      (hbounded.traceAdjointMap_meanErgodicProjection_apply_eq_self_iff Y).2 hfixed

/-- For a positive trace-preserving matrix endomorphism, the trace adjoint of
the mean-ergodic projection is a positive unital idempotent retraction onto the
fixed-point space of the adjoint endomorphism.

Source: Wolf, Proposition 6.3 and Equation (6.14), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--269; this is
the positive unital adjoint projection used in the proof of Theorem 6.14,
lines 1488--1492. -/
theorem IsPositiveMap.traceAdjoint_meanErgodicProjection_isPositiveUnitalRetraction
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    let Pstar := Matrix.traceAdjointMap
      (LinearMap.meanErgodicProjection T (hT.hasBoundedOrbits_of_tracePreserving hTP))
    IsPositiveMap Pstar ∧
      Pstar 1 = 1 ∧
      (∀ Y, Pstar (Pstar Y) = Pstar Y) ∧
      LinearMap.range Pstar = LinearMap.ker (Matrix.traceAdjointMap T - 1) ∧
      (∀ Y, Pstar Y = Y ↔ Matrix.traceAdjointMap T Y = Y) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hT.meanErgodicProjection_isPositiveMap
      (hT.hasBoundedOrbits_of_tracePreserving hTP)).traceAdjointMap
  · exact isTracePreservingMap_iff_traceAdjointMap_one.mp
      (hTP.meanErgodicProjection_isTracePreservingMap
        (hT.hasBoundedOrbits_of_tracePreserving hTP))
  · intro Y
    exact (hT.hasBoundedOrbits_of_tracePreserving hTP)
      |>.traceAdjointMap_meanErgodicProjection_apply_self Y
  · exact (hT.hasBoundedOrbits_of_tracePreserving hTP)
      |>.range_traceAdjointMap_meanErgodicProjection
  · intro Y
    exact (hT.hasBoundedOrbits_of_tracePreserving hTP)
      |>.traceAdjointMap_meanErgodicProjection_apply_eq_self_iff Y
