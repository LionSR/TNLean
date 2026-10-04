/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixGramLeftInverse
import TNLean.MPS.Structure.TraceQuotientAlgebraRecovery
import TNLean.MPS.Structure.FramedLeftIdealRealization

/-!
# Reconstruction of physical letters from trace-quotient coordinates

Inverting a full-rank section of the two-site trace form recovers coordinates for every
physical letter. A pointwise minimal coefficient identification sends these coordinates to the
minimal tensor letters. A framed principal-left-ideal representation therefore produces a
tensor gauge equivalent to the normalized minimal tensor.

These are auxiliary finite-data consequences towards the reconstruction discussed in
arXiv:1010.3732, Section II.F.2, lines 953–993 of the local source. The frame is supplied, and
no continuous pointwise minimal tensor is assumed. The two-site trace form is complex bilinear;
only the section Gram matrix is positive. No conclusion concerning all positive-length vectors
of a noninjective raw tensor follows solely from its two- and three-site trace data.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix BigOperators

namespace Matrix

/-- Coordinates of the original physical letters in a fixed trace section. -/
noncomputable def traceQuotientLetterCoordinates {d r : ℕ}
    (G : Matrix (Fin d) (Fin d) ℂ) (F : Matrix (Fin d) (Fin r) ℂ) :
    Matrix (Fin r) (Fin d) ℂ :=
  ((G * F)ᴴ * (G * F))⁻¹ * (G * F)ᴴ * G

/-- The Gram left inverse of a physical trace section reconstructs each minimal tensor letter.
This is an auxiliary finite-data statement towards arXiv:1010.3732, Section II.F.2,
lines 953–993. Its pointwise bond identification is not assumed continuous. -/
theorem traceQuotientLetterCoordinates_recover {d r D : ℕ}
    (A : MPSTensor d D) (Q : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (G : Matrix (Fin d) (Fin d) ℂ) (F : Matrix (Fin d) (Fin r) ℂ) (α₂ : ℂ)
    (hG : ∀ j i, G j i = α₂ * Matrix.trace (A i * A j))
    (hInj : Function.Injective (G * F).mulVec)
    (hPair : ∀ x, (G * F) *ᵥ x = α₂ • MPSTensor.traceMulRightPi A (Q x)) :
    ∀ i, Q (traceQuotientLetterCoordinates G F *ᵥ Pi.single i 1) = A i := by
  intro i
  have hCol : G *ᵥ Pi.single i 1 = (G * F) *ᵥ Q.symm (A i) := by
    ext j
    simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply, hG, hPair,
      Q.apply_symm_apply,
      Pi.smul_apply, smul_eq_mul, MPSTensor.traceMulRightPi_apply]
  have hLeft := Matrix.gramLeftInverse_mul (G * F) hInj
  rw [traceQuotientLetterCoordinates, ← Matrix.mulVec_mulVec, hCol, Matrix.mulVec_mulVec, hLeft,
    Matrix.one_mulVec, Q.apply_symm_apply]

end Matrix

namespace MPSTensor

/-- Framed realization of the recovered quotient letters is gauge equivalent to the
normalized minimal tensor. The scalar κ is the normalization of its matrix-algebra
identification. For the two- and three-site quotient product it is α₃ / α₂.
This does not identify the longer vectors of a noninjective raw tensor. -/
theorem gaugeEquiv_traceQuotientLetters {d r D : ℕ} [NeZero D]
    (A : MPSTensor d D) (Q E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (hE : ∀ x y, E (μ x y) = E x * E y) (κ : ℂ) (hNorm : ∀ x, E x = κ • Q x)
    (G : Matrix (Fin d) (Fin d) ℂ) (F : Matrix (Fin d) (Fin r) ℂ) (α₂ : ℂ)
    (hG : ∀ j i, G j i = α₂ * Matrix.trace (A i * A j))
    (hInj : Function.Injective (G * F).mulVec)
    (hPair : ∀ x, (G * F) *ᵥ x = α₂ • MPSTensor.traceMulRightPi A (Q x))
    (p : Fin r → ℂ) (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (H : (Fin r → ℂ) →ₗ[ℂ] (Fin D → ℂ)) (hHJ : H.comp J = LinearMap.id)
    (hRange : LinearMap.range J = LinearMap.range (μ.flip p)) :
    GaugeEquiv (κ • A) (fun i => Matrix.leftIdealFrameAction μ J H
      (Matrix.traceQuotientLetterCoordinates G F *ᵥ Pi.single i 1)) := by
  obtain ⟨X, hX⟩ := Matrix.exists_inner_of_leftIdealFrame μ E hE p J H hHJ hRange
  refine ⟨X, fun i => ?_⟩
  change Matrix.leftIdealFrameAction μ J H
    (Matrix.traceQuotientLetterCoordinates G F *ᵥ Pi.single i 1) =
      (X : Matrix (Fin D) (Fin D) ℂ) * (κ • A i) *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  rw [hX, hNorm, Matrix.traceQuotientLetterCoordinates_recover A Q G F α₂ hG hInj hPair]

end MPSTensor
