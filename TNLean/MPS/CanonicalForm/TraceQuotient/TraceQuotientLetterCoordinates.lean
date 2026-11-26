/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Topology.ContinuousIdempotentFrames
import TNLean.MPS.CanonicalForm.TraceQuotient.TraceQuotientAlgebraRecovery
import TNLean.MPS.CanonicalForm.TraceQuotient.FramedLeftIdealRealization
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Instances.Matrix

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

## Continuity of reconstructed letter coordinates

The Gram left inverse of an injective fixed trace section varies continuously. Hence the
coordinates of all physical letters vary continuously with the two-site trace form. This is
an auxiliary finite-dimensional step towards reconstruction in arXiv:1010.3732,
Section II.F.2, lines 953–993 of the local source; no continuity of a minimal tensor or
physical-gap implication is asserted.

## Normalized trace-quotient letters

An injective minimal tensor and a normalized coefficient identification imply that the
corresponding physical trace section is injective. Its Gram coordinates recover the physical
letters with the same normalization. This is an algebraic auxiliary step towards the
reconstruction discussed in arXiv:1010.3732, Section II.F.2, lines 953–993 of the local source.
The coefficient identification is used pointwise and is not assumed continuous; no
physical-gap implication is asserted.
-/

open MPTensor

section

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

end

section

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix Matrix.Norms.L2Operator

namespace Matrix

/-- Reconstructed letter coordinates are continuous wherever the fixed section is injective. -/
theorem continuousOn_traceQuotientLetterCoordinates
    {T : Type*} [TopologicalSpace T] {d r : ℕ} (S : Set T)
    (G : T → Matrix (Fin d) (Fin d) ℂ) (hG : ContinuousOn G S)
    (F : Matrix (Fin d) (Fin r) ℂ)
    (hInj : ∀ t ∈ S, Function.Injective (G t * F).mulVec) :
    ContinuousOn (fun t => traceQuotientLetterCoordinates (G t) F) S := by
  rw [continuousOn_iff_continuous_domRestrict] at hG ⊢
  have hC : Continuous fun t : S => G t * F := hG.matrix_mul continuous_const
  exact (continuous_gramLeftInverse _ hC (fun t => hInj t t.property)).matrix_mul hG

end Matrix

end

section

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix

namespace Matrix

/-- A normalized minimal coefficient identification derives section injectivity and
reconstructs the normalized physical letters in that section. -/
theorem traceQuotientLetters_of_normalized_linearEquiv {d r D : ℕ}
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (G : Matrix (Fin d) (Fin d) ℂ) (F : Matrix (Fin d) (Fin r) ℂ) (α₂ κ : ℂ)
    (hα₂ : α₂ ≠ 0) (hκ : κ ≠ 0)
    (hG : ∀ j i, G j i = α₂ * Matrix.trace (A i * A j))
    (hE : ∀ x, E x = κ • Fintype.linearCombination ℂ A (F *ᵥ x)) :
    Function.Injective (G * F).mulVec ∧
      ∀ i, E (traceQuotientLetterCoordinates G F *ᵥ Pi.single i 1) = κ • A i := by
  have hPair := traceQuotientSection_pair A G F α₂ hG
  have hTrace : Function.Injective (MPSTensor.traceMulRightPi A) :=
    LinearMap.ker_eq_bot.mp (MPSTensor.traceMulRightPi_ker_eq_bot hA)
  have hInj : Function.Injective (G * F).mulVec := by
    intro x y hxy
    apply E.injective
    rw [hE, hE]
    apply congrArg (κ • ·)
    apply hTrace
    exact smul_right_injective _ hα₂ ((hPair x).symm.trans (hxy.trans (hPair y)))
  let Q := E.trans (LinearEquiv.smulOfNeZero ℂ
    (Matrix (Fin D) (Fin D) ℂ) κ⁻¹ (inv_ne_zero hκ))
  have hQ : ∀ x, Q x = Fintype.linearCombination ℂ A (F *ᵥ x) := by
    intro x
    change κ⁻¹ • E x = _
    rw [hE, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  have hRecover := traceQuotientLetterCoordinates_recover A Q G F α₂ hG hInj
    (fun x => by rw [hQ]; exact hPair x)
  refine ⟨hInj, fun i => ?_⟩
  rw [hE]
  exact congrArg (κ • ·) ((hQ _).symm.trans (hRecover i))

end Matrix

end
