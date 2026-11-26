/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.GappedPath.ExactMPSGappedPhase
import TNLean.MPS.CanonicalForm.Correlation.WindowCorrelator
import QICLean.ManyBody.Hamiltonian.NegativeFrequency
import QICLean.Analysis.Norm.MatrixToEuclidean

/-!
# Normalized correlations depend only on the periodic MPS rays

Equality of the actual positive-length periodic lines preserves every
normalized expectation and connected window correlator. Mathlib's
singleton-span criterion gives a unit scalar, including when both vectors
vanish. There is no chosen normalization or tensor gauge.

Source: SPC11, arXiv:1010.3732, Section II.F, lines 929–953, where physical
states are rays and the minimal tensor representative may change.
-/

open scoped InnerProductSpace

namespace MPSTensor

/-- The window-correlator normalization is the squared-norm expectation
of the actual unnormalized periodic vector. Source: arXiv:2307.01696,
Supplemental Material, Lemma 2; SPC11 Section II.F. -/
theorem mpvExpectation_eq_inner_div_norm_sq
    {d D : ℕ} (A : MPSTensor d D) (N : ℕ) (O : MPOTensor.ChainOperator d N) :
    mpvExpectation A N O =
      ⟪mpvState A N, Matrix.toEuclideanCLM (𝕜 := ℂ) O (mpvState A N)⟫_ℂ /
        ((‖mpvState A N‖ ^ 2 : ℝ) : ℂ) := by
  rw [mpvExpectation_eq_div, inner_self_eq_norm_sq_to_K]
  rw [Complex.ofReal_pow]
  rfl

/-- Every normalized finite expectation is invariant under equality of
the actual positive-length MPS rays. Source: SPC11, arXiv:1010.3732,
Section II.F, lines 929–953. -/
theorem SamePositiveMpvRay.mpvExpectation_eq
    {d D E N : ℕ} {A : MPSTensor d D} {B : MPSTensor d E}
    (hRay : SamePositiveMpvRay A B) (hN : 0 < N) (O : MPOTensor.ChainOperator d N) :
    mpvExpectation A N O = mpvExpectation B N O := by
  obtain ⟨c, hc⟩ := Submodule.span_singleton_eq_span_singleton.mp (hRay N hN)
  change (c : ℂ) • (mpv A : Cfg d N → ℂ) = mpv B at hc
  have hstate : mpvState B N = (c : ℂ) • mpvState A N := by
    unfold mpvState
    rw [← map_smul]
    exact congrArg (EuclideanSpace.equiv (ι := Cfg d N) (𝕜 := ℂ)).symm hc.symm
  rw [mpvExpectation_eq_inner_div_norm_sq,
    mpvExpectation_eq_inner_div_norm_sq, hstate,
    Matrix.inner_toEuclideanCLM_div_norm_sq_smul _ _ c.ne_zero]

/-- Connected window correlations are invariant under equality of the
actual periodic rays. No injectivity, canonical gauge or nonzero-vector
condition is needed for this algebraic identity.
Source: SPC11, arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem SamePositiveMpvRay.mpvConnectedCorrelator_eq
    {d D E N L : ℕ} {A : MPSTensor d D} {B : MPSTensor d E}
    (hRay : SamePositiveMpvRay A B) (hN : 0 < N) (a b : ℕ)
    (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) (ha : a + L ≤ N) (hb : b + L ≤ N) :
    mpvConnectedCorrelator A N a b X Y ha hb = mpvConnectedCorrelator B N a b X Y ha hb := by
  simp only [mpvConnectedCorrelator, hRay.mpvExpectation_eq hN]

end MPSTensor
