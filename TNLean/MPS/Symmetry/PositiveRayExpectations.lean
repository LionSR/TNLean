/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactMPSGappedPhase
import TNLean.MPS.Preparation.WindowCorrelator
import TNLean.Lattice.ObservableCentering

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

namespace TNLean.Lattice

/-- A nonzero scalar does not change the actual normalized expectation,
even when the vector itself is zero. Source: SPC11, arXiv:1010.3732,
Section II.F, lines 929–953, normalization of physical rays. -/
theorem normalizedVectorExpectation_smul
    {n : Type*} [Fintype n] [DecidableEq n]
    (ψ : EuclideanSpace ℂ n) (A : Matrix n n ℂ) {c : ℂ} (hc : c ≠ 0) :
    normalizedVectorExpectation (c • ψ) A = normalizedVectorExpectation ψ A := by
  have hnorm (φ : EuclideanSpace ℂ n) :
      ((‖φ‖ ^ 2 : ℝ) : ℂ) = ⟪φ, φ⟫_ℂ := by
    simpa only [Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K φ).symm
  simp only [normalizedVectorExpectation, hnorm, map_smul, inner_smul_left,
    inner_smul_right, ← mul_assoc]
  exact mul_div_mul_left _ _ (mul_ne_zero (star_ne_zero.mpr hc) hc)

end TNLean.Lattice

namespace MPSTensor

open TNLean.Lattice

/-- The window-correlator normalization is the squared-norm expectation
of the actual unnormalized periodic vector. Source: arXiv:2307.01696,
Supplemental Material, Lemma 2; SPC11 Section II.F. -/
theorem mpvExpectation_eq_normalizedVectorExpectation
    {d D : ℕ} (A : MPSTensor d D) (N : ℕ) (O : MPOTensor.ChainOperator d N) :
    mpvExpectation A N O = normalizedVectorExpectation (mpvState A N) O := by
  rw [mpvExpectation_eq_div, inner_self_eq_norm_sq_to_K]
  unfold normalizedVectorExpectation
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
  rw [mpvExpectation_eq_normalizedVectorExpectation,
    mpvExpectation_eq_normalizedVectorExpectation, hstate,
    normalizedVectorExpectation_smul _ _ c.ne_zero]

/-- Connected window correlations are invariant under equality of the
actual periodic rays. No injectivity, canonical gauge or nonzero-vector
condition is needed for this algebraic identity.
Source: SPC11, arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem SamePositiveMpvRay.mpvConnectedCorrelator_eq
    {d D E N L : ℕ} {A : MPSTensor d D} {B : MPSTensor d E}
    (hRay : SamePositiveMpvRay A B) (hN : 0 < N) (a b : ℕ)
    (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    mpvConnectedCorrelator A N a b X Y = mpvConnectedCorrelator B N a b X Y := by
  simp only [mpvConnectedCorrelator, hRay.mpvExpectation_eq hN]

end MPSTensor
