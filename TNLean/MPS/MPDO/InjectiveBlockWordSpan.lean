/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CompleteZipperFusionBlocked

/-!
# Simultaneous word spans of unnormalized injective blocks

Pairwise inequivalent injective blocks of positive dimension have a common
positive word length at which their tuples span the full product matrix
algebra. Spectral normalization of the original blocks is unnecessary:
independent nonzero scalar normalizations give normal tensors, and the
resulting simultaneous span transfers back at the same length.

This is the common-blocking step in Garre-Rubio, Lootens and Molnár,
arXiv:2203.12563v3, Appendix A, using the block-injectivity theorem of
arXiv:1606.00608, lines 317--345.
-/

namespace MPSTensor

/-- Individually injective, pairwise gauge-phase-inequivalent blocks have a
common positive simultaneous spanning length, without a spectral-radius-one
assumption on any original block. -/
theorem exists_positive_wordTupleSpanTop_of_isInjective
    {d g : ℕ} {dim : Fin g → ℕ}
    {B : (j : Fin g) → MPSTensor d (dim j)}
    (hInj : ∀ j, Kraus.IsInjective (B j)) (hdimPos : ∀ j, 0 < dim j)
    (hDistinct : BlocksNotGaugePhaseEquiv (d := d) B) :
    ∃ L : ℕ, 0 < L ∧ WordTupleSpanTop B L := by
  have hScaled : ∀ j, ∃ ζ : ℂ, ζ ≠ 0 ∧ IsNormalTensor (ζ • B j) := by
    intro j
    have : NeZero (dim j) := ⟨(hdimPos j).ne'⟩
    obtain ⟨A, ζ, hζ, hGauge, -, -, hA⟩ :=
      exists_leftCanonical_normalTensor_scale_of_isNormal (hInj j).isNormal
    exact ⟨ζ, hζ, IsNormalTensor.of_gaugeEquiv hA hGauge⟩
  choose scale hscale hNormal using hScaled
  obtain ⟨L, hL, hSpan⟩ := exists_positive_wordTupleSpanTop_of_isNormal hNormal hdimPos
    (fun j k hjk hdim hGPE => hDistinct j k hjk hdim
      (gaugePhaseEquiv_of_smul_smul_cast hdim (hscale j) (hscale k) hGPE))
  exact ⟨L, hL, wordTupleSpanTop_of_smul hscale hSpan⟩

end MPSTensor
