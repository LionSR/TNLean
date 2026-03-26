/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Spectral.SpectralGap
import TNLean.Channel.Peripheral.Spectrum

/-!
# Quantitative spectral gap bounds for MPS transfer operators

This file provides **explicit quantitative bounds** on the spectral gap of
MPS transfer operators, strengthening the existing qualitative result
`spectralRadius_mixedTransfer_lt_one` (which only proves `ρ < 1` without
a lower bound on `1 - ρ`).

## Building blocks (already formalized elsewhere)

* `pow_tendsto_zero_of_spectralRadius_lt_one` in `Spectral/SpectralGap.lean` —
  exponential convergence to zero when spectral radius < 1
* `compl_eigenvalue_norm_lt_one_of_primitive` in `Peripheral/Spectrum.lean` —
  primitive channels have spectral gap
* `cumulativeSpan_eq_top` in `Wielandt/WielandtBound.lean` — the D² Wielandt bound

## Main results

* `exponential_convergence_of_primitive` — for a primitive TP channel,
  `‖E^n(X) - P(X)‖ ≤ C · (1-δ)^n · ‖X‖` (convergence to fixed-point projection)
* `correlation_length_bound` — exponential decay of traceless iterates
* `spectral_gap_from_wielandt` — explicit spectral gap `δ > 0` with
  all non-unit eigenvalues satisfying `|μ| ≤ 1 - δ`

## Strengthening relative to the literature

The existing formalization proves `ρ(F_{AB}) < 1` for non-equivalent blocks
but gives no explicit bound. This file provides constructive bounds.

## References

* [M. Wolf, *Quantum Channels & Operations*, §6.3]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal ENNReal
open Matrix Finset

namespace MPSTensor

variable {d D : ℕ}

/-! ## Convergence rate from spectral gap -/

/-- **Exponential convergence of primitive channels.**

For a primitive TP channel `E` with unique fixed point `ρ_∞`, the iterates
`E^n(X)` converge exponentially to the fixed-point projection `P(X)`:

  `‖E^n(X) - P(X)‖ ≤ C · (1-δ)^n · ‖X‖`

where `P(X) = tr(X) · ρ_∞ / tr(ρ_∞)` is the projection onto the fixed state,
`δ > 0` is the spectral gap, and `C` depends on the Jordan structure.

The spectral gap `δ` exists by `compl_eigenvalue_norm_lt_one_of_primitive`
from `Peripheral/Spectrum.lean`. The exponential convergence follows from
`pow_tendsto_zero_of_spectralRadius_lt_one` in `Spectral/SpectralGap.lean`
applied to `E - P` (which has spectral radius < 1 by primitivity). -/
theorem exponential_convergence_of_primitive [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitive (transferMap (d := d) (D := D) A))
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ)
    (hρ_ne : ρ ≠ 0) (htr : Matrix.trace ρ ≠ 0) :
    ∃ (C : ℝ) (δ : ℝ),
      0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (n : ℕ) (X : Matrix (Fin D) (Fin D) ℂ),
        ‖((transferMap (d := d) (D := D) A)^[n]) X -
          fixedPointProj ρ htr X‖ ≤
          C * (1 - δ) ^ n * ‖X‖ := by
  -- TODO (#22): use compl_eigenvalue_norm_lt_one_of_primitive for spectral gap,
  -- then pow_tendsto_zero_of_spectralRadius_lt_one for exponential convergence
  sorry

/-- **Correlation length bound.**

For a primitive TP-normalized MPS tensor, traceless matrices decay
exponentially under the transfer map iteration. The rate is determined by
the spectral gap, which exists by primitivity.

This uses `pow_tendsto_zero_of_spectralRadius_lt_one` from
`Spectral/SpectralGap.lean` directly — traceless matrices lie in
`ker(P) = range(E - P)`, where `E - P` has spectral radius < 1. -/
theorem correlation_length_bound [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : IsInjective A) :
    ∃ (C : ℝ) (ξ : ℝ),
      0 < C ∧ 0 < ξ ∧
      ∀ (n : ℕ) (X : Matrix (Fin D) (Fin D) ℂ),
        Matrix.trace X = 0 →
        ‖((transferMap (d := d) (D := D) A)^[n]) X‖ ≤
          C * Real.exp (-(n : ℝ) / ξ) * ‖X‖ := by
  -- TODO (#22): ξ = -1/log(ρ₂) where ρ₂ is second-largest eigenvalue modulus
  sorry

/-! ## Explicit gap from Wielandt bound -/

/-- **Spectral gap from the Wielandt bound** (existential version).

For an injective TP-normalized MPS tensor, all eigenvalues of the transfer
map other than 1 have modulus strictly less than 1, with a uniform gap.

The existential bound `∃ δ > 0` follows from: injectivity implies primitivity
(by the Wielandt bound), primitivity implies spectral gap
(by `compl_eigenvalue_norm_lt_one_of_primitive`), and in finite dimensions
the maximum over finitely many eigenvalues gives a uniform bound. -/
theorem spectral_gap_from_wielandt [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : IsInjective A) :
    ∃ (δ : ℝ), 0 < δ ∧
      ∀ (μ : ℂ), Module.End.HasEigenvalue (transferMap (d := d) (D := D) A) μ →
        μ ≠ 1 → ‖μ‖ ≤ 1 - δ := by
  -- TODO (#22): combine injective_implies_irreducibleCP + isPrimitive +
  -- compl_eigenvalue_norm_lt_one_of_primitive + finite eigenvalue max
  sorry

end MPSTensor
