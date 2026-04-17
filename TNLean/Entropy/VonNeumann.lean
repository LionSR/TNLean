/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Analysis.Entropy

/-!
# Von Neumann entropy (namespace bootstrap)

This module provides the `Entropy` namespace wrappers for the von
Neumann entropy defined in `TNLean.Analysis.Entropy`. It is the first
of three files in the `TNLean/Entropy/` bootstrap that unblocks the
Simple MPDO RFP track (see issue #236, infrastructure request #613,
and the umbrella task #239).

The underlying eigenvalue-based definition, the nonnegativity proof,
and the `S(ρ) ≤ log D` bound are imported from
`TNLean.Analysis.Entropy`; they are re-exported here under the
`Entropy` namespace so that downstream MPDO/RFP modules can refer to a
single stable surface for quantum entropy.

## Main definitions

* `Entropy.vonNeumannEntropy` — `S(ρ) = -tr(ρ log ρ)` for a Hermitian
  matrix `ρ`, in terms of eigenvalues.

## Main results

* `Entropy.vonNeumannEntropy_nonneg` — `S(ρ) ≥ 0` for density
  matrices.
* `Entropy.vonNeumannEntropy_le_log_dim` — `S(ρ) ≤ log D` for density
  matrices on a `D`-dimensional system.

## Implementation notes

These are thin re-exports of the declarations in
`TNLean.Analysis.Entropy`. The purpose of the dedicated
`TNLean/Entropy/` directory is to give the entropy API a single import
point so that the axiomatized strong-subadditivity inequality lives
next to the provable results it combines with.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*][Wolf2012QChannels]
* arXiv:1606.00608 §4.4
-/

open scoped Matrix ComplexOrder
open Matrix Finset Real

namespace Entropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Von Neumann entropy** of a Hermitian matrix.

For a Hermitian matrix `ρ` with eigenvalues `λᵢ`, the von Neumann
entropy is `S(ρ) = ∑ᵢ negMulLog(λᵢ) = -∑ᵢ λᵢ log(λᵢ)`.

When `ρ` is a density matrix (PSD with trace 1), this is the standard
quantum entropy `S(ρ) = -tr(ρ log ρ)`.

This is a thin wrapper around `_root_.vonNeumannEntropy`. -/
noncomputable def vonNeumannEntropy
    (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) : ℝ :=
  _root_.vonNeumannEntropy ρ hρ

/-- Unfolding lemma relating the namespaced wrapper to the underlying
definition in `TNLean.Analysis.Entropy`. -/
@[simp] theorem vonNeumannEntropy_eq
    (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) :
    vonNeumannEntropy ρ hρ = _root_.vonNeumannEntropy ρ hρ := rfl

section FinD

variable {D : ℕ}

/-- Von Neumann entropy is nonneg for density matrices.

Each eigenvalue `λᵢ` of a density matrix satisfies `0 ≤ λᵢ ≤ 1`, and
`negMulLog` is nonneg on `[0, 1]`.

Proved from Mathlib via `Real.negMulLog_nonneg`; not axiomatized. -/
theorem vonNeumannEntropy_nonneg
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ ∈ densityMatrices D) :
    0 ≤ vonNeumannEntropy ρ hρ.1.isHermitian :=
  _root_.vonNeumannEntropy_nonneg hρ

/-- Von Neumann entropy is bounded above by `log D`.

Proved via Jensen's inequality applied to the concave function
`Real.negMulLog`; the maximum is achieved at the maximally mixed state
`ρ = I / D`, giving `S(ρ) ≤ log D`. Not axiomatized. -/
theorem vonNeumannEntropy_le_log_dim
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ ∈ densityMatrices D)
    (hD : 0 < D) :
    vonNeumannEntropy ρ hρ.1.isHermitian ≤ Real.log D :=
  _root_.vonNeumannEntropy_le_log_dim hρ hD

end FinD

end Entropy
