/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Analysis.Entropy

/-!
# Von Neumann entropy in the `Entropy` namespace

This module provides `Entropy`-namespace aliases for the von Neumann
entropy definitions and theorems from `TNLean.Analysis.Entropy`.

The underlying eigenvalue-based definition, the nonnegativity proof,
and the `S(ρ) ≤ log D` bound live in `TNLean.Analysis.Entropy`. The
aliases defined here are definitionally equal to their root-namespace
counterparts (see issues #236, #613, #239).

## Main declarations

* `Entropy.vonNeumannEntropy` — alias of `_root_.vonNeumannEntropy`,
  `S(ρ) = -tr(ρ log ρ)` for a Hermitian matrix
* `Entropy.vonNeumannEntropy_nonneg` — alias of
  `_root_.vonNeumannEntropy_nonneg`: `S(ρ) ≥ 0` for density matrices
* `Entropy.vonNeumannEntropy_le_log_dim` — alias of
  `_root_.vonNeumannEntropy_le_log_dim`: `S(ρ) ≤ log D` for density
  matrices on a `D`-dimensional system

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*][Wolf2012QChannels]
* arXiv:1606.00608 Section 4.4
-/

namespace Entropy

/-- **Von Neumann entropy** of a Hermitian matrix, namespaced alias.

For a Hermitian matrix `ρ` with eigenvalues `λᵢ`, the von Neumann
entropy is `S(ρ) = ∑ᵢ negMulLog(λᵢ) = -∑ᵢ λᵢ log(λᵢ)`. Definitionally
equal to `_root_.vonNeumannEntropy`. -/
noncomputable alias vonNeumannEntropy := _root_.vonNeumannEntropy

/-- **Von Neumann entropy is nonneg for density matrices**, namespaced
alias of `_root_.vonNeumannEntropy_nonneg`. -/
alias vonNeumannEntropy_nonneg := _root_.vonNeumannEntropy_nonneg

/-- **Von Neumann entropy is bounded above by `log D`** on a
`D`-dimensional system, namespaced alias of
`_root_.vonNeumannEntropy_le_log_dim`. -/
alias vonNeumannEntropy_le_log_dim := _root_.vonNeumannEntropy_le_log_dim

end Entropy
