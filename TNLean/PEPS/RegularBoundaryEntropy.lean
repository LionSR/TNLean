/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularBoundaryState
import TNLean.Algebra.FlatDensityEntropy

/-!
# Entropy of the virtual regular boundary state

For `n + 1` regular boundary legs, the virtual reduced density operator is the averaging
projector divided by its rank `|G| ^ n`. Its nonzero eigenvalues all equal `1 / |G| ^ n`,
and its von Neumann entropy is `log (|G| ^ n) = n log |G|`.

This is the virtual calculation in Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
Theorem 6.9 (`Papers/1001.3807/paper_v3.tex`, lines 2027–2072). Identifying this entropy
with that of a physical PEPS region requires the separate contraction and isometry arguments.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The virtual boundary entropy is the logarithm of its invariant dimension.
Source: arXiv:1001.3807, Theorem 6.9 and its proof, lines 2027–2072. -/
theorem vonNeumannEntropy_regularBoundaryDensity (n : ℕ) :
    vonNeumannEntropy (regularBoundaryDensity (G := G) n)
        (regularBoundaryDensity_posSemidef n).isHermitian =
      Real.log ((Fintype.card G : ℝ) ^ n) := by
  apply vonNeumannEntropy_of_mul_self_eq_inv_smul
    (regularBoundaryDensity_posSemidef n) (trace_regularBoundaryDensity n)
  simpa only [Complex.ofReal_pow, Complex.ofReal_natCast] using
    regularBoundaryDensity_mul_self (G := G) n

/-- The virtual entropy equals the number of relative boundary labels times `log |G|`.
Source: arXiv:1001.3807, Theorem 6.9, lines 2027–2037. -/
theorem vonNeumannEntropy_regularBoundaryDensity_eq_mul_log (n : ℕ) :
    vonNeumannEntropy (regularBoundaryDensity (G := G) n)
        (regularBoundaryDensity_posSemidef n).isHermitian =
      (n : ℝ) * Real.log (Fintype.card G : ℝ) := by
  rw [vonNeumannEntropy_regularBoundaryDensity, Real.log_pow]

/-- In terms of the `n + 1` boundary legs, the virtual entropy has area term
`(n + 1) log |G|` and correction `-log |G|`. Source: arXiv:1001.3807, Theorem 6.9,
lines 2027–2037. -/
theorem vonNeumannEntropy_regularBoundaryDensity_eq_boundaryLength (n : ℕ) :
    vonNeumannEntropy (regularBoundaryDensity (G := G) n)
        (regularBoundaryDensity_posSemidef n).isHermitian =
      ((n + 1 : ℕ) : ℝ) * Real.log (Fintype.card G : ℝ) -
        Real.log (Fintype.card G : ℝ) := by
  rw [vonNeumannEntropy_regularBoundaryDensity_eq_mul_log]
  push_cast
  ring

end TNLean.PEPS
