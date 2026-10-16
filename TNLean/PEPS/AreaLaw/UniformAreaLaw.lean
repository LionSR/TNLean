/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryTheoremFromTwoFamilies
import TNLean.PEPS.AreaLaw.Geometry.TwoFamilyDecomposition

/-!
# The uniform area law on finite induced lattice domains

The two-family geometric decomposition, the sublinear collar estimate and
amplification give an entropy bound proportional to the number of cut edges.
The constant depends only on the local dimension, interaction range,
interaction norm bound and spectral gap. It is uniform over the finite domain,
Hamiltonian, normalized gapped ground state and cut; no connectedness or
restriction on holes is required.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, Theorem 1.1 (`thm:area`, `eq:area-law`); final proof in
`10-geometry.tex`, lines 803–857. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- **Theorem 1.1** (`thm:area`, `eq:area-law`). The entanglement entropy of
any region of a finite induced square-lattice domain is bounded by a constant
times its edge boundary. The constant depends only on the local dimension,
interaction range, interaction norm bound and spectral gap, and is chosen
before the domain, Hamiltonian, ground state and region.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Theorem 1.1; final proof in `10-geometry.tex`, lines 803–857.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem uniformAreaLaw : UniformAreaLaw := by
  exact uniformAreaLaw_of_twoFamilies fun R ↦
    ⟨2 * (R : ℝ) + 11, 24, by linarith, le_rfl, twoFamilyDecomposition _ _⟩

end TNLean.PEPS.AreaLaw
