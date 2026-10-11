/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TwoFamilies
import QICLean.Entropy.FiniteProductContinuity

/-!
# Regional entropy continuity on a finite lattice

For two normalized vectors on the same finite lattice, the entropy change
on a fixed region is bounded by the global trace distance and the number of
sites in that region. The dimension factor is `1 + |A| log q`.

The statement makes no geometric or Hamiltonian assumption and includes
empty regions and local dimension one. Both vectors are supplied; the
argument makes no further choice of state.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, Lemma 2.1 (`01-preliminaries.tex`, lines 33–46), as used in
`08-scanner.tex`, lines 399–404, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The proof is independently written from the mathematical argument.
-/

namespace TNLean.PEPS.AreaLaw

/-- Regional entropy continuity with the dimension of the actual region.
Source: Lemma 2.1, `01-preliminaries.tex`, lines 33–46, and its application
in `08-scanner.tex`, lines 399–404. -/
theorem abs_regionalEntropy_sub_le_sqrt_traceDistance
    (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω Φ : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (hΦ : ‖Φ‖ = 1)
    (A : Finset (Site Λ)) :
    |regionalEntropy Λ q Ω A - regionalEntropy Λ q Φ A| ≤
      4 * Real.sqrt (Matrix.traceDistance
        (Matrix.vecMulVec Ω (star Ω)) (Matrix.vecMulVec Φ (star Φ))) *
        (1 + (A.card : ℝ) * Real.log q) := by
  have h := FiniteProduct.abs_entropy_sub_le_sqrt_traceDistance
    (fun _ : Site Λ ↦ Fin q) Ω Φ hΩ hΦ A
  done

end TNLean.PEPS.AreaLaw
