/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.PhysicalCollarInformation
import TNLean.PEPS.AreaLaw.AmplificationProof

/-!
# The uniform area law conditional on the two-family decomposition

The physical collar and amplification theorems reduce the uniform area law to
the two-family decomposition at common admissible template constants. This
module proves that implication; the geometric decomposition remains a hypothesis.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*, proof
of Theorem 1.1, `10-geometry.tex`, lines 803–857, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw

/-- The uniform area law conditional on the two-family decomposition at
admissible template constants. The collar and amplification bounds are supplied
by their physical proofs. Source: OpenAI, *A two-dimensional area law from a
global spectral gap*, proof of Theorem 1.1, `10-geometry.tex`, lines 803–857,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This implication does not construct the decomposition of Proposition 11.2. -/
theorem uniformAreaLaw_of_twoFamilies
    (htwo : ∀ R : ℕ, ∃ D₀ Ctpl : ℝ,
      2 * (R : ℝ) + 10 < D₀ ∧ 24 ≤ Ctpl ∧ TwoFamilyDecomposition D₀ Ctpl) :
    UniformAreaLaw := by
  apply uniformAreaLaw_of_collar_twoFamilies
  intro q hq R J Δ hJ hΔ
  obtain ⟨D₀, Ctpl, hD₀, hCtpl, hdec⟩ := htwo R
  exact ⟨D₀, Ctpl, sublinearCollarBound_real q R hq hJ.le hΔ hD₀ hCtpl, hdec⟩

end TNLean.PEPS.AreaLaw
