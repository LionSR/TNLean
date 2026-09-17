/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.IsingGauge

/-!
# The Ising letter identity: the spin sector, abelian left label

The letters `(h, h')` of the stacked product `Θ_2 ⋆ (√2 A_σ)` whose two labels carry the middle
label `ρ = σ` and whose left label `h` has an abelian first entry, that is
`h ∈ {(1,σ,σ), (ψ,σ,σ)}` and `h' ∈ {(1,σ,σ), (ψ,σ,σ), (σ,σ,1), (σ,σ,ψ)}`: eight letters, each
of which is block diagonal in the block coordinates with the blocks `5 (√2 A_σ)`, `3 (√2 A_σ)`
and sixteen zeros. The spin sector has sixteen letters, twice as many as the other two, and is
split between this file and `IsingLetterSectorSigmaSigma` by the first entry of the left label,
which is abelian exactly when the label index is below `8`.

The letter identity of the weighted Ising bond object
(`Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, §1.3, check T2-G3) is decided
sector by sector, one exhaustive kernel computation per file, so that no single file carries
more than a few of the conjugated `24 × 24` matrices over `ℤ√2`. The sector matrices and
the gauge are those of `IsingGauge`; the sectors are assembled in `IsingWeightedTwist`.

## Main results

* `IsingTwist.conjSector_eq_blockDiagonal_of_rho_two_of_lt`: every letter of the spin sector
  whose left label is `(1,σ,σ)` or `(ψ,σ,σ)` is block diagonal with the prescribed blocks.
-/

namespace IsingTwist

open MPSTensor Zsqrtd

/-- **The letter identity on the spin sector, abelian left label** (data file §1.3, check
T2-G3): every letter of the spin sector whose left label is `(1,σ,σ)` or `(ψ,σ,σ)` is block
diagonal with the prescribed blocks. -/
theorem conjSector_eq_blockDiagonal_of_rho_two_of_lt :
    ∀ h h' : Fin 10, isingRho h = 2 → isingRho h' = 2 → h.val < 8 →
      conjSector 2 h h' = Matrix.blockDiagonal' (isingBlockZ (isingSigmaZ h h')) := by
  decide +kernel

end IsingTwist
