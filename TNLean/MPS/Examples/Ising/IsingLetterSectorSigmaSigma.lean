/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Ising.IsingGauge

/-!
# The Ising letter identity: the spin sector, left label starting with the spin

The letters `(h, h')` of the stacked product `Θ_2 ⋆ (√2 A_σ)` whose two labels carry the middle
label `ρ = σ` and whose left label `h` has the first entry `σ`, that is
`h ∈ {(σ,σ,1), (σ,σ,ψ)}` and `h' ∈ {(1,σ,σ), (ψ,σ,σ), (σ,σ,1), (σ,σ,ψ)}`: eight letters, each
of which is block diagonal in the block coordinates with the blocks `5 (√2 A_σ)`, `3 (√2 A_σ)`
and sixteen zeros. This is the second half of the spin sector, the first half being
`IsingLetterSectorSigmaAbelian`; the left label starts with the spin exactly when the label
index is at least `8`.

The letter identity of the weighted Ising bond object
(`Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, §1.3, check T2-G3) is decided
sector by sector, one exhaustive kernel computation per file, so that no single file carries
more than a few of the conjugated `24 × 24` matrices over `ℤ√2`. The sector matrices and
the gauge are those of `IsingGauge`; the sectors are assembled in `IsingWeightedTwist`.

## Main results

* `IsingTwist.conjSector_eq_blockDiagonal_of_rho_two_of_le`: every letter of the spin sector
  whose left label is `(σ,σ,1)` or `(σ,σ,ψ)` is block diagonal with the prescribed blocks.
-/

namespace IsingTwist

open MPSTensor Zsqrtd

/-- **The letter identity on the spin sector, left label starting with the spin** (data file
§1.3, check T2-G3): every letter of the spin sector whose left label is `(σ,σ,1)` or `(σ,σ,ψ)`
is block diagonal with the prescribed blocks. -/
theorem conjSector_eq_blockDiagonal_of_rho_two_of_le :
    ∀ h h' : Fin 10, isingRho h = 2 → isingRho h' = 2 → 8 ≤ h.val →
      conjSector 2 h h' = Matrix.blockDiagonal' (isingBlockZ (isingSigmaZ h h')) := by
  decide +kernel

end IsingTwist
