/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Ising.IsingGauge

/-!
# The Ising letter identity: the fermion sector

The letters `(h, h')` of the stacked product `Θ_2 ⋆ (√2 A_σ)` whose two labels carry the middle
label `ρ = ψ`, that is `h, h' ∈ {(1,ψ,ψ), (ψ,ψ,1), (σ,ψ,σ)}`: nine letters, each of which is
block diagonal in the block coordinates with the blocks `5 (√2 A_σ)`, `3 (√2 A_σ)` and sixteen
zeros. This is the sector carrying the sign `[F^{ψσψ}_σ] = -1` of the gauge.

The letter identity of the weighted Ising bond object
(`Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, §1.3, check T2-G3) is decided
sector by sector, one exhaustive kernel computation per file, so that no single file carries
more than a few of the conjugated `24 × 24` matrices over `ℤ√2`. The sector matrices and
the gauge are those of `IsingGauge`; the sectors are assembled in `IsingWeightedTwist`.

## Main results

* `IsingTwist.conjSector_eq_blockDiagonal_of_rho_one`: every letter of the fermion sector is
  block diagonal with the prescribed blocks.
-/

namespace IsingTwist

open MPSTensor Zsqrtd

/-- **The letter identity on the fermion sector** (data file §1.3, check T2-G3): every letter of
the fermion sector is block diagonal with the prescribed blocks. -/
theorem conjSector_eq_blockDiagonal_of_rho_one :
    ∀ h h' : Fin 10, isingRho h = 1 → isingRho h' = 1 →
      conjSector 1 h h' = Matrix.blockDiagonal' (isingBlockZ (isingSigmaZ h h')) := by
  decide +kernel

end IsingTwist
