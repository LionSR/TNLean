# Declaration-free import waypoint retirement (2026-08-26)

Audited at TNLean `e091784dec9f7c478a2802ec741637456da436e0`.

Three modules carried no declarations at all: each was a header, a single
import, and a module docstring pointing at the module that owns the results.
The project pass-through exception applies — nothing forwards, every non-Archive
importer is migrated, and no Blueprint tag names any of them.

| Removed module | Replacement |
|---|---|
| `TNLean.Spectral.MPVOverlapDecay` | `TNLean.Spectral.TransferOperatorGapInjective` |
| `TNLean.Spectral.TransferOperatorGap` | `TNLean.Spectral.TransferOperatorGapInjective` |
| `TNLean.Wielandt.Primitivity.ToNormal` | `QICLean.Kraus.PrimitiveFixedPoint` (already imported by every consumer) |

Migrated importers: `PiAlgebra/CanonicalFormSepAux` (both waypoints),
`MPS/Overlap/CastDecay`, `MPS/SharedInfra/GaugePhase`,
`Spectral/PrimitiveOverlap`, `MPS/Core/Correlations`,
`MPS/Symmetry/StringOrderDefs`. `Wielandt/Primitivity/ToNormal` had no
importer outside the generated aggregator.

One declaration went with them:

| Removed declaration | Replacement |
|---|---|
| `MPSTensor.mpvInner_tendsto_zero` | none — zero consumers; the overlap form `MPSTensor.mpvOverlap_tendsto_zero` it wrapped survives |

`mpvInner_tendsto_zero` was advertised only by the deleted `MPVOverlapDecay`
docstring; repository-wide search found no term-level use. Recovering it costs
the three lines of its old proof from `mpvOverlap_tendsto_zero`.

The stale citations to the deleted files in the `clm_norm_instances` candidate
entry of `docs/tactic_patterns.md` were repointed to the surviving occurrences
in the same change. Dated snapshots under `docs/audits/`, `docs/slides/`, and
the closed entries of `docs/proof_debt_ledger.md` are left as historical record.
