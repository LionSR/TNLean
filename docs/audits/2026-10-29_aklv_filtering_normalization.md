# AKLV normalization and filtering validation

Date: 2026-10-29. Published slice based on tested prerequisite
`b0e62a1ff38cc6c71fa301f94449ad855ebf4c25`.

The five source modules were compiled with the repository Lean options and
warnings as errors. The TNLean import closure has 29 modules; its 24 pre-existing modules
are byte-identical to the tested prerequisite. Toolchain,
`lakefile.toml`, and `lake-manifest.json` are byte-identical; QICLean remains
`acda92aa70e69b37507e422bceb5414036859fe6` and Mathlib remains
`c55e6e786f49471c72fbddbec5415808896aec1e` (Lean v4.35.0-rc3).

Targeted exact/transitive axiom audits for the normalized filtering estimates
and original-chain normalization report only `propext`, `Classical.choice`
and `Quot.sound`. No new axioms, proof holes or kernel bypasses were introduced.
The blueprint links only these proved auxiliary statements; no physical
approximate-projector construction or full area-law result is claimed.

Full-root blueprint `checkdecls` remains a CI gate: the local targeted workspace
has no built `TNLean.olean`. The new declarations were separately checked after
importing the compiled AKLV modules.

## Final audit: five-module normalization/filtering publication slice

Scope is exactly the current source of `NormalizedVector`, `ApproximationStep`, `FilteredApproximation`, `DisjointGroundEnergy`, and `ChainNormalization`. No other new sequence, entropy, physical projector, or fixed-seed-overlap result is included in this verdict. The review is semantic; public-baseline dependency-byte checks, strict compilation, axiom printouts, documentation checks, and publication are the owner's separate responsibilities.

**Verdict: PASS.** No mathematical blocker, phase defect, hidden conclusion, or new normalization premise was found in these five modules. All five corresponding compiled artifacts were current at review time. The reviewer made no repository edits and performed no publication or approval action.

The additions since the third audit resolve the prior middle-block interface consideration:

- `exists_three_disjoint_ground_shifts` now retains implications from positivity of each original operator to nonnegativity of its constructed shift. Each implication is proved using the actual normalized regional eigenvector already constructed, so these are conclusions, not extra assumptions. No nonnegative minimum is asserted for a merely Hermitian operator.
- `exists_chain_normalization` derives positivity of the three original regional sums from the original positive terms and applies those implications. Its conclusion now provides `x,m,y>=0` together with PSD shifted blocks, `0<=e<=2`, and the preserved original ground vector/projector gap.
- `middleCutBlock_le_window` proves the explicit order cap `(b-a) I` from the original upper contraction bounds and a nonnegative middle shift. The strict interior bond set injects into `[a,b)`, so its cardinality is at most the stated natural-number difference. Subtracting the nonnegative scalar shift cannot increase the matrix. The estimate is intentionally one bond looser than the exact strict-interior count. The theorem remains valid without a separate `a<b` hypothesis: when `b<=a`, the strict interior is empty and the asserted upper cap is zero.
- The small shared orthogonal-decomposition lemma in `NormalizedVector` follows directly from the unit self-inner-product identity. `ApproximationStep` and `FilteredApproximation` use it without changing their hypotheses or conclusions. A focused Mathlib inner-product-space source search found no equivalent named theorem for this exact unit-vector subtraction identity.
- The previously reviewed nonzero normalization, explicit unit phase, `4 delta r` step estimate, `2 delta/mu^2` overlap estimate, seven-eighths budget, and actual Schmidt-rank bounds remain unchanged mathematically and are sound.

Reviewed source SHA-256 snapshots:

| Module | SHA-256 |
| --- | --- |
| NormalizedVector | `f062ba41cd80adc7a4b3daedb83b29cba69a263f3538a4a17eca7dac1b8e6fcf` |
| ApproximationStep | `3da4aab5a76cb7c2e0e84b100dc8d3c47eaa4f617cf8ed972eff961d551668fc` |
| FilteredApproximation | `69c2415cb591b2933ae0ce09105bf68c89a367de26fc9a6f17042061651584a5` |
| DisjointGroundEnergy | `bee0264166923e69ee9ab2653aee83ccd0c52e4af826dfe62be11d2b7e3f88cb` |
| ChainNormalization | `2561cd7815466682866786201145cf450958f7df9b51ae3ee855d5d084eaea94` |

This slice is a valid set of independent normalization and filtering results. It must not be described as completing the original-chain area-law proof or constructing the physical approximate projectors.
