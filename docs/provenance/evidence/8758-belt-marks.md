# Actual belt-cell marks: verification pending

The six proposed declarations in `BeltMarks.lean` define the nine actual
marked points of a dyadic belt cell and their deduplicated finite union over
a collection of belt cells. The points are the image of `Fin 3 × Fin 3`
under coordinate offsets zero, one half and one: the center, four corners
and four side midpoints. They lie in the closed cell.

The intended results prove that one cell has exactly nine distinct marks
and that the cardinality of the union is at most nine times the number of
cells. Combining this count with the established sparse-belt estimate
selects actual coordinate residues with

\[
|\mathcal M_k|\le576(2C_0+1)^2\,|\partial_\Lambda A|\,2^{-\delta_0k/2}.
\]

The coefficient is exactly 9 × 64. These are proposed mathematical
statements until exact committed-source verification is recorded. No build,
axiom-audit result or elapsed time is fabricated in this pending template.

## Source, attribution and scope

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.

The nine marks and deduplication are in lines 325–330 in the proof of
`prop:two-families`, immediately before `geometry:initial-stars`. The final
sparse-shift composition also uses `geometry:belt-count`, lines 220–228.
The proof text is independently written; no upstream Lean source or proof
text is reused. OpenAI Codex (GPT-6) assists LionSR under the existing
[TNLean #8758 claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6043892601).

This contribution concerns actual mark locations and finite counting. It does
not assign the smallest incident cell scale to each deduplicated mark, prove
isolated stars, separation or completeness of the contact marks, or construct
repairs. Minimum incident-scale assignment, contacts, repairs, descendant
counts, birth separation from earlier actual regions, the complete two-family
partition and both manuscript headline theorems remain open.

## Proposed exact inventory

- `TNLean.PEPS.AreaLaw.Geometry.beltCellMarks`;
- `TNLean.PEPS.AreaLaw.Geometry.beltMarks`;
- `TNLean.PEPS.AreaLaw.Geometry.beltCellMarks_subset_closure_dyadicCell`;
- `TNLean.PEPS.AreaLaw.Geometry.card_beltCellMarks`;
- `TNLean.PEPS.AreaLaw.Geometry.card_beltMarks_le`;
- `TNLean.PEPS.AreaLaw.Geometry.exists_sparse_dyadic_belt_marks_shift`.

The shard is `docs/provenance/openai-math.d/8758-belt-marks.json`. All six
entries remain planned, with proposed names and pending verification.
The prior 209 entries and all of their source and evidence must remain
unchanged. The final immutable baseline is captured after the completed
primary-count evidence is committed and incorporated into this branch.

## Canonical evidence to be recorded

Exact frozen source revision: **Pending**.
Published pull request and evidence head: **Pending**.

| Check | Expected command | Result | Elapsed seconds |
|---|---|---|---|
| Changed Geometry target | `lake build TNLean.PEPS.AreaLaw.Geometry` | Pending | Pending |
| Imported six-name audit | `lake env lean docs/provenance/evidence/8758-belt-marks-axioms.lean` | Pending | Pending |

The actual commands must run through the own-worktree
`scripts/lake_build_locked.sh` under the shared repository lock, reusing the
warmed cache and pinned prebuilt Mathlib artifacts. The source-only
preparation worktree has no Lake cache and performs no cache or build operation.
Its source was elaborated non-mutatingly from the existing warmed worktree.

The final record identifies actual commands, frozen source, times, exit
codes, module diagnostics and SHA256 hashes of
`8758-belt-marks-build.log` and `8758-belt-marks-axioms.log`. Any normalization
of captured whitespace must be described. The exact audit prints every
selected imported public name; its actual dependencies are recorded only
after the audit runs. Promotion updates only the six new rows after these
checks and a complete 215-entry provenance/source/license/notice validation
pass. The previous 209 entries and evidence remain byte-identical.

Independent mathematical and source review: **Passed** for all six declarations.
Strict non-mutating elaboration with all package options: **Passed**, without warnings.
Blueprint source synchronization: **Pending**.
Generated imports and formatter idempotence: **Passed**; 75 aggregators cover 2,834 production modules.
Full-library CI, compiled blueprint declarations and rendering: **Pending**.

The parent work recorded a whole-library local declaration-check failure
caused by a missing pre-existing `Fibonacci.olean` artifact. Its historical
failure log remains intact. A repeated local whole-library check is not
required for this planned changed-leaf verification; complete compiled
blueprint checking and rendering are tracked separately in CI.
