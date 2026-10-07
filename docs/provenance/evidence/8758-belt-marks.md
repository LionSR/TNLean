# The actual marked points of belt cells

Six original declarations in `BeltMarks.lean` define the nine actual marks
of a dyadic cell and their deduplicated finite union over a finite family of
cells at one scale. The coordinate offsets zero, one half and one give the
center, four corners and four side midpoints. All nine points belong to the
closed cell and are distinct, since its side is positive.

For every finite cell-index set F, including the empty set, the number of
marks in the union is at most nine times the number of cells. The established
sparse-belt estimate therefore supplies actual coordinate residues with

\[
|\mathcal M_k|\le576(2C_0+1)^2\,|\partial_\Lambda A|\,2^{-\delta_0 k/2}.
\]

The coefficient is exactly 9 × 64. The bound is uniform in the finite
domain, cut, origin and nonnegative scale, including empty cuts and layers.

## Source, attribution and scope

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.

The nine marks and deduplication are in lines 325–330 in the proof of
`prop:two-families`, immediately before `geometry:initial-stars`. The sparse
composition also uses `geometry:belt-count`, lines 220–228. The proof text is
independently written; no upstream Lean source or proof text is reused.
OpenAI Codex (GPT-6) assists LionSR under the existing
[TNLean #8758 claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6043892601).

This contribution concerns actual locations and finite counting at one scale.
Minimum incident-scale assignment across layers, contact completeness,
isolated stars, mark separation, repairs, descendant counts, birth separation
from earlier actual regions, the complete two-family partition and both
manuscript headline theorems remain open. Independent review approved the
mathematical scope of the two definitions and four theorems.

## Exact source and canonical evidence

Exact verified source: `0b1556b85180ed55e2a1db6ada9f44cc24a8df2b`.
The six audited declarations are:

- `TNLean.PEPS.AreaLaw.Geometry.beltCellMarks`;
- `TNLean.PEPS.AreaLaw.Geometry.beltMarks`;
- `TNLean.PEPS.AreaLaw.Geometry.beltCellMarks_subset_closure_dyadicCell`;
- `TNLean.PEPS.AreaLaw.Geometry.card_beltCellMarks`;
- `TNLean.PEPS.AreaLaw.Geometry.card_beltMarks_le`;
- `TNLean.PEPS.AreaLaw.Geometry.exists_sparse_dyadic_belt_marks_shift`.

| Check | Actual command | Exit code | Elapsed seconds |
|---|---|---|---|
| Changed Geometry target | `lake build TNLean.PEPS.AreaLaw.Geometry` | 0 | 15.964 |
| Imported six-name audit | `lake env lean docs/provenance/evidence/8758-belt-marks-axioms.lean` | 0 | 4.331 |

The new `BeltMarks` module compiled in 10 seconds and the Geometry aggregator
in 2.8 seconds, without warnings. Every one of the six exact imported names
reports only `propext`, `Classical.choice` and `Quot.sound`. No placeholder,
additional axiom or prohibited proof mechanism is reported.

The commands ran consecutively through the own-worktree
`scripts/lake_build_locked.sh --` under the shared repository lock, reusing
the warmed cache and pinned prebuilt Mathlib artifacts. The driver completed
and released the lock. No local full-library or Mathlib source build was
repeated. The source-only preparation worktree had no `.lake` directory and
performed no cache or build operation. Its source passed non-mutating
elaboration with all package options from the warmed worktree.

Evidence log paths and SHA256 hashes:

- `8758-belt-marks-build.log`: `c37744f6852ab8e1708887b9ef8df195f276e679516021794f1a50eb7436b77b`;
- `8758-belt-marks-axioms.log`: `1d7a7c77eeea8fd30e0d2ce99468afa25825adeecd686b6d3f09d3fca472c012`.

Each log records its actual command, frozen source revision, elapsed time
and exit code. Captured output has trailing whitespace removed; build
diagnostics and the actual quoted axiom results are preserved.

## Provenance and integration

The complete 215-entry current-policy provenance/source/license/notice
validation passes, including exact module and audit bytes at the frozen
source, command headers, log hashes and the six quoted imported names.
Promotion changes precisely the six new entries in
`docs/provenance/openai-math.d/8758-belt-marks.json`; all prior 209 entries,
proof sources and evidence remain unchanged. The prior-byte baseline is
captured from the completed primary-count publication
`61fd819e7fe4689b8e0893affc9f127238b191ec`.

Complete blueprint source synchronization and reverse coverage passed with
20,169 distinct public references and 20,163 theorem-like entries. No missing
or duplicate references were reported. All six new declaration tags match
the independently reviewed statements. Formatter idempotence, reader-facing
prose and generated imports were checked. The Geometry proof-pattern scan
found no repeated block.

The earlier local whole-library declaration check failed because of the
missing pre-existing `Fibonacci.olean` artifact. Its historical failure log
remains unchanged; that unrelated check was not repeated locally for this
changed module. Full-library CI, compiled blueprint declaration checking and
rendering remain pending. Source synchronization and the successful imported
audit are distinguished from those full-library checks.
