# 2026-04-28 — Issue #970 common phase-cover adapter

## Scope and issue-thread check

This branch starts the next non-Gemma connection after merged PR #984.  Before
writing statements I read the bodies and comments for issues #970, #944, #969,
#942, and #652, and inspected the merged PR #984 diff.

The issue-thread conclusions used here are:

- #976 already proved the nonzero-block span adapter
  `MPSTensor.mpv_span_eq_of_common_phase_cover` and the exact-nonzero sector theorem
  `MPSTensor.fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_phaseCover`.
- #984 exposes explicitly relabeled one-sided common-sector families, but it does
  not yet construct cross-side maps from both nonzero-sector families onto a single
  common MPV phase family.
- #944 is now reduced to the finite-length span comparison for the original
  nonzero-weight block families, after the one-sided BNT representative-span transport.
- #970 asks for the comparison step from the common nonzero-sector construction to
  that span comparison. The mathematically precise data are a common family together with
  surjective class maps from both sides and MPV-phase equivalences for every
  nonzero-weight block.
- #969 and #652 still require a later common injectivity/Wielandt blocking stage
  before the fully unconditional non-periodic canonical-form theorem can be
  closed.

## Paper route checked

This branch follows the CPSV/CPGSV non-Gemma route.

- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 217--225 state the block-diagonal
  weighted nonzero decomposition and normalize the corresponding completely positive
  maps by their spectral radii.
- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 227--231 state the blocking by the
  least common multiple of periods to remove peripheral cyclic components.
- `Papers/2011.12127/TN-Review-main.tex` lines 1815--1820 give the same
  period-removal step and identify the primitive data after blocking.
- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 317--332 define injectivity and
  state the Wielandt blocking step.  This branch does not assert that final
  injectivity refinement.

## Lean progress in this branch

### Equal-norm comparison file

New declarations:

- `MPSTensor.MPVCommonPhaseCover`: a data record for two nonzero-block families.
  It stores a finite common block family, class maps from both nonzero-weight families to
  the common family, MPV-phase equivalences between each nonzero-weight block and its
  common representative, and surjectivity of both maps.
- `MPSTensor.MPVCommonPhaseCover.span_eq`: applies the already-merged span
  theorem to prove equality of the two finite-length nonzero-block MPV spans from
  this common-cover data.

The data record deliberately contains only the actual mathematical comparison
data needed by the span adapter.  It does not claim that this data follows from
`SameMPV₂` alone.

### `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean`

New theorem:

- `MPSTensor.fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_commonPhaseCover`.

This is the common-cover form of
`MPSTensor.fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_phaseCover`:
callers supply one `MPVCommonPhaseCover` instead of separately passing the common
family, two class maps, phase equivalences, and surjectivity proofs.  The proof is
a direct application of the existing theorem and introduces no new analytic
assumption.

### `blueprint/src/chapter/ch11_assembly.tex`

Added entries for:

- the common MPV phase-cover data;
- the span equality theorem obtained from that data;
- the exact nonzero-sector theorem that uses the data.

## Remaining paper hypotheses

The full #970/#944 comparison is not closed by this branch.  The remaining
mathematical hypothesis is the construction, from the structural `SameMPV₂` reduction
and the common-blocking data, of:

1. one common nonzero-sector family after any needed relabeling and further
   injectivity blocking;
2. surjective class maps from each side's nonzero sectors to that common family;
3. MPV-phase equivalences between every nonzero sector and its common representative;
4. exact zero-tail bookkeeping at the final common blocking length.

Once those data are available, `MPVCommonPhaseCover.span_eq` discharges the
finite-length span equality required by #944, and the structural theorem reformulation
passes that span equality to the existing after-blocking sector comparison theorem.
