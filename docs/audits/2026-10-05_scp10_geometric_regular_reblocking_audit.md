# SCP10 geometric regular PEPS renormalization audit

Date: 2026-10-05.
Frozen prerequisite: `0dac182b8460fe5545953920fa7fc2b86f93f6d7`.
Source: `Papers/1001.3807/paper_v3.tex`, Observations 6.5–6.6,
lines 1818–1915; the three `figs4/renorm-*` diagrams. The fixed-point
figure was inspected alongside the coefficient conventions.

## Result and exact scope

`exists_regularTwoByTwoOriginalTensorIsometry` proves the normalized
same-original-tensor renormalization statement on an untwisted torus whose
coarse periods are at least three. Its only mathematical input is regular
G-isometry of the homogeneous four-leg tensor. The group is any finite group;
the common finite physical alphabet is arbitrary, with unused directions allowed.

The conclusion contains:

- Nonzero actual fine and original-coarse states, derived from the identity
  closure sector, rather than supplied as assumptions.
- A unit-norm surplus Bell state with every endpoint register retained.
- Positive factors `ca`, `cb`, an explicit family of local physical matrices,
  and a Hilbert-space isometry on the derived fine physical support.
- The unnormalized identity with the complete positive factor
  `(∏ v, sqrt (ca v) / sqrt (cb v)) * sqrt |G| ^ |E|`.
- The normalized identity: the isometry sends the normalized fine state to
  the normalized state of the **same original coarse tensor**, tensored with
  the normalized Bell product.
- A coefficient formula showing that this isometry acts by four-site
  physical grouping, the product of the local physical matrices, and output
  register regrouping. It is not an unspecified state-to-state isometry.

The canonical-coarse statement is also proved separately by consuming
`exists_regularGraphPhysicalSupportIsometry` from the frozen prerequisite.
The original tensor is identified with the canonical tensor by an actual
isometric equivalence between their complete physical supports.

The geometric reblocking is stronger in its boundary-size scope: it works
for all positive coarse periods, including one and two, on the bond-indexed
torus. The Bell support argument uses a simple coarse graph only for periods
at least three. Small-period physical Bell separation, inserted/twisted
closures, and other boundary conditions are explicitly outside the packet.
No unrestricted source label is promoted. The precise scope is documented in
`docs/paper-gaps/scp10_two_by_two_regular_fixed_point.tex`.

## Derived geometry, Gram identities, and supports

`twoByTwoTiledBondEquiv` is a bijection of **all** fine horizontal and vertical
bond assignments with paired crossing bonds and four internal bonds per
block. Its local neighbor identity is checked at all four corners and all
periodic seams. `twoByTwoBoundaryEquiv` retains the eight boundary legs as
four pairs. `torusBondNetwork_eq_twoByTwoBlocked` derives the actual global
contraction, with scalar one and no supplied global equality.

The four-site Gram proof expands the actual internal contraction. The four
internal edge constraints force all four group-average labels to agree;
the four free internal ket labels supply `|G|^4`. Thus the blocked isometry
factor is `|G| * ∏ i, cᵢ`. The additional `|G|` records the internal cycle.
There is no assumed block Gram or block G-isometry condition.

The original target tensor with surplus physical registers is proved
G-isometric from the original local tensor. Its graph state is proved to be
the original graph state times the unnormalized residual Bell product by
reindexing actual edge sums. Physical support transport uses normalized
adjoints and normalized target maps. Product-range membership of the actual
fine state is derived, and all unused ambient physical directions are kept
outside that explicitly stated support rather than silently discarded.

## Verification

All twelve new production modules were compiled directly with the pinned
Lean v4.35.0-rc3 compiler, using:

`-j1 -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true
-DmaxSynthPendingDepth=3 -Dlinter.mathlibStandardSet=true -DwarningAsError=true`.

| Module | Strict time (seconds) |
| --- | ---: |
| TorusTwoByTwoBlocking | 3.45 |
| TorusGraphBondContraction | 2.72 |
| GIsometricCoordinateTransport | 2.14 |
| GIsometricCanonicalSupport | 3.44 |
| RegularTwoByTwoGraphCoordinates | 8.67 |
| TwoByTwoTensorIsometry | 5.42 |
| RegularTwoByTwoPhysicalBlocking | 6.34 |
| RegularTwoByTwoNonzero | 2.91 |
| GraphGIsometricSupportTransport | 6.26 |
| PhysicalStateNormalization | 2.41 |
| RegularGraphSurplusSite | 6.41 |
| RegularTwoByTwoOriginalTensor | 5.32 |

These are local diagnostic times, all below the repository's 25-second
warning threshold. Final source SHA-256 values were rechecked against the
strict compilation receipts after production freeze.

Both strict regression files pass: `TorusTwoByTwoBlocking` in 3.32 seconds
and `TwoByTwoTensorIsometry` in 4.05 seconds. They cover arbitrary alphabets,
coarse periods one and two for the bond-indexed geometry, the nonabelian group
S₃, an actually unused physical direction, failure of ambient surjectivity,
the original fine 6×6/coarse 3×3 tensor, derived nonzero states, and the exact
normalized original-tensor/Bell identity.

An exhaustive compiled harness checks all **66 public declarations** and
prints all of their transitive axioms. The only axioms are `propext`,
`Classical.choice`, and `Quot.sound`. The harness passes strict flags in
3.19 seconds. Guarded axiom regressions also cover the mathematical capstones.
No `sorry`, `admit`, `native_decide`, unsafe cast, or new axiom is present.

The exact-source artifact audit covers **184 TNLean/QIC modules** from all
twelve new production roots and both tests. It reports zero source mismatches
and no missing required production artifact. Twenty-one imported QIC source
modules were compared with the exact pinned QIC commit, rather than relying
on the donor package's differing HEAD. The Mathlib donor's HEAD matches its
pin and its tracked tree is clean. Existing exact-source caches were reused;
no Mathlib build or new full checkout was performed.

All **66 declarations have exactly one blueprint owner** across five new
fragments. There are no missing or extra tags, duplicate owners, unknown
dependency labels, or unbalanced environments. Pinned latexindent 3.24.7
formatting and second-pass idempotence were checked on the new TeX files.
The five fragments render together as a six-page PDF with resolved references
and no overfull boxes; the standalone scope note renders as three pages.
The geometric formulas, normalized original-tensor statement, and scope note
were inspected visually. The scoped tactic-pattern scanner reports no
repeated pattern above its thresholds; no new candidate is recorded.

## Reproducibility and limits of this verification

Local evidence is retained under `.validation/`:

- `geometric-final-strict-results.json`, with source hashes and production times
- `geometric-final-test-results.json`, with the final regression and exhaustive-harness runs
- `geometric-all-declarations.json` and `geometric-all-declarations.strict.log`
- `two-by-two-isometry-source-audit.json`, the 184-module exact-source audit
- `audit-two-by-two-isometry.py`, the runnable source/artifact audit
- `geometric-blueprint-audit.json`, the complete scoped ownership/coverage check
- `geometric-tactic-patterns.log` and `geometric-render/`

The packet changes only new files. No existing production file, frozen packet,
root import, blueprint router, publication state, or MPU-gauging file was
changed. Because aggregate imports and routers were deliberately left alone,
a repository-wide build and root `checkdecls` run are not claimed. Exhaustive
new-module strict compilation and compiled declaration checks are the evidence
for this packet. The repository-wide blueprint sync scan separately reports
523 pre-existing/dependency-resolution issues in this sparse worktree; all
owned declarations and labels pass the independent scoped check.
