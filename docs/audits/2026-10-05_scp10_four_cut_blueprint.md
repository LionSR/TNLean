# SCP10 four-block closure: blueprint and declaration audit

## Scope and source ownership

This documentation packet covers all **304 public declarations in the 30 source
modules** added between `3b3da4eff` and
`0fb7def90924c0b68a6c4fe081538d85e3669f51`. It includes definitions,
abbreviations, theorems, and inline `@[simp] theorem` declarations. Regression
examples remain tests; no test-only declaration is assigned a mathematical
blueprint owner.

The complete machine-readable inventory is
[`2026-10-05_scp10_four_cut_blueprint_inventory.json`](2026-10-05_scp10_four_cut_blueprint_inventory.json).
It records every fully qualified declaration, its source file and line, its
unique blueprint label, its owning fragment, the source commit, and the SHA-256
of every source module. The focused checker independently enumerates source
names, requires exact coverage, and verifies that the source files still match
the committed SHA-256 snapshot. Checking requires no historical Git objects,
so it also works after squash publication or in a shallow/exported checkout.
Historical commit IDs are provenance labels only. Explicit `--write-inventory`
regeneration re-enumerates all declarations and retains the source attribution
only when the module bytes are unchanged; changed bytes are marked
`working-tree`, rather than attributed to the earlier snapshot.

The source-labelled owner is `thm:peps_four_cut_closure`, attached exclusively to
`TNLean.PEPS.DependentTorus.fourCutSpace_eq_commutingClosureSpan`.
Its displayed equality uses the actual four cut maps and actual commuting
closure networks. Each of the eight virtual alphabets and each of the four
physical alphabets may differ. Each bond carries its own matching semi-regular
representation, and each site is G-injective for the representation on its
actual incidences. A cut accepts one arbitrary joint boundary tensor; no initial
factorization or boundary invariance is imposed.

No additional common-dimension, homogeneous-tensor, G-isometry, parent-kernel,
period-at-least-three, or supplied spanning hypothesis appears. The proof works
for algebraic semi-regular representations; the source's unitary convention is
a specialization. The common-alphabet theorem has a separate specialization
owner and is not used to label the unrestricted source theorem.

### Exact primary-source anchors

All anchors below are in `Papers/1001.3807/paper_v3.tex`.

| Source content | Exact source label or passage | Blueprint owner |
| --- | --- | --- |
| G-injectivity and invariant left inverse | Definition 5.1; `eq:2d-ug-sym`, `eq:2d-linv`, lines 1278–1296 | Existing `def:peps_g_injective`, `thm:peps_g_injective_left_inverse`; dependent incident and inverse entries cite these owners |
| Independent matching link representations | Lines 1310–1316 | `def:peps_dependent_incident_action`, `def:peps_full_four_cut_space` |
| Trace-dual coefficient extraction | Lemma 4.6; `lemma:noninj:semireg-trace-ug-delta`, lines 1015–1029 | Existing `thm:peps_torus_projector_extraction`, then `thm:peps_dependent_coefficient_extraction` |
| Four-block closure statement | Theorem 5.5; `thm:2d:closure`, `eq:2d:closure-intersection`, lines 1424–1474 | `thm:peps_four_cut_closure` |
| Applying the invariant inverse and comparing closures | `eq:2d:closure-inv`, `eq:2d:close-in-in`, lines 1481–1513 | `thm:peps_dependent_common_inverse`, `thm:peps_dependent_uncut_coefficients`, `thm:peps_full_four_cut_nonflat_zero` |
| Projector contraction and movable strings | Theorem 5.9, lines 1582–1621; `eq:2d:move-strings` | `thm:peps_dependent_projector_expansion`, `thm:peps_dependent_vertex_gauge` |

The finite product-range/slice theorem and generic directed-multigraph results
are stated as auxiliary mathematical results, not as additional named source
theorems. They justify the coordinate support step before the source's
coefficient comparison. Existing related owners remain untouched; the new
fragments reference fourteen previously established labels rather than duplicating
their declaration tags.

## Fragment order

The proposed inclusion order, after the existing torus/group-representation
foundations, is:

1. `ch24_peps_four_cut_labelled_geometry.tex`
2. `ch24_peps_dependent_networks.tex`
3. `ch24_peps_dependent_projectors.tex`
4. `ch24_peps_dependent_bond_support.tex`
5. `ch24_peps_full_four_cut_closure.tex`
6. `ch24_peps_four_cut_diagrams.tex`
7. `ch24_peps_four_cut_common_boundaries.tex`
8. `ch24_peps_four_cut_common_projectors.tex`
9. `ch24_peps_four_cut_common_reconstruction.tex`

All paths are under `blueprint/src/chapter/`. The first six give the unrestricted
argument and its four pictures; the final three document the common-alphabet
and uniform specializations and their supporting declarations. Each grouped
entry states the definitions, equivalent forms, or immediate specializations
owned by its tags, and theorem groups include mathematical proofs with the
actual normalization and orientation formulas.

Shared routers, `blueprint/lean_decls`, Lean source, import aggregators, and
paper-gap claims are deliberately outside this documentation commit. Integration
must add these fragments once in the order above, regenerate shared declaration
metadata through the normal build, and update the old source-status claim to
point to the dependent capstone. The generic endpoint and support results do
not assert completion of the separate intersection or geometric reblocking
source targets.

## Diagram contract

The four panels represent the source's `close-out-out`, `close-in-out`,
`close-out-in`, and `close-in-in` contractions. Coordinates are
`A=(0,1)`, `B=(1,1)`, `C=(0,0)`, `D=(1,0)`, with x rightward and y upward.
A horizontal bond has tail `(x,y)` and head `(x+1,y)`; a vertical bond has
tail `(x,y+1)` and head `(x,y)`. Cut `(c,r)` opens horizontal bonds with head
column c and vertical bonds with tail row r. Thus the four panels correspond
to `(0,0)`, `(1,0)`, `(0,1)`, `(1,1)` and to boundary tensors M, N, P, Q.

Each panel has:

- four block tensors, each with four virtual ports and one explicit physical leg;
- all eight distinct native bond IDs, without identifying parallel bonds;
- four uncut identity pairings;
- a single eight-port boundary tensor, permitting arbitrary correlations;
- head/tail superscripts on each cut incidence;
- external typed boundary `(virtual, physical)=(0,4)`.

The central placement of the boundary tensor is an incidence-preserving drawing
choice; the source's exterior/interior positions are encoded by the labelled
cut rather than by a potentially ambiguous planar picture. The regression
checks the actual labelled graph and each incidence against the cut formula,
not only the number of external legs.

## Validation

Run the declaration/source audit from the repository root:

```sh
python3 scripts/check_peps_four_cut_blueprint.py
# With the pinned Lean executable and already warmed LEAN_PATH:
python3 scripts/check_peps_four_cut_blueprint.py --lean-check
```

The compiled-name check loads all thirty module artifacts and resolves all
304 quoted constants in Lean's environment. It uses strict implicit arguments,
`maxSynthPendingDepth=3`, the Mathlib standard linter set, and warnings as errors.
It does not rebuild packages or replace the separate strict source/regression
validation recorded in the full source audit.

Run the Tenkz regression with the pinned Tenkz checkout and XeLaTeX available:

```sh
python3 scripts/test_tenkz_peps_four_cut.py --output-dir /tmp/four-cut-review
```

Validation outcomes and focused rendering details are recorded below after
completion. Full integrated blueprint web/PDF generation remains the
integrator's responsibility because shared routers are not changed here.

### Completed checks

- **PASS:** 304/304 public declarations have exactly one labelled, checked
  mathematical owner. There are no missing, duplicate, or unexpected tags.
- **PASS:** all thirty source files match the audited source commit byte for
  byte; all eight exact primary-source labels resolve uniquely in the paper.
- **PASS:** every reference, dependency label, and citation in the nine new
  fragments resolves uniquely against repository source.
- **PASS:** all 304 declarations resolve in the compiled Lean environment with
  the strict settings above. The check uses elaborated quoted names, avoiding
  source-linter-inappropriate hash commands.
- **PASS:** four diagrams render separately and together under the actual
  report preamble; their complete labelled incidence graphs and typed external
  signatures agree with the source cuts. Tenkz reports no audit findings.
- **PASS:** a focused XeLaTeX/BibTeX render of all nine final fragments produces
  23 pages. The final log has no undefined references/citations, missing
  characters, overfull boxes, or underfull boxes. All pages were visually
  inspected, including the source theorem, proof chain, and four cut diagrams.
- **PASS:** all nine fragments are idempotent under pinned latexindent 3.24.7;
  focused reader-facing prose checks, Python compilation, and whitespace checks
  pass.

The focused render supplies local `E.1`–`E.14` reference numbers for the fourteen
source-verified, previously established dependencies outside these fragments;
it does not invent integrated book numbers or reproduce their owning text.
Hyperref's empty-target notices for those review-only external anchors are
expected. This is a focused layout/reference check, not a claim that the shared
book routers or full web publication have already been built.

The combined-render regression also covers page breaks between pictures.
Keeping each caption and its Tenkz picture in one minipage avoids a picture
construction failure observed when page output interrupted the fourth panel.
All generated PDFs, PNGs, logs, and pre-existing validation data remain outside
the commit; only the new blueprint sources, audits, and two check scripts are
committed.
