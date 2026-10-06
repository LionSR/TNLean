# Joint inserted boundaries for the block path

## Source and mathematical scope

GLM23 v3, `Papers/2203.12563/REsubmission.tex`, lines 1695–1777, extends
its mixed construction to block families. This auxiliary package handles
joint extended boundary spaces for a finite family with a common physical
alphabet. It assumes simultaneous one-site spanning and a nonzero insertion
in each block. It assumes neither orthogonality of the physical block
columns nor invertibility of the insertion.

The three production modules define the joint inserted trace map, prove
positive-length boundary injectivity and simultaneous inserted-word
spanning, derive the restriction intersection, identify the actual open
Hamiltonian kernel for every N≥2, compute its dimension as the sum of the
squared block dimensions, and prove fixed-volume kernel-projector
continuity. Empty label sets, zero physical dimension and singular
nonzero insertions are retained. The nilpotent and overlapping-column
regressions exercise these distinctions.

These results do not prove an endpoint spectral gap, periodic endpoint
identification, fixed-MPO commutation, or the full degenerate phase
classification. The actual mixed-family span and the volume-independent
boundary comparison remain separate source obligations. In particular,
thermodynamic block orthogonality does not imply one-site physical
orthogonality, and a minimum of independent block gaps does not supply the
needed joint gap.

## Validation and recovery

The first full exact-body check completed with exit one. It identified
three production elaboration details: unfolding the one-site sum maps,
evaluating a zero block tuple, and rewriting the joint sum for continuity.
It also identified strict style/test issues. The intersection and open-kernel
arguments had no independent diagnostic, but no passing package check is
claimed; downstream guards correctly rejected unfinished dependencies.

A repaired full check started before the cloud executor was replaced. Its
terminal result is unknown. All four original production/regression files
were recovered and matched their recorded pre-reset SHA-256 values. The
repaired snapshot was recreated by applying the exact retained repair
operations. Those repaired-file hashes were first recorded during recovery;
this is not a claim to have recovered a successful second log.

The integration additionally shortened the explicit nilpotent-square simp
proof to avoid unused simp arguments. These repairs, the production modules
and all six strict axiom guards subsequently passed the full CI build; the
unknown recovery-run outcome remains unknown. No proof placeholder or new
axiom is authored.

### Checked production checkpoint

Draft [#8719](https://github.com/LionSR/TNLean/pull/8719) has production head
`edd9d1ff2afb79c7a9e9f6c29ffe8e63bf19d699`, with tree
`0b8fbec9396a0c22dec565493e5c2dd6f8cbf241`. The recovered local checkpoint
`a7510c36de0c35f7bf712f287baa45ecb714e9d6` has exactly the same tree.
[CI run 37414574404, build job 112110257136](https://github.com/LionSR/TNLean/actions/runs/37414574404/job/112110257136)
tested merge `eba712a1c3bff50bbf2f859207d214585615e143`, whose tree is also
`0b8fbec9396a0c22dec565493e5c2dd6f8cbf241`, and passed the full library build, separate-module strict regressions, all six standard-axiom
guards and the unchanged timing gate. The three new production modules took
4.2, 4.5 and 8.2 seconds respectively. The guards permit only `propext`,
`Classical.choice` and `Quot.sound`.

The blueprint job failed at pinned LaTeX formatting in
`ch30_mpo_joint_inserted_open.tex`; its downstream rendering/browser checks
were not thereby validated. The documentation correction adds checked
statement markers for all 22 declaration owners in four entries and checked
markers for the three proofs, using the successful production checkpoint.
It also applies the pinned formatter to this leaf only. It changes no Lean
source, regression, workflow, router or dependency pin.

### Documentation validation

Generated imports, the existing strict regression loop and the chapter
router already include this package. The final documentation batch passed:

- The repository-wide pinned `latexindent` 3.24.7 check, with only this
  chapter reformatted.
- Global source synchronization: 19,753 references and 39,424 declarations,
  with no missing, stale or duplicate ownership tags. The exact QIC source
  revision was `2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`, matching the pin.
- Reverse coverage for all three new production modules: no declaration
  owners missing from the blueprint. The chapter has 22 checked owners in
  four entries; the three checked proofs cover 16 theorem owners.
- A six-page focused PDF, rendered with the unchanged mathematical leaf
  and seven exact referenced statements. Visual inspection covered all
  four joint entries, their proofs and the referenced Tenkz figure. The
  final TeX log has no unresolved references, missing glyphs or overflow
  diagnostics.
- Strict `texra-blueprint` 0.3.8 web rendering and generated-source checks
  on six HTML pages. All 22 owner links are present. The focused temporary
  router selects the leaf and reference context; its configuration omits
  the unrelated fundamental-theorem graph subset. Repository configuration
  and strict renderer checks are unchanged. The inherited Tenkz picture
  uses the renderer's supported PDF-to-SVG route because local `dvisvgm`
  is absent; no new diagram is introduced.

This is focused rendering, not a new full-volume or browser-CI pass.
The full-volume browser harness cannot run on this extract because its
fixture pages are absent; a separate browser launch also confirmed that
local Chromium is missing. Browser checks remain **unrun**, and the
fail-closed CI browser gate is unchanged. The optional local `chktex`
invocation is also unrun because its executable is absent. No local Lean
build, probe or cache mutation was performed. Independent source-only mathematical review
found no blocker; compiler verification comes from the CI run above.
The manifest records exact production and rendered-artifact hashes.

## Dependency boundary

The draft is based on the checked whole-path head
`8ed3342960e9f543dc988be6ac62a598676ea359`. It changes no dependency pin,
PEPS source or MPU-gauging source. Existing unchanged block interval and
continuity APIs are reused. A supplemental compression experiment and a
future-gap design note are excluded from this production package.
