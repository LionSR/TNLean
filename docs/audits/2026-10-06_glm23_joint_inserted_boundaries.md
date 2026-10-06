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

The integration additionally shortens the explicit nilpotent-square simp
proof to avoid likely unused simp arguments. That change and all six strict
axiom guards still require separate-module CI. No proof placeholder or new
axiom is authored. All 22 new declaration owners remain unchecked.

Generated imports, the existing strict regression loop and the chapter
router include this package. Global and reverse source synchronization pass
using the exact pinned QIC source. The draft is checkpointed before further
long checking. Post-recovery Lean, full blueprint rendering/browser checks
and the unchanged timing gate remain pending. Independent source-only
mathematical review found no blocker; it is not compiler verification.

## Dependency boundary

The draft is based on the checked whole-path head
`8ed3342960e9f543dc988be6ac62a598676ea359`. It changes no dependency pin,
PEPS source or MPU-gauging source. Existing unchanged block interval and
continuity APIs are reused. A supplemental compression experiment and a
future-gap design note are excluded from this production package.
