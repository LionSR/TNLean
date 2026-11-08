# Exact frustration-free exterior clipping

Source: AKLV, arXiv:1301.1162v1, Section 4, frustration-free clipping preceding
Theorem 4.3 (`t:ent`), `1dfrustrated34.tex:810–818`:
<https://arxiv.org/html/1301.1162v1#S4>.
The source says that clipping keeps the original ground state and an inverse-gap
cutoff preserves a constant fraction of the original gap. This bounded result
makes that step explicit using already accepted truncation estimates.

Base: TN main `7b1ef717cec8bb851b433585e7b28cf4f7639208`, pinned Lean
v4.35.0-rc3, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`, QICLean
`14ecc5b64bb61cccb01a6583bbab3252bee1486b`.

## Actual statement and construction

The one new public lemma in
`TNLean/MPS/AreaLaw/AKLV/FrustrationFreeClipping.lean` takes the original
nearest-neighbor supported positive contractions, two retained boundary bonds
`a < b`, a unit vector Ω with original energy zero, original projector gap
`0 < g ≤ 1`, and cutoff `t ≥ 1024/g`.

Its operator is the actual existing two-sided truncation of the existing zero-
shift cut blocks: bonds strictly before a and strictly after b are clipped
separately, both boundary bonds and the middle bonds are retained. Regional
positivity follows from finite positive sums. Commutation and reconstruction
come from `normalizedCutBlock_commutations` and `normalizedCutBlock_sum`.
There is no supplied normalized-chain object, regional positivity, commutation,
clipped gap, spectral comparison, or kernel premise.

The conclusion is `0 ≤ K ≤ H`, exact preservation `KΩ = 0`, and
`K ≥ (g/2)(I − |Ω><Ω|)`, about the same original Ω. Exact preservation follows
from QICLean's accepted order-sandwich lemma. The accepted
`orthogonal_clipped_energy_ge` at e = 0 needs
`1024g ≤ t g²`, which follows from `t ≥ 1024/g`. Decomposing an arbitrary vector
along the actual unit Ω and using the accepted eigenvector-energy splitting
turns that orthogonal lower bound into the projector inequality.

No new functional calculus, clipping-gap framework, detectability argument,
canonical predicate, or dependency is introduced. Neither #10331 nor #10371 is
a prerequisite: accepted main already gives the inverse-gap cutoff at zero
energy. The potentially sharper generic degenerate-kernel estimate is not part
of this change. This result does not optimize the Chebyshev parameters or prove
the final source entropy rate without inverse-gap logarithms. Issue #9838 stays
open for those separate construction/rate and acceptance obligations.

## Review and validation

Two independent native source reviews passed the entire 129-line proof and
actual pinned APIs. Both checked the raw-matrix/Euclidean action identification,
order sandwich, original-ground-vector preservation, inverse-gap scalar cutoff,
Pythagorean norm-product identity, energy splitting, and final operator-gap
conversion. These reviews did not elaborate Lean.

Generated imports, full Blueprint/source synchronization and reverse coverage,
duplicate tags, Blueprint roles, active mathematical references, ChkTeX, source
width/size, proof-token checks, repeated-tactic scan, and whitespace checks
passed. The Blueprint contains one new supporting lemma entry with one public
anchor marked `notready`. TeX was formatted with the repository wrapper. The
proof reuse is recorded in the tactic-pattern ledger.

The native source checker read source-only exact dependency checkouts at the
manifest pins. No local Lean, Lake, build, elaboration, or compiled Blueprint
check ran, and no compiled acceptance is claimed. Exact-head hosted acceptance
and integration remain separate gates.
