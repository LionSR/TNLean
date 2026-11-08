# Pure one-particle window overlap

Context: #10386, the finite-prefix zero-momentum condition in the
SPWC10 ground-state dichotomy. This change proves a local ingredient;
it does not assert a counterexample satisfying the full all-volume
frustration-free uniqueness assumptions.

The geometric state is the existing `MPSTensor.pvbsEdge`, with actual
one-particle coefficient q^j. No second weighted-W state, parallel
canonical predicate or auxiliary Hamiltonian assumption is introduced.

The two-by-two minor at its first cut is exactly q for every length at
least two. A generic overlapping-section argument proves that a vector
with one-dimensional first and last windows must vanish when this
minor is nonzero. Thus the same entangled pure one-particle vector
cannot occupy two adjacent overlapping windows. The theorem concerns
actual coefficients on the union, rather than an assumed purity or
nonvanishing conclusion.

The right-endpoint recursion reuses the existing PVBS first-site data.
Mathlib's `Fin.snoc_eq_cons_rotate` supplies the cyclic placement. Under
q^n=1 the resulting identity is q times the rotated vector equals the
original vector. If q is nontrivial, the line is cyclically invariant
but the vector is not. This alone does not resolve #10386: a full
fixed-interaction model still requires the main-sector, mixed-sector
and every-volume kernel arguments.

## Verification

Independent bounded source/API review checked the minor, overlapping
sections, endpoint recursion and cyclic-phase orientation against the
pinned Mathlib and existing PVBS APIs, finding no concrete mismatch.
All seven new declarations have supporting Blueprint anchors and
remain `notready`. No local Lean, Lake, build or checkdecls command was
run, as requested; source review is not kernel acceptance.

For source provenance, all 8,563 Mathlib Lean files in the shared
read-only snapshot match the exact git blobs at the manifest pin
c55e6e786f49471c72fbddbec5415808896aec1e, and all 1,368 QICLean Lean
files match acda92aa70e69b37507e422bceb5414036859fe6. The snapshots have
no own .git directory, so a git command in them must not be treated as
an independent dependency-head check.
