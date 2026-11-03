# Guarded failure ancestry below one balanced root

For an arbitrary choice space, each choice determines one merge operation
of the existing balanced interval recursion. Fix any property of interval
spaces which holds for the full local space at every valid short leaf.
The new deterministic theorem proves that the root failure set is contained
in the union of guarded local failure sets over precisely the existing
balancedIntervalMergeList below that root.

A guarded local failure means that both actual midpoint children satisfy
the property but their actual parent does not. Every space is evaluated
using the same chosen operation. No successful-parent assumption, local
failure bound, probability law, measurability hypothesis or supplied failing
descendant is used. In particular the theorem supplies the deterministic
set inclusion needed before a separate probabilistic union bound.

## Proof and edge cases

Fix a choice and induct on the root length. A short root is the full local
space, so its assumed leaf property excludes failure. At a long root,
consider its actual two midpoint children. If either fails, the induction
locates a guarded failed descendant in that child's actual merge list,
which is a sublist of the root merge list. If both satisfy the property,
the failed parent itself gives the required witness and is the final entry
of the root list. The set inclusion follows by inserting this witness into
the indexed union.

The positive leaf width guarantees that both children of a long valid root
are strictly shorter. Weak endpoint cuts and intervals of length zero are
included. A zero-length root is a short leaf and therefore has empty failure
set under the leaf hypothesis. The proof needs no positive local dimension
or nonzero Hilbert space. The index list is the existing actual list, not a
new tree model and not all overlapping intervals. No distinctness of entries
is needed, so duplicates would not affect the union.

The source context is ALVV, arXiv:1602.08828v2, Figure fig:algo1 and the
probability estimate at lines 1777–1817. This is a separate deterministic
auxiliary, not a proof of the source's probability or running-time theorem.
Conditional local probability estimates and their later summation remain
separate. The existing count of the actual root list is unchanged.

## Verification and provenance

The source-only worktree is based on TN
435cbe7fe53e5d3a04c1b8eb2382753749f21a64, and has no .lake directory.
The private checker reads the immutable fully warmed provider at that same
TN commit with its own QIC b2ea12a0139820758e161514968ed9ead661c5a7.
Exact clean heads, the full-build readiness record, selected source/object
hashes, build inputs and the prebuilt Mathlib artifact hash are guarded
before and after each check. Outputs are confined to
/tmp/tnlean-balanced-failure-20261103. No shared cache is changed and no
Mathlib source is compiled.

The actual-name strict check passes in 4.598 seconds with three guarded
dependency pairs. The imported audit covers all three public declarations in 3.955 seconds
with four guarded dependency pairs, and uses only propext, Classical.choice
and Quot.sound. Its exact hashes are recorded in the external manifest. Temporary audit commands are
deleted after checking. No production fixture or diagnostic command is added.

Source-only blueprint synchronisation reads dependency sources from the
same immutable provider. Import aggregation, blueprint roles, reader-facing
prose, forbidden-token, whitespace and dependency-label checks accompany
the contribution. The tactic scan identifies no added repeated block;
the merge-list membership simplification is performed once before the
three logical cases. Ordinary build and compiled blueprint validation remain
for coordinated integration.
